(function () {
  "use strict";

  var BRIDGE_INIT = "gamehub:bridge:init";
  var BRIDGE_READY = "gamehub:bridge:ready";
  var BRIDGE_EVENT = "gamehub:bridge:event";
  var BRIDGE_LOG = "gamehub:bridge:log";
  var ACK = "gamehub:ack";

  /**
   * This SDK's version. Kept identical to packages/sdk/protocol/manifest.mjs by sdk:check, which
   * fails the build if the two disagree.
   *
   * It has to mean something, and until 1.0.0 it did not: every SDK ever shipped reported
   * "0.1.0", including builds from before the platform could ask a game what it implements.
   * A game arrived claiming the same version as the SDK it was four protocol changes behind,
   * so the one field that could have named the problem said nothing at all.
   *
   * So 0.1.0 now means exactly one thing — old enough to predate the checks — and every
   * version from here is compared against the platform's own at handshake. Bump it whenever
   * the wire protocol changes.
   */
  var SDK_VERSION = "2.0.0";

  // ---- Acknowledgements ----------------------------------------------------
  //
  // Every message that carries an `id` gets one back. It is a receipt, and it answers the
  // one question neither side can otherwise ask: did you actually do anything with that?
  //
  // Delivery is not the interesting part — postMessage does not lose messages. `handled` is.
  // The platform can watch what a game SENDS, but a game *receiving* gamehub:audio:set and honouring
  // it produces no traffic at all, so from outside, a game that mutes itself and a game that
  // ignores the volume button look identical. The ack is the game's own code path answering
  // for itself.

  /**
   * Which subscriptions count as handling a given inbound message.
   *
   * A game handles mute by calling onMute(), which subscribes to gamehub:audio:muted — NOT to
   * gamehub:audio:set, which the SDK itself consumes. Counting handlers on gamehub:audio:set alone would report
   * "unhandled" for a game that handles mute perfectly.
   */
  var ACK_PROOF = {
    "gamehub:audio:set": ["gamehub:audio:set", "gamehub:audio:muted"],
    "gamehub:screen:set": ["gamehub:screen:set"],
    "gamehub:data:state": ["gamehub:data:state", "gamehub:data:changed"],
    "gamehub:user:state": ["gamehub:user:state"],
    "gamehub:wallet:state": ["gamehub:wallet:state", "gamehub:wallet:changed"],
    "gamehub:ad:state": ["gamehub:ad:state", "gamehub:ad:finished"],
  };

  /**
   * The messages Unity answers for itself, from C#.
   *
   * GameHubBridge.jslib subscribes to these on the game's behalf whether or not the C# does
   * anything with them — it has to, it cannot know what the game will want. So a JS-side ack
   * would answer "handled" for every Unity build ever made, including one that ignores the
   * platform's volume button entirely. GameHubBridge.cs looks at its own event subscriptions
   * and answers honestly through ackEvent().
   */
  var UNITY_ACKS = { "gamehub:audio:set": true, "gamehub:screen:set": true };

  /**
   * Events a game is not allowed to send, ever.
   *
   * Two kinds live here.
   *
   * The wallet ones: a game may READ its player's Flux balance and SPEND from it, and may never
   * add to it. Flux is real currency — it is bought, or granted by the platform for watching a
   * platform ad. A game earning it would be a game printing money. Deleting wallet.set() from
   * the API below is not enough on its own, because emit() is a generic escape hatch and
   * `sdk.emit("gamehub:wallet:set", { fluxCoins: 1e9 })` is one line. So the refusal lives here,
   * at the only door out of the iframe.
   *
   * The achievement ones: the platform no longer has achievements at all. A game built against
   * the old SDK still calls these, and it deserves to be told so — in its own console, by name —
   * rather than emitting into a void for ever and wondering why nothing shows up.
   *
   * The platform rejects all of these too. This is the half that says why.
   */
  var FORBIDDEN_EMITS = {
    "gamehub:wallet:set": "A game cannot increase Flux Coins. Read with wallet.get(), take with wallet.spend().",
    "gamehub:wallet:add": "A game cannot increase Flux Coins. Read with wallet.get(), take with wallet.spend().",
    "gamehub:wallet:earn": "A game cannot increase Flux Coins. Read with wallet.get(), take with wallet.spend().",
    "gamehub:achievements:manifest": "The platform no longer has achievements. Track them inside your own game.",
    "gamehub:achievement:progress": "The platform no longer has achievements. Track them inside your own game.",
    // A casino round is answered BY the platform, never announced TO it. If a game could send a
    // result, it could send itself a win — which is the entire thing the casino design exists to
    // prevent. Sending a bet is how you play; sending a result is how you would cheat.
    "gamehub:casino:result": "A game cannot report its own casino result. Send a bet with casino.round() and the server will roll.",
  };

  function isObject(value) {
    return !!value && typeof value === "object" && !Array.isArray(value);
  }

  /** a < b, comparing dotted numeric versions. Missing parts count as 0. */
  function olderThan(a, b) {
    var left = String(a || "0").split(".");
    var right = String(b || "0").split(".");
    for (var i = 0; i < Math.max(left.length, right.length); i++) {
      var l = parseInt(left[i], 10) || 0;
      var r = parseInt(right[i], 10) || 0;
      if (l !== r) return l < r;
    }
    return false;
  }

  function GameHubSDK(options) {
    options = options || {};
    this.sessionId = null;
    this.targetOrigin = options.targetOrigin || "*";
    this.debug = !!options.debug;
    this.capabilities = {
      challenge: !!(options.capabilities && options.capabilities.challenge),
      pocketConsole: !!(options.capabilities && options.capabilities.pocketConsole),
      fullscreen: !options.capabilities || options.capabilities.fullscreen !== false,
      mute: !options.capabilities || options.capabilities.mute !== false,
      leaderboard: !options.capabilities || options.capabilities.leaderboard !== false,
    };
    this.handlers = {};
    // How many of handlers[type] are the SDK's own. Anything above this count is the game's,
    // and only the game's count as evidence that the game handles something.
    this._internalCounts = {};
    this.destroyed = false;
    this.context = { preview: false };

    // Acks. `_outSeq` numbers what we send; `_unityAcks` parks the id of a message we have
    // handed to C# and are waiting for it to answer for.
    this._outSeq = 0;
    this._unityAcks = {};
    this._dispatchErrors = 0;

    // The SDK version the platform that served us is on, learnt at handshake, and whether
    // we are behind it. Null until bridge:init arrives, and stays null when the host is
    // itself too old to say — an unknown platform version is not evidence of anything.
    this._platformVersion = null;
    this._stale = false;

    // ---- what the game ACTUALLY wired up -----------------------------------
    //
    // `capabilities` above is DECLARED — it defaults to true, so a game that does
    // nothing at all still claims it handles mute. Anything gated on it is theatre.
    //
    // This is different: each flag is set only when the game really registers a handler
    // or calls the API. It is what the platform checks before letting a game be
    // published, because "the platform sent gamehub:audio:set" and "the game muted itself" are
    // not the same fact, and only the second one matters to a player.
    this._wired = {
      mute: false,        // subscribed to gamehub:audio:set (the platform's volume button)
      fullscreen: false,  // subscribed to gamehub:screen:set, or asks for it
      data: false,        // uses the save API at all
      user: false,        // reads who the player is (needed for own-backend saves)
      wallet: false,
      ads: false,
      leaderboard: false,
      pocket: false,      // subscribed to gamehub:pocket:input (a phone as controller)
    };
    // Unity reports its own wiring from C# — the .jslib subscribes to everything on the
    // game's behalf, so inferring from JS handlers there would mark every Unity game as
    // compliant regardless of what its C# does. See setWiring() and UNITY_ACKS.
    this._autoWiring = options.engine !== "unity";
    this._autoAck = options.engine !== "unity";
    // Older Unity builds construct with { engine: "unity" } instead of calling setEngine, so
    // the save has to be requested down this path too. See _askForSave.
    if (options.engine === "unity") this._askForSave();

    this._onMessage = this._onMessage.bind(this);
    window.addEventListener("message", this._onMessage);

    var self = this;

    this._onInternal("gamehub:capabilities:get", function () { self._reportCapabilities(); });
    this._onInternal(ACK, function (payload) { self._onHostAck(payload); });
    this.challenge = {
      ready: function (payload) { self.emit("gamehub:challenge:ready", payload || {}); },
      updateState: function (payload) { self.emit("gamehub:challenge:state", payload || {}); },
      submitResult: function (payload) { self.emit("gamehub:challenge:result", payload || {}); },
      onStart: function (handler) { return self.on("gamehub:challenge:start", handler); },
      onLeaderboard: function (handler) { return self.on("gamehub:challenge:leaderboard", handler); },
      onEnd: function (handler) { return self.on("gamehub:challenge:end", handler); },
    };
    this.pocket = {
      ready: function (payload) { self.emit("gamehub:pocket:ready", payload || {}); },
      setControllerSchema: function (payload) { self.emit("gamehub:pocket:schema", payload || {}); },
      onInput: function (handler) { return self.on("gamehub:pocket:input", handler); },
      onPlayerJoined: function (handler) { return self.on("gamehub:pocket:player_joined", handler); },
      onPlayerReconnected: function (handler) { return self.on("gamehub:pocket:player_reconnected", handler); },
      onPlayerLeft: function (handler) { return self.on("gamehub:pocket:player_left", handler); },

      /**
       * Move every phone to a screen the controller declared.
       *
       * `data` is yours and opaque to every hop between here and the phone — nothing inspects a
       * key, supplies a default, or attaches meaning to a field name. It reaches the controller
       * as the `detail.data` of a `pocket:screen` event.
       *
       * Deliberately NOT wired via _wire(): `pocket` means "this game handles phone input", and
       * pushing a screen is not handling input. Two bits for one capability is how a game gets
       * reported as supporting Pocket Console when it reads nothing.
       */
      setState: function (screen, data) {
        self.emit("gamehub:pocket:state", { slot: null, screen: String(screen == null ? "" : screen), data: data || {} });
      },

      /**
       * Move ONE seat. This is the whole of multiplayer state: a game where the first finisher
       * ends it for everyone calls setState; a game where the others keep playing calls this for
       * the seat that finished. A race needs both — seat-targeted as players cross the line, then
       * setState("ranking") once all are done — which is why there is no mode to declare.
       *
       * A bad slot is logged rather than thrown: a game must not crash because it computed a seat
       * wrong, and a silent drop would be worse than either.
       */
      setSeatState: function (slot, screen, data) {
        var seat = Math.trunc(Number(slot));
        if (!isFinite(seat) || seat < 1) {
          self.log("warn", "pocket.setSeatState ignored: slot must be a whole number of 1 or more", { slot: slot, screen: screen });
          return;
        }
        self.emit("gamehub:pocket:state", { slot: seat, screen: String(screen == null ? "" : screen), data: data || {} });
      },
    };
    this.leaderboard = {
      // Declaring a board or posting a score IS using the leaderboard, so both mark it wired.
      // Without this, a game that submits scores but never subscribes to onSharing reported
      // leaderboard:false — the platform's assessment then showed "leaderboard not used" for a
      // game visibly posting scores. (_wire is a no-op in Unity mode, where C# reports its own
      // wiring; this is for web games, which infer wiring from what they call.)
      define: function (payload) { self._wire("leaderboard"); self.emit("gamehub:leaderboard:define", payload || {}); },
      submitScore: function (payload) { self._wire("leaderboard"); self.emit("gamehub:leaderboard:score", payload || {}); },
      onSharing: function (handler) { return self.on("gamehub:leaderboard:sharing", handler); },
    };

    // ---- Save data -------------------------------------------------------
    // The game stays the source of truth: it saves locally as it always did, and
    // this mirrors the map to the player's account so progress follows them to
    // another device.
    this._save = {
      cache: {},            // the map the game reads and writes, synchronously
      rev: 0,               // last rev the platform confirmed; we send rev + 1
      updatedAt: null,      // when the platform last accepted a write, ISO-8601
      loaded: false,
      mode: "no",
      loggedIn: false,
      flushTimer: null,
      lastSentHash: null,   // dirty check: skip a flush that would change nothing
      pending: null,        // resolve fns for flush() callers
      readyResolvers: [],
    };
    this._onInternal("gamehub:data:state", function (payload) { self._onDataState(payload); });
    this._onInternal("gamehub:data:error", function (payload) {
      var message = (payload && payload.message) || "Save failed.";
      if (console && console.warn) console.warn("[GameHubSDK] data: " + message);
      self._dispatch("gamehub:data:failed", { message: message });
    });

    this.data = {
      getItem: function (key) {
        self._wire("data");
        var value = self._save.cache[String(key)];
        return typeof value === "string" ? value : null;
      },
      setItem: function (key, value) {
        self._wire("data");
        if (!self._requireSaveMode() || !self._requireLoaded("setItem")) return;
        self._save.cache[String(key)] = String(value);
        self._scheduleFlush();
      },
      removeItem: function (key) {
        if (!self._requireSaveMode() || !self._requireLoaded("removeItem")) return;
        delete self._save.cache[String(key)];
        self._scheduleFlush();
      },
      keys: function () { return Object.keys(self._save.cache); },
      getAll: function () { return Object.assign({}, self._save.cache); },
      clear: function () {
        if (!self._requireSaveMode() || !self._requireLoaded("clear")) return;
        self._save.cache = {};
        self.emit("gamehub:data:clear", {});
      },
      flush: function () { return self._flush(true); },
      onChange: function (handler) { return self.on("gamehub:data:changed", handler); },
      isReady: function () { return self._save.loaded; },
      rev: function () { return self._save.rev; },
      updatedAt: function () { return self._save.updatedAt; },
    };

    // ---- Wallet ----------------------------------------------------------
    // Flux Coins are real currency, so the balance is whatever the SERVER says it is —
    // never what the game says it is.
    //
    // A game can READ the balance and ask to SPEND from it. There is no way to add to it,
    // and that is not an oversight: coins are bought from the platform, or granted by the
    // platform for watching a PLATFORM ad. A game that could add to the balance would be a
    // game printing money.
    //
    // This includes rewarded ads a game asks for. Those pay out in the GAME's own currency —
    // clear the boss, unlock the skin — and the game grants that itself. They do not pay Flux.
    this._wallet = { fluxCoins: null, currency: "flux", rate: 1, pending: [] };
    this._onInternal("gamehub:wallet:state", function (payload) {
      payload = payload || {};
      if (typeof payload.fluxCoins === "number") self._wallet.fluxCoins = payload.fluxCoins;
      if (typeof payload.currency === "string") self._wallet.currency = payload.currency;
      if (typeof payload.rate === "number") self._wallet.rate = payload.rate;
      self._resolveWallet({ ok: true, fluxCoins: self._wallet.fluxCoins });
      self._dispatch("gamehub:wallet:changed", self.wallet.get());
    });
    this._onInternal("gamehub:wallet:error", function (payload) {
      var message = (payload && payload.message) || "Wallet call failed.";
      self._resolveWallet({ ok: false, error: message, fluxCoins: self._wallet.fluxCoins });
      self._dispatch("gamehub:wallet:failed", { message: message });
    });

    this.wallet = {
      /** The last balance the platform sent. null until the first wallet:state arrives. */
      get: function () {
        return {
          fluxCoins: self._wallet.fluxCoins,
          currency: self._wallet.currency,
          rate: self._wallet.rate,
        };
      },
      /** Asks the platform for the current balance. Resolves with { ok, fluxCoins }. */
      fetch: function () {
        self._wire("wallet");
        self.emit("gamehub:wallet:get", { currency: self._wallet.currency, rate: self._wallet.rate });
        return self._awaitWallet();
      },
      /**
       * Spends `amount` coins. The SERVER checks the balance covers it, so this can
       * fail: resolves { ok: false, error } if the player cannot afford it. Do not
       * hand out whatever was bought until this resolves ok.
       *
       * This is the only way a game may move the balance, and it only moves it down.
       */
      spend: function (amount, reason) {
        var value = Number(amount);
        if (!isFinite(value) || value <= 0) {
          return Promise.resolve({ ok: false, error: "Spend amount must be a positive number." });
        }
        self.emit("gamehub:wallet:spend", { amount: value, reason: String(reason || "game") });
        return self._awaitWallet();
      },
      onChange: function (handler) { return self.on("gamehub:wallet:changed", handler); },
      onError: function (handler) { return self.on("gamehub:wallet:failed", handler); },
    };

    // ---- Casino ----------------------------------------------------------
    //
    // The one sanctioned way Flux can go UP from inside a game — and it is sanctioned precisely
    // because the game has no say in it.
    //
    //     YOU SEND A BET. YOU NEVER SEND A PAYOUT.
    //
    // Look at round() below: there is no parameter for an outcome, a multiplier or a payout.
    // Not because they are validated away — because they do not exist. The server owns the
    // paytable, owns the dice, and settles the money in one transaction. Your game is a
    // renderer for a result that has already happened.
    //
    // This only works at all if your game is registered as casino-class by an admin. It is not
    // something a game can opt into. Every other game calling round() gets refused, which is
    // why this module being present in the SDK for everyone is harmless.
    this._casino = { pending: {}, seq: 0 };

    // The FULL event name, exactly as the platform sends it. This said "casino:result" and the
    // platform sends "gamehub:casino:result", so the reply arrived, matched no handler, and every
    // round hung on "Rolling…" for ever. Nothing threw — a promise that is never resolved is
    // indistinguishable from one that is merely slow, which is why this looked like a hang and
    // not like a bug.
    this._onInternal("gamehub:casino:result", function (payload) {
      var key = payload && payload.roundKey;
      var entry = key ? self._casino.pending[key] : null;
      if (!entry) return;
      self._settleCasino(key, payload);
    });

    this.casino = {
      /**
       * Play one round. Resolves with the outcome the SERVER rolled:
       *
       *   { ok, outcome, multiplier, bet, payout, balance, nonce, roll, serverSeedHash }
       *
       * It can resolve `{ ok: false, code: "insufficient" }` — the player could not afford the
       * bet. That is an answer, not an error: show them a top-up, do not retry.
       *
       * `roundKey` is an idempotency key and it is UNIQUE server-side. If the network drops and
       * you retry with the same key, you get the SAME result back — you are not charged twice
       * and you do not get a second spin. Generate one per round and reuse it on retry.
       */
      round: function (options) {
        var opts = options || {};
        var bet = Math.round(Number(opts.bet));
        if (!isFinite(bet) || bet <= 0) {
          return Promise.resolve({ ok: false, error: "Bet must be a positive whole number." });
        }
        var mode = String(opts.mode || "").trim();
        if (!mode) {
          return Promise.resolve({ ok: false, error: "Missing casino mode." });
        }

        var key = String(opts.roundKey || "").trim() || self._newRoundKey();
        var promise = self._awaitCasino(key);
        self.emit("gamehub:casino:round", { mode: mode, bet: bet, roundKey: key });
        return promise;
      },

      /** The current commitment: { serverSeedHash, clientSeed, nonce }. */
      seed: function () {
        var key = self._newRoundKey();
        var promise = self._awaitCasino(key);
        self.emit("gamehub:casino:seed", { roundKey: key });
        return promise;
      },

      /**
       * Rotate the seed. This REVEALS the old server seed, so the player can recompute every
       * round they played against it and check we were not lying. Let them set their own
       * clientSeed — that is the half we do not control, and it is what makes the proof mean
       * something.
       */
      rotateSeed: function (clientSeed) {
        var key = self._newRoundKey();
        var promise = self._awaitCasino(key);
        self.emit("gamehub:casino:rotate", { roundKey: key, clientSeed: clientSeed || null });
        return promise;
      },
    };

    // ---- Mute ------------------------------------------------------------
    // Two directions, and both matter. The platform's volume button sends gamehub:audio:set;
    // the game must honour it or the button is a lie. When the game mutes itself, it
    // sends gamehub:audio:changed so the platform's icon matches what the player hears.
    this._muted = false;
    this._onInternal("gamehub:audio:set", function (payload) {
      var next = !!(payload && payload.muted);
      if (next === self._muted) return;
      self._muted = next;
      self._dispatch("gamehub:audio:muted", { muted: next, source: "platform" });
    });

    // ---- Ads -------------------------------------------------------------
    // The ad is a PLATFORM overlay. The game never renders it, never times it, and never
    // decides whether it was watched — a game cannot be trusted to report that, so the
    // decision stays outside the iframe. The game asks, pauses itself, and waits.
    //
    // What it pays out is the GAME's business. An ad the game asked for grants nothing in
    // Flux Coins: you clear the boss level, you unlock the skin, you refill the lives —
    // whatever your game's own economy says, granted by your own code when rewarded is true.
    //
    // (The platform has its own "watch an ad for Flux" button in its UI. That one is the
    // platform's, the player starts it deliberately, and it has nothing to do with a game.)
    this._ad = { pending: null };
    this._onInternal("gamehub:ad:state", function (payload) {
      payload = payload || {};
      var status = String(payload.status || "");
      if (status === "started") {
        self._dispatch("gamehub:ad:started", payload);
        return;
      }
      var resolve = self._ad.pending;
      self._ad.pending = null;
      var result = {
        rewarded: status === "rewarded",
        reason: payload.reason || null,
      };
      self._dispatch("gamehub:ad:finished", result);
      if (resolve) resolve(result);
    });

    this.ads = {
      /**
       * Shows a rewarded ad and resolves with { rewarded, reason }.
       *
       * `rewarded: true` means the player watched it to the end — now grant whatever YOUR
       * game promised them. `rewarded: false` means they skipped it or it failed: grant
       * nothing.
       *
       * This does not pay Flux Coins and never did anything useful with them. There is no
       * `balance` in the result, because there is no balance change to report.
       */
      showRewarded: function (payload) {
        self._wire("ads");
        if (self._ad.pending) return Promise.resolve({ rewarded: false, reason: "already-showing" });
        self.emit("gamehub:ad:show", Object.assign({ type: "rewarded" }, payload || {}));
        return new Promise(function (resolve) { self._ad.pending = resolve; });
      },
      onStarted: function (handler) { return self.on("gamehub:ad:started", handler); },
      onFinished: function (handler) { return self.on("gamehub:ad:finished", handler); },
    };

    /**
     * Who is playing.
     *
     * get() -> {
     *   loggedIn, userId, playerId, username, displayName, avatarPath, playerCode,
     *   email, emailShared
     * }
     *
     * `playerId` is the one to key your own records on: pseudonymous, stable for this
     * player in this game, and deliberately NOT comparable across games.
     *
     * `email` is null unless the platform granted this game the per-game email opt-in
     * and the game saves to its own backend — so it is null for most games, and for
     * every guest. `emailShared` tells you which of those two it is. Never build login
     * on it; it can be null forever and is not yours to assume.
     */
    this.user = {
      get: function () {
        return Object.assign({ loggedIn: self._save.loggedIn }, self._user || {});
      },
      onChange: function (handler) { return self.on("gamehub:user:state", handler); },
    };
    this._onInternal("gamehub:user:state", function (payload) {
      self._user = payload || {};
      self._save.loggedIn = !!(payload && payload.loggedIn);
    });

    // Closing the tab must not cost the player the last few seconds of play.
    // A debounced flush is still pending at that moment, so force it out now.
    // visibilitychange->hidden is the only event mobile browsers reliably fire.
    if (typeof document !== "undefined") {
      document.addEventListener("visibilitychange", function () {
        if (document.visibilityState === "hidden") self._flush(false);
      });
    }
    if (typeof window !== "undefined") {
      window.addEventListener("pagehide", function () { self._flush(false); });
    }
  }

  /** Resolves once the platform has handed us the player's save. */
  GameHubSDK.prototype.init = function () {
    var self = this;
    this._wire("data");

    // ASK, ALWAYS — even when the save is already here.
    //
    // The host pushes gamehub:data:state unprompted at the handshake, and a game cannot call
    // init() before the bridge exists, so the save has usually ALREADY arrived by the time
    // init() runs. This used to return early in that case without sending anything.
    //
    // Which meant the platform never saw the game touch the save API. Its publish gate looks
    // for a data:get, :set or :clear, so a game that called init() correctly and then simply
    // had not written yet — a quiz nobody had answered, a level nobody had finished — was
    // refused with "published as Platform save, but it never used the save API". The failure
    // depended on message ordering, so it looked intermittent and survived being "tested" by a
    // test that happened to call init() first.
    //
    // The extra ask costs one message and the host answers it with the state it already sent.
    self.emit("gamehub:data:get", {});

    if (this._save.loaded) return Promise.resolve(this.data.getAll());
    return new Promise(function (resolve) {
      self._save.readyResolvers.push(resolve);
    });
  };

  /**
   * Rule 2 of the save contract: nothing is written before the player's save arrives.
   *
   * Until it does, the game does not know whether this player is new — and on a browser they
   * have never used, everything local reads as "new". A write made in that window is this
   * browser's blank state, and it lands on top of the account save still in flight. That is not
   * a hypothetical: it is how a real player's progress was replaced by zeroes.
   *
   * Dropped and named, rather than queued. Queuing would preserve values the game computed from
   * a state it should never have acted on, which is the same bug with a delay.
   */
  GameHubSDK.prototype._requireLoaded = function (call) {
    if (this._save.loaded) return true;
    if (console && console.warn) {
      console.warn(
        "[GameHubSDK] data." + call + "() was called before the player's save arrived, so it was " +
        "dropped. Wait for init() to resolve (or data.isReady()) before writing — until then a " +
        "brand-new browser and a brand-new player look identical."
      );
    }
    return false;
  };

  GameHubSDK.prototype._requireSaveMode = function () {
    if (this._save.mode === "sdk") return true;
    if (console && console.warn) {
      console.warn(
        "[GameHubSDK] This game is not published with platform save enabled, so data.* is a no-op. " +
        "Set \"Save progress\" to the Data Module option when you publish."
      );
    }
    return false;
  };

  // Every wallet call is a round trip, and the platform answers with the same
  // wallet:state either way, so a caller cannot tell "my spend landed" from "someone
  // else's did". Queue the resolvers and settle them all on the next reply: the
  // balance in it is authoritative regardless of which call produced it.
  /**
   * How long a round may go unanswered before we call it lost.
   *
   * A pending promise nobody ever resolves does not throw, does not log, and does not time out —
   * it just sits there, and the game sits there with it, showing "Rolling…" for ever. That is
   * exactly the bug that shipped here: the reply arrived under a name the SDK was not listening
   * for, and the only symptom was a spinner.
   *
   * So a round now always ends. If the platform has not answered in this long, the promise
   * rejects with something a developer can act on, instead of failing silently and looking slow.
   */
  var CASINO_TIMEOUT_MS = 20000;

  /** Register a pending casino call, and guarantee it settles one way or the other. */
  GameHubSDK.prototype._awaitCasino = function (key) {
    var self = this;
    return new Promise(function (resolve) {
      var timer = setTimeout(function () {
        self._settleCasino(key, {
          roundKey: key,
          ok: false,
          code: "timeout",
          error:
            "The platform did not answer this round within " +
            CASINO_TIMEOUT_MS / 1000 +
            "s. The bet may or may not have been placed — retry with the SAME roundKey and you " +
            "will get the original result rather than a second spin.",
        });
      }, CASINO_TIMEOUT_MS);
      self._casino.pending[key] = { resolve: resolve, timer: timer };
    });
  };

  GameHubSDK.prototype._settleCasino = function (key, payload) {
    var entry = this._casino.pending[key];
    if (!entry) return;
    delete this._casino.pending[key];
    if (entry.timer) clearTimeout(entry.timer);
    entry.resolve(payload);
  };

  // An idempotency key for one round. Uniqueness only has to hold per player, and the server
  // enforces it anyway (the column is UNIQUE) — this just has to not collide with itself.
  GameHubSDK.prototype._newRoundKey = function () {
    var rand = "";
    try {
      if (typeof crypto !== "undefined" && crypto.getRandomValues) {
        var buf = new Uint8Array(8);
        crypto.getRandomValues(buf);
        for (var i = 0; i < buf.length; i++) rand += buf[i].toString(16).padStart(2, "0");
      }
    } catch (_e) {}
    if (!rand) rand = Math.random().toString(16).slice(2) + Math.random().toString(16).slice(2);
    return "r" + Date.now().toString(36) + "-" + (++this._casino.seq) + "-" + rand;
  };

  GameHubSDK.prototype._awaitWallet = function () {
    var self = this;
    return new Promise(function (resolve) { self._wallet.pending.push(resolve); });
  };

  GameHubSDK.prototype._resolveWallet = function (result) {
    var waiting = this._wallet.pending;
    this._wallet.pending = [];
    waiting.forEach(function (resolve) { resolve(result); });
  };

  GameHubSDK.prototype._hash = function (map) {
    // Stable: key order must not change the result, or every flush looks dirty
    // and the check buys nothing. JSON-encoding each pair keeps the delimiters
    // unambiguous, so {"a b":"c"} and {"a":"b c"} cannot collide.
    var keys = Object.keys(map).sort();
    var parts = [];
    for (var i = 0; i < keys.length; i++) {
      parts.push(JSON.stringify(keys[i]) + ":" + JSON.stringify(map[keys[i]]));
    }
    return parts.join(",");
  };

  GameHubSDK.prototype._scheduleFlush = function () {
    var self = this;
    if (this._save.flushTimer) return;
    // A game calling setItem in its update loop must not produce a request per
    // frame; coalesce the burst into one write.
    this._save.flushTimer = setTimeout(function () { self._flush(false); }, 1000);
  };

  GameHubSDK.prototype._flush = function (force) {
    var self = this;
    if (this._save.flushTimer) {
      clearTimeout(this._save.flushTimer);
      this._save.flushTimer = null;
    }
    if (this._save.mode !== "sdk") return Promise.resolve(false);

    var hash = this._hash(this._save.cache);
    // Most "save every 30s" games spend that time in a menu writing identical
    // data. Skipping the unchanged flush removes most writes for free.
    if (!force && hash === this._save.lastSentHash) return Promise.resolve(false);
    this._save.lastSentHash = hash;

    this.emit("gamehub:data:set", {
      data: Object.assign({}, this._save.cache),
      rev: this._save.rev + 1,
    });

    return new Promise(function (resolve) { self._save.pending = resolve; });
  };

  GameHubSDK.prototype._onDataState = function (payload) {
    payload = payload || {};
    var save = this._save;
    var incomingRev = Number(payload.rev);
    if (typeof payload.mode === "string") save.mode = payload.mode;
    if (typeof payload.loggedIn === "boolean") save.loggedIn = payload.loggedIn;

    var changed = false;
    if (isObject(payload.data)) {
      var next = payload.data;
      // The platform is authoritative here. This fires when the save first
      // arrives, after a guest map is merged up on login, or when our own write
      // was rejected as stale because another device is ahead of us — in every
      // case adopting it is right, and keeping our copy would roll the player back.
      if (this._hash(next) !== this._hash(save.cache)) changed = true;
      save.cache = Object.assign({}, next);
      save.lastSentHash = this._hash(save.cache);
    }
    if (Number.isFinite(incomingRev) && incomingRev >= 0) save.rev = incomingRev;
    if (typeof payload.updatedAt === "string" || payload.updatedAt === null) save.updatedAt = payload.updatedAt;

    var wasLoaded = save.loaded;
    save.loaded = true;

    if (save.pending) {
      var resolve = save.pending;
      save.pending = null;
      resolve(true);
    }

    if (!wasLoaded) {
      var resolvers = save.readyResolvers.slice();
      save.readyResolvers = [];
      var all = this.data.getAll();
      resolvers.forEach(function (fn) { fn(all); });
    }

    if (changed && wasLoaded) this._dispatch("gamehub:data:changed", this.data.getAll());
  };

  GameHubSDK.create = function (options) {
    return new GameHubSDK(options);
  };

  GameHubSDK.prototype.destroy = function () {
    this.destroyed = true;
    this.handlers = {};
    window.removeEventListener("message", this._onMessage);
  };

  /** The SDK's own subscriptions. Deliberately does NOT count as the game wiring anything
   *  up — otherwise every game would look compliant because the SDK subscribed for it. */
  GameHubSDK.prototype._onInternal = function (type, handler) {
    if (!this.handlers[type]) this.handlers[type] = [];
    this.handlers[type].push(handler);
    this._internalCounts[type] = (this._internalCounts[type] || 0) + 1;
    return function () {};
  };

  /** How many handlers on `type` belong to the GAME. The SDK's own do not count. */
  GameHubSDK.prototype._gameHandlers = function (type) {
    var total = (this.handlers[type] || []).length;
    return Math.max(0, total - (this._internalCounts[type] || 0));
  };

  /** Did the game do anything with this message? */
  GameHubSDK.prototype._isHandled = function (event) {
    // A handler that threw did not handle anything. Saying otherwise would send the
    // developer looking for a missing subscription that is right there.
    if (this._dispatchErrors > 0) return false;
    var types = ACK_PROOF[event] || [event];
    for (var i = 0; i < types.length; i++) {
      if (this._gameHandlers(types[i]) > 0) return true;
    }
    return false;
  };

  GameHubSDK.prototype._maybeAck = function (id, event) {
    if (!id || event === ACK) return;  // never acknowledge an acknowledgement
    if (!this._autoAck && UNITY_ACKS[event]) {
      // Unity answers this one itself. Park the id: the .jslib has just handed the message
      // to C#, and C# will call ackEvent() once it knows whether the game is listening.
      this._unityAcks[event] = id;
      return;
    }
    this.ack(id, event, this._isHandled(event));
  };

  /** Answers one message by id. */
  GameHubSDK.prototype.ack = function (id, event, handled) {
    if (!id) return;
    this._send(BRIDGE_EVENT, {
      event: ACK,
      name: ACK,
      payload: {
        id: String(id),
        event: String(event || ""),
        handled: !!handled,
        source: this._autoAck ? "sdk" : "unity",
      },
    });
  };

  /** Unity's answer for a message we parked in _maybeAck. Called from C# via the .jslib. */
  GameHubSDK.prototype.ackEvent = function (event, handled) {
    var id = this._unityAcks[event];
    if (!id) return;
    delete this._unityAcks[event];
    this.ack(id, event, handled);
  };

  /** The platform answering something WE sent. */
  GameHubSDK.prototype._onHostAck = function (payload) {
    payload = payload || {};
    if (payload.handled === false && console && console.warn) {
      // The platform received it and did nothing with it. Nearly always a misspelt event
      // name, which is otherwise completely silent — the game keeps emitting into a void.
      console.warn(
        "[GameHubSDK] the platform does not handle \"" + String(payload.event || "") + "\". " +
        "Check the event name — nothing is listening for it."
      );
    }
  };

  /** Fires when the platform answers a message this game sent. Payload: { id, event, handled }. */
  GameHubSDK.prototype.onAck = function (handler) {
    return this.on(ACK, handler);
  };

  /** Which requirement a given subscription satisfies. */
  var WIRES = {
    "gamehub:audio:set": "mute",
    "gamehub:screen:set": "fullscreen",
    "gamehub:data:changed": "data",
    "gamehub:user:state": "user",
    "gamehub:wallet:changed": "wallet",
    "gamehub:ad:finished": "ads",
    "gamehub:leaderboard:sharing": "leaderboard",
    "gamehub:audio:muted": "mute",
    "gamehub:pocket:input": "pocket",
  };

  GameHubSDK.prototype._wire = function (name) {
    if (this._autoWiring && name) this._wired[name] = true;
  };

  /**
   * Unity reports its own wiring, from C#.
   *
   * The .jslib subscribes to gamehub:audio:set, gamehub:screen:set and the rest on the game's behalf,
   * whether or not the game's C# does anything with them. So inferring wiring from JS
   * handlers in a Unity build would mark every Unity game as compliant — including one
   * that ignores the platform's volume button entirely. GameHubBridge.cs looks at its own
   * event subscriptions instead and tells us the truth.
   */
  GameHubSDK.prototype.setWiring = function (partial) {
    if (!isObject(partial)) return;
    for (var key in this._wired) {
      if (typeof partial[key] === "boolean") this._wired[key] = partial[key];
    }
    // Push it, do not wait to be asked. C# reports a frame into the game's life, which may
    // be long after the host gave up asking — a Unity build can take ten seconds to boot.
    this._reportCapabilities();
  };

  GameHubSDK.prototype.getWiring = function () {
    return Object.assign({}, this._wired);
  };

  /**
   * Switches an SDK that already exists into Unity mode.
   *
   * The .jslib cannot get this from create({ engine: "unity" }). The WebGL template loads
   * gamehub-sdk.js in <head> — deliberately, the build is not allowed to ship without it — so
   * by the time Unity's GameHubBridge_Init runs, window.GameHubBridge is already here and the
   * create() call is skipped entirely.
   *
   * Which means every Unity build was running in auto-wiring mode, inferring what the game
   * implements from JavaScript subscriptions... which in a Unity build are the .jslib's own,
   * made on the game's behalf, unconditionally. Every requirement came back "wired". That is
   * the exact false pass the wiring report exists to prevent, and it was hiding inside the
   * mechanism meant to prevent it.
   */
  GameHubSDK.prototype.setEngine = function (engine) {
    var unity = engine === "unity";
    this._autoWiring = !unity;
    this._autoAck = !unity;
    if (unity) {
      // Anything already inferred came from JS subscriptions, and in Unity those are not the
      // game's. C# is about to report the truth; start it from nothing.
      for (var key in this._wired) this._wired[key] = false;
      this._askForSave();
    }
  };

  /**
   * Requests the player's save on a Unity game's behalf.
   *
   * A web game asks in init(). Unity has no equivalent — nothing in the C# or the .jslib ever
   * asked — so the save arrived only if the host volunteered it, and the platform never saw the
   * game touch the save API at all. Every Unity game published as "Platform save" was refused
   * with "it never used the save API".
   *
   * It lives HERE, in the SDK, rather than in the .jslib on purpose. The .jslib is compiled
   * into a WebGL build and cannot change without a rebuild, but gamehub-sdk.js is loaded from
   * the platform's own origin at run time — so putting it here fixes games that were already
   * built, including ones nobody can rebuild any more.
   *
   * _wire() is a no-op in Unity mode, so this asks for the save without claiming the game uses
   * it. What the game implements is still reported by C#, from its own subscriptions.
   */
  GameHubSDK.prototype._askForSave = function () {
    var self = this;
    // After the handshake, so the host knows who is asking. Deferred rather than queued: the
    // engine is set during bridge init, which is the same turn the host is still setting up.
    setTimeout(function () {
      if (!self.destroyed) self.emit("gamehub:data:get", {});
    }, 0);
  };

  GameHubSDK.prototype._reportCapabilities = function () {
    this.emit("gamehub:capabilities:state", {
      sdk: "@gamehub/sdk",
      version: SDK_VERSION,
      // What the platform told us it is on, and whether we are behind it. Reported rather
      // than inferred by the host: only the SDK knows which version it actually is.
      platformVersion: this._platformVersion,
      stale: this._stale,
      // What the game SAYS it supports. Defaults to true — do not gate on it.
      declared: Object.assign({}, this.capabilities),
      // What the game actually wired up. Gate on this.
      wired: this.getWiring(),
      saveMode: this._save.mode,
    });
  };

  GameHubSDK.prototype.on = function (type, handler) {
    this._wire(WIRES[type]);
    if (!this.handlers[type]) this.handlers[type] = [];
    this.handlers[type].push(handler);
    var list = this.handlers[type];
    return function () {
      var index = list.indexOf(handler);
      if (index >= 0) list.splice(index, 1);
    };
  };

  /** Sends an event to the platform. Returns the id the platform will acknowledge it by. */
  GameHubSDK.prototype.emit = function (event, payload) {
    var refusal = FORBIDDEN_EMITS[event];
    if (refusal) {
      // Refused here rather than sent-and-rejected, so it is impossible to mistake for a
      // network problem or a platform bug. The message never leaves the iframe.
      if (console && console.error) console.error("[GameHubSDK] refusing to send \"" + event + "\". " + refusal);
      return null;
    }
    var id = "g" + (++this._outSeq);
    this._send(BRIDGE_EVENT, { id: id, event: event, name: event, payload: payload || {} });
    return id;
  };

  GameHubSDK.prototype.log = function (level, message, data) {
    this._send(BRIDGE_LOG, { level: level, message: message, data: data || null });
  };

  GameHubSDK.prototype.requestPlatformFullscreen = function (orientation) {
    this._wire("fullscreen");
    this.emit("gamehub:screen:request", { orientation: orientation || "auto" });
  };

  /** Tells the platform the game muted/unmuted itself, so its volume icon matches. */
  GameHubSDK.prototype.setMuted = function (muted) {
    this._wire("mute");
    var next = !!muted;
    // The platform echoes its own gamehub:audio:set back to us. Without this guard that echo
    // would bounce straight back out as gamehub:audio:changed and the two would ping-pong.
    if (next === this._muted) return;
    this._muted = next;
    this.emit("gamehub:audio:changed", { muted: next });
    this._dispatch("gamehub:audio:muted", { muted: next, source: "game" });
  };

  GameHubSDK.prototype.isMuted = function () {
    return !!this._muted;
  };

  /** Fires whenever mute changes, from either side. Payload: { muted, source }. */
  GameHubSDK.prototype.onMute = function (handler) {
    return this.on("gamehub:audio:muted", handler);
  };

  GameHubSDK.prototype.requestLogin = function (reason) {
    this.emit("gamehub:auth:login", { reason: reason || "game" });
  };

  GameHubSDK.prototype.getSessionId = function () {
    return this.sessionId;
  };

  GameHubSDK.prototype.getContext = function () {
    return Object.assign({}, this.context);
  };

  GameHubSDK.prototype.isPreview = function () {
    return !!(this.context && this.context.preview);
  };

  GameHubSDK.prototype.onContext = function (handler) {
    var unsubscribe = this.on("gamehub:context", handler);
    handler(this.getContext());
    return unsubscribe;
  };

  GameHubSDK.prototype._onMessage = function (event) {
    var data = event.data;
    if (this.destroyed || !isObject(data) || typeof data.type !== "string") return;
    if (data.type === BRIDGE_INIT) {
      if (typeof data.sessionId === "string") this.sessionId = data.sessionId;
      this.context = {
        role: typeof data.role === "string" ? data.role : this.context.role,
        preview: data.preview === true || data.role === "dashboard-preview",
        sessionId: this.sessionId || undefined,
        gameId: typeof data.gameId === "string" ? data.gameId : undefined,
        slug: typeof data.slug === "string" ? data.slug : undefined,
        embedType: typeof data.embedType === "string" ? data.embedType : undefined,
        orientation: typeof data.orientation === "string" ? data.orientation : undefined,
        testUser: isObject(data.testUser)
          ? {
              id: String(data.testUser.id || "preview-user"),
              username: typeof data.testUser.username === "string" ? data.testUser.username : undefined,
              displayName: typeof data.testUser.displayName === "string" ? data.testUser.displayName : undefined,
              email: typeof data.testUser.email === "string" ? data.testUser.email : null,
              test: data.testUser.test === true,
              local: data.testUser.local === true,
            }
          : undefined,
      };
      // What SDK the platform itself is on. An older host does not send this at all, so
      // "no answer" means "cannot tell", not "you are current".
      if (typeof data.sdkVersion === "string" && data.sdkVersion) {
        this._platformVersion = data.sdkVersion;
        this._stale = olderThan(SDK_VERSION, data.sdkVersion);
      }

      this._send(BRIDGE_READY, {
        sdk: "@gamehub/sdk",
        version: SDK_VERSION,
        capabilities: this.capabilities,
        preview: this.context.preview,
      });
      this._dispatch("gamehub:context", this.getContext());
      this.log("info", "GameHub SDK ready");

      // Said in the game's OWN console, because that is where the developer is looking.
      // The platform says it too, on the assessment screen — but a developer running the
      // game locally never sees that screen, and a stale SDK is silent by nature: it does
      // not error, it just fails to answer questions it has never heard of.
      if (this._stale) {
        var warn = console && (console.warn || console.log);
        if (warn) {
          warn.call(
            console,
            "[GameHubSDK] this game bundles SDK " + SDK_VERSION + ", but the platform is on " +
            this._platformVersion + ". Update the SDK and rebuild — an out-of-date SDK cannot " +
            "answer checks it does not know about, and the platform will not publish a game it " +
            "cannot verify."
          );
        }
        this.log("warn", "SDK " + SDK_VERSION + " is older than the platform's " + this._platformVersion);
      }
      return;
    }
    var eventType = data.type === BRIDGE_EVENT && typeof data.event === "string" ? data.event : data.type;
    var payload = data.type === BRIDGE_EVENT && isObject(data.payload) ? data.payload : data;

    // Reset before the top-level dispatch, not inside it: handling gamehub:audio:set runs a nested
    // dispatch of gamehub:audio:muted, and a throw in the game's mute handler happens down
    // there. It still has to count against the ack for gamehub:audio:set.
    this._dispatchErrors = 0;

    // Unity's ack id is parked BEFORE the dispatch, and only Unity's.
    //
    // SendMessage into Unity is synchronous, so the whole chain — .jslib handler, C#
    // OnGameHubMuted, C# Ack(), ackEvent() — runs to completion inside _dispatch below.
    // Parking afterwards meant ackEvent() looked for an id that had not been parked yet,
    // found nothing, and took its `if (!id) return` — dropping the answer silently. The id
    // was then parked for a reply that had already come and gone, so it sat there for ever
    // and the platform never heard from the game at all.
    //
    // What it saw instead was the auto-ack from the probe sent before Unity had booted,
    // which correctly reported handled:false — nothing was listening yet. That "no" was the
    // game's only answer on record, while C# reported the wiring as present, and a game that
    // handles mute perfectly failed to publish for not answering a question it had answered.
    //
    // The auto-ack path still runs AFTER the dispatch: it reads _dispatchErrors and the
    // handler count, and both only mean anything once the handlers have actually run.
    var id = typeof data.id === "string" ? data.id : null;
    var parked = false;
    if (id && !this._autoAck && UNITY_ACKS[eventType] && eventType !== ACK) {
      this._unityAcks[eventType] = id;
      parked = true;
    }
    this._dispatch(eventType, payload);
    if (id && !parked) this._maybeAck(id, eventType);
  };

  GameHubSDK.prototype._dispatch = function (type, payload) {
    if (this.debug && console && console.debug) console.debug("[GameHubSDK] recv", type, payload);
    var self = this;
    var list = this.handlers[type] || [];
    list.slice().forEach(function (handler) {
      // One game's broken handler must not take the bridge down with it. Without this, a
      // throw here escapes into the window's message listener and every later message in
      // the same dispatch is skipped — including the ack that would have reported it.
      try {
        handler(payload);
      } catch (err) {
        self._dispatchErrors++;
        if (console && console.error) console.error("[GameHubSDK] a handler for " + type + " threw", err);
      }
    });
  };

  GameHubSDK.prototype._send = function (type, payload) {
    if (!window.parent) return;
    var message = Object.assign({ type: type, sessionId: this.sessionId || undefined }, payload || {});
    if (this.debug && console && console.debug) console.debug("[GameHubSDK] send", message);
    window.parent.postMessage(message, this.targetOrigin);
  };

  GameHubSDK.prototype.getVersion = function () {
    return SDK_VERSION;
  };

  /** Readable without constructing anything: `window.GameHubSDK.VERSION` in the console. */
  GameHubSDK.VERSION = SDK_VERSION;

  window.GameHubSDK = GameHubSDK;
  window.GameHubBridge = window.GameHubBridge || GameHubSDK.create({
    debug: false,
      capabilities: { challenge: true, pocketConsole: true, fullscreen: true, mute: true, leaderboard: true },
    });
})();
