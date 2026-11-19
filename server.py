"""Multiplayer server for the card game "31".

The server is the referee: it owns the deck, every hand, the rules, the computer
players and all timers. Browsers only show what it sends and send taps.
Rules are a 1:1 port of the single-player game ("31 prototype 1.3.html").

Run locally:
    pip install websockets==15.0.1
    python server.py            # listens on 0.0.0.0:8765
    PORT=9000 TIME_SCALE=0.1 python server.py   # other port, 10x faster timers

Open http://localhost:8765/ in a browser to check it is up: it answers
"ok - 31 server <version>, started <date time UTC>".

Render settings (Web Service):
    Build command:  pip install websockets==15.0.1
    Start command:  python server.py
    After a deploy, open the service address: the version and start time
    there tell you which copy is running.
    (Render sets PORT itself; the health check path can stay "/".)

Layout of this file: game rules (Game, bots), Hub (rooms, quick match, tokens,
timers, broadcast; no network code), then a thin websockets handler and main().
Nothing personal is logged: only counts, connects and errors.
"""

import asyncio
import json
import logging
import os
import random
import secrets
import string
import time
from datetime import datetime, timezone
from http import HTTPStatus

log = logging.getLogger("31")

# ---------------------------------------------------------------- settings

SERVER_VERSION = "1.1"     # raise with every change you deploy; shown at "/", in the log and in "welcome"
STARTED = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")   # when this copy of the server started
TIME_SCALE = 1.0          # multiplies every delay (tests use a tiny value)

MOVE_MS = 20000           # human move timer
TURN_DELAY_MS = 1000      # extra time before a human's timer starts
BET_EXTRA_MS = 1400       # added to a human's timer after a bet
DISCONNECTED_MS = 5000    # a disconnected human's seat acts after this
DEAL_WAIT_MS = 15 * 90 + 800
THINK_MS = 1200
THINK_RANDOM_MS = 400
SHOW_MS = 1700            # a computer swap is announced this long before it happens
BET_WAIT_MS = 1400        # computer waits this long after a bet
REVEAL_MS = 4500          # client showdown
REVEAL_BIG_MS = 3200      # extra for 31 / Fire
REVEAL_BACKFIRE_MS = 3200  # extra when a knock backfired
END_WAIT_MS = 20000       # wait for the next round after the showdown
TOKEN_KEEP_MS = 10 * 60 * 1000
QUICK_WAIT_MS = 20000
MAX_NAME = 12
RESTORE_MS = 10000        # a returning player gets at least this long for the current turn
IDLE_TURNS = 3            # timeouts in a row before a computer player takes over
MAX_CONNECTIONS = 300     # simple caps against flooding
MAX_ROOMS = 150

SUITS = ["♠", "♥", "♦", "♣"]
RANKS = ["7", "8", "9", "10", "J", "Q", "K", "A"]


def secs(ms):
    """Scaled delay in seconds."""
    return ms * TIME_SCALE / 1000.0


# ---------------------------------------------------------------- scoring
# A card is a tuple (rank, suit).

def card_value(c):
    r = c[0]
    if r == "A":
        return 11
    if r in ("J", "Q", "K"):
        return 10
    return int(r)


def score_hand(hand):
    if len(hand) == 3 and all(c[0] == "A" for c in hand):
        return 32                                   # Fire
    if len(hand) == 3 and hand[0][0] == hand[1][0] == hand[2][0]:
        return 30.5                                 # three of a kind
    sums = {}
    best = 0
    for c in hand:
        sums[c[1]] = sums.get(c[1], 0) + card_value(c)
        if sums[c[1]] > best:
            best = sums[c[1]]
    return best


def fmt_score(x):
    return str(int(x)) if x == int(x) else str(x)


def card_json(c):
    return None if c is None else {"r": c[0], "s": c[1]}


def suit_sums(hand):
    m = {}
    for c in hand:
        m[c[1]] = m.get(c[1], 0) + card_value(c)
    return sorted(m.values(), reverse=True)


def hand_key(hand):
    s = suit_sums(hand)
    return score_hand(hand) + (s[1] if len(s) > 1 else 0) / 100.0


def all_swaps(hand, middle):
    out = []
    for h in range(3):
        for m in range(3):
            nh = list(hand)
            nh[h] = middle[m]
            out.append(({"type": "swap", "h": h, "m": m}, nh))
    out.append(({"type": "all"}, list(middle)))
    return out


# ---------------------------------------------------------------- game

class Player:
    __slots__ = ("name", "bot", "lives", "out", "hand", "knock_at", "bet_used", "staked")

    def __init__(self, name, bot, lives, knock_at):
        self.name = name
        self.bot = bot
        self.lives = lives
        self.out = False
        self.hand = []
        self.knock_at = knock_at     # computer players knock at 25-28
        self.bet_used = False        # one heart bet per whole game
        self.staked = False          # bet heart on the table this round


class Game:
    """Pure game logic. No timers, no network. Seats are 0-3 (absolute)."""

    def __init__(self, cfg, lives=3, bet_on=False, rng=None):
        # cfg: list of 4 (name, bot) pairs
        self.rng = rng or random.SystemRandom()
        self.bet_on = bool(bet_on)
        self.players = [Player(n, b, lives, 25 + self.rng.randrange(4)) for n, b in cfg]
        self.deck = []
        self.discard = []
        self.middle = []
        self.middle_hidden = True
        self.dealer = self.rng.randrange(4)          # first dealer is random
        self.turn = 0
        self.knocker = None
        self.passes = 0
        self.turns = 0
        self.phase = "dealer"      # dealer | play | showdown | over
        self.round = 0
        self.result = None
        self.winner = None         # seat, or None (draw when game over)
        self.events = []
        self.start_round(True)

    # -- helpers
    def active(self):
        return [i for i, p in enumerate(self.players) if not p.out]

    def next_active(self, i):
        for k in range(1, 5):
            j = (i + k) % 4
            if not self.players[j].out:
                return j
        return i

    def make_deck(self):
        d = [(r, s) for s in SUITS for r in RANKS]
        self.rng.shuffle(d)
        return d

    # -- round flow
    def start_round(self, first):
        self.deck = self.make_deck()
        self.discard = []
        self.round += 1
        self.knocker = None
        self.result = None
        self.passes = 0
        self.turns = 0
        if not first:
            self.dealer = self.next_active(self.dealer)
        for p in self.players:
            if p.out:
                p.hand = []
            else:
                p.hand, self.deck = self.deck[:3], self.deck[3:]
        self.middle, self.deck = self.deck[:3], self.deck[3:]
        self.middle_hidden = True
        self.phase = "dealer"
        self.turn = self.dealer
        self.events = [{"t": "deal"}]

    def next_round(self):
        if self.phase == "showdown":
            self.start_round(False)

    def dealer_decide(self, take):
        if self.phase != "dealer":
            return "Not the dealer phase"
        p = self.players[self.dealer]
        if take:
            p.hand, self.middle = self.middle, p.hand
        self.middle_hidden = False
        self.phase = "play"
        self.turns = 1       # the dealer's choice counts as the dealer's turn
        self.turn = self.next_active(self.dealer)
        self.events = [{"t": "take" if take else "keep", "pi": self.dealer}]
        if any(score_hand(self.players[i].hand) >= 31 for i in self.active()):
            self.end_round()
        return None

    def knock_open(self):
        return self.turns >= len(self.active())

    def can_knock(self):
        return self.phase == "play" and self.knocker is None and self.knock_open()

    def can_bet(self, pi):
        p = self.players[pi]
        return (self.bet_on and self.phase == "play" and not p.out
                and not p.bet_used and p.lives >= 2)

    def refresh_middle(self):
        self.discard.extend(self.middle)
        if len(self.deck) < 3:
            d = list(self.discard)
            self.rng.shuffle(d)
            self.deck = self.deck + d
            self.discard = []
        self.middle, self.deck = self.deck[:3], self.deck[3:]
        self.passes = 0

    def do_move(self, pi, move):
        """Returns None when done, or an error text. move: {'type': ...}"""
        if self.phase != "play" or self.turn != pi:
            return "Not your turn"
        p = self.players[pi]
        t = move.get("type")
        if t == "bet":
            if not self.can_bet(pi):
                return "You cannot bet a heart now"
            p.bet_used = True
            p.staked = True
            p.lives -= 1
            self.refresh_middle()
            self.events = [{"t": "bet", "pi": pi}]
            return None            # extra action: the same player still moves
        if t == "knock" and not self.can_knock():
            return "You cannot knock now"
        self.events = []
        if t == "swap":
            h, m = move["h"], move["m"]
            p.hand[h], self.middle[m] = self.middle[m], p.hand[h]
            self.passes = 0
            self.events.append({"t": "swap", "pi": pi, "h": h, "m": m})
        elif t == "all":
            p.hand, self.middle = self.middle, p.hand
            self.passes = 0
            self.events.append({"t": "all", "pi": pi})
        elif t == "pass":
            self.passes += 1
            self.events.append({"t": "pass", "pi": pi})
        elif t == "knock":
            self.knocker = pi
            self.passes = 0
            self.events.append({"t": "knock", "pi": pi})
        else:
            return "Unknown move"
        self.finish_turn()
        return None

    def finish_turn(self):
        mover = self.turn
        self.turns += 1
        if score_hand(self.players[mover].hand) >= 31:
            self.end_round()
            return
        if self.passes >= len(self.active()):
            self.refresh_middle()
            self.events.append({"t": "refresh"})
        nxt = self.next_active(mover)
        if self.knocker is not None and nxt == self.knocker:
            self.end_round()
            return
        self.turn = nxt

    # -- settlement (done at once; the client shows the showdown afterwards)
    def end_round(self):
        self.phase = "showdown"
        self.middle_hidden = False
        act = self.active()
        sc = {i: score_hand(self.players[i].hand) for i in act}
        name = lambda i: self.players[i].name
        fire = [i for i in act if sc[i] == 32]
        s31 = [i for i in act if sc[i] == 31]
        if fire:
            losers = [i for i in act if sc[i] != 32]
            head = name(fire[0]) + " has Fire (three Aces)! Everyone else loses a heart."
        else:
            low = min(sc.values())
            losers = [i for i in act if sc[i] == low]
            # the knocker only pays when strictly lowest
            if self.knocker is not None and len(losers) > 1 and self.knocker in losers:
                losers.remove(self.knocker)
            head = ((" & ".join(name(i) for i in s31) + " made 31. ") if s31 else "") + \
                "Lowest hand: " + ", ".join("%s (%s)" % (name(i), fmt_score(low)) for i in losers) + "."
        top = max(sc.values())
        rows = []
        for i in act:
            p = self.players[i]
            s = sc[i]
            lost = i in losers
            pen = (2 if (not fire and i == self.knocker) else 1) if lost else 0
            bet = 1 if p.staked else 0
            before = p.lives + bet
            total = pen + bet if lost else 0
            after = max(0, before - total)
            rows.append({
                "pen": pen, "bet": bet, "total": total, "i": i, "score": s,
                "hand": list(p.hand),
                "outcome": ("out" if after == 0 else "lose") if lost else ("win" if s == top else "safe"),
                "special": "Fire" if s == 32 else "Schnauz" if s == 31 else
                           "Three of a kind" if s == 30.5 else "",
                "before": before, "after": after,
            })
        rows.sort(key=lambda r: -r["score"])      # stable, best first
        big = (fire[0] if fire else s31[0]) if (fire or s31) else None
        if fire:
            title = name(fire[0]) + " has Fire!"
        elif s31:
            title = " & ".join(name(i) for i in s31) + " made 31!"
        else:
            title = "Round %d" % self.round
        back = next((r["i"] for r in rows if r["pen"] == 2), None)
        self.result = {"title": title, "head": head, "notes": [], "rows": rows,
                       "big": ("fire" if fire else "s31") if big is not None else None,
                       "backfire": back}
        self.apply_result(losers, rows)
        self.events.append({"t": "end"})

    def apply_result(self, losers, rows):
        # staked hearts go back first; losers then pay their loss plus the bet heart
        for r in rows:
            if r["bet"]:
                q = self.players[r["i"]]
                q.lives += r["bet"]
                q.staked = False
        notes = []
        for i in losers:
            r = next(x for x in rows if x["i"] == i)
            notes.append(self.players[i].name + " " + self.lose_life(self.players[i], r["pen"], r["bet"]))
        self.result["notes"] = notes
        left = self.active()
        if len(left) <= 1:
            self.phase = "over"
            self.winner = left[0] if left else None
        # else the phase stays 'showdown'

    @staticmethod
    def lose_life(p, pen, bet):
        pen = pen or 1
        bet = bet or 0
        n = pen + bet
        p.lives -= n
        why = (" (knocked and lost: 2 hearts)" if pen == 2 else "") + \
              (" (bet lost: 1 extra heart)" if bet else "")
        if p.lives <= 0:
            p.lives = 0
            p.out = True
            return "is out" + why
        return ("loses %d hearts" % n if n >= 2 else "loses a heart") + why

    # -- computer players
    def bot_dealer_takes(self, pi):
        return score_hand(self.players[pi].hand) < 17 + self.rng.random() * 3

    def bot_choose(self, pi):
        p = self.players[pi]
        cur = score_hand(p.hand)
        cur_key = hand_key(p.hand)
        swaps = all_swaps(p.hand, self.middle)
        best = None
        for mv, nh in swaps:
            k, s = hand_key(nh), score_hand(nh)
            if best is None or k > best[1] or (k == best[1] and self.rng.random() < 0.3):
                best = (mv, k, s)
        if best[2] >= 31:
            return best[0]                       # always take 31 or Fire
        if self.can_knock() and cur >= p.knock_at:
            return {"type": "knock"}
        # Heart bet: cautious, weak hand, nothing gains 5+, not in the opening round of turns
        if (self.can_bet(pi) and self.knock_open() and (p.lives >= 3 or cur < 14) and cur < 20
                and max(score_hand(nh) for _, nh in swaps) - cur < 5):
            return {"type": "bet"}
        if best[1] > cur_key:
            return best[0]
        return {"type": "pass"}


# ---------------------------------------------------------------- hub

def clean_name(v):
    if not isinstance(v, str):
        return "Player"
    v = "".join(ch for ch in v if ch.isprintable()).strip()[:MAX_NAME].strip()
    return v or "Player"


class Member:
    """A person (one token). May have a connection (link), a room seat, a queue slot."""

    def __init__(self):
        self.token = secrets.token_urlsafe(16)
        self.name = "Player"
        self.link = None
        self.room = None
        self.seat = None
        self.queued = False
        self.since = 0.0
        self.expire = None


class Link:
    """One connection with its outgoing message queue."""

    def __init__(self, conn):
        self.conn = conn
        self.member = None
        self.q = asyncio.Queue()
        self.task = None


class Seat:
    __slots__ = ("kind", "member", "name")

    def __init__(self, kind="empty", member=None, name=""):
        self.kind = kind          # empty | human | bot
        self.member = member      # None for a human that left (seat plays on automatically)
        self.name = name

    def connected(self):
        return self.kind == "bot" or (self.member is not None and self.member.link is not None)


class Room:
    def __init__(self, hub, code, hearts=3, bet=False):
        self.hub = hub
        self.code = code
        self.hearts = hearts
        self.bet = bool(bet) and hearts >= 2      # a heart bet needs 2+ hearts
        self.seats = [Seat() for _ in range(4)]
        self.host = 0
        self.mode = "lobby"        # lobby | game
        self.game = None
        self.task = None
        self.pending = None        # computer swap being shown
        self.event = None          # events of the last action (cleared after one broadcast)
        self.ready = set()
        self.turn_key = None
        self.deadline = 0.0
        self.timer_total = 0
        self.end_deadline = 0.0
        self.end_total = 0
        self.misses = [0] * 4      # timeouts in a row per seat
        self.away = [False] * 4    # idle human seat played by the computer
        self.deleted = False

    # -- seats
    def humans(self):
        return [i for i, s in enumerate(self.seats) if s.kind == "human" and s.member is not None]

    def add_human(self, member):
        for i, s in enumerate(self.seats):
            if s.kind == "empty":
                s.kind, s.member, s.name = "human", member, member.name
                member.room, member.seat = self, i
                return i
        return None

    # -- sending
    def broadcast(self):
        for i in self.humans():
            m = self.seats[i].member
            if m.link is None:
                continue
            m.send(self.lobby_for(i) if self.mode == "lobby" else self.state_for(i))
        self.event = None

    def lobby_for(self, seat):
        return {"t": "lobby", "code": self.code, "host": self.host, "you": seat,
                "seats": [{"name": s.name if s.kind != "empty" else "", "kind": s.kind,
                           "connected": s.connected()} for s in self.seats],
                "hearts": self.hearts, "bet": self.bet}

    def state_for(self, viewer):
        g = self.game
        v = lambda a: None if a is None else (a - viewer) % 4
        showdown = g.phase in ("showdown", "over")
        players = []
        for k in range(4):
            a = (viewer + k) % 4
            p = g.players[a]
            if p.out and a != viewer and not showdown:
                hand = []
            elif a == viewer or showdown:
                hand = [card_json(c) for c in p.hand]
            else:
                hand = [None] * len(p.hand)
            players.append({"name": p.name, "seat": a, "bot": p.bot,
                            "connected": self.seats[a].connected(), "away": self.away[a],
                            "lives": p.lives, "out": p.out, "betUsed": p.bet_used,
                            "staked": p.staked, "hand": hand})
        middle = [None] * 3 if (g.middle_hidden and not showdown) else [card_json(c) for c in g.middle]
        on_turn = g.phase in ("dealer", "play") and g.turn == viewer and not g.players[viewer].out
        can_knock = bool(on_turn and g.phase == "play" and g.can_knock())
        can_bet = bool(on_turn and g.phase == "play" and g.can_bet(viewer))
        timer = None
        if g.phase in ("dealer", "play") and self.turn_key and not g.players[g.turn].bot \
                and not self.away[g.turn] and self.seats[g.turn].member is not None:
            left = max(0.0, (self.deadline - time.monotonic()) * 1000.0 / max(TIME_SCALE, 1e-9))
            timer = {"left": int(left), "total": int(self.timer_total)}
        ev = None
        if self.pending:
            ev = {"t": "pending", "pi": v(self.pending["pi"]), "move": self.pending["move"]}
        events = [self._ev_view(e, v) for e in (self.event or [])]
        if ev is None and events:
            ev = events[-1]
        result = None
        next_in = None
        if showdown and g.result:
            result = self._result_view(g.result, v)
            next_in = int(max(0.0, (self.end_deadline - time.monotonic()) * 1000.0
                              / max(TIME_SCALE, 1e-9)))
        return {"t": "state", "code": self.code, "round": g.round, "phase": g.phase,
                "players": players, "middle": middle,
                "dealer": v(g.dealer), "turn": v(g.turn), "knocker": v(g.knocker),
                "passes": g.passes, "turns": g.turns,
                "canKnock": can_knock, "canBet": can_bet, "timer": timer,
                "event": ev, "events": events if not self.pending else [],
                "result": result, "nextIn": next_in,
                "winner": v(g.winner) if g.phase == "over" else None,
                "draw": g.phase == "over" and g.winner is None}

    @staticmethod
    def _ev_view(e, v):
        e = dict(e)
        if "pi" in e:
            e["pi"] = v(e["pi"])
        return e

    @staticmethod
    def _result_view(res, v):
        rows = []
        for r in res["rows"]:
            r = dict(r)
            r["i"] = v(r["i"])
            r["hand"] = [card_json(c) for c in r["hand"]]
            rows.append(r)
        return {"title": res["title"], "head": res["head"], "notes": list(res["notes"]),
                "rows": rows, "big": res["big"], "backfire": v(res["backfire"])}

    # -- starting and ending a game
    def start(self):
        cfg = []
        for i, s in enumerate(self.seats):
            if s.kind == "empty":
                s.kind, s.member, s.name = "bot", None, "CPU %d" % (i + 1)
            cfg.append((s.name, s.kind == "bot"))
        self.game = Game(cfg, self.hearts, self.bet)
        self.misses = [0] * 4
        self.away = [False] * 4
        self.mode = "game"
        self.ready = set()
        self.pending = None
        self.turn_key = None
        self.event = self.game.events
        self.after_action()

    def to_lobby(self):
        for s in self.seats:
            if s.kind == "bot" or (s.kind == "human" and s.member is None):
                s.kind, s.member, s.name = "empty", None, ""
        self.mode = "lobby"
        self.game = None
        self.pending = None
        self.event = None
        self.ready = set()
        self.cancel_task()
        if not self.humans():
            self.hub.delete_room(self)
            return
        if self.seats[self.host].kind != "human":
            self.host = self.humans()[0]
        self.broadcast()

    def remove_member(self, member):
        """A human leaves (or its token expired)."""
        seat = member.seat
        member.room, member.seat = None, None
        if seat is None:
            return
        s = self.seats[seat]
        if self.mode == "lobby":
            s.kind, s.member, s.name = "empty", None, ""
        else:
            # gone for good: a computer player takes the seat for the rest of this game
            s.kind, s.member, s.name = "bot", None, "CPU %d" % (seat + 1)
            self.game.players[seat].bot = True
            self.game.players[seat].name = s.name
            self.away[seat] = False
        if not self.humans():
            self.hub.delete_room(self)
            return
        if self.mode == "lobby" and self.host == seat:
            self.host = self.humans()[0]
        self.broadcast()
        if self.mode == "game" and self.game.phase in ("dealer", "play") and self.game.turn == seat:
            self.pending = None
            self.reschedule()      # the computer plays the seat now, with normal pacing

    def restore_timer(self, seat):
        """A player came back on their own turn: give the move time back."""
        g = self.game
        if self.mode != "game" or g.phase not in ("dealer", "play") or g.turn != seat \
                or g.players[seat].bot or self.away[seat] or not self.turn_key:
            return
        now = time.monotonic()
        self.deadline = min(max(self.deadline, now + secs(RESTORE_MS)),
                            now + secs(self.timer_total))
        self.reschedule()

    # -- timers
    def cancel_task(self):
        cur = asyncio.current_task()
        if self.task is not None and self.task is not cur and not self.task.done():
            self.task.cancel()
        self.task = None

    def after_action(self):
        self.arm()
        self.broadcast()
        self.reschedule()

    def arm(self):
        """Start the move timer of a human who has just come on turn."""
        g = self.game
        if g.phase not in ("dealer", "play") or g.players[g.turn].bot or self.away[g.turn]:
            self.turn_key = None
            return
        key = self._key()
        if self.turn_key == key:
            return
        self.turn_key = key
        total = TURN_DELAY_MS + MOVE_MS
        delay = total if self.seats[g.turn].connected() else DISCONNECTED_MS
        self.timer_total = total
        self.deadline = time.monotonic() + secs(delay)

    def reschedule(self):
        self.cancel_task()
        if self.deleted or self.mode != "game":
            return
        g = self.game
        if g.phase in ("dealer", "play"):
            coro = self._turn()
        else:
            coro = self._end_wait()
        self.task = asyncio.get_running_loop().create_task(coro)

    def _key(self):
        g = self.game
        return (g.round, g.phase, g.turn, g.turns)

    async def _turn(self):
        g = self.game
        seat = g.turn
        key = self._key()
        s = self.seats[seat]
        if g.players[seat].bot or self.away[seat]:
            await self._bot_turn(seat, key)
            return
        # a human (connected or not): the timer was armed in after_action
        await asyncio.sleep(max(0.0, self.deadline - time.monotonic()))
        if self._key() != key:
            return
        if s.kind == "human" and s.connected():
            self.misses[seat] += 1          # idle protection: a connected human timed out
            if self.misses[seat] >= IDLE_TURNS:
                self.away[seat] = True
        if g.phase == "dealer":
            g.dealer_decide(False)
        else:
            g.do_move(seat, {"type": "pass"})
        self.event = g.events
        self.after_action()

    async def _bot_turn(self, seat, key):
        g = self.game
        self.turn_key = None
        if g.phase == "dealer":
            await asyncio.sleep(secs(DEAL_WAIT_MS + THINK_MS + g.rng.random() * THINK_RANDOM_MS))
            if self._key() != key:
                return
            g.dealer_decide(g.bot_dealer_takes(seat))
            self.event = g.events
            self.after_action()
            return
        await asyncio.sleep(secs(THINK_MS + g.rng.random() * THINK_RANDOM_MS))
        while True:
            if self._key() != key:
                return
            move = g.bot_choose(seat)
            if move["type"] == "bet":
                g.do_move(seat, move)
                self.event = g.events
                self.broadcast()
                await asyncio.sleep(secs(BET_WAIT_MS))
                continue
            if move["type"] in ("swap", "all"):
                self.pending = {"pi": seat, "move": move}
                self.broadcast()
                await asyncio.sleep(secs(SHOW_MS))
                self.pending = None
                if self._key() != key:
                    return
            g.do_move(seat, move)
            self.event = g.events
            self.after_action()
            return

    def _end_wait(self):
        g = self.game
        res = g.result or {}
        if g.phase == "over":
            who = [i for i in self.humans() if self.seats[i].connected() and not self.away[i]]
        else:
            who = [i for i in self.humans() if self.seats[i].connected() and not g.players[i].out
                   and not self.away[i]]
        total = REVEAL_MS + (REVEAL_BIG_MS if res.get("big") else 0) + \
            (REVEAL_BACKFIRE_MS if res.get("backfire") is not None else 0)
        if who:
            total += END_WAIT_MS
        self.end_total = total
        self.end_deadline = time.monotonic() + secs(total)
        return self._end_sleep()

    async def _end_sleep(self):
        await asyncio.sleep(max(0.0, self.end_deadline - time.monotonic()))
        self.finish_end()

    def waiting_for_next(self):
        g = self.game
        if g.phase == "over":
            who = [i for i in self.humans() if self.seats[i].connected() and not self.away[i]]
        else:
            who = [i for i in self.humans() if self.seats[i].connected() and not g.players[i].out
                   and not self.away[i]]
        return who

    def finish_end(self):
        g = self.game
        if g.phase == "over":
            self.to_lobby()
            return
        if g.phase != "showdown":
            return
        self.ready = set()
        g.next_round()
        self.turn_key = None
        self.event = g.events
        self.after_action()

    # -- human input
    def on_next(self, seat):
        g = self.game
        if g.phase not in ("showdown", "over"):
            return
        self.ready.add(seat)
        who = self.waiting_for_next()
        if who and all(i in self.ready for i in who):
            self.finish_end()

    def on_act(self, seat, a, msg):
        g = self.game
        if g.phase == "dealer":
            if g.turn != seat:
                return "Not your turn"
            if a not in ("keep", "take"):
                return "Choose keep or take"
            g.dealer_decide(a == "take")
        elif g.phase == "play":
            if g.turn != seat:
                return "Not your turn"
            if a == "swap":
                h, m = msg.get("h"), msg.get("m")
                if not (isinstance(h, int) and isinstance(m, int)
                        and not isinstance(h, bool) and not isinstance(m, bool)
                        and 0 <= h <= 2 and 0 <= m <= 2):
                    return "Bad card choice"
                err = g.do_move(seat, {"type": "swap", "h": h, "m": m})
            elif a in ("all", "pass", "knock", "bet"):
                err = g.do_move(seat, {"type": a})
            else:
                return "Unknown action"
            if err:
                return err
            if a == "bet":
                # same turn goes on, with a little more time
                self.deadline += secs(BET_EXTRA_MS)
                self.timer_total += BET_EXTRA_MS
        else:
            return "No move to make now"
        self.misses[seat] = 0           # an own action: the idle count starts again
        if self.away[seat]:
            self.away[seat] = False
        if self.pending is not None and self.pending["pi"] == seat:
            self.pending = None
        self.event = g.events
        self.after_action()
        return None

    def on_back(self, seat):
        """The human is back: clear 'away' and give the turn back if it is theirs."""
        self.misses[seat] = 0
        if not self.away[seat]:
            return
        self.away[seat] = False
        g = self.game
        if g.phase in ("dealer", "play") and g.turn == seat:
            self.pending = None
            self.turn_key = None
            self.after_action()
        else:
            self.broadcast()


class Hub:
    """Rooms, quick match, tokens, timers and broadcast. Transport independent."""

    def __init__(self):
        self.links = {}        # conn -> Link
        self.members = {}      # token -> Member
        self.rooms = {}        # code -> Room
        self.queue = []        # queued Members, longest waiting first
        self.quick_task = None

    # -- connection life
    def connect(self, conn):
        if len(self.links) >= MAX_CONNECTIONS:
            return None                  # full: the handler closes the connection
        link = Link(conn)
        m = Member()
        self._bind(link, m)
        self.members[m.token] = m
        self.links[conn] = link
        link.task = asyncio.get_running_loop().create_task(self._pump(link))
        m.send({"t": "welcome", "version": SERVER_VERSION, "started": STARTED, "token": m.token})
        log.info("connect (%d open)", len(self.links))
        return link

    async def _pump(self, link):
        try:
            while True:
                s = await link.q.get()
                await link.conn.send(s)
        except asyncio.CancelledError:
            raise
        except Exception:
            pass

    @staticmethod
    def _bind(link, member):
        link.member = member
        member.link = link
        member.send = lambda obj, _l=link: _l.q.put_nowait(json.dumps(obj)) if _l.q.qsize() < 1000 else None

    def disconnect(self, conn):
        link = self.links.pop(conn, None)
        if link is None:
            return
        if link.task:
            link.task.cancel()
        m = link.member
        log.info("disconnect (%d open)", len(self.links))
        if m is None or m.link is not link:
            return
        m.link = None
        if m.queued:
            self._dequeue(m)
        if m.room is None:
            self.members.pop(m.token, None)      # nothing to come back to
            return
        # keep the seat for a while
        m.expire = asyncio.get_running_loop().create_task(self._expire(m))
        room = m.room
        if room.mode == "game":
            g = room.game
            if g.phase in ("dealer", "play") and g.turn == m.seat:
                room.deadline = min(room.deadline, time.monotonic() + secs(DISCONNECTED_MS))
            room.broadcast()
            if g.phase in ("dealer", "play") and g.turn == m.seat:
                room.reschedule()
        else:
            if room.host == m.seat:
                alive = [i for i in room.humans() if room.seats[i].connected()]
                if alive:
                    room.host = alive[0]
            room.broadcast()

    async def _expire(self, m):
        await asyncio.sleep(secs(TOKEN_KEEP_MS))
        if m.link is not None:
            return
        self.members.pop(m.token, None)
        if m.room is not None:
            m.room.remove_member(m)

    def send_error(self, conn, text):
        link = self.links.get(conn)
        if link is not None and link.member is not None:
            link.member.send({"t": "error", "msg": text})

    # -- messages
    def message(self, conn, msg):
        link = self.links.get(conn)
        if link is None:
            return
        m = link.member
        try:
            if not isinstance(msg, dict) or not isinstance(msg.get("t"), str):
                m.send({"t": "error", "msg": "Bad message"})
                return
            fn = getattr(self, "_h_" + msg["t"], None) if msg["t"].isalpha() else None
            if fn is None:
                m.send({"t": "error", "msg": "Unknown message"})
                return
            err = fn(link, m, msg)
            if err:
                m.send({"t": "error", "msg": err})
        except Exception as e:      # never crash the hub on bad input
            log.error("handler error: %s", type(e).__name__)
            try:
                m.send({"t": "error", "msg": "Server error"})
            except Exception:
                pass

    def _h_hello(self, link, m, msg):
        tok = msg.get("token")
        if not isinstance(tok, str) or len(tok) > 100:
            return "Bad token"
        old = self.members.get(tok)
        if old is None or old is m:
            m.send({"t": "welcome", "version": SERVER_VERSION, "started": STARTED, "token": m.token})
            return None
        if m.room is not None or m.queued:
            return "Already in a room"
        # move this connection onto the old member
        self.members.pop(m.token, None)
        if old.link is not None and old.link is not link:
            stale = old.link
            fresh = Member()
            self.members[fresh.token] = fresh
            self._bind(stale, fresh)          # the stale connection becomes anonymous
            fresh.send({"t": "welcome", "version": SERVER_VERSION, "started": STARTED, "token": fresh.token})
        if old.expire is not None:
            old.expire.cancel()
            old.expire = None
        self._bind(link, old)
        old.send({"t": "welcome", "version": SERVER_VERSION, "started": STARTED, "token": old.token})
        if old.room is not None:
            old.room.restore_timer(old.seat)
            old.room.broadcast()
        elif old.queued:
            old.send({"t": "queue", "waiting": len(self.queue)})
        return None

    def _free(self, m):
        if m.room is not None:
            return "Already in a room"
        if m.queued:
            return "Already in the queue"
        return None

    def new_code(self):
        letters = [c for c in string.ascii_uppercase if c not in "IO"]
        for _ in range(1000):
            code = "".join(secrets.choice(letters) for _ in range(4))
            if code not in self.rooms:
                return code
        raise RuntimeError("no free code")

    def _h_create(self, link, m, msg):
        err = self._free(m)
        if err:
            return err
        hearts = msg.get("hearts", 3)
        bet = msg.get("bet", False)
        if isinstance(hearts, bool) or not isinstance(hearts, int) or not 1 <= hearts <= 4:
            return "Hearts must be 1 to 4"
        if not isinstance(bet, bool):
            return "Bad bet setting"
        if len(self.rooms) >= MAX_ROOMS:
            return "Server is full"
        m.name = clean_name(msg.get("name"))
        room = Room(self, self.new_code(), hearts, bet)
        self.rooms[room.code] = room
        room.add_human(m)
        room.host = m.seat
        log.info("room created (%d rooms)", len(self.rooms))
        room.broadcast()
        return None

    def _h_join(self, link, m, msg):
        err = self._free(m)
        if err:
            return err
        code = msg.get("code")
        if not isinstance(code, str):
            return "Bad room code"
        room = self.rooms.get(code.strip().upper())
        if room is None:
            return "Unknown room code"
        if room.mode != "lobby":
            return "Game already running"
        m.name = clean_name(msg.get("name"))
        if room.add_human(m) is None:
            return "Room is full"
        room.broadcast()
        return None

    def _h_leave(self, link, m, msg):
        if m.queued:
            self._dequeue(m)
        if m.room is not None:
            m.room.remove_member(m)
        return None

    def _h_start(self, link, m, msg):
        room = m.room
        if room is None:
            return "Not in a room"
        if room.mode != "lobby":
            return "Game already running"
        if room.host != m.seat:
            return "Only the host can start"
        room.start()
        return None

    def _h_back(self, link, m, msg):
        room = m.room
        if room is None or room.mode != "game":
            return "No game running"
        room.on_back(m.seat)
        return None

    def _h_next(self, link, m, msg):
        room = m.room
        if room is None or room.mode != "game":
            return "No game running"
        room.on_next(m.seat)
        return None

    def _h_act(self, link, m, msg):
        room = m.room
        if room is None or room.mode != "game":
            return "No game running"
        a = msg.get("a")
        if not isinstance(a, str):
            return "Bad action"
        return room.on_act(m.seat, a, msg)

    # -- quick match
    def _h_quick(self, link, m, msg):
        err = self._free(m)
        if err:
            return err
        if len(self.rooms) >= MAX_ROOMS:
            return "Server is full"
        m.name = clean_name(msg.get("name"))
        m.queued = True
        m.since = time.monotonic()
        self.queue.append(m)
        if len(self.queue) >= 4:
            self._make_quick_room()
        self._queue_changed()
        return None

    def _h_cancel(self, link, m, msg):
        if m.queued:
            self._dequeue(m)
            m.send({"t": "queue", "waiting": 0})
        return None

    def _dequeue(self, m):
        if m in self.queue:
            self.queue.remove(m)
        m.queued = False
        self._queue_changed()

    def _queue_changed(self):
        for q in self.queue:
            q.send({"t": "queue", "waiting": len(self.queue)})
        if self.quick_task is not None:
            self.quick_task.cancel()
            self.quick_task = None
        if self.queue:
            wait = self.queue[0].since + secs(QUICK_WAIT_MS) - time.monotonic()
            self.quick_task = asyncio.get_running_loop().create_task(self._quick_wait(max(0.0, wait)))

    async def _quick_wait(self, wait):
        await asyncio.sleep(wait)
        self.quick_task = None
        if self.queue:
            self._make_quick_room()
            self._queue_changed()

    def _make_quick_room(self):
        batch, self.queue = self.queue[:4], self.queue[4:]
        if len(self.rooms) >= MAX_ROOMS:
            for m in batch:
                m.queued = False
                m.send({"t": "error", "msg": "Server is full"})
            return
        room = Room(self, self.new_code(), 3, False)
        self.rooms[room.code] = room
        for m in batch:
            m.queued = False
            room.add_human(m)
        room.host = batch[0].seat
        log.info("quick room created (%d rooms)", len(self.rooms))
        room.start()

    # -- rooms
    def delete_room(self, room):
        room.deleted = True
        room.cancel_task()
        self.rooms.pop(room.code, None)
        for s in room.seats:
            if s.member is not None:
                s.member.room, s.member.seat = None, None
        log.info("room deleted (%d rooms)", len(self.rooms))


# ---------------------------------------------------------------- network

async def run_server(hub, port):
    from websockets.asyncio.server import serve    # only needed for the network server

    async def handler(conn):
        if hub.connect(conn) is None:
            await conn.close()
            return
        try:
            async for raw in conn:
                try:
                    msg = json.loads(raw)
                except ValueError:
                    hub.send_error(conn, "Bad message")
                    continue
                hub.message(conn, msg)
        except Exception:
            pass
        finally:
            hub.disconnect(conn)

    def process_request(connection, request):
        if request.headers.get("Upgrade", "").lower() != "websocket":
            return connection.respond(HTTPStatus.OK, "ok\n")
        return None

    async with serve(handler, "0.0.0.0", port, process_request=process_request, max_size=4096):
        log.info("31 server %s listening on port %d (started %s)", SERVER_VERSION, port, STARTED)
        await asyncio.get_running_loop().create_future()


def quiet_probes(record):
    """Log filter: False for the library's 'opening handshake failed' lines (port probes)."""
    return not (record.name.startswith("websockets") and record.getMessage() == "opening handshake failed")


def main():
    global TIME_SCALE
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(message)s")
    # the library's own INFO lines can include client addresses: keep them out of the log
    logging.getLogger("websockets").setLevel(logging.WARNING)
    # Render (and web scanners) probe the port with HEAD or other non-WebSocket requests; the
    # library rejects them before our health check sees them and logs a long traceback each time.
    # Drop just that message; every other error still shows.
    for h in logging.getLogger().handlers:
        h.addFilter(quiet_probes)
    port =int(os.environ.get("PORT", "8765"))
    TIME_SCALE = float(os.environ.get("TIME_SCALE", "1.0"))

    async def go():
        await run_server(Hub(), port)

    asyncio.run(go())


if __name__ == "__main__":
    main()
