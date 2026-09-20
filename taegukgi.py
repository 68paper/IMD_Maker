#!/usr/bin/env python3
"""
태극기 주사위 게임 (가칭) — 로컬 실행 도구 (룰북 v0.9.5)

사용법
  python taegukgi.py play                 # 웹 게임을 내 컴퓨터에서 열기
  python taegukgi.py sim                  # AI 전용 시뮬레이션 (기본 4인 1000판)
  python taegukgi.py sim -n 3 -g 500      # 3인 500판
  python taegukgi.py sim --all -g 1000    # 3 · 4 · 5인 모두
  python taegukgi.py sim --json out.json  # 결과를 JSON으로 저장

파이썬 3.8 이상, 표준 라이브러리만 사용합니다.
"""
import argparse
import http.server
import json
import os
import random
import socketserver
import sys
import threading
import time
import webbrowser

VERSION = "0.9.5"

# =====================================================================
#  규칙 엔진 (웹 버전 index.html과 같은 규칙 · 같은 AI)
# =====================================================================

ROWS = [(0, 1, 2), (3, 4, 5), (6, 7, 8)]
COLS = [(0, 3, 6), (1, 4, 7), (2, 5, 8)]
CELL_ROW = [0, 0, 0, 1, 1, 1, 2, 2, 2]
CELL_COL = [0, 1, 2, 0, 1, 2, 0, 1, 2]
ADJ = {0: (1, 3), 1: (0, 2, 4), 2: (1, 5), 3: (0, 4, 6), 4: (1, 3, 5, 7),
       5: (2, 4, 8), 6: (3, 7), 7: (4, 6, 8), 8: (5, 7)}
COLORS = ["black", "white", "red", "blue"]
PIECES = ["taegeuk", "geon", "ri", "gam", "gon"]
PIECE_NAME = {"taegeuk": "태극", "geon": "건", "ri": "리", "gam": "감", "gon": "곤"}
VALUE_TO_PIECE = {2: "taegeuk", 3: "geon", 4: "ri", 5: "gam", 6: "gon"}
CONSEC_SETS = [frozenset((2, 3, 4)), frozenset((3, 4, 5)), frozenset((4, 5, 6))]
COMBO_TYPES = ("same", "consec", "color")
REWARD = {"same": 2, "consec": 2, "color": 1}
TIEBREAK = {"same": 0.03, "consec": 0.02, "color": 0.01}


def line_type(vals):
    """세 칸이 모두 찬 줄의 조합 종류. 조합이 아니면 None."""
    if any(v[1] == 1 for v in vals):
        return None
    pips = {v[1] for v in vals}
    colors = {v[0] for v in vals}
    if len(pips) == 1 and len(colors) == 3:
        return "same"
    if len(colors) == 1 and len(pips) == 3:
        return "consec" if frozenset(pips) in CONSEC_SETS else "color"
    return None


def full(board, line):
    return all(board[i] is not None for i in line)


def lines_at(cell):
    return ROWS[CELL_ROW[cell]], COLS[CELL_COL[cell]]


def legal_cells(board):
    # 룰북 v0.9.5: 감시의 눈(1)도 배치 기준이 된다.
    empties = [i for i in range(9) if board[i] is None]
    if len(empties) == 9:
        return empties
    legal = set()
    for p in range(9):
        if board[p] is not None:
            for n in ADJ[p]:
                if board[n] is None:
                    legal.add(n)
    return sorted(legal)


class Player:
    def __init__(self, pid, tie_rand):
        self.id = pid
        self.board = [None] * 9
        self.parts = {k: 0 for k in PIECES}
        self.arrival = 0
        self.tie_rand = tie_rand
        self.first_flag_round = None
        self.st = dict(same=0, consec=0, color=0, cross=0, scatter_lines=0, scatter_dice=0,
                       forced=0, blocked=0, eyes_taken=0, eyes_removed=0)

    def pieces(self):
        return sum(self.parts.values())

    def flags(self):
        return min(self.parts.values())

    def score(self):
        return self.pieces() + self.flags()


def pick_least(cands, pl, rng):
    mn = min(pl.parts[c] for c in cands)
    return rng.choice([c for c in cands if pl.parts[c] == mn])


def perp_potential(board, cell, die, exclude):
    color, pip = die
    s = 0
    for line in lines_at(cell):
        if line == exclude:
            continue
        others = [board[i] for i in line if i != cell and board[i] is not None]
        if not others or any(d[1] == 1 for d in others):
            continue
        if all(d[1] == pip for d in others):
            s += 2 * len(others)
        if all(d[0] == color for d in others) and pip not in {d[1] for d in others}:
            s += 2 * len(others)
    return s


def choose_keep(board, line, rng):
    best, key = [], None
    for cell in line:
        r, c = lines_at(cell)
        perp = c if line == r else r
        pen = -100 if all(board[i] is not None for i in perp if i != cell) else 0
        k = pen + perp_potential(board, cell, board[cell], line)
        if key is None or k > key:
            key, best = k, [cell]
        elif k == key:
            best.append(cell)
    return rng.choice(best)


def remove_eye(board, rng):
    eyes = [i for i in range(9) if board[i] is not None and board[i][1] == 1]
    if not eyes:
        return None
    best, key = [], None
    for c in eyes:
        s = 0
        for line in lines_at(c):
            o = [board[i] for i in line if i != c and board[i] is not None and board[i][1] != 1]
            if len(o) == 2 and (o[0][1] == o[1][1] or o[0][0] == o[1][0]):
                s += 2
            else:
                s += len(o)
        if key is None or s > key:
            key, best = s, [c]
        elif s == key:
            best.append(c)
    c = rng.choice(best)
    color = board[c][0]
    board[c] = None
    return color


def resolve(g, pl, line, ctype, values, keep=None):
    board, rng = pl.board, g.rng
    if keep is None:
        keep = choose_keep(board, line, rng)
    for i in line:
        if i != keep:
            g.bag[board[i][0]] += 1
            board[i] = None
    line_opts = [VALUE_TO_PIECE[v] for v in dict.fromkeys(values)]
    if ctype == "same":
        col = remove_eye(board, rng)
        if col is not None:
            g.bag[col] += 1
            pl.st["eyes_removed"] += 1
        for _ in range(2):
            pl.parts[pick_least(PIECES, pl, rng)] += 1
    elif ctype == "consec":
        # 룰북 v0.9.3: 세 눈 중 1개 + 원하는 조각 1개
        pl.parts[pick_least(line_opts, pl, rng)] += 1
        pl.parts[pick_least(PIECES, pl, rng)] += 1
    else:
        pl.parts[pick_least(line_opts, pl, rng)] += 1


def eval_building(board, cell, die):
    color, pip = die
    score = 0.0
    for line in lines_at(cell):
        ex = [board[i] for i in line if i != cell and board[i] is not None]
        if not ex:
            continue
        has1 = any(d[1] == 1 for d in ex)
        if pip == 1:
            if has1:
                score -= 2
            else:
                pot = (len({d[1] for d in ex}) == 1) + (len({d[0] for d in ex}) == 1)
                score += -8 - 4 * pot * len(ex)
            continue
        if has1:
            score -= 3
            continue
        pips_e = [d[1] for d in ex]
        compat_same = all(d[1] == pip for d in ex)
        track = 0
        compat_track = False
        if all(d[0] == color for d in ex):
            distinct = pip not in pips_e
            compat_track = distinct
            if len(ex) == 2:
                in_win = frozenset(pips_e + [pip]) in CONSEC_SETS and distinct
            else:
                in_win = any(pip in s and pips_e[0] in s for s in CONSEC_SETS) and distinct
            track = (3 * len(ex) + 1) if in_win else (3 * len(ex) if distinct else 0)
        if compat_same and compat_track:
            score += max(2 * len(ex) + 1, track)
        elif compat_same:
            score += 2 * len(ex) + 1
        elif compat_track:
            score += track
        else:
            score -= 6
    return score


def choose_move(board, pool, rng):
    cells = legal_cells(board)
    if not cells:
        return None, False
    best, key, any_free = [], None, False
    for pi, die in enumerate(pool):
        for cell in cells:
            board[cell] = die
            res = []
            for line in lines_at(cell):
                if full(board, line):
                    res.append((line, line_type([board[i] for i in line])))
            combos = [t for _, t in res if t]
            scat = any(t is None and any(board[i][1] != 1 for i in l) for l, t in res)
            if len(combos) == 2:
                k = (3, sum(REWARD[t] + TIEBREAK[t] for t in combos))
            elif len(combos) == 1:
                k = (2, REWARD[combos[0]] + TIEBREAK[combos[0]])
            else:
                k = (1, eval_building(board, cell, die) - (30 if scat else 0))
            board[cell] = None
            if not scat:
                any_free = True
            if key is None or k > key:
                key, best = k, [(pi, cell)]
            elif k == key:
                best.append((pi, cell))
    return rng.choice(best), (not any_free)


class Game:
    def __init__(self, n, seed):
        self.n = n
        self.rng = random.Random(seed)
        self.bag = {c: 16 for c in COLORS}
        self.players = [Player(i, self.rng.random()) for i in range(n)]
        self.arrival_counter = 0
        self.round = 0
        self.lead_hist = []
        self.r4 = None
        self.zero_color_rounds = 0

    def draw(self, k):
        out = []
        for _ in range(min(k, sum(self.bag.values()))):
            r = self.rng.randrange(sum(self.bag.values()))
            for c in COLORS:
                if r < self.bag[c]:
                    self.bag[c] -= 1
                    out.append(c)
                    break
                r -= self.bag[c]
        return out

    def place(self, pl, die, cell):
        b = pl.board
        b[cell] = die
        if die[1] == 1:
            pl.st["eyes_taken"] += 1
        found = []
        for line in lines_at(cell):
            if full(b, line):
                t = line_type([b[i] for i in line])
                if t:
                    found.append((line, t, [b[i][1] for i in line]))
        if len(found) == 2:
            pl.st["cross"] += 1
            for line, t, vals in sorted(found, key=lambda x: -REWARD[x[1]]):
                pl.st[t] += 1
                resolve(self, pl, line, t, vals, keep=cell)
        elif found:
            line, t, vals = found[0]
            pl.st[t] += 1
            resolve(self, pl, line, t, vals)
        for line in lines_at(cell):
            if full(b, line) and not line_type([b[i] for i in line]):
                removed = [i for i in line if b[i][1] != 1]
                if removed:
                    for i in removed:
                        self.bag[b[i][0]] += 1
                        b[i] = None
                    pl.st["scatter_lines"] += 1
                    pl.st["scatter_dice"] += len(removed)

    def play_round(self):
        self.round += 1
        ps = self.players
        order = sorted(range(self.n), key=lambda i: (ps[i].score(), -ps[i].arrival, ps[i].tie_rand)) \
            if self.round > 1 else self.rng.sample(range(self.n), self.n)
        if self.round == 1:
            self.order1 = order[:]
        pool = [(c, self.rng.randint(1, 6)) for c in self.draw(self.n * 2 + 2)]
        cnt = {c: 0 for c in COLORS}
        for c, _ in pool:
            cnt[c] += 1
        if any(v == 0 for v in cnt.values()):
            self.zero_color_rounds += 1
        for pid in order:
            pl = ps[pid]
            for _ in range(2):
                if not pool:
                    break
                mv, forced = choose_move(pl.board, pool, self.rng)
                before = pl.score()
                if mv is None:
                    idx = next((i for i, d in enumerate(pool) if d[1] == 1), None)
                    if idx is None:
                        idx = self.rng.randrange(len(pool))
                    self.bag[pool.pop(idx)[0]] += 1
                    pl.st["blocked"] += 1
                    col = remove_eye(pl.board, self.rng)
                    if col is not None:
                        self.bag[col] += 1
                        pl.st["eyes_removed"] += 1
                    continue
                if forced:
                    pl.st["forced"] += 1
                pi, cell = mv
                had_flags = pl.flags()
                self.place(pl, pool.pop(pi), cell)
                if pl.score() != before:
                    self.arrival_counter += 1
                    pl.arrival = self.arrival_counter
                if pl.flags() > had_flags and pl.first_flag_round is None:
                    pl.first_flag_round = self.round
        for c, _ in pool:
            self.bag[c] += 1
        sc = [p.score() for p in ps]
        m = max(sc)
        leaders = [i for i in range(self.n) if sc[i] == m]
        self.lead_hist.append(leaders[0] if len(leaders) == 1 else None)
        if self.round == 4:
            self.r4 = sc[:]

    def run(self):
        for _ in range(8):
            self.play_round()
        sc = [p.score() for p in self.players]
        m = max(sc)
        tied = [i for i in range(self.n) if sc[i] == m]
        self.winner = min(tied, key=lambda i: (self.players[i].arrival, self.players[i].tie_rand))
        self.raw_tie = len(tied) > 1
        ch, prev = 0, None
        for x in self.lead_hist:
            if x is not None:
                if prev is not None and x != prev:
                    ch += 1
                prev = x
        self.changes = ch
        return self


# =====================================================================
#  시뮬레이션 집계
# =====================================================================

def simulate(n, games, seed):
    base = random.Random(seed)
    acc = dict(pieces=0, taegeuk=0, same=0, consec=0, color=0, cross=0, scatter=0, scatter_dice=0,
               forced=0, blocked=0, completers=0, two_flags=0, tie=0, gap=0, changes=0,
               reversal=0, zero_color=0)
    tops = []
    t0 = time.time()
    for _ in range(games):
        g = Game(n, base.getrandbits(32)).run()
        sc = [p.score() for p in g.players]
        tops.append(max(sc))
        acc["tie"] += g.raw_tie
        acc["gap"] += max(sc) - min(sc)
        acc["changes"] += g.changes
        acc["zero_color"] += g.zero_color_rounds
        r4max = max(g.r4)
        if g.r4[g.winner] != r4max:
            acc["reversal"] += 1
        for p in g.players:
            acc["pieces"] += p.pieces()
            acc["taegeuk"] += p.parts["taegeuk"]
            for k in ("same", "consec", "color", "cross", "forced", "blocked"):
                acc[k] += p.st[k]
            acc["scatter"] += p.st["scatter_lines"]
            acc["scatter_dice"] += p.st["scatter_dice"]
            acc["completers"] += p.flags() >= 1
            acc["two_flags"] += p.flags() >= 2
    pg = games * n
    tops.sort()
    pct = lambda q: tops[min(len(tops) - 1, int(q * len(tops)))]
    return {
        "version": VERSION, "players": n, "games": games, "seed": seed,
        "seconds": round(time.time() - t0, 2),
        "pieces_per_player": acc["pieces"] / pg,
        "taegeuk_share": acc["taegeuk"] / max(1, acc["pieces"]),
        "same_per_player": acc["same"] / pg,
        "consec_per_player": acc["consec"] / pg,
        "color_per_player": acc["color"] / pg,
        "cross_per_player": acc["cross"] / pg,
        "scatter_lines_per_player": acc["scatter"] / pg,
        "scatter_dice_per_player": acc["scatter_dice"] / pg,
        "forced_scatter_per_player": acc["forced"] / pg,
        "blocked_per_player": acc["blocked"] / pg,
        "flag_completion_rate": acc["completers"] / pg,
        "two_flags_rate": acc["two_flags"] / pg,
        "tie_rate": acc["tie"] / games,
        "first_last_gap": acc["gap"] / games,
        "leader_changes": acc["changes"] / games,
        "reversal_rate": acc["reversal"] / games,
        "zero_color_round_rate": acc["zero_color"] / (games * 8),
        "top_score_mean": sum(tops) / games,
        "top_score_p95": pct(0.95), "top_score_p99": pct(0.99), "top_score_max": tops[-1],
    }


def print_report(results):
    rows = [
        ("인당 조각", "pieces_per_player", "{:.2f}"),
        ("태극 비율", "taegeuk_share", "{:.1%}"),
        ("같은 눈 (인당)", "same_per_player", "{:.2f}"),
        ("연속 (인당)", "consec_per_player", "{:.2f}"),
        ("같은 색 (인당)", "color_per_player", "{:.2f}"),
        ("교차 완성 (인당)", "cross_per_player", "{:.3f}"),
        ("흩어진 줄 (인당)", "scatter_lines_per_player", "{:.2f}"),
        ("강제 흩어짐 (인당)", "forced_scatter_per_player", "{:.2f}"),
        ("배치 불가 (인당)", "blocked_per_player", "{:.3f}"),
        ("태극기 완성 비율", "flag_completion_rate", "{:.1%}"),
        ("태극기 2장 이상", "two_flags_rate", "{:.1%}"),
        ("1등 동점 비율", "tie_rate", "{:.1%}"),
        ("1등 - 꼴찌 격차", "first_last_gap", "{:.2f}"),
        ("선두 교체", "leader_changes", "{:.2f}"),
        ("역전율 (4R 뒤집힘)", "reversal_rate", "{:.1%}"),
        ("한 색이 빠진 라운드", "zero_color_round_rate", "{:.1%}"),
        ("1등 점수 평균", "top_score_mean", "{:.2f}"),
        ("1등 점수 95%", "top_score_p95", "{}"),
        ("1등 점수 99%", "top_score_p99", "{}"),
        ("1등 점수 최대", "top_score_max", "{}"),
    ]
    head = "{:<20}".format("지표") + "".join("{:>12}".format("%d인" % r["players"]) for r in results)
    print()
    print("태극기 주사위 게임 시뮬레이션 (룰북 v%s)" % VERSION)
    print("  " + " · ".join("%d인 %d판 (시드 %s, %.1f초)" % (r["players"], r["games"], r["seed"], r["seconds"]) for r in results))
    print("-" * 60)
    print(head)
    for label, key, fmt in rows:
        print("{:<20}".format(label) + "".join("{:>12}".format(fmt.format(r[key])) for r in results))
    print()


# =====================================================================
#  웹 게임 실행
# =====================================================================

def play(port, html):
    folder = os.path.dirname(os.path.abspath(html))
    name = os.path.basename(html)
    if not os.path.exists(html):
        print("'%s' 파일을 찾을 수 없습니다. taegukgi.py와 같은 폴더에 index.html을 두세요." % html)
        sys.exit(1)
    os.chdir(folder)

    class Quiet(http.server.SimpleHTTPRequestHandler):
        def log_message(self, *a):
            pass

    socketserver.TCPServer.allow_reuse_address = True
    for p in range(port, port + 20):
        try:
            httpd = socketserver.TCPServer(("127.0.0.1", p), Quiet)
            break
        except OSError:
            continue
    else:
        print("사용할 수 있는 포트를 찾지 못했습니다.")
        sys.exit(1)
    url = "http://127.0.0.1:%d/%s" % (p, name)
    print("태극기 주사위 게임을 엽니다: %s" % url)
    print("끝내려면 이 창에서 Ctrl + C 를 누르세요.")
    threading.Timer(0.6, lambda: webbrowser.open(url)).start()
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        print("\n종료했습니다.")
    finally:
        httpd.server_close()


def main():
    ap = argparse.ArgumentParser(description="태극기 주사위 게임 로컬 실행 도구 (룰북 v%s)" % VERSION)
    sub = ap.add_subparsers(dest="cmd")

    p_play = sub.add_parser("play", help="웹 게임을 브라우저로 열기")
    p_play.add_argument("--port", type=int, default=8000, help="사용할 포트 (기본 8000)")
    p_play.add_argument("--file", default=None, help="게임 HTML 파일 경로 (기본: 같은 폴더의 index.html)")

    p_sim = sub.add_parser("sim", help="AI 전용 시뮬레이션")
    p_sim.add_argument("-n", "--players", type=int, choices=[3, 4, 5], default=4, help="인원 (3 · 4 · 5, 기본 4)")
    p_sim.add_argument("-g", "--games", type=int, default=1000, help="판 수 (기본 1000)")
    p_sim.add_argument("-s", "--seed", type=int, default=None, help="난수 시드 (비우면 무작위)")
    p_sim.add_argument("--all", action="store_true", help="3 · 4 · 5인 모두 실행")
    p_sim.add_argument("--json", default=None, help="결과를 저장할 JSON 파일 이름")

    args = ap.parse_args()
    if args.cmd == "play":
        html = args.file or os.path.join(os.path.dirname(os.path.abspath(__file__)), "index.html")
        play(args.port, html)
    elif args.cmd == "sim":
        seed = args.seed if args.seed is not None else random.randrange(2 ** 31)
        ns = [3, 4, 5] if args.all else [args.players]
        results = []
        for n in ns:
            print("%d인 %d판 실행 중…" % (n, args.games), flush=True)
            results.append(simulate(n, args.games, seed))
        print_report(results)
        if args.json:
            with open(args.json, "w", encoding="utf-8") as f:
                json.dump(results, f, ensure_ascii=False, indent=2)
            print("결과를 %s에 저장했습니다." % args.json)
    else:
        ap.print_help()


if __name__ == "__main__":
    main()
