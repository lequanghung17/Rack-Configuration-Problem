# IncrementalSAT_c1_nsc.py
# Incremental SAT optimization for Rack Configuration Problem
# using Integrated model (rel + a + w) + SB3-prefix + load ordering
# and assumption-based incremental linear search.
#
# NSC is used for:
#   - ExactlyOne on assignment of each card instance
#   - connector-capacity cardinality
#   - total active rack-use cardinality
#
# PBEnc is still used for:
#   - weighted power capacity
#   - weighted cost bounds
#
# ITotalizer is still used for:
#   - unary load bits L(m,r,k) needed by load-order symmetry

import re
import time
import argparse
from dataclasses import dataclass
from threading import Timer
from typing import List, Tuple, Dict, Optional

from pysat.formula import CNF, IDPool
from pysat.card import ITotalizer
from pysat.pb import PBEnc, EncType as PBEncType
from pysat.solvers import Solver


# -------------------------
# Utils
# -------------------------
def log(msg: str):
    print(f"[{time.strftime('%H:%M:%S')}] {msg}", flush=True)


# -------------------------
# Data
# -------------------------
@dataclass
class RackModel:
    power_cap: int
    connectors: int
    cost: int


@dataclass
class CardType:
    power: int
    demand: int


@dataclass
class Instance:
    nbRackModels: int
    nbCardTypes: int
    nbRacks: int
    rackModels: List[RackModel]
    cardTypes: List[CardType]


# -------------------------
# Parsing
# -------------------------
def read_text_auto(path: str) -> str:
    raw = open(path, "rb").read()
    if raw.startswith(b"\xff\xfe") or raw.startswith(b"\xfe\xff"):
        txt = raw.decode("utf-16", errors="ignore")
    elif raw.startswith(b"\xef\xbb\xbf"):
        txt = raw.decode("utf-8-sig", errors="ignore")
    else:
        nul = raw.count(b"\x00")
        if len(raw) and (nul / len(raw) > 0.05):
            try:
                txt = raw.decode("utf-16le", errors="ignore")
            except Exception:
                txt = raw.decode("utf-16be", errors="ignore")
        else:
            txt = raw.decode("utf-8", errors="ignore")
    return txt.replace("\x00", "")


def normalize_text(s: str) -> str:
    s = s.replace("\ufeff", "")
    s = s.replace("\xa0", " ")
    s = re.sub(r"[\u200b\u200c\u200d\u2060]", "", s)
    s = s.replace("\r\n", "\n").replace("\r", "\n")
    return s


def _extract_int_field(text: str, name: str) -> int:
    m = re.search(rf"\b{name}\b\s*=\s*(\d+)\s*;", text, flags=re.IGNORECASE)
    if not m:
        raise ValueError(f"Missing {name}.")
    return int(m.group(1))


def _extract_block(text: str, name: str) -> str:
    m = re.search(rf"\b{name}\b\s*=\s*\[(.*?)\]\s*;", text, flags=re.IGNORECASE | re.DOTALL)
    if not m:
        raise ValueError(f"Missing {name} block.")
    return m.group(1)


def _parse_angle_tuples(block: str) -> List[Tuple[int, ...]]:
    res: List[Tuple[int, ...]] = []
    for mm in re.finditer(r"<\s*([^>]+?)\s*>", block, flags=re.DOTALL):
        nums = [int(x.strip()) for x in mm.group(1).split(",") if x.strip()]
        res.append(tuple(nums))
    return res


def parse_instance_file(path: str) -> Instance:
    text = normalize_text(read_text_auto(path))
    nbRackModels = _extract_int_field(text, "nbRackModels")
    nbCardTypes = _extract_int_field(text, "nbCardTypes")
    nbRacks = _extract_int_field(text, "nbRacks")

    rm = _parse_angle_tuples(_extract_block(text, "RackModels"))  # <P,S,Cost>
    ct = _parse_angle_tuples(_extract_block(text, "CardTypes"))   # <Pow,Demand>

    if len(rm) != nbRackModels:
        raise ValueError(f"RackModels count mismatch: got {len(rm)} expected {nbRackModels}")
    if len(ct) != nbCardTypes:
        raise ValueError(f"CardTypes count mismatch: got {len(ct)} expected {nbCardTypes}")

    rackModels = [RackModel(power_cap=p, connectors=s, cost=c) for (p, s, c) in rm]
    cardTypes = [CardType(power=powc, demand=dem) for (powc, dem) in ct]
    return Instance(nbRackModels, nbCardTypes, nbRacks, rackModels, cardTypes)


# -------------------------
# NSC helpers
# -------------------------
def _alloc_nsc_matrix(vpool: IDPool, n: int, k: int, tag: str) -> List[List[int]]:
    """
    Allocate NSC auxiliary matrix R[i][j] for i = 1..n-1, j = 1..min(i,k).
    Row 0 is unused so indexing matches the paper formulas naturally.
    """
    R = [[0] * (k + 1) for _ in range(n)]
    for i in range(1, n):
        upto = min(i, k)
        for j in range(1, upto + 1):
            R[i][j] = vpool.id(f"nsc_R_{tag}_{i}_{j}")
    return R


def nsc_atmost_k(cnf: CNF, lits: List[int], k: int, vpool: IDPool, tag: str):
    """
    NSC <= k using formulas (1), (2), (3), (8).
    """
    n = len(lits)

    if k < 0:
        cnf.append([])
        return

    if n == 0 or k >= n:
        return

    if k == 0:
        for x in lits:
            cnf.append([-x])
        return

    if n == 1:
        return

    R = _alloc_nsc_matrix(vpool, n, k, tag)

    # (1) Xi -> R[i,1], for i = 1..n-1
    for i in range(1, n):
        cnf.append([-lits[i - 1], R[i][1]])

    # (2) R[i-1,j] -> R[i,j], for i = 2..n-1
    for i in range(2, n):
        for j in range(1, min(i - 1, k) + 1):
            cnf.append([-R[i - 1][j], R[i][j]])

    # (3) Xi /\ R[i-1,j-1] -> R[i,j], for i = 2..n-1
    for i in range(2, n):
        for j in range(2, min(i, k) + 1):
            cnf.append([-lits[i - 1], -R[i - 1][j - 1], R[i][j]])

    # (8) Xi -> ¬R[i-1,k], for i = k+1..n
    for i in range(k + 1, n + 1):
        cnf.append([-lits[i - 1], -R[i - 1][k]])


def nsc_exactly_k(cnf: CNF, lits: List[int], k: int, vpool: IDPool, tag: str):
    """
    NSC = k using formulas (1)..(8).
    """
    n = len(lits)

    if k < 0 or k > n:
        cnf.append([])
        return

    if n == 0:
        if k != 0:
            cnf.append([])
        return

    if k == 0:
        for x in lits:
            cnf.append([-x])
        return

    if k == n:
        for x in lits:
            cnf.append([x])
        return

    # n >= 2 and 1 <= k <= n-1
    R = _alloc_nsc_matrix(vpool, n, k, tag)

    # (1) Xi -> R[i,1], for i = 1..n-1
    for i in range(1, n):
        cnf.append([-lits[i - 1], R[i][1]])

    # (2) R[i-1,j] -> R[i,j], for i = 2..n-1
    for i in range(2, n):
        for j in range(1, min(i - 1, k) + 1):
            cnf.append([-R[i - 1][j], R[i][j]])

    # (3) Xi /\ R[i-1,j-1] -> R[i,j], for i = 2..n-1
    for i in range(2, n):
        for j in range(2, min(i, k) + 1):
            cnf.append([-lits[i - 1], -R[i - 1][j - 1], R[i][j]])

    # (4) ¬Xi /\ ¬R[i-1,j] -> ¬R[i,j], for i = 2..n-1
    for i in range(2, n):
        for j in range(1, min(i - 1, k) + 1):
            cnf.append([lits[i - 1], R[i - 1][j], -R[i][j]])

    # (5) ¬Xi -> ¬R[i,i], for i = 1..min(n-1,k)
    for i in range(1, min(n - 1, k) + 1):
        cnf.append([lits[i - 1], -R[i][i]])

    # (6) ¬R[i-1,j-1] -> ¬R[i,j], for i = 2..n-1
    for i in range(2, n):
        for j in range(2, min(i, k) + 1):
            cnf.append([R[i - 1][j - 1], -R[i][j]])

    # (7) At least k:
    # (R[n-1][k] OR Xn) AND (R[n-1][k] OR R[n-1][k-1]) for k > 1
    cnf.append([R[n - 1][k], lits[n - 1]])
    if k > 1:
        cnf.append([R[n - 1][k], R[n - 1][k - 1]])

    # (8) At most k
    for i in range(k + 1, n + 1):
        cnf.append([-lits[i - 1], -R[i - 1][k]])


def add_exactly_one_nsc(cnf: CNF, lits: List[int], vpool: IDPool, tag: str):
    nsc_exactly_k(cnf, lits, 1, vpool, tag)


# -------------------------
# Integrated model (F1)
# -------------------------
class IntegratedModelSAT:
    def __init__(self, inst: Instance):
        self.inst = inst
        self.vpool = IDPool()
        self.cnf = CNF()

        self.M = list(range(1, inst.nbRackModels + 1))
        self.R = list(range(1, inst.nbRacks + 1))
        self.C = list(range(1, inst.nbCardTypes + 1))

        # Q: card instances
        self.Q: List[Tuple[int, int]] = []
        for c in self.C:
            d = inst.cardTypes[c - 1].demand
            for t in range(1, d + 1):
                self.Q.append((c, t))

        # Ordered rack-uses
        self.P_list: List[Tuple[int, int]] = [(m, r) for m in self.M for r in self.R]
        self.P_size = len(self.P_list)

        self._rel: Dict[Tuple[int, int, int, int], int] = {}
        self._a: Dict[Tuple[int, int, int, int], int] = {}
        self._w: Dict[Tuple[int, int], int] = {}
        self._pref: Dict[Tuple[int, int, int], int] = {}
        self._L: Dict[Tuple[int, int, int], int] = {}

    # vars
    def w(self, m: int, r: int) -> int:
        k = (m, r)
        if k not in self._w:
            self._w[k] = self.vpool.id(f"w_{m}_{r}")
        return self._w[k]

    def rel(self, m: int, r: int, c: int, t: int) -> int:
        k = (m, r, c, t)
        if k not in self._rel:
            self._rel[k] = self.vpool.id(f"rel_{m}_{r}_{c}_{t}")
        return self._rel[k]

    def a(self, m: int, r: int, c: int, t: int) -> int:
        k = (m, r, c, t)
        if k not in self._a:
            self._a[k] = self.vpool.id(f"a_{m}_{r}_{c}_{t}")
        return self._a[k]

    def pref(self, c: int, t: int, j: int) -> int:
        k = (c, t, j)
        if k not in self._pref:
            self._pref[k] = self.vpool.id(f"pref_{c}_{t}_{j}")
        return self._pref[k]

    def L(self, m: int, r: int, k: int) -> int:
        return self._L[(m, r, k)]

    # params
    def Sm(self, m: int) -> int:
        return self.inst.rackModels[m - 1].connectors

    def Pm(self, m: int) -> int:
        return self.inst.rackModels[m - 1].power_cap

    def Costm(self, m: int) -> int:
        return self.inst.rackModels[m - 1].cost

    def build_F1(self):
        self._add_channelling()
        self._add_primal_constraints_and_L()
        self._add_dual_symmetry_SB3_prefix()
        self._add_load_nonincreasing_symmetry()

    def _add_channelling(self):
        # rel <-> a
        for (c, t) in self.Q:
            for (m, r) in self.P_list:
                rv = self.rel(m, r, c, t)
                av = self.a(m, r, c, t)
                self.cnf.append([-rv, av])
                self.cnf.append([-av, rv])

    def _add_primal_constraints_and_L(self):
        # Each card instance assigned exactly once
        for (c, t) in self.Q:
            lits = [self.rel(m, r, c, t) for (m, r) in self.P_list]
            add_exactly_one_nsc(self.cnf, lits, self.vpool, tag=f"exo_{c}_{t}")

        pow_weights = [self.inst.cardTypes[c - 1].power for (c, _t) in self.Q]

        for (m, r) in self.P_list:
            rel_lits = [self.rel(m, r, c, t) for (c, t) in self.Q]
            wm = self.w(m, r)

            # rel -> w
            for lit in rel_lits:
                self.cnf.append([-lit, wm])

            # w -> OR(rel)
            self.cnf.append([-wm] + rel_lits)

            # connector capacity: sum rel <= Sm(m)
            nsc_atmost_k(self.cnf, rel_lits, self.Sm(m), self.vpool, tag=f"conn_{m}_{r}")

            # power capacity: keep weighted PB encoding
            pbp = PBEnc.leq(
                lits=rel_lits,
                weights=pow_weights,
                bound=self.Pm(m),
                vpool=self.vpool,
                encoding=PBEncType.best,
            )
            self.cnf.extend(pbp.clauses)

            # Keep unary load outputs for load-order symmetry
            ub = min(self.Sm(m), len(rel_lits))
            if ub > 0:
                tot = ITotalizer(rel_lits, ubound=ub, top_id=self.vpool.top)
                self.cnf.extend(tot.cnf.clauses)

                for k in range(1, ub + 1):
                    self._L[(m, r, k)] = tot.rhs[k - 1]

                if hasattr(tot, "top_id") and tot.top_id is not None:
                    self.vpool.top = max(self.vpool.top, tot.top_id)
                else:
                    mx = 0
                    for cl in tot.cnf.clauses:
                        for lit in cl:
                            mx = max(mx, abs(lit))
                    self.vpool.top = max(self.vpool.top, mx)

        # total active rack-uses <= nbRacks
        w_lits = [self.w(m, r) for (m, r) in self.P_list]
        nsc_atmost_k(self.cnf, w_lits, self.inst.nbRacks, self.vpool, tag="cardW")

        # per-model prefix: w(m,r) -> w(m,r-1)
        for m in self.M:
            for r in range(2, self.inst.nbRacks + 1):
                self.cnf.append([-self.w(m, r), self.w(m, r - 1)])

    def _add_dual_symmetry_SB3_prefix(self):
        # pref(c,t,j) <-> OR_{i<=j} a_i(c,t)
        P = self.P_size
        for c in self.C:
            d = self.inst.cardTypes[c - 1].demand
            if d <= 1:
                continue

            for t in range(1, d + 1):
                (m1, r1) = self.P_list[0]
                a1 = self.a(m1, r1, c, t)
                p1 = self.pref(c, t, 1)
                self.cnf.append([-a1, p1])
                self.cnf.append([-p1, a1])

                for j in range(2, P + 1):
                    (mj, rj) = self.P_list[j - 1]
                    aj = self.a(mj, rj, c, t)
                    pj = self.pref(c, t, j)
                    pprev = self.pref(c, t, j - 1)

                    self.cnf.append([-pprev, pj])
                    self.cnf.append([-aj, pj])
                    self.cnf.append([-pj, pprev, aj])

            # SB3 ordering
            for t in range(2, d + 1):
                for j in range(1, P + 1):
                    self.cnf.append([-self.pref(c, t, j), self.pref(c, t - 1, j)])

    def _add_load_nonincreasing_symmetry(self):
        for m in self.M:
            ub = min(self.Sm(m), len(self.Q))
            if ub <= 0:
                continue
            for r in range(2, self.inst.nbRacks + 1):
                w_prev = self.w(m, r - 1)
                w_cur = self.w(m, r)
                for k in range(1, ub + 1):
                    self.cnf.append([-w_prev, -w_cur, -self.L(m, r, k), self.L(m, r - 1, k)])

    # objective helpers
    def cost_terms(self) -> Tuple[List[int], List[int]]:
        w_lits = [self.w(m, r) for (m, r) in self.P_list]
        weights = [self.Costm(m) for (m, _r) in self.P_list]
        return w_lits, weights

    def model_cost(self, model: List[int]) -> int:
        pos = {l for l in model if l > 0}
        total = 0
        for (m, r) in self.P_list:
            if self.w(m, r) in pos:
                total += self.Costm(m)
        return total

    def decode_counts(self, model: List[int]) -> Tuple[Dict[Tuple[int, int], int], Dict[Tuple[int, int], List[int]]]:
        model_set = {l for l in model if l > 0}
        active: Dict[Tuple[int, int], int] = {}
        counts: Dict[Tuple[int, int], List[int]] = {}

        for (m, r) in self.P_list:
            if self.w(m, r) in model_set:
                active[(m, r)] = 1
                counts[(m, r)] = [0] * self.inst.nbCardTypes

        for (c, t) in self.Q:
            placed = None
            for (m, r) in self.P_list:
                if self.rel(m, r, c, t) in model_set:
                    placed = (m, r)
                    break
            if placed is None:
                raise RuntimeError("Decode error: some card instance not assigned.")
            counts.setdefault(placed, [0] * self.inst.nbCardTypes)[c - 1] += 1

        return active, counts


# -------------------------
# Assumption-based cost bounding
# -------------------------
def encode_cost_le_assumption(
    sat: IntegratedModelSAT,
    bound: int,
    tag: str,
) -> Tuple[List[List[int]], int]:
    """
    Encode:
        act => (cost <= bound)

    Every PB clause C becomes:
        (-act OR C)
    """
    w_lits, weights = sat.cost_terms()

    act = sat.vpool.id(f"act_cost_le_{bound}_{tag}")

    pb = PBEnc.leq(
        lits=w_lits,
        weights=weights,
        bound=bound,
        vpool=sat.vpool,
        encoding=PBEncType.best,
    )

    gated = []
    for cl in pb.clauses:
        gated.append([-act] + cl)

    return gated, act


# -------------------------
# Timed SAT call
# -------------------------
def solve_with_timeout(s: Solver, assumptions: List[int], timeout_sec: Optional[float]):
    """
    Return:
      True  -> SAT
      False -> UNSAT
      None  -> interrupted / timed out / unknown
    """
    if timeout_sec is None:
        return s.solve(assumptions=assumptions)

    if timeout_sec <= 0:
        return None

    timer = Timer(timeout_sec, lambda: s.interrupt())
    timer.start()
    try:
        res = s.solve_limited(assumptions=assumptions, expect_interrupt=True)
    finally:
        timer.cancel()
        s.clear_interrupt()

    return res


# -------------------------
# Incremental optimization
# -------------------------
def optimize_incremental_assumption(
    inst: Instance,
    solver_name: str = "g42",
    start_ub: Optional[int] = None,
    deadline: Optional[float] = None,
) -> Tuple[Optional[List[int]], Optional[int], Dict[str, object]]:
    sat = IntegratedModelSAT(inst)
    sat.build_F1()

    stats: Dict[str, object] = {
        "vars_base": sat.vpool.top,
        "clauses_base": len(sat.cnf.clauses),
        "sat_calls": 0,
        "tighten_steps": 0,
        "assumption_solves": 0,
        "status": "UNKNOWN",
        "solver_time_sec": 0.0,
    }

    best_model: Optional[List[int]] = None
    best_cost: Optional[int] = None

    if deadline is not None and time.perf_counter() >= deadline:
        stats["status"] = "TIME_LIMIT"
        return best_model, best_cost, stats

    with Solver(name=solver_name, bootstrap_with=sat.cnf.clauses, use_timer=True) as s:
        first_assumptions: List[int] = []

        if start_ub is not None:
            if start_ub < 0:
                stats["status"] = "INFEASIBLE"
                stats["solver_time_sec"] = s.time_accum()
                return None, None, stats

            bound_clauses, act = encode_cost_le_assumption(sat, start_ub, tag="start")
            for cl in bound_clauses:
                s.add_clause(cl)

            first_assumptions = [act]
            stats["tighten_steps"] += 1
            stats["assumption_solves"] += 1

        stats["sat_calls"] += 1
        remaining = None if deadline is None else max(0.0, deadline - time.perf_counter())
        ok = solve_with_timeout(s, first_assumptions, remaining)

        if ok is None:
            stats["status"] = "TIME_LIMIT"
            stats["solver_time_sec"] = s.time_accum()
            return best_model, best_cost, stats

        if ok is False:
            stats["status"] = "INFEASIBLE"
            stats["solver_time_sec"] = s.time_accum()
            return None, None, stats

        model = s.get_model()
        cost = sat.model_cost(model)
        best_model = model
        best_cost = cost

        while True:
            new_bound = best_cost - 1
            if new_bound < 0:
                stats["status"] = "OPTIMAL"
                stats["solver_time_sec"] = s.time_accum()
                return best_model, best_cost, stats

            bound_clauses, act = encode_cost_le_assumption(
                sat,
                new_bound,
                tag=f"step{stats['tighten_steps'] + 1}",
            )
            for cl in bound_clauses:
                s.add_clause(cl)

            stats["tighten_steps"] += 1
            stats["sat_calls"] += 1
            stats["assumption_solves"] += 1

            remaining = None if deadline is None else max(0.0, deadline - time.perf_counter())
            ok = solve_with_timeout(s, [act], remaining)

            if ok is None:
                stats["status"] = "TIME_LIMIT"
                stats["solver_time_sec"] = s.time_accum()
                return best_model, best_cost, stats

            if ok is False:
                stats["status"] = "OPTIMAL"
                stats["solver_time_sec"] = s.time_accum()
                return best_model, best_cost, stats

            model = s.get_model()
            cost = sat.model_cost(model)
            best_model = model
            best_cost = cost


# -------------------------
# Output
# -------------------------
def print_solution(inst: Instance, active: Dict[Tuple[int, int], int], counts: Dict[Tuple[int, int], List[int]], opt_cost: int):
    print("=" * 110)
    print(f"OPT_COST = {opt_cost}")
    used = len(active)
    print(f"USED_RACK-USES = {used}  (<= nbRacks = {inst.nbRacks})\n")

    header = ["p", "m", "r", "Cost(m)"] + [f"Type{c}" for c in range(1, inst.nbCardTypes + 1)]
    print(" | ".join(f"{h:>8}" for h in header))
    print("-" * (11 * len(header)))

    p_list = [(m, r) for m in range(1, inst.nbRackModels + 1) for r in range(1, inst.nbRacks + 1)]
    p_idx = {mr: i + 1 for i, mr in enumerate(p_list)}

    for (m, r) in p_list:
        if (m, r) not in active:
            continue
        row = [p_idx[(m, r)], m, r, inst.rackModels[m - 1].cost] + counts.get((m, r), [0] * inst.nbCardTypes)
        print(" | ".join(f"{v:>8}" for v in row))
    print()


# -------------------------
# Main
# -------------------------
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--inst", required=True, help="instance .txt file")
    ap.add_argument("--solver", default="g42", help="PySAT solver name (e.g. g42, g4, cadical153, m22, ...)")
    ap.add_argument("--ub", type=int, default=None, help="optional starting UB for cost <= ub")
    ap.add_argument("--time-limit", type=float, default=None, help="total wall-clock time limit in seconds (parse + build + solve)")
    args = ap.parse_args()

    t_total0 = time.perf_counter()
    deadline = None if args.time_limit is None else t_total0 + float(args.time_limit)

    inst = parse_instance_file(args.inst)
    t_parse1 = time.perf_counter()

    total_cards = sum(ct.demand for ct in inst.cardTypes)
    log(
        f"parsed: nbRackModels={inst.nbRackModels}, nbRacks={inst.nbRacks}, "
        f"nbCardTypes={inst.nbCardTypes}, totalCardInstances={total_cards}"
    )

    log("building F1 with NSC cardinalities and running assumption-based incremental SAT...")
    model, opt_cost, stats = optimize_incremental_assumption(
        inst,
        solver_name=args.solver,
        start_ub=args.ub,
        deadline=deadline,
    )
    t_solve1 = time.perf_counter()

    parse_sec = t_parse1 - t_total0
    total_after_parse = t_solve1 - t_parse1
    solve_sec = float(stats.get("solver_time_sec", 0.0))
    build_sec = max(0.0, total_after_parse - solve_sec)
    total_sec = t_solve1 - t_total0

    log(
        f"done | status={stats.get('status', 'UNKNOWN')} | "
        f"sat_calls={stats['sat_calls']} "
        f"tighten_steps={stats['tighten_steps']} "
        f"assumption_solves={stats['assumption_solves']} | "
        f"base_vars={stats['vars_base']} "
        f"base_clauses={stats['clauses_base']}"
    )

    if model is None:
        if stats.get("status") == "INFEASIBLE":
            print("\nINFEASIBLE.\n")
        elif stats.get("status") == "TIME_LIMIT":
            print("\nTIME_LIMIT.\n")
        else:
            print("\nUNKNOWN / NO SOLUTION.\n")

        print(f"parse_sec = {parse_sec:.6f}")
        print(f"build_sec = {build_sec:.6f}")
        print(f"solve_sec = {solve_sec:.6f}")
        print(f"total_sec = {total_sec:.6f}")
        return

    sat = IntegratedModelSAT(inst)
    sat.build_F1()
    active, counts = sat.decode_counts(model)

    print_solution(inst, active, counts, opt_cost=opt_cost)
    print(f"status    = {stats.get('status', 'UNKNOWN')}")
    print(f"parse_sec = {parse_sec:.6f}")
    print(f"build_sec = {build_sec:.6f}")
    print(f"solve_sec = {solve_sec:.6f}")
    print(f"total_sec = {total_sec:.6f}")


if __name__ == "__main__":
    main()







#     hungle@qHung17-ASUS:~/RCP_bench$ source .venv39/bin/activate
# (.venv39) hungle@qHung17-ASUS:~/RCP_bench$ for i in 1 2 3 4 5 6 7 8 9 10; do   echo "===== Running instance$i =====";   python src/IncrementalSAT_c1_nsc.py     --inst "instances/instance$i.txt"     --time-limit 36
# 00 ; done
# ===== Running instance1 =====
# [14:55:09] parsed: nbRackModels=2, nbRacks=5, nbCardTypes=4, totalCardInstances=17
# [14:55:09] building F1 with NSC cardinalities and running assumption-based incremental SAT...
# [14:55:09] done | status=INFEASIBLE | sat_calls=1 tighten_steps=0 assumption_solves=0 | base_vars=2320 base_clauses=7730

# INFEASIBLE.

# parse_sec = 0.000547
# build_sec = 0.031431
# solve_sec = 0.000265
# total_sec = 0.032243
# ===== Running instance2 =====
# [14:55:09] parsed: nbRackModels=2, nbRacks=10, nbCardTypes=4, totalCardInstances=34
# [14:55:09] building F1 with NSC cardinalities and running assumption-based incremental SAT...
# [14:55:10] done | status=INFEASIBLE | sat_calls=1 tighten_steps=0 assumption_solves=0 | base_vars=10458 base_clauses=39844

# INFEASIBLE.

# parse_sec = 0.000632
# build_sec = 1.512230
# solve_sec = 0.000895
# total_sec = 1.513757
# ===== Running instance3 =====
# [14:55:11] parsed: nbRackModels=2, nbRacks=12, nbCardTypes=6, totalCardInstances=45
# [14:55:11] building F1 with NSC cardinalities and running assumption-based incremental SAT...
# [14:55:15] done | status=INFEASIBLE | sat_calls=1 tighten_steps=0 assumption_solves=0 | base_vars=20797 base_clauses=73898

# INFEASIBLE.

# parse_sec = 0.000682
# build_sec = 4.463603
# solve_sec = 0.001502
# total_sec = 4.465788
# ===== Running instance4 =====
# [14:55:15] parsed: nbRackModels=6, nbRacks=9, nbCardTypes=6, totalCardInstances=25
# [14:55:15] building F1 with NSC cardinalities and running assumption-based incremental SAT...
# [14:55:15] done | status=INFEASIBLE | sat_calls=1 tighten_steps=0 assumption_solves=0 | base_vars=17520 base_clauses=56760

# INFEASIBLE.

# parse_sec = 0.000677
# build_sec = 0.149546
# solve_sec = 0.001199
# total_sec = 0.151422
# ===== Running instance5 =====
# [14:55:15] parsed: nbRackModels=2, nbRacks=5, nbCardTypes=5, totalCardInstances=26
# [14:55:15] building F1 with NSC cardinalities and running assumption-based incremental SAT...
# [14:55:15] done | status=INFEASIBLE | sat_calls=1 tighten_steps=0 assumption_solves=0 | base_vars=4431 base_clauses=14850

# INFEASIBLE.

# parse_sec = 0.001430
# build_sec = 0.074439
# solve_sec = 0.000398
# total_sec = 0.076267
# ===== Running instance6 =====
# [14:55:16] parsed: nbRackModels=2, nbRacks=6, nbCardTypes=6, totalCardInstances=25
# [14:55:16] building F1 with NSC cardinalities and running assumption-based incremental SAT...
# [14:55:16] done | status=INFEASIBLE | sat_calls=1 tighten_steps=0 assumption_solves=0 | base_vars=5026 base_clauses=17022

# INFEASIBLE.

# parse_sec = 0.001671
# build_sec = 0.067027
# solve_sec = 0.000354
# total_sec = 0.069052
# ===== Running instance7 =====
# [14:55:16] parsed: nbRackModels=2, nbRacks=7, nbCardTypes=6, totalCardInstances=35
# [14:55:16] building F1 with NSC cardinalities and running assumption-based incremental SAT...
# [14:55:17] done | status=INFEASIBLE | sat_calls=1 tighten_steps=0 assumption_solves=0 | base_vars=9326 base_clauses=31777

# INFEASIBLE.

# parse_sec = 0.001158
# build_sec = 1.259589
# solve_sec = 0.000591
# total_sec = 1.261338
# ===== Running instance8 =====
# [14:55:17] parsed: nbRackModels=4, nbRacks=8, nbCardTypes=6, totalCardInstances=36
# [14:55:17] building F1 with NSC cardinalities and running assumption-based incremental SAT...
# [14:55:20] done | status=INFEASIBLE | sat_calls=1 tighten_steps=0 assumption_solves=0 | base_vars=17954 base_clauses=58259

# INFEASIBLE.

# parse_sec = 0.003082
# build_sec = 2.977339
# solve_sec = 0.000992
# total_sec = 2.981414
# ===== Running instance9 =====
# [14:55:20] parsed: nbRackModels=6, nbRacks=6, nbCardTypes=6, totalCardInstances=19
# [14:55:20] building F1 with NSC cardinalities and running assumption-based incremental SAT...
# [14:55:20] done | status=INFEASIBLE | sat_calls=1 tighten_steps=0 assumption_solves=0 | base_vars=8181 base_clauses=25560

# INFEASIBLE.

# parse_sec = 0.002878
# build_sec = 0.046690
# solve_sec = 0.000503
# total_sec = 0.050071
# ===== Running instance10 =====
# [14:55:20] parsed: nbRackModels=2, nbRacks=14, nbCardTypes=6, totalCardInstances=57
# [14:55:20] building F1 with NSC cardinalities and running assumption-based incremental SAT...
# [14:55:53] done | status=INFEASIBLE | sat_calls=1 tighten_steps=0 assumption_solves=0 | base_vars=31358 base_clauses=113019

# INFEASIBLE.

# parse_sec = 0.002181
# build_sec = 31.471042
# solve_sec = 0.002420
# total_sec = 31.475643
# (.venv39) hungle@qHung17-ASUS:~/RCP_bench$ for i in 1 2 3 4 5 6 7 8 9 10; do   echo "===== Running instance$i =====";   python src/IncrementalSAT_c1_nsc.py     --inst "instances/instance$i.txt"     --time-limit 3600 ; done
# ===== Running instance1 =====
# [15:09:23] parsed: nbRackModels=2, nbRacks=5, nbCardTypes=4, totalCardInstances=17
# [15:09:23] building F1 with NSC cardinalities and running assumption-based incremental SAT...
# [15:09:23] done | status=OPTIMAL | sat_calls=5 tighten_steps=4 assumption_solves=4 | base_vars=3408 base_clauses=7730
# ==============================================================================================================
# OPT_COST = 550
# USED_RACK-USES = 3  (<= nbRacks = 5)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4
# ----------------------------------------------------------------------------------------
#        1 |        1 |        1 |      150 |        5 |        0 |        1 |        0
#        6 |        2 |        1 |      200 |        4 |        1 |        0 |        1
#        7 |        2 |        2 |      200 |        1 |        3 |        1 |        0

# status    = OPTIMAL
# parse_sec = 0.000572
# build_sec = 0.028500
# solve_sec = 0.006385
# total_sec = 0.035457
# ===== Running instance2 =====
# [15:09:23] parsed: nbRackModels=2, nbRacks=10, nbCardTypes=4, totalCardInstances=34
# [15:09:23] building F1 with NSC cardinalities and running assumption-based incremental SAT...
# [15:09:29] done | status=OPTIMAL | sat_calls=9 tighten_steps=8 assumption_solves=8 | base_vars=16881 base_clauses=39844
# ==============================================================================================================
# OPT_COST = 1100
# USED_RACK-USES = 6  (<= nbRacks = 10)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4
# ----------------------------------------------------------------------------------------
#        1 |        1 |        1 |      150 |        3 |        0 |        0 |        1
#        2 |        1 |        2 |      150 |        3 |        2 |        0 |        0
#       11 |        2 |        1 |      200 |        8 |        1 |        0 |        0
#       12 |        2 |        2 |      200 |        6 |        2 |        0 |        0
#       13 |        2 |        3 |      200 |        0 |        0 |        4 |        0
#       14 |        2 |        4 |      200 |        0 |        3 |        0 |        1

# status    = OPTIMAL
# parse_sec = 0.000688
# build_sec = 1.338025
# solve_sec = 4.325570
# total_sec = 5.664282
# ===== Running instance3 =====
# [15:09:31] parsed: nbRackModels=2, nbRacks=12, nbCardTypes=6, totalCardInstances=45
# [15:09:31] building F1 with NSC cardinalities and running assumption-based incremental SAT...
# [15:17:56] done | status=OPTIMAL | sat_calls=9 tighten_steps=8 assumption_solves=8 | base_vars=31797 base_clauses=73898
# ==============================================================================================================
# OPT_COST = 1200
# USED_RACK-USES = 6  (<= nbRacks = 12)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5 |    Type6
# --------------------------------------------------------------------------------------------------------------
#       13 |        2 |        1 |      200 |        3 |        0 |        3 |        1 |        0 |        0
#       14 |        2 |        2 |      200 |        0 |        2 |        2 |        0 |        1 |        0
#       15 |        2 |        3 |      200 |        0 |        4 |        3 |        0 |        0 |        0
#       16 |        2 |        4 |      200 |        6 |        3 |        0 |        0 |        1 |        0
#       17 |        2 |        5 |      200 |        5 |        0 |        0 |        3 |        0 |        0
#       18 |        2 |        6 |      200 |        6 |        1 |        0 |        0 |        0 |        1

# status    = OPTIMAL
# parse_sec = 0.000727
# build_sec = 0.000000
# solve_sec = 500.162637
# total_sec = 490.960946
# ===== Running instance4 =====
# [15:18:01] parsed: nbRackModels=6, nbRacks=9, nbCardTypes=6, totalCardInstances=25
# [15:18:01] building F1 with NSC cardinalities and running assumption-based incremental SAT...
# [15:23:00] done | status=OPTIMAL | sat_calls=6 tighten_steps=5 assumption_solves=5 | base_vars=23312 base_clauses=56760
# ==============================================================================================================
# OPT_COST = 1150
# USED_RACK-USES = 5  (<= nbRacks = 9)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5 |    Type6
# --------------------------------------------------------------------------------------------------------------
#       19 |        3 |        1 |      150 |        1 |        3 |        0 |        0 |        0 |        0
#       28 |        4 |        1 |      200 |        8 |        1 |        0 |        0 |        0 |        0
#       29 |        4 |        2 |      200 |        0 |        0 |        1 |        2 |        0 |        0
#       46 |        6 |        1 |      300 |        1 |        2 |        2 |        0 |        1 |        0
#       47 |        6 |        2 |      300 |        0 |        0 |        1 |        0 |        1 |        1

# status    = OPTIMAL
# parse_sec = 0.000855
# build_sec = 0.000000
# solve_sec = 299.169287
# total_sec = 291.074585
# ===== Running instance5 =====
# [15:23:01] parsed: nbRackModels=2, nbRacks=5, nbCardTypes=5, totalCardInstances=26
# [15:23:01] building F1 with NSC cardinalities and running assumption-based incremental SAT...
# [15:23:01] done | status=OPTIMAL | sat_calls=4 tighten_steps=3 assumption_solves=3 | base_vars=6464 base_clauses=14850
# ==============================================================================================================
# OPT_COST = 700
# USED_RACK-USES = 4  (<= nbRacks = 5)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5
# ---------------------------------------------------------------------------------------------------
#        1 |        1 |        1 |      150 |        7 |        0 |        0 |        0 |        1
#        2 |        1 |        2 |      150 |        0 |        1 |        2 |        1 |        0
#        6 |        2 |        1 |      200 |        0 |        0 |        1 |        0 |        2
#        7 |        2 |        2 |      200 |        5 |        5 |        1 |        0 |        0

# status    = OPTIMAL
# parse_sec = 0.015075
# build_sec = 0.064457
# solve_sec = 0.146706
# total_sec = 0.226238
# ===== Running instance6 =====
# [15:23:01] parsed: nbRackModels=2, nbRacks=6, nbCardTypes=6, totalCardInstances=25
# [15:23:01] building F1 with NSC cardinalities and running assumption-based incremental SAT...
# [15:23:01] done | status=OPTIMAL | sat_calls=6 tighten_steps=5 assumption_solves=5 | base_vars=7430 base_clauses=17022
# ==============================================================================================================
# OPT_COST = 650
# USED_RACK-USES = 4  (<= nbRacks = 6)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5 |    Type6
# --------------------------------------------------------------------------------------------------------------
#        1 |        1 |        1 |      150 |        3 |        1 |        0 |        0 |        0 |        1
#        2 |        1 |        2 |      150 |        4 |        3 |        0 |        1 |        0 |        0
#        3 |        1 |        3 |      150 |        0 |        0 |        0 |        0 |        2 |        0
#        7 |        2 |        1 |      200 |        7 |        0 |        2 |        1 |        0 |        0

# status    = OPTIMAL
# parse_sec = 0.035654
# build_sec = 0.076068
# solve_sec = 0.105106
# total_sec = 0.216828
# ===== Running instance7 =====
# [15:23:01] parsed: nbRackModels=2, nbRacks=7, nbCardTypes=6, totalCardInstances=35
# [15:23:01] building F1 with NSC cardinalities and running assumption-based incremental SAT...
# [15:23:07] done | status=OPTIMAL | sat_calls=6 tighten_steps=5 assumption_solves=5 | base_vars=13776 base_clauses=31777
# ==============================================================================================================
# OPT_COST = 850
# USED_RACK-USES = 5  (<= nbRacks = 7)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5 |    Type6
# --------------------------------------------------------------------------------------------------------------
#        1 |        1 |        1 |      150 |        7 |        0 |        0 |        0 |        1 |        0
#        2 |        1 |        2 |      150 |        2 |        6 |        0 |        0 |        0 |        0
#        3 |        1 |        3 |      150 |        4 |        3 |        1 |        0 |        0 |        0
#        8 |        2 |        1 |      200 |        0 |        1 |        0 |        0 |        1 |        1
#        9 |        2 |        2 |      200 |        5 |        0 |        0 |        3 |        0 |        0

# status    = OPTIMAL
# parse_sec = 0.001187
# build_sec = 1.146164
# solve_sec = 4.039499
# total_sec = 5.186851
# ===== Running instance8 =====
# [15:23:08] parsed: nbRackModels=4, nbRacks=8, nbCardTypes=6, totalCardInstances=36
# [15:23:08] building F1 with NSC cardinalities and running assumption-based incremental SAT...
# [15:23:16] done | status=OPTIMAL | sat_calls=7 tighten_steps=6 assumption_solves=6 | base_vars=25304 base_clauses=58259
# ==============================================================================================================
# OPT_COST = 900
# USED_RACK-USES = 6  (<= nbRacks = 8)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5 |    Type6
# --------------------------------------------------------------------------------------------------------------
#        1 |        1 |        1 |       50 |        0 |        0 |        0 |        1 |        0 |        0
#       17 |        3 |        1 |      150 |        0 |        1 |        0 |        1 |        1 |        0
#       18 |        3 |        2 |      150 |        2 |        1 |        0 |        0 |        0 |        1
#       19 |        3 |        3 |      150 |        5 |        0 |        0 |        0 |        0 |        1
#       25 |        4 |        1 |      200 |        6 |        0 |        1 |        0 |        0 |        1
#       26 |        4 |        2 |      200 |       12 |        0 |        2 |        0 |        0 |        0

# status    = OPTIMAL
# parse_sec = 0.003074
# build_sec = 2.754813
# solve_sec = 4.731603
# total_sec = 7.489491
# ===== Running instance9 =====
# [15:23:19] parsed: nbRackModels=6, nbRacks=6, nbCardTypes=6, totalCardInstances=19
# [15:23:19] building F1 with NSC cardinalities and running assumption-based incremental SAT...
# [15:23:30] done | status=OPTIMAL | sat_calls=8 tighten_steps=7 assumption_solves=7 | base_vars=10736 base_clauses=25560
# ==============================================================================================================
# OPT_COST = 1000
# USED_RACK-USES = 6  (<= nbRacks = 6)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5 |    Type6
# --------------------------------------------------------------------------------------------------------------
#        1 |        1 |        1 |       50 |        0 |        0 |        1 |        0 |        0 |        0
#        2 |        1 |        2 |       50 |        0 |        0 |        1 |        0 |        0 |        0
#       13 |        3 |        1 |      150 |        3 |        0 |        0 |        1 |        0 |        0
#       14 |        3 |        2 |      150 |        0 |        0 |        0 |        2 |        0 |        0
#       31 |        6 |        1 |      300 |        3 |        1 |        0 |        0 |        2 |        0
#       32 |        6 |        2 |      300 |        1 |        2 |        1 |        0 |        0 |        1

# status    = OPTIMAL
# parse_sec = 0.001052
# build_sec = 0.000000
# solve_sec = 11.291113
# total_sec = 11.033563
# ===== Running instance10 =====
# [15:23:30] parsed: nbRackModels=2, nbRacks=14, nbCardTypes=6, totalCardInstances=57
# [15:23:30] building F1 with NSC cardinalities and running assumption-based incremental SAT...
# [16:25:10] done | status=TIME_LIMIT | sat_calls=7 tighten_steps=6 assumption_solves=6 | base_vars=48418 base_clauses=113019
# ==============================================================================================================
# OPT_COST = 1650
# USED_RACK-USES = 9  (<= nbRacks = 14)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5 |    Type6
# --------------------------------------------------------------------------------------------------------------
#        1 |        1 |        1 |      150 |        0 |        0 |        0 |        3 |        0 |        0
#        2 |        1 |        2 |      150 |        0 |        5 |        0 |        1 |        0 |        0
#        3 |        1 |        3 |      150 |        1 |        3 |        0 |        1 |        0 |        0
#       15 |        2 |        1 |      200 |        1 |        0 |        1 |        0 |        2 |        0
#       16 |        2 |        2 |      200 |        6 |        0 |        1 |        0 |        0 |        1
#       17 |        2 |        3 |      200 |        0 |        0 |        5 |        0 |        0 |        0
#       18 |        2 |        4 |      200 |       15 |        0 |        1 |        0 |        0 |        0
#       19 |        2 |        5 |      200 |        1 |        3 |        0 |        1 |        1 |        0
#       20 |        2 |        6 |      200 |        0 |        1 |        2 |        0 |        0 |        1

# status    = TIME_LIMIT
# parse_sec = 0.003327
# build_sec = 0.000000
# solve_sec = 3668.954861
# total_sec = 3600.077007
# (.venv39) hungle@qHung17-ASUS:~/RCP_bench$ for i in 11 12; do   echo "=
# ==== Running instance$i =====";   python src/IncrementalSAT_c1_nsc.py  
#    --inst "instances/instance$i.txt"     --time-limit 3600 ; done
# ===== Running instance11 =====
# [17:20:55] parsed: nbRackModels=6, nbRacks=12, nbCardTypes=6, totalCardInstances=47
# [17:20:55] building F1 with NSC cardinalities and running assumption-based incremental SAT...
# [18:22:45] done | status=TIME_LIMIT | sat_calls=13 tighten_steps=12 assumption_solves=12 | base_vars=75991 base_clauses=190858
# ==============================================================================================================
# OPT_COST = 2250
# USED_RACK-USES = 8  (<= nbRacks = 12)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5 |    Type6
# --------------------------------------------------------------------------------------------------------------
#       25 |        3 |        1 |      150 |        3 |        2 |        0 |        0 |        0 |        0
#       61 |        6 |        1 |      300 |        1 |        2 |        4 |        0 |        0 |        0
#       62 |        6 |        2 |      300 |        0 |        3 |        2 |        1 |        0 |        0
#       63 |        6 |        3 |      300 |        0 |        0 |        0 |        0 |        3 |        0
#       64 |        6 |        4 |      300 |        1 |        2 |        1 |        2 |        0 |        0
#       65 |        6 |        5 |      300 |       10 |        0 |        0 |        0 |        1 |        0
#       66 |        6 |        6 |      300 |        3 |        1 |        1 |        0 |        0 |        1
#       67 |        6 |        7 |      300 |        0 |        0 |        0 |        2 |        0 |        1

# status    = TIME_LIMIT
# parse_sec = 0.002112
# build_sec = 0.000000
# solve_sec = 3702.780715
# total_sec = 3600.485430
# ===== Running instance12 =====
# [18:22:52] parsed: nbRackModels=6, nbRacks=13, nbCardTypes=7, totalCardInstances=62
# [18:22:52] building F1 with NSC cardinalities and running assumption-based incremental SAT...
# [19:25:01] done | status=TIME_LIMIT | sat_calls=7 tighten_steps=6 assumption_solves=6 | base_vars=128196 base_clauses=320595
# ==============================================================================================================
# OPT_COST = 2400
# USED_RACK-USES = 10  (<= nbRacks = 13)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5 |    Type6 |    Type7
# -------------------------------------------------------------------------------------------------------------------------
#        1 |        1 |        1 |       50 |        1 |        0 |        1 |        0 |        0 |        0 |        0
#       14 |        2 |        1 |      100 |        1 |        2 |        0 |        1 |        0 |        0 |        0
#       53 |        5 |        1 |      250 |        0 |        1 |        0 |        0 |        3 |        0 |        0
#       54 |        5 |        2 |      250 |        3 |        1 |        5 |        0 |        0 |        0 |        0
#       55 |        5 |        3 |      250 |        1 |        7 |        0 |        0 |        0 |        1 |        0
#       66 |        6 |        1 |      300 |        1 |        1 |        3 |        0 |        2 |        0 |        0
#       67 |        6 |        2 |      300 |        2 |        0 |        0 |        0 |        1 |        2 |        0
#       68 |        6 |        3 |      300 |        1 |        0 |        1 |        0 |        0 |        1 |        1
#       69 |        6 |        4 |      300 |        0 |        0 |        0 |        6 |        0 |        0 |        0
#       70 |        6 |        5 |      300 |       10 |        0 |        0 |        1 |        0 |        0 |        1

# status    = TIME_LIMIT
# parse_sec = 0.002791
# build_sec = 229.541008
# solve_sec = 3371.073817
# total_sec = 3600.617615
# (.venv39) hungle@qHung17-ASUS:~/RCP_bench$ 