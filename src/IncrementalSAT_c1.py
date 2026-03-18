# incremental_sat_assumption_full.py
# Incremental SAT optimization for Rack Configuration Problem
# using Integrated model (rel + a + w) + SB3-prefix + load ordering
# and assumption-based incremental linear search.

import re
import time
import argparse
from dataclasses import dataclass
from threading import Timer
from typing import List, Tuple, Dict, Optional

from pysat.formula import CNF, IDPool
from pysat.card import CardEnc, EncType as CardEncType, ITotalizer
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
# CNF helpers
# -------------------------
def add_exactly_one(cnf: CNF, lits: List[int], vpool: IDPool):
    # at least one
    cnf.append(lits[:])

    # at most one
    if len(lits) <= 4:
        for i in range(len(lits)):
            for j in range(i + 1, len(lits)):
                cnf.append([-lits[i], -lits[j]])
    else:
        amo = CardEnc.atmost(
            lits=lits,
            bound=1,
            encoding=CardEncType.seqcounter,
            vpool=vpool,
        )
        cnf.extend(amo.clauses)


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
        # each card instance assigned exactly once
        for (c, t) in self.Q:
            lits = [self.rel(m, r, c, t) for (m, r) in self.P_list]
            add_exactly_one(self.cnf, lits, self.vpool)

        pow_weights = [self.inst.cardTypes[c - 1].power for (c, _t) in self.Q]

        for (m, r) in self.P_list:
            rel_lits = [self.rel(m, r, c, t) for (c, t) in self.Q]
            wm = self.w(m, r)

            # rel -> w
            for lit in rel_lits:
                self.cnf.append([-lit, wm])

            # w -> OR(rel)
            self.cnf.append([-wm] + rel_lits)

            # connector capacity
            con = CardEnc.atmost(
                lits=rel_lits,
                bound=self.Sm(m),
                encoding=CardEncType.seqcounter,
                vpool=self.vpool,
            )
            self.cnf.extend(con.clauses)

            # power capacity
            pbp = PBEnc.leq(
                lits=rel_lits,
                weights=pow_weights,
                bound=self.Pm(m),
                vpool=self.vpool,
                encoding=PBEncType.best,
            )
            self.cnf.extend(pbp.clauses)

            # unary load bits by totalizer
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
        card = CardEnc.atmost(
            lits=w_lits,
            bound=self.inst.nbRacks,
            encoding=CardEncType.seqcounter,
            vpool=self.vpool,
        )
        self.cnf.extend(card.clauses)

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

    # If total time already exceeded before solving starts
    if deadline is not None and time.perf_counter() >= deadline:
        stats["status"] = "TIME_LIMIT"
        return best_model, best_cost, stats

    with Solver(name=solver_name, bootstrap_with=sat.cnf.clauses, use_timer=True) as s:
        first_assumptions: List[int] = []

        # optional initial UB as activated bound
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

        # incremental linear descent
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

    # total time = parse + build/encode + solve
    t_total0 = time.perf_counter()
    deadline = None if args.time_limit is None else t_total0 + float(args.time_limit)

    # parse
    inst = parse_instance_file(args.inst)
    t_parse1 = time.perf_counter()

    total_cards = sum(ct.demand for ct in inst.cardTypes)
    log(
        f"parsed: nbRackModels={inst.nbRackModels}, nbRacks={inst.nbRacks}, "
        f"nbCardTypes={inst.nbCardTypes}, totalCardInstances={total_cards}"
    )

    # optimize (includes building inside)
    log("building F1 and running assumption-based incremental SAT...")
    model, opt_cost, stats = optimize_incremental_assumption(
        inst,
        solver_name=args.solver,
        start_ub=args.ub,
        deadline=deadline,
    )
    t_solve1 = time.perf_counter()

    # build_sec here is total_after_parse - solver_time, because build is inside optimize()
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

    # decode using fresh build (same variable order)
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