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
from functools import lru_cache

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
def _model_max_uses(sat: IntegratedModelSAT, m: int) -> int:
    """
    Maximum number of rack-uses that model m can contribute.
    Because of the global card constraint sum_{m,r} w(m,r) <= nbRacks,
    each model can be used at most nbRacks times.
    """
    return sat.inst.nbRacks


def _enumerate_min_bad_count_combinations(
    sat: IntegratedModelSAT,
    bound: int,
) -> List[Tuple[Tuple[int, int], ...]]:
    """
    Return minimal 'bad' combinations of per-model counts.

    A combination is represented as a tuple:
        ((m1, a1), (m2, a2), ...)

    meaning:
        count_m1 >= a1, count_m2 >= a2, ...
    and the total cost strictly exceeds 'bound'.

    We only keep minimal bad combinations:
      - total_cost > bound
      - for every chosen (m,a), decreasing a by 1 makes total_cost <= bound

    Because w(m,r) already forms a unary prefix for count of model m,
    the clause
        (-act OR -w(m1,a1) OR -w(m2,a2) ...)
    forbids that bad combination.
    """
    models = list(sat.M)
    max_use = {m: _model_max_uses(sat, m) for m in models}
    cost = {m: sat.Costm(m) for m in models}

    bad: List[Tuple[Tuple[int, int], ...]] = []

    def dfs(idx: int, current_cost: int, chosen: Dict[int, int]) -> None:
        if idx == len(models):
            if current_cost > bound:
                # minimality check
                for m, a in chosen.items():
                    if a <= 0:
                        continue
                    reduced_cost = current_cost - cost[m]
                    if reduced_cost > bound:
                        return
                combo = tuple((m, chosen[m]) for m in models if chosen[m] > 0)
                bad.append(combo)
            return

        m = models[idx]
        cm = cost[m]
        ub = max_use[m]

        # Try all possible counts for this model.
        # We keep full enumeration because number of rack models is small.
        for a in range(0, ub + 1):
            chosen[m] = a
            dfs(idx + 1, current_cost + cm * a, chosen)

        chosen.pop(m, None)

    dfs(0, 0, {})
    return bad


@lru_cache(maxsize=None)
def _cached_bad_count_combinations(
    nb_models: int,
    nb_racks: int,
    costs_sig: Tuple[int, ...],
    bound: int,
) -> Tuple[Tuple[Tuple[int, int], ...], ...]:
    """
    Cache bad combinations by structural signature:
      - nb_models
      - nb_racks
      - cost vector
      - bound

    This avoids recomputing combination sets if the same bound is requested again.
    """
    # Rebuild a lightweight pseudo-structure for enumeration
    class _FakeSat:
        pass

    fake = _FakeSat()
    fake.M = list(range(1, nb_models + 1))

    class _FakeInst:
        pass

    fake.inst = _FakeInst()
    fake.inst.nbRacks = nb_racks

    def _costm(m: int) -> int:
        return costs_sig[m - 1]

    fake.Costm = _costm

    combos = _enumerate_min_bad_count_combinations(fake, bound)
    return tuple(combos)


def _get_bad_count_combinations(
    sat: IntegratedModelSAT,
    bound: int,
) -> List[Tuple[Tuple[int, int], ...]]:
    costs_sig = tuple(sat.Costm(m) for m in sat.M)
    return list(
        _cached_bad_count_combinations(
            len(sat.M),
            sat.inst.nbRacks,
            costs_sig,
            bound,
        )
    )


def encode_cost_le_assumption(
    sat: IntegratedModelSAT,
    bound: int,
    tag: str,
) -> Tuple[List[List[int]], int]:
    """
    Encode:
        act => (total cost <= bound)

    New version:
      - do NOT build a fresh PB encoding over all w(m,r)
      - use the existing unary prefix variables w(m,r) directly as count bits
      - forbid minimal bad count combinations whose total cost exceeds bound

    Clause schema:
        (-act OR -w(m1,a1) OR -w(m2,a2) ...)

    meaning:
        if act is assumed true, then that bad count combination is forbidden.
    """
    act = sat.vpool.id(f"act_cost_le_{bound}_{tag}")

    bad_combos = _get_bad_count_combinations(sat, bound)
    gated: List[List[int]] = []

    for combo in bad_combos:
        cl = [-act]
        for (m, a) in combo:
            # count_m >= a  <=>  w(m,a) = 1, thanks to prefix semantics
            cl.append(-sat.w(m, a))
        gated.append(cl)

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





#     (.venv39) hungle@qHung17-ASUS:~/RCP_bench$ for i in 1 2 3 4 5 6 7 8 9 10 11 12 ; do echo "====instance$i===="  ;python src
# /test.py --inst instances/instance$i.txt --solver g42 --time-limit 3600; done
# ====instance1====
# [22:59:25] parsed: nbRackModels=2, nbRacks=5, nbCardTypes=4, totalCardInstances=17
# [22:59:25] building F1 and running assumption-based incremental SAT...
# [22:59:25] done | status=OPTIMAL | sat_calls=7 tighten_steps=6 assumption_solves=6 | base_vars=2578 base_clauses=5997
# ==============================================================================================================
# OPT_COST = 550
# USED_RACK-USES = 3  (<= nbRacks = 5)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4
# ----------------------------------------------------------------------------------------
#        1 |        1 |        1 |      150 |        3 |        1 |        1 |        0
#        6 |        2 |        1 |      200 |        3 |        0 |        1 |        1
#        7 |        2 |        2 |      200 |        4 |        3 |        0 |        0

# status    = OPTIMAL
# parse_sec = 0.000813
# build_sec = 0.024097
# solve_sec = 0.003766
# total_sec = 0.028676
# ====instance2====
# [22:59:26] parsed: nbRackModels=2, nbRacks=10, nbCardTypes=4, totalCardInstances=34
# [22:59:26] building F1 and running assumption-based incremental SAT...
# [22:59:30] done | status=OPTIMAL | sat_calls=10 tighten_steps=9 assumption_solves=9 | base_vars=15356 base_clauses=36148
# ==============================================================================================================
# OPT_COST = 1100
# USED_RACK-USES = 6  (<= nbRacks = 10)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4
# ----------------------------------------------------------------------------------------
#        1 |        1 |        1 |      150 |        3 |        1 |        1 |        0
#        2 |        1 |        2 |      150 |        0 |        0 |        0 |        2
#       11 |        2 |        1 |      200 |        8 |        1 |        0 |        0
#       12 |        2 |        2 |      200 |        6 |        2 |        0 |        0
#       13 |        2 |        3 |      200 |        1 |        2 |        2 |        0
#       14 |        2 |        4 |      200 |        2 |        2 |        1 |        0

# status    = OPTIMAL
# parse_sec = 0.002710
# build_sec = 1.286876
# solve_sec = 2.859744
# total_sec = 4.149329
# ====instance3====
# [22:59:31] parsed: nbRackModels=2, nbRacks=12, nbCardTypes=6, totalCardInstances=45
# [22:59:31] building F1 and running assumption-based incremental SAT...
# [23:14:16] done | status=OPTIMAL | sat_calls=10 tighten_steps=9 assumption_solves=9 | base_vars=29955 base_clauses=69179
# ==============================================================================================================
# OPT_COST = 1200
# USED_RACK-USES = 8  (<= nbRacks = 12)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5 |    Type6
# --------------------------------------------------------------------------------------------------------------
#        1 |        1 |        1 |      150 |        5 |        1 |        2 |        0 |        0 |        0
#        2 |        1 |        2 |      150 |        7 |        0 |        0 |        0 |        1 |        0
#        3 |        1 |        3 |      150 |        5 |        0 |        0 |        0 |        0 |        1
#        4 |        1 |        4 |      150 |        0 |        7 |        0 |        0 |        0 |        0
#        5 |        1 |        5 |      150 |        1 |        1 |        3 |        0 |        0 |        0
#        6 |        1 |        6 |      150 |        0 |        0 |        0 |        3 |        0 |        0
#        7 |        1 |        7 |      150 |        2 |        0 |        0 |        1 |        1 |        0
#        8 |        1 |        8 |      150 |        0 |        1 |        3 |        0 |        0 |        0

# status    = OPTIMAL
# parse_sec = 0.000956
# build_sec = 0.000000
# solve_sec = 879.643891
# total_sec = 848.302275
# ====instance4====
# [23:14:21] parsed: nbRackModels=6, nbRacks=9, nbCardTypes=6, totalCardInstances=25
# [23:14:21] building F1 and running assumption-based incremental SAT...
# [23:30:01] done | status=OPTIMAL | sat_calls=14 tighten_steps=13 assumption_solves=13 | base_vars=21881 base_clauses=52573
# ==============================================================================================================
# OPT_COST = 1150
# USED_RACK-USES = 6  (<= nbRacks = 9)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5 |    Type6
# --------------------------------------------------------------------------------------------------------------
#        1 |        1 |        1 |       50 |        0 |        0 |        1 |        0 |        0 |        0
#       10 |        2 |        1 |      100 |        1 |        0 |        0 |        1 |        0 |        0
#       11 |        2 |        2 |      100 |        1 |        0 |        0 |        1 |        0 |        0
#       46 |        6 |        1 |      300 |        5 |        0 |        0 |        0 |        2 |        0
#       47 |        6 |        2 |      300 |        2 |        4 |        2 |        0 |        0 |        0
#       48 |        6 |        3 |      300 |        1 |        2 |        1 |        0 |        0 |        1

# status    = OPTIMAL
# parse_sec = 0.003187
# build_sec = 0.000000
# solve_sec = 936.360860
# total_sec = 899.424320
# ====instance5====
# [23:30:02] parsed: nbRackModels=2, nbRacks=5, nbCardTypes=5, totalCardInstances=26
# [23:30:02] building F1 and running assumption-based incremental SAT...
# [23:30:02] done | status=OPTIMAL | sat_calls=3 tighten_steps=2 assumption_solves=2 | base_vars=5714 base_clauses=13116
# ==============================================================================================================
# OPT_COST = 700
# USED_RACK-USES = 4  (<= nbRacks = 5)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5
# ---------------------------------------------------------------------------------------------------
#        1 |        1 |        1 |      150 |        0 |        0 |        0 |        0 |        2
#        2 |        1 |        2 |      150 |        6 |        0 |        2 |        0 |        0
#        6 |        2 |        1 |      200 |        3 |        6 |        0 |        1 |        0
#        7 |        2 |        2 |      200 |        3 |        0 |        2 |        0 |        1

# status    = OPTIMAL
# parse_sec = 0.003190
# build_sec = 0.066193
# solve_sec = 0.113917
# total_sec = 0.183301
# ====instance6====
# [23:30:02] parsed: nbRackModels=2, nbRacks=6, nbCardTypes=6, totalCardInstances=25
# [23:30:02] building F1 and running assumption-based incremental SAT...
# [23:30:02] done | status=OPTIMAL | sat_calls=7 tighten_steps=6 assumption_solves=6 | base_vars=6527 base_clauses=14941
# ==============================================================================================================
# OPT_COST = 650
# USED_RACK-USES = 4  (<= nbRacks = 6)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5 |    Type6
# --------------------------------------------------------------------------------------------------------------
#        1 |        1 |        1 |      150 |        2 |        4 |        0 |        1 |        0 |        0
#        2 |        1 |        2 |      150 |        5 |        0 |        0 |        0 |        0 |        1
#        3 |        1 |        3 |      150 |        2 |        0 |        2 |        1 |        0 |        0
#        7 |        2 |        1 |      200 |        5 |        0 |        0 |        0 |        2 |        0

# status    = OPTIMAL
# parse_sec = 0.003318
# build_sec = 0.074771
# solve_sec = 0.119493
# total_sec = 0.197582
# ====instance7====
# [23:30:02] parsed: nbRackModels=2, nbRacks=7, nbCardTypes=6, totalCardInstances=35
# [23:30:02] building F1 and running assumption-based incremental SAT...
# [23:30:10] done | status=OPTIMAL | sat_calls=9 tighten_steps=8 assumption_solves=8 | base_vars=12719 base_clauses=29208
# ==============================================================================================================
# OPT_COST = 850
# USED_RACK-USES = 5  (<= nbRacks = 7)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5 |    Type6
# --------------------------------------------------------------------------------------------------------------
#        1 |        1 |        1 |      150 |        2 |        3 |        1 |        0 |        0 |        0
#        2 |        1 |        2 |      150 |        1 |        7 |        0 |        0 |        0 |        0
#        3 |        1 |        3 |      150 |        0 |        0 |        0 |        0 |        2 |        0
#        8 |        2 |        1 |      200 |        0 |        0 |        0 |        2 |        0 |        1
#        9 |        2 |        2 |      200 |       15 |        0 |        0 |        1 |        0 |        0

# status    = OPTIMAL
# parse_sec = 0.001429
# build_sec = 0.945597
# solve_sec = 4.859919
# total_sec = 5.806945
# ====instance8====
# [23:30:11] parsed: nbRackModels=4, nbRacks=8, nbCardTypes=6, totalCardInstances=36
# [23:30:11] building F1 and running assumption-based incremental SAT...
# [23:30:20] done | status=OPTIMAL | sat_calls=8 tighten_steps=7 assumption_solves=7 | base_vars=24036 base_clauses=54607
# ==============================================================================================================
# OPT_COST = 900
# USED_RACK-USES = 7  (<= nbRacks = 8)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5 |    Type6
# --------------------------------------------------------------------------------------------------------------
#        1 |        1 |        1 |       50 |        0 |        2 |        0 |        0 |        0 |        0
#        2 |        1 |        2 |       50 |        0 |        0 |        0 |        1 |        0 |        0
#       17 |        3 |        1 |      150 |        0 |        0 |        0 |        1 |        0 |        1
#       18 |        3 |        2 |      150 |        7 |        0 |        0 |        0 |        1 |        0
#       19 |        3 |        3 |      150 |        5 |        0 |        0 |        0 |        0 |        1
#       20 |        3 |        4 |      150 |        5 |        0 |        0 |        0 |        0 |        1
#       25 |        4 |        1 |      200 |        8 |        0 |        3 |        0 |        0 |        0

# status    = OPTIMAL
# parse_sec = 0.001283
# build_sec = 2.428071
# solve_sec = 7.207581
# total_sec = 9.636935
# ====instance9====
# [23:30:23] parsed: nbRackModels=6, nbRacks=6, nbCardTypes=6, totalCardInstances=19
# [23:30:23] building F1 and running assumption-based incremental SAT...
# [23:30:44] done | status=OPTIMAL | sat_calls=8 tighten_steps=7 assumption_solves=7 | base_vars=9791 base_clauses=23005
# ==============================================================================================================
# OPT_COST = 1000
# USED_RACK-USES = 5  (<= nbRacks = 6)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5 |    Type6
# --------------------------------------------------------------------------------------------------------------
#       19 |        4 |        1 |      200 |        0 |        0 |        0 |        0 |        2 |        0
#       20 |        4 |        2 |      200 |        2 |        0 |        0 |        0 |        0 |        1
#       21 |        4 |        3 |      200 |        0 |        0 |        1 |        2 |        0 |        0
#       22 |        4 |        4 |      200 |        3 |        1 |        2 |        0 |        0 |        0
#       23 |        4 |        5 |      200 |        2 |        2 |        0 |        1 |        0 |        0

# status    = OPTIMAL
# parse_sec = 0.001268
# build_sec = 0.000000
# solve_sec = 19.674031
# total_sec = 19.085309
# ====instance10====
# [23:30:44] parsed: nbRackModels=2, nbRacks=14, nbCardTypes=6, totalCardInstances=57
# [23:30:44] building F1 and running assumption-based incremental SAT...
# [00:33:30] done | status=TIME_LIMIT | sat_calls=11 tighten_steps=10 assumption_solves=10 | base_vars=46255 base_clauses=107154
# ==============================================================================================================
# OPT_COST = 1650
# USED_RACK-USES = 10  (<= nbRacks = 14)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5 |    Type6
# --------------------------------------------------------------------------------------------------------------
#        1 |        1 |        1 |      150 |        1 |        1 |        3 |        0 |        0 |        0
#        2 |        1 |        2 |      150 |        1 |        0 |        1 |        2 |        0 |        0
#        3 |        1 |        3 |      150 |        0 |        3 |        0 |        0 |        1 |        0
#        4 |        1 |        4 |      150 |        1 |        1 |        3 |        0 |        0 |        0
#        5 |        1 |        5 |      150 |        3 |        0 |        0 |        2 |        0 |        0
#        6 |        1 |        6 |      150 |        0 |        0 |        0 |        0 |        2 |        0
#        7 |        1 |        7 |      150 |        6 |        0 |        1 |        1 |        0 |        0
#       15 |        2 |        1 |      200 |        0 |        3 |        2 |        1 |        0 |        0
#       16 |        2 |        2 |      200 |        0 |        0 |        0 |        0 |        0 |        2
#       17 |        2 |        3 |      200 |       12 |        4 |        0 |        0 |        0 |        0

# status    = TIME_LIMIT
# parse_sec = 0.001607
# build_sec = 0.000000
# solve_sec = 3736.117024
# total_sec = 3600.392120
# ====instance11====
# [00:34:01] parsed: nbRackModels=6, nbRacks=12, nbCardTypes=6, totalCardInstances=47
# [00:34:01] building F1 and running assumption-based incremental SAT...
