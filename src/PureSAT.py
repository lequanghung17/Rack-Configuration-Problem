# integrated_puresat.py
# Pure SAT optimization for Rack Configuration Problem (CSPLib prob31)
# using Integrated model (rel + a + w) + SB3-prefix + load ordering,
# and PureSAT loop: SAT(F1 ∧ (F0 ≤ k)) tighten k incrementally.

import os
import re
import time
import argparse
from dataclasses import dataclass
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
# Parsing (same spirit as your MaxSAT wrappers)
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
    # ALO
    cnf.append(lits[:])
    # AMO
    if len(lits) <= 4:
        for i in range(len(lits)):
            for j in range(i + 1, len(lits)):
                cnf.append([-lits[i], -lits[j]])
    else:
        amo = CardEnc.atmost(lits=lits, bound=1, encoding=CardEncType.seqcounter, vpool=vpool)
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

        # P list: ordered rack-uses
        self.P_list: List[Tuple[int, int]] = [(m, r) for m in self.M for r in self.R]
        self.P_size = len(self.P_list)

        self._rel: Dict[Tuple[int, int, int, int], int] = {}
        self._a: Dict[Tuple[int, int, int, int], int] = {}
        self._w: Dict[Tuple[int, int], int] = {}
        self._pref: Dict[Tuple[int, int, int], int] = {}
        self._L: Dict[Tuple[int, int, int], int] = {}  # L(m,r,k)

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

    # build F1
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
        # ExactlyOne for each card instance
        for (c, t) in self.Q:
            lits = [self.rel(m, r, c, t) for (m, r) in self.P_list]
            add_exactly_one(self.cnf, lits, self.vpool)

        # weights for power PB (aligned with rel_lits order over Q)
        pow_weights = [self.inst.cardTypes[c - 1].power for (c, _t) in self.Q]

        # per rack-use constraints
        for (m, r) in self.P_list:
            rel_lits = [self.rel(m, r, c, t) for (c, t) in self.Q]
            wm = self.w(m, r)

            # rel -> w
            for lit in rel_lits:
                self.cnf.append([-lit, wm])

            # w -> OR(rel)  (avoid empty-active rack)
            self.cnf.append([-wm] + rel_lits)

            # connector capacity: sum rel <= Sm(m)
            con = CardEnc.atmost(
                lits=rel_lits,
                bound=self.Sm(m),
                encoding=CardEncType.seqcounter,
                vpool=self.vpool,
            )
            self.cnf.extend(con.clauses)

            # power capacity: sum power*rel <= Pm(m)
            pbp = PBEnc.leq(
                lits=rel_lits,
                weights=pow_weights,
                bound=self.Pm(m),
                vpool=self.vpool,
                encoding=PBEncType.best,
            )
            self.cnf.extend(pbp.clauses)

            # L-bits via totalizer (unary load)
            ub = min(self.Sm(m), len(rel_lits))
            if ub > 0:
                # ensure totalizer uses fresh ids above current pool
                tot = ITotalizer(rel_lits, ubound=ub, top_id=self.vpool.top)
                self.cnf.extend(tot.cnf.clauses)

                for k in range(1, ub + 1):
                    self._L[(m, r, k)] = tot.rhs[k - 1]

                # advance pool top so future encoders don't reuse ids
                if hasattr(tot, "top_id") and tot.top_id is not None:
                    self.vpool.top = max(self.vpool.top, tot.top_id)
                else:
                    # conservative fallback
                    mx = 0
                    for cl in tot.cnf.clauses:
                        for lit in cl:
                            mx = max(mx, abs(lit))
                    self.vpool.top = max(self.vpool.top, mx)

        # total number of active rack-uses <= nbRacks
        w_lits = [self.w(m, r) for (m, r) in self.P_list]
        card = CardEnc.atmost(
            lits=w_lits,
            bound=self.inst.nbRacks,
            encoding=CardEncType.seqcounter,
            vpool=self.vpool,
        )
        self.cnf.extend(card.clauses)

        # per model: w(m,r) -> w(m,r-1)
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
                # j=1 base
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

                    # pprev -> pj
                    self.cnf.append([-pprev, pj])
                    # aj -> pj
                    self.cnf.append([-aj, pj])
                    # pj -> (pprev OR aj)
                    self.cnf.append([-pj, pprev, aj])

            # SB3 ordering: pref(c,t,j) -> pref(c,t-1,j)
            for t in range(2, d + 1):
                for j in range(1, P + 1):
                    self.cnf.append([-self.pref(c, t, j), self.pref(c, t - 1, j)])

    def _add_load_nonincreasing_symmetry(self):
        # If both rack-uses active: load(m,r) <= load(m,r-1)
        for m in self.M:
            ub = min(self.Sm(m), len(self.Q))
            if ub <= 0:
                continue
            for r in range(2, self.inst.nbRacks + 1):
                w_prev = self.w(m, r - 1)
                w_cur = self.w(m, r)
                for k in range(1, ub + 1):
                    self.cnf.append([-w_prev, -w_cur, -self.L(m, r, k), self.L(m, r - 1, k)])

    # F0 helpers (objective)
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
# PureSAT optimize: incremental tightening
# -------------------------
def optimize_puresat(inst: Instance, solver_name: str = "g42", start_ub: Optional[int] = None) -> Tuple[Optional[List[int]], Optional[int], Dict[str, int]]:
    sat = IntegratedModelSAT(inst)
    sat.build_F1()

    stats = {
        "vars_base": sat.vpool.top,
        "clauses_base": len(sat.cnf.clauses),
        "sat_calls": 0,
        "tighten_steps": 0,
    }

    best_model: Optional[List[int]] = None
    best_cost: Optional[int] = None

    with Solver(name=solver_name, bootstrap_with=sat.cnf.clauses) as s:
        # If user provides a starting UB, add F0 <= UB first
        if start_ub is not None:
            w_lits, weights = sat.cost_terms()
            pb = PBEnc.leq(lits=w_lits, weights=weights, bound=start_ub, vpool=sat.vpool, encoding=PBEncType.best)
            for cl in pb.clauses:
                s.add_clause(cl)
            stats["tighten_steps"] += 1

        while True:
            stats["sat_calls"] += 1
            ok = s.solve()
            if not ok:
                break

            model = s.get_model()
            cost = sat.model_cost(model)

            best_model = model
            best_cost = cost

            # tighten: F0 <= cost-1
            new_bound = cost - 1
            if new_bound < 0:
                break

            w_lits, weights = sat.cost_terms()
            pb = PBEnc.leq(lits=w_lits, weights=weights, bound=new_bound, vpool=sat.vpool, encoding=PBEncType.best)
            for cl in pb.clauses:
                s.add_clause(cl)
            stats["tighten_steps"] += 1

    return best_model, best_cost, stats


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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--inst", required=True, help="instance .txt file")
    ap.add_argument("--solver", default="g42", help="PySAT solver name (e.g., g3, g42, m22, cadical153, ...)")
    ap.add_argument("--ub", type=int, default=None, help="optional starting UB for F0 (sum cost*w) <= ub")
    args = ap.parse_args()

    inst = parse_instance_file(args.inst)
    total_cards = sum(ct.demand for ct in inst.cardTypes)
    log(f"parsed: nbRackModels={inst.nbRackModels}, nbRacks={inst.nbRacks}, nbCardTypes={inst.nbCardTypes}, totalCardInstances={total_cards}")

    log("building F1 (Integrated hard constraints + SB3 + load ordering)...")
    t0 = time.time()
    model, opt_cost, stats = optimize_puresat(inst, solver_name=args.solver, start_ub=args.ub)
    log(f"done in {time.time() - t0:.2f}s | sat_calls={stats['sat_calls']} tighten_steps={stats['tighten_steps']} | base_vars={stats['vars_base']} base_clauses={stats['clauses_base']}")

    if model is None:
        print("\nUNSAT: no feasible solution for F1 (or given UB too small).\n")
        return

    # decode
    sat = IntegratedModelSAT(inst)
    sat.build_F1()
    active, counts = sat.decode_counts(model)
    print_solution(inst, active, counts, opt_cost=opt_cost)


if __name__ == "__main__":
    main()