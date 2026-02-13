# modelA_bound.py
import os
import re
import argparse
from dataclasses import dataclass
from typing import List, Tuple, Dict, Optional

from pysat.formula import CNF, IDPool
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType as CardEncType, ITotalizer
from pysat.pb import PBEnc, EncType as PBEncType


# ============================================================
# Data classes
# ============================================================

@dataclass
class RackModel:
    power_cap: int   # Pm
    connectors: int  # Sm
    cost: int        # Costm


@dataclass
class CardType:
    power: int   # Powc
    demand: int  # Dc


@dataclass
class Instance:
    nbRackModels: int
    nbCardTypes: int
    nbRacks: int
    rackModels: List[RackModel]
    cardTypes: List[CardType]


# ============================================================
# Robust file reading (UTF-8 / UTF-8 BOM / UTF-16)
# ============================================================

def read_text_auto(path: str) -> str:
    raw = open(path, "rb").read()

    # UTF-16 BOM
    if raw.startswith(b"\xff\xfe") or raw.startswith(b"\xfe\xff"):
        txt = raw.decode("utf-16", errors="ignore")
    # UTF-8 BOM
    elif raw.startswith(b"\xef\xbb\xbf"):
        txt = raw.decode("utf-8-sig", errors="ignore")
    else:
        # Heuristic: nếu có nhiều NUL -> UTF-16LE/BE (không BOM)
        nul = raw.count(b"\x00")
        if len(raw) and nul / len(raw) > 0.05:
            # thử LE trước (Windows thường LE)
            try:
                txt = raw.decode("utf-16le", errors="ignore")
            except Exception:
                txt = raw.decode("utf-16be", errors="ignore")
        else:
            txt = raw.decode("utf-8", errors="ignore")

    # Remove NULs just in case + normalize
    txt = txt.replace("\x00", "")
    return txt



def normalize_text(s: str) -> str:
    s = s.replace("\ufeff", "")
    s = s.replace("\xa0", " ")  # NBSP
    s = re.sub(r"[\u200b\u200c\u200d\u2060]", "", s)  # zero-width
    s = s.replace("\r\n", "\n").replace("\r", "\n")
    return s



# ============================================================
# Parsing instance (format like your files)
# ============================================================

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
    tuples: List[Tuple[int, ...]] = []
    for mm in re.finditer(r"<\s*([^>]+?)\s*>", block, flags=re.DOTALL):
        inside = mm.group(1)
        nums = [int(x.strip()) for x in inside.split(",") if x.strip()]
        tuples.append(tuple(nums))
    return tuples


def parse_instance_text(text: str) -> Instance:
    text = normalize_text(text)

    nbRackModels = _extract_int_field(text, "nbRackModels")
    nbCardTypes  = _extract_int_field(text, "nbCardTypes")
    nbRacks      = _extract_int_field(text, "nbRacks")

    rm_block = _extract_block(text, "RackModels")
    ct_block = _extract_block(text, "CardTypes")

    rm_tuples = _parse_angle_tuples(rm_block)  # <P,S,Cost>
    ct_tuples = _parse_angle_tuples(ct_block)  # <Pow,Demand>

    if len(rm_tuples) != nbRackModels:
        raise ValueError(f"RackModels count mismatch: got {len(rm_tuples)} expected {nbRackModels}")
    if len(ct_tuples) != nbCardTypes:
        raise ValueError(f"CardTypes count mismatch: got {len(ct_tuples)} expected {nbCardTypes}")

    for t in rm_tuples:
        if len(t) != 3:
            raise ValueError(f"RackModels tuple must be <P,S,Cost>, got {t}")
    for t in ct_tuples:
        if len(t) != 2:
            raise ValueError(f"CardTypes tuple must be <Pow,Demand>, got {t}")

    rackModels = [RackModel(power_cap=p, connectors=s, cost=c) for (p, s, c) in rm_tuples]
    cardTypes  = [CardType(power=powc, demand=dem) for (powc, dem) in ct_tuples]
    return Instance(nbRackModels, nbCardTypes, nbRacks, rackModels, cardTypes)


def parse_instance_file(path: str) -> Instance:
    return parse_instance_text(read_text_auto(path))


# ============================================================
# CNF helpers
# ============================================================

def add_exactly_one(cnf: CNF, lits: List[int], vpool: IDPool):
    # ExactlyOne = ALO + AMO
    cnf.append(lits[:])  # ALO
    if len(lits) <= 20:
        for i in range(len(lits)):
            for j in range(i + 1, len(lits)):
                cnf.append([-lits[i], -lits[j]])
    else:
        amo = CardEnc.atmost(lits=lits, bound=1, encoding=CardEncType.seqcounter, vpool=vpool)
        cnf.extend(amo.clauses)


def add_pb_leq_gated(
    cnf: CNF,
    lits: List[int],
    weights: List[int],
    bound: int,
    vpool: IDPool,
    gate_lit: Optional[int] = None,
):
    """
    Encode sum(weights[i]*lits[i]) <= bound using PBEnc (pblib).
    If gate_lit is provided, every clause becomes [gate_lit] + clause.
    gate_lit should be -x for 'x -> constraint'.
    """
    enc = PBEnc.leq(lits=lits, weights=weights, bound=bound, vpool=vpool, encoding=PBEncType.best)
    if gate_lit is None:
        cnf.extend(enc.clauses)
    else:
        for cl in enc.clauses:
            cnf.append([gate_lit] + cl)

def make_itotalizer(lits, ub, vpool):
    """
    Compatible with different PySAT versions.
    Tries several ITotalizer signatures.
    """
    try:
        # newest style (some versions): ITotalizer(lits, ubound, vpool=...)
        return ITotalizer(lits, ub, vpool=vpool)
    except TypeError:
        pass
    try:
        # some versions: ITotalizer(lits=lits, ubound=..., vpool=...)
        return ITotalizer(lits=lits, ubound=ub, vpool=vpool)
    except TypeError:
        pass
    # last resort: no vpool keyword
    return ITotalizer(lits, ub)

# ============================================================
# Model A
# ============================================================

class ModelA:
    def __init__(self, inst: Instance):
        self.inst = inst
        self.vpool = IDPool()
        self.cnf = CNF()

        self.R = list(range(1, inst.nbRacks + 1))
        self.M = list(range(1, inst.nbRackModels + 1))
        self.M0 = [0] + self.M  # include dummy 0
        self.C = list(range(1, inst.nbCardTypes + 1))

        # Card instances Q = [(c,t)]
        self.Q: List[Tuple[int, int]] = []
        for c in self.C:
            for t in range(1, inst.cardTypes[c - 1].demand + 1):
                self.Q.append((c, t))

        self._x: Dict[Tuple[int, int], int] = {}
        self._z: Dict[Tuple[int, int, int], int] = {}

    def x(self, r: int, m: int) -> int:
        k = (r, m)
        if k not in self._x:
            self._x[k] = self.vpool.id(f"x_{r}_{m}")
        return self._x[k]

    def z(self, r: int, c: int, t: int) -> int:
        k = (r, c, t)
        if k not in self._z:
            self._z[k] = self.vpool.id(f"z_{r}_{c}_{t}")
        return self._z[k]

    def model_params(self, m: int) -> Tuple[int, int, int]:
        # returns (S_m, P_m, Cost_m)
        if m == 0:
            return 0, 0, 0
        rm = self.inst.rackModels[m - 1]
        return rm.connectors, rm.power_cap, rm.cost

    def build(self):
        # (A1) ExactlyOne model per rack
        for r in self.R:
            add_exactly_one(self.cnf, [self.x(r, m) for m in self.M0], self.vpool)

        # (A2) ExactlyOne rack per card instance
        for (c, t) in self.Q:
            add_exactly_one(self.cnf, [self.z(r, c, t) for r in self.R], self.vpool)

        # weights aligned with self.Q order
        all_weights = [self.inst.cardTypes[c - 1].power for (c, _t) in self.Q]

        # (A3)(A4) gated constraints
        for r in self.R:
            all_lits = [self.z(r, c, t) for (c, t) in self.Q]

            for m in self.M0:
                xr = self.x(r, m)
                S_m, P_m, _ = self.model_params(m)

                # (A3) gated connectors: x -> sum z <= S_m
                con_enc = CardEnc.atmost(all_lits, S_m, encoding=CardEncType.totalizer, vpool=self.vpool)
                for cl in con_enc.clauses:
                    self.cnf.append([-xr] + cl)

                # (A4) gated power PB: x -> sum power*z <= P_m
                add_pb_leq_gated(
                    cnf=self.cnf,
                    lits=all_lits,
                    weights=all_weights,
                    bound=P_m,
                    vpool=self.vpool,
                    gate_lit=-xr,
                )

        # Symmetry A
        # self._add_symmetry_A()

    # def _add_symmetry_A(self):
    #     D = len(self.Q)
    #     T: Dict[Tuple[int, int], int] = {}

    #     for r in self.R:
    #         lits = [self.z(r, c, t) for (c, t) in self.Q]
    #         tot = make_itotalizer(lits, D, self.vpool)

    #         self.cnf.extend(tot.cnf.clauses)
    #         for k in range(1, D + 1):
    #             T[(r, k)] = tot.rhs[k - 1]  # Tot_r >= k
    #         try:
    #             tot.delete()
    #         except Exception:
    #             pass
    #         try:
    #             setattr(tot, "tobj", None)
    #         except Exception:
    #             pass

    #     for r in range(2, self.inst.nbRacks + 1):
    #         for m in self.M0:
    #             x_prev = self.x(r - 1, m)
    #             x_cur = self.x(r, m)
    #             for k in range(1, D + 1):
    #                 self.cnf.append([-x_prev, -x_cur, -T[(r, k)], T[(r - 1, k)]])

    def decode_x(self, model_set: set) -> Dict[int, int]:
        chosen: Dict[int, int] = {}
        for r in self.R:
            for m in self.M0:
                if self.x(r, m) in model_set:
                    chosen[r] = m
                    break
        return chosen

    def decode_counts(self, model_set: set) -> Dict[int, List[int]]:
        # counts[r][c-1] = number of cards type c in rack r
        counts = {r: [0] * self.inst.nbCardTypes for r in self.R}
        for (c, t) in self.Q:
            placed = None
            for r in self.R:
                if self.z(r, c, t) in model_set:
                    placed = r
                    break
            if placed is None:
                raise RuntimeError("Decode error: some card instance not assigned")
            counts[placed][c - 1] += 1
        return counts

    def cost_from_model(self, model_set: set) -> int:
        total = 0
        for r in self.R:
            for m in self.M0:
                if self.x(r, m) in model_set:
                    total += self.model_params(m)[2]
                    break
        return total


# ============================================================
# SAT-bound optimization (tighten from first solution)
# ============================================================

def optimize_sat_bound(modelA: ModelA) -> Optional[Tuple[int, Dict[int, int], Dict[int, List[int]]]]:
    base = modelA.cnf

    # initial feasible
    with Solver(name="g42", bootstrap_with=base.clauses) as s:
        if not s.solve():
            return None
        best = s.get_model()

    best_set = set(l for l in best if l > 0)
    best_cost = modelA.cost_from_model(best_set)

    # cost literals/weights (exclude dummy)
    cost_lits, cost_wts = [], []
    for r in modelA.R:
        for m in modelA.M0:
            cm = modelA.model_params(m)[2]
            if cm > 0:
                cost_lits.append(modelA.x(r, m))
                cost_wts.append(cm)

    # tighten
    B = best_cost - 1
    while B >= 0:
        bound_cnf = CNF()
        add_pb_leq_gated(
            cnf=bound_cnf,
            lits=cost_lits,
            weights=cost_wts,
            bound=B,
            vpool=modelA.vpool,
            gate_lit=None,
        )

        with Solver(name="g42", bootstrap_with=base.clauses + bound_cnf.clauses) as s:
            if s.solve():
                best = s.get_model()
                best_set = set(l for l in best if l > 0)
                best_cost = modelA.cost_from_model(best_set)
                B = best_cost - 1
            else:
                break

    chosen = modelA.decode_x(best_set)
    counts = modelA.decode_counts(best_set)
    return best_cost, chosen, counts


# ============================================================
# Output formatting
# ============================================================

def print_solution(inst: Instance, chosen: Dict[int, int], counts: Dict[int, List[int]], opt_cost: int, title: str):
    print("=" * 90)
    print(title)
    print(f"OPT_COST = {opt_cost}\n")

    header = ["Rack", "RackModel"] + [f"Type{c}" for c in range(1, inst.nbCardTypes + 1)]
    print(" | ".join(f"{h:>8}" for h in header))
    print("-" * (11 * len(header)))

    for r in range(1, inst.nbRacks + 1):
        row = [r, chosen.get(r, -1)] + counts.get(r, [0] * inst.nbCardTypes)
        print(" | ".join(f"{v:>8}" for v in row))
    print()


# ============================================================
# Run instances from instances/ next to this script
# ============================================================

def list_instance_files(inst_dir: str) -> List[str]:
    if not os.path.isdir(inst_dir):
        return []
    files = []
    for fn in os.listdir(inst_dir):
        p = os.path.join(inst_dir, fn)
        if os.path.isfile(p) and fn.lower().endswith(".txt"):
            files.append(p)

    def key(p: str):
        base = os.path.basename(p)
        nums = re.findall(r"\d+", base)
        return (re.sub(r"\d+", "", base).lower(),
                int(nums[0]) if nums else 10**9,
                base.lower())

    files.sort(key=key)
    return files


def run_one(path: str):
    print(f"START {name}", flush=True)

    name = os.path.basename(path)
    try:
        inst = parse_instance_file(path)
        m = ModelA(inst)
        m.build()
        res = optimize_sat_bound(m)
        if res is None:
            print("=" * 90)
            print(f"{name}: UNSAT\n")
            return
        cost, chosen, counts = res
        print_solution(inst, chosen, counts, cost, title=f"Instance: {name}")
    except Exception as e:
        print("=" * 90)
        print(f"{name}: PARSE/ERROR: {e}\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--inst", default=None, help="run single instance file (optional)")
    args = ap.parse_args()

    base_dir = os.path.dirname(os.path.abspath(__file__))
    inst_dir = os.path.join(base_dir, "instances")

    if args.inst:
        path = args.inst
        if not os.path.isabs(path):
            path = os.path.join(base_dir, path)
        if not path.lower().endswith(".txt"):
            path += ".txt"
        run_one(path)
        return

    files = list_instance_files(inst_dir)
    if not files:
        print(f"Không tìm thấy file .txt trong folder: {inst_dir}")
        return

    print(f"Reading instances from: {inst_dir}\n")
    for p in files:
        run_one(p)


if __name__ == "__main__":
    main()
