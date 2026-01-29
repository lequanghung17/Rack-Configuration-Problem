# modelA_maxsat.py
import os
import re
import argparse
from dataclasses import dataclass
from typing import List, Tuple, Dict

from pysat.formula import WCNF, IDPool
from pysat.card import CardEnc, EncType as CardEncType
from pysat.pb import PBEnc, EncType as PBEncType
from pysat.examples.rc2 import RC2

import time

def log(msg: str):
    print(f"[{time.strftime('%H:%M:%S')}] {msg}", flush=True)



# =========================
# Data classes
# =========================

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


# =========================
# Robust read + parse
# =========================

def read_text_auto(path: str) -> str:
    raw = open(path, "rb").read()
    if raw.startswith(b"\xff\xfe") or raw.startswith(b"\xfe\xff"):
        txt = raw.decode("utf-16", errors="ignore")
    elif raw.startswith(b"\xef\xbb\xbf"):
        txt = raw.decode("utf-8-sig", errors="ignore")
    else:
        nul = raw.count(b"\x00")
        if len(raw) and nul / len(raw) > 0.05:
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

def _parse_angle_tuples(block: str):
    res = []
    for mm in re.finditer(r"<\s*([^>]+?)\s*>", block, flags=re.DOTALL):
        nums = [int(x.strip()) for x in mm.group(1).split(",") if x.strip()]
        res.append(tuple(nums))
    return res

def parse_instance_file(path: str) -> Instance:
    text = normalize_text(read_text_auto(path))
    nbRackModels = _extract_int_field(text, "nbRackModels")
    nbCardTypes  = _extract_int_field(text, "nbCardTypes")
    nbRacks      = _extract_int_field(text, "nbRacks")
    rm = _parse_angle_tuples(_extract_block(text, "RackModels"))
    ct = _parse_angle_tuples(_extract_block(text, "CardTypes"))
    rackModels = [RackModel(power_cap=p, connectors=s, cost=c) for (p, s, c) in rm]
    cardTypes  = [CardType(power=powc, demand=dem) for (powc, dem) in ct]
    return Instance(nbRackModels, nbCardTypes, nbRacks, rackModels, cardTypes)


# =========================
# Encoding helpers
# =========================

def add_exactly_one_hard(wcnf: WCNF, lits: List[int], vpool: IDPool):
    # ALO
    wcnf.append(lits[:])  # hard by default in WCNF.append
    # AMO
    if len(lits) <= 20:
        for i in range(len(lits)):
            for j in range(i + 1, len(lits)):
                wcnf.append([-lits[i], -lits[j]])
    else:
        amo = CardEnc.atmost(lits=lits, bound=1, encoding=CardEncType.seqcounter, vpool=vpool)
        for cl in amo.clauses:
            wcnf.append(cl)

def add_pb_leq_gated_hard(wcnf: WCNF, lits, weights, bound, vpool, gate_lit: int):
    # Encode (gate_lit OR clause) for every clause of PBEnc.leq
    enc = PBEnc.leq(lits=lits, weights=weights, bound=bound, vpool=vpool, encoding=PBEncType.best)
    for cl in enc.clauses:
        wcnf.append([gate_lit] + cl)


# =========================
# Model A + MaxSAT
# =========================

class ModelA_MaxSAT:
    def __init__(self, inst: Instance):
        self.inst = inst
        self.vpool = IDPool()
        self.wcnf = WCNF()

        self.R = list(range(1, inst.nbRacks + 1))
        self.M = list(range(1, inst.nbRackModels + 1))
        self.M0 = [0] + self.M
        self.C = list(range(1, inst.nbCardTypes + 1))

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

    def model_params(self, m: int):
        if m == 0:
            return 0, 0, 0
        rm = self.inst.rackModels[m - 1]
        return rm.connectors, rm.power_cap, rm.cost

    def build_hard(self):
        # (A1) ExactlyOne model per rack
        for r in self.R:
            add_exactly_one_hard(self.wcnf, [self.x(r, m) for m in self.M0], self.vpool)

        # (A2) ExactlyOne rack per card instance
        for (c, t) in self.Q:
            add_exactly_one_hard(self.wcnf, [self.z(r, c, t) for r in self.R], self.vpool)

        all_weights = [self.inst.cardTypes[c - 1].power for (c, _t) in self.Q]

        # (A3)(A4) gated constraints per rack/model
        for r in self.R:
            all_lits = [self.z(r, c, t) for (c, t) in self.Q]

            for m in self.M0:
                xr = self.x(r, m)
                S_m, P_m, _ = self.model_params(m)

                # connectors: (-x OR sum z <= S_m)
                con_enc = CardEnc.atmost(all_lits, S_m, encoding=CardEncType.totalizer, vpool=self.vpool)
                for cl in con_enc.clauses:
                    self.wcnf.append([-xr] + cl)

                # power PB: (-x OR sum w*z <= P_m)
                add_pb_leq_gated_hard(self.wcnf, all_lits, all_weights, P_m, self.vpool, gate_lit=-xr)

    def add_soft_costs(self):
        # soft clauses: (~x(r,m)) with weight = cost(m) for m>0
        for r in self.R:
            for m in self.M:
                cost = self.model_params(m)[2]
                if cost > 0:
                    self.wcnf.append([-self.x(r, m)], weight=cost)

    def solve(self):
        self.build_hard()
        self.add_soft_costs()

        with RC2(self.wcnf, solver='g42') as rc2:
            model = rc2.compute()
            if model is None:
                return None

            model_set = set(l for l in model if l > 0)
            opt_cost = rc2.cost

        chosen = {}
        for r in self.R:
            for m in self.M0:
                if self.x(r, m) in model_set:
                    chosen[r] = m
                    break

        counts = {r: [0] * self.inst.nbCardTypes for r in self.R}
        for (c, t) in self.Q:
            for r in self.R:
                if self.z(r, c, t) in model_set:
                    counts[r][c - 1] += 1
                    break

        return opt_cost, chosen, counts


# =========================
# Run all instances
# =========================

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

def print_solution(inst: Instance, chosen, counts, opt_cost, title: str):
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

def run_one(path: str):
    name = os.path.basename(path)
    t0 = time.time()
    try:
        log(f"START {name}")
        log(f"  reading + parsing...")
        inst = parse_instance_file(path)

        total_cards = sum(ct.demand for ct in inst.cardTypes)
        log(f"  parsed OK: nbRacks={inst.nbRacks}, nbRackModels={inst.nbRackModels}, "
            f"nbCardTypes={inst.nbCardTypes}, totalCardInstances={total_cards}")

        log(f"  building WCNF (hard+soft)...")
        solver = ModelA_MaxSAT(inst)

        t_build0 = time.time()
        solver.build_hard()
        solver.add_soft_costs()
        log(f"  build done in {time.time() - t_build0:.2f}s "
            f"(vars={solver.vpool.top}, hard={len(solver.wcnf.hard)}, soft={len(solver.wcnf.soft)})")

        log(f"  solving with RC2(g42)...")
        t_solve0 = time.time()
        with RC2(solver.wcnf, solver='g42') as rc2:
            model = rc2.compute()
            if model is None:
                log(f"  UNSAT (RC2 returned None)")
                return
            opt_cost = rc2.cost
        log(f"  solved in {time.time() - t_solve0:.2f}s, OPT_COST={opt_cost}")

        model_set = set(l for l in model if l > 0)

        # decode
        chosen = {}
        for r in range(1, inst.nbRacks + 1):
            for m in [0] + list(range(1, inst.nbRackModels + 1)):
                if solver.x(r, m) in model_set:
                    chosen[r] = m
                    break

        counts = {r: [0] * inst.nbCardTypes for r in range(1, inst.nbRacks + 1)}
        for (c, t) in solver.Q:
            for r in range(1, inst.nbRacks + 1):
                if solver.z(r, c, t) in model_set:
                    counts[r][c - 1] += 1
                    break

        print_solution(inst, chosen, counts, opt_cost, title=f"Instance: {name}")
        log(f"DONE {name} total_time={time.time() - t0:.2f}s")

    except Exception as e:
        log(f"ERROR {name}: {e}")

        print(f"{name}: ERROR: {e}\n")

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
    log(f"Found {len(files)} instance files.")

    for i, p in enumerate(files, 1):
        log(f"=== [{i}/{len(files)}] running {os.path.basename(p)} ===")
        run_one(p)


if __name__ == "__main__":
    main()
