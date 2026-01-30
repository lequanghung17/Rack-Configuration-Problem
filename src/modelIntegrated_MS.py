# # integrated_maxsat.py
# import os
# import re
# import time
# import argparse
# from dataclasses import dataclass
# from typing import List, Tuple, Dict, Optional

# from pysat.formula import WCNF, IDPool
# from pysat.card import CardEnc, EncType as CardEncType
# from pysat.pb import PBEnc, EncType as PBEncType
# from pysat.examples.rc2 import RC2


# # =========================
# # Logging
# # =========================
# def log(msg: str):
#     print(f"[{time.strftime('%H:%M:%S')}] {msg}", flush=True)


# # =========================
# # Data classes
# # =========================
# @dataclass
# class RackModel:
#     power_cap: int   # Pm
#     connectors: int  # Sm
#     cost: int        # price(m)


# @dataclass
# class CardType:
#     power: int   # power(c)
#     demand: int  # quantity(c)


# @dataclass
# class Instance:
#     nbRackModels: int
#     nbCardTypes: int
#     nbRacks: int
#     rackModels: List[RackModel]
#     cardTypes: List[CardType]


# # =========================
# # Robust read + parse
# # =========================
# def read_text_auto(path: str) -> str:
#     raw = open(path, "rb").read()

#     if raw.startswith(b"\xff\xfe") or raw.startswith(b"\xfe\xff"):
#         txt = raw.decode("utf-16", errors="ignore")
#     elif raw.startswith(b"\xef\xbb\xbf"):
#         txt = raw.decode("utf-8-sig", errors="ignore")
#     else:
#         nul = raw.count(b"\x00")
#         if len(raw) and nul / len(raw) > 0.05:
#             try:
#                 txt = raw.decode("utf-16le", errors="ignore")
#             except Exception:
#                 txt = raw.decode("utf-16be", errors="ignore")
#         else:
#             txt = raw.decode("utf-8", errors="ignore")

#     return txt.replace("\x00", "")


# def normalize_text(s: str) -> str:
#     s = s.replace("\ufeff", "")
#     s = s.replace("\xa0", " ")
#     s = re.sub(r"[\u200b\u200c\u200d\u2060]", "", s)
#     s = s.replace("\r\n", "\n").replace("\r", "\n")
#     return s


# def _extract_int_field(text: str, name: str) -> int:
#     m = re.search(rf"\b{name}\b\s*=\s*(\d+)\s*;", text, flags=re.IGNORECASE)
#     if not m:
#         raise ValueError(f"Missing {name}.")
#     return int(m.group(1))


# def _extract_block(text: str, name: str) -> str:
#     m = re.search(rf"\b{name}\b\s*=\s*\[(.*?)\]\s*;", text, flags=re.IGNORECASE | re.DOTALL)
#     if not m:
#         raise ValueError(f"Missing {name} block.")
#     return m.group(1)


# def _parse_angle_tuples(block: str) -> List[Tuple[int, ...]]:
#     res: List[Tuple[int, ...]] = []
#     for mm in re.finditer(r"<\s*([^>]+?)\s*>", block, flags=re.DOTALL):
#         nums = [int(x.strip()) for x in mm.group(1).split(",") if x.strip()]
#         res.append(tuple(nums))
#     return res


# def parse_instance_file(path: str) -> Instance:
#     text = normalize_text(read_text_auto(path))

#     nbRackModels = _extract_int_field(text, "nbRackModels")
#     nbCardTypes  = _extract_int_field(text, "nbCardTypes")
#     nbRacks      = _extract_int_field(text, "nbRacks")

#     rm = _parse_angle_tuples(_extract_block(text, "RackModels"))  # <P,S,Cost>
#     ct = _parse_angle_tuples(_extract_block(text, "CardTypes"))   # <Pow,Demand>

#     if len(rm) != nbRackModels:
#         raise ValueError(f"RackModels count mismatch: got {len(rm)} expected {nbRackModels}")
#     if len(ct) != nbCardTypes:
#         raise ValueError(f"CardTypes count mismatch: got {len(ct)} expected {nbCardTypes}")

#     rackModels = [RackModel(power_cap=p, connectors=s, cost=c) for (p, s, c) in rm]
#     cardTypes  = [CardType(power=powc, demand=dem) for (powc, dem) in ct]
#     return Instance(nbRackModels, nbCardTypes, nbRacks, rackModels, cardTypes)


# # =========================
# # WCNF helpers (hard constraints)
# # =========================
# def add_exactly_one_hard(wcnf: WCNF, lits: List[int], vpool: IDPool):
#     # ALO
#     wcnf.append(lits[:])
#     # AMO
#     if len(lits) <= 20:
#         for i in range(len(lits)):
#             for j in range(i + 1, len(lits)):
#                 wcnf.append([-lits[i], -lits[j]])
#     else:
#         amo = CardEnc.atmost(lits=lits, bound=1, encoding=CardEncType.seqcounter, vpool=vpool)
#         for cl in amo.clauses:
#             wcnf.append(cl)


# def add_pb_leq_gated_hard(wcnf: WCNF, lits: List[int], weights: List[int], bound: int,
#                           vpool: IDPool, gate_lit: int):
#     """
#     gate_lit = -x  =>  x -> (sum weights*lits <= bound)
#     Implement by: for each clause cl of PB encoder, add (gate_lit OR cl).
#     """
#     enc = PBEnc.leq(lits=lits, weights=weights, bound=bound, vpool=vpool, encoding=PBEncType.best)
#     for cl in enc.clauses:
#         wcnf.append([gate_lit] + cl)


# # =========================
# # Integrated Model (Primal + Dual + Channelling) + MaxSAT
# # =========================
# class IntegratedModelMaxSAT:
#     """
#     Sets:
#       M = {1..nbRackModels}
#       R = {1..nbRacks}          (used as rack-use index r within each model)
#       P = M x R                 (rack-use)
#       Q = {(c,t): c in C, t=1..demand(c)}  (card instances)

#     Vars:
#       rel[m,r,c,t] in {0,1}   (primal view)
#       a[m,r,c,t]   in {0,1}   (dual view / map one-hot)
#       w[m,r]       in {0,1}   (rack-use active)

#     Integrated:
#       Channelling: rel <-> a  for all (m,r,c,t)

#       Keep "problem" constraints on primal (rel,w):
#         - Demand: ExactlyOne rel over P for each (c,t)
#         - Conn: sum rel <= S_m for each (m,r)
#         - Power: sum power(c)*rel <= P_m for each (m,r)
#         - Link: rel -> w  AND  (optional) w -> OR rel  (to avoid paying empty rack)
#         - Card: sum w <= nbRacks
#         - Cost: minimize sum price(m)*w[m,r] via Weighted MaxSAT (soft)

#       Keep strong symmetry on dual (a):
#         - Prefix on w (per model): w[m,r] -> w[m,r-1]
#         - SB3 ordering on a within each card type c:
#             Map(c,t-1) >= Map(c,t) (on index of P)
#     """
#     def __init__(self, inst: Instance):
#         self.inst = inst
#         self.vpool = IDPool()
#         self.wcnf = WCNF()

#         self.M = list(range(1, inst.nbRackModels + 1))
#         self.R = list(range(1, inst.nbRacks + 1))   # rack-use position within model
#         self.C = list(range(1, inst.nbCardTypes + 1))

#         # Q card instances
#         self.Q: List[Tuple[int, int]] = []
#         for c in self.C:
#             d = inst.cardTypes[c - 1].demand
#             for t in range(1, d + 1):
#                 self.Q.append((c, t))

#         # P rack-use list with a fixed index p=1..|P|
#         # Order: m=1..M, r=1..R
#         self.P_list: List[Tuple[int, int]] = [(m, r) for m in self.M for r in self.R]
#         self.P_index: Dict[Tuple[int, int], int] = {mr: i + 1 for i, mr in enumerate(self.P_list)}
#         self.P_size = len(self.P_list)

#         self._rel: Dict[Tuple[int, int, int, int], int] = {}
#         self._a: Dict[Tuple[int, int, int, int], int] = {}
#         self._w: Dict[Tuple[int, int], int] = {}

#     # --- vars ---
#     def w(self, m: int, r: int) -> int:
#         k = (m, r)
#         if k not in self._w:
#             self._w[k] = self.vpool.id(f"w_{m}_{r}")
#         return self._w[k]

#     def rel(self, m: int, r: int, c: int, t: int) -> int:
#         k = (m, r, c, t)
#         if k not in self._rel:
#             self._rel[k] = self.vpool.id(f"rel_{m}_{r}_{c}_{t}")
#         return self._rel[k]

#     def a(self, m: int, r: int, c: int, t: int) -> int:
#         k = (m, r, c, t)
#         if k not in self._a:
#             self._a[k] = self.vpool.id(f"a_{m}_{r}_{c}_{t}")
#         return self._a[k]

#     # --- model params ---
#     def Sm(self, m: int) -> int:
#         return self.inst.rackModels[m - 1].connectors

#     def Pm(self, m: int) -> int:
#         return self.inst.rackModels[m - 1].power_cap

#     def Costm(self, m: int) -> int:
#         return self.inst.rackModels[m - 1].cost

#     # --- build ---
#     def build(self):
#         self._add_channelling()
#         self._add_primal_constraints()
#         self._add_dual_symmetry()
#         self._add_cost_soft()

#     def _add_channelling(self):
#         # rel <-> a : (¬rel ∨ a) ∧ (¬a ∨ rel)
#         for (c, t) in self.Q:
#             for (m, r) in self.P_list:
#                 relv = self.rel(m, r, c, t)
#                 av = self.a(m, r, c, t)
#                 self.wcnf.append([-relv, av])
#                 self.wcnf.append([-av, relv])

#     def _add_primal_constraints(self):
#         # (P-Demand) ExactlyOne rel over P for each (c,t)
#         for (c, t) in self.Q:
#             lits = [self.rel(m, r, c, t) for (m, r) in self.P_list]
#             add_exactly_one_hard(self.wcnf, lits, self.vpool)

#         # Prepare weights aligned with Q order for power constraints
#         pow_weights = [self.inst.cardTypes[c - 1].power for (c, _t) in self.Q]

#         # For each rack-use (m,r):
#         for (m, r) in self.P_list:
#             rel_lits = [self.rel(m, r, c, t) for (c, t) in self.Q]
#             wm = self.w(m, r)

#             # (P-Link) rel -> w : (¬rel ∨ w)
#             for lit in rel_lits:
#                 self.wcnf.append([-lit, wm])

#             # Optional but recommended: w -> OR rel  (avoid paying empty rack-use)
#             # (¬w ∨ rel1 ∨ rel2 ∨ ...)
#             self.wcnf.append([-wm] + rel_lits)

#             # (P-Conn) sum rel <= S_m
#             con = CardEnc.atmost(lits=rel_lits, bound=self.Sm(m),
#                                  encoding=CardEncType.seqcounter, vpool=self.vpool)
#             for cl in con.clauses:
#                 self.wcnf.append(cl)

#             # (P-Power) PB: sum power(c)*rel <= P_m
#             enc = PBEnc.leq(lits=rel_lits, weights=pow_weights, bound=self.Pm(m),
#                             vpool=self.vpool, encoding=PBEncType.best)
#             for cl in enc.clauses:
#                 self.wcnf.append(cl)

#         # (P-Card) total active rack-use <= nbRacks
#         # Using atmost on all w[m,r]
#         w_lits = [self.w(m, r) for (m, r) in self.P_list]
#         card = CardEnc.atmost(lits=w_lits, bound=self.inst.nbRacks,
#                               encoding=CardEncType.seqcounter, vpool=self.vpool)
#         for cl in card.clauses:
#             self.wcnf.append(cl)

#     def _add_dual_symmetry(self):
#         # Prefix symmetry on w per model: w[m,r] -> w[m,r-1]
#         for m in self.M:
#             for r in range(2, self.inst.nbRacks + 1):
#                 self.wcnf.append([-self.w(m, r), self.w(m, r - 1)])

#         # SB3 ordering on a within each card type c:
#         # Let p=1..|P| index rack-use. Map(c,t) = p via one-hot a_p(c,t).
#         # Constraint: Map(c,t-1) >= Map(c,t)
#         # CNF: for each j:  ¬a_j(c,t) ∨ (a_j(c,t-1) ∨ ... ∨ a_|P|(c,t-1))
#         for c in self.C:
#             d = self.inst.cardTypes[c - 1].demand
#             if d <= 1:
#                 continue
#             for t in range(2, d + 1):
#                 for j in range(1, self.P_size + 1):
#                     (m_j, r_j) = self.P_list[j - 1]
#                     ajt = self.a(m_j, r_j, c, t)
#                     rhs = []
#                     for i in range(j, self.P_size + 1):
#                         (m_i, r_i) = self.P_list[i - 1]
#                         rhs.append(self.a(m_i, r_i, c, t - 1))
#                     self.wcnf.append([-ajt] + rhs)

#     def _add_cost_soft(self):
#         # Weighted MaxSAT: soft clauses (¬w[m,r]) with weight = price(m)
#         for (m, r) in self.P_list:
#             cost = self.Costm(m)
#             if cost > 0:
#                 self.wcnf.append([-self.w(m, r)], weight=cost)

#     # --- solve + decode ---
#     def solve(self) -> Optional[Tuple[int, Dict[Tuple[int, int], int], Dict[Tuple[int, int], List[int]]]]:
#         with RC2(self.wcnf, solver="g42") as rc2:
#             model = rc2.compute()
#             if model is None:
#                 return None
#             opt_cost = rc2.cost

#         model_set = set(l for l in model if l > 0)

#         # active rack-uses and counts
#         active: Dict[Tuple[int, int], int] = {}
#         counts: Dict[Tuple[int, int], List[int]] = {}

#         for (m, r) in self.P_list:
#             wm = self.w(m, r)
#             if wm in model_set:
#                 active[(m, r)] = 1
#                 counts[(m, r)] = [0] * self.inst.nbCardTypes

#         for (c, t) in self.Q:
#             # find which rack-use gets this card instance (use rel view)
#             placed = None
#             for (m, r) in self.P_list:
#                 if self.rel(m, r, c, t) in model_set:
#                     placed = (m, r)
#                     break
#             if placed is None:
#                 raise RuntimeError("Decode error: some card instance not assigned")
#             if placed in counts:
#                 counts[placed][c - 1] += 1
#             else:
#                 # Should not happen because rel->w and w->OR rel, but keep safe
#                 counts.setdefault(placed, [0]*self.inst.nbCardTypes)[c-1] += 1

#         return opt_cost, active, counts


# # =========================
# # Printing
# # =========================
# def print_solution(inst: Instance,
#                    opt_cost: int,
#                    active: Dict[Tuple[int, int], int],
#                    counts: Dict[Tuple[int, int], List[int]],
#                    title: str):
#     print("=" * 100)
#     print(title)
#     print(f"OPT_COST = {opt_cost}")
#     used = len(active)
#     print(f"USED_RACKS (active rack-uses) = {used}  (<= nbRacks = {inst.nbRacks})\n")

#     header = ["p", "m", "r", "Cost(m)"] + [f"Type{c}" for c in range(1, inst.nbCardTypes + 1)]
#     print(" | ".join(f"{h:>8}" for h in header))
#     print("-" * (11 * len(header)))

#     # show active rack-uses in P order (m-major, r-minor)
#     p_list = [(m, r) for m in range(1, inst.nbRackModels + 1) for r in range(1, inst.nbRacks + 1)]
#     p_idx = {mr: i + 1 for i, mr in enumerate(p_list)}

#     for (m, r) in p_list:
#         if (m, r) not in active:
#             continue
#         row = [p_idx[(m, r)], m, r, inst.rackModels[m - 1].cost] + counts.get((m, r), [0]*inst.nbCardTypes)
#         print(" | ".join(f"{v:>8}" for v in row))
#     print()


# # =========================
# # Run all instances in folder
# # =========================
# def list_instance_files(inst_dir: str) -> List[str]:
#     if not os.path.isdir(inst_dir):
#         return []
#     files = []
#     for fn in os.listdir(inst_dir):
#         p = os.path.join(inst_dir, fn)
#         if os.path.isfile(p) and fn.lower().endswith(".txt"):
#             files.append(p)

#     def key(p: str):
#         base = os.path.basename(p)
#         nums = re.findall(r"\d+", base)
#         return (re.sub(r"\d+", "", base).lower(),
#                 int(nums[0]) if nums else 10**9,
#                 base.lower())

#     files.sort(key=key)
#     return files


# def run_one(path: str):
#     name = os.path.basename(path)
#     t0 = time.time()
#     try:
#         log(f"START {name}")
#         inst = parse_instance_file(path)
#         total_cards = sum(ct.demand for ct in inst.cardTypes)
#         log(f"  parsed: nbRackModels={inst.nbRackModels}, nbRacks={inst.nbRacks}, "
#             f"nbCardTypes={inst.nbCardTypes}, totalCardInstances={total_cards}")

#         log("  building WCNF (Integrated)...")
#         t_build = time.time()
#         solver = IntegratedModelMaxSAT(inst)
#         solver.build()
#         log(f"  build done in {time.time() - t_build:.2f}s "
#             f"(vars={solver.vpool.top}, hard={len(solver.wcnf.hard)}, soft={len(solver.wcnf.soft)})")

#         log("  solving RC2(g42)...")
#         t_solve = time.time()
#         res = solver.solve()
#         if res is None:
#             log("  UNSAT")
#             return
#         opt_cost, active, counts = res
#         log(f"  solved in {time.time() - t_solve:.2f}s, OPT_COST={opt_cost}")

#         print_solution(inst, opt_cost, active, counts, title=f"Instance: {name}")
#         log(f"DONE {name} total_time={time.time() - t0:.2f}s")

#     except Exception as e:
#         log(f"ERROR {name}: {e}")


# def main():
#     ap = argparse.ArgumentParser()
#     ap.add_argument("--inst", default=None, help="run a single instance file (optional)")
#     args = ap.parse_args()

#     base_dir = os.path.dirname(os.path.abspath(__file__))
#     inst_dir = os.path.join(base_dir, "instances")

#     if args.inst:
#         p = args.inst
#         if not os.path.isabs(p):
#             p = os.path.join(base_dir, p)
#         if not p.lower().endswith(".txt"):
#             p += ".txt"
#         run_one(p)
#         return

#     files = list_instance_files(inst_dir)
#     if not files:
#         log(f"Không tìm thấy file .txt trong folder: {inst_dir}")
#         return

#     log(f"Reading instances from: {inst_dir}")
#     log(f"Found {len(files)} files: {', '.join(os.path.basename(x) for x in files)}")

#     for i, p in enumerate(files, 1):
#         log(f"=== [{i}/{len(files)}] RUN {os.path.basename(p)} ===")
#         run_one(p)


# if __name__ == "__main__":
#     main()


# integrated_maxsat.py
# modelIntegrated_MS.py
import os
import re
import time
import argparse
from dataclasses import dataclass
from typing import List, Tuple, Dict, Optional

from pysat.formula import WCNF, IDPool
from pysat.card import CardEnc, EncType as CardEncType, ITotalizer
from pysat.pb import PBEnc, EncType as PBEncType
from pysat.examples.rc2 import RC2


# =========================
# Logging
# =========================
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

    # UTF-16 BOM
    if raw.startswith(b"\xff\xfe") or raw.startswith(b"\xfe\xff"):
        txt = raw.decode("utf-16", errors="ignore")
    # UTF-8 BOM
    elif raw.startswith(b"\xef\xbb\xbf"):
        txt = raw.decode("utf-8-sig", errors="ignore")
    else:
        # heuristic: lots of NUL => UTF-16
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
    s = re.sub(r"[\u200b\u200c\u200d\u2060]", "", s)  # zero-width
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

    rm = _parse_angle_tuples(_extract_block(text, "RackModels"))   # <P,S,Cost>
    ct = _parse_angle_tuples(_extract_block(text, "CardTypes"))    # <Pow,Demand>

    if len(rm) != nbRackModels:
        raise ValueError(f"RackModels count mismatch: got {len(rm)} expected {nbRackModels}")
    if len(ct) != nbCardTypes:
        raise ValueError(f"CardTypes count mismatch: got {len(ct)} expected {nbCardTypes}")

    rackModels = [RackModel(power_cap=p, connectors=s, cost=c) for (p, s, c) in rm]
    cardTypes = [CardType(power=powc, demand=dem) for (powc, dem) in ct]
    return Instance(nbRackModels, nbCardTypes, nbRacks, rackModels, cardTypes)


# =========================
# WCNF helpers
# =========================
def add_exactly_one_hard(wcnf: WCNF, lits: List[int], vpool: IDPool):
    # ALO
    wcnf.append(lits[:])

    # AMO
    if len(lits) <= 4:
        for i in range(len(lits)):
            for j in range(i + 1, len(lits)):
                wcnf.append([-lits[i], -lits[j]])
    else:
        amo = CardEnc.atmost(lits=lits, bound=1, encoding=CardEncType.seqcounter, vpool=vpool)
        for cl in amo.clauses:
            wcnf.append(cl)


# =========================
# Integrated (Primal+Dual+Channelling) + Weighted MaxSAT
# =========================
class IntegratedModelMaxSAT:
    """
    Vars:
      rel[m,r,c,t]  (Primal view)
      a[m,r,c,t]    (Dual/Map view)
      w[m,r]        rack-use active
      L[m,r,k]      unary load bit: "load(m,r) >= k" (safe one-way encoding)

    Constraints:
      - (Primal) demand/conn/power/link/card on rel,w
      - (Dual) SB3 ordering on a, prefix on w
      - (Integrated) channelling rel <-> a
      - (Sym) load non-increasing using L-bits (gated by w)
      - (Opt) Weighted MaxSAT: soft clauses (¬w[m,r]) with weight price(m)
    """

    def __init__(self, inst: Instance):
        self.inst = inst
        self.vpool = IDPool()
        self.wcnf = WCNF()

        self.M = list(range(1, inst.nbRackModels + 1))
        self.R = list(range(1, inst.nbRacks + 1))
        self.C = list(range(1, inst.nbCardTypes + 1))
        self._pref: Dict[Tuple[int, int, int], int] = {}  # (c,t,j) -> var


        # Q = card instances
        self.Q: List[Tuple[int, int]] = []
        for c in self.C:
            d = inst.cardTypes[c - 1].demand
            for t in range(1, d + 1):
                self.Q.append((c, t))

        # P = rack-use list (fixed index p=1..|P|)
        self.P_list: List[Tuple[int, int]] = [(m, r) for m in self.M for r in self.R]
        self.P_size = len(self.P_list)

        self._rel: Dict[Tuple[int, int, int, int], int] = {}
        self._a: Dict[Tuple[int, int, int, int], int] = {}
        self._w: Dict[Tuple[int, int], int] = {}
        self._L: Dict[Tuple[int, int, int], int] = {}  # NEW: L_{m,r,k}

    # ----- vars -----
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

    def L(self, m: int, r: int, k: int) -> int:
        return self._L[(m, r, k)]

    # ----- params -----
    def Sm(self, m: int) -> int:
        return self.inst.rackModels[m - 1].connectors

    def Pm(self, m: int) -> int:
        return self.inst.rackModels[m - 1].power_cap

    def Costm(self, m: int) -> int:
        return self.inst.rackModels[m - 1].cost
    
    def pref(self, c: int, t: int, j: int) -> int:
        k = (c, t, j)
        if k not in self._pref:
            self._pref[k] = self.vpool.id(f"pref_{c}_{t}_{j}")
        return self._pref[k]


    # ----- build -----
    def build(self):
        self._add_channelling()
        self._add_primal_constraints_and_L()
        # self._add_dual_symmetry_SB3()
        self._add_dual_symmetry_SB3_prefix()

        self._add_load_nonincreasing_symmetry()
        self._add_cost_soft()

    def _add_channelling(self):
        # rel <-> a:
        # (¬rel ∨ a) ∧ (¬a ∨ rel)
        for (c, t) in self.Q:
            for (m, r) in self.P_list:
                relv = self.rel(m, r, c, t)
                av = self.a(m, r, c, t)
                self.wcnf.append([-relv, av])
                self.wcnf.append([-av, relv])

    def _add_primal_constraints_and_L(self):
        # (P-Demand) ExactlyOne rel over P for each (c,t)
        for (c, t) in self.Q:
            lits = [self.rel(m, r, c, t) for (m, r) in self.P_list]
            add_exactly_one_hard(self.wcnf, lits, self.vpool)

        # power weights aligned with Q
        pow_weights = [self.inst.cardTypes[c - 1].power for (c, _t) in self.Q]

        # per rack-use (m,r)
        for (m, r) in self.P_list:
            rel_lits = [self.rel(m, r, c, t) for (c, t) in self.Q]
            wm = self.w(m, r)

            # (P-Link) rel -> w
            for lit in rel_lits:
                self.wcnf.append([-lit, wm])

            # (Recommended) w -> OR rel (avoid paying empty rack-use)
            self.wcnf.append([-wm] + rel_lits)

            # (P-Conn) sum rel <= S_m
            con = CardEnc.atmost(
                lits=rel_lits,
                bound=self.Sm(m),
                encoding=CardEncType.seqcounter,
                vpool=self.vpool,
            )
            for cl in con.clauses:
                self.wcnf.append(cl)

            # (P-Power) sum power*rel <= P_m
            pb = PBEnc.leq(
                lits=rel_lits,
                weights=pow_weights,
                bound=self.Pm(m),
                vpool=self.vpool,
                encoding=PBEncType.best,
            )
            for cl in pb.clauses:
                self.wcnf.append(cl)

            # ===== L bits WITHOUT tot.rhs (compatible with old PySAT) =====
                        # ===== L bits bằng ITotalizer (chuẩn paper) =====
            # L_{m,r,k} := (load(m,r) >= k) được lấy trực tiếp từ rhs của totalizer
            ub = min(self.Sm(m), len(rel_lits))

            # ITotalizer bản bạn dùng có signature: (lits, ubound, top_id=None)
            top = self.vpool.top
            tot = ITotalizer(rel_lits, ubound=ub, top_id=top)

            # add clauses totalizer
            for cl in tot.cnf.clauses:
                self.wcnf.append(cl)

            # ánh xạ L(m,r,k) = tot.rhs[k-1]
            for k in range(1, ub + 1):
                self._L[(m, r, k)] = tot.rhs[k - 1]

            # đồng bộ vpool.top để tránh trùng id với biến phụ của totalizer
            new_top = getattr(tot, "top_id", None)
            if new_top is None:
                new_top = max([abs(x) for x in tot.rhs] + [abs(x) for x in rel_lits])
            self.vpool.top = max(self.vpool.top, new_top)


        # (P-Card) sum w <= nbRacks  (over all rack-use)
        w_lits = [self.w(m, r) for (m, r) in self.P_list]
        card = CardEnc.atmost(
            lits=w_lits,
            bound=self.inst.nbRacks,
            encoding=CardEncType.seqcounter,
            vpool=self.vpool,
        )
        for cl in card.clauses:
            self.wcnf.append(cl)

        # Prefix symmetry on w per model: w[m,r] -> w[m,r-1]
        for m in self.M:
            for r in range(2, self.inst.nbRacks + 1):
                self.wcnf.append([-self.w(m, r), self.w(m, r - 1)])

    # def _add_dual_symmetry_SB3(self):
    #     # SB3 ordering on a within each card type c:
    #     # Map(c,t-1) >= Map(c,t)
    #     for c in self.C:
    #         d = self.inst.cardTypes[c - 1].demand
    #         if d <= 1:
    #             continue
    #         for t in range(2, d + 1):
    #             for j in range(1, self.P_size + 1):
    #                 (m_j, r_j) = self.P_list[j - 1]
    #                 ajt = self.a(m_j, r_j, c, t)

    #                 rhs = []
    #                 for i in range(j, self.P_size + 1):
    #                     (m_i, r_i) = self.P_list[i - 1]
    #                     rhs.append(self.a(m_i, r_i, c, t - 1))

    #                 self.wcnf.append([-ajt] + rhs)

    def _add_dual_symmetry_SB3_prefix(self):

    # """
    # Prefix variables pref[c,t,j] = OR_{i=1..j} a[i,c,t]
    # Then SB3: pos(c,t-1) <= pos(c,t)  <=>  pref[c,t,j] -> pref[c,t-1,j] for all j
    # """
        


        P = self.P_size  # |P|
    # Build prefix definition for every card instance (c,t)
        for c in self.C:
            d = self.inst.cardTypes[c - 1].demand
            if d <= 1:
                continue

            for t in range(1, d + 1):
            # j = 1: pref = a1
                (m1, r1) = self.P_list[0]
                a1 = self.a(m1, r1, c, t)
                p1 = self.pref(c, t, 1)
            # p1 <-> a1
                self.wcnf.append([-a1, p1])   # a1 -> p1
                self.wcnf.append([-p1, a1])   # p1 -> a1

            # j >= 2: pref[j] <-> pref[j-1] OR a[j]
                for j in range(2, P + 1):
                    (mj, rj) = self.P_list[j - 1]
                    aj = self.a(mj, rj, c, t)
                    pj = self.pref(c, t, j)
                    pprev = self.pref(c, t, j - 1)

                # (pprev -> pj)
                    self.wcnf.append([-pprev, pj])

                # (aj -> pj)
                    self.wcnf.append([-aj, pj])

                # (pj -> pprev OR aj)
                    self.wcnf.append([-pj, pprev, aj])

        # Now SB3: for t=2..d, for all j: pref[t,j] -> pref[t-1,j]
            for t in range(2, d + 1):
                for j in range(1, P + 1):
                    self.wcnf.append([-self.pref(c, t, j), self.pref(c, t - 1, j)])


                    

    def _add_load_nonincreasing_symmetry(self):
        # (w_{m,r-1} ∧ w_{m,r}) => (¬L_{m,r,k} ∨ L_{m,r-1,k})
        # CNF: (¬w_{m,r-1} ∨ ¬w_{m,r} ∨ ¬L_{m,r,k} ∨ L_{m,r-1,k})
        for m in self.M:
            ub = min(self.Sm(m), len(self.Q))

            for r in range(2, self.inst.nbRacks + 1):
                w_prev = self.w(m, r - 1)
                w_cur = self.w(m, r)
                for k in range(1, ub + 1):
                    self.wcnf.append([-w_prev, -w_cur, -self.L(m, r, k), self.L(m, r - 1, k)])

    def _add_cost_soft(self):
        # Weighted MaxSAT: soft clause (¬w[m,r]) with weight price(m)
        for (m, r) in self.P_list:
            cost = self.Costm(m)
            if cost > 0:
                self.wcnf.append([-self.w(m, r)], weight=cost)

    # ----- solve + decode -----
    def solve(self) -> Optional[Tuple[int, Dict[Tuple[int, int], int], Dict[Tuple[int, int], List[int]]]]:
        with RC2(self.wcnf, solver="g42") as rc2:
            model = rc2.compute()
            if model is None:
                return None
            opt_cost = rc2.cost

        model_set = set(l for l in model if l > 0)

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
                raise RuntimeError("Decode error: some card instance not assigned")
            counts.setdefault(placed, [0] * self.inst.nbCardTypes)[c - 1] += 1

        return opt_cost, active, counts


# =========================
# Output formatting
# =========================
def print_solution(inst: Instance,
                   opt_cost: int,
                   active: Dict[Tuple[int, int], int],
                   counts: Dict[Tuple[int, int], List[int]],
                   title: str):
    print("=" * 110)
    print(title)
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


# =========================
# Run instances from ./instances
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


def run_one(path: str):
    name = os.path.basename(path)
    t0 = time.time()
    try:
        log(f"START {name}")
        inst = parse_instance_file(path)
        total_cards = sum(ct.demand for ct in inst.cardTypes)
        log(f"  parsed: nbRackModels={inst.nbRackModels}, nbRacks={inst.nbRacks}, "
            f"nbCardTypes={inst.nbCardTypes}, totalCardInstances={total_cards}")

        log("  building WCNF (Integrated + SB3 + load)...")
        t_build = time.time()
        solver = IntegratedModelMaxSAT(inst)
        solver.build()
        log(f"  build done in {time.time() - t_build:.2f}s "
            f"(vars={solver.vpool.top}, hard={len(solver.wcnf.hard)}, soft={len(solver.wcnf.soft)})")

        log("  solving RC2(g42)...")
        t_solve = time.time()
        res = solver.solve()
        if res is None:
            log("  UNSAT")
            return

        opt_cost, active, counts = res
        log(f"  solved in {time.time() - t_solve:.2f}s, OPT_COST={opt_cost}")

        print_solution(inst, opt_cost, active, counts, title=f"Instance: {name}")
        log(f"DONE {name} total_time={time.time() - t0:.2f}s")

    except Exception as e:
        log(f"ERROR {name}: {e}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--inst", default=None, help="run a single instance file (optional)")
    args = ap.parse_args()

    base_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__))) 
    inst_dir = os.path.join(base_dir, "instances")

    if args.inst:
        p = args.inst
        if not os.path.isabs(p):
            p = os.path.join(base_dir, p)
        if not p.lower().endswith(".txt"):
            p += ".txt"
        run_one(p)
        return

    files = list_instance_files(inst_dir)
    if not files:
        log(f"Không tìm thấy file .txt trong folder: {inst_dir}")
        return

    log(f"Reading instances from: {inst_dir}")
    log(f"Found {len(files)} files: {', '.join(os.path.basename(x) for x in files)}")

    for i, p in enumerate(files, 1):
        log(f"=== [{i}/{len(files)}] RUN {os.path.basename(p)} ===")
        run_one(p)


if __name__ == "__main__":
    main()
