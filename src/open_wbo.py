import os
import re
import time
import argparse
import tempfile
import subprocess
from dataclasses import dataclass
from typing import List, Tuple, Dict, Optional

from pysat.formula import WCNF, IDPool
from pysat.card import CardEnc, EncType as CardEncType, ITotalizer
from pysat.pb import PBEnc, EncType as PBEncType


# =========================
# Logging
# =========================
def log(msg: str):
    print(f"[{time.strftime('%H:%M:%S')}] {msg}", flush=True)


def win_to_wsl_path(p: str) -> str:
    ap = os.path.abspath(p)
    # C:\Users\PC\... -> /mnt/c/Users/PC/...
    drive = ap[0].lower()
    rest = ap[2:].replace("\\", "/")
    return f"/mnt/{drive}{rest}"


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
    def __init__(self, inst: Instance):
        self.inst = inst
        self.vpool = IDPool()
        self.wcnf = WCNF()

        self.M = list(range(1, inst.nbRackModels + 1))
        self.R = list(range(1, inst.nbRacks + 1))
        self.C = list(range(1, inst.nbCardTypes + 1))
        self._pref: Dict[Tuple[int, int, int], int] = {}

        # Q = card instances
        self.Q: List[Tuple[int, int]] = []
        for c in self.C:
            d = inst.cardTypes[c - 1].demand
            for t in range(1, d + 1):
                self.Q.append((c, t))

        # P = rack-use list
        self.P_list: List[Tuple[int, int]] = [(m, r) for m in self.M for r in self.R]
        self.P_size = len(self.P_list)

        self._rel: Dict[Tuple[int, int, int, int], int] = {}
        self._a: Dict[Tuple[int, int, int, int], int] = {}
        self._w: Dict[Tuple[int, int], int] = {}
        self._L: Dict[Tuple[int, int, int], int] = {}

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
        self._add_dual_symmetry_SB3_prefix()
        self._add_load_nonincreasing_symmetry()
        self._add_cost_soft()

    def _add_channelling(self):
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

        pow_weights = [self.inst.cardTypes[c - 1].power for (c, _t) in self.Q]

        for (m, r) in self.P_list:
            rel_lits = [self.rel(m, r, c, t) for (c, t) in self.Q]
            wm = self.w(m, r)

            # rel -> w
            for lit in rel_lits:
                self.wcnf.append([-lit, wm])

            # w -> OR rel
            self.wcnf.append([-wm] + rel_lits)

            # Conn
            con = CardEnc.atmost(
                lits=rel_lits,
                bound=self.Sm(m),
                encoding=CardEncType.seqcounter,
                vpool=self.vpool,
            )
            for cl in con.clauses:
                self.wcnf.append(cl)

            # Power
            pb = PBEnc.leq(
                lits=rel_lits,
                weights=pow_weights,
                bound=self.Pm(m),
                vpool=self.vpool,
                encoding=PBEncType.best,
            )
            for cl in pb.clauses:
                self.wcnf.append(cl)

            # L bits (ITotalizer)
            ub = min(self.Sm(m), len(rel_lits))
            top = self.vpool.top
            tot = ITotalizer(rel_lits, ubound=ub, top_id=top)

            for cl in tot.cnf.clauses:
                self.wcnf.append(cl)

            for k in range(1, ub + 1):
                self._L[(m, r, k)] = tot.rhs[k - 1]

            new_top = getattr(tot, "top_id", None)
            if new_top is None:
                new_top = max([abs(x) for x in tot.rhs] + [abs(x) for x in rel_lits])
            self.vpool.top = max(self.vpool.top, new_top)

        # Card: sum w <= nbRacks
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

    def _add_dual_symmetry_SB3_prefix(self):
        P = self.P_size
        for c in self.C:
            d = self.inst.cardTypes[c - 1].demand
            if d <= 1:
                continue

            # define pref
            for t in range(1, d + 1):
                (m1, r1) = self.P_list[0]
                a1 = self.a(m1, r1, c, t)
                p1 = self.pref(c, t, 1)
                self.wcnf.append([-a1, p1])
                self.wcnf.append([-p1, a1])

                for j in range(2, P + 1):
                    (mj, rj) = self.P_list[j - 1]
                    aj = self.a(mj, rj, c, t)
                    pj = self.pref(c, t, j)
                    pprev = self.pref(c, t, j - 1)

                    self.wcnf.append([-pprev, pj])
                    self.wcnf.append([-aj, pj])
                    self.wcnf.append([-pj, pprev, aj])

            # SB3 (giữ y như bản bạn đang dùng)
            for t in range(2, d + 1):
                for j in range(1, P + 1):
                    self.wcnf.append([-self.pref(c, t, j), self.pref(c, t - 1, j)])

    def _add_load_nonincreasing_symmetry(self):
        for m in self.M:
            ub = min(self.Sm(m), len(self.Q))
            for r in range(2, self.inst.nbRacks + 1):
                w_prev = self.w(m, r - 1)
                w_cur = self.w(m, r)
                for k in range(1, ub + 1):
                    self.wcnf.append([-w_prev, -w_cur, -self.L(m, r, k), self.L(m, r - 1, k)])

    def _add_cost_soft(self):
        for (m, r) in self.P_list:
            cost = self.Costm(m)
            if cost > 0:
                self.wcnf.append([-self.w(m, r)], weight=cost)

    # =========================
    # SOLVE with Open-WBO (Linux binary via WSL on Windows)
    # =========================
    def solve(self, openwbo_path: str, extra_args: Optional[List[str]] = None) -> Optional[
        Tuple[int, Dict[Tuple[int, int], int], Dict[Tuple[int, int], List[int]]]
    ]:
        """
        Dùng Open-WBO để giải .wcnf.
        Parse:
          - 's ...'
          - 'o <num>' (lấy dòng o cuối)
          - 'v <lits ... 0>' (cần -print-model)
        """
        # Ensure WCNF header fields are correct
        self.wcnf.nv = self.vpool.top
        soft_sum = sum(self.wcnf.wght) if getattr(self.wcnf, "wght", None) is not None else 0
        self.wcnf.topw = soft_sum + 1  # hard weight > sum soft weights

        fd, wcnf_path = tempfile.mkstemp(prefix="rack_", suffix=".wcnf")
        os.close(fd)
        self.wcnf.to_file(wcnf_path)

        # Build command (WSL on Windows)
        if os.name == "nt":
            solver_wsl = win_to_wsl_path(openwbo_path)
            wcnf_wsl = win_to_wsl_path(wcnf_path)

            cmd = ["wsl", "-d", "Ubuntu", "--", solver_wsl]
            if extra_args:
                cmd += extra_args
            # if "-print-model" not in cmd:
            #     cmd += ["-print-model"]
            cmd += [wcnf_wsl]
        else:
            cmd = [openwbo_path]
            if extra_args:
                cmd += extra_args
            # if "-print-model" not in cmd:
            #     cmd += ["-print-model"]
            cmd += [wcnf_path]

        proc = subprocess.run(cmd, capture_output=True, text=True)
        text = (proc.stdout or "") + "\n" + (proc.stderr or "")

        try:
            os.remove(wcnf_path)
        except Exception:
            pass

        status = None
        costs: List[int] = []
        lits: List[int] = []

        for line in text.splitlines():
            line = line.strip()
            if not line:
                continue
            if line.startswith("s "):
                status = line[2:].strip()
            elif line.startswith("o "):
                try:
                    # costs.append(int(line[2:].strip()))
                   
                    m = re.match(r"^o\s*[:=]?\s*(\d+)\s*$", line)
                    if m:
                        costs.append(int(m.group(1)))
                except Exception:
                    pass
            elif line.startswith("v "):
                # Open-WBO prints literals ending with 0
                parts = line[2:].strip().split()
                for p in parts:
                    if p == "0":
                        break
                    try:
                        lits.append(int(p))
                    except Exception:
                        pass

        if status and ("UNSAT" in status.upper()):
            return None
        if not costs:
            print("CMD:", " ".join(cmd))
            print("RET:", proc.returncode)
            print("---- solver output (first 2000 chars) ----")
            print(text[:2000])
            print("------------------------------------------")
            raise RuntimeError(
                "Open-WBO output missing objective line 'o <cost>' (or solver failed). "
                "Try adding verbosity, e.g. --openwbo_args -verbosity=1"
            )

        opt_cost = costs[-1]
        model_set = set(l for l in lits if l > 0)

        # Decode (same logic as your RC2/EvalMaxSAT decode)
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
# Run instances
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


def run_one(path: str, solver_path: str, solver_args: Optional[List[str]] = None):
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

        log(f"  solving Open-WBO: {solver_path} ...")
        t_solve = time.time()
        res = solver.solve(openwbo_path=solver_path, extra_args=solver_args)
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
    ap.add_argument("--openwbo", default=None, help="path to Open-WBO binary (Linux ok; will run via WSL on Windows)")
    ap.add_argument(
        "--openwbo_args",
        nargs=argparse.REMAINDER,
        default=[],
        help="extra args for Open-WBO, e.g. --openwbo_args -verbosity=1"
    )
    args = ap.parse_args()

    base_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    inst_dir = os.path.join(base_dir, "instances")
    script_dir = os.path.dirname(os.path.abspath(__file__))

    # default solver path: src/open-wbo-inc_static if exists
    solver_path = args.openwbo
    if not solver_path:
        cand = os.path.join(script_dir, "open-wbo-inc_static")
        solver_path = cand

    # resolve relative path
    if not os.path.isabs(solver_path):
        cand = os.path.join(base_dir, solver_path)
        if os.path.exists(cand):
            solver_path = cand
        else:
            cand = os.path.join(script_dir, solver_path)
            if os.path.exists(cand):
                solver_path = cand

    if not os.path.exists(solver_path):
        raise FileNotFoundError(f"Open-WBO binary not found: {solver_path}")

    solver_args = args.openwbo_args if args.openwbo_args else None

    if args.inst:
        p = args.inst
        if not os.path.isabs(p):
            p = os.path.join(base_dir, p)
        if not p.lower().endswith(".txt"):
            p += ".txt"
        run_one(p, solver_path=solver_path, solver_args=solver_args)
        return

    files = list_instance_files(inst_dir)
    if not files:
        log(f"Không tìm thấy file .txt trong folder: {inst_dir}")
        return

    log(f"Reading instances from: {inst_dir}")
    log(f"Found {len(files)} files: {', '.join(os.path.basename(x) for x in files)}")

    for i, p in enumerate(files, 1):
        log(f"=== [{i}/{len(files)}] RUN {os.path.basename(p)} ===")
        run_one(p, solver_path=solver_path, solver_args=solver_args)


if __name__ == "__main__":
    main()
