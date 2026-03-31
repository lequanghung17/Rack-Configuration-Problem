# Pure SAT optimization for RCP with optional PainLess backend.
#
# Two execution modes:
#   1) backend=pysat     -> original fresh-solver-per-bound loop via PySAT
#   2) backend=painless  -> write DIMACS CNF for each bound, call PainLess,
#                           parse SAT/UNSAT + model, then tighten bound = cost-1
#
# This fits the current PureSAT structure well because the model already
# rebuilds the solver on every iteration.

import argparse
import os
import re
import shlex
import subprocess
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from pysat.card import CardEnc, EncType as CardEncType, ITotalizer
from pysat.formula import CNF, IDPool
from pysat.pb import PBEnc, EncType as PBEncType
from pysat.solvers import Solver


def log(msg: str):
    print(f"[{time.strftime('%H:%M:%S')}] {msg}", flush=True)


def default_painless_bin() -> str:
    here = Path(__file__).resolve()
    candidates = [
        here.parent.parent / 'solvers' / 'painless' / 'build' / 'release' / 'painless_release',
        here.parent / 'solvers' / 'painless' / 'build' / 'release' / 'painless_release',
        Path('solvers') / 'painless' / 'build' / 'release' / 'painless_release',
        Path('build') / 'release' / 'painless_release',
    ]
    for p in candidates:
        if p.exists():
            return str(p)
    return str(candidates[0])


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


@dataclass
class ExternalSatResult:
    status: str  # SAT / UNSAT / UNKNOWN
    model: Optional[List[int]]
    returncode: int
    runtime_sec: float
    stdout: str
    stderr: str
    command: List[str]
    winner_type: Optional[str] = None


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

    rm = _parse_angle_tuples(_extract_block(text, "RackModels"))
    ct = _parse_angle_tuples(_extract_block(text, "CardTypes"))

    if len(rm) != nbRackModels:
        raise ValueError(f"RackModels count mismatch: got {len(rm)} expected {nbRackModels}")
    if len(ct) != nbCardTypes:
        raise ValueError(f"CardTypes count mismatch: got {len(ct)} expected {nbCardTypes}")

    rackModels = [RackModel(power_cap=p, connectors=s, cost=c) for (p, s, c) in rm]
    cardTypes = [CardType(power=powc, demand=dem) for (powc, dem) in ct]
    return Instance(nbRackModels, nbCardTypes, nbRacks, rackModels, cardTypes)


def add_exactly_one(cnf: CNF, lits: List[int], vpool: IDPool):
    cnf.append(lits[:])
    if len(lits) <= 4:
        for i in range(len(lits)):
            for j in range(i + 1, len(lits)):
                cnf.append([-lits[i], -lits[j]])
    else:
        amo = CardEnc.atmost(lits=lits, bound=1, encoding=CardEncType.seqcounter, vpool=vpool)
        cnf.extend(amo.clauses)


class IntegratedModelSAT:
    def __init__(self, inst: Instance):
        self.inst = inst
        self.vpool = IDPool()
        self.cnf = CNF()

        self.M = list(range(1, inst.nbRackModels + 1))
        self.R = list(range(1, inst.nbRacks + 1))
        self.C = list(range(1, inst.nbCardTypes + 1))

        self.Q: List[Tuple[int, int]] = []
        for c in self.C:
            d = inst.cardTypes[c - 1].demand
            for t in range(1, d + 1):
                self.Q.append((c, t))

        self.P_list: List[Tuple[int, int]] = [(m, r) for m in self.M for r in self.R]
        self.P_size = len(self.P_list)

        self._rel: Dict[Tuple[int, int, int, int], int] = {}
        self._a: Dict[Tuple[int, int, int, int], int] = {}
        self._w: Dict[Tuple[int, int], int] = {}
        self._pref: Dict[Tuple[int, int, int], int] = {}
        self._L: Dict[Tuple[int, int, int], int] = {}

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
        for (c, t) in self.Q:
            for (m, r) in self.P_list:
                rv = self.rel(m, r, c, t)
                av = self.a(m, r, c, t)
                self.cnf.append([-rv, av])
                self.cnf.append([-av, rv])

    def _add_primal_constraints_and_L(self):
        for (c, t) in self.Q:
            lits = [self.rel(m, r, c, t) for (m, r) in self.P_list]
            add_exactly_one(self.cnf, lits, self.vpool)

        pow_weights = [self.inst.cardTypes[c - 1].power for (c, _t) in self.Q]

        for (m, r) in self.P_list:
            rel_lits = [self.rel(m, r, c, t) for (c, t) in self.Q]
            wm = self.w(m, r)

            for lit in rel_lits:
                self.cnf.append([-lit, wm])
            self.cnf.append([-wm] + rel_lits)

            con = CardEnc.atmost(
                lits=rel_lits,
                bound=self.Sm(m),
                encoding=CardEncType.seqcounter,
                vpool=self.vpool,
            )
            self.cnf.extend(con.clauses)

            pbp = PBEnc.leq(
                lits=rel_lits,
                weights=pow_weights,
                bound=self.Pm(m),
                vpool=self.vpool,
                encoding=PBEncType.best,
            )
            self.cnf.extend(pbp.clauses)

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

        w_lits = [self.w(m, r) for (m, r) in self.P_list]
        card = CardEnc.atmost(
            lits=w_lits,
            bound=self.inst.nbRacks,
            encoding=CardEncType.seqcounter,
            vpool=self.vpool,
        )
        self.cnf.extend(card.clauses)

        for m in self.M:
            for r in range(2, self.inst.nbRacks + 1):
                self.cnf.append([-self.w(m, r), self.w(m, r - 1)])

    def _add_dual_symmetry_SB3_prefix(self):
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


def build_bound_clauses(sat: IntegratedModelSAT, bound: Optional[int]) -> List[List[int]]:
    if bound is None:
        return []
    w_lits, weights = sat.cost_terms()
    pb = PBEnc.leq(lits=w_lits, weights=weights, bound=bound, vpool=sat.vpool, encoding=PBEncType.best)
    return pb.clauses


def make_cnf(base_clauses: List[List[int]], extra_clauses: List[List[int]]) -> CNF:
    cnf = CNF()
    cnf.extend(base_clauses)
    cnf.extend(extra_clauses)
    return cnf


def parse_winner_type(stdout: str, stderr: str) -> Optional[str]:
    text = (stdout or "") + "\n" + (stderr or "")

    patterns = [
        r"WINNER_BACKEND:\s*([A-Za-z0-9_+\-]+)",
        r"backend:\s*([A-Za-z0-9_+\-]+)",
        r"The winner is.*of type:\s*([A-Za-z0-9_+\-]+)",
    ]

    for pat in patterns:
        m = re.search(pat, text, flags=re.IGNORECASE)
        if m:
            return m.group(1)

    return None


def parse_sat_competition_output(stdout: str, stderr: str, returncode: int) -> Tuple[str, Optional[List[int]]]:
    text = (stdout or "") + "\n" + (stderr or "")
    status = "UNKNOWN"

    for line in text.splitlines():
        s = line.strip().upper()
        if s.startswith("S "):
            if "UNSATISFIABLE" in s:
                status = "UNSAT"
                break
            if "SATISFIABLE" in s:
                status = "SAT"
                break

    if status == "UNKNOWN":
        if returncode == 10:
            status = "SAT"
        elif returncode == 20:
            status = "UNSAT"

    model: List[int] = []
    if status == "SAT":
        for line in text.splitlines():
            stripped = line.strip()
            if not stripped:
                continue
            upper = stripped.upper()
            if upper.startswith("V ") or upper == "V" or stripped.startswith("v ") or stripped == "v":
                payload = stripped[1:].strip()
                if payload:
                    for tok in payload.split():
                        if tok == "0":
                            continue
                        try:
                            model.append(int(tok))
                        except ValueError:
                            pass

        if not model:
            int_line = re.compile(r"^[\s\-\d]+0?\s*$")
            for line in text.splitlines():
                if int_line.match(line.strip()):
                    for tok in line.split():
                        if tok == "0":
                            continue
                        try:
                            model.append(int(tok))
                        except ValueError:
                            pass

    return status, (model or None)


def run_painless_once(
    cnf_path: str,
    painless_bin: str,
    cpus: int,
    timeout_sec: int,
    portfolio: str,
    extra_args: str = "",
    launcher_prefix: str = "",
) -> ExternalSatResult:
    cmd: List[str] = []
    if launcher_prefix.strip():
        cmd.extend(shlex.split(launcher_prefix))

    cmd.append(painless_bin)
    cmd.append(f"-c={cpus}")
    if timeout_sec is not None and timeout_sec >= 0:
        cmd.append(f"-t={timeout_sec}")
    if portfolio:
        cmd.append(f"-solver={portfolio}")
    if extra_args.strip():
        cmd.extend(shlex.split(extra_args))
    cmd.append(cnf_path)

    t0 = time.time()
    proc = subprocess.run(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
    )
    runtime_sec = time.time() - t0

    status, model = parse_sat_competition_output(proc.stdout, proc.stderr, proc.returncode)
    winner_type = parse_winner_type(proc.stdout, proc.stderr)

    return ExternalSatResult(
        status=status,
        model=model,
        returncode=proc.returncode,
        runtime_sec=runtime_sec,
        stdout=proc.stdout,
        stderr=proc.stderr,
        command=cmd,
        winner_type=winner_type,
    )


def optimize_puresat_rebuild_solver(
    inst: Instance,
    solver_name: str = "g42",
    start_ub: Optional[int] = None,
) -> Tuple[Optional[List[int]], Optional[int], Dict[str, float]]:
    sat = IntegratedModelSAT(inst)
    sat.build_F1()

    stats: Dict[str, float] = {
        "vars_base": sat.vpool.top,
        "clauses_base": len(sat.cnf.clauses),
        "sat_calls": 0,
        "tighten_steps": 0,
        "rebuilds": 0,
        "external_seconds": 0.0,
    }

    best_model: Optional[List[int]] = None
    best_cost: Optional[int] = None
    bound_clauses = build_bound_clauses(sat, start_ub)
    if start_ub is not None:
        stats["tighten_steps"] += 1

    while True:
        stats["rebuilds"] += 1
        stats["sat_calls"] += 1

        with Solver(name=solver_name, bootstrap_with=(sat.cnf.clauses + bound_clauses)) as s:
            ok = s.solve()
            if not ok:
                break
            model = s.get_model()
            cost = sat.model_cost(model)

        best_model = model
        best_cost = cost

        new_bound = cost - 1
        if new_bound < 0:
            break

        bound_clauses = build_bound_clauses(sat, new_bound)
        stats["tighten_steps"] += 1

    return best_model, best_cost, stats


def optimize_puresat_painless(
    inst: Instance,
    painless_bin: str,
    cpus: int = 8,
    timeout_sec: int = 500,
    portfolio: str = "kc",
    extra_args: str = "",
    launcher_prefix: str = "",
    start_ub: Optional[int] = None,
    keep_cnf_dir: Optional[str] = None,
) -> Tuple[Optional[List[int]], Optional[int], Dict[str, float]]:
    sat = IntegratedModelSAT(inst)
    sat.build_F1()

    stats: Dict[str, float] = {
        "vars_base": sat.vpool.top,
        "clauses_base": len(sat.cnf.clauses),
        "sat_calls": 0,
        "tighten_steps": 0,
        "rebuilds": 0,
        "external_seconds": 0.0,
        "last_returncode": 0,
        "last_status": "",
    }

    best_model: Optional[List[int]] = None
    best_cost: Optional[int] = None
    current_bound: Optional[int] = start_ub
    best_winner_type: Optional[str] = None

    if current_bound is not None:
        stats["tighten_steps"] += 1

    if keep_cnf_dir is not None:
        Path(keep_cnf_dir).mkdir(parents=True, exist_ok=True)
        temp_ctx = None
        workdir = keep_cnf_dir
    else:
        temp_ctx = tempfile.TemporaryDirectory(prefix="puresat_painless_")
        workdir = temp_ctx.name

    try:
        while True:
            stats["rebuilds"] += 1
            stats["sat_calls"] += 1

            bound_clauses = build_bound_clauses(sat, current_bound)
            full_cnf = make_cnf(sat.cnf.clauses, bound_clauses)
            cnf_path = os.path.join(workdir, f"iter_{int(stats['sat_calls']):03d}.cnf")
            full_cnf.to_file(cnf_path)

            log(
                f"PainLess call #{int(stats['sat_calls'])}: bound="
                f"{current_bound if current_bound is not None else 'none'} | "
                f"vars={full_cnf.nv} clauses={len(full_cnf.clauses)}"
            )

            res = run_painless_once(
                cnf_path=cnf_path,
                painless_bin=painless_bin,
                cpus=cpus,
                timeout_sec=timeout_sec,
                portfolio=portfolio,
                extra_args=extra_args,
                launcher_prefix=launcher_prefix,
            )

            stats["external_seconds"] += res.runtime_sec
            stats["last_returncode"] = res.returncode
            stats["last_status"] = res.status

            winner_msg = res.winner_type if res.winner_type else "UNKNOWN_SOLVER"
            log(
                f"PainLess result #{int(stats['sat_calls'])}: status={res.status} "
                f"| winner={winner_msg} | runtime={res.runtime_sec:.2f}s"
            )

            if res.status == "UNSAT":
                stats["best_winner_type"] = best_winner_type if best_winner_type is not None else ""
                break

            if res.status == "UNKNOWN":
                tail_stdout = "\n".join(res.stdout.splitlines()[-20:])
                tail_stderr = "\n".join(res.stderr.splitlines()[-20:])
                raise RuntimeError(
                    "PainLess returned UNKNOWN/unparsed output.\n"
                    f"command: {' '.join(res.command)}\n"
                    f"returncode: {res.returncode}\n"
                    f"winner: {winner_msg}\n"
                    f"stdout tail:\n{tail_stdout}\n"
                    f"stderr tail:\n{tail_stderr}"
                )

            if res.status != "SAT":
                tail_stdout = "\n".join(res.stdout.splitlines()[-20:])
                tail_stderr = "\n".join(res.stderr.splitlines()[-20:])
                raise RuntimeError(
                    "PainLess returned unexpected output.\n"
                    f"command: {' '.join(res.command)}\n"
                    f"returncode: {res.returncode}\n"
                    f"winner: {winner_msg}\n"
                    f"stdout tail:\n{tail_stdout}\n"
                    f"stderr tail:\n{tail_stderr}"
                )

            if not res.model:
                raise RuntimeError(
                    "PainLess reported SAT but no model could be parsed. "
                    "Try removing '--no-model' from your arguments or switching configuration."
                )

            model = res.model
            cost = sat.model_cost(model)
            best_model = model
            best_cost = cost
            best_winner_type = res.winner_type

            log(
                f"New incumbent: cost={best_cost} | "
                f"best_solver_so_far={best_winner_type if best_winner_type else 'UNKNOWN_SOLVER'}"
            )

            new_bound = cost - 1
            if new_bound < 0:
                stats["best_winner_type"] = best_winner_type if best_winner_type is not None else ""
                break
            current_bound = new_bound
            stats["tighten_steps"] += 1

        return best_model, best_cost, stats
    finally:
        if temp_ctx is not None:
            temp_ctx.cleanup()


def print_solution(
    inst: Instance,
    active: Dict[Tuple[int, int], int],
    counts: Dict[Tuple[int, int], List[int]],
    opt_cost: int,
):
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
    ap.add_argument("--backend", choices=["pysat", "painless"], default="painless")
    ap.add_argument("--solver", default="g42", help="PySAT solver name when backend=pysat")
    ap.add_argument("--ub", type=int, default=None, help="optional starting UB for F0 (sum cost*w) <= ub")

    ap.add_argument(
        "--painless-bin",
        default=default_painless_bin(),
        help="Path to PainLess binary. Auto-detects ../solvers/painless/build/release/painless_release when this script lives in src/.",
    )
    ap.add_argument("--painless-cpus", type=int, default=8, help="Number of PainLess solver threads (-c)")
    ap.add_argument("--painless-timeout", type=int, default=500, help="PainLess timeout in seconds (-t)")
    ap.add_argument("--painless-portfolio", default="kc", help="PainLess portfolio string, e.g. kc, IMl")
    ap.add_argument(
        "--painless-extra",
        default="",
        help="Extra raw PainLess arguments, e.g. '-shr-strat=1 -shr-sleep=200000'",
    )
    ap.add_argument(
        "--painless-prefix",
        default="",
        help="Optional launcher prefix, e.g. 'mpirun -np 1'",
    )
    ap.add_argument(
        "--keep-cnf-dir",
        default=None,
        help="Optional directory to keep per-iteration CNF files for debugging",
    )

    args = ap.parse_args()

    inst = parse_instance_file(args.inst)
    total_cards = sum(ct.demand for ct in inst.cardTypes)
    log(
        f"parsed: nbRackModels={inst.nbRackModels}, nbRacks={inst.nbRacks}, "
        f"nbCardTypes={inst.nbCardTypes}, totalCardInstances={total_cards}"
    )

    t0 = time.time()
    if args.backend == "pysat":
        model, opt_cost, stats = optimize_puresat_rebuild_solver(
            inst,
            solver_name=args.solver,
            start_ub=args.ub,
        )
    else:
        if not os.path.exists(args.painless_bin):
            raise FileNotFoundError(
                f"PainLess binary not found: {args.painless_bin}\n"
                "Expected layout for your project: RCP_BENCH/solvers/painless/build/release/painless_release"
            )
        model, opt_cost, stats = optimize_puresat_painless(
            inst,
            painless_bin=args.painless_bin,
            cpus=args.painless_cpus,
            timeout_sec=args.painless_timeout,
            portfolio=args.painless_portfolio,
            extra_args=args.painless_extra,
            launcher_prefix=args.painless_prefix,
            start_ub=args.ub,
            keep_cnf_dir=args.keep_cnf_dir,
        )

    elapsed = time.time() - t0
    log(
        f"done in {elapsed:.2f}s | sat_calls={int(stats['sat_calls'])} rebuilds={int(stats['rebuilds'])} "
        f"tighten_steps={int(stats['tighten_steps'])} | base_vars={int(stats['vars_base'])} "
        f"base_clauses={int(stats['clauses_base'])} | external_seconds={stats['external_seconds']:.2f}"
    )

    if args.backend == "painless":
        best_solver = stats.get("best_winner_type", "")
        if best_solver:
            print(f"\nBEST_PAINLESS_SOLVER = {best_solver}\n")

    if model is None:
        print("\nUNSAT: no feasible solution for F1 (or given UB too small).\n")
        return

    sat = IntegratedModelSAT(inst)
    sat.build_F1()
    active, counts = sat.decode_counts(model)
    print_solution(inst, active, counts, opt_cost=opt_cost)


if __name__ == "__main__":
    main()






# hungle@qHung17-ASUS:~/RCP_bench$ for i in 1 2 3 4 5 6 7 8 9 10 11 12; do echo "===== Running instance$i =====";python src/P
# ureSAT_painless.py   --inst instances/instance$i.txt   --backend painless   --painless-cpus 8   --painless-timeout 3600   --painless-
# portfolio kc   --keep-cnf-dir debug_cnf ; done
# ===== Running instance1 =====
# [00:51:21] parsed: nbRackModels=2, nbRacks=5, nbCardTypes=4, totalCardInstances=17
# [00:51:21] PainLess call #1: bound=none | vars=2578 clauses=5997
# [00:51:21] PainLess call #2: bound=999 | vars=2605 clauses=6046
# [00:51:21] PainLess call #3: bound=799 | vars=2632 clauses=6047
# [00:51:21] PainLess call #4: bound=599 | vars=2657 clauses=6044
# [00:51:21] PainLess call #5: bound=549 | vars=2682 clauses=6044
# [00:51:22] done in 0.45s | sat_calls=5 rebuilds=5 tighten_steps=4 | base_vars=2578 base_clauses=5997 | external_seconds=0.39
# ==============================================================================================================
# OPT_COST = 550
# USED_RACK-USES = 3  (<= nbRacks = 5)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4
# ----------------------------------------------------------------------------------------
#        1 |        1 |        1 |      150 |        1 |        1 |        0 |        1
#        6 |        2 |        1 |      200 |        4 |        3 |        0 |        0
#        7 |        2 |        2 |      200 |        5 |        0 |        2 |        0

# ===== Running instance2 =====
# [00:51:22] parsed: nbRackModels=2, nbRacks=10, nbCardTypes=4, totalCardInstances=34
# [00:51:23] PainLess call #1: bound=none | vars=15356 clauses=36148
# [00:51:23] PainLess call #2: bound=1199 | vars=15451 clauses=36331
# [00:51:24] PainLess call #3: bound=1149 | vars=15546 clauses=36331
# [00:51:24] PainLess call #4: bound=1099 | vars=15641 clauses=36331
# [00:51:26] done in 4.50s | sat_calls=4 rebuilds=4 tighten_steps=3 | base_vars=15356 base_clauses=36148 | external_seconds=2.81
# ==============================================================================================================
# OPT_COST = 1100
# USED_RACK-USES = 7  (<= nbRacks = 10)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4
# ----------------------------------------------------------------------------------------
#        1 |        1 |        1 |      150 |        7 |        0 |        0 |        0
#        2 |        1 |        2 |      150 |        7 |        0 |        0 |        0
#        3 |        1 |        3 |      150 |        5 |        1 |        0 |        0
#        4 |        1 |        4 |      150 |        1 |        2 |        1 |        0
#        5 |        1 |        5 |      150 |        0 |        0 |        0 |        2
#        6 |        1 |        6 |      150 |        0 |        0 |        3 |        0
#       11 |        2 |        1 |      200 |        0 |        5 |        0 |        0

# ===== Running instance3 =====
# [00:51:28] parsed: nbRackModels=2, nbRacks=12, nbCardTypes=6, totalCardInstances=45
# [00:51:32] PainLess call #1: bound=none | vars=29955 clauses=69179
# [00:51:32] PainLess call #2: bound=1499 | vars=30096 clauses=69452
# [00:51:33] PainLess call #3: bound=1349 | vars=30229 clauses=69437
# [00:51:33] PainLess call #4: bound=1199 | vars=30352 clauses=69418
# [01:15:02] done in 1414.44s | sat_calls=4 rebuilds=4 tighten_steps=3 | base_vars=29955 base_clauses=69179 | external_seconds=1409.66
# ==============================================================================================================
# OPT_COST = 1200
# USED_RACK-USES = 8  (<= nbRacks = 12)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5 |    Type6
# --------------------------------------------------------------------------------------------------------------
#        1 |        1 |        1 |      150 |        3 |        1 |        0 |        2 |        0 |        0
#        2 |        1 |        2 |      150 |        6 |        0 |        2 |        0 |        0 |        0
#        3 |        1 |        3 |      150 |        1 |        5 |        1 |        0 |        0 |        0
#        4 |        1 |        4 |      150 |        2 |        0 |        3 |        0 |        0 |        0
#        5 |        1 |        5 |      150 |        0 |        2 |        0 |        2 |        0 |        0
#        6 |        1 |        6 |      150 |        5 |        1 |        2 |        0 |        0 |        0
#        7 |        1 |        7 |      150 |        0 |        0 |        0 |        0 |        2 |        0
#        8 |        1 |        8 |      150 |        3 |        1 |        0 |        0 |        0 |        1

# ===== Running instance4 =====
# [01:15:06] parsed: nbRackModels=6, nbRacks=9, nbCardTypes=6, totalCardInstances=25
# [01:15:06] PainLess call #1: bound=none | vars=21881 clauses=52573
# [01:15:07] PainLess call #2: bound=2699 | vars=23259 clauses=55278
# [01:15:07] PainLess call #3: bound=1199 | vars=23971 clauses=53975
# [01:15:07] PainLess call #4: bound=1149 | vars=24655 clauses=53920
# [01:19:54] done in 288.11s | sat_calls=4 rebuilds=4 tighten_steps=3 | base_vars=21881 base_clauses=52573 | external_seconds=287.51
# ==============================================================================================================
# OPT_COST = 1150
# USED_RACK-USES = 8  (<= nbRacks = 9)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5 |    Type6
# --------------------------------------------------------------------------------------------------------------
#       10 |        2 |        1 |      100 |        0 |        0 |        2 |        0 |        0 |        0
#       11 |        2 |        2 |      100 |        3 |        1 |        0 |        0 |        0 |        0
#       12 |        2 |        3 |      100 |        0 |        0 |        0 |        0 |        1 |        0
#       13 |        2 |        4 |      100 |        2 |        0 |        1 |        0 |        0 |        0
#       14 |        2 |        5 |      100 |        0 |        0 |        0 |        0 |        1 |        0
#       15 |        2 |        6 |      100 |        1 |        2 |        0 |        0 |        0 |        0
#       37 |        5 |        1 |      250 |        1 |        2 |        0 |        0 |        0 |        1
#       46 |        6 |        1 |      300 |        3 |        1 |        1 |        2 |        0 |        0

# ===== Running instance5 =====
# [01:19:55] parsed: nbRackModels=2, nbRacks=5, nbCardTypes=5, totalCardInstances=26
# [01:19:55] PainLess call #1: bound=none | vars=5714 clauses=13116
# [01:19:55] PainLess call #2: bound=999 | vars=5741 clauses=13165
# [01:19:55] PainLess call #3: bound=799 | vars=5768 clauses=13166
# [01:19:55] PainLess call #4: bound=749 | vars=5796 clauses=13168
# [01:19:55] PainLess call #5: bound=699 | vars=5824 clauses=13168
# [01:19:56] done in 0.89s | sat_calls=5 rebuilds=5 tighten_steps=4 | base_vars=5714 base_clauses=13116 | external_seconds=0.68
# ==============================================================================================================
# OPT_COST = 700
# USED_RACK-USES = 4  (<= nbRacks = 5)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5
# ---------------------------------------------------------------------------------------------------
#        1 |        1 |        1 |      150 |        0 |        0 |        0 |        0 |        2
#        2 |        1 |        2 |      150 |        5 |        1 |        0 |        0 |        1
#        6 |        2 |        1 |      200 |        3 |        0 |        4 |        0 |        0
#        7 |        2 |        2 |      200 |        4 |        5 |        0 |        1 |        0

# ===== Running instance6 =====
# [01:19:56] parsed: nbRackModels=2, nbRacks=6, nbCardTypes=6, totalCardInstances=25
# [01:19:56] PainLess call #1: bound=none | vars=6527 clauses=14941
# [01:19:56] PainLess call #2: bound=1199 | vars=6566 clauses=15012
# [01:19:56] PainLess call #3: bound=999 | vars=6605 clauses=15013
# [01:19:56] PainLess call #4: bound=899 | vars=6645 clauses=15016
# [01:19:56] PainLess call #5: bound=749 | vars=6682 clauses=15011
# [01:19:57] PainLess call #6: bound=699 | vars=6719 clauses=15011
# [01:19:57] PainLess call #7: bound=649 | vars=6756 clauses=15011
# [01:19:57] done in 1.19s | sat_calls=7 rebuilds=7 tighten_steps=6 | base_vars=6527 base_clauses=14941 | external_seconds=0.92
# ==============================================================================================================
# OPT_COST = 650
# USED_RACK-USES = 4  (<= nbRacks = 6)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5 |    Type6
# --------------------------------------------------------------------------------------------------------------
#        1 |        1 |        1 |      150 |        3 |        1 |        0 |        0 |        0 |        1
#        2 |        1 |        2 |      150 |        0 |        0 |        0 |        0 |        2 |        0
#        3 |        1 |        3 |      150 |        0 |        1 |        2 |        1 |        0 |        0
#        7 |        2 |        1 |      200 |       11 |        2 |        0 |        1 |        0 |        0

# ===== Running instance7 =====
# [01:19:57] parsed: nbRackModels=2, nbRacks=7, nbCardTypes=6, totalCardInstances=35
# [01:20:01] PainLess call #1: bound=none | vars=12719 clauses=29208
# [01:20:01] PainLess call #2: bound=1399 | vars=12772 clauses=29306
# [01:20:01] PainLess call #3: bound=1049 | vars=12826 clauses=29310
# [01:20:01] PainLess call #4: bound=899 | vars=12877 clauses=29305
# [01:20:01] PainLess call #5: bound=849 | vars=12928 clauses=29305
# [01:20:06] done in 8.55s | sat_calls=5 rebuilds=5 tighten_steps=4 | base_vars=12719 base_clauses=29208 | external_seconds=4.90
# ==============================================================================================================
# OPT_COST = 850
# USED_RACK-USES = 5  (<= nbRacks = 7)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5 |    Type6
# --------------------------------------------------------------------------------------------------------------
#        1 |        1 |        1 |      150 |        1 |        7 |        0 |        0 |        0 |        0
#        2 |        1 |        2 |      150 |        4 |        3 |        1 |        0 |        0 |        0
#        3 |        1 |        3 |      150 |        5 |        0 |        0 |        2 |        0 |        0
#        8 |        2 |        1 |      200 |        8 |        0 |        0 |        0 |        0 |        1
#        9 |        2 |        2 |      200 |        0 |        0 |        0 |        1 |        2 |        0

# ===== Running instance8 =====
# [01:20:07] parsed: nbRackModels=4, nbRacks=8, nbCardTypes=6, totalCardInstances=36
# [01:20:10] PainLess call #1: bound=none | vars=24036 clauses=54607
# [01:20:11] PainLess call #2: bound=1599 | vars=24432 clauses=55371
# [01:20:11] PainLess call #3: bound=999 | vars=24737 clauses=55199
# [01:20:11] PainLess call #4: bound=949 | vars=25031 clauses=55178
# [01:20:11] PainLess call #5: bound=899 | vars=25316 clauses=55161
# [01:20:16] done in 9.03s | sat_calls=5 rebuilds=5 tighten_steps=4 | base_vars=24036 base_clauses=54607 | external_seconds=5.74
# ==============================================================================================================
# OPT_COST = 900
# USED_RACK-USES = 7  (<= nbRacks = 8)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5 |    Type6
# --------------------------------------------------------------------------------------------------------------
#        1 |        1 |        1 |       50 |        0 |        2 |        0 |        0 |        0 |        0
#        2 |        1 |        2 |       50 |        1 |        0 |        1 |        0 |        0 |        0
#        9 |        2 |        1 |      100 |        0 |        0 |        0 |        2 |        0 |        0
#       17 |        3 |        1 |      150 |        7 |        0 |        0 |        0 |        1 |        0
#       18 |        3 |        2 |      150 |        5 |        0 |        0 |        0 |        0 |        1
#       25 |        4 |        1 |      200 |       12 |        0 |        2 |        0 |        0 |        0
#       26 |        4 |        2 |      200 |        0 |        0 |        0 |        0 |        0 |        2

# ===== Running instance9 =====
# [01:20:19] parsed: nbRackModels=6, nbRacks=6, nbCardTypes=6, totalCardInstances=19
# [01:20:19] PainLess call #1: bound=none | vars=9791 clauses=23005
# [01:20:20] PainLess call #2: bound=1799 | vars=10368 clauses=24126
# [01:20:20] PainLess call #3: bound=1499 | vars=10874 clauses=23990
# [01:20:20] PainLess call #4: bound=1199 | vars=11296 clauses=23828
# [01:20:20] PainLess call #5: bound=1149 | vars=11701 clauses=23795
# [01:20:20] PainLess call #6: bound=999 | vars=12061 clauses=23708
# [01:20:27] done in 7.62s | sat_calls=6 rebuilds=6 tighten_steps=5 | base_vars=9791 base_clauses=23005 | external_seconds=7.30
# ==============================================================================================================
# OPT_COST = 1000
# USED_RACK-USES = 4  (<= nbRacks = 6)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5 |    Type6
# --------------------------------------------------------------------------------------------------------------
#        7 |        2 |        1 |      100 |        0 |        0 |        0 |        0 |        1 |        0
#       31 |        6 |        1 |      300 |        0 |        0 |        3 |        2 |        0 |        0
#       32 |        6 |        2 |      300 |        4 |        3 |        0 |        0 |        1 |        0
#       33 |        6 |        3 |      300 |        3 |        0 |        0 |        1 |        0 |        1

# ===== Running instance10 =====
# [01:20:27] parsed: nbRackModels=2, nbRacks=14, nbCardTypes=6, totalCardInstances=57
# [01:21:00] PainLess call #1: bound=none | vars=46255 clauses=107154
# [01:21:01] PainLess call #2: bound=2099 | vars=46456 clauses=107543
# [01:21:01] PainLess call #3: bound=1999 | vars=46652 clauses=107533
# [01:21:02] PainLess call #4: bound=1949 | vars=46848 clauses=107534
# [01:21:02] PainLess call #5: bound=1799 | vars=47037 clauses=107521
# [01:21:03] PainLess call #6: bound=1749 | vars=47226 clauses=107521
# [01:21:04] PainLess call #7: bound=1699 | vars=47415 clauses=107521
# [01:21:06] PainLess call #8: bound=1649 | vars=47602 clauses=107518
# Traceback (most recent call last):
#   File "/home/hungle/RCP_bench/src/PureSAT_painless.py", line 743, in <module>
#     main()
#   File "/home/hungle/RCP_bench/src/PureSAT_painless.py", line 713, in main
#     model, opt_cost, stats = optimize_puresat_painless(
#   File "/home/hungle/RCP_bench/src/PureSAT_painless.py", line 603, in optimize_puresat_painless
#     raise RuntimeError(
# RuntimeError: PainLess returned UNKNOWN/unparsed output.
# command: /home/hungle/RCP_bench/solvers/painless/build/release/painless_release -c=8 -t=3600 -solver=kc debug_cnf/iter_008.cnf
# returncode: 0
# stdout tail:
# c| C1           | 6258652           | 2289211494        | 1277           | 7331463           |                   
# c| K2           | 14204886          | 3120275324        | 333423         | 32009597          |                   
# c| C2           | 6068007           | 2138656268        | 332547         | 14111584          |                   
# c| K3           | 14273438          | 3120287860        | 349048         | 33661739          |                   
# c| C3           | 5900958           | 2182646601        | 566834         | 18964769          |                   
# s UNKNOWN
# c[3609.53] Resolution time: 3609.533108 s
# c================================================================================
# cProcess Resource Usage
# c================================================================================
# ccCPU Time (User):                                          30734.597392s (99.83%)
# cCPU Time (System):                                           51.272561s (0.166%)
# cMaximum Resident Set Size:                          1300812 KB (33.75% of total)
# cPage Reclaims (Soft Page Faults):                                        1854132
# cPage Faults (Hard Page Faults):                                                0
# cBlock Input Operations:                                                        0
# cBlock Output Operations:                                                       0
# cVoluntary Context Switches:                                                18360
# cInvoluntary Context Switches:                                              23876
# c================================================================================
# stderr tail:

# ===== Running instance11 =====
# [02:25:17] parsed: nbRackModels=6, nbRacks=12, nbCardTypes=6, totalCardInstances=47
# [02:25:23] PainLess call #1: bound=none | vars=68113 clauses=171765
# [02:25:25] PainLess call #2: bound=3599 | vars=70643 clauses=176756
# [02:25:26] PainLess call #3: bound=3349 | vars=73057 clauses=176529
# [02:25:27] PainLess call #4: bound=3199 | vars=75391 clauses=176372
# [02:25:28] PainLess call #5: bound=2599 | vars=77392 clauses=175718
# [02:25:29] PainLess call #6: bound=2449 | vars=79308 clauses=175551
# [02:25:30] PainLess call #7: bound=2349 | vars=81155 clauses=175415
# [02:25:33] PainLess call #8: bound=2299 | vars=82970 clauses=175352
# [02:25:37] PainLess call #9: bound=2249 | vars=84755 clauses=175293
# Traceback (most recent call last):
#   File "/home/hungle/RCP_bench/src/PureSAT_painless.py", line 743, in <module>
#     main()
#   File "/home/hungle/RCP_bench/src/PureSAT_painless.py", line 713, in main
#     model, opt_cost, stats = optimize_puresat_painless(
#   File "/home/hungle/RCP_bench/src/PureSAT_painless.py", line 603, in optimize_puresat_painless
#     raise RuntimeError(
# RuntimeError: PainLess returned UNKNOWN/unparsed output.
# command: /home/hungle/RCP_bench/solvers/painless/build/release/painless_release -c=8 -t=3600 -solver=kc debug_cnf/iter_009.cnf
# returncode: 0
# stdout tail:
# c| C1           | 6264112           | 1802347306        | 1277           | 7323250           |                   
# c| K2           | 15645920          | 3059911347        | 392463         | 32064290          |                   
# c| C2           | 7125892           | 1965462856        | 403555         | 16884612          |                   
# c| K3           | 15379084          | 3119672773        | 394828         | 34458591          |                   
# c| C3           | 7162018           | 2107265288        | 697952         | 25467765          |                   
# s UNKNOWN
# c[3611.84] Resolution time: 3611.841639 s
# c================================================================================
# cProcess Resource Usage
# c================================================================================
# ccCPU Time (User):                                          30679.224494s (99.83%)
# cCPU Time (System):                                           51.198659s (0.166%)
# cMaximum Resident Set Size:                          1607628 KB (41.71% of total)
# cPage Reclaims (Soft Page Faults):                                        2115899
# cPage Faults (Hard Page Faults):                                                0
# cBlock Input Operations:                                                        0
# cBlock Output Operations:                                                       0
# cVoluntary Context Switches:                                                19655
# cInvoluntary Context Switches:                                              23918
# c================================================================================
# stderr tail:

# ===== Running instance12 =====
# [03:29:36] parsed: nbRackModels=6, nbRacks=13, nbCardTypes=7, totalCardInstances=62
# [03:35:14] PainLess call #1: bound=none | vars=119655 clauses=298739
# [03:35:16] PainLess call #2: bound=3899 | vars=122647 clauses=304648
# [03:35:18] PainLess call #3: bound=2849 | vars=125040 clauses=303471
# [03:35:19] PainLess call #4: bound=2799 | vars=127402 clauses=303410
# [03:35:21] PainLess call #5: bound=2449 | vars=129530 clauses=302949
# [03:35:26] PainLess call #6: bound=2399 | vars=131617 clauses=302868
# Traceback (most recent call last):
#   File "/home/hungle/RCP_bench/src/PureSAT_painless.py", line 743, in <module>
#     main()
#   File "/home/hungle/RCP_bench/src/PureSAT_painless.py", line 713, in main
#     model, opt_cost, stats = optimize_puresat_painless(
#   File "/home/hungle/RCP_bench/src/PureSAT_painless.py", line 603, in optimize_puresat_painless
#     raise RuntimeError(
# RuntimeError: PainLess returned UNKNOWN/unparsed output.
# command: /home/hungle/RCP_bench/solvers/painless/build/release/painless_release -c=8 -t=3600 -solver=kc debug_cnf/iter_006.cnf
# returncode: 0
# stdout tail:
# c| C1           | 4644450           | 1988954801        | 1021           | 5686751           |                   
# c| K2           | 15066982          | 4301347843        | 380658         | 42914268          |                   
# c| C2           | 4880197           | 2238924180        | 208278         | 16940399          |                   
# c| K3           | 14854435          | 4126395072        | 407248         | 43180614          |                   
# c| C3           | 4602397           | 2260841419        | 460951         | 30793096          |                   
# s UNKNOWN
# c[3613.58] Resolution time: 3613.579789 s
# c================================================================================
# cProcess Resource Usage
# c================================================================================
# ccCPU Time (User):                                          31137.451109s (99.81%)
# cCPU Time (System):                                           56.524900s (0.181%)
# cMaximum Resident Set Size:                          1895696 KB (49.19% of total)
# cPage Reclaims (Soft Page Faults):                                        2354862
# cPage Faults (Hard Page Faults):                                                0
# cBlock Input Operations:                                                        0
# cBlock Output Operations:                                                       0
# cVoluntary Context Switches:                                                22095
# cInvoluntary Context Switches:                                              26585
# c================================================================================
# stderr tail:




# hungle@qHung17-ASUS:~/RCP_bench$ source .venv39/bin/activate
# (.venv39) hungle@qHung17-ASUS:~/RCP_bench$ for i in 1 2 3 4 5 6 7 8 9 10 11 12; do echo "===== Running instance$i =====";python src/PureSAT_painless.py   --inst instances/instance$i.txt   --backend painless   --painless-cpus 8   --painless-timeout 3600   --painless-portfolio IMl   --keep-cnf-dir debug_cnf ; done
# ===== Running instance1 =====
# [00:05:32] parsed: nbRackModels=2, nbRacks=5, nbCardTypes=4, totalCardInstances=17
# [00:05:32] PainLess call #1: bound=none | vars=2578 clauses=5997
# [00:05:32] PainLess call #2: bound=599 | vars=2603 clauses=6044
# [00:05:32] PainLess call #3: bound=549 | vars=2628 clauses=6044
# [00:05:32] done in 0.34s | sat_calls=3 rebuilds=3 tighten_steps=2 | base_vars=2578 base_clauses=5997 | external_seconds=0.29
# ==============================================================================================================
# OPT_COST = 550
# USED_RACK-USES = 3  (<= nbRacks = 5)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4
# ----------------------------------------------------------------------------------------
#        1 |        1 |        1 |      150 |        2 |        0 |        2 |        0
#        6 |        2 |        1 |      200 |        8 |        1 |        0 |        0
#        7 |        2 |        2 |      200 |        0 |        3 |        0 |        1

# ===== Running instance2 =====
# [00:05:32] parsed: nbRackModels=2, nbRacks=10, nbCardTypes=4, totalCardInstances=34
# [00:05:34] PainLess call #1: bound=none | vars=15356 clauses=36148
# [00:05:34] PainLess call #2: bound=1199 | vars=15451 clauses=36331
# [00:05:35] PainLess call #3: bound=1149 | vars=15546 clauses=36331
# [00:05:35] PainLess call #4: bound=1099 | vars=15641 clauses=36331
# [00:05:40] done in 7.20s | sat_calls=4 rebuilds=4 tighten_steps=3 | base_vars=15356 base_clauses=36148 | external_seconds=5.32
# ==============================================================================================================
# OPT_COST = 1100
# USED_RACK-USES = 7  (<= nbRacks = 10)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4
# ----------------------------------------------------------------------------------------
#        1 |        1 |        1 |      150 |        1 |        3 |        0 |        0
#        2 |        1 |        2 |      150 |        3 |        2 |        0 |        0
#        3 |        1 |        3 |      150 |        5 |        0 |        1 |        0
#        4 |        1 |        4 |      150 |        3 |        2 |        0 |        0
#        5 |        1 |        5 |      150 |        5 |        0 |        1 |        0
#        6 |        1 |        6 |      150 |        3 |        1 |        1 |        0
#       11 |        2 |        1 |      200 |        0 |        0 |        1 |        2

# ===== Running instance3 =====
# [00:05:42] parsed: nbRackModels=2, nbRacks=12, nbCardTypes=6, totalCardInstances=45
# [00:05:49] PainLess call #1: bound=none | vars=29955 clauses=69179
# [00:05:49] PainLess call #2: bound=1349 | vars=30088 clauses=69437
# [00:05:49] PainLess call #3: bound=1199 | vars=30211 clauses=69418
# [00:27:33] done in 1311.09s | sat_calls=3 rebuilds=3 tighten_steps=2 | base_vars=29955 base_clauses=69179 | external_seconds=1304.00
# ==============================================================================================================
# OPT_COST = 1200
# USED_RACK-USES = 6  (<= nbRacks = 12)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5 |    Type6
# --------------------------------------------------------------------------------------------------------------
#       13 |        2 |        1 |      200 |        0 |        3 |        1 |        0 |        0 |        1
#       14 |        2 |        2 |      200 |        0 |        0 |        5 |        0 |        0 |        0
#       15 |        2 |        3 |      200 |        1 |        0 |        1 |        3 |        0 |        0
#       16 |        2 |        4 |      200 |        5 |        0 |        0 |        0 |        2 |        0
#       17 |        2 |        5 |      200 |        0 |        5 |        1 |        1 |        0 |        0
#       18 |        2 |        6 |      200 |       14 |        2 |        0 |        0 |        0 |        0

# ===== Running instance4 =====
# [00:27:38] parsed: nbRackModels=6, nbRacks=9, nbCardTypes=6, totalCardInstances=25
# [00:27:38] PainLess call #1: bound=none | vars=21881 clauses=52573
# [00:27:38] PainLess call #2: bound=1199 | vars=22593 clauses=53975
# [00:27:39] PainLess call #3: bound=1149 | vars=23277 clauses=53920
# [00:38:26] done in 648.00s | sat_calls=3 rebuilds=3 tighten_steps=2 | base_vars=21881 base_clauses=52573 | external_seconds=647.50
# ==============================================================================================================
# OPT_COST = 1150
# USED_RACK-USES = 6  (<= nbRacks = 9)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5 |    Type6
# --------------------------------------------------------------------------------------------------------------
#       10 |        2 |        1 |      100 |        0 |        0 |        0 |        0 |        1 |        0
#       19 |        3 |        1 |      150 |        0 |        0 |        0 |        0 |        0 |        1
#       20 |        3 |        2 |      150 |        0 |        0 |        3 |        0 |        0 |        0
#       21 |        3 |        3 |      150 |        1 |        2 |        1 |        0 |        0 |        0
#       46 |        6 |        1 |      300 |        2 |        0 |        0 |        2 |        1 |        0
#       47 |        6 |        2 |      300 |        7 |        4 |        0 |        0 |        0 |        0

# ===== Running instance5 =====
# [00:38:26] parsed: nbRackModels=2, nbRacks=5, nbCardTypes=5, totalCardInstances=26
# [00:38:26] PainLess call #1: bound=none | vars=5714 clauses=13116
# [00:38:27] PainLess call #2: bound=749 | vars=5742 clauses=13168
# [00:38:27] PainLess call #3: bound=699 | vars=5770 clauses=13168
# [00:38:27] done in 0.73s | sat_calls=3 rebuilds=3 tighten_steps=2 | base_vars=5714 base_clauses=13116 | external_seconds=0.55
# ==============================================================================================================
# OPT_COST = 700
# USED_RACK-USES = 4  (<= nbRacks = 5)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5
# ---------------------------------------------------------------------------------------------------
#        1 |        1 |        1 |      150 |        4 |        3 |        0 |        1 |        0
#        2 |        1 |        2 |      150 |        0 |        3 |        0 |        0 |        1
#        6 |        2 |        1 |      200 |        8 |        0 |        3 |        0 |        0
#        7 |        2 |        2 |      200 |        0 |        0 |        1 |        0 |        2

# ===== Running instance6 =====
# [00:38:27] parsed: nbRackModels=2, nbRacks=6, nbCardTypes=6, totalCardInstances=25
# [00:38:27] PainLess call #1: bound=none | vars=6527 clauses=14941
# [00:38:28] PainLess call #2: bound=749 | vars=6564 clauses=15011
# [00:38:28] PainLess call #3: bound=649 | vars=6601 clauses=15011
# [00:38:28] done in 0.65s | sat_calls=3 rebuilds=3 tighten_steps=2 | base_vars=6527 base_clauses=14941 | external_seconds=0.47
# ==============================================================================================================
# OPT_COST = 650
# USED_RACK-USES = 4  (<= nbRacks = 6)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5 |    Type6
# --------------------------------------------------------------------------------------------------------------
#        1 |        1 |        1 |      150 |        0 |        1 |        2 |        1 |        0 |        0
#        2 |        1 |        2 |      150 |        0 |        0 |        0 |        0 |        2 |        0
#        3 |        1 |        3 |      150 |        1 |        2 |        0 |        0 |        0 |        1
#        7 |        2 |        1 |      200 |       13 |        1 |        0 |        1 |        0 |        0

# ===== Running instance7 =====
# [00:38:28] parsed: nbRackModels=2, nbRacks=7, nbCardTypes=6, totalCardInstances=35
# [00:38:30] PainLess call #1: bound=none | vars=12719 clauses=29208
# [00:38:30] PainLess call #2: bound=1049 | vars=12773 clauses=29310
# [00:38:30] PainLess call #3: bound=999 | vars=12824 clauses=29304
# [00:38:30] PainLess call #4: bound=949 | vars=12875 clauses=29304
# [00:38:31] PainLess call #5: bound=849 | vars=12926 clauses=29305
# [00:38:38] done in 9.66s | sat_calls=5 rebuilds=5 tighten_steps=4 | base_vars=12719 base_clauses=29208 | external_seconds=7.94
# ==============================================================================================================
# OPT_COST = 850
# USED_RACK-USES = 5  (<= nbRacks = 7)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5 |    Type6
# --------------------------------------------------------------------------------------------------------------
#        1 |        1 |        1 |      150 |        5 |        2 |        1 |        0 |        0 |        0
#        2 |        1 |        2 |      150 |        5 |        0 |        0 |        0 |        0 |        1
#        3 |        1 |        3 |      150 |        7 |        0 |        0 |        0 |        1 |        0
#        8 |        2 |        1 |      200 |        1 |        7 |        0 |        1 |        0 |        0
#        9 |        2 |        2 |      200 |        0 |        1 |        0 |        2 |        1 |        0

# ===== Running instance8 =====
# [00:38:40] parsed: nbRackModels=4, nbRacks=8, nbCardTypes=6, totalCardInstances=36
# [00:38:43] PainLess call #1: bound=none | vars=24036 clauses=54607
# [00:38:43] PainLess call #2: bound=899 | vars=24321 clauses=55161
# [00:38:54] done in 14.67s | sat_calls=2 rebuilds=2 tighten_steps=1 | base_vars=24036 base_clauses=54607 | external_seconds=11.41
# ==============================================================================================================
# OPT_COST = 900
# USED_RACK-USES = 8  (<= nbRacks = 8)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5 |    Type6
# --------------------------------------------------------------------------------------------------------------
#        1 |        1 |        1 |       50 |        0 |        0 |        0 |        1 |        0 |        0
#        2 |        1 |        2 |       50 |        0 |        0 |        0 |        1 |        0 |        0
#        9 |        2 |        1 |      100 |        0 |        0 |        0 |        0 |        0 |        1
#       10 |        2 |        2 |      100 |        0 |        0 |        0 |        0 |        0 |        1
#       11 |        2 |        3 |      100 |        0 |        0 |        0 |        0 |        0 |        1
#       12 |        2 |        4 |      100 |        0 |        1 |        0 |        0 |        1 |        0
#       25 |        4 |        1 |      200 |       15 |        0 |        1 |        0 |        0 |        0
#       26 |        4 |        2 |      200 |       10 |        1 |        2 |        0 |        0 |        0

# ===== Running instance9 =====
# [00:38:57] parsed: nbRackModels=6, nbRacks=6, nbCardTypes=6, totalCardInstances=19
# [00:38:58] PainLess call #1: bound=none | vars=9791 clauses=23005
# [00:38:58] PainLess call #2: bound=999 | vars=10151 clauses=23708
# [00:39:17] done in 19.02s | sat_calls=2 rebuilds=2 tighten_steps=1 | base_vars=9791 base_clauses=23005 | external_seconds=18.88
# ==============================================================================================================
# OPT_COST = 1000
# USED_RACK-USES = 6  (<= nbRacks = 6)

#        p |        m |        r |  Cost(m) |    Type1 |    Type2 |    Type3 |    Type4 |    Type5 |    Type6
# --------------------------------------------------------------------------------------------------------------
#        1 |        1 |        1 |       50 |        0 |        0 |        1 |        0 |        0 |        0
#        7 |        2 |        1 |      100 |        0 |        0 |        0 |        0 |        1 |        0
#        8 |        2 |        2 |      100 |        0 |        0 |        0 |        0 |        1 |        0
#       19 |        4 |        1 |      200 |        0 |        0 |        1 |        0 |        0 |        1
#       25 |        5 |        1 |      250 |        6 |        3 |        0 |        0 |        0 |        0
#       31 |        6 |        1 |      300 |        1 |        0 |        1 |        3 |        0 |        0

# ===== Running instance10 =====
# [00:39:17] parsed: nbRackModels=2, nbRacks=14, nbCardTypes=6, totalCardInstances=57
# [00:39:51] PainLess call #1: bound=none | vars=46255 clauses=107154
# [00:39:51] PainLess call #2: bound=1799 | vars=46444 clauses=107521
# [00:39:52] PainLess call #3: bound=1699 | vars=46633 clauses=107521
# [00:39:53] PainLess call #4: bound=1649 | vars=46820 clauses=107518
# Traceback (most recent call last):
#   File "/home/hungle/RCP_bench/src/PureSAT_painless.py", line 743, in <module>
#     main()
#   File "/home/hungle/RCP_bench/src/PureSAT_painless.py", line 713, in main
#     model, opt_cost, stats = optimize_puresat_painless(
#   File "/home/hungle/RCP_bench/src/PureSAT_painless.py", line 603, in optimize_puresat_painless
#     raise RuntimeError(
# RuntimeError: PainLess returned UNKNOWN/unparsed output.
# command: /home/hungle/RCP_bench/solvers/painless/build/release/painless_release -c=8 -t=3600 -solver=IMl debug_cnf/iter_004.cnf
# returncode: 0
# stdout tail:
# c[3600.01] (virtual void KissatINCSolver::printStatistics()) Not implemented yet !!
# c| MC1          | 6030303           | 1336997074        | 9723           | 7720143           |                   
# c| L1           | 3084261           | 2868956984        | 13932          | 4811658           |                   
# c[3600.01] (virtual void KissatINCSolver::printStatistics()) Not implemented yet !!
# c| MC2          | 7911640           | 1578427612        | 18694          | 10663300          |                   
# s UNKNOWN
# c[3600.60] Resolution time: 3600.596092 s
# c================================================================================
# cProcess Resource Usage
# c================================================================================
# ccCPU Time (User):                                          29529.515345s (99.44%)
# cCPU Time (System):                                          165.326310s (0.556%)
# cMaximum Resident Set Size:                          1528656 KB (39.66% of total)
# cPage Reclaims (Soft Page Faults):                                        7370507
# cPage Faults (Hard Page Faults):                                                0
# cBlock Input Operations:                                                        0
# cBlock Output Operations:                                                       0
# cVoluntary Context Switches:                                                 7360
# cInvoluntary Context Switches:                                              30735
# c================================================================================
# stderr tail:

# ===== Running instance11 =====
# [01:41:44] parsed: nbRackModels=6, nbRacks=12, nbCardTypes=6, totalCardInstances=47
# [01:41:50] PainLess call #1: bound=none | vars=68113 clauses=171765
# [01:41:51] PainLess call #2: bound=2799 | vars=70234 clauses=175954
# [01:41:52] PainLess call #3: bound=2649 | vars=72265 clauses=175777
# [01:41:53] PainLess call #4: bound=2449 | vars=74181 clauses=175551
# [01:41:54] PainLess call #5: bound=2399 | vars=76061 clauses=175480
# [01:41:55] PainLess call #6: bound=2349 | vars=77908 clauses=175415
# [01:41:56] PainLess call #7: bound=2299 | vars=79723 clauses=175352
# [01:41:59] PainLess call #8: bound=2249 | vars=81508 clauses=175293
# Traceback (most recent call last):
#   File "/home/hungle/RCP_bench/src/PureSAT_painless.py", line 743, in <module>
#     main()
#   File "/home/hungle/RCP_bench/src/PureSAT_painless.py", line 713, in main
#     model, opt_cost, stats = optimize_puresat_painless(
#   File "/home/hungle/RCP_bench/src/PureSAT_painless.py", line 603, in optimize_puresat_painless
#     raise RuntimeError(
# RuntimeError: PainLess returned UNKNOWN/unparsed output.
# command: /home/hungle/RCP_bench/solvers/painless/build/release/painless_release -c=8 -t=3600 -solver=IMl debug_cnf/iter_008.cnf
# returncode: 0
# stdout tail:
# c[3600.03] (virtual void KissatINCSolver::printStatistics()) Not implemented yet !!
# c| MC1          | 5393315           | 1223575451        | 8381           | 6657779           |                   
# c| L1           | 2976774           | 2736680102        | 12349          | 4237733           |                   
# c[3600.03] (virtual void KissatINCSolver::printStatistics()) Not implemented yet !!
# c| MC2          | 6731428           | 1184562321        | 15273          | 9433903           |                   
# s UNKNOWN
# c[3600.35] Resolution time: 3600.351767 s
# c================================================================================
# cProcess Resource Usage
# c================================================================================
# ccCPU Time (User):                                          29298.920322s (99.12%)
# cCPU Time (System):                                          258.779536s (0.875%)
# cMaximum Resident Set Size:                          1622024 KB (42.09% of total)
# cPage Reclaims (Soft Page Faults):                                       17176080
# cPage Faults (Hard Page Faults):                                                0
# cBlock Input Operations:                                                        0
# cBlock Output Operations:                                                       0
# cVoluntary Context Switches:                                                 7368
# cInvoluntary Context Switches:                                              32380
# c================================================================================
# stderr tail:

# ===== Running instance12 =====
# [02:43:33] parsed: nbRackModels=6, nbRacks=13, nbCardTypes=7, totalCardInstances=62
# [02:49:03] PainLess call #1: bound=none | vars=119655 clauses=298739
# [02:49:05] PainLess call #2: bound=3599 | vars=122492 clauses=304344
# [02:49:06] PainLess call #3: bound=2999 | vars=124980 clauses=303658
# [02:49:08] PainLess call #4: bound=2799 | vars=127342 clauses=303410
# [02:49:11] PainLess call #5: bound=2699 | vars=129636 clauses=303276
# [02:49:13] PainLess call #6: bound=2549 | vars=131829 clauses=303077
# [02:49:15] PainLess call #7: bound=2399 | vars=133916 clauses=302868
# Traceback (most recent call last):
#   File "/home/hungle/RCP_bench/src/PureSAT_painless.py", line 743, in <module>
#     main()
#   File "/home/hungle/RCP_bench/src/PureSAT_painless.py", line 713, in main
#     model, opt_cost, stats = optimize_puresat_painless(
#   File "/home/hungle/RCP_bench/src/PureSAT_painless.py", line 603, in optimize_puresat_painless
#     raise RuntimeError(
# RuntimeError: PainLess returned UNKNOWN/unparsed output.
# command: /home/hungle/RCP_bench/solvers/painless/build/release/painless_release -c=8 -t=3600 -solver=IMl debug_cnf/iter_007.cnf
# returncode: 0
# stdout tail:
# c[3600.01] (virtual void KissatINCSolver::printStatistics()) Not implemented yet !!
# c| MC1          | 3310522           | 1040051019        | 5902           | 4370127           |                   
# c| L1           | 2517251           | 2762192790        | 21435          | 4027474           |                   
# c[3600.01] (virtual void KissatINCSolver::printStatistics()) Not implemented yet !!
# c| MC2          | 4630740           | 1205745494        | 12292          | 7268611           |                   
# s UNKNOWN
# c[3600.13] Resolution time: 3600.127127 s
# c================================================================================
# cProcess Resource Usage
# c================================================================================
# ccCPU Time (User):                                          29444.570168s (98.98%)
# cCPU Time (System):                                          300.754756s (1.011%)
# cMaximum Resident Set Size:                          1698080 KB (44.06% of total)
# cPage Reclaims (Soft Page Faults):                                       20777522
# cPage Faults (Hard Page Faults):                                                0
# cBlock Input Operations:                                                        0
# cBlock Output Operations:                                                       0
# cVoluntary Context Switches:                                                 7617
# cInvoluntary Context Switches:                                              36999
# c================================================================================
# stderr tail:

# (.venv39) hungle@qHung17-ASUS:~/RCP_bench$ 