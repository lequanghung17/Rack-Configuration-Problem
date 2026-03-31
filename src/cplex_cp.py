import re
import time
import argparse
import shutil
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from docplex.cp.model import CpoModel


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


def log(msg: str) -> None:
    print(f"[{time.strftime('%H:%M:%S')}] {msg}", flush=True)


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


class IntegratedModelCP:
    """
    Integrated CP model:
      - primal variables: rel, w
      - dual variables: map_pos
      - channeling: map_pos[q] == sum(j * rel_j[q])
      - primal feasibility/capacity constraints on rel, w
      - extra dual SB: ordered map positions among copies of the same card type
      - primal SB: prefix activity and nonincreasing load across consecutive uses
    """

    def __init__(
        self,
        inst: Instance,
        use_map_order: bool = True,
        use_load_order: bool = True,
        model_name: str = "RCP_Integrated_CP",
    ) -> None:
        self.inst = inst
        self.use_map_order = use_map_order
        self.use_load_order = use_load_order
        self.model = CpoModel(name=model_name)

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
        self.P_pos = {mr: j + 1 for j, mr in enumerate(self.P_list)}
        self.pos_to_mr = {j + 1: mr for j, mr in enumerate(self.P_list)}

        self.w: Dict[Tuple[int, int], object] = {}
        self.rel: Dict[Tuple[int, int, int, int], object] = {}
        self.map_pos: Dict[Tuple[int, int], object] = {}
        self.load: Dict[Tuple[int, int], object] = {}

    def Sm(self, m: int) -> int:
        return self.inst.rackModels[m - 1].connectors

    def Pm(self, m: int) -> int:
        return self.inst.rackModels[m - 1].power_cap

    def Costm(self, m: int) -> int:
        return self.inst.rackModels[m - 1].cost

    def build(self) -> CpoModel:
        self._add_variables()
        self._add_primal_constraints()
        self._add_channelling()
        if self.use_map_order:
            self._add_dual_order_symmetry()
        if self.use_load_order:
            self._add_load_nonincreasing_symmetry()
        self._set_objective()
        return self.model

    def _add_variables(self) -> None:
        for (m, r) in self.P_list:
            self.w[(m, r)] = self.model.integer_var(min=0, max=1, name=f"w_{m}_{r}")
            self.load[(m, r)] = self.model.integer_var(
                min=0,
                max=min(self.Sm(m), len(self.Q)),
                name=f"load_{m}_{r}",
            )

        for (m, r) in self.P_list:
            for (c, t) in self.Q:
                self.rel[(m, r, c, t)] = self.model.integer_var(
                    min=0, max=1, name=f"rel_{m}_{r}_{c}_{t}"
                )

        for (c, t) in self.Q:
            self.map_pos[(c, t)] = self.model.integer_var(
                min=1, max=self.P_size, name=f"map_{c}_{t}"
            )

    def _add_primal_constraints(self) -> None:
        for (c, t) in self.Q:
            self.model.add(sum(self.rel[(m, r, c, t)] for (m, r) in self.P_list) == 1)

        self.model.add(sum(self.w[(m, r)] for (m, r) in self.P_list) <= self.inst.nbRacks)

        for (m, r) in self.P_list:
            rels = [self.rel[(m, r, c, t)] for (c, t) in self.Q]
            wm = self.w[(m, r)]
            load_mr = self.load[(m, r)]

            for (c, t) in self.Q:
                self.model.add(self.rel[(m, r, c, t)] <= wm)

            self.model.add(sum(rels) >= wm)
            self.model.add(sum(rels) <= self.Sm(m))
            self.model.add(
                sum(
                    self.inst.cardTypes[c - 1].power * self.rel[(m, r, c, t)]
                    for (c, t) in self.Q
                ) <= self.Pm(m)
            )
            self.model.add(load_mr == sum(rels))

        for m in self.M:
            for r in range(2, self.inst.nbRacks + 1):
                self.model.add(self.w[(m, r)] <= self.w[(m, r - 1)])

    def _add_channelling(self) -> None:
        for (c, t) in self.Q:
            self.model.add(
                self.map_pos[(c, t)] ==
                sum((j + 1) * self.rel[(m, r, c, t)] for j, (m, r) in enumerate(self.P_list))
            )

    def _add_dual_order_symmetry(self) -> None:
        for c in self.C:
            d = self.inst.cardTypes[c - 1].demand
            for t in range(2, d + 1):
                self.model.add(self.map_pos[(c, t - 1)] <= self.map_pos[(c, t)])

    def _add_load_nonincreasing_symmetry(self) -> None:
        for m in self.M:
            for r in range(2, self.inst.nbRacks + 1):
                self.model.add(self.load[(m, r - 1)] >= self.load[(m, r)])

    def _set_objective(self) -> None:
        self.model.add(
            self.model.minimize(
                sum(self.Costm(m) * self.w[(m, r)] for (m, r) in self.P_list)
            )
        )

    def solve(
        self,
        time_limit: Optional[float] = None,
        workers: Optional[int] = None,
        execfile: Optional[str] = None,
        quiet: bool = False,
    ):
        kwargs = {}
        if time_limit is not None:
            kwargs["TimeLimit"] = float(time_limit)
        if workers is not None:
            kwargs["Workers"] = int(workers)
        if quiet:
            kwargs["LogVerbosity"] = "Quiet"
        if execfile is not None:
            kwargs["execfile"] = execfile
        return self.model.solve(**kwargs)

    def decode_solution(self, sol) -> Tuple[Dict[Tuple[int, int], int], Dict[Tuple[int, int], List[int]]]:
        active: Dict[Tuple[int, int], int] = {}
        counts: Dict[Tuple[int, int], List[int]] = {}

        for (m, r) in self.P_list:
            if int(round(sol[self.w[(m, r)]])) == 1:
                active[(m, r)] = 1
                counts[(m, r)] = [0] * self.inst.nbCardTypes

        for (c, t) in self.Q:
            pos = int(round(sol[self.map_pos[(c, t)]]))
            if pos not in self.pos_to_mr:
                raise RuntimeError(
                    f"Decode error: map position {pos} is invalid for card instance ({c},{t})."
                )
            mr = self.pos_to_mr[pos]
            counts.setdefault(mr, [0] * self.inst.nbCardTypes)[c - 1] += 1

        return active, counts

    def objective_from_solution(self, sol) -> int:
        total = 0
        for (m, r) in self.P_list:
            total += self.Costm(m) * int(round(sol[self.w[(m, r)]]))
        return total


def print_solution(
    inst: Instance,
    active: Dict[Tuple[int, int], int],
    counts: Dict[Tuple[int, int], List[int]],
    opt_cost: int,
) -> None:
    print("=" * 110)
    print(f"OPT_COST = {opt_cost}")
    used = len(active)
    print(f"USED_RACK-USES = {used}  (<= nbRacks = {inst.nbRacks})\n")

    header = ["p", "m", "r", "Cost(m)"] + [f"Type{c}" for c in range(1, inst.nbCardTypes + 1)]
    print(" | ".join(f"{h:>8}" for h in header))
    print("-" * (11 * len(header)))

    p_idx = {
        (m, r): i + 1
        for i, (m, r) in enumerate(
            (m, r)
            for m in range(1, inst.nbRackModels + 1)
            for r in range(1, inst.nbRacks + 1)
        )
    }

    for m in range(1, inst.nbRackModels + 1):
        for r in range(1, inst.nbRacks + 1):
            if (m, r) not in active:
                continue
            row = [p_idx[(m, r)], m, r, inst.rackModels[m - 1].cost] + counts.get(
                (m, r), [0] * inst.nbCardTypes
            )
            print(" | ".join(f"{v:>8}" for v in row))
    print()


def find_cpoptimizer(user_execfile: Optional[str]) -> Optional[str]:
    if user_execfile:
        p = Path(user_execfile).expanduser()
        if p.is_file():
            return str(p)
        raise FileNotFoundError(f"--execfile not found: {p}")

    candidates = []
    env_exec = shutil.which("cpoptimizer")
    if env_exec:
        candidates.append(env_exec)

    prefix_exec = Path(sys.prefix) / "bin" / "cpoptimizer"
    candidates.append(str(prefix_exec))

    home_exec = Path.home() / "RCP_bench" / ".venv39" / "bin" / "cpoptimizer"
    candidates.append(str(home_exec))

    for cand in candidates:
        if cand and Path(cand).is_file():
            return cand
    return None


def main() -> None:
    ap = argparse.ArgumentParser(description="Integrated CP Optimizer model for Rack Configuration Problem")
    ap.add_argument("--inst", required=True, help="instance .txt file")
    ap.add_argument("--time-limit", type=float, default=None, help="optional time limit in seconds")
    ap.add_argument("--workers", type=int, default=None, help="optional number of CP Optimizer workers")
    ap.add_argument("--no-map-order", action="store_true", help="disable dual ordering symmetry Map(c,t-1) <= Map(c,t)")
    ap.add_argument("--no-load-order", action="store_true", help="disable nonincreasing load symmetry across consecutive uses")
    ap.add_argument("--execfile", default=None, help="optional explicit path to cpoptimizer executable")
    ap.add_argument("--quiet", action="store_true", help="suppress CP Optimizer log")
    args = ap.parse_args()

    inst = parse_instance_file(args.inst)
    total_cards = sum(ct.demand for ct in inst.cardTypes)
    log(
        f"parsed: nbRackModels={inst.nbRackModels}, nbRacks={inst.nbRacks}, "
        f"nbCardTypes={inst.nbCardTypes}, totalCardInstances={total_cards}"
    )

    builder = IntegratedModelCP(
        inst,
        use_map_order=not args.no_map_order,
        use_load_order=not args.no_load_order,
    )

    t0 = time.time()
    builder.build()
    log(
        f"model built: use_map_order={not args.no_map_order}, "
        f"use_load_order={not args.no_load_order}"
    )

    execfile = find_cpoptimizer(args.execfile)
    if execfile is None:
        raise RuntimeError(
            "Could not find cpoptimizer. Activate the right venv or pass --execfile /path/to/cpoptimizer"
        )

    sol = builder.solve(
        time_limit=args.time_limit,
        workers=args.workers,
        execfile=execfile,
        quiet=args.quiet,
    )
    elapsed = time.time() - t0

    if not sol:
        print("\nNo feasible solution found.\n")
        return

    solve_status = sol.get_solve_status()
    active, counts = builder.decode_solution(sol)
    obj = builder.objective_from_solution(sol)
    log(f"done in {elapsed:.2f}s | solve_status={solve_status} | execfile={execfile}")
    print_solution(inst, active, counts, opt_cost=obj)


if __name__ == "__main__":
    main()