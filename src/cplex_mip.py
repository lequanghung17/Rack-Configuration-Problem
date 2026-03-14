import re
import time
import argparse
from dataclasses import dataclass
from typing import Dict, List, Tuple, Optional

from docplex.mp.model import Model


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


class IntegratedMIPCplex:
    """
    Integrated MIP model in docplex.mp:
      - primal: rel, w
      - dual:   map_pos
      - channel: map_pos[q] = sum(pos * rel[pos, q])
      - primal constraints on rel, w
      - extra dual SB: map ordering among copies of same card type
      - primal SB: prefix w-order and nonincreasing load
    """

    def __init__(
        self,
        inst: Instance,
        use_map_order: bool = True,
        use_load_order: bool = True,
        name: str = "RCP_Integrated_MIP_CPLEX",
    ):
        self.inst = inst
        self.use_map_order = use_map_order
        self.use_load_order = use_load_order
        self.mdl = Model(name=name)

        self.M = list(range(1, inst.nbRackModels + 1))
        self.R = list(range(1, inst.nbRacks + 1))
        self.C = list(range(1, inst.nbCardTypes + 1))

        # Q = {(c,t)}
        self.Q: List[Tuple[int, int]] = []
        for c in self.C:
            d = inst.cardTypes[c - 1].demand
            for t in range(1, d + 1):
                self.Q.append((c, t))

        # P_list = [(m,r)] in lexicographic order, exactly like SAT/CP style
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

    def build(self) -> Model:
        self._add_variables()
        self._add_primal_constraints()
        self._add_channelling()
        if self.use_map_order:
            self._add_dual_order_symmetry()
        if self.use_load_order:
            self._add_load_nonincreasing_symmetry()
        self._set_objective()
        return self.mdl

    def _add_variables(self) -> None:
        for (m, r) in self.P_list:
            self.w[(m, r)] = self.mdl.binary_var(name=f"w_{m}_{r}")
            self.load[(m, r)] = self.mdl.integer_var(
                lb=0, ub=min(self.Sm(m), len(self.Q)), name=f"load_{m}_{r}"
            )

        for (m, r) in self.P_list:
            for (c, t) in self.Q:
                self.rel[(m, r, c, t)] = self.mdl.binary_var(name=f"rel_{m}_{r}_{c}_{t}")

        for (c, t) in self.Q:
            self.map_pos[(c, t)] = self.mdl.integer_var(
                lb=1, ub=self.P_size, name=f"map_{c}_{t}"
            )

    def _add_primal_constraints(self) -> None:
        # Each card instance assigned exactly once
        for (c, t) in self.Q:
            self.mdl.add_constraint(
                self.mdl.sum(self.rel[(m, r, c, t)] for (m, r) in self.P_list) == 1,
                ctname=f"assign_{c}_{t}",
            )

        # At most nbRacks active uses in total
        self.mdl.add_constraint(
            self.mdl.sum(self.w[(m, r)] for (m, r) in self.P_list) <= self.inst.nbRacks,
            ctname="limit_total_active_uses",
        )

        for (m, r) in self.P_list:
            rels = [self.rel[(m, r, c, t)] for (c, t) in self.Q]

            # rel -> w
            for (c, t) in self.Q:
                self.mdl.add_constraint(
                    self.rel[(m, r, c, t)] <= self.w[(m, r)],
                    ctname=f"link_rel_w_{m}_{r}_{c}_{t}",
                )

            # w -> OR(rel), linearized as w <= sum(rel)
            self.mdl.add_constraint(
                self.w[(m, r)] <= self.mdl.sum(rels),
                ctname=f"link_w_rel_{m}_{r}",
            )

            # load[m,r] = number of cards assigned to this use
            self.mdl.add_constraint(
                self.load[(m, r)] == self.mdl.sum(rels),
                ctname=f"load_def_{m}_{r}",
            )

            # connector capacity
            self.mdl.add_constraint(
                self.mdl.sum(rels) <= self.Sm(m),
                ctname=f"slots_{m}_{r}",
            )

            # power capacity
            self.mdl.add_constraint(
                self.mdl.sum(
                    self.inst.cardTypes[c - 1].power * self.rel[(m, r, c, t)]
                    for (c, t) in self.Q
                ) <= self.Pm(m),
                ctname=f"power_{m}_{r}",
            )

        # prefix on uses for each rack model: w(m,r) <= w(m,r-1)
        for m in self.M:
            for r in range(2, self.inst.nbRacks + 1):
                self.mdl.add_constraint(
                    self.w[(m, r)] <= self.w[(m, r - 1)],
                    ctname=f"prefix_w_{m}_{r}",
                )

    def _add_channelling(self) -> None:
        for (c, t) in self.Q:
            self.mdl.add_constraint(
                self.map_pos[(c, t)] ==
                self.mdl.sum((j + 1) * self.rel[(m, r, c, t)]
                             for j, (m, r) in enumerate(self.P_list)),
                ctname=f"channel_{c}_{t}",
            )

    def _add_dual_order_symmetry(self) -> None:
        # Same direction as your CP/SAT-aligned version:
        # Map(c,t-1) <= Map(c,t)
        for c in self.C:
            d = self.inst.cardTypes[c - 1].demand
            for t in range(2, d + 1):
                self.mdl.add_constraint(
                    self.map_pos[(c, t - 1)] <= self.map_pos[(c, t)],
                    ctname=f"map_order_{c}_{t}",
                )

    def _add_load_nonincreasing_symmetry(self) -> None:
        for m in self.M:
            for r in range(2, self.inst.nbRacks + 1):
                self.mdl.add_constraint(
                    self.load[(m, r - 1)] >= self.load[(m, r)],
                    ctname=f"load_order_{m}_{r}",
                )

    def _set_objective(self) -> None:
        self.mdl.minimize(
            self.mdl.sum(self.Costm(m) * self.w[(m, r)] for (m, r) in self.P_list)
        )

    def solve(
        self,
        time_limit: Optional[float] = None,
        threads: Optional[int] = None,
        mip_gap: Optional[float] = None,
        quiet: bool = False,
    ):
        if time_limit is not None:
            self.mdl.parameters.timelimit = float(time_limit)
        if threads is not None:
            self.mdl.parameters.threads = int(threads)
        if mip_gap is not None:
            self.mdl.parameters.mip.tolerances.mipgap = float(mip_gap)

        if quiet:
            return self.mdl.solve(log_output=False)
        return self.mdl.solve(log_output=True)

    def objective_from_solution(self, sol) -> int:
        total = 0
        for (m, r) in self.P_list:
            if sol.get_value(self.w[(m, r)]) > 0.5:
                total += self.Costm(m)
        return int(round(total))

    def decode_solution(
        self, sol
    ) -> Tuple[Dict[Tuple[int, int], int], Dict[Tuple[int, int], List[int]]]:
        active: Dict[Tuple[int, int], int] = {}
        counts: Dict[Tuple[int, int], List[int]] = {}

        for (m, r) in self.P_list:
            if sol.get_value(self.w[(m, r)]) > 0.5:
                active[(m, r)] = 1
                counts[(m, r)] = [0] * self.inst.nbCardTypes

        for (c, t) in self.Q:
            pos = int(round(sol.get_value(self.map_pos[(c, t)])))
            if pos not in self.pos_to_mr:
                raise RuntimeError(f"Invalid map position {pos} for card ({c},{t})")
            mr = self.pos_to_mr[pos]
            counts.setdefault(mr, [0] * self.inst.nbCardTypes)[c - 1] += 1

        return active, counts


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


def main() -> None:
    ap = argparse.ArgumentParser(description="Integrated MIP model for Rack Configuration Problem with CPLEX")
    ap.add_argument("--inst", required=True, help="instance .txt file")
    ap.add_argument("--time-limit", type=float, default=None, help="time limit in seconds")
    ap.add_argument("--threads", type=int, default=None, help="number of CPLEX threads")
    ap.add_argument("--mip-gap", type=float, default=None, help="relative MIP gap")
    ap.add_argument("--no-map-order", action="store_true", help="disable dual ordering symmetry")
    ap.add_argument("--no-load-order", action="store_true", help="disable nonincreasing load symmetry")
    ap.add_argument("--quiet", action="store_true", help="disable CPLEX log")
    args = ap.parse_args()

    inst = parse_instance_file(args.inst)
    total_cards = sum(ct.demand for ct in inst.cardTypes)
    log(
        f"parsed: nbRackModels={inst.nbRackModels}, nbRacks={inst.nbRacks}, "
        f"nbCardTypes={inst.nbCardTypes}, totalCardInstances={total_cards}"
    )

    builder = IntegratedMIPCplex(
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

    sol = builder.solve(
        time_limit=args.time_limit,
        threads=args.threads,
        mip_gap=args.mip_gap,
        quiet=args.quiet,
    )
    elapsed = time.time() - t0

    if sol is None:
        print("\nNo feasible solution found.\n")
        return

    status = sol.solve_details.status
    obj = builder.objective_from_solution(sol)
    active, counts = builder.decode_solution(sol)

    log(f"done in {elapsed:.2f}s | status={status}")
    print_solution(inst, active, counts, opt_cost=obj)


if __name__ == "__main__":
    main()