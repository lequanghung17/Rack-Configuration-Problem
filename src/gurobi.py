import re
import time
import argparse
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

import gurobipy as gp
from gurobipy import GRB


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

    rm = _parse_angle_tuples(_extract_block(text, "RackModels"))  # <P,S,Cost>
    ct = _parse_angle_tuples(_extract_block(text, "CardTypes"))   # <Pow,Demand>

    if len(rm) != nbRackModels:
        raise ValueError(f"RackModels count mismatch: got {len(rm)} expected {nbRackModels}")
    if len(ct) != nbCardTypes:
        raise ValueError(f"CardTypes count mismatch: got {len(ct)} expected {nbCardTypes}")

    rackModels = [RackModel(power_cap=p, connectors=s, cost=c) for (p, s, c) in rm]
    cardTypes = [CardType(power=powc, demand=dem) for (powc, dem) in ct]
    return Instance(nbRackModels, nbCardTypes, nbRacks, rackModels, cardTypes)


class IntegratedModelMIP:
    """
    Integrated MIP model aligned with the user's SAT implementation:
      - primal variables: rel, w
      - dual-side Boolean view: a
      - channeling: rel == a
      - primal constraints only on rel, w
      - extra dual SB3 on a via prefix variables pref
      - load ordering symmetry by nonincreasing load for adjacent uses
    """

    def __init__(
        self,
        inst: Instance,
        use_sb3: bool = True,
        use_load_order: bool = True,
        branch_on_dual: bool = False,
        model_name: str = "RCP_Integrated_Gurobi",
    ) -> None:
        self.inst = inst
        self.use_sb3 = use_sb3
        self.use_load_order = use_load_order
        self.branch_on_dual = branch_on_dual

        self.model = gp.Model(model_name)

        self.M = list(range(1, inst.nbRackModels + 1))
        self.R = list(range(1, inst.nbRacks + 1))
        self.C = list(range(1, inst.nbCardTypes + 1))

        # Q: card instances (c, t)
        self.Q: List[Tuple[int, int]] = []
        for c in self.C:
            d = inst.cardTypes[c - 1].demand
            for t in range(1, d + 1):
                self.Q.append((c, t))

        # Ordered rack-uses, same order as the SAT code.
        self.P_list: List[Tuple[int, int]] = [(m, r) for m in self.M for r in self.R]
        self.P_size = len(self.P_list)
        self.P_pos = {mr: j + 1 for j, mr in enumerate(self.P_list)}

        self.w: Dict[Tuple[int, int], gp.Var] = {}
        self.rel: Dict[Tuple[int, int, int, int], gp.Var] = {}
        self.a: Dict[Tuple[int, int, int, int], gp.Var] = {}
        self.pref: Dict[Tuple[int, int, int], gp.Var] = {}
        self.load: Dict[Tuple[int, int], gp.Var] = {}

    def Sm(self, m: int) -> int:
        return self.inst.rackModels[m - 1].connectors

    def Pm(self, m: int) -> int:
        return self.inst.rackModels[m - 1].power_cap

    def Costm(self, m: int) -> int:
        return self.inst.rackModels[m - 1].cost

    def build(self) -> gp.Model:
        self._add_variables()
        self._add_channelling()
        self._add_primal_constraints()
        if self.use_sb3:
            self._add_dual_symmetry_sb3_prefix()
        if self.use_load_order:
            self._add_load_nonincreasing_symmetry()
        self._set_objective()
        self._set_branch_priorities()
        self.model.update()
        return self.model

    def _add_variables(self) -> None:
        for (m, r) in self.P_list:
            self.w[(m, r)] = self.model.addVar(vtype=GRB.BINARY, name=f"w_{m}_{r}")
            self.load[(m, r)] = self.model.addVar(
                vtype=GRB.INTEGER,
                lb=0,
                ub=min(self.Sm(m), len(self.Q)),
                name=f"load_{m}_{r}",
            )

        for (m, r) in self.P_list:
            for (c, t) in self.Q:
                self.rel[(m, r, c, t)] = self.model.addVar(vtype=GRB.BINARY, name=f"rel_{m}_{r}_{c}_{t}")
                self.a[(m, r, c, t)] = self.model.addVar(vtype=GRB.BINARY, name=f"a_{m}_{r}_{c}_{t}")

        if self.use_sb3:
            for c in self.C:
                d = self.inst.cardTypes[c - 1].demand
                if d <= 1:
                    continue
                for t in range(1, d + 1):
                    for j in range(1, self.P_size + 1):
                        self.pref[(c, t, j)] = self.model.addVar(vtype=GRB.BINARY, name=f"pref_{c}_{t}_{j}")

        self.model.update()

    def _add_channelling(self) -> None:
        for (m, r) in self.P_list:
            for (c, t) in self.Q:
                self.model.addConstr(
                    self.rel[(m, r, c, t)] == self.a[(m, r, c, t)],
                    name=f"channel_{m}_{r}_{c}_{t}",
                )

    def _add_primal_constraints(self) -> None:
        # Each card instance is assigned to exactly one rack-use.
        for (c, t) in self.Q:
            self.model.addConstr(
                gp.quicksum(self.rel[(m, r, c, t)] for (m, r) in self.P_list) == 1,
                name=f"assign_once_{c}_{t}",
            )

        # Rack-use feasibility, linking, load definition.
        for (m, r) in self.P_list:
            rels = [self.rel[(m, r, c, t)] for (c, t) in self.Q]
            wm = self.w[(m, r)]
            load_mr = self.load[(m, r)]

            # rel -> w
            for (c, t) in self.Q:
                self.model.addConstr(
                    self.rel[(m, r, c, t)] <= wm,
                    name=f"rel_implies_w_{m}_{r}_{c}_{t}",
                )

            # w -> OR(rel), linearized as sum(rel) >= w
            self.model.addConstr(gp.quicksum(rels) >= wm, name=f"w_nonempty_{m}_{r}")

            # Connector capacity
            self.model.addConstr(
                gp.quicksum(rels) <= self.Sm(m),
                name=f"connector_cap_{m}_{r}",
            )

            # Power capacity
            self.model.addConstr(
                gp.quicksum(self.inst.cardTypes[c - 1].power * self.rel[(m, r, c, t)] for (c, t) in self.Q)
                <= self.Pm(m),
                name=f"power_cap_{m}_{r}",
            )

            # Load = number of assigned card instances in this rack-use.
            self.model.addConstr(
                load_mr == gp.quicksum(rels),
                name=f"load_def_{m}_{r}",
            )

        # At most nbRacks active rack-uses overall.
        self.model.addConstr(
            gp.quicksum(self.w[(m, r)] for (m, r) in self.P_list) <= self.inst.nbRacks,
            name="cardinality_active_rack_uses",
        )

        # Prefix activity per rack model: w(m,r) -> w(m,r-1)
        for m in self.M:
            for r in range(2, self.inst.nbRacks + 1):
                self.model.addConstr(
                    self.w[(m, r)] <= self.w[(m, r - 1)],
                    name=f"w_prefix_{m}_{r}",
                )

    def _add_dual_symmetry_sb3_prefix(self) -> None:
        # pref(c,t,j) = OR_{i <= j} a_i(c,t), where i follows P_list order.
        for c in self.C:
            d = self.inst.cardTypes[c - 1].demand
            if d <= 1:
                continue

            for t in range(1, d + 1):
                m1, r1 = self.P_list[0]
                self.model.addConstr(
                    self.pref[(c, t, 1)] == self.a[(m1, r1, c, t)],
                    name=f"pref_base_{c}_{t}_1",
                )

                for j in range(2, self.P_size + 1):
                    mj, rj = self.P_list[j - 1]
                    pj = self.pref[(c, t, j)]
                    pprev = self.pref[(c, t, j - 1)]
                    aj = self.a[(mj, rj, c, t)]

                    self.model.addConstr(pj >= pprev, name=f"pref_ge_prev_{c}_{t}_{j}")
                    self.model.addConstr(pj >= aj, name=f"pref_ge_a_{c}_{t}_{j}")
                    self.model.addConstr(pj <= pprev + aj, name=f"pref_le_or_{c}_{t}_{j}")

            # SB3: ordered map positions among copies of the same card type.
            for t in range(2, d + 1):
                for j in range(1, self.P_size + 1):
                    self.model.addConstr(
                        self.pref[(c, t, j)] <= self.pref[(c, t - 1, j)],
                        name=f"sb3_{c}_{t}_{j}",
                    )

    def _add_load_nonincreasing_symmetry(self) -> None:
        # Equivalent MIP form of the SAT load ordering.
        for m in self.M:
            for r in range(2, self.inst.nbRacks + 1):
                self.model.addConstr(
                    self.load[(m, r - 1)] >= self.load[(m, r)],
                    name=f"load_noninc_{m}_{r}",
                )

    def _set_objective(self) -> None:
        self.model.setObjective(
            gp.quicksum(self.Costm(m) * self.w[(m, r)] for (m, r) in self.P_list),
            GRB.MINIMIZE,
        )

    def _set_branch_priorities(self) -> None:
        if not self.branch_on_dual:
            return

        # Encourage branching on dual-side variables first, echoing the paper.
        for var in self.a.values():
            var.BranchPriority = 20
        for var in self.w.values():
            var.BranchPriority = 10
        for var in self.rel.values():
            var.BranchPriority = 1

    def optimize(
        self,
        time_limit: Optional[float] = None,
        mip_gap: Optional[float] = None,
        threads: Optional[int] = None,
        output_flag: int = 1,
        write_lp: Optional[str] = None,
    ) -> gp.Model:
        if time_limit is not None:
            self.model.Params.TimeLimit = float(time_limit)
        if mip_gap is not None:
            self.model.Params.MIPGap = float(mip_gap)
        if threads is not None:
            self.model.Params.Threads = int(threads)
        self.model.Params.OutputFlag = int(output_flag)

        if write_lp:
            self.model.write(write_lp)

        self.model.optimize()
        return self.model

    def decode_counts(self) -> Tuple[Dict[Tuple[int, int], int], Dict[Tuple[int, int], List[int]]]:
        active: Dict[Tuple[int, int], int] = {}
        counts: Dict[Tuple[int, int], List[int]] = {}

        for (m, r) in self.P_list:
            if self.w[(m, r)].X > 0.5:
                active[(m, r)] = 1
                counts[(m, r)] = [0] * self.inst.nbCardTypes

        for (c, t) in self.Q:
            placed: Optional[Tuple[int, int]] = None
            for (m, r) in self.P_list:
                if self.rel[(m, r, c, t)].X > 0.5:
                    placed = (m, r)
                    break
            if placed is None:
                raise RuntimeError(f"Decode error: card instance ({c},{t}) not assigned.")
            counts.setdefault(placed, [0] * self.inst.nbCardTypes)[c - 1] += 1

        return active, counts


def print_solution(
    inst: Instance,
    active: Dict[Tuple[int, int], int],
    counts: Dict[Tuple[int, int], List[int]],
    opt_cost: float,
) -> None:
    print("=" * 110)
    print(f"OPT_COST = {int(round(opt_cost))}")
    used = len(active)
    print(f"USED_RACK-USES = {used}  (<= nbRacks = {inst.nbRacks})\n")

    header = ["p", "m", "r", "Cost(m)"] + [f"Type{c}" for c in range(1, inst.nbCardTypes + 1)]
    print(" | ".join(f"{h:>8}" for h in header))
    print("-" * (11 * len(header)))

    p_idx = {(m, r): i + 1 for i, (m, r) in enumerate((m, r) for m in range(1, inst.nbRackModels + 1) for r in range(1, inst.nbRacks + 1))}

    for m in range(1, inst.nbRackModels + 1):
        for r in range(1, inst.nbRacks + 1):
            if (m, r) not in active:
                continue
            row = [p_idx[(m, r)], m, r, inst.rackModels[m - 1].cost] + counts.get((m, r), [0] * inst.nbCardTypes)
            print(" | ".join(f"{v:>8}" for v in row))
    print()


def main() -> None:
    ap = argparse.ArgumentParser(description="Integrated Gurobi MIP for Rack Configuration Problem")
    ap.add_argument("--inst", required=True, help="instance .txt file")
    ap.add_argument("--time-limit", type=float, default=None, help="optional time limit in seconds")
    ap.add_argument("--mip-gap", type=float, default=None, help="optional relative MIP gap")
    ap.add_argument("--threads", type=int, default=None, help="optional number of Gurobi threads")
    ap.add_argument("--no-sb3", action="store_true", help="disable dual SB3-prefix symmetry breaking")
    ap.add_argument("--no-load-order", action="store_true", help="disable load nonincreasing symmetry breaking")
    ap.add_argument("--branch-on-dual", action="store_true", help="set higher Gurobi BranchPriority on dual variables a")
    ap.add_argument("--write-lp", default=None, help="optional path to export the LP model")
    ap.add_argument("--quiet", action="store_true", help="suppress Gurobi log")
    args = ap.parse_args()

    inst = parse_instance_file(args.inst)
    total_cards = sum(ct.demand for ct in inst.cardTypes)
    log(
        f"parsed: nbRackModels={inst.nbRackModels}, nbRacks={inst.nbRacks}, "
        f"nbCardTypes={inst.nbCardTypes}, totalCardInstances={total_cards}"
    )

    builder = IntegratedModelMIP(
        inst,
        use_sb3=not args.no_sb3,
        use_load_order=not args.no_load_order,
        branch_on_dual=args.branch_on_dual,
    )

    t0 = time.time()
    model = builder.build()
    log(
        f"model built: vars={model.NumVars}, constrs={model.NumConstrs}, "
        f"use_sb3={not args.no_sb3}, use_load_order={not args.no_load_order}"
    )

    builder.optimize(
        time_limit=args.time_limit,
        mip_gap=args.mip_gap,
        threads=args.threads,
        output_flag=0 if args.quiet else 1,
        write_lp=args.write_lp,
    )
    elapsed = time.time() - t0

    status = model.Status
    if status in (GRB.OPTIMAL, GRB.SUBOPTIMAL, GRB.TIME_LIMIT, GRB.INTERRUPTED):
        if model.SolCount == 0:
            print("\nNo feasible solution found.\n")
            return

        active, counts = builder.decode_counts()
        log(
            f"done in {elapsed:.2f}s | status={status} | solcount={model.SolCount} | "
            f"best_obj={model.ObjVal:.6f} | best_bound={model.ObjBound:.6f}"
        )
        print_solution(inst, active, counts, opt_cost=model.ObjVal)
        return

    if status == GRB.INFEASIBLE:
        print("\nINFEASIBLE.\n")
        return

    print(f"\nFinished with Gurobi status code {status}.\n")


if __name__ == "__main__":
    main()
