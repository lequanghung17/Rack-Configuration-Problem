# src/Integrated_pycsp.py
# Integrated model (FULL symmetry breaking) for Rack Configuration Problem (CSPLib prob031)
# Based on: "Symmetry Breaking in a Rack Configuration Problem"
#
# Variables:
#   W[m][r]   ∈ {0,1} : r-th use of model m is used
#   Rel[m][r][k] ∈ {0,1} : card instance k is placed in (m,r)
#   Map[k]    ∈ P     : dual mapping of card k to a slot (m,r)
#
# Constraints (primal on Rel/W) + channelling + ALL SB:
#   SB1: Decreasing(W[m]) for each model m
#   SB2: if W[m,r-1]=W[m,r]=1 then |Rel(m,r-1)| >= |Rel(m,r)|
#   SB3: for each type tau: Map[t-1] >= Map[t] across identical cards

from pycsp3 import *
import re
import sys
import time
from typing import List, Tuple


# -------------------------
# Instance parser (your .txt format)
# -------------------------
def parse_instance_txt(path: str) -> Tuple[int, List[List[int]], List[List[int]]]:
    txt = open(path, "r", encoding="utf-8").read()

    def get_int(name: str) -> int:
        m = re.search(rf"{name}\s*=\s*(\d+)\s*;", txt)
        if not m:
            raise ValueError(f"Missing {name} in {path}")
        return int(m.group(1))

    def get_tuples(name: str, arity: int) -> List[List[int]]:
        m = re.search(rf"{name}\s*=\s*\[(.*?)\]\s*;", txt, re.S)
        if not m:
            raise ValueError(f"Missing {name} block in {path}")
        block = m.group(1)
        tuples = re.findall(r"<\s*([0-9,\s]+)\s*>", block)
        out = []
        for t in tuples:
            nums = [int(x.strip()) for x in t.split(",")]
            if len(nums) != arity:
                raise ValueError(
                    f"{name} tuple arity mismatch: got {len(nums)} expected {arity} in {path}"
                )
            out.append(nums)
        return out

    nbRacks = get_int("nbRacks")
    rackModels = get_tuples("RackModels", 3)  # <powerCap, connectors, price>
    cardTypes = get_tuples("CardTypes", 2)    # <cardPower, demand>

    # optional consistency checks
    nbRackModels = get_int("nbRackModels")
    nbCardTypes = get_int("nbCardTypes")
    if nbRackModels != len(rackModels):
        raise ValueError(f"nbRackModels={nbRackModels} but found {len(rackModels)} RackModels in {path}")
    if nbCardTypes != len(cardTypes):
        raise ValueError(f"nbCardTypes={nbCardTypes} but found {len(cardTypes)} CardTypes in {path}")

    return nbRacks, rackModels, cardTypes


# -------------------------
# Load data from CLI .txt (recommended)
# Usage:
#   python src/Integrated_pycsp.py instances/instance1.txt
# Optional:
#   python src/Integrated_pycsp.py instances/instance1.txt choco
#   python src/Integrated_pycsp.py instances/instance1.txt ace
# -------------------------
solver_name = None
instance_path = None

if len(sys.argv) >= 2:
    instance_path = sys.argv[1]
if len(sys.argv) >= 3:
    solver_name = sys.argv[2]

if instance_path and instance_path.endswith(".txt"):
    nRacks, models, cardTypes = parse_instance_txt(instance_path)
else:
    # fallback if you run via pycsp3 -data=...
    nRacks, models, cardTypes = data

# models: [powerCap, connectors, price]
powersCap, connectorsCap, prices = columns(models, 0), columns(models, 1), columns(models, 2)
# cardTypes: [cardPower, demand]
cardPowers, demands = columns(cardTypes, 0), columns(cardTypes, 1)

nModels = len(models)
nTypes = len(cardTypes)

# Expand each card type into individual card instances (tau, t)
cardTypeOf = []
for tau in range(nTypes):
    cardTypeOf += [tau] * demands[tau]
nCards = len(cardTypeOf)

# slot encoding: (m,r) -> slotId
def slot_id(m: int, r: int) -> int:
    return m * nRacks + r

nSlots = nModels * nRacks


# -------------------------
# Variables
# -------------------------
W = VarArray(size=[nModels, nRacks], dom={0, 1})
Rel = VarArray(size=[nModels, nRacks, nCards], dom={0, 1})
Map = VarArray(size=nCards, dom=range(nSlots))


# -------------------------
# Constraints + FULL SB
# -------------------------
constraints = []

# (1) Demand: each card assigned exactly once
constraints += [Sum(Rel[:, :, k]) == 1 for k in range(nCards)]

# (2) Connector capacity
constraints += [
    Sum(Rel[m][r]) <= connectorsCap[m]
    for m in range(nModels) for r in range(nRacks)
]

# (3) Power capacity
constraints += [
    Sum(Rel[m][r][k] * cardPowers[cardTypeOf[k]] for k in range(nCards)) <= powersCap[m]
    for m in range(nModels) for r in range(nRacks)
]

# (4) Cardinality on used rack-uses
constraints += [Sum(W) <= nRacks]

# (5) Linking Rel -> W
constraints += [
    Rel[m][r][k] <= W[m][r]
    for m in range(nModels) for r in range(nRacks) for k in range(nCards)
]

# (6) CHANNELLING: Rel[m,r,k] <-> (Map[k] == slot_id(m,r))
constraints += [
    Rel[m][r][k] == (Map[k] == slot_id(m, r))
    for k in range(nCards)
    for m in range(nModels)
    for r in range(nRacks)
]

# -------------------------
# Symmetry Breaking (ALL)
# -------------------------

# SB1: no gaps per model
constraints += [Decreasing(W[m]) for m in range(nModels)]

# SB2: adjacent used rack-uses of same model have non-increasing #cards
constraints += [
    imply(
        (W[m][r - 1] == 1) & (W[m][r] == 1),
        Sum(Rel[m][r - 1]) >= Sum(Rel[m][r])
    )
    for m in range(nModels)
    for r in range(1, nRacks)
]

# SB3: order identical cards of each type by Map (paper uses non-increasing)
start = 0
for tau in range(nTypes):
    q = demands[tau]
    if q >= 2:
        constraints += [Map[start + t - 1] >= Map[start + t] for t in range(1, q)]
    start += q

satisfy(constraints)

# Objective: minimize total cost
OBJ = Sum(W[m][r] * prices[m] for m in range(nModels) for r in range(nRacks))
minimize(OBJ)


# -------------------------
# Solve + Print results (when running as plain python script)
# -------------------------
def compute_cost() -> int:
    total = 0
    for m in range(nModels):
        for r in range(nRacks):
            total += prices[m] * int(value(W[m][r]))
    return total

def pretty_solution():
    # Print used rack-uses and card distribution by type
    used = [(m, r) for m in range(nModels) for r in range(nRacks) if int(value(W[m][r])) == 1]

    print("\n===== SOLUTION =====")
    print(f"Used rack-uses: {len(used)} (limit nbRacks={nRacks})")
    if not used:
        return

    # Group by model
    by_model = {m: [] for m in range(nModels)}
    for (m, r) in used:
        by_model[m].append(r)

    print("\nUsed rack-uses per model:")
    for m in range(nModels):
        if by_model[m]:
            print(f"  model {m}: uses {by_model[m]}  (price={prices[m]}, capPower={powersCap[m]}, capConn={connectorsCap[m]})")

    print("\nRack contents (counts by card type):")
    for (m, r) in used:
        counts = [0] * nTypes
        for k in range(nCards):
            if int(value(Rel[m][r][k])) == 1:
                counts[cardTypeOf[k]] += 1
        total_cards = sum(counts)
        total_power = sum(counts[tau] * cardPowers[tau] for tau in range(nTypes))
        print(f"  (m={m}, r={r}) cards={total_cards}, power={total_power}  counts={counts}")

def main():
    print("===== INSTANCE =====")
    if instance_path:
        print(f"Path: {instance_path}")
    print(f"nbRacks={nRacks}, nbModels={nModels}, nbTypes={nTypes}, nbCards={nCards}")
    print("Running solver..." + (f" (solver={solver_name})" if solver_name else ""))

    t0 = time.time()
    try:
        if solver_name:
            res = solve(solver=solver_name)
        else:
            res = solve()
    except Exception as e:
        print("\n[ERROR] solve() failed. This usually means the solver backend isn't configured.")
        print("Try: python src/Integrated_pycsp.py instances/instance1.txt choco")
        print(f"Exception: {e}")
        return
    t1 = time.time()

    print("\n===== STATUS =====")
    print(f"Wall time (python): {t1 - t0:.3f} s")

    # Some backends expose extra status; if unavailable, this will just be skipped.
    try:
        print(f"Solver status: {solverStatus()}")
    except Exception:
        pass

    if not res:
        print("No solution found (or solver returned UNSAT/UNKNOWN).")
        return

    print("\n===== OBJECTIVE =====")
    print(f"Cost: {compute_cost()}")

    pretty_solution()

if __name__ == "__main__":
    main()
