import argparse
import time
from pysat.solvers import Solver

from IncrementalSAT_reuse_var import (
    parse_instance_file,
    IntegratedModelSAT,
    encode_cost_le_assumption,
    solve_with_timeout,
)
from shared_state import read_state, update_ub, set_worker_status, mark_optimal


def log(msg: str) -> None:
    print(f"[SAT-COUNT {time.strftime('%H:%M:%S')}] {msg}", flush=True)


def main():
    t_total0 = time.perf_counter()

    ap = argparse.ArgumentParser()
    ap.add_argument("--inst", required=True)
    ap.add_argument("--state-file", required=True)
    ap.add_argument("--solver", default="g42")
    ap.add_argument("--poll", type=float, default=0.5)
    args = ap.parse_args()

    inst = parse_instance_file(args.inst)
    sat = IntegratedModelSAT(inst)
    sat.build_F1()

    log(f"built F1 | vars={sat.vpool.top} | clauses={len(sat.cnf.clauses)}")

    last_tested_ub = None

    with Solver(name=args.solver, bootstrap_with=sat.cnf.clauses, use_timer=True) as s:
        while True:
            st = read_state(args.state_file)
            status = st.get("status", "RUNNING")
            deadline_ts = st.get("deadline_ts", float("inf"))

            total_now = time.perf_counter() - t_total0
            solver_now = s.time_accum()

            if status != "RUNNING":
                set_worker_status(
                    args.state_file,
                    "sat_status",
                    f"STOPPED_{status}",
                    extra={
                        "sat_solver_time_sec": solver_now,
                        "sat_total_time_sec": total_now,
                    },
                )
                return

            if time.time() >= deadline_ts:
                set_worker_status(
                    args.state_file,
                    "sat_status",
                    "TIME_LIMIT",
                    extra={
                        "sat_solver_time_sec": solver_now,
                        "sat_total_time_sec": total_now,
                    },
                )
                return

            ub = st.get("global_ub", None)
            if ub is None:
                time.sleep(args.poll)
                continue

            if last_tested_ub is not None and ub >= last_tested_ub:
                time.sleep(args.poll)
                continue

            target = ub - 1
            if target < 0:
                mark_optimal(
                    args.state_file,
                    ub,
                    source="SAT",
                    extra={
                        "sat_status": "OPTIMAL",
                        "sat_solver_time_sec": solver_now,
                        "sat_total_time_sec": total_now,
                    },
                )
                return

            log(f"certifying UB={ub} by solving cost <= {target}")

            bound_clauses, act = encode_cost_le_assumption(sat, target, tag=f"cert_{ub}")
            for cl in bound_clauses:
                s.add_clause(cl)

            last_tested_ub = ub
            remaining = max(0.0, deadline_ts - time.time())
            res = solve_with_timeout(s, [act], remaining)

            total_now = time.perf_counter() - t_total0
            solver_now = s.time_accum()

            if res is None:
                set_worker_status(
                    args.state_file,
                    "sat_status",
                    "TIME_LIMIT",
                    extra={
                        "sat_solver_time_sec": solver_now,
                        "sat_total_time_sec": total_now,
                    },
                )
                return

            if res is False:
                st_after = read_state(args.state_file)
                current_ub = st_after.get("global_ub", None)
                if current_ub == ub:
                    mark_optimal(
                        args.state_file,
                        ub,
                        source="SAT",
                        extra={
                            "sat_status": "OPTIMAL",
                            "sat_certified_against": target,
                            "sat_solver_time_sec": solver_now,
                            "sat_total_time_sec": total_now,
                        },
                    )
                    log(f"OPTIMAL by SAT certificate | no solution with cost <= {target}")
                    return
                else:
                    continue

            model = s.get_model()
            new_cost = sat.model_cost(model)
            update_ub(
                args.state_file,
                int(new_cost),
                source="SAT",
                extra={
                    "sat_status": "RUNNING",
                    "sat_last_improvement_from": ub,
                    "sat_solver_time_sec": solver_now,
                    "sat_total_time_sec": total_now,
                },
            )
            log(f"SAT improved UB: {ub} -> {new_cost}")


if __name__ == "__main__":
    main()