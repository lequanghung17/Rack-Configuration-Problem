import argparse
import time

from cplex_mip import parse_instance_file, IntegratedMIPCplex
from shared_state import read_state, update_ub, set_worker_status, mark_optimal


def log(msg: str) -> None:
    print(f"[MIP-CPLEX {time.strftime('%H:%M:%S')}] {msg}", flush=True)


def _normalize_cplex_status(status) -> str:
    s = str(status).lower()
    if "optimal" in s:
        return "OPTIMAL"
    if "infeasible" in s:
        return "INFEASIBLE"
    if "time" in s and "limit" in s:
        return "TIME_LIMIT"
    if "abort" in s or "interrupt" in s:
        return "INTERRUPTED"
    return str(status)


def main() -> None:
    t_total0 = time.perf_counter()

    ap = argparse.ArgumentParser(description="Hybrid CPLEX worker for RCP")
    ap.add_argument("--inst", required=True)
    ap.add_argument("--state-file", required=True)
    ap.add_argument("--threads", type=int, default=1)
    ap.add_argument("--mip-gap", type=float, default=None)
    ap.add_argument("--no-map-order", action="store_true")
    ap.add_argument("--no-load-order", action="store_true")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args()

    st = read_state(args.state_file)
    deadline_ts = st["deadline_ts"]
    remaining = max(0.0, deadline_ts - time.time())

    inst = parse_instance_file(args.inst)
    builder = IntegratedMIPCplex(
        inst,
        use_map_order=not args.no_map_order,
        use_load_order=not args.no_load_order,
    )
    builder.build()

    log(f"start optimize | threads={args.threads} | time_limit={remaining:.2f}s")

    t_solve0 = time.perf_counter()
    sol = builder.solve(
        time_limit=remaining,
        threads=args.threads,
        mip_gap=args.mip_gap,
        quiet=args.quiet,
    )
    t_solve1 = time.perf_counter()
    t_total1 = time.perf_counter()

    solve_runtime = t_solve1 - t_solve0
    total_runtime = t_total1 - t_total0

    extra = {
        "mip_solve_time_sec": solve_runtime,
        "mip_total_time_sec": total_runtime,
    }

    if sol is not None:
        obj = builder.objective_from_solution(sol)
        status_raw = sol.solve_details.status
        status_norm = _normalize_cplex_status(status_raw)

        extra["mip_status_raw"] = str(status_raw)
        extra["mip_objval"] = float(obj)

        update_ub(args.state_file, int(round(obj)), source="MIP", extra=extra)

        if status_norm == "OPTIMAL":
            mark_optimal(
                args.state_file,
                int(round(obj)),
                source="MIP",
                extra={**extra, "mip_status": "OPTIMAL"},
            )
            log(f"OPTIMAL by MIP | obj={obj:.6f} | solve={solve_runtime:.2f}s | total={total_runtime:.2f}s")
            return

        if status_norm == "TIME_LIMIT":
            set_worker_status(args.state_file, "mip_status", "TIME_LIMIT", extra=extra)
            log(f"TIME_LIMIT with feasible solution | obj={obj:.6f} | solve={solve_runtime:.2f}s | total={total_runtime:.2f}s")
            return

        if status_norm == "INFEASIBLE":
            set_worker_status(args.state_file, "mip_status", "INFEASIBLE", extra=extra)
            log(f"INFEASIBLE | total={total_runtime:.2f}s")
            return

        set_worker_status(args.state_file, "mip_status", status_norm, extra=extra)
        log(f"finished with status={status_norm} | obj={obj:.6f} | solve={solve_runtime:.2f}s | total={total_runtime:.2f}s")
        return

    st_now = read_state(args.state_file)
    if time.time() >= st_now.get("deadline_ts", float("inf")):
        set_worker_status(args.state_file, "mip_status", "TIME_LIMIT", extra=extra)
        log(f"TIME_LIMIT | solve={solve_runtime:.2f}s | total={total_runtime:.2f}s")
        return

    if st_now.get("status") == "OPTIMAL":
        set_worker_status(args.state_file, "mip_status", "STOPPED_OPTIMAL", extra=extra)
        log(f"stop because global status=OPTIMAL | solve={solve_runtime:.2f}s | total={total_runtime:.2f}s")
        return

    set_worker_status(args.state_file, "mip_status", "NO_SOLUTION", extra=extra)
    log(f"finished with no solution | solve={solve_runtime:.2f}s | total={total_runtime:.2f}s")


if __name__ == "__main__":
    main()





# import argparse
# import time

# from cplex_mip import parse_instance_file, IntegratedMIPCplex
# from shared_state import read_state, update_ub, set_worker_status, mark_optimal


# def log(msg: str) -> None:
#     print(f"[MIP-CPLEX {time.strftime('%H:%M:%S')}] {msg}", flush=True)


# def _normalize_cplex_status(status) -> str:
#     s = str(status).lower()
#     if "optimal" in s:
#         return "OPTIMAL"
#     if "infeasible" in s:
#         return "INFEASIBLE"
#     if "time" in s and "limit" in s:
#         return "TIME_LIMIT"
#     if "abort" in s or "interrupt" in s:
#         return "INTERRUPTED"
#     return str(status)


# def main() -> None:
#     ap = argparse.ArgumentParser(description="Hybrid CPLEX worker for RCP")
#     ap.add_argument("--inst", required=True)
#     ap.add_argument("--state-file", required=True)
#     ap.add_argument("--threads", type=int, default=1)
#     ap.add_argument("--mip-gap", type=float, default=None)
#     ap.add_argument("--no-map-order", action="store_true")
#     ap.add_argument("--no-load-order", action="store_true")
#     ap.add_argument("--quiet", action="store_true")
#     args = ap.parse_args()

#     st = read_state(args.state_file)
#     deadline_ts = st["deadline_ts"]
#     remaining = max(0.0, deadline_ts - time.time())

#     inst = parse_instance_file(args.inst)
#     builder = IntegratedMIPCplex(
#         inst,
#         use_map_order=not args.no_map_order,
#         use_load_order=not args.no_load_order,
#     )
#     builder.build()

#     log(f"start optimize | threads={args.threads} | time_limit={remaining:.2f}s")

#     t0 = time.perf_counter()
#     sol = builder.solve(
#         time_limit=remaining,
#         threads=args.threads,
#         mip_gap=args.mip_gap,
#         quiet=args.quiet,
#     )
#     t1 = time.perf_counter()

#     runtime = t1 - t0
#     extra = {
#         "mip_runtime_sec": runtime,
#     }

#     # Nếu có nghiệm feasible, cập nhật UB vào shared state
#     if sol is not None:
#         obj = builder.objective_from_solution(sol)
#         status_raw = sol.solve_details.status
#         status_norm = _normalize_cplex_status(status_raw)

#         extra["mip_status_raw"] = str(status_raw)
#         extra["mip_objval"] = float(obj)

#         # ObjBound/BestBound trong docplex không chắc có sẵn theo đúng field,
#         # nên trước mắt chỉ ghi objval; nếu sau này lấy được best bound thì thêm vào đây.
#         update_ub(args.state_file, int(round(obj)), source="MIP", extra=extra)

#         if status_norm == "OPTIMAL":
#             mark_optimal(
#                 args.state_file,
#                 int(round(obj)),
#                 source="MIP",
#                 extra={**extra, "mip_status": "OPTIMAL"},
#             )
#             log(f"OPTIMAL by MIP | obj={obj:.6f} | runtime={runtime:.2f}s")
#             return

#         if status_norm == "TIME_LIMIT":
#             set_worker_status(
#                 args.state_file,
#                 "mip_status",
#                 "TIME_LIMIT",
#                 extra=extra,
#             )
#             log(f"TIME_LIMIT with feasible solution | obj={obj:.6f} | runtime={runtime:.2f}s")
#             return

#         if status_norm == "INFEASIBLE":
#             set_worker_status(
#                 args.state_file,
#                 "mip_status",
#                 "INFEASIBLE",
#                 extra=extra,
#             )
#             log("INFEASIBLE")
#             return

#         set_worker_status(
#             args.state_file,
#             "mip_status",
#             status_norm,
#             extra=extra,
#         )
#         log(f"finished with status={status_norm} | obj={obj:.6f} | runtime={runtime:.2f}s")
#         return

#     # sol is None
#     st_now = read_state(args.state_file)
#     if time.time() >= st_now.get("deadline_ts", float("inf")):
#         set_worker_status(
#             args.state_file,
#             "mip_status",
#             "TIME_LIMIT",
#             extra=extra,
#         )
#         log(f"TIME_LIMIT | runtime={runtime:.2f}s")
#         return

#     if st_now.get("status") == "OPTIMAL":
#         set_worker_status(
#             args.state_file,
#             "mip_status",
#             "STOPPED_OPTIMAL",
#             extra=extra,
#         )
#         log(f"stop because global status=OPTIMAL | runtime={runtime:.2f}s")
#         return

#     set_worker_status(
#         args.state_file,
#         "mip_status",
#         "NO_SOLUTION",
#         extra=extra,
#     )
#     log(f"finished with no solution | runtime={runtime:.2f}s")


# if __name__ == "__main__":
#     main()