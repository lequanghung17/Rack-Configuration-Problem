import argparse
import time

import gurobipy as gp
from gurobipy import GRB

from gurobi import parse_instance_file, IntegratedModelMIP
from shared_state import read_state, update_ub, set_worker_status, mark_optimal


def log(msg: str) -> None:
    print(f"[MIP {time.strftime('%H:%M:%S')}] {msg}", flush=True)


def main() -> None:
    t_total0 = time.perf_counter()

    ap = argparse.ArgumentParser(description="Hybrid Gurobi worker for RCP")
    ap.add_argument("--inst", required=True)
    ap.add_argument("--state-file", required=True)
    ap.add_argument("--threads", type=int, default=1)
    ap.add_argument("--mip-gap", type=float, default=None)
    ap.add_argument("--no-sb3", action="store_true")
    ap.add_argument("--no-load-order", action="store_true")
    ap.add_argument("--branch-on-dual", action="store_true")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args()

    st = read_state(args.state_file)
    deadline_ts = st["deadline_ts"]
    remaining = max(0.0, deadline_ts - time.time())

    inst = parse_instance_file(args.inst)
    builder = IntegratedModelMIP(
        inst,
        use_sb3=not args.no_sb3,
        use_load_order=not args.no_load_order,
        branch_on_dual=args.branch_on_dual,
    )
    model = builder.build()

    model.Params.Threads = int(args.threads)
    model.Params.OutputFlag = 0 if args.quiet else 1
    model.Params.TimeLimit = float(remaining)
    if args.mip_gap is not None:
        model.Params.MIPGap = float(args.mip_gap)

    log(f"start optimize | threads={args.threads} | time_limit={remaining:.2f}s")

    def cb(m: gp.Model, where: int):
        if where == GRB.Callback.MIPSOL:
            try:
                obj = m.cbGet(GRB.Callback.MIPSOL_OBJ)
                update_ub(
                    args.state_file,
                    int(round(obj)),
                    source="MIP",
                    extra={"mip_status": "RUNNING"},
                )
            except Exception:
                pass

        elif where == GRB.Callback.MIP:
            st_now = read_state(args.state_file)
            if st_now.get("status") == "OPTIMAL":
                m.terminate()
                return
            if time.time() >= st_now.get("deadline_ts", float("inf")):
                m.terminate()
                return

    t_solve0 = time.perf_counter()
    model.optimize(cb)
    t_solve1 = time.perf_counter()
    t_total1 = time.perf_counter()

    status = model.Status
    solve_runtime = t_solve1 - t_solve0
    total_runtime = t_total1 - t_total0

    extra = {
        "mip_solve_time_sec": solve_runtime,
        "mip_total_time_sec": total_runtime,
        "mip_status_code": int(status),
    }

    if model.SolCount > 0:
        extra["mip_objval"] = float(model.ObjVal)
        extra["mip_objbound"] = float(model.ObjBound)
        update_ub(args.state_file, int(round(model.ObjVal)), source="MIP", extra=extra)

    if status == GRB.OPTIMAL and model.SolCount > 0:
        mark_optimal(
            args.state_file,
            int(round(model.ObjVal)),
            source="MIP",
            extra=extra,
        )
        log(
            f"OPTIMAL by MIP | obj={model.ObjVal:.6f} | "
            f"solve={solve_runtime:.2f}s | total={total_runtime:.2f}s"
        )
        return

    if status == GRB.TIME_LIMIT:
        set_worker_status(args.state_file, "mip_status", "TIME_LIMIT", extra=extra)
        log(f"TIME_LIMIT | solve={solve_runtime:.2f}s | total={total_runtime:.2f}s")
        return

    if status == GRB.INTERRUPTED:
        set_worker_status(args.state_file, "mip_status", "INTERRUPTED", extra=extra)
        log(f"INTERRUPTED | solve={solve_runtime:.2f}s | total={total_runtime:.2f}s")
        return

    if status == GRB.INFEASIBLE:
        set_worker_status(args.state_file, "mip_status", "INFEASIBLE", extra=extra)
        log(f"INFEASIBLE | total={total_runtime:.2f}s")
        return

    set_worker_status(args.state_file, "mip_status", f"STATUS_{status}", extra=extra)
    log(f"finished with status={status} | solve={solve_runtime:.2f}s | total={total_runtime:.2f}s")


if __name__ == "__main__":
    main()

# import argparse
# import time

# import gurobipy as gp
# from gurobipy import GRB

# from gurobi import parse_instance_file, IntegratedModelMIP
# from shared_state import read_state, update_ub, set_worker_status, mark_optimal


# def log(msg: str) -> None:
#     print(f"[MIP {time.strftime('%H:%M:%S')}] {msg}", flush=True)


# def main() -> None:
#     ap = argparse.ArgumentParser(description="Hybrid Gurobi worker for RCP")
#     ap.add_argument("--inst", required=True)
#     ap.add_argument("--state-file", required=True)
#     ap.add_argument("--threads", type=int, default=1)
#     ap.add_argument("--mip-gap", type=float, default=None)
#     ap.add_argument("--no-sb3", action="store_true")
#     ap.add_argument("--no-load-order", action="store_true")
#     ap.add_argument("--branch-on-dual", action="store_true")
#     ap.add_argument("--quiet", action="store_true")
#     args = ap.parse_args()

#     st = read_state(args.state_file)
#     deadline_ts = st["deadline_ts"]
#     remaining = max(0.0, deadline_ts - time.time())

#     inst = parse_instance_file(args.inst)
#     builder = IntegratedModelMIP(
#         inst,
#         use_sb3=not args.no_sb3,
#         use_load_order=not args.no_load_order,
#         branch_on_dual=args.branch_on_dual,
#     )
#     model = builder.build()

#     model.Params.Threads = int(args.threads)
#     model.Params.OutputFlag = 0 if args.quiet else 1
#     model.Params.TimeLimit = float(remaining)
#     if args.mip_gap is not None:
#         model.Params.MIPGap = float(args.mip_gap)

#     log(f"start optimize | threads={args.threads} | time_limit={remaining:.2f}s")

#     def cb(m: gp.Model, where: int):
#         if where == GRB.Callback.MIPSOL:
#             try:
#                 obj = m.cbGet(GRB.Callback.MIPSOL_OBJ)
#                 update_ub(
#                     args.state_file,
#                     int(round(obj)),
#                     source="MIP",
#                     extra={"mip_status": "RUNNING"},
#                 )
#             except Exception:
#                 pass

#         elif where == GRB.Callback.MIP:
#             st_now = read_state(args.state_file)
#             if st_now.get("status") == "OPTIMAL":
#                 m.terminate()
#                 return
#             if time.time() >= st_now.get("deadline_ts", float("inf")):
#                 m.terminate()
#                 return

#     t0 = time.perf_counter()
#     model.optimize(cb)
#     t1 = time.perf_counter()

#     status = model.Status
#     extra = {
#         "mip_runtime_sec": t1 - t0,
#         "mip_status_code": int(status),
#     }

#     if model.SolCount > 0:
#         extra["mip_objval"] = float(model.ObjVal)
#         extra["mip_objbound"] = float(model.ObjBound)
#         update_ub(args.state_file, int(round(model.ObjVal)), source="MIP", extra=extra)

#     if status == GRB.OPTIMAL and model.SolCount > 0:
#         mark_optimal(
#             args.state_file,
#             int(round(model.ObjVal)),
#             source="MIP",
#             extra=extra,
#         )
#         log(f"OPTIMAL by MIP | obj={model.ObjVal:.6f} | runtime={t1 - t0:.2f}s")
#         return

#     if status == GRB.TIME_LIMIT:
#         set_worker_status(args.state_file, "mip_status", "TIME_LIMIT", extra=extra)
#         log(f"TIME_LIMIT | runtime={t1 - t0:.2f}s")
#         return

#     if status == GRB.INTERRUPTED:
#         set_worker_status(args.state_file, "mip_status", "INTERRUPTED", extra=extra)
#         log(f"INTERRUPTED | runtime={t1 - t0:.2f}s")
#         return

#     if status == GRB.INFEASIBLE:
#         set_worker_status(args.state_file, "mip_status", "INFEASIBLE", extra=extra)
#         log("INFEASIBLE")
#         return

#     set_worker_status(args.state_file, "mip_status", f"STATUS_{status}", extra=extra)
#     log(f"finished with status={status} | runtime={t1 - t0:.2f}s")


# if __name__ == "__main__":
#     main()