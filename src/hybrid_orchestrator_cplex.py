import argparse
import os
import signal
import subprocess
import sys
import time
from pathlib import Path

from shared_state import init_state, read_state, mark_time_limit, update_state


def log(msg: str) -> None:
    print(f"[ORCH {time.strftime('%H:%M:%S')}] {msg}", flush=True)


def terminate_process_tree(proc: subprocess.Popen) -> None:
    if proc.poll() is not None:
        return
    try:
        os.killpg(os.getpgid(proc.pid), signal.SIGTERM)
    except Exception:
        try:
            proc.terminate()
        except Exception:
            pass


def main() -> None:
    t_total0 = time.perf_counter()

    ap = argparse.ArgumentParser(description="Hybrid orchestrator: CPLEX main + SAT certifier")
    ap.add_argument("--inst", required=True)
    ap.add_argument("--time-limit", type=float, default=3600)
    ap.add_argument("--state-file", default="logs/shared_state.json")
    ap.add_argument("--sat-solver", default="g42")
    ap.add_argument("--threads", type=int, default=1)
    ap.add_argument("--mip-gap", type=float, default=None)
    ap.add_argument("--poll", type=float, default=0.5)
    ap.add_argument("--quiet-mip", action="store_true")
    ap.add_argument("--no-map-order", action="store_true")
    ap.add_argument("--no-load-order", action="store_true")
    args = ap.parse_args()

    src_dir = Path(__file__).resolve().parent

    init_state(args.state_file, args.inst, args.time_limit)
    st0 = read_state(args.state_file)
    deadline_ts = st0["deadline_ts"]

    mip_cmd = [
        sys.executable,
        str(src_dir / "hybrid_mip_cplex_worker.py"),
        "--inst", args.inst,
        "--state-file", args.state_file,
        "--threads", str(args.threads),
    ]
    if args.mip_gap is not None:
        mip_cmd += ["--mip-gap", str(args.mip_gap)]
    if args.quiet_mip:
        mip_cmd += ["--quiet"]
    if args.no_map_order:
        mip_cmd += ["--no-map-order"]
    if args.no_load_order:
        mip_cmd += ["--no-load-order"]

    sat_cmd = [
        sys.executable,
        # str(src_dir / "hybrid_sat_certifier_worker.py"),
        str(src_dir / "hybrid_sat_reuse_var_certifier_worker.py"),
        "--inst", args.inst,
        "--state-file", args.state_file,
        "--solver", args.sat_solver,
        "--poll", str(args.poll),
    ]

    log("starting workers")
    log("MIP cmd: " + " ".join(mip_cmd))
    log("SAT cmd: " + " ".join(sat_cmd))

    mip_proc = subprocess.Popen(mip_cmd, preexec_fn=os.setsid)
    sat_proc = subprocess.Popen(sat_cmd, preexec_fn=os.setsid)

    try:
        while True:
            st = read_state(args.state_file)
            status = st.get("status", "RUNNING")
            ub = st.get("global_ub", None)
            best_source = st.get("best_source", None)

            if ub is not None:
                log(f"current global_ub={ub} from {best_source}")

            if status == "OPTIMAL":
                log(f"OPTIMAL found: {st.get('optimal_cost')} by {st.get('best_source')}")
                break

            if time.time() >= deadline_ts:
                log("global time limit reached")
                mark_time_limit(args.state_file)
                break

            if mip_proc.poll() is not None and sat_proc.poll() is not None:
                log("both workers exited")
                break

            time.sleep(args.poll)

    finally:
        terminate_process_tree(mip_proc)
        terminate_process_tree(sat_proc)

    total_runtime_sec = time.perf_counter() - t_total0

    def _add_total(s):
        s["total_runtime_sec"] = total_runtime_sec
        s["updated_at"] = time.time()
        return s

    update_state(args.state_file, _add_total)

    st_final = read_state(args.state_file)
    print("\n" + "=" * 80)
    print("FINAL HYBRID STATE")
    print("=" * 80)
    for k in sorted(st_final.keys()):
        print(f"{k}: {st_final[k]}")
    print("=" * 80 + "\n")


if __name__ == "__main__":
    main()



# import argparse
# import os
# import signal
# import subprocess
# import sys
# import time
# from pathlib import Path

# from shared_state import init_state, read_state, mark_time_limit


# def log(msg: str) -> None:
#     print(f"[ORCH {time.strftime('%H:%M:%S')}] {msg}", flush=True)


# def terminate_process_tree(proc: subprocess.Popen) -> None:
#     if proc.poll() is not None:
#         return
#     try:
#         os.killpg(os.getpgid(proc.pid), signal.SIGTERM)
#     except Exception:
#         try:
#             proc.terminate()
#         except Exception:
#             pass


# def main() -> None:
#     ap = argparse.ArgumentParser(description="Hybrid orchestrator: CPLEX main + SAT certifier")
#     ap.add_argument("--inst", required=True)
#     ap.add_argument("--time-limit", type=float, default=3600)
#     ap.add_argument("--state-file", default="logs/shared_state.json")
#     ap.add_argument("--sat-solver", default="g42")
#     ap.add_argument("--threads", type=int, default=1)
#     ap.add_argument("--mip-gap", type=float, default=None)
#     ap.add_argument("--poll", type=float, default=0.5)
#     ap.add_argument("--quiet-mip", action="store_true")
#     ap.add_argument("--no-map-order", action="store_true")
#     ap.add_argument("--no-load-order", action="store_true")
#     args = ap.parse_args()

#     src_dir = Path(__file__).resolve().parent

#     init_state(args.state_file, args.inst, args.time_limit)
#     st0 = read_state(args.state_file)
#     deadline_ts = st0["deadline_ts"]

#     mip_cmd = [
#         sys.executable,
#         str(src_dir / "hybrid_mip_cplex_worker.py"),
#         "--inst", args.inst,
#         "--state-file", args.state_file,
#         "--threads", str(args.threads),
#     ]
#     if args.mip_gap is not None:
#         mip_cmd += ["--mip-gap", str(args.mip_gap)]
#     if args.quiet_mip:
#         mip_cmd += ["--quiet"]
#     if args.no_map_order:
#         mip_cmd += ["--no-map-order"]
#     if args.no_load_order:
#         mip_cmd += ["--no-load-order"]

#     sat_cmd = [
#         sys.executable,
#         str(src_dir / "hybrid_sat_certifier_worker.py"),
#         "--inst", args.inst,
#         "--state-file", args.state_file,
#         "--solver", args.sat_solver,
#         "--poll", str(args.poll),
#     ]

#     log("starting workers")
#     log("MIP cmd: " + " ".join(mip_cmd))
#     log("SAT cmd: " + " ".join(sat_cmd))

#     mip_proc = subprocess.Popen(mip_cmd, preexec_fn=os.setsid)
#     sat_proc = subprocess.Popen(sat_cmd, preexec_fn=os.setsid)

#     try:
#         while True:
#             st = read_state(args.state_file)
#             status = st.get("status", "RUNNING")
#             ub = st.get("global_ub", None)
#             best_source = st.get("best_source", None)

#             if ub is not None:
#                 log(f"current global_ub={ub} from {best_source}")

#             if status == "OPTIMAL":
#                 log(f"OPTIMAL found: {st.get('optimal_cost')} by {st.get('best_source')}")
#                 break

#             if time.time() >= deadline_ts:
#                 log("global time limit reached")
#                 mark_time_limit(args.state_file)
#                 break

#             if mip_proc.poll() is not None and sat_proc.poll() is not None:
#                 log("both workers exited")
#                 break

#             time.sleep(args.poll)

#     finally:
#         terminate_process_tree(mip_proc)
#         terminate_process_tree(sat_proc)

#     st_final = read_state(args.state_file)
#     print("\n" + "=" * 80)
#     print("FINAL HYBRID STATE")
#     print("=" * 80)
#     for k in sorted(st_final.keys()):
#         print(f"{k}: {st_final[k]}")
#     print("=" * 80 + "\n")


# if __name__ == "__main__":
#     main()