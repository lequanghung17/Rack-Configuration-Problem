import json
import os
import time
import tempfile
import fcntl
from typing import Any, Callable, Dict, Optional


def _lock_path(state_path: str) -> str:
    return state_path + ".lock"


def _read_unlocked(state_path: str) -> Dict[str, Any]:
    if not os.path.exists(state_path):
        return {}
    with open(state_path, "r", encoding="utf-8") as f:
        return json.load(f)


def _write_unlocked(state_path: str, state: Dict[str, Any]) -> None:
    directory = os.path.dirname(state_path) or "."
    os.makedirs(directory, exist_ok=True)

    fd, tmp_path = tempfile.mkstemp(prefix=".state_", suffix=".tmp", dir=directory)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            json.dump(state, f, indent=2, sort_keys=True)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp_path, state_path)
    finally:
        if os.path.exists(tmp_path):
            try:
                os.remove(tmp_path)
            except OSError:
                pass


def read_state(state_path: str) -> Dict[str, Any]:
    lock_path = _lock_path(state_path)
    directory = os.path.dirname(lock_path) or "."
    os.makedirs(directory, exist_ok=True)

    with open(lock_path, "a+", encoding="utf-8") as lockf:
        fcntl.flock(lockf, fcntl.LOCK_SH)
        try:
            return _read_unlocked(state_path)
        finally:
            fcntl.flock(lockf, fcntl.LOCK_UN)


def update_state(state_path: str, updater: Callable[[Dict[str, Any]], Dict[str, Any]]) -> Dict[str, Any]:
    lock_path = _lock_path(state_path)
    directory = os.path.dirname(lock_path) or "."
    os.makedirs(directory, exist_ok=True)

    with open(lock_path, "a+", encoding="utf-8") as lockf:
        fcntl.flock(lockf, fcntl.LOCK_EX)
        try:
            state = _read_unlocked(state_path)
            new_state = updater(dict(state))
            _write_unlocked(state_path, new_state)
            return new_state
        finally:
            fcntl.flock(lockf, fcntl.LOCK_UN)


def init_state(state_path: str, instance_path: str, total_time_limit: float) -> Dict[str, Any]:
    now = time.time()
    deadline_ts = now + float(total_time_limit)

    state = {
        "instance": instance_path,
        "status": "RUNNING",
        "global_ub": None,
        "global_lb": None,
        "optimal_cost": None,
        "best_source": None,
        "mip_status": None,
        "sat_status": None,
        "deadline_ts": deadline_ts,
        "updated_at": now,
    }
    _write_unlocked(state_path, state)
    return state


def update_ub(state_path: str, new_ub: int, source: str, extra: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
    def _upd(s: Dict[str, Any]) -> Dict[str, Any]:
        cur = s.get("global_ub")
        if cur is None or new_ub < cur:
            s["global_ub"] = int(new_ub)
            s["best_source"] = source
            s["updated_at"] = time.time()
        if extra:
            s.update(extra)
        return s

    return update_state(state_path, _upd)


def set_worker_status(state_path: str, key: str, value: str, extra: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
    def _upd(s: Dict[str, Any]) -> Dict[str, Any]:
        s[key] = value
        s["updated_at"] = time.time()
        if extra:
            s.update(extra)
        return s

    return update_state(state_path, _upd)


def mark_optimal(state_path: str, cost: int, source: str, extra: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
    def _upd(s: Dict[str, Any]) -> Dict[str, Any]:
        s["status"] = "OPTIMAL"
        s["optimal_cost"] = int(cost)
        s["global_ub"] = int(cost)
        s["best_source"] = source
        s["updated_at"] = time.time()
        if extra:
            s.update(extra)
        return s

    return update_state(state_path, _upd)


def mark_time_limit(state_path: str) -> Dict[str, Any]:
    def _upd(s: Dict[str, Any]) -> Dict[str, Any]:
        if s.get("status") == "RUNNING":
            s["status"] = "TIME_LIMIT"
            s["updated_at"] = time.time()
        return s

    return update_state(state_path, _upd)