# progress.py  – thread‑local sink for partial boards
import queue, threading, time

# Store a per‑thread queue so parallel solves don't interfere
_local = threading.local()

def bind(q: queue.Queue):
    """Attach q to the *current* thread; called by the web layer."""
    _local.q = q

def unbind():
    if hasattr(_local, "q"):
        del _local.q

def step(board):
    """
    Push a deep‑copied board to whatever queue is bound
    (-1 = unknown, 0 = island, 1 = sea).  No‑op if nothing bound.
    """
    q = getattr(_local, "q", None)
    if q:
        from copy import deepcopy
        q.put(("PART", deepcopy(board)))          # never leak mutable refs
