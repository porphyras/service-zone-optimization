"""Route B: run ./solve with SZ_MIPPIPE=1; it searches, builds the zone-selection MIP and sends it
here over its stdout; we solve it with highspy and send the column values back over its stdin.
The solver itself validates the answer and writes solution.json. Nothing is printed to stdout.
Protocol (little endian): int32 magic, nc, nr, nnz, hasWarm; float64 time limit; then cost, lower,
upper (nc float64 each), integrality (nc int8), row lower, row upper (nr float64 each), column
starts (nc+1 int32), row indices (nnz int32), values (nnz float64), warm start (nc float64).
Reply: int32 status (2 optimal, 1 feasible, 0 none) and nc float64 values. nc = 0 ends."""
import os
import subprocess
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
MAGIC = 0x4D495031


def read_exact(f, n):
    b = bytearray()
    while len(b) < n:
        c = f.read(n - len(b))
        if not c:
            return None
        b += c
    return bytes(b)


def solve(hdr, tl, f):
    import highspy
    nc, nr, nnz, has_warm = hdr
    arr = lambda n, dt: np.frombuffer(read_exact(f, n * np.dtype(dt).itemsize), dtype=dt)
    cost, lo, hi = arr(nc, "<f8"), arr(nc, "<f8"), arr(nc, "<f8")
    integ = arr(nc, "i1")
    rlo, rhi = arr(nr, "<f8"), arr(nr, "<f8")
    start, index, value = arr(nc + 1, "<i4"), arr(nnz, "<i4"), arr(nnz, "<f8")
    warm = arr(nc, "<f8") if has_warm else None
    h = highspy.Highs()
    h.setOptionValue("output_flag", False)
    h.setOptionValue("time_limit", float(tl))
    h.setOptionValue("mip_rel_gap", 1e-6)
    lp = highspy.HighsLp()
    lp.num_col_, lp.num_row_ = nc, nr
    lp.sense_ = highspy.ObjSense.kMaximize
    lp.col_cost_, lp.col_lower_, lp.col_upper_ = cost, lo, hi
    lp.row_lower_, lp.row_upper_ = rlo, rhi
    lp.a_matrix_.format_ = highspy.MatrixFormat.kColwise
    lp.a_matrix_.num_col_, lp.a_matrix_.num_row_ = nc, nr
    lp.a_matrix_.start_, lp.a_matrix_.index_, lp.a_matrix_.value_ = start, index, value
    lp.integrality_ = [highspy.HighsVarType.kInteger if v else highspy.HighsVarType.kContinuous for v in integ]
    h.passModel(lp)
    if warm is not None:
        s0 = highspy.HighsSolution()
        s0.col_value = list(warm)
        s0.value_valid = True
        h.setSolution(s0)
    h.run()
    info = h.getInfo()
    if info.primal_solution_status != 2:  # kSolutionStatusFeasible
        return 0, None
    st = 2 if h.getModelStatus() == highspy.HighsModelStatus.kOptimal else 1
    return st, np.asarray(h.getSolution().col_value, dtype="<f8")


def main():
    env = dict(os.environ, SZ_MIPPIPE="1")
    args = [os.path.join(HERE, "solve")] + sys.argv[1:]
    p = subprocess.Popen(args, stdin=subprocess.PIPE, stdout=subprocess.PIPE, env=env, cwd=os.getcwd())
    try:
        while True:
            raw = read_exact(p.stdout, 5 * 4 + 8)
            if raw is None:
                break
            hdr = np.frombuffer(raw[:20], dtype="<i4")
            tl = float(np.frombuffer(raw[20:], dtype="<f8")[0])
            if int(hdr[0]) != MAGIC or int(hdr[1]) == 0:
                break
            try:
                st, x = solve([int(v) for v in hdr[1:]], tl, p.stdout)
            except Exception as e:  # never leave the solver waiting
                print("mip_driver:", repr(e), file=sys.stderr)
                st, x = 0, None
            p.stdin.write(np.int32(st).tobytes())
            if x is not None:
                p.stdin.write(x.tobytes())
            p.stdin.flush()
    except Exception as e:
        print("mip_driver:", repr(e), file=sys.stderr)
    finally:
        try:
            p.stdin.close()
        except Exception:
            pass
    return p.wait()


if __name__ == "__main__":
    sys.exit(main())
