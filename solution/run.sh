#!/bin/sh
# make --silent run: nothing on stdout. Route A (solve_mip, HiGHS inside), else route B (Python
# driver + highspy over pipes), else the pure solver. If the chosen route fails, the pure solver
# gets the time that is left (it rewrites solution.json from scratch) if the failure came early.
cd "$(dirname "$0")" || exit 1
START=$(date +%s)
rc=1
if [ -x ./solve_mip ]; then
    ./solve_mip > /dev/null
    rc=$?
elif [ -x .venv/bin/python ] && [ -x ./solve ]; then
    .venv/bin/python mip_driver.py > /dev/null
    rc=$?
fi
# a late failure keeps the checkpoint the solver already wrote (better than a short rerun)
if [ $rc -ne 0 ] && [ $(($(date +%s) - START)) -lt 150 ]; then
    LEFT=$((280 - ($(date +%s) - START)))
    [ $LEFT -gt 250 ] && LEFT=250
    [ $LEFT -gt 3 ] && ./solve $LEFT > /dev/null
fi
exit 0
