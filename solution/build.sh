#!/bin/sh
# make build: always builds ./solve (pure C++ solver, no dependencies; with SZ_MIPPIPE=1 it hands
# its MIP to an external driver). Then tries route A: ./solve_mip = the same solver statically
# linked with HiGHS (preinstalled HiGHS in /usr/local, else pkg-config / cmake, else HiGHS built
# from source under /solution/highs-local). If route A fails, route B: .venv with highspy for
# mip_driver.py. run.sh picks the best route that exists. Nothing here may make the build fail.
cd "$(dirname "$0")" || exit 0
HERE=$(pwd)
LOG="$HERE/build.log"
: > "$LOG"
say() { echo "[build] $*" >&2; echo "[build] $*" >> "$LOG"; }
CXXFLAGS="-O3 -std=c++17"  # -O3: same results as -O2 (no fast-math), ~5-14% faster with g++ 15 on x86-64
NPROC=$(nproc 2>/dev/null || echo 2)

g++ $CXXFLAGS -o solve main.cpp >> "$LOG" 2>&1 || g++ -O2 -o solve main.cpp >> "$LOG" 2>&1
[ -x solve ] && say "solve: ok" || say "solve: FAILED"

rm -f solve_mip
try_link() {  # $1 = include flags, $2 = libs
    g++ $CXXFLAGS -DUSE_HIGHS $1 -o solve_mip.tmp main.cpp $2 >> "$LOG" 2>&1 || return 1
    # sanity run on a tiny instance (also proves the binary starts in this image)
    mkdir -p .selftest && cd .selftest || return 1
    printf '{"sites":[{"x":0,"y":0,"reward":10,"tasks":[0]},{"x":1,"y":0,"reward":10,"tasks":[0]},{"x":5,"y":5,"reward":10,"tasks":[]}],"offices":[{"x":0,"y":1,"cost":1,"maxSize":3},{"x":5,"y":6,"cost":1,"maxSize":3}],"workers":[[0]],"distances":[[1,1,9],[9,9,1]],"maxDifference":1,"balanceCoefficient":0.5}' > instance.json
    ../solve_mip.tmp 6 1 > /dev/null 2> selftest.log
    rc=$?
    # the answer must be a non-empty JSON list of zones (python3 when present, else a shape check)
    ok=1
    if [ -s solution.json ] && grep -q '"officeId"' solution.json; then
        if command -v python3 > /dev/null; then
            python3 -c 'import json; z = json.load(open("solution.json")); assert isinstance(z, list) and z' 2>> selftest.log && ok=0
        else
            tr -d ' \n\r\t' < solution.json | grep -q '^\[.*\]$' && ok=0
        fi
    fi
    cat selftest.log >> "$LOG"
    cd "$HERE" && rm -rf .selftest
    [ $rc -eq 0 ] && [ $ok -eq 0 ] && mv solve_mip.tmp solve_mip && return 0
    rm -f solve_mip.tmp
    return 1
}
link_prefix() {  # $1 = install prefix
    P=$1
    [ -f "$P/include/highs/Highs.h" ] || return 1
    for L in lib lib64 lib/x86_64-linux-gnu; do
        [ -f "$P/$L/libhighs.a" ] || [ -f "$P/$L/libhighs.so" ] || continue
        INC="-I$P/include/highs -I$P/include"
        EX=""
        [ -f "$P/$L/libhighs_extras.a" ] && EX="-lhighs_extras"
        BL=""
        [ -f "$P/$L/libopenblas.a" ] && BL="-lopenblas"
        for LIBS in "-L$P/$L -Wl,-Bstatic -lhighs $EX $BL -Wl,-Bdynamic -lz -lpthread -ldl" \
                    "-L$P/$L -Wl,-Bstatic -lhighs $EX $BL -Wl,-Bdynamic -lpthread -ldl" \
                    "-L$P/$L -lhighs $EX $BL -lz -lpthread -ldl" \
                    "-L$P/$L -lhighs $EX $BL -lpthread -ldl -Wl,-rpath,$P/$L"; do
            if try_link "$INC" "$LIBS"; then say "solve_mip: linked HiGHS from $P/$L ($LIBS)"; return 0; fi
        done
    done
    return 1
}
route_a() {
    for P in /usr/local /usr /opt/highs /opt/HiGHS; do link_prefix "$P" && return 0; done
    if pkg-config --exists highs 2>/dev/null; then
        try_link "$(pkg-config --cflags highs) -I$(pkg-config --variable=includedir highs)/.." "$(pkg-config --libs highs) -lpthread -ldl" &&
            { say "solve_mip: linked HiGHS via pkg-config"; return 0; }
    fi
    # build HiGHS from source (static, C++ library only) under /solution
    if command -v git > /dev/null && command -v cmake > /dev/null; then
        say "HiGHS not found: building v1.15.1 from source"
        T0=$(date +%s)
        rm -rf highs-src highs-build
        if timeout 300 git clone -q --depth 1 --branch v1.15.1 https://github.com/ERGO-Code/HiGHS.git highs-src >> "$LOG" 2>&1 &&
            timeout 900 cmake -S highs-src -B highs-build -DCMAKE_BUILD_TYPE=Release -DBUILD_SHARED_LIBS=OFF \
                -DBUILD_TESTING=OFF -DBUILD_EXAMPLES=OFF -DBUILD_CXX_EXE=OFF -DZLIB=OFF \
                -DCMAKE_INSTALL_PREFIX="$HERE/highs-local" >> "$LOG" 2>&1 &&
            timeout 1200 cmake --build highs-build -j"$NPROC" >> "$LOG" 2>&1 &&
            cmake --install highs-build >> "$LOG" 2>&1; then
            say "HiGHS built in $(( $(date +%s) - T0 ))s"
            rm -rf highs-src highs-build
            link_prefix "$HERE/highs-local" && return 0
        else
            say "HiGHS source build failed after $(( $(date +%s) - T0 ))s"
        fi
        rm -rf highs-src highs-build
    fi
    return 1
}
route_b() {
    command -v python3 > /dev/null || return 1
    rm -rf .venv
    python3 -m venv .venv >> "$LOG" 2>&1 || return 1
    .venv/bin/pip install -q highspy numpy >> "$LOG" 2>&1 || return 1
    .venv/bin/python -c "import highspy, numpy" >> "$LOG" 2>&1 || return 1
    say "route B: .venv with highspy ready"
}
route_a || say "route A unavailable"
if [ ! -x solve_mip ]; then
    route_b || { say "route B unavailable"; rm -rf .venv; }
fi
exit 0
