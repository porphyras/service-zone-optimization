// Service Zone Optimization: simulated annealing over site->office assignment.
// Reads instance.json, writes solution.json (both in cwd).
// Optional argv[1]: time limit in seconds; argv[2]: random seed.
#include <algorithm>
#include <bitset>
#include <set>
#include <chrono>
#include <climits>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <functional>
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <random>
#include <sstream>
#include <string>
#include <tuple>
#include <thread>
#include <vector>
#include <numeric>

#include <poll.h>
#include <signal.h>
#include <sys/resource.h>
#include <sys/wait.h>
#include <unistd.h>
#ifdef __linux__
#include <sched.h>
#endif

#ifdef USE_HIGHS
#include "Highs.h"
#endif

using namespace std;

// ---------------------------------------------------------------- JSON
struct J {
    enum T { NUL, NUM, STR, ARR, OBJ, BOOL } t = NUL;
    double num = 0;
    string str;
    vector<J> arr;
    vector<double> nv;  // an array of numbers only: its values (arr stays empty); see at()
    bool isNum = false;
    vector<pair<string, J>> obj;
    const J& operator[](const char* k) const {
        for (auto& kv : obj)
            if (kv.first == k) return kv.second;
        static J nul;
        return nul;
    }
    const J& operator[](size_t i) const { return arr[i]; }
    size_t size() const { return isNum ? nv.size() : arr.size(); }
    double at(size_t i) const { return isNum ? nv[i] : arr[i].num; }  // element i of an array of numbers
};

// strtod with a fast exact path: up to 15 significant digits and a decimal exponent within
// +-22 make the mantissa and the power of ten exact doubles, so one correctly rounded multiply or
// divide gives the correctly rounded value, which is what strtod returns (Clinger's fast path)
static double parseNum(const char* p, char** end) {
    static const double p10[23] = {1e0, 1e1, 1e2, 1e3, 1e4, 1e5, 1e6, 1e7, 1e8, 1e9, 1e10, 1e11,
                                   1e12, 1e13, 1e14, 1e15, 1e16, 1e17, 1e18, 1e19, 1e20, 1e21, 1e22};
    const char* q = p;
    bool neg = false;
    if (*q == '-') neg = true, q++;
    uint64_t m = 0;
    int digits = 0, e10 = 0;
    bool any = false;
    while (*q >= '0' && *q <= '9') {
        any = true;
        if (m == 0 && *q == '0') {
            q++;
            continue;
        }
        if (digits >= 18) return strtod(p, end);
        m = m * 10 + (uint64_t)(*q - '0'), digits++, q++;
    }
    if (*q == '.') {
        q++;
        while (*q >= '0' && *q <= '9') {
            any = true;
            if (m == 0 && *q == '0') {
                e10--, q++;
                continue;
            }
            if (digits >= 18) return strtod(p, end);
            m = m * 10 + (uint64_t)(*q - '0'), digits++, e10--, q++;
        }
    }
    if (!any) return strtod(p, end);
    if (*q == 'e' || *q == 'E') {
        const char* r = q + 1;
        bool en = false;
        if (*r == '+' || *r == '-') en = *r == '-', r++;
        if (!(*r >= '0' && *r <= '9')) return strtod(p, end);
        int x = 0;
        while (*r >= '0' && *r <= '9') {
            if (x > 10000) return strtod(p, end);
            x = x * 10 + (*r - '0'), r++;
        }
        e10 += en ? -x : x;
        q = r;
    }
    if (m == 0) {
        *end = (char*)q;
        return neg ? -0.0 : 0.0;
    }
    if (digits > 15 || e10 < -22 || e10 > 22) return strtod(p, end);
    double v = (double)m;
    v = e10 >= 0 ? v * p10[e10] : v / p10[-e10];
    *end = (char*)q;
    return neg ? -v : v;
}

struct Parser {
    const char* p;
    void ws() {
        while (*p == ' ' || *p == '\n' || *p == '\r' || *p == '\t') p++;
    }
    string parseStr() {
        string s;
        p++;
        while (*p && *p != '"') {
            if (*p == '\\') {
                p++;
                if (*p == 'u') {
                    p += 5;
                    s += '?';
                    continue;
                }
            }
            s += *p++;
        }
        p++;
        return s;
    }
    J parse() {
        ws();
        J v;
        if (*p == '{') {
            v.t = J::OBJ;
            p++;
            ws();
            if (*p == '}') {
                p++;
                return v;
            }
            while (true) {
                ws();
                string k = parseStr();
                ws();
                p++;  // ':'
                v.obj.emplace_back(k, parse());
                ws();
                if (*p == ',') {
                    p++;
                    continue;
                }
                p++;  // '}'
                break;
            }
        } else if (*p == '[') {
            v.t = J::ARR;
            p++;
            ws();
            if (*p == ']') {
                p++;
                return v;
            }
            // numbers only (the distance rows, task and skill lists): kept flat, same strtod values
            auto numStart = [](char c) { return c == '-' || c == '+' || c == '.' || (c >= '0' && c <= '9'); };
            if (numStart(*p)) {
                v.isNum = true;
                while (true) {
                    char* e;
                    v.nv.push_back(parseNum(p, &e));
                    p = e;
                    ws();
                    if (*p != ',') break;
                    p++;
                    ws();
                    if (!numStart(*p)) {  // not numbers only after all: back to the general form
                        for (double x : v.nv) {
                            J q;
                            q.t = J::NUM, q.num = x;
                            v.arr.push_back(std::move(q));
                        }
                        v.nv.clear(), v.isNum = false;
                        break;
                    }
                }
                if (v.isNum) {
                    p++;  // ']'
                    return v;
                }
            }
            while (true) {
                v.arr.push_back(parse());
                ws();
                if (*p == ',') {
                    p++;
                    continue;
                }
                p++;  // ']'
                break;
            }
        } else if (*p == '"') {
            v.t = J::STR;
            v.str = parseStr();
        } else if (*p == 't' || *p == 'f') {
            v.t = J::BOOL;
            v.num = (*p == 't');
            p += (*p == 't') ? 4 : 5;
        } else if (*p == 'n') {
            p += 4;
        } else {
            v.t = J::NUM;
            char* e;
            v.num = parseNum(p, &e);
            p = e;
        }
        return v;
    }
};

// ---------------------------------------------------------------- data
int n, K, W, NS, NP;  // sites, offices, workers, skills, points (sites + offices)
vector<double> px, py;  // point coords: [0,n) sites, [n,n+K) offices
vector<double> rew, ocost;
vector<int> maxSize, ntask;
const int MAXSK = 256;
typedef bitset<MAXSK> Mask;  // skill set (skills renumbered compactly)
vector<Mask> smask;          // skills needed by site
vector<vector<double>> dist;  // dist[o][s]
// the same values site-major (distT[s * K + o]) when not too large: loops over the offices of one
// site read one cache line per 8 offices instead of one per office
vector<double> distT;
inline double distSO(int o, int s) { return distT.empty() ? dist[o][s] : distT[(size_t)s * K + o]; }
vector<Mask> wmask;           // skills of worker
int A;
double alpha;
double EPS;
bool singleSkillWorkers = true;
vector<int> availSkill;  // workers per skill (single-skill case)
// Multi-skill workers are solved through one primary skill per worker (wmask) for the counting
// model, while the annealer keeps an explicit assignment of real workers (realW) to offices,
// so one worker may cover several skills of its office ("native" worker mode).
bool nativeW = false;
vector<Mask> realW;   // real skill sets (relevant skills only)
vector<vector<int>> skW;  // native mode: per skill, the workers having it
Mask anyW;                // native mode: skills some worker has
int AS = 0;           // length of an assignment vector: n sites (+ W workers in native mode)

mt19937_64 rng(12345);
inline double urand() { return (rng() >> 11) * (1.0 / 9007199254740992.0); }
inline int irand(int m) { return (int)(rng() % (uint64_t)m); }

chrono::steady_clock::time_point T0;
double lsCutoff = 1e300;  // r29s level scans stop past this real time since the start (0.6 x the time limit, set in main)
chrono::system_clock::time_point T0w;  // wall clock at the start (see elapsed)
static const bool szDebug = false;
// r43: the r37 structure phase ran (equal-load regime, loose window): the regime samples are skipped
static bool r37Fired = false;
double elapsed() {
    double m = chrono::duration<double>(chrono::steady_clock::now() - T0).count();
    // the judge may time the run by the wall clock: on a VM under load the monotonic clock can run
    // slow (WSL2/Hyper-V: 3-5 %) while the wall clock is stepped forward to the host's every ~30 s;
    // follow the wall clock when it is ahead (a step of more than 30 s is a clock reset, ignored)
    double w = chrono::duration<double>(chrono::system_clock::now() - T0w).count();
    return w > m && w < m + 30 ? w : m;
}

// ---------------------------------------------------------------- geometry
inline double cross(int o, int a, int b) {
    return (px[a] - px[o]) * (py[b] - py[o]) - (py[a] - py[o]) * (px[b] - px[o]);
}

// Convex hull (CCW, strictly convex vertices only) of the given point ids.
vector<int> skOff, skLst;  // per site: its skills (CSR), from smask
void buildSkillLists() {
    skOff.assign(n + 1, 0), skLst.clear();
    for (int s = 0; s < n; s++) {
        for (int k = 0; k < NS; k++)
            if (smask[s][k]) skLst.push_back(k);
        skOff[s + 1] = skLst.size();
    }
}
// prank[p]: rank of point p in (x, y) order, equal for equal coordinates (built once after reading)
vector<int> prank;
void buildRanks() {
    vector<int> ord(NP);
    for (int p = 0; p < NP; p++) ord[p] = p;
    sort(ord.begin(), ord.end(), [](int a, int b) { return px[a] < px[b] || (px[a] == px[b] && py[a] < py[b]); });
    prank.assign(NP, 0);
    for (int i = 1; i < NP; i++) {
        int a = ord[i - 1], b = ord[i];
        prank[b] = prank[a] + (px[a] != px[b] || py[a] != py[b]);
    }
}
inline uint64_t pkey(int p) { return (uint64_t)(uint32_t)prank[p] << 32 | (uint32_t)p; }
vector<int> siteKeyOrder;  // the sites sorted by pkey (built once): per-zone key lists come out sorted
void buildSiteKeyOrder() {
    vector<uint64_t> k(n);
    for (int s = 0; s < n; s++) k[s] = pkey(s);
    sort(k.begin(), k.end());
    siteKeyOrder.resize(n);
    for (int s = 0; s < n; s++) siteKeyOrder[s] = (int)(uint32_t)k[s];
}
void hullSorted(vector<int>& pts, vector<int>& out);
void buildHull(vector<int>& pts, vector<int>& out) {
    // sort by (x, y), equal coordinates by id: packed (rank, id) keys (rank = position in (x, y) order)
    {
        static vector<uint64_t> keys;
        size_t m0 = pts.size();
        keys.resize(m0);
        for (size_t i = 0; i < m0; i++) keys[i] = pkey(pts[i]);
        sort(keys.begin(), keys.end());
        for (size_t i = 0; i < m0; i++) pts[i] = (int)(uint32_t)keys[i];
    }
    hullSorted(pts, out);
}
// pts sorted by (rank, id)
void hullSorted(vector<int>& pts, vector<int>& out) {
    out.clear();
    // dedupe identical coordinates, keeping local coordinate copies of the kept points
    static vector<double> hx, hy;
    if (hx.size() < pts.size()) hx.resize(pts.size()), hy.resize(pts.size());
    double* __restrict X = hx.data();
    double* __restrict Y = hy.data();
    int m = 0;
    for (size_t i = 0; i < pts.size(); i++) {
        int p = pts[i];
        double x = px[p], y = py[p];
        if (m == 0 || x != X[m - 1] || y != Y[m - 1]) pts[m] = p, X[m] = x, Y[m] = y, m++;
    }
    pts.resize(m);
    if (m <= 2) {
        out = pts;
        return;
    }
    // monotone chain; the stack keeps the coordinates of its points (same cross products as cross())
    static vector<double> sx, sy;
    static vector<int> hi;
    if ((int)hi.size() < 2 * m) hi.resize(2 * m), sx.resize(2 * m), sy.resize(2 * m);
    int* __restrict H = hi.data();
    double* __restrict SX = sx.data();
    double* __restrict SY = sy.data();
    int k = 0;
    for (int i = 0; i < m; i++) {
        const double bx = X[i], by = Y[i];
        while (k >= 2 && (SX[k - 1] - SX[k - 2]) * (by - SY[k - 2]) - (SY[k - 1] - SY[k - 2]) * (bx - SX[k - 2]) <= 0) k--;
        H[k] = i, SX[k] = bx, SY[k] = by, k++;
    }
    for (int i = m - 2, t = k + 1; i >= 0; i--) {
        const double bx = X[i], by = Y[i];
        while (k >= t && (SX[k - 1] - SX[k - 2]) * (by - SY[k - 2]) - (SY[k - 1] - SY[k - 2]) * (bx - SX[k - 2]) <= 0) k--;
        H[k] = i, SX[k] = bx, SY[k] = by, k++;
    }
    out.resize(k - 1);
    for (int i = 0; i < k - 1; i++) out[i] = pts[H[i]];
}

struct Hull {
    vector<int> v;  // vertex ids
    double x0, x1, y0, y1;
    void bbox() {
        x0 = y0 = 1e300;
        x1 = y1 = -1e300;
        for (int i : v) {
            x0 = min(x0, px[i]);
            x1 = max(x1, px[i]);
            y0 = min(y0, py[i]);
            y1 = max(y1, py[i]);
        }
        x0 -= EPS;
        y0 -= EPS;
        x1 += EPS;
        y1 += EPS;
    }
    // conservative "covers": true if point is inside or within EPS of the hull
    bool covers(int p) const {
        double x = px[p], y = py[p];
        if (x < x0 || x > x1 || y < y0 || y > y1) return false;
        int h = v.size();
        if (h == 1) return hypot(x - px[v[0]], y - py[v[0]]) <= EPS;
        if (h == 2) {
            double ax = px[v[0]], ay = py[v[0]], bx = px[v[1]], by = py[v[1]];
            double dx = bx - ax, dy = by - ay, L2 = dx * dx + dy * dy;
            double t = ((x - ax) * dx + (y - ay) * dy) / L2;
            t = max(0.0, min(1.0, t));
            return hypot(x - ax - t * dx, y - ay - t * dy) <= EPS;
        }
        for (int i = 0; i < h; i++) {
            int a = v[i], b = v[(i + 1) % h];
            double dx = px[b] - px[a], dy = py[b] - py[a];
            double c = dx * (y - py[a]) - dy * (x - px[a]);
            if (c < -EPS * sqrt(dx * dx + dy * dy)) return false;
        }
        return true;
    }
};

// ---------------------------------------------------------------- state
struct State {
    vector<int> asg;               // site -> office or -1
    vector<vector<int>> mem;       // office -> sites
    vector<int> pos;               // index of site within mem
    vector<int> cnt, tsum;         // per office
    vector<vector<int>> skc;       // office x skill -> count of sites needing skill
    vector<Mask> omask;            // required skills per office
    vector<Hull> hull;             // per office (includes office point)
    vector<vector<int>> cov;       // per office: covered point ids
    vector<int> cover;             // per point: number of office hulls covering it
    vector<int> ownS;              // per point: sum of the offices covering it (= the zone when cover is 1)
    vector<vector<uint64_t>> skey; // per office: its sites' keys pkey(s), sorted
    int multiCov = 0;              // points covered by two or more zones
    vector<int> need;              // per skill: number of offices requiring it
    vector<vector<int>> owk;       // native worker mode: office -> workers (asg[n + w] = office)
    struct Ext {                   // up to 5 extreme (value, office) pairs among nonempty offices
        int n = 0, v[5], o[5];
    } loC, hiC, loT, hiT;
    double base;                   // sum over assigned (reward - dist) - cost of nonempty offices
    double openCost;               // cost of nonempty offices
};

State S;
vector<int> bestAsg;
vector<int> validAsg;  // last best that passed validateFull (safe fallback)
double validObj = 0;
double bestObj = -1e300;
bool haveBest = false;

void computeHullOf(int o, const vector<int>& sites, Hull& h, vector<int>& tmp) {
    tmp.assign(sites.begin(), sites.end());
    tmp.push_back(n + o);
    buildHull(tmp, h.v);
    h.bbox();
}
// Uniform grid over all points, to visit only points inside a hull's bounding box.
// Stored contiguously (CSR): cell c holds gPts[gStart[c] .. gStart[c + 1]) in increasing point id,
// with their coordinates in gXs / gYs (sequential access in the hot scans).
int GW = 1;
double gx0, gy0, gcw, gch;
double gSlackX = 0, gSlackY = 0;  // cell rectangles are widened by this (rounding of point -> cell)
vector<int> gStart, gPts;
vector<double> gXs, gYs;
void buildGrid() {
    GW = max(1, (int)sqrt(NP / 4.0));
    double x0 = 1e300, x1 = -1e300, y0 = 1e300, y1 = -1e300;
    for (int p = 0; p < NP; p++) x0 = min(x0, px[p]), x1 = max(x1, px[p]), y0 = min(y0, py[p]), y1 = max(y1, py[p]);
    gx0 = x0, gy0 = y0;
    gcw = x1 > x0 ? (x1 - x0) / GW : 1.0;
    gch = y1 > y0 ? (y1 - y0) / GW : 1.0;
    double mag = NP ? max(max(fabs(x0), fabs(x1)), max(fabs(y0), fabs(y1))) : 0.0;
    gSlackX = 1e-6 * gcw + 1e-12 * mag;
    gSlackY = 1e-6 * gch + 1e-12 * mag;
    vector<int> cellOf(NP);
    gStart.assign(GW * GW + 1, 0);
    for (int p = 0; p < NP; p++) {
        int cx = min(GW - 1, max(0, (int)((px[p] - gx0) / gcw)));
        int cy = min(GW - 1, max(0, (int)((py[p] - gy0) / gch)));
        cellOf[p] = cy * GW + cx;
        gStart[cellOf[p] + 1]++;
    }
    for (int c = 0; c < GW * GW; c++) gStart[c + 1] += gStart[c];
    gPts.assign(NP, 0), gXs.assign(NP, 0), gYs.assign(NP, 0);
    vector<int> fill(gStart.begin(), gStart.end() - 1);
    for (int p = 0; p < NP; p++) {
        int k = fill[cellOf[p]]++;
        gPts[k] = p, gXs[k] = px[p], gYs[k] = py[p];
    }
}
// Calls f(p) for every point p with h.covers(p), in grid order (rows, then cells, then point id);
// stops when f returns false. Same calls as testing every point of the bounding box with covers.
// Each grid row is cut into SB horizontal sub-bands; per sub-band and edge the corner values of the
// affine edge function give x bounds: beyond an "out" bound some edge fails by over 2x its EPS
// tolerance (point not covered), within the "in" bounds every edge holds with half its tolerance
// left (point covered). Cells entirely out are skipped, cells entirely in are taken whole, and only
// points between the bounds get the exact edge test. The margins dwarf the rounding of the bounds.
struct EdgeTab {
    vector<double> ax, ay, dx, dy, thr, inv, cb;
} etab;
const int SB = 4;
// Optional priority box (pbx0..pby1, bounds in coordinates): the cells overlapping it are visited
// first, then all the others. Same set of calls, another order: only for callers that do not
// depend on the order (a stop means rejection, and the collected coverage is order-free).
template <class F>
inline bool forEachInBox(const Hull& h, F f, double pbx0 = 1, double pbx1 = 0, double pby0 = 0, double pby1 = 0) {  // f returns false to stop
    auto cellOf = [](double v) { return (int)min((double)(GW - 1), max(0.0, floor(v))); };
    int cx0 = cellOf((h.x0 - gx0) / gcw), cx1 = cellOf((h.x1 - gx0) / gcw);
    int cy0 = cellOf((h.y0 - gy0) / gch), cy1 = cellOf((h.y1 - gy0) / gch);
    const int hs = h.v.size();
    // priority cells [qx0, qx1] x [qy0, qy1] (clipped to the box; empty when not given)
    int qx0 = 1, qx1 = 0, qy0 = 1, qy1 = 0;
    if (pbx0 <= pbx1 && hs >= 3) {
        qx0 = max(cx0, cellOf((pbx0 - gx0) / gcw)), qx1 = min(cx1, cellOf((pbx1 - gx0) / gcw));
        qy0 = max(cy0, cellOf((pby0 - gy0) / gch)), qy1 = min(cy1, cellOf((pby1 - gy0) / gch));
        if (qx0 == cx0 && qx1 == cx1 && qy0 == cy0 && qy1 == cy1) qx0 = 1, qx1 = 0;  // the whole box: plain order
        if (qx0 > qx1 || qy0 > qy1) qx0 = 1, qx1 = 0, qy0 = 1, qy1 = 0;
    }
    if (hs < 3) {
        for (int cy = cy0; cy <= cy1; cy++)
            for (int cx = cx0; cx <= cx1; cx++) {
                int c = cy * GW + cx;
                for (int k = gStart[c]; k < gStart[c + 1]; k++)
                    if (h.covers(gPts[k]) && !f(gPts[k])) return false;
            }
        return true;
    }
    if ((int)etab.ax.size() < hs) {
        etab.ax.resize(hs), etab.ay.resize(hs), etab.dx.resize(hs), etab.dy.resize(hs), etab.thr.resize(hs), etab.inv.resize(hs);
        etab.cb.resize((size_t)hs * (SB + 1));
    }
    double* __restrict eax = etab.ax.data();
    double* __restrict eay = etab.ay.data();
    double* __restrict edx = etab.dx.data();
    double* __restrict edy = etab.dy.data();
    double* __restrict ethr = etab.thr.data();
    double* __restrict einv = etab.inv.data();
    double* __restrict ecb = etab.cb.data();
    for (int i = 0; i < hs; i++) {
        int a = h.v[i], b = h.v[i + 1 < hs ? i + 1 : 0];
        double dx = px[b] - px[a], dy = py[b] - py[a];
        eax[i] = px[a], eay[i] = py[a], edx[i] = dx, edy[i] = dy;
        ethr[i] = -EPS * sqrt(dx * dx + dy * dy);
        einv[i] = dy != 0 ? 1.0 / dy : 0.0;
    }
    const double bx0 = h.x0, bx1 = h.x1, by0 = h.y0, by1 = h.y1;
    double Yb[SB + 1], Lo[SB], Ro[SB], ALo[SB], AHi[SB];
    // pass 0: the priority cells; pass 1: everything else
    const bool prio = qx0 <= qx1;
    for (int pass = prio ? 0 : 1; pass < 2; pass++)
    for (int cy = pass == 0 ? qy0 : cy0, cyEnd = pass == 0 ? qy1 : cy1; cy <= cyEnd; cy++) {
        const bool skipRow = prio && pass == 1 && cy >= qy0 && cy <= qy1;  // its cells [qx0, qx1] were visited
        double Ylo = gy0 + cy * gch - gSlackY, Yhi = gy0 + (cy + 1) * gch + gSlackY;
        for (int t = 0; t < SB; t++) Yb[t] = Ylo + (Yhi - Ylo) * t / SB;
        Yb[SB] = Yhi;
        for (int i = 0; i < hs; i++)
            for (int t = 0; t <= SB; t++) ecb[i * (SB + 1) + t] = edx[i] * (Yb[t] - eay[i]);
        // per sub-band bounds; row aggregates for whole cells
        double rLo = 1e300, rRo = -1e300, rALo = -1e300, rAHi = 1e300;
        bool anyIn = true, allOut = true;
        for (int j = 0; j < SB; j++) {
            double Lout = -1e300, Rout = 1e300, Lin = -1e300, Rin = 1e300;
            bool out = false, in = Yb[j] >= by0 && Yb[j + 1] <= by1;
            for (int i = 0; i < hs; i++) {
                double c0 = ecb[i * (SB + 1) + j], c1 = ecb[i * (SB + 1) + j + 1];
                double cMax = max(c0, c1), cMin = min(c0, c1);
                double kout = 2 * ethr[i], kin = 0.5 * ethr[i];
                double dy = edy[i];
                if (dy > 0) {
                    Rout = min(Rout, eax[i] + (cMax - kout) * einv[i]);
                    Rin = min(Rin, eax[i] + (cMin - kin) * einv[i]);
                } else if (dy < 0) {
                    Lout = max(Lout, eax[i] + (cMax - kout) * einv[i]);
                    Lin = max(Lin, eax[i] + (cMin - kin) * einv[i]);
                } else {
                    if (cMax < kout) out = true;
                    if (cMin < kin) in = false;
                }
            }
            if (out) Lout = 1e300, Rout = -1e300;
            Lo[j] = Lout, Ro[j] = Rout;
            ALo[j] = in ? max(Lin, bx0) : 1e300;
            AHi[j] = in ? min(Rin, bx1) : -1e300;
            rLo = min(rLo, Lout), rRo = max(rRo, Rout);
            rALo = max(rALo, ALo[j]), rAHi = min(rAHi, AHi[j]);
            allOut = allOut && out;
            anyIn = anyIn && in;
        }
        if (allOut) continue;
        const double sbScale = SB / (Yhi - Ylo);
        for (int cx = pass == 0 ? qx0 : cx0, cxEnd = pass == 0 ? qx1 : cx1; cx <= cxEnd; cx++) {
            if (skipRow && cx == qx0) {
                cx = qx1;
                continue;
            }
            double Xlo = gx0 + cx * gcw - gSlackX, Xhi = gx0 + (cx + 1) * gcw + gSlackX;
            if (Xlo > rRo || Xhi < rLo) continue;
            int c = cy * GW + cx;
            int k0 = gStart[c], k1 = gStart[c + 1];
            if (anyIn && Xlo >= rALo && Xhi <= rAHi) {
                for (int k = k0; k < k1; k++)
                    if (!f(gPts[k])) return false;
                continue;
            }
            for (int k = k0; k < k1; k++) {
                double x = gXs[k], y = gYs[k];
                int j = (int)((y - Ylo) * sbScale);
                j = j < 0 ? 0 : j >= SB ? SB - 1 : j;
                if (y >= Yb[j] && y <= Yb[j + 1]) {
                    if (x > Ro[j] || x < Lo[j]) continue;  // some edge fails clearly (or bOut[j])
                    if (x >= ALo[j] && x <= AHi[j]) {      // every edge holds clearly, inside the bbox
                        if (!f(gPts[k])) return false;
                        continue;
                    }
                }
                if (x < bx0 || x > bx1 || y < by0 || y > by1) continue;
                bool in = true;
                for (int i = 0; i < hs; i++)
                    if (edx[i] * (y - eay[i]) - edy[i] * (x - eax[i]) < ethr[i]) {
                        in = false;
                        break;
                    }
                if (in && !f(gPts[k])) return false;
            }
        }
    }
    return true;
}
void computeCov(const Hull& h, vector<int>& out) {
    out.clear();
    forEachInBox(h, [&](int p) {
        out.push_back(p);
        return true;
    });
}

// worker feasibility for given required masks of open offices
vector<int> assignWorkersResult;
bool assignWorkers(const vector<Mask>& masks, bool wantResult) {
    if (singleSkillWorkers && !wantResult) {
        static vector<int> need;
        need.assign(NS, 0);
        for (const Mask& m : masks)
            for (int s = 0; s < NS; s++)
                if (m[s])
                    if (++need[s] > availSkill[s]) return false;
        return true;
    }
    // backtracking: for each office cover each needed skill
    int nm = masks.size();
    vector<int> used(W, -1);
    vector<Mask> covered(nm);
    long long budget = wantResult ? (1LL << 60) : 20000;
    // visit offices with the most required skills first (deterministic for a given mask list)
    vector<int> ord(nm);
    for (int i = 0; i < nm; i++) ord[i] = i;
    stable_sort(ord.begin(), ord.end(), [&](int a, int b) { return masks[a].count() > masks[b].count(); });
    // depth-first search with an explicit stack (the depth can reach sum|mask| + #offices, too deep
    // for the call stack on big inputs): a frame = one office still missing skill s, trying workers
    struct Frame {
        int pi, s, w;  // w = worker currently tried (-1 = none yet)
        Mask prev;     // covered[ord[pi]] before w joined
    };
    vector<Frame> stk;
    bool ok = false;
    int pi = 0;
    bool descend = true;  // true: enter search level pi; false: try the next worker of the top frame
    while (true) {
        if (descend) {
            if (--budget < 0) break;
            if (pi == nm) {
                ok = true;
                break;
            }
            int oi = ord[pi];
            Mask rem = masks[oi] & ~covered[oi];
            if (rem.none()) {
                pi++;
                continue;
            }
            int s = 0;
            while (!rem[s]) s++;
            stk.push_back({pi, s, -1, covered[oi]});
            descend = false;
        }
        if (stk.empty()) break;
        Frame& F = stk.back();
        int oi = ord[F.pi];
        int w = 0;
        if (F.w >= 0) {  // the previous choice failed: undo it
            covered[oi] = F.prev;
            used[F.w] = -1;
            w = F.w + 1;
        }
        while (w < W && (used[w] != -1 || !wmask[w][F.s])) w++;
        if (w >= W) {
            stk.pop_back();
            continue;
        }
        F.w = w;
        used[w] = oi;
        covered[oi] |= wmask[w];
        pi = F.pi;
        descend = true;
    }
    if (ok && wantResult) assignWorkersResult = used;
    return ok;
}

void pushExt(State::Ext& e, int v, int o, bool lo) {
    int i;
    if (e.n < 5) {
        i = e.n++;
    } else {
        if (lo ? v >= e.v[4] : v <= e.v[4]) return;
        i = 4;
    }
    while (i > 0 && (lo ? v < e.v[i - 1] : v > e.v[i - 1])) {
        e.v[i] = e.v[i - 1], e.o[i] = e.o[i - 1];
        i--;
    }
    e.v[i] = v, e.o[i] = o;
}
void refreshExt(State& st) {
    st.loC.n = st.hiC.n = st.loT.n = st.hiT.n = 0;
    for (int o = 0; o < K; o++) {
        if (st.cnt[o] == 0) continue;
        pushExt(st.loC, st.cnt[o], o, true);
        pushExt(st.hiC, st.cnt[o], o, false);
        pushExt(st.loT, st.tsum[o], o, true);
        pushExt(st.hiT, st.tsum[o], o, false);
    }
}

void initState(State& st) {
    st.asg.assign(AS, -1);
    st.owk.assign(nativeW ? K : 0, {});
    st.mem.assign(K, {});
    st.skey.assign(K, {});
    st.pos.assign(n, -1);
    st.cnt.assign(K, 0);
    st.tsum.assign(K, 0);
    st.skc.assign(K, vector<int>(NS, 0));
    st.omask.assign(K, 0);
    st.hull.assign(K, Hull());
    st.cov.assign(K, {});
    st.cover.assign(NP, 0);
    st.ownS.assign(NP, 0);
    st.multiCov = 0;
    st.need.assign(NS, 0);
    st.base = 0;
    st.openCost = 0;
    vector<int> tmp;
    for (int o = 0; o < K; o++) {
        computeHullOf(o, {}, st.hull[o], tmp);
        st.cov[o].clear();  // an unopened office has no zone
    }
    refreshExt(st);
}

// evaluation of imbalance terms over nonempty offices with overrides
struct Ov {
    int o, cnt, tsum;
};
inline void extremes(const State& st, const Ov* ov, int nov, int& cmin, int& cmax, int& tmin, int& tmax) {
    cmin = tmin = INT32_MAX;
    cmax = tmax = INT32_MIN;
    for (int o = 0; o < K; o++) {
        int c = st.cnt[o], t = st.tsum[o];
        for (int i = 0; i < nov; i++)
            if (ov[i].o == o) c = ov[i].cnt, t = ov[i].tsum;
        if (c == 0) continue;
        cmin = min(cmin, c);
        cmax = max(cmax, c);
        tmin = min(tmin, t);
        tmax = max(tmax, t);
    }
    if (cmax == INT32_MIN) cmin = cmax = tmin = tmax = 0;
}

double lambdaCnt = 0;  // soft penalty weight for count imbalance beyond A
double wAlpha = 1;     // annealed weight of the task-imbalance term
double wCost = 1;      // annealed weight of office opening costs
// L1 pull of every open office's task load towards a common level (soft runs with a task penalty):
// unlike the range term it moves all zones at once, so the run ends near one level with most sites
double l1Cost = 0;     // cost per task of deviation (0 = off)
double l1Tau = 0;      // target level
inline double l1Dev(int c, int t) { return c > 0 ? fabs(t - l1Tau) : 0.0; }

inline double softTerms(int cmin, int cmax, int tmin, int tmax, double lam) {
    return -wAlpha * alpha * (tmax - tmin) - lam * max(0, cmax - cmin - A);
}

// level-targeted runs: every open office's task load is pulled toward a common level lvTarget
// (with heavy alpha, SA otherwise stays at whatever common level it first reached)
int lvTarget = -1;
double wLv = 0;
inline double lvTerm(int cnt, int t) { return cnt > 0 ? fabs((double)(t - lvTarget)) : 0.0; }

double trueObjective(const State& st) {
    int cmin, cmax, tmin, tmax;
    extremes(st, nullptr, 0, cmin, cmax, tmin, tmax);
    return st.base - alpha * (tmax - tmin);
}
bool countFeasible(const State& st) {
    int cmin, cmax, tmin, tmax;
    extremes(st, nullptr, 0, cmin, cmax, tmin, tmax);
    return cmax - cmin <= A;
}

// Build a full state from an assignment (no feasibility checks).
bool buildWorkers(State& st, const vector<int>& asg);
State fromAsg(const vector<int>& asg) {
    State st;
    initState(st);
    vector<int> tmp;
    for (int s = 0; s < n; s++) {
        int o = asg[s];
        st.asg[s] = o;
        if (o < 0) continue;
        st.pos[s] = st.mem[o].size();
        st.mem[o].push_back(s);
        st.cnt[o]++;
        st.tsum[o] += ntask[s];
        st.base += rew[s] - dist[o][s];
        for (int q = skOff[s]; q < skOff[s + 1]; q++) st.skc[o][skLst[q]]++;
        st.omask[o] |= smask[s];
    }
    // sorted site keys per zone, from the global key order
    for (int o = 0; o < K; o++) st.skey[o].clear(), st.skey[o].reserve(st.cnt[o]);
    for (int s : siteKeyOrder)
        if (asg[s] >= 0) st.skey[asg[s]].push_back(pkey(s));
    st.cover.assign(NP, 0);
    st.ownS.assign(NP, 0);
    st.multiCov = 0;
    for (int o = 0; o < K; o++) {
        if (st.cnt[o] > 0) st.base -= ocost[o], st.openCost += ocost[o];
        // sorted site keys; the hull input is them plus the office (same sorted list as buildHull's)
        auto& sk = st.skey[o];
        {
            uint64_t ok = pkey(n + o);
            tmp.clear();
            size_t i = 0;
            for (; i < sk.size() && sk[i] < ok; i++) tmp.push_back((int)(uint32_t)sk[i]);
            tmp.push_back(n + o);
            for (; i < sk.size(); i++) tmp.push_back((int)(uint32_t)sk[i]);
            hullSorted(tmp, st.hull[o].v);
            st.hull[o].bbox();
        }
        st.cov[o].clear();
        if (st.cnt[o] == 0) continue;  // an unopened office has no zone
        computeCov(st.hull[o], st.cov[o]);
        for (int p : st.cov[o]) {
            if (++st.cover[p] == 2) st.multiCov++;
            st.ownS[p] += o;
        }
    }
    st.need.assign(NS, 0);
    for (int o = 0; o < K; o++)
        for (int k = 0; k < NS; k++)
            if (st.omask[o][k]) st.need[k]++;
    if (nativeW) buildWorkers(st, asg);
    refreshExt(st);
    return st;
}

// fast min/max of counts and task sums over nonempty offices, with overrides for affected offices
inline void fastExtremesGen(const State& st, const Ov* ov, int nov, int& cmin, int& cmax, int& tmin, int& tmax);
inline void fastExtremes(const State& st, const Ov* ov, int nov, int& cmin, int& cmax, int& tmin, int& tmax) {
    if (nov > 4) return fastExtremesGen(st, ov, nov, cmin, cmax, tmin, tmax);
    // same values as fastExtremesGen: per list the first entry of an unaffected office, combined
    // with the overridden values of the affected offices that stay open
    int oa[4] = {-2, -2, -2, -2};
    int oc0 = INT32_MAX, oc1 = INT32_MIN, ot0 = INT32_MAX, ot1 = INT32_MIN;
    for (int a = 0; a < nov; a++) {
        oa[a] = ov[a].o;
        if (ov[a].cnt > 0) {
            oc0 = min(oc0, ov[a].cnt), oc1 = max(oc1, ov[a].cnt);
            ot0 = min(ot0, ov[a].tsum), ot1 = max(ot1, ov[a].tsum);
        }
    }
    auto first = [&](const State::Ext& e, int none) {
        for (int i = 0; i < e.n; i++) {
            int o = e.o[i];
            if (o != oa[0] && o != oa[1] && o != oa[2] && o != oa[3]) return e.v[i];
        }
        return none;
    };
    cmin = min(first(st.loC, INT32_MAX), oc0);
    if (cmin == INT32_MAX) {
        cmin = cmax = tmin = tmax = 0;
        return;
    }
    cmax = max(first(st.hiC, INT32_MIN), oc1);
    tmin = min(first(st.loT, INT32_MAX), ot0);
    tmax = max(first(st.hiT, INT32_MIN), ot1);
}
inline void fastExtremesGen(const State& st, const Ov* ov, int nov, int& cmin, int& cmax, int& tmin, int& tmax) {
    auto pick = [&](const State::Ext& e, bool lo, bool tasks) {
        int best = lo ? INT32_MAX : INT32_MIN;
        for (int i = 0; i < e.n; i++) {
            bool affected = false;
            for (int a = 0; a < nov; a++)
                if (ov[a].o == e.o[i]) affected = true;
            if (!affected) {
                best = e.v[i];
                break;
            }
        }
        for (int a = 0; a < nov; a++)
            if (ov[a].cnt > 0) {
                int v = tasks ? ov[a].tsum : ov[a].cnt;
                best = lo ? min(best, v) : max(best, v);
            }
        return best;
    };
    cmin = pick(st.loC, true, false);
    if (cmin == INT32_MAX) {
        cmin = cmax = tmin = tmax = 0;
        return;
    }
    cmax = pick(st.hiC, false, false);
    tmin = pick(st.loT, true, true);
    tmax = pick(st.hiT, false, true);
}

// ---------------------------------------------------------------- moves
// A change: list of (site, newOffice). Affected offices recomputed.
struct Change {
    int s, from, to;
};

vector<int> tmpPts, tmpPts2;

struct NewGeom {
    int o;
    bool changed;
    Hull h;
    vector<int> cov;
};
NewGeom ng[4];

// Evaluate and (if accepted) apply a change set. Returns true if applied.
bool tcRef = false;  // verification: force the general geometry check

// ---------------------------------------------------------------- native worker mode
// Planned worker moves of one change: tentative office per touched worker.
struct WPlan {
    vector<int> tw, ep, touched;
    int epoch = 0;
    void begin() {
        if ((int)tw.size() < W) tw.assign(W, -1), ep.assign(W, 0);
        ++epoch;
        touched.clear();
    }
    int get(const State& st, int w) const { return ep[w] == epoch ? tw[w] : st.asg[n + w]; }
    void set(int w, int o) {
        if (ep[w] != epoch) ep[w] = epoch, touched.push_back(w);
        tw[w] = o;
    }
} wplan;
void wListOf(const State& st, int o, vector<int>& out) {
    out.clear();
    for (int w : st.owk[o])
        if (wplan.get(st, w) == o) out.push_back(w);
    for (int w : wplan.touched)
        if (wplan.tw[w] == o && st.asg[n + w] != o) out.push_back(w);
}
// Re-plan the workers of the affected offices for their new skill masks: drop workers that became
// redundant, cover missing skills with free workers (most new skills first, least versatile on
// ties), else take a worker from another office that can replace it with a free one.
bool planWorkers(const State& st, const int* aff, const Mask* nm, int naff) {
    wplan.begin();
    static vector<int> lst, lst2;
    for (int a = 0; a < naff; a++) {
        int o = aff[a];
        if (nm[a] == st.omask[o]) continue;
        wListOf(st, o, lst);
        if (nm[a].none()) {
            for (int w : lst) wplan.set(w, -1);
            continue;
        }
        sort(lst.begin(), lst.end(), [&](int x, int y) { return realW[x].count() > realW[y].count(); });
        for (size_t i = 0; i < lst.size(); i++) {
            Mask others;
            for (size_t j = 0; j < lst.size(); j++)
                if (j != i && lst[j] >= 0) others |= realW[lst[j]];
            if ((nm[a] & realW[lst[i]] & ~others).none()) wplan.set(lst[i], -1), lst[i] = -1;
        }
    }
    for (int a = 0; a < naff; a++) {
        int o = aff[a];
        if (nm[a] == st.omask[o] || nm[a].none()) continue;
        wListOf(st, o, lst);
        Mask have;
        for (int w : lst) have |= realW[w];
        Mask miss = nm[a] & ~have;
        while (miss.any()) {
            int k = 0;
            while (!miss[k]) k++;
            // free worker with skill k covering the most missing skills (least versatile on ties)
            int bw = -1, bc = 0, bp = INT32_MAX, mc = miss.count();
            for (int w : skW[k]) {
                if (wplan.get(st, w) != -1) continue;
                int c = (realW[w] & miss).count();
                int pc = realW[w].count();
                if (c > bc || (c == bc && pc < bp)) bc = c, bp = pc, bw = w;
                if (bc == mc && bp == mc) break;  // exact cover of the missing skills
            }
            if (bw >= 0) {
                wplan.set(bw, o);
                miss &= ~realW[bw];
                continue;
            }
            bool ok = false;
            for (int w : skW[k]) {
                if (ok) break;
                int o2 = wplan.get(st, w);
                if (o2 < 0 || o2 == o) continue;
                bool affected = false;
                for (int b = 0; b < naff; b++)
                    if (aff[b] == o2) affected = true;
                if (affected) continue;
                wListOf(st, o2, lst2);
                Mask others;
                for (int x : lst2)
                    if (x != w) others |= realW[x];
                Mask lost = st.omask[o2] & realW[w] & ~others;
                int f = -1, fp = INT32_MAX;
                if (lost.any()) {
                    int k2 = 0;
                    while (!lost[k2]) k2++;
                    for (int x : skW[k2])
                        if (wplan.get(st, x) == -1 && (realW[x] & lost) == lost && (int)realW[x].count() < fp) fp = realW[x].count(), f = x;
                    if (f < 0) continue;
                }
                wplan.set(w, o);
                if (f >= 0) wplan.set(f, o2);
                miss &= ~realW[w];
                ok = true;
            }
            if (!ok) return false;
        }
    }
    return true;
}
void applyWorkerPlan(State& st) {
    for (int w : wplan.touched) {
        int old = st.asg[n + w], nw = wplan.tw[w];
        if (old == nw) continue;
        if (old >= 0) {
            auto& v = st.owk[old];
            for (size_t i = 0; i < v.size(); i++)
                if (v[i] == w) {
                    v[i] = v.back();
                    v.pop_back();
                    break;
                }
        }
        if (nw >= 0) st.owk[nw].push_back(w);
        st.asg[n + w] = nw;
    }
}
// Workers for a state rebuilt from an assignment vector: the stored worker part if it still covers
// every office, else greedy covers (most demanding offices first), else one primary-skill worker
// per needed skill (always feasible when the primary-skill counts allow the masks).
bool buildWorkers(State& st, const vector<int>& asg) {
    auto reset = [&] {
        st.owk.assign(K, {});
        for (int w = 0; w < W; w++) st.asg[n + w] = -1;
    };
    auto coveredAll = [&] {
        for (int o = 0; o < K; o++) {
            if (st.cnt[o] == 0) continue;
            Mask c;
            for (int w : st.owk[o]) c |= realW[w];
            if ((st.omask[o] & ~c).any()) return false;
        }
        return true;
    };
    reset();
    if ((int)asg.size() == AS) {
        for (int w = 0; w < W; w++) {
            int o = asg[n + w];
            if (o >= 0 && o < K && st.cnt[o] > 0 && (realW[w] & st.omask[o]).any()) st.asg[n + w] = o, st.owk[o].push_back(w);
        }
        if (coveredAll()) return true;
        reset();
    }
    vector<int> ord;
    for (int o = 0; o < K; o++)
        if (st.cnt[o] > 0 && st.omask[o].any()) ord.push_back(o);
    sort(ord.begin(), ord.end(), [&](int a, int b) { return st.omask[a].count() > st.omask[b].count(); });
    bool ok = true;
    for (int o : ord) {
        Mask miss = st.omask[o];
        while (miss.any() && ok) {
            int k = 0;
            while (!miss[k]) k++;
            int bw = -1, bc = 0, bp = INT32_MAX, mc = miss.count();
            for (int w : skW[k]) {
                if (st.asg[n + w] != -1) continue;
                int c = (realW[w] & miss).count();
                int pc = realW[w].count();
                if (c > bc || (c == bc && pc < bp)) bc = c, bp = pc, bw = w;
                if (bc == mc && bp == mc) break;
            }
            if (bw < 0) ok = false;
            else st.asg[n + bw] = o, st.owk[o].push_back(bw), miss &= ~realW[bw];
        }
    }
    if (ok) return true;
    reset();
    for (int o : ord)
        for (int k = 0; k < NS; k++) {
            if (!st.omask[o][k]) continue;
            int bw = -1;
            for (int w = 0; w < W && bw < 0; w++)
                if (st.asg[n + w] == -1 && wmask[w][k]) bw = w;
            if (bw < 0) return false;
            st.asg[n + bw] = o, st.owk[o].push_back(bw);
        }
    return true;
}

// skey batching (doUnassign of many sites): removals only mark the site (skDead) and the hull rebuilds skip
// marked keys; doUnassign compacts the touched skey lists once at the end. The resulting state and the random
// stream are bit-identical to erasing key by key (that was O(zone) memmove per site: minutes for a 1e6-site zone)
vector<char> skDead;
bool skDefer = false;
__attribute__((noinline)) static bool tryChangeBody(State& st, const Change* ch, int nch, double T, bool deltaDone) {
    // affected offices
    int aff[8], naff = 0;
    auto addAff = [&](int o) {
        if (o < 0) return;
        for (int i = 0; i < naff; i++)
            if (aff[i] == o) return;
        aff[naff++] = o;
    };
    for (int i = 0; i < nch; i++) {
        addAff(ch[i].from), addAff(ch[i].to);
    }
    Ov ov[8];
    double dBase = 0, dCost = 0;
    bool maskChanged = false;
    // skill count changes as (office slot, skill, delta) over the skills of the moved sites; the new
    // mask of an office is its old mask with exactly these skills re-evaluated (mask = count > 0)
    static vector<int> dA, dK, dD;
    dA.clear(), dK.clear(), dD.clear();
    auto addD = [&](int a, int k, int d) {
        for (size_t q = 0; q < dA.size(); q++)
            if (dA[q] == a && dK[q] == k) {
                dD[q] += d;
                return;
            }
        dA.push_back(a), dK.push_back(k), dD.push_back(d);
    };
    for (int a = 0; a < naff; a++) {
        int o = aff[a];
        ov[a] = {o, st.cnt[o], st.tsum[o]};
    }
    for (int i = 0; i < nch; i++) {
        int s = ch[i].s;
        for (int a = 0; a < naff; a++) {
            if (aff[a] == ch[i].from) {
                ov[a].cnt--;
                ov[a].tsum -= ntask[s];
                dBase -= rew[s] - distSO(aff[a], s);
                for (int q = skOff[s]; q < skOff[s + 1]; q++) addD(a, skLst[q], -1);
            }
            if (aff[a] == ch[i].to) {
                ov[a].cnt++;
                ov[a].tsum += ntask[s];
                dBase += rew[s] - distSO(aff[a], s);
                for (int q = skOff[s]; q < skOff[s + 1]; q++) addD(a, skLst[q], +1);
            }
        }
    }
    Mask newMask[8];
    for (int a = 0; a < naff; a++) {
        int o = aff[a];
        if (ov[a].cnt > maxSize[o]) return false;
        if (st.cnt[o] == 0 && ov[a].cnt > 0) dBase -= ocost[o], dCost += ocost[o];
        if (st.cnt[o] > 0 && ov[a].cnt == 0) dBase += ocost[o], dCost -= ocost[o];
        newMask[a] = st.omask[o];
    }
    for (size_t q = 0; q < dA.size(); q++) {
        if (dD[q] == 0) continue;
        int a = dA[q], k = dK[q];
        newMask[a].set(k, st.skc[aff[a]][k] + dD[q] > 0);
        if (newMask[a][k] != st.omask[aff[a]][k]) maskChanged = true;
    }
    if (!deltaDone) {
    int c0, c1, t0, t1, n0, n1, u0, u1;
    if (st.loC.n > 0) c0 = st.loC.v[0], c1 = st.hiC.v[0], t0 = st.loT.v[0], t1 = st.hiT.v[0];  // = fastExtremes without overrides
    else c0 = c1 = t0 = t1 = 0;
    fastExtremes(st, ov, naff, n0, n1, u0, u1);
    double delta = dBase + (1 - wCost) * dCost + softTerms(n0, n1, u0, u1, lambdaCnt) - softTerms(c0, c1, t0, t1, lambdaCnt);
    if (l1Cost > 0)
        for (int a = 0; a < naff; a++) delta -= l1Cost * (l1Dev(ov[a].cnt, ov[a].tsum) - l1Dev(st.cnt[aff[a]], st.tsum[aff[a]]));
    if (lvTarget >= 0)
        for (int a = 0; a < naff; a++) delta -= wLv * alpha * (lvTerm(ov[a].cnt, ov[a].tsum) - lvTerm(st.cnt[aff[a]], st.tsum[aff[a]]));
    if (delta < 0 && urand() >= exp(delta / T)) return false;
    }
    bool pureRemoval = true;
    for (int i = 0; i < nch; i++)
        if (ch[i].to >= 0) pureRemoval = false;
    if (nativeW) {
        // planned after the geometry checks; here only a cheap necessary condition
        if (maskChanged)
            for (int a = 0; a < naff; a++)
                if ((newMask[a] & ~anyW).any()) return false;
    } else if (pureRemoval) {
        // removing sites can only relax skill requirements
    } else if (maskChanged && singleSkillWorkers) {
        // only skills in the change list can flip (each (slot, skill) appears once there)
        static vector<int> dneed;
        if ((int)dneed.size() < NS) dneed.assign(NS, 0);
        bool okW = true;
        for (size_t q = 0; q < dA.size(); q++) {
            int a = dA[q], k = dK[q];
            dneed[k] += (int)newMask[a][k] - (int)st.omask[aff[a]][k];
        }
        for (size_t q = 0; q < dA.size(); q++) {
            int k = dK[q];
            if (dneed[k] > 0 && st.need[k] + dneed[k] > availSkill[k]) okW = false;
        }
        for (size_t q = 0; q < dA.size(); q++) dneed[dK[q]] = 0;
        if (!okW) return false;
    } else if (maskChanged) {
        static vector<Mask> masks;
        masks.clear();
        for (int o = 0; o < K; o++) {
            int c = st.cnt[o];
            Mask m = st.omask[o];
            for (int a = 0; a < naff; a++)
                if (aff[a] == o) c = ov[a].cnt, m = newMask[a];
            if (c > 0 && m.any()) masks.push_back(m);
        }
        if (!assignWorkers(masks, false)) return false;
    }
    // geometry
    if (st.multiCov > 0 || tcRef) {  // some point lies in two zones: the general check
    // how many of the affected offices currently cover each point
    static vector<int> oldMark, oldEp;
    static int oldEpoch = 0;
    if ((int)oldMark.size() < NP) oldMark.assign(NP, 0), oldEp.assign(NP, 0);
    ++oldEpoch;
    for (int a = 0; a < naff; a++)
        for (int p : st.cov[aff[a]]) {
            if (oldEp[p] != oldEpoch) oldEp[p] = oldEpoch, oldMark[p] = 0;
            oldMark[p]++;
        }
    for (int a = 0; a < naff; a++) {
        int o = aff[a];
        NewGeom& g = ng[a];
        g.o = o;
        if (ov[a].cnt == 0) {  // office closes: its zone disappears
            g.changed = true;
            static vector<int> none;
            computeHullOf(o, none, g.h, tmpPts);
            g.cov.clear();
            continue;
        }
        // does hull change?
        bool needRebuild = false;
        bool grows = false;
        for (int i = 0; i < nch; i++) {
            if (ch[i].from == o) {
                // removing a site that is a hull vertex changes hull
                for (int v : st.hull[o].v)
                    if (v == ch[i].s) needRebuild = true;
            }
            if (ch[i].to == o) grows = true;
        }
        if (st.cnt[o] == 0) needRebuild = true;  // opening office: always build its zone
        if (!needRebuild && !grows) {
            g.changed = false;
            continue;
        }
        if (needRebuild) {
            // members minus removed plus added plus the office, merged in key order (the order
            // buildHull would sort them into), from the sorted site keys
            static vector<uint64_t> addK;
            addK.clear();
            for (int i = 0; i < nch; i++)
                if (ch[i].to == o) addK.push_back(pkey(ch[i].s));
            addK.push_back(pkey(n + o));
            sort(addK.begin(), addK.end());
            tmpPts.clear();
            size_t j = 0;
            for (uint64_t key : st.skey[o]) {
                int s = (int)(uint32_t)key;
                if (skDefer && skDead[s]) continue;  // removed earlier in this doUnassign (compacted at its end)
                bool removed = false;
                for (int i = 0; i < nch; i++)
                    if (ch[i].s == s && ch[i].from == o) removed = true;
                if (removed) continue;
                while (j < addK.size() && addK[j] < key) tmpPts.push_back((int)(uint32_t)addK[j++]);
                tmpPts.push_back(s);
            }
            while (j < addK.size()) tmpPts.push_back((int)(uint32_t)addK[j++]);
            hullSorted(tmpPts, g.h.v);
        } else {
            tmpPts.assign(st.hull[o].v.begin(), st.hull[o].v.end());
            for (int i = 0; i < nch; i++)
                if (ch[i].to == o) tmpPts.push_back(ch[i].s);
            buildHull(tmpPts, g.h.v);
        }
        if (!needRebuild && g.h.v.size() == st.hull[o].v.size()) {
            // unchanged if same vertex set
            bool same = true;
            for (int v : g.h.v)
                if (find(st.hull[o].v.begin(), st.hull[o].v.end(), v) == st.hull[o].v.end()) same = false;
            if (same) {
                g.changed = false;
                continue;
            }
        }
        g.changed = true;
        g.h.bbox();
        // covered points; check conflicts against non-affected offices
        g.cov.clear();
        bool clash = !forEachInBox(g.h, [&](int p) {
            if (st.cover[p] - (oldEp[p] == oldEpoch ? oldMark[p] : 0) > 0) return false;
            g.cov.push_back(p);
            return true;
        });
        if (clash) return false;
    }
    // pairwise conflicts among affected offices (using new or old coverage)
    if (naff >= 2) {
        static vector<int> owner;
        static int ownerEpoch = 0;
        static vector<int> ownerEp;
        if ((int)owner.size() < NP) owner.assign(NP, -1), ownerEp.assign(NP, 0);
        ++ownerEpoch;
        for (int a = 0; a < naff; a++) {
            const vector<int>& cv = ng[a].changed ? ng[a].cov : st.cov[aff[a]];
            for (int p : cv) {
                if (ownerEp[p] == ownerEpoch && owner[p] != a) return false;
                ownerEp[p] = ownerEpoch;
                owner[p] = a;
            }
        }
    }
    } else {
        // zones are disjoint on the points: a point's zone is ownS[p]. Pass 1 builds the new hulls,
        // pass 2 scans the changed ones: a point may not be covered by an unaffected zone, by an
        // affected zone that keeps its coverage, or by the new hull of another changed zone.
        // A site joining a zone while it lies in an unaffected zone: it is outside the zone's old
        // hull (that one covers it not), so it becomes a vertex of the new hull, which covers it:
        // the scan would stop at it. Rejected before any hull is built.
    for (int i = 0; i < nch; i++) {
        int sI = ch[i].s;
        if (ch[i].to < 0 || !st.cover[sI]) continue;
        int w = st.ownS[sI];
        bool affW = false;
        for (int a = 0; a < naff; a++) affW |= aff[a] == w;
        if (!affW) return false;
    }
    for (int a = 0; a < naff; a++) {
        int o = aff[a];
        NewGeom& g = ng[a];
        g.o = o;
        if (ov[a].cnt == 0) {  // office closes: its zone disappears
            g.changed = true;
            static vector<int> none;
            computeHullOf(o, none, g.h, tmpPts);
            g.cov.clear();
            continue;
        }
        // does hull change?
        bool needRebuild = false;
        bool grows = false;
        for (int i = 0; i < nch; i++) {
            if (ch[i].from == o) {
                // removing a site that is a hull vertex changes hull
                for (int v : st.hull[o].v)
                    if (v == ch[i].s) needRebuild = true;
            }
            if (ch[i].to == o) grows = true;
        }
        if (st.cnt[o] == 0) needRebuild = true;  // opening office: always build its zone
        if (!needRebuild && !grows) {
            g.changed = false;
            continue;
        }
        if (needRebuild) {
            // members minus removed plus added plus the office, merged in key order (the order
            // buildHull would sort them into), from the sorted site keys
            static vector<uint64_t> addK;
            addK.clear();
            for (int i = 0; i < nch; i++)
                if (ch[i].to == o) addK.push_back(pkey(ch[i].s));
            addK.push_back(pkey(n + o));
            sort(addK.begin(), addK.end());
            tmpPts.clear();
            size_t j = 0;
            for (uint64_t key : st.skey[o]) {
                int s = (int)(uint32_t)key;
                if (skDefer && skDead[s]) continue;  // removed earlier in this doUnassign (compacted at its end)
                bool removed = false;
                for (int i = 0; i < nch; i++)
                    if (ch[i].s == s && ch[i].from == o) removed = true;
                if (removed) continue;
                while (j < addK.size() && addK[j] < key) tmpPts.push_back((int)(uint32_t)addK[j++]);
                tmpPts.push_back(s);
            }
            while (j < addK.size()) tmpPts.push_back((int)(uint32_t)addK[j++]);
            hullSorted(tmpPts, g.h.v);
        } else {
            tmpPts.assign(st.hull[o].v.begin(), st.hull[o].v.end());
            for (int i = 0; i < nch; i++)
                if (ch[i].to == o) tmpPts.push_back(ch[i].s);
            buildHull(tmpPts, g.h.v);
        }
        if (!needRebuild && g.h.v.size() == st.hull[o].v.size()) {
            // unchanged if same vertex set
            bool same = true;
            for (int v : g.h.v)
                if (find(st.hull[o].v.begin(), st.hull[o].v.end(), v) == st.hull[o].v.end()) same = false;
            if (same) {
                g.changed = false;
                continue;
            }
        }
        g.changed = true;
        g.h.bbox();
    }
        static vector<int> affPos;
        static vector<unsigned> affEp, newEp;
        static unsigned affEpoch = 0, newEpoch = 0;
        if ((int)affPos.size() < K) affPos.assign(K, -1), affEp.assign(K, 0);
        if ((int)newEp.size() < NP) newEp.assign(NP, 0);
        if (++affEpoch == 0) fill(affEp.begin(), affEp.end(), 0), affEpoch = 1;
        if (++newEpoch == 0) fill(newEp.begin(), newEp.end(), 0), newEpoch = 1;
        for (int a = 0; a < naff; a++) affEp[aff[a]] = affEpoch, affPos[aff[a]] = a;
        const int* cover = st.cover.data();
        const int* own = st.ownS.data();
        for (int a = 0; a < naff; a++) {
            NewGeom& g = ng[a];
            if (!g.changed || ov[a].cnt == 0) continue;
            const int o = aff[a];
            g.cov.clear();
            // a clash can only come from the part the zone gains: each added site with its two hull
            // neighbours spans a triangle holding that part, so those cells are scanned first
            double bx0 = 1, bx1 = 0, by0 = 0, by1 = 0;
            const int hs = g.h.v.size();
            for (int i = 0; i < nch; i++) {
                if (ch[i].to != o) continue;
                int s = ch[i].s;
                // an added site inside a zone that keeps its coverage: the scan would stop at it
                if (cover[s]) {
                    int w = own[s];
                    if (w != o && (affEp[w] != affEpoch || !ng[affPos[w]].changed) && g.h.covers(s)) return false;
                }
                for (int j = 0; j < hs; j++)
                    if (g.h.v[j] == s) {
                        int u = g.h.v[j ? j - 1 : hs - 1], v = g.h.v[j + 1 < hs ? j + 1 : 0];
                        double lx = min(px[s], min(px[u], px[v])), hx = max(px[s], max(px[u], px[v]));
                        double ly = min(py[s], min(py[u], py[v])), hy = max(py[s], max(py[u], py[v]));
                        if (bx0 > bx1) bx0 = lx, bx1 = hx, by0 = ly, by1 = hy;
                        else bx0 = min(bx0, lx), bx1 = max(bx1, hx), by0 = min(by0, ly), by1 = max(by1, hy);
                        break;
                    }
            }
            // hull vertices of other zones in that part (they are points of those zones): one inside
            // the new hull is a clash the scan would stop at as well
            if (bx0 <= bx1)
                for (int q = 0; q < K; q++) {
                    if (q == o || st.cnt[q] == 0) continue;
                    const Hull& Hq = st.hull[q];
                    if (Hq.x1 < bx0 || Hq.x0 > bx1 || Hq.y1 < by0 || Hq.y0 > by1) continue;
                    for (int v : Hq.v) {
                        if (px[v] < bx0 || px[v] > bx1 || py[v] < by0 || py[v] > by1 || !cover[v]) continue;
                        int w = own[v];
                        if (w != o && (affEp[w] != affEpoch || !ng[affPos[w]].changed) && g.h.covers(v)) return false;
                    }
                }
            bool ok = forEachInBox(g.h, [&](int p) {
                if (cover[p]) {
                    int w = own[p];
                    if (w != o && (affEp[w] != affEpoch || !ng[affPos[w]].changed)) return false;
                }
                if (newEp[p] == newEpoch) return false;
                newEp[p] = newEpoch;
                g.cov.push_back(p);
                return true;
            }, bx0, bx1, by0, by1);
            if (!ok) return false;
        }
    }
    if (nativeW && maskChanged && !planWorkers(st, aff, newMask, naff)) return false;
    // apply
    if (nativeW && maskChanged) applyWorkerPlan(st);
    for (int i = 0; i < nch; i++) {
        int s = ch[i].s, f = ch[i].from, t = ch[i].to;
        if (f >= 0) {
            auto& m = st.mem[f];
            int ps = st.pos[s];
            m[ps] = m.back();
            st.pos[m[ps]] = ps;
            m.pop_back();
            for (int q = skOff[s]; q < skOff[s + 1]; q++) st.skc[f][skLst[q]]--;
            if (skDefer)
                skDead[s] = 1;
            else {
                auto& sk = st.skey[f];
                auto it = lower_bound(sk.begin(), sk.end(), pkey(s));
                if (it != sk.end() && *it == pkey(s)) sk.erase(it);
            }
        }
        if (t >= 0) {
            st.pos[s] = st.mem[t].size();
            st.mem[t].push_back(s);
            auto& sk = st.skey[t];
            sk.insert(upper_bound(sk.begin(), sk.end(), pkey(s)), pkey(s));
            for (int q = skOff[s]; q < skOff[s + 1]; q++) st.skc[t][skLst[q]]++;
        } else
            st.pos[s] = -1;
        st.asg[s] = t;
    }
    for (size_t q = 0; q < dA.size(); q++) {  // skills outside the change list keep their mask bits
        int a = dA[q], k = dK[q];
        st.need[k] += (int)newMask[a][k] - (int)st.omask[aff[a]][k];
    }
    for (int a = 0; a < naff; a++) {
        int o = aff[a];
        st.cnt[o] = ov[a].cnt;
        st.tsum[o] = ov[a].tsum;
        st.omask[o] = newMask[a];
        if (ng[a].changed) {
            for (int p : st.cov[o]) {
                if (st.cover[p]-- == 2) st.multiCov--;
                st.ownS[p] -= o;
            }
            Hull& H = st.hull[o];
            H.v.swap(ng[a].h.v);
            H.x0 = ng[a].h.x0, H.x1 = ng[a].h.x1, H.y0 = ng[a].h.y0, H.y1 = ng[a].h.y1;
            st.cov[o].swap(ng[a].cov);
            for (int p : st.cov[o]) {
                if (++st.cover[p] == 2) st.multiCov++;
                st.ownS[p] += o;
            }
        }
    }
    st.base += dBase;
    st.openCost += dCost;
    refreshExt(st);
    return true;
}
static bool tryChangeBody(State& st, const Change* ch, int nch, double T, bool deltaDone);
static inline bool tryChangeImpl(State& st, const Change* ch, int nch, double T) {
    // single change: the annealing test first, with the same arithmetic in the same order as the
    // general code below (which then skips its own test, so the random stream is the same)
    bool deltaDone = false;
    if (nch == 1 && ch[0].from != ch[0].to) {
        const int s = ch[0].s, f = ch[0].from, t = ch[0].to;
        Ov q[2];
        int nq = 0;
        if (f >= 0) q[nq++] = {f, st.cnt[f] - 1, st.tsum[f] - ntask[s]};
        if (t >= 0) q[nq++] = {t, st.cnt[t] + 1, st.tsum[t] + ntask[s]};
        double dB = 0, dC = 0;
        if (f >= 0) dB -= rew[s] - distSO(f, s);
        if (t >= 0) dB += rew[s] - distSO(t, s);
        for (int a = 0; a < nq; a++) {
            int o = q[a].o;
            if (q[a].cnt > maxSize[o]) return false;
            if (st.cnt[o] == 0 && q[a].cnt > 0) dB -= ocost[o], dC += ocost[o];
            if (st.cnt[o] > 0 && q[a].cnt == 0) dB += ocost[o], dC -= ocost[o];
        }
        int c0, c1, t0, t1, n0, n1, u0, u1;
        if (st.loC.n > 0) c0 = st.loC.v[0], c1 = st.hiC.v[0], t0 = st.loT.v[0], t1 = st.hiT.v[0];
        else c0 = c1 = t0 = t1 = 0;
        fastExtremes(st, q, nq, n0, n1, u0, u1);
        double delta = dB + (1 - wCost) * dC + softTerms(n0, n1, u0, u1, lambdaCnt) - softTerms(c0, c1, t0, t1, lambdaCnt);
        if (l1Cost > 0)
            for (int a = 0; a < nq; a++) delta -= l1Cost * (l1Dev(q[a].cnt, q[a].tsum) - l1Dev(st.cnt[q[a].o], st.tsum[q[a].o]));
        if (lvTarget >= 0)
            for (int a = 0; a < nq; a++) delta -= wLv * alpha * (lvTerm(q[a].cnt, q[a].tsum) - lvTerm(st.cnt[q[a].o], st.tsum[q[a].o]));
        if (delta < 0 && urand() >= exp(delta / T)) return false;
        deltaDone = true;
    }
    return tryChangeBody(st, ch, nch, T, deltaDone);
}
#ifdef SZ_VERIFY
// verification build: every change also runs on a copy through the general geometry check, and
// the outcome, the random stream and the resulting states must agree
long long vfCalls = 0;
static void vfFail(const char* what) {
    fprintf(stderr, "VERIFY MISMATCH: %s (call %lld)\n", what, vfCalls);
    exit(3);
}
bool tryChange(State& st, const Change* ch, int nch, double T) {
    vfCalls++;
    State cp = st;
    auto rs = rng;
    tcRef = true;
    bool r1 = tryChangeImpl(cp, ch, nch, T);
    tcRef = false;
    auto rs1 = rng;
    rng = rs;
    bool r2 = tryChangeImpl(st, ch, nch, T);
    if (r1 != r2) vfFail("result");
    if (!(rng == rs1)) vfFail("rng");
    if (cp.asg != st.asg || cp.cnt != st.cnt || cp.tsum != st.tsum || cp.cover != st.cover || cp.ownS != st.ownS ||
        cp.multiCov != st.multiCov || cp.skey != st.skey || cp.omask != st.omask || cp.need != st.need || cp.owk != st.owk)
        vfFail("state");
    for (int o = 0; o < K; o++) {
        if (cp.hull[o].v != st.hull[o].v) vfFail("hull");
        vector<int> a = cp.cov[o], b = st.cov[o];
        sort(a.begin(), a.end()), sort(b.begin(), b.end());  // the order of coverage lists is free
        if (a != b) vfFail("cov");
    }
    // the flat invariants
    for (int o = 0; o < K; o++) {
        vector<uint64_t> k;
        for (int s : st.mem[o]) k.push_back(pkey(s));
        sort(k.begin(), k.end());
        if (k != st.skey[o]) vfFail("skey invariant");
        for (int sk = 0; sk < NS; sk++)
            if ((st.skc[o][sk] > 0) != (bool)st.omask[o][sk]) vfFail("omask invariant");
    }
    return r2;
}
#else
inline bool tryChange(State& st, const Change* ch, int nch, double T) { return tryChangeImpl(st, ch, nch, T); }
#endif

// soft energy used by the annealer
double energy(const State& st) {
    int cmin, cmax, tmin, tmax;
    extremes(st, nullptr, 0, cmin, cmax, tmin, tmax);
    double e = st.base + (1 - wCost) * st.openCost + softTerms(cmin, cmax, tmin, tmax, lambdaCnt);
    if (l1Cost > 0)
        for (int o = 0; o < K; o++) e -= l1Cost * l1Dev(st.cnt[o], st.tsum[o]);
    if (lvTarget >= 0)
        for (int o = 0; o < K; o++) e -= wLv * alpha * lvTerm(st.cnt[o], st.tsum[o]);
    return e;
}

// Sorting sites by a per-site key: the keys are computed once into a scratch array and compared
// from there (the same values in the same comparisons as a comparator computing them each time,
// so std::sort makes the same moves and gives the same order, ties included).
static vector<double> sortKeyBuf;
template <class KF>
static inline void sortSitesByKey(vector<int>::iterator b, vector<int>::iterator e, bool desc, KF key) {
    if ((int)sortKeyBuf.size() < n) sortKeyBuf.resize(n);
    double* k = sortKeyBuf.data();
    for (auto i = b; i != e; ++i) k[*i] = key(*i);
    if (desc) sort(b, e, [k](int x, int y) { return k[x] > k[y]; });
    else sort(b, e, [k](int x, int y) { return k[x] < k[y]; });
}
vector<vector<int>> nearOrder;  // per office: sites sorted by distance
vector<vector<int>> nearOff;    // per site: closest offices by distance
const double FORCE_T = 1e300;

// ---- forced building blocks for compound moves (no SA test inside)

// Forced site-by-site adds (doOpen, doInsert, doTopUp, zone moves) can touch hundreds of
// thousands of sites on huge instances (n = 1.3M: one doOpen took 80 s): they stop at opDeadline
// (the SA run's end + 1 s inside saLoop, else the hard deadline); the clock is read every 16th site
extern double hardDeadline;
double opDeadline = 1e300;
static inline bool opLate(int& chk) { return (chk++ & 15) == 0 && elapsed() > min(opDeadline, hardDeadline); }

// Pull nearby sites into empty office q. Returns number of sites added.
int doOpen(State& st, int q) {
    if (st.cnt[q] != 0) return 0;
    int openCnt = 0, sumCnt = 0, maxT = 0;
    for (int o = 0; o < K; o++)
        if (st.cnt[o] > 0) openCnt++, sumCnt += st.cnt[o], maxT = max(maxT, st.tsum[o]);
    // with a balance penalty, aim the new office at the current task level
    int taskCap = (openCnt && alpha > 0 && irand(2)) ? maxT : INT32_MAX;
    int target = openCnt ? sumCnt / (openCnt + 1) : maxSize[q];
    target = max(1, min(maxSize[q], target + irand(max(1, target / 3 + 1)) - target / 6));
    Change c;
    int added = 0;
    int scanned = 0, scanCap = min(n, 3 * target + 20), chk = 0;
    for (int s : nearOrder[q]) {
        if (added >= target || ++scanned > scanCap || opLate(chk)) break;
        if (st.tsum[q] + ntask[s] > taskCap) continue;
        if (st.asg[s] >= 0 && irand(2)) continue;  // prefer free sites half of the time
        c = {s, st.asg[s], q};
        if (tryChange(st, &c, 1, FORCE_T)) added++;
    }
    return added;
}

// Unassign the given sites (always feasible).
void doUnassign(State& st, const vector<int>& sites) {
    Change c;
#ifndef SZ_VERIFY
    if (sites.size() >= 256 && !skDefer) {  // batched skey removal (see skDead): same state, no O(zone) erases
        if (skDead.size() < (size_t)n) skDead.assign(n, 0);
        vector<char> touched(K, 0);
        vector<int> tried;  // the sites removed here (their skDead marks are cleared at the end)
        tried.reserve(sites.size());
        skDefer = true;
        for (int s : sites) {
            if (st.asg[s] < 0) continue;
            touched[st.asg[s]] = 1;
            tried.push_back(s);
            c = {s, st.asg[s], -1};
            tryChange(st, &c, 1, FORCE_T);
        }
        skDefer = false;
        for (int o = 0; o < K; o++)
            if (touched[o]) {
                auto& sk = st.skey[o];
                sk.erase(remove_if(sk.begin(), sk.end(), [](uint64_t k) { return skDead[(uint32_t)k] != 0; }), sk.end());
            }
        for (int s : tried) skDead[s] = 0;  // (sites may alias st.mem[o], which the loop has changed)
        return;
    }
#endif
    for (int s : sites) {
        if (st.asg[s] < 0) continue;
        c = {s, st.asg[s], -1};
        tryChange(st, &c, 1, FORCE_T);
    }
}

// Greedily give free sites to open offices when that improves the energy.
double hardDeadline = 1e300;  // never let greedy refills run past this
double searchEnd = 1e300;     // end of the search phases (no band trims close to it)
// per site: all offices by distance, computed on first use; only for sites whose office distances
// are all distinct (then the sorted list of open offices is unique, so filtering this list gives
// exactly the per-call sort)
vector<uint16_t> rfOrd;
vector<char> rfState;  // 0 unknown, 1 rfOrd ready, 2 ties (sort per call)
const uint16_t* refillOrder(int s) {
    if (rfState.empty()) {
        if (K <= 1 || K >= 65535 || (double)n * K > 2.4e7) return nullptr;
        rfState.assign(n, 0);
        rfOrd.assign((size_t)n * K, 0);
    }
    if (rfState[s] == 0) {
        uint16_t* r = rfOrd.data() + (size_t)s * K;
        for (int o = 0; o < K; o++) r[o] = o;
        stable_sort(r, r + K, [&](int a, int b) { return distSO(a, s) < distSO(b, s); });
        bool tie = false;
        for (int i = 1; i < K && !tie; i++) tie = !(distSO(r[i - 1], s) < distSO(r[i], s));
        rfState[s] = tie ? 2 : 1;
    }
    return rfState[s] == 1 ? rfOrd.data() + (size_t)s * K : nullptr;
}
// A free site joining an open office o at temperature 0: tryChange first rejects it without a
// random draw when o is full, then computes delta = (p + 0) + soft(new) - soft(old) with the
// profit p and soft(new) <= 0, and rejects with one draw when delta < 0. Rounding is monotone, so
// p - soft(old) < 0 (as computed) implies delta < 0: such offices are rejected here the same way.
static inline bool refillTry(State& st, int s, int o, double softOld, bool quick) {
    if (st.cnt[o] + 1 > maxSize[o]) return false;
    if (quick && (rew[s] - distSO(o, s)) - softOld < 0) {
        urand();
        return false;
    }
    Change c = {s, -1, o};
    return tryChange(st, &c, 1, 0.0);
}
void doRefill(State& st, const vector<int>& sites) {
    int chk = 0;
    const bool quick = l1Cost <= 0 && lvTarget < 0 && alpha >= 0;  // no other soft terms in delta
    for (int s : sites) {
        // the safety deadline (opDeadline inside saLoop, see opLate): the clock is read for every 16th
        // site; stopping early leaves free sites, the state stays valid
        if ((chk++ & 15) == 0 && elapsed() > min(opDeadline, hardDeadline)) return;
        if (st.asg[s] >= 0) continue;
        double softOld = 0;
        if (st.loC.n > 0) softOld = softTerms(st.loC.v[0], st.hiC.v[0], st.loT.v[0], st.hiT.v[0], lambdaCnt);
        else softOld = softTerms(0, 0, 0, 0, lambdaCnt);
        if (const uint16_t* ord = refillOrder(s)) {
            for (int i = 0; i < K; i++) {
                int o = ord[i];
                if (st.cnt[o] == 0) continue;
                if (refillTry(st, s, o, softOld, quick)) break;
            }
            continue;
        }
        static vector<int> order(K);
        int no = 0;
        for (int o = 0; o < K; o++)
            if (st.cnt[o] > 0) order[no++] = o;
        sort(order.begin(), order.begin() + no, [&](int a, int b) { return dist[a][s] < dist[b][s]; });
        for (int i = 0; i < no; i++)
            if (refillTry(st, s, order[i], softOld, quick)) break;
    }
}

// Open the closed office q by carving: every site nearer (Euclidean) to q than to its own office is
// freed (each zone keeps the part on its own side, so it stays valid and stops covering q), free
// profitable sites within the same radius join them, and q takes them nearest first up to its
// size; whatever q cannot take is refilled greedily. Returns the number of sites q took.
int doInsert(State& st, int q) {
    if (q < 0 || q >= K || st.cnt[q] != 0 || maxSize[q] <= 0) return 0;
    auto sq = [&](int s, int o) { double dx = px[s] - px[n + o], dy = py[s] - py[n + o]; return dx * dx + dy * dy; };
    vector<pair<double, int>> cand, freeC;
    double R2 = -1;
    for (int s = 0; s < n; s++) {
        double dq = sq(s, q);
        int o = st.asg[s];
        if (o >= 0) {
            if (dq < sq(s, o)) cand.push_back({dq, s}), R2 = max(R2, dq);
        } else if (rew[s] - dist[q][s] > 0)
            freeC.push_back({dq, s});
    }
    sort(freeC.begin(), freeC.end());
    if (R2 < 0 && !freeC.empty()) R2 = freeC[min(freeC.size(), (size_t)maxSize[q]) - 1].first;
    for (auto& f : freeC)
        if (f.first <= R2) cand.push_back(f);
    sort(cand.begin(), cand.end());
    vector<int> freed;
    for (auto& c : cand)
        if (st.asg[c.second] >= 0) freed.push_back(c.second);
    doUnassign(st, freed);
    if (st.cover[n + q] > 0) {  // still inside some hull (ties on the bisector): give up, refill
        doRefill(st, freed);
        return 0;
    }
    int added = 0, chk = 0;
    Change c;
    for (auto& e : cand) {
        if (added >= maxSize[q] || opLate(chk)) break;
        int s = e.second;
        if (st.asg[s] >= 0 || rew[s] - dist[q][s] <= 0) continue;
        c = {s, -1, q};
        if (tryChange(st, &c, 1, FORCE_T)) added++;
    }
    doRefill(st, freed);
    return added;
}

// Top up office p with free nearby profitable sites that need no skill p lacks (after it dropped
// a skill, so it keeps its size with the workers it still has), up to its size before the drop.
static const int topUpOn = 1;
void doTopUp(State& st, int p, int target) {
    if (!topUpOn || st.cnt[p] == 0) return;
    target = min(target, maxSize[p]);
    Change c;
    int scanned = 0, scanCap = min(n, 4 * maxSize[p] + 20), chk = 0;
    for (int s : nearOrder[p]) {
        if (st.cnt[p] >= target || ++scanned > scanCap || opLate(chk)) break;
        if (st.asg[s] != -1 || (smask[s] & ~st.omask[p]).any() || rew[s] - dist[p][s] <= 0) continue;
        c = {s, -1, p};
        tryChange(st, &c, 1, FORCE_T);
    }
}

// Greedily even out task loads after a compound change: top up the lightest office
// with free sites, or drop low-value sites from the heaviest one, while that pays off.
void doBalance(State& st) {
    if (alpha <= 0) return;
    Change c;
    for (int step = 0; step < 4 * K + 50; step++) {
        if (st.loT.n == 0) return;
        int lo = st.loT.o[0], hi = st.hiT.o[0];
        int gap = st.hiT.v[0] - st.loT.v[0];
        if (gap <= 0) return;
        bool done = false;
        int tries = 0;
        for (int s : nearOrder[lo]) {
            if (st.asg[s] != -1 || ntask[s] == 0 || ntask[s] > gap) continue;
            if (++tries > 30) break;
            c = {s, -1, lo};
            if (tryChange(st, &c, 1, 0.0)) {
                done = true;
                break;
            }
        }
        if (done) continue;
        int bs = -1;
        double bv = 1e300;
        for (int s : st.mem[hi])
            if (ntask[s] > 0 && ntask[s] <= gap && rew[s] - dist[hi][s] < bv) bv = rew[s] - dist[hi][s], bs = s;
        if (bs < 0) return;
        c = {bs, hi, -1};
        if (!tryChange(st, &c, 1, 0.0)) return;
    }
}

// Run a compound move: apply forced ops, then accept/reject the whole by SA rule.
template <class F>
bool compound(State& st, double T, F ops) {
    State backup = st;
    double e0 = energy(st);
    if (!ops()) {
        st = std::move(backup);
        return false;
    }
    static const bool noBalance = false;
    if (!noBalance) doBalance(st);
    double dE = energy(st) - e0;
    if (dE >= 0 || urand() < exp(dE / T)) return true;
    st = std::move(backup);
    return false;
}

int pickOpen(const State& st) {
    static vector<int> c(max(K, 64));
    int k = 0;
    for (int o = 0; o < K; o++)
        if (st.cnt[o] > 0) c[k++] = o;
    return k ? c[irand(k)] : -1;
}
int pickEmpty(const State& st) {
    static vector<int> c(max(K, 64));
    int k = 0;
    for (int o = 0; o < K; o++)
        if (st.cnt[o] == 0) c[k++] = o;
    return k ? c[irand(k)] : -1;
}
int pickSkill(const Mask& m) {
    static vector<int> c(MAXSK);
    int k = 0;
    for (int s = 0; s < NS; s++)
        if (m[s]) c[k++] = s;
    return k ? c[irand(k)] : -1;
}
vector<int> sitesWithSkill(const State& st, int o, int sk) {
    vector<int> r;
    for (int s : st.mem[o])
        if (smask[s][sk]) r.push_back(s);
    return r;
}

// Shift the task level of every open office by the same amount d (balance-preserving):
// d > 0 adds one d-task site to each office, d < 0 removes one.
bool doLevel(State& st, int d) {
    static vector<int> open(K);
    int no = 0;
    for (int o = 0; o < K; o++)
        if (st.cnt[o] > 0) open[no++] = o;
    if (no == 0) return false;
    for (int i = no - 1; i > 0; i--) swap(open[i], open[irand(i + 1)]);
    Change c;
    for (int i = 0; i < no; i++) {
        int o = open[i];
        bool done = false;
        if (d > 0) {
            int tries = 0;
            for (int s : nearOrder[o]) {
                if (st.asg[s] != -1 || ntask[s] != d) continue;
                if (++tries > 40) break;
                c = {s, -1, o};
                if (tryChange(st, &c, 1, FORCE_T)) {
                    done = true;
                    break;
                }
            }
        } else {
            // remove the least profitable site with exactly -d tasks
            int bs = -1;
            double bv = 1e300;
            for (int s : st.mem[o])
                if (ntask[s] == -d && rew[s] - dist[o][s] < bv) bv = rew[s] - dist[o][s], bs = s;
            if (bs >= 0) {
                c = {bs, o, -1};
                done = tryChange(st, &c, 1, FORCE_T);
            }
        }
        if (!done) return false;
    }
    return true;
}

// Make the site counts satisfy |cnt_a - cnt_b| <= A: pick a window [lo, lo + A],
// close offices below it, trim offices above it (dropping least profitable sites),
// then greedily refill. Only removals precede the refill, so geometry stays valid.
void repairCounts(State& st) {
    vector<int> open;
    for (int o = 0; o < K; o++)
        if (st.cnt[o] > 0) open.push_back(o);
    if (open.empty()) return;
    // per office: site profits sorted descending, prefix sums
    vector<vector<double>> pref(K);
    for (int o : open) {
        vector<double> v;
        for (int s : st.mem[o]) v.push_back(rew[s] - dist[o][s]);
        sort(v.rbegin(), v.rend());
        pref[o].assign(v.size() + 1, 0);
        for (size_t i = 0; i < v.size(); i++) pref[o][i + 1] = pref[o][i] + v[i];
    }
    int bestLo = -1;
    double bestVal = -1e300;
    vector<int> loDone;  // window starts evaluated (a repeat gives the same value: never a strict gain)
    for (int o0 : open) {
        int lo = st.cnt[o0];
        if (find(loDone.begin(), loDone.end(), lo) != loDone.end()) continue;
        loDone.push_back(lo);
        double val = 0;
        for (int o : open) {
            if (st.cnt[o] < lo) continue;
            int keep = min(st.cnt[o], lo + A);
            val += pref[o][keep] - ocost[o];
        }
        if (val > bestVal) bestVal = val, bestLo = lo;
    }
    double lamSave = lambdaCnt;
    lambdaCnt = max(lambdaCnt, 1e18);
    for (int o : open) {
        if (st.cnt[o] < bestLo) {
            vector<int> sites = st.mem[o];
            doUnassign(st, sites);
        } else if (st.cnt[o] > bestLo + A) {
            vector<int> sites = st.mem[o];
            sortSitesByKey(sites.begin(), sites.end(), false, [&](int a) { return rew[a] - dist[o][a]; });
            sites.resize(st.cnt[o] - (bestLo + A));
            doUnassign(st, sites);
        }
    }
    vector<int> freeSites;
    for (int s = 0; s < n; s++)
        if (st.asg[s] < 0) freeSites.push_back(s);
    doRefill(st, freeSites);
    lambdaCnt = lamSave;
}

// Record the current state as best if it (or its count-repaired copy) improves.
// Equalize task loads: pick a common level L, close offices below it and strip the
// least efficient task-bearing sites from offices above it (removals keep geometry valid).
void repairTasks(State& st) {
    if (alpha <= 0) return;
    vector<int> open;
    for (int o = 0; o < K; o++)
        if (st.cnt[o] > 0) open.push_back(o);
    if (open.size() <= 1) return;
    vector<vector<int>> strip(K);
    vector<double> officeVal(K, 0);
    for (int o : open) {
        for (int s : st.mem[o]) {
            officeVal[o] += rew[s] - dist[o][s];
            if (ntask[s] > 0) strip[o].push_back(s);
        }
        officeVal[o] -= ocost[o];
        sortSitesByKey(strip[o].begin(), strip[o].end(), false, [&](int a) { return (rew[a] - dist[o][a]) / ntask[a]; });
    }
    int bestL = -1;
    double bestVal = trueObjective(st);
    vector<int> lDone;  // levels evaluated (a repeat gives the same value: it cannot pass the test again)
    for (int o0 : open) {
        int L = st.tsum[o0];
        if (find(lDone.begin(), lDone.end(), L) != lDone.end()) continue;
        lDone.push_back(L);
        double val = 0;
        int maxr = 0;
        for (int o : open) {
            if (st.tsum[o] < L) continue;
            int t = st.tsum[o];
            double v = officeVal[o];
            for (int s : strip[o])
                if (t - ntask[s] >= L) t -= ntask[s], v -= rew[s] - dist[o][s];
            val += v;
            maxr = max(maxr, t - L);
        }
        val -= alpha * maxr;
        if (val > bestVal + 1e-9 * (1 + fabs(bestVal))) bestVal = val, bestL = L;
    }
    if (bestL < 0) return;
    for (int o : open) {
        if (st.tsum[o] < bestL) {
            vector<int> sites = st.mem[o];
            doUnassign(st, sites);
            continue;
        }
        vector<int> drop;
        int t = st.tsum[o];
        for (int s : strip[o])
            if (t - ntask[s] >= bestL) t -= ntask[s], drop.push_back(s);
        doUnassign(st, drop);
    }
    vector<int> freeSites;
    for (int s = 0; s < n; s++)
        if (st.asg[s] < 0) freeSites.push_back(s);
    doRefill(st, freeSites);
}

// ---------------------------------------------------------------- exact task-band selection
// Zones z (office zo[z], candidate sites cand[z]) may keep any subset of their candidates.
// Choose the subsets maximizing  sum(reward - dist) - cost(open) - alpha * (max tasks - min tasks)
// with |subset| <= maxSize: an exact-task-total knapsack per zone (a few Lagrange levels for the
// size limit), then the best common band [L, L + d] of task totals over the open zones.
// Returns the site assignment (size n, -1 = unassigned), or an empty vector when the tables
// would be too large, the count balance A breaks, or nothing pays.
double bandOps = 4e8;  // knapsack cell updates allowed per call
// f[t] = NEG for every t above the reachable maximum hi (the prefix sum of the weights), so the
// item loop stops there; and with |p| < 1e200, NEG + p rounds back to NEG, so the explicit NEG test
// is dropped (an unreachable source can never beat f[t] >= NEG). Same tables as the plain loop.
template <bool BITS>
static void knapRunT(const vector<int>& cs, const vector<double>& pr, int T, double lam, vector<double>& f, vector<int>& c,
                     vector<uint64_t>* bits) {
    const double NEG = -1e300;
    f.assign(T + 1, NEG);
    c.assign(T + 1, 0);
    f[0] = 0;
    size_t words = (size_t)(T + 64) / 64;
    if (BITS) bits->assign(cs.size() * words, 0);
    double* __restrict F = f.data();
    int* __restrict C = c.data();
    int hi = 0;
    for (size_t i = 0; i < cs.size(); i++) {
        int w = ntask[cs[i]];
        double p = pr[i] - lam;
        uint64_t* b = BITS ? bits->data() + i * words : nullptr;
        if (w == 0) {
            if (p <= 0) continue;
            for (int t = 0; t <= hi; t++)
                if (F[t] > NEG) {
                    F[t] += p, C[t]++;
                    if (BITS) b[t >> 6] |= 1ULL << (t & 63);
                }
            continue;
        }
        int top = (int)min((long long)T, (long long)hi + w);
        if (fabs(p) < 1e200) {
            for (int t = top; t >= w; t--) {  // branch-free: same values as the conditional update
                double v = F[t - w] + p, fo = F[t];
                bool up = v > fo;
                F[t] = up ? v : fo;
                C[t] = up ? C[t - w] + 1 : C[t];
                if (BITS) b[t >> 6] |= (uint64_t)up << (t & 63);
            }
        } else {
            for (int t = top; t >= w; t--) {
                double v = F[t - w];
                if (v <= NEG) continue;
                v += p;
                if (v > F[t]) {
                    F[t] = v, C[t] = C[t - w] + 1;
                    if (BITS) b[t >> 6] |= 1ULL << (t & 63);
                }
            }
        }
        hi = max(hi, top);
    }
}
static void knapRun(const vector<int>& cs, const vector<double>& pr, int T, double lam, vector<double>& f, vector<int>& c,
                    vector<uint64_t>* bits) {
    if (bits) knapRunT<true>(cs, pr, T, lam, f, c, bits);
    else knapRunT<false>(cs, pr, T, lam, f, c, nullptr);
}
// Per-zone knapsack tables are a function of (office, filtered candidates, level extension); the
// triangulation sweep meets the same zones under many task levels, so it caches them (and the
// reconstructed site sets per chosen task total). Exact: a hit returns the very same tables.
struct BandCacheEnt {
    int o;
    bool ext;
    vector<int> cand;
    vector<double> F, lams;
    vector<unsigned char> lev;
    unordered_map<int, vector<int>> picks;  // task total -> chosen candidates
};
bool bandCacheOn = false;
vector<BandCacheEnt> bcEnt;
unordered_map<uint64_t, vector<int>> bcIdx;
size_t bcWords = 0;
long long bcHits = 0, bcMiss = 0;
void bandCacheClear() {
    vector<BandCacheEnt>().swap(bcEnt);
    unordered_map<uint64_t, vector<int>>().swap(bcIdx);
    bcWords = 0;
}
static uint64_t bcHash(int o, bool ext, const vector<int>& c) {
    uint64_t h = 0x9E3779B97F4A7C15ULL ^ ((uint64_t)o << 1) ^ (uint64_t)ext;
    for (int v : c) h = (h ^ (uint64_t)(uint32_t)v) * 0x100000001B3ULL, h ^= h >> 29;
    return h ^ c.size();
}
static int bcFind(uint64_t h, int o, bool ext, const vector<int>& c) {
    auto it = bcIdx.find(h);
    if (it == bcIdx.end()) return -1;
    for (int id : it->second)
        if (bcEnt[id].o == o && bcEnt[id].ext == ext && bcEnt[id].cand == c) return id;
    return -1;
}
vector<int> bandSelect(const vector<int>& zo, const vector<vector<int>>& candIn, double* outVal) {
    *outVal = -1e300;
    int Z = zo.size();
    const double NEG = -1e300;
    vector<vector<int>> cand(Z);
    vector<vector<double>> prof(Z);
    vector<int> Tc(Z, 0);
    double work = 0;
    int Tmax = 0;
    for (int z = 0; z < Z; z++) {
        int o = zo[z];
        for (int s : candIn[z]) {
            double p = rew[s] - dist[o][s];
            if (p > 0 || (alpha > 0 && ntask[s] > 0 && p > -alpha * ntask[s])) cand[z].push_back(s), prof[z].push_back(p), Tc[z] += ntask[s];
        }
        work += (double)cand[z].size() * (Tc[z] + 1);
        Tmax = max(Tmax, Tc[z]);
    }
    if (work * 2 > bandOps || (double)Z * (Tmax + 1) > 2e7) return {};
    // F[z][t]: best real profit with exactly t tasks within the size limit; lev[z][t]: its Lagrange level
    vector<vector<double>> F(Z);
    vector<vector<unsigned char>> lev(Z);
    vector<vector<double>> lams(Z);
    vector<double> f;
    vector<int> c;
    const bool ext = work * 6 <= bandOps;
    vector<int> cacheId(Z, -1);
    for (int z = 0; z < Z; z++) {
        int o = zo[z], T = Tc[z];
        uint64_t hk = 0;
        if (bandCacheOn) {
            hk = bcHash(o, ext, cand[z]);
            int id = bcFind(hk, o, ext, cand[z]);
            if (id >= 0) {
                F[z] = bcEnt[id].F, lev[z] = bcEnt[id].lev, lams[z] = bcEnt[id].lams;
                cacheId[z] = id, bcHits++;
                continue;
            }
            bcMiss++;
        }
        F[z].assign(T + 1, NEG);
        lev[z].assign(T + 1, 0);
        lams[z] = {0.0};
        auto store = [&]() {
            if (!bandCacheOn || bcWords > 3000000) return;
            BandCacheEnt e;
            e.o = o, e.ext = ext, e.cand = cand[z], e.F = F[z], e.lev = lev[z], e.lams = lams[z];
            bcWords += 2 * (size_t)T + cand[z].size() + 16;
            cacheId[z] = bcEnt.size();
            bcIdx[hk].push_back(bcEnt.size());
            bcEnt.push_back(std::move(e));
        };
        if (cand[z].empty() || maxSize[o] <= 0) {
            store();
            continue;
        }
        double mp = 0;
        for (double p : prof[z]) mp += fabs(p);
        mp /= cand[z].size();
        for (int l = 0; l < (int)lams[z].size(); l++) {
            knapRun(cand[z], prof[z], T, lams[z][l], f, c, nullptr);
            bool over = false;
            for (int t = 0; t <= T; t++) {
                if (f[t] <= NEG) continue;
                if (c[t] > maxSize[o]) {
                    over = true;
                    continue;
                }
                double v = f[t] + lams[z][l] * c[t];
                if (v > F[z][t]) F[z][t] = v, lev[z][t] = l;
            }
            if (l == 0 && over && ext)
                for (double m : {0.1, 0.3, 1.0, 3.0}) lams[z].push_back(m * mp);
        }
        store();
    }
    // best band
    double UB = 0;
    vector<double> zmax(Z, NEG);
    for (int z = 0; z < Z; z++) {
        for (double v : F[z]) zmax[z] = max(zmax[z], v);
        UB += max(0.0, zmax[z] - ocost[zo[z]]);
    }
    double best = NEG;
    int bL = -1, bD = -1;
    int maxD = (int)min((double)Tmax, 3e8 / ((double)Z * (Tmax + 1)));  // band widths tried (work cap)
    if (alpha <= 0) {
        best = UB, bL = 0, bD = Tmax;
    } else {
        vector<vector<double>> cur(Z);
        for (int z = 0; z < Z; z++) {
            cur[z].assign(Tmax + 1, NEG);
            for (int t = 0; t < (int)F[z].size(); t++) cur[z][t] = F[z][t] - ocost[zo[z]];
        }
        vector<double> val(Tmax + 1);
        // ub[L]: every zone at its best level >= L, so val[L] <= ub[L] for every width d (sums in the
        // same zone order, floating addition is monotone); ub falls with L, so the levels that can
        // still beat best (ub[L] - alpha * d > best) form a shrinking prefix [0, Lact)
        vector<double> ub(Tmax + 1, 0.0);
        for (int z = 0; z < Z; z++) {
            double sm = NEG, cz = ocost[zo[z]];
            for (int L = Tmax; L >= 0; L--) {
                if (L < (int)F[z].size()) sm = max(sm, F[z][L]);
                double tm = sm - cz;
                ub[L] += tm > 0 ? tm : 0.0;
            }
        }
        int Lact = Tmax + 1;
        for (int d = 0; d <= maxD; d++) {
            if (alpha * d >= UB - best) break;
            while (Lact > 0 && !(ub[Lact - 1] - alpha * d > best)) Lact--;
            if (Lact == 0) break;
            const int Lend = min(Lact, Tmax - d + 1);  // levels L < Lend are evaluated
            // one pass per zone: widen its band table to width d, then add its positive values
            // (same values and the same summation order as two separate passes)
            fill(val.begin(), val.begin() + Lend, 0.0);
            double* __restrict vl = val.data();
            for (int z = 0; z < Z; z++) {
                double* __restrict cz_ = cur[z].data();
                const int fz = F[z].size();
                int lim = -1;
                if (d > 0) {
                    const double* Fz = F[z].data();
                    double cz = ocost[zo[z]];
                    lim = min(Tmax - d, fz - 1 - d);
                    int top = min(lim, Lend - 1);
                    for (int L = 0; L <= top; L++) {
                        double a = cz_[L], b = Fz[L + d] - cz;
                        double m = max(a, b);
                        cz_[L] = m;
                        vl[L] += m > 0 ? m : 0.0;
                    }
                }
                int hi = min(Lend, fz);  // beyond its table a zone holds NEG: adds nothing
                for (int L = max(0, lim + 1); L < hi; L++) {
                    double m = cz_[L];
                    vl[L] += m > 0 ? m : 0.0;
                }
            }
            for (int L = 0; L < Lend; L++)  // read through vl: val is written only through the restrict pointer
                if (vl[L] > 0 && vl[L] - alpha * d > best) best = vl[L] - alpha * d, bL = L, bD = d;
        }
    }
    if (bL < 0 || best <= 0) return {};
    vector<int> asg(n, -1);
    vector<uint64_t> bits;
    int cmin = INT32_MAX, cmax = 0;
    for (int z = 0; z < Z; z++) {
        int bt = -1;
        double bv = 0;
        int hi = min((int)F[z].size() - 1, bL + bD);
        for (int t = bL; t <= hi; t++)
            if (F[z][t] - ocost[zo[z]] > bv) bv = F[z][t] - ocost[zo[z]], bt = t;
        if (bt < 0) continue;
        int cnt = 0;
        const vector<int>* cached = nullptr;
        if (cacheId[z] >= 0) {
            auto it = bcEnt[cacheId[z]].picks.find(bt);
            if (it != bcEnt[cacheId[z]].picks.end()) cached = &it->second;
        }
        if (cached) {
            for (int s : *cached) asg[s] = zo[z], cnt++;
        } else {
            double lam = lams[z][lev[z][bt]];
            // tables up to bt only: f[t] uses lower t only, so entries 0..bt (and their bits) are the
            // same as in the full run, and the trace back from bt never looks higher
            knapRun(cand[z], prof[z], bt, lam, f, c, &bits);
            size_t words = (size_t)(bt + 64) / 64;
            int t = bt;
            vector<int> chosen;
            for (int i = (int)cand[z].size() - 1; i >= 0; i--)
                if (bits[i * words + (t >> 6)] >> (t & 63) & 1) {
                    asg[cand[z][i]] = zo[z], cnt++;
                    chosen.push_back(cand[z][i]);
                    t -= ntask[cand[z][i]];
                }
            if (cacheId[z] >= 0 && bcWords <= 3000000) bcWords += chosen.size() + 8, bcEnt[cacheId[z]].picks[bt] = std::move(chosen);
        }
        if (cnt == 0) continue;
        cmin = min(cmin, cnt), cmax = max(cmax, cnt);
    }
    if (cmax > 0 && cmax - cmin > A) return {};
    *outVal = best;
    return asg;
}
// The band value of bandSelect without the assignment, with the per-zone knapsack tables cached by
// (office, candidate set): a local search that changes one or two zones per move recomputes only those.
struct BandZT {
    vector<double> F;  // best real profit with exactly t tasks within the size limit (-1e300: none)
    double fmax = -1e300;  // the largest entry of F (computed once, in index order)
};
static unordered_map<uint64_t, BandZT> bandCache;
static double bandCacheDoubles = 0;  // table entries stored in bandCache (its memory bound)
double bandValueCached(const vector<int>& zo, const vector<vector<int>>& candIn) {
    const double NEG = -1e300;
    int Z = zo.size();
    if (bandCacheDoubles > 2e7) bandCache.clear(), bandCacheDoubles = 0;
    // the work estimate of bandSelect (same candidate filter): over its cap bandSelect returns nothing,
    // and the extra Lagrange levels run only below a sixth of it (ext is part of the cache key)
    double work = 0;
    for (int z = 0; z < Z; z++) {
        int o = zo[z], cnt = 0, Tc = 0;
        for (int s : candIn[z]) {
            double p = rew[s] - dist[o][s];
            if (p > 0 || (alpha > 0 && ntask[s] > 0 && p > -alpha * ntask[s])) cnt++, Tc += ntask[s];
        }
        work += (double)cnt * (Tc + 1);
    }
    if (work * 2 > bandOps) return NEG;
    const bool ext = work * 6 <= bandOps;
    static vector<const BandZT*> zt;
    zt.assign(Z, nullptr);
    static vector<double> f;
    static vector<int> c;
    int Tmax = 0;
    for (int z = 0; z < Z; z++) {
        int o = zo[z];
        uint64_t h = 1469598103934665603ULL ^ (uint64_t)(o + 1) * 0x9E3779B97F4A7C15ULL ^ (ext ? 0 : 0xA5A5A5A5A5A5A5A5ULL);
        for (int x : candIn[z]) h = (h ^ (uint64_t)(x + 1)) * 1099511628211ULL;
        auto it = bandCache.find(h);
        if (it == bandCache.end()) {
            vector<int> cand;
            vector<double> prof;
            int Tc = 0;
            for (int s : candIn[z]) {
                double p = rew[s] - dist[o][s];
                if (p > 0 || (alpha > 0 && ntask[s] > 0 && p > -alpha * ntask[s])) cand.push_back(s), prof.push_back(p), Tc += ntask[s];
            }
            BandZT t;
            t.F.assign(Tc + 1, NEG);
            if (!cand.empty() && maxSize[o] > 0) {
                double mp = 0;
                for (double p : prof) mp += fabs(p);
                mp /= cand.size();
                vector<double> lams = {0.0};
                for (int l = 0; l < (int)lams.size(); l++) {
                    knapRun(cand, prof, Tc, lams[l], f, c, nullptr);
                    bool over = false;
                    for (int tt = 0; tt <= Tc; tt++) {
                        if (f[tt] <= NEG) continue;
                        if (c[tt] > maxSize[o]) {
                            over = true;
                            continue;
                        }
                        t.F[tt] = max(t.F[tt], f[tt] + lams[l] * c[tt]);
                    }
                    if (l == 0 && over && ext)
                        for (double mm : {0.1, 0.3, 1.0, 3.0}) lams.push_back(mm * mp);
                }
            }
            for (double v : t.F) t.fmax = max(t.fmax, v);
            bandCacheDoubles += Tc + 1;
            it = bandCache.emplace(h, std::move(t)).first;
        }
        zt[z] = &it->second;
        Tmax = max(Tmax, (int)it->second.F.size() - 1);
    }
    if ((double)Z * (Tmax + 1) > 2e7) return NEG;
    double UB = 0;
    for (int z = 0; z < Z; z++) {
        double zm = max(NEG, zt[z]->fmax);  // = the running max over F from NEG
        UB += max(0.0, zm - ocost[zo[z]]);
    }
    double best = NEG;
    // an estimate for local search: bands wider than bandEstD tasks are not tried (with a task penalty
    // the good plans sit in narrow bands; the exact bandSelect checks every new best)
    static const int bandEstD = 16;
    int maxD = (int)min((double)min(Tmax, bandEstD), 3e8 / ((double)Z * (Tmax + 1)));
    if (alpha <= 0) return UB > 0 ? UB : NEG;
    // cur[z][L] = best of F[L .. L + d] - cost; val[L] = sum over z (in z order) of its positive part.
    // The window update and the sum run in one pass per zone (adding +0.0 for a non-positive part
    // leaves a sum >= 0 unchanged, so the branch-free sum equals the conditional one)
    const int TW = Tmax + 1;
    static vector<double> curBuf, val;
    curBuf.resize((size_t)Z * TW);
    val.resize(TW);
    for (int z = 0; z < Z; z++) {
        double* cz = &curBuf[(size_t)z * TW];
        const vector<double>& Fz = zt[z]->F;
        const double oc = ocost[zo[z]];
        int m = (int)Fz.size();
        for (int t = 0; t < m; t++) cz[t] = Fz[t] - oc;
        for (int t = m; t < TW; t++) cz[t] = NEG;
    }
    for (int d = 0; d <= maxD; d++) {
        if (alpha * d >= UB - best) break;
        const int top = Tmax - d;  // L = 0 .. top
        double* __restrict V = val.data();
        for (int L = 0; L <= top; L++) V[L] = 0.0;
        for (int z = 0; z < Z; z++) {
            double* __restrict cz = &curBuf[(size_t)z * TW];
            int lim = -1;
            if (d > 0) {
                const double* __restrict Fd = zt[z]->F.data() + d;
                const double oc = ocost[zo[z]];
                lim = min(top, (int)zt[z]->F.size() - 1 - d);
                for (int L = 0; L <= lim; L++) {
                    double a = cz[L], b = Fd[L] - oc;
                    double v = a < b ? b : a;  // std::max(a, b)
                    cz[L] = v;
                    V[L] += v > 0 ? v : 0.0;
                }
            }
            for (int L = max(0, lim + 1); L <= top; L++) {
                double v = cz[L];
                V[L] += v > 0 ? v : 0.0;
            }
        }
        // the best V[L] - pen over V[L] > 0 (a maximum: the same value in any order; no NaN, and
        // V[L] - pen is never -0.0 for V[L] > 0), then the update of best as in the plain loop
        const double pen = alpha * d;
        double m0 = -INFINITY, m1 = -INFINITY, m2 = -INFINITY, m3 = -INFINITY;
        int L = 0;
        for (; L + 3 <= top; L += 4) {
            double x0 = V[L] > 0 ? V[L] - pen : -INFINITY, x1 = V[L + 1] > 0 ? V[L + 1] - pen : -INFINITY;
            double x2 = V[L + 2] > 0 ? V[L + 2] - pen : -INFINITY, x3 = V[L + 3] > 0 ? V[L + 3] - pen : -INFINITY;
            m0 = m0 < x0 ? x0 : m0, m1 = m1 < x1 ? x1 : m1, m2 = m2 < x2 ? x2 : m2, m3 = m3 < x3 ? x3 : m3;
        }
        for (; L <= top; L++) {
            double x0 = V[L] > 0 ? V[L] - pen : -INFINITY;
            m0 = m0 < x0 ? x0 : m0;
        }
        double m = max(max(m0, m1), max(m2, m3));
        if (m > best) best = m;
    }
    return best > 0 ? best : NEG;
}
// Trim the open offices of a state to their best common task band (removals only: geometry and
// workers stay valid). Returns false when no better state was found.
bool bandTrim(State& st) {
    if (alpha <= 0) return false;
    vector<int> zo;
    vector<vector<int>> cand;
    for (int o = 0; o < K; o++)
        if (st.cnt[o] > 0) zo.push_back(o), cand.push_back(st.mem[o]);
    if (zo.size() <= 1) return false;
    double v;
    vector<int> asg = bandSelect(zo, cand, &v);
    if (asg.empty()) return false;
    if ((int)st.asg.size() > n) asg.insert(asg.end(), st.asg.begin() + n, st.asg.end());
    State r = fromAsg(asg);
    if (!countFeasible(r) || trueObjective(r) <= trueObjective(st) + 1e-9) return false;
    st = std::move(r);
    return true;
}

// ---------------------------------------------------------------- exact task balance (tight A)
// With a task-imbalance penalty and a tight count window (A small against the zone size) every
// zone must carry the same task load with (almost) the same number of sites, and trimming to a
// common band loses many sites. epFix drives the open zones into a band [tau, tau + d] by
// count-preserving exchanges: a zone trades one of its sites for a free site with another task
// count near its office, or swaps a site with a neighbouring zone that deviates the other way
// (or, as a chain step, with an on-level neighbour). Plain drops/additions are used when the
// count window allows. exactPolish tries several bands on copies, closes zones it cannot fix when
// that pays, then grows all zones by one site at a time while that pays.
long long epCalls = 0, epWins = 0;
double epTime = 0, epLastObj = -1e300;
bool epOn = false;  // set in main: alpha > 0 and a tight count window
static const bool lineOn = true;
bool lineMode = false;  // levelSweep evaluates office sets by line cells only
bool lineGate = false;  // set in main: task penalty and enough capacity (or a tight window)
static bool epFix(State& st, int tau, int d, double endTime) {
    vector<int> Z;
    for (int o = 0; o < K; o++)
        if (st.cnt[o] > 0) Z.push_back(o);
    int nz = Z.size();
    if (nz < 2) return true;
    vector<vector<int>> nb(K);
    for (int o : Z) {
        vector<pair<double, int>> v;
        for (int q : Z)
            if (q != o) v.push_back({pow(px[n + o] - px[n + q], 2) + pow(py[n + o] - py[n + q], 2), q});
        int m = min((int)v.size(), 8);
        partial_sort(v.begin(), v.begin() + m, v.end());
        for (int i = 0; i < m; i++) nb[o].push_back(v[i].second);
    }
    auto dev = [&](int o) {
        int t = st.tsum[o];
        return t < tau ? t - tau : t > tau + d ? t - tau - d : 0;
    };
    auto prof = [&](int o, int s) { return rew[s] - dist[o][s]; };
    vector<char> stuck(K, 0);
    struct Mv {
        double sc;
        int p, q, j;  // p leaves o (to j or free), q joins o (from j or free); -1 = none
    };
    vector<Mv> mv;
    vector<int> pc, qc;
    int budget = 100 * nz + 200;
    for (int it = 0; it < budget; it++) {
        if ((it & 7) == 0 && elapsed() > endTime) return false;
        int o = -1, dv = 0;
        for (int z : Z)
            if (st.cnt[z] > 0 && !stuck[z]) {
                int x = dev(z);
                if (abs(x) > abs(dv)) dv = x, o = z;
            }
        if (o < 0) break;
        int sg = dv > 0 ? 1 : -1, need = abs(dv);
        int cmin = INT32_MAX, cmax = 0;
        for (int z : Z)
            if (st.cnt[z] > 0) cmin = min(cmin, st.cnt[z]), cmax = max(cmax, st.cnt[z]);
        mv.clear();
        // (R) replace a site of o by a free site near o; (D)/(Add) when the count window allows
        pc.clear(), qc.clear();
        for (int s : st.mem[o]) pc.push_back(s);
        int M = min(n, 3 * st.cnt[o] + 40);
        for (int i = 0; i < M; i++) {
            int s = nearOrder[o][i];
            if (st.asg[s] == -1) qc.push_back(s);
        }
        sort(pc.begin(), pc.end(), [&](int a, int b) { return prof(o, a) < prof(o, b); });
        sort(qc.begin(), qc.end(), [&](int a, int b) { return prof(o, a) > prof(o, b); });
        {
            // per task count keep the cheapest few leavers and the best few joiners
            map<int, int> np, nq;
            vector<int> P, Q;
            for (int s : pc)
                if (np[ntask[s]]++ < 6) P.push_back(s);
            for (int s : qc)
                if (nq[ntask[s]]++ < 10) Q.push_back(s);
            for (int p : P)
                for (int q : Q) {
                    int dt = ntask[p] - ntask[q];
                    if (sg * dt >= 1 && sg * dt <= need) mv.push_back({prof(o, q) - prof(o, p), p, q, -1});
                }
            bool canDrop = st.cnt[o] - 1 >= cmax - A && st.cnt[o] > 1;
            bool canAdd = st.cnt[o] + 1 <= cmin + A && st.cnt[o] + 1 <= maxSize[o];
            if (sg > 0 && canDrop)
                for (int p : P)
                    if (ntask[p] >= 1 && ntask[p] <= need) mv.push_back({-prof(o, p), p, -1, -1});
            if (sg < 0 && canAdd)
                for (int q : Q)
                    if (ntask[q] >= 1 && ntask[q] <= need) mv.push_back({prof(o, q), -1, q, -1});
        }
        // (S) swap with a neighbouring zone deviating the other way (chain: on level, penalized)
        for (int j : nb[o]) {
            if (st.cnt[j] == 0) continue;
            int dj = dev(j);
            bool direct = dj * sg < 0;
            if (!direct && dj != 0) continue;
            int lim = direct ? min(need, abs(dj)) : need;
            double chainPen = direct ? 0.0 : 1e-3 + 0.5 * fabs(prof(o, st.mem[o][0]));
            // a site can only change zones if it is a hull vertex of its zone (else it stays covered)
            vector<int> P, Q;
            for (int v : st.hull[o].v)
                if (v < n && st.asg[v] == o) P.push_back(v);
            for (int v : st.hull[j].v)
                if (v < n && st.asg[v] == j) Q.push_back(v);
            sort(P.begin(), P.end(), [&](int a, int b) { return dist[j][a] - dist[o][a] < dist[j][b] - dist[o][b]; });
            sort(Q.begin(), Q.end(), [&](int a, int b) { return dist[o][a] - dist[j][a] < dist[o][b] - dist[j][b]; });
            if (P.size() > 10) P.resize(10);
            if (Q.size() > 10) Q.resize(10);
            for (int p : P)
                for (int q : Q) {
                    int dt = ntask[p] - ntask[q];
                    if (sg * dt >= 1 && sg * dt <= lim)
                        mv.push_back({prof(j, p) + prof(o, q) - prof(o, p) - prof(j, q) - chainPen, p, q, j});
                }
        }
        sort(mv.begin(), mv.end(), [](const Mv& a, const Mv& b) { return a.sc > b.sc; });
        bool ok = false;
        int tries = 0, okJ = -1;
        Change ch[2];
        for (const Mv& m : mv) {
            if (++tries > 150) break;
            int nc = 0;
            if (m.p >= 0) ch[nc++] = {m.p, o, m.j};
            if (m.q >= 0) ch[nc++] = {m.q, m.j, o};
            if (tryChange(st, ch, nc, FORCE_T)) {
                ok = true, okJ = m.j;
                break;
            }
        }
        if (ok) {  // the zones around the changed boundary may have new options
            stuck[o] = 0;
            for (int q : nb[o]) stuck[q] = 0;
            if (okJ >= 0)
                for (int q : nb[okJ]) stuck[q] = 0;
        } else
            stuck[o] = 1;
    }
    for (int z : Z)
        if (st.cnt[z] > 0 && dev(z) != 0) return false;
    return true;
}
static void epCloseBad(State& st, int tau, int d, double endTime) {
    // zones left outside the band: close them (cheapest first) while the true objective improves
    for (int rep = 0; rep < K; rep++) {
        if (elapsed() > endTime) return;
        double cur = trueObjective(st);
        int bo = -1;
        double bv = cur;
        for (int o = 0; o < K; o++) {
            if (st.cnt[o] == 0 || (st.tsum[o] >= tau && st.tsum[o] <= tau + d)) continue;
            State c = st;
            vector<int> sites = c.mem[o];
            doUnassign(c, sites);
            if (!countFeasible(c)) continue;
            double v = trueObjective(c);
            if (v > bv + 1e-9) bv = v, bo = o;
        }
        if (bo < 0) return;
        vector<int> sites = st.mem[bo];
        doUnassign(st, sites);
    }
}
bool exactPolish(State& st, double endTime) {
    if (alpha <= 0 || !countFeasible(st)) return false;
    double t0 = elapsed();
    epCalls++;
    vector<int> ts;
    set<int> tk;
    for (int o = 0; o < K; o++)
        if (st.cnt[o] > 0) ts.push_back(st.tsum[o]);
    for (int s = 0; s < n; s++)
        if (ntask[s] > 0) tk.insert(ntask[s]);
    if (ts.size() < 2) return false;
    sort(ts.begin(), ts.end());
    double start = trueObjective(st), bestV = start;
    State best = st;
    if (ts.back() > ts[0]) {
        int med = ts[ts.size() / 2];
        vector<pair<int, int>> cfg = {{med, 0}, {med - 1, 0}, {med + 1, 0}, {med - 1, 1}, {med, 1}, {med - 2, 0}, {med + 2, 0}};
        for (auto [tau, d] : cfg) {
            if (elapsed() > endTime) break;
            if (tau < ts[0] || tau + d > ts.back() || alpha * d >= alpha * (ts.back() - ts[0])) continue;
            State c = st;
            bool fixed = epFix(c, tau, d, endTime);
            if (!fixed) epCloseBad(c, tau, d, endTime);
            if (!countFeasible(c)) continue;
            double v = trueObjective(c);
            if (v > bestV + 1e-9) bestV = v, best = std::move(c);
        }
    }
    // uniform growth: one free site with x tasks per zone keeps every load in its band
    for (int rep = 0; rep < 64 && elapsed() < endTime; rep++) {
        bool imp = false;
        for (int x : tk) {
            State c = best;
            if (!doLevel(c, x) || !countFeasible(c)) continue;
            double v = trueObjective(c);
            if (v > bestV + 1e-9) {
                bestV = v, best = std::move(c), imp = true;
                break;
            }
        }
        if (!imp) break;
    }
    epTime += elapsed() - t0;
    if (bestV > start + 1e-9 * max(1.0, fabs(start))) {
        st = std::move(best);
        epWins++;
        return true;
    }
    return false;
}

// Record the current state as best if it (or its repaired copy) improves.
// ---------------------------------------------------------------- zone pool (MIP columns)
// Every process collects the zones (office, site set) of the assignments it meets: fan/tri/power
// diagram starts, accepted power-diagram states, SA states and run bests. At the end the parent
// merges all pools and picks the best compatible set of zones with an exact MIP (see mipImprove).
struct PZone {
    int o;
    vector<int> s;  // sorted site ids
    uint64_t h;
};
vector<PZone> pool;
unordered_set<uint64_t> poolSeen;
bool poolOn = false;
size_t poolCap = 40000;
uint64_t zoneHash(int o, const vector<int>& s) {
    uint64_t h = 0x9E3779B97F4A7C15ULL ^ (uint64_t)(o + 1) * 0xBF58476D1CE4E5B9ULL;
    for (int v : s) {
        h ^= (uint64_t)(v + 1) + 0x9E3779B97F4A7C15ULL + (h << 6) + (h >> 2);
        h *= 0x94D049BB133111EBULL;
    }
    return h;
}
void poolAddZone(int o, vector<int> s) {
    if (!poolOn || s.empty() || (int)s.size() > maxSize[o]) return;
    sort(s.begin(), s.end());
    uint64_t h = zoneHash(o, s);
    if (poolSeen.count(h)) return;
    if (pool.size() >= poolCap) {  // full: replace a random older zone (later zones tend to be better)
        size_t i = irand(pool.size());
        poolSeen.erase(pool[i].h);
        pool[i] = {o, std::move(s), h};
    } else
        pool.push_back({o, std::move(s), h});
    poolSeen.insert(h);
}
void poolAddAsg(const vector<int>& asg) {
    if (!poolOn) return;
    static vector<vector<int>> z;
    z.assign(K, {});
    for (int s = 0; s < n && s < (int)asg.size(); s++)
        if (asg[s] >= 0 && asg[s] < K) z[asg[s]].push_back(s);
    for (int o = 0; o < K; o++)
        if (!z[o].empty()) poolAddZone(o, z[o]);
}
void poolAddAsgT(const vector<int>& asg, double gap) {  // throttled
    static double last = -1e9;
    if (!poolOn) return;
    double t = elapsed();
    if (t - last < gap) return;
    last = t;
    poolAddAsg(asg);
}

long long trimCalls = 0, trimWins = 0;
double trimTime = 0, trimLast = 0, trimLastEnd = -1e300;  // total / last duration, end of the last trim
double runBestObj = -1e300;  // best true objective seen during the current SA run
void considerBest(const State& st, bool allowRepair) {
    poolAddAsgT(st.asg, 0.2);
    if (countFeasible(st)) {
        double obj = trueObjective(st);
        runBestObj = max(runBestObj, obj);
        if (obj > bestObj + 1e-9) bestObj = obj, bestAsg = st.asg;
        if (alpha <= 0) return;
    }
    if (!allowRepair) return;
    // true weights from here on: no soft terms (L1 pull, ladder level) in the trim or the repairs
    double lamSave = lambdaCnt, waSave = wAlpha, wcSave = wCost, l1Save = l1Cost;
    int lvSave = lvTarget;
    lambdaCnt = 1e18, wAlpha = 1, wCost = 1, l1Cost = 0, lvTarget = -1;
    static const bool trimOn = true;
    // time budget: at most ~4% of the elapsed time, calls spaced by 10x the last trim's duration,
    // none close to the end of the search; rarer still (by count) while it never pays
    double now = trimOn && alpha > 0 ? elapsed() : 0;
    if (trimOn && alpha > 0 && now < searchEnd - max(1.0, 3 * trimLast) && trimTime <= 0.04 * now &&
        now - trimLastEnd >= 10 * trimLast && (trimCalls++ < 16 || trimWins > 0 || trimCalls % 8 == 0)) {
        State b = st;
        if (bandTrim(b) && countFeasible(b)) {
            double obj = trueObjective(b);
            runBestObj = max(runBestObj, obj);
            poolAddAsg(b.asg);
            if (obj > bestObj + 1e-9) bestObj = obj, bestAsg = b.asg, trimWins++;
        }
        trimLastEnd = elapsed();
        trimLast = trimLastEnd - now;
        trimTime += trimLast;
    }
    State r = st;
    if (!countFeasible(r)) repairCounts(r);
    if (alpha > 0) {
        repairTasks(r);
        if (!countFeasible(r)) repairCounts(r);
    }
    lambdaCnt = lamSave, wAlpha = waSave, wCost = wcSave, l1Cost = l1Save, lvTarget = lvSave;
    poolAddAsg(r.asg);
    if (countFeasible(r)) {
        double obj = trueObjective(r);
        runBestObj = max(runBestObj, obj);
        if (obj > bestObj + 1e-9) bestObj = obj, bestAsg = r.asg;
    }
    // tight count window: drive each new best to one exact task level (bounded share of the time)
    if (epOn) {
        double t = elapsed();
        if (t < searchEnd - 1.0 && epTime <= 0.08 * t + 0.3 && fabs(bestObj - epLastObj) > 1e-9) {
            epLastObj = bestObj;
            lambdaCnt = 1e18, wAlpha = 1, wCost = 1, l1Cost = 0, lvTarget = -1;
            State b = fromAsg(bestAsg);
            if (exactPolish(b, min(searchEnd - 0.5, t + max(0.5, 0.01 * searchEnd)))) {
                double obj = trueObjective(b);
                runBestObj = max(runBestObj, obj);
                poolAddAsg(b.asg);
                if (obj > bestObj + 1e-9) bestObj = obj, bestAsg = b.asg;
                epLastObj = bestObj;
            }
            lambdaCnt = lamSave, wAlpha = waSave, wCost = wcSave, l1Cost = l1Save, lvTarget = lvSave;
        }
    }
}

// Objective of a state after the repairs considerBest applies (true weights); asgOut gets that state.
double repairedValue(const State& st, vector<int>& asgOut) {
    double best = -1e300;
    if (countFeasible(st)) best = trueObjective(st), asgOut = st.asg;
    double lamSave = lambdaCnt, waSave = wAlpha, wcSave = wCost, l1Save = l1Cost;
    int lvSave = lvTarget;
    lambdaCnt = 1e18, wAlpha = 1, wCost = 1, l1Cost = 0, lvTarget = -1;
    State r = st;
    if (!countFeasible(r)) repairCounts(r);
    if (alpha > 0) {
        repairTasks(r);
        if (!countFeasible(r)) repairCounts(r);
    }
    lambdaCnt = lamSave, wAlpha = waSave, wCost = wcSave, l1Cost = l1Save, lvTarget = lvSave;
    if (countFeasible(r)) {
        double v = trueObjective(r);
        if (v > best) best = v, asgOut = r.asg;
    }
    return best;
}

bool macroMove(State& st, double T) {
    static const bool noLevel = false;
    static const int ruinShare = 3;  // out of 10
    if (irand(10) < ruinShare) {  // ruin a region around an office and greedily recreate it
        int o = irand(K);
        int R = min(n, 10 + irand(51));
        return compound(st, T, [&] {
            vector<int> region(nearOrder[o].begin(), nearOrder[o].begin() + R);
            doUnassign(st, region);
            sortSitesByKey(region.begin(), region.end(), true, [&](int a) { return rew[a] - dist[nearOff[a][0]][a]; });
            doRefill(st, region);
            return true;
        });
    }
    int kind = irand(alpha > 0 && !noLevel ? 7 : 5);
    if (kind == 4) {  // move a whole zone from an open office to an empty one
        int p = pickOpen(st), q = pickEmpty(st);
        if (p < 0 || q < 0) return false;
        return compound(st, T, [&] {
            vector<int> sites = st.mem[p];
            doUnassign(st, sites);
            Change c;
            int moved = 0, chk = 0;
            for (int s : sites) {
                if (opLate(chk)) break;
                c = {s, st.asg[s], q};
                moved += tryChange(st, &c, 1, FORCE_T);
            }
            doRefill(st, sites);
            return moved > 0;
        });
    }
    if (kind >= 5) {
        int d = 1 + irand(3);
        if (kind == 6) d = -d;
        return compound(st, T, [&] { return doLevel(st, d); });
    }
    if (kind == 0) {  // open an empty office
        int q = pickEmpty(st);
        if (q < 0) return false;
        return compound(st, T, [&] { return doOpen(st, q) > 0; });
    }
    if (kind == 1) {  // close an office, redistribute its sites
        int p = pickOpen(st);
        if (p < 0) return false;
        return compound(st, T, [&] {
            vector<int> sites = st.mem[p];
            doUnassign(st, sites);
            doRefill(st, sites);
            return true;
        });
    }
    if (kind == 2) {  // drop one skill from an office (frees a worker), refill elsewhere
        int p = pickOpen(st);
        if (p < 0) return false;
        int sk = pickSkill(st.omask[p]);
        if (sk < 0) return false;
        return compound(st, T, [&] {
            vector<int> sites = sitesWithSkill(st, p, sk);
            int before = st.cnt[p];
            doUnassign(st, sites);
            doTopUp(st, p, before);
            doRefill(st, sites);
            return true;
        });
    }
    // drop a skill from an office and open an empty office with the freed worker
    int p = pickOpen(st), q = pickEmpty(st);
    if (p < 0 || q < 0) return false;
    int sk = pickSkill(st.omask[p]);
    if (sk < 0) return false;
    return compound(st, T, [&] {
        vector<int> sites = sitesWithSkill(st, p, sk);
        int before = st.cnt[p];
        doUnassign(st, sites);
        doTopUp(st, p, before);
        if (doOpen(st, q) == 0) return false;
        doRefill(st, sites);
        return true;
    });
}

// ---------------------------------------------------------------- power-diagram construction
// Partition sites into Voronoi/power cells of a set of open offices (cells are convex and
// disjoint, so zones built inside them never conflict), then fill each cell greedily.
string validateFull(const State& st);
vector<double> genX, genY;  // power-cell generators (empty: the office locations)
inline double gX(int o) { return genX.empty() ? px[n + o] : genX[o]; }
inline double gY(int o) { return genY.empty() ? py[n + o] : genY[o]; }
string validateBuilt(const State& st);
// outSt (optional): receives fromAsg(result) when it was built here (*built = true)
vector<int> powerInit(vector<int> open, const vector<double>& w, State* outSt = nullptr, bool* built = nullptr) {
    if (built) *built = false;
    vector<int> asg(n, -1);
    // drop offices sharing a location with an earlier one
    {
        vector<int> keep;
        for (int o : open) {
            bool dup = false;
            for (int q : keep)
                if (px[n + o] == px[n + q] && py[n + o] == py[n + q]) dup = true;
            if (!dup) keep.push_back(o);
        }
        open.swap(keep);
    }
    // free generators: an office must lie inside its own power cell (then its zone, the hull of
    // the office and sites of the cell, stays inside the convex cell); drop offices that do not
    while (!genX.empty() && !open.empty()) {
        int bad = -1;
        for (int o : open) {
            double x = px[n + o], y = py[n + o];
            double own = pow(x - gX(o), 2) + pow(y - gY(o), 2) - w[o];
            for (int q : open)
                if (q != o && pow(x - gX(q), 2) + pow(y - gY(q), 2) - w[q] <= own) {
                    bad = o;
                    break;
                }
            if (bad >= 0) break;
        }
        if (bad < 0) break;
        open.erase(find(open.begin(), open.end(), bad));
    }
    if (open.empty()) return asg;
    vector<vector<int>> cell(K);
    for (int s = 0; s < n; s++) {
        int bo = -1;
        double bv = 1e300;
        for (int o : open) {
            double dx = px[s] - gX(o), dy = py[s] - gY(o);
            double v = dx * dx + dy * dy - w[o];
            if (v < bv) bv = v, bo = o;
        }
        if (rew[s] - dist[bo][s] > 0) cell[bo].push_back(s);
    }
    // skills: offices in order of their cell value take sites while workers allow
    vector<double> cellVal(K, 0);
    for (int o : open) {
        sortSitesByKey(cell[o].begin(), cell[o].end(), true, [&](int a) { return rew[a] - dist[o][a]; });
        for (int i = 0; i < (int)cell[o].size() && i < maxSize[o]; i++) cellVal[o] += rew[cell[o][i]] - dist[o][cell[o][i]];
    }
    sort(open.begin(), open.end(), [&](int a, int b) { return cellVal[a] > cellVal[b]; });
    vector<int> used(NS, 0);
    vector<vector<int>> pick(K);
    for (int o : open) {
        Mask have;
        for (int s : cell[o]) {
            if ((int)pick[o].size() >= maxSize[o]) break;
            Mask needNew = smask[s] & ~have;
            bool ok = true;
            for (int k = 0; k < NS && ok; k++)
                if (needNew[k] && used[k] >= availSkill[k]) ok = false;
            if (!singleSkillWorkers && needNew.any()) ok = false;  // keep it simple for multi-skill workers
            if (!ok) continue;
            for (int k = 0; k < NS; k++)
                if (needNew[k]) used[k]++;
            have |= needNew;
            pick[o].push_back(s);
        }
    }
    // common count window [lo, lo + A] (a window start seen before gives the same value again and
    // cannot pass the strict test a second time: each distinct start is evaluated once)
    int bestLo = -1;
    double bestVal = 0;
    static vector<int> loSeen;
    static int loEpoch = 0;
    if ((int)loSeen.size() < n + 1) loSeen.assign(n + 1, 0);
    if (++loEpoch == INT32_MAX) fill(loSeen.begin(), loSeen.end(), 0), loEpoch = 1;
    for (int o0 : open) {
        int lo = pick[o0].size();
        if (lo == 0 || loSeen[lo] == loEpoch) continue;
        loSeen[lo] = loEpoch;
        double val = 0;
        for (int o : open) {
            if ((int)pick[o].size() < lo) continue;
            int keep = min((int)pick[o].size(), lo + A);
            const int* pk = pick[o].data();
            const double* dO = dist[o].data();
            for (int i = 0; i < keep; i++) val += rew[pk[i]] - dO[pk[i]];
            val -= ocost[o];
        }
        if (val > bestVal) bestVal = val, bestLo = lo;
    }
    if (bestLo < 0) return asg;
    for (int o : open) {
        if ((int)pick[o].size() < bestLo) continue;
        int keep = min((int)pick[o].size(), bestLo + A);
        for (int i = 0; i < keep; i++) asg[pick[o][i]] = o;
    }
    // safety: cell boundaries can put a point on two hulls; fall back to empty then
    {
        State st = fromAsg(asg);
        if (!validateBuilt(st).empty()) asg.assign(n, -1);
        else if (outSt) *outSt = std::move(st), *built = true;
    }
    return asg;
}

int nearOffOf(int a) {
    int b = -1;
    double bd = 1e300;
    for (int q = 0; q < K; q++) {
        if (q == a) continue;
        double d2 = pow(px[n + a] - px[n + q], 2) + pow(py[n + a] - py[n + q], 2) + urand() * 1e-12;
        if (irand(3) == 0) d2 *= 1 + urand();  // some randomness among near ones
        if (d2 < bd) bd = d2, b = q;
    }
    return b;
}

// Random open set with plain Voronoi cells.
vector<int> randomPowerInit() {
    double p = 0.3 + 0.7 * urand();
    vector<int> open;
    for (int o = 0; o < K; o++)
        if (urand() < p) open.push_back(o);
    if (open.empty()) open.push_back(irand(K));
    return powerInit(open, vector<double>(K, 0.0));
}

// ---------------------------------------------------------------- fan (wedge) construction
// Offices clustered far outside the sites: the best zones are thin radial wedges, one office per
// wedge, ordered across the view direction. Sites are sorted by angle around an apex P behind the
// office cluster; an exact DP over G candidate angular cuts picks an ordered sequence of disjoint
// wedges (convex cones, so zones inside them never conflict), each holding one office whose value
// is its best <= maxSize profitable sites in the wedge minus its cost. Skills, count window and
// task balance are fixed afterwards; the result is always fully validated.
vector<int> fanLastCounts;  // zone sizes chosen by the last fanInit before the count window
struct FanGeo {
    double px, py, base;  // apex and the direction mapped to angle 0
};
inline double fanAngle(double x, double y, const FanGeo& f) {
    double a = atan2(y - f.py, x - f.px) - f.base;
    while (a > M_PI) a -= 2 * M_PI;
    while (a <= -M_PI) a += 2 * M_PI;
    return a;
}
// Returns the assignment (all -1 on failure or when estimated work exceeds opBudget).
// *ops receives the work estimate, *val the true objective (-1e300 if unusable).
// Zones hold between cLo and cHi sites (a count window for small maxDifference; 0 / n = free).
vector<int> fanInit(const FanGeo& f, int G, double opBudget, double* ops, double* val, int cLo, int cHi) {
    vector<int> none(n, -1);
    *val = -1e300;
    *ops = 0;
    // candidate sites: every needed skill has some worker, profitable for some office
    vector<pair<double, int>> sa;
    for (int s = 0; s < n; s++) {
        bool ok = true;
        for (int k = 0; k < NS && ok; k++)
            if (smask[s][k] && availSkill[k] == 0) ok = false;
        if (!ok) continue;
        bool prof = false;
        for (int o = 0; o < K && !prof; o++)
            if (rew[s] - dist[o][s] > 0) prof = true;
        if (prof) sa.push_back({fanAngle(px[s], py[s], f), s});
    }
    int m = sa.size();
    if (m == 0) return none;
    sort(sa.begin(), sa.end());
    vector<double> oang(K);
    double amin = sa[0].first, amax = sa[m - 1].first;
    for (int o = 0; o < K; o++) {
        oang[o] = fanAngle(px[n + o], py[n + o], f);
        amin = min(amin, oang[o]), amax = max(amax, oang[o]);
    }
    // cuts in the widest angular gap near each quantile (keeps sites well away from wedge edges)
    vector<double> cut;
    cut.push_back(amin - 1e-7);
    int lastI = 0;
    G = max(2, min(G, m));
    for (int j = 1; j < G; j++) {
        int q = (int)((long long)j * m / G);
        int bi = -1;
        double bg = 0;
        for (int i = max(1, q - 3); i <= min(m - 1, q + 3); i++) {
            double g = sa[i].first - sa[i - 1].first;
            if (i > lastI && g > bg) bg = g, bi = i;
        }
        if (bi < 0 || bg < 1e-12) continue;
        cut.push_back(0.5 * (sa[bi - 1].first + sa[bi].first));
        lastI = bi;
    }
    cut.push_back(amax + 1e-7);
    int nc = cut.size();
    vector<int> bstart(nc);  // first sorted site with angle > cut[j]
    for (int j = 0, i = 0; j < nc; j++) {
        while (i < m && sa[i].first <= cut[j]) i++;
        bstart[j] = i;
    }
    vector<int> obk(K, -1);  // bucket holding the office: cut[ia] < angle < cut[ia + 1]
    double est = 0;
    for (int o = 0; o < K; o++) {
        if (maxSize[o] <= 0) continue;
        int ia = int(upper_bound(cut.begin(), cut.end(), oang[o]) - cut.begin()) - 1;
        if (ia < 0 || ia >= nc - 1 || oang[o] == cut[ia]) continue;
        obk[o] = ia;
        for (int a = 0; a <= ia; a++) est += m - bstart[a];
    }
    *ops = est;
    if (est > opBudget) return none;
    // V[a][b]: best value over offices of the wedge (cut[a], cut[b])
    vector<double> V((size_t)nc * nc, -1e300);
    vector<int> Vo((size_t)nc * nc, -1);
    vector<double> pr(m);
    vector<int> byRank, rk;
    vector<double> rval;
    vector<uint64_t> topBits;
    const double maxW = M_PI - 1e-6;  // wedges must stay convex
    for (int o = 0; o < K; o++) {
        int ia = obk[o];
        if (ia < 0) continue;
        for (int i = 0; i < m; i++) pr[i] = rew[sa[i].second] - dist[o][sa[i].second];
        int cap = min(maxSize[o], cHi);
        if (cap < cLo) continue;
        if (cap <= 0) continue;  // no site fits: the rank bitset below needs cap >= 1 (th >= 0)
        // Streaming "sum of the cap largest positive values" per start cut a. The top set is kept as a
        // bitset over ranks (value ascending, later index first among equal values), so its minimum
        // (the heap top of a min-heap) is the lowest set bit and only moves up: a new value replaces
        // it exactly when the min-heap would (strictly larger value), and tot gets the same additions.
        int npos = 0;
        for (int i = 0; i < m; i++) npos += pr[i] > 0;
        byRank.resize(npos);
        npos = 0;
        for (int i = 0; i < m; i++)
            if (pr[i] > 0) byRank[npos++] = i;
        sort(byRank.begin(), byRank.end(), [&](int x, int y) { return pr[x] < pr[y] || (pr[x] == pr[y] && x > y); });
        rk.assign(m, -1);
        rval.resize(npos);
        for (int r = 0; r < npos; r++) rk[byRank[r]] = r, rval[r] = pr[byRank[r]];
        const size_t nw = (size_t)(npos + 63) / 64;
        topBits.resize(nw);
        uint64_t* tb = topBits.data();
        for (int a = 0; a <= ia; a++) {
            if (cut[ia + 1] - cut[a] >= maxW) continue;
            fill(topBits.begin(), topBits.end(), 0);
            double tot = 0;
            int cnt = 0, th = -1;
            int i = bstart[a];
            for (int b = a + 1; b < nc; b++) {
                if (cut[b] - cut[a] >= maxW) break;
                for (; i < bstart[b]; i++) {
                    int r = rk[i];
                    if (r < 0) continue;  // value <= 0
                    if (cnt < cap) {
                        tb[r >> 6] |= 1ULL << (r & 63);
                        tot += rval[r];
                        if (++cnt == cap) {  // full: the minimum is the lowest rank held
                            size_t w = 0;
                            while (!tb[w]) w++;
                            th = (int)(w * 64 + __builtin_ctzll(tb[w]));
                        }
                    } else if (r > th) {
                        tot += rval[r] - rval[th];
                        tb[th >> 6] &= ~(1ULL << (th & 63));
                        tb[r >> 6] |= 1ULL << (r & 63);
                        // next held rank above th (r itself at the latest)
                        size_t w = (size_t)th >> 6;
                        uint64_t bits = tb[w] & (~0ULL << (th & 63));
                        while (!bits) bits = tb[++w];
                        th = (int)(w * 64 + __builtin_ctzll(bits));
                    }
                }
                if (b > ia && cnt >= cLo) {
                    double v = tot - ocost[o];
                    size_t id = (size_t)a * nc + b;
                    if (v > 0 && v > V[id]) V[id] = v, Vo[id] = o;
                }
            }
        }
    }
    // DP over cuts: g[b] = best total of wedges ending at or before cut b
    vector<double> g(nc, 0.0);
    vector<int> back(nc, -1);
    for (int b = 1; b < nc; b++) {
        g[b] = g[b - 1];
        for (int a = 0; a < b; a++) {
            double v = V[(size_t)a * nc + b];
            if (v > -1e299 && g[a] + v > g[b]) g[b] = g[a] + v, back[b] = a;
        }
    }
    struct Z {
        int o, a, b;
        double v;
    };
    vector<Z> zs;
    for (int b = nc - 1; b > 0;) {
        if (back[b] < 0) {
            b--;
            continue;
        }
        int a = back[b];
        zs.push_back({Vo[(size_t)a * nc + b], a, b, V[(size_t)a * nc + b]});
        b = a;
    }
    if (zs.empty()) return none;
    // skills: zones in value order take their best sites while workers allow
    sort(zs.begin(), zs.end(), [](const Z& x, const Z& y) { return x.v > y.v; });
    vector<int> used(NS, 0);
    vector<Mask> masks;
    vector<vector<int>> pick(K);
    for (const Z& z : zs) {
        int o = z.o;
        vector<pair<double, int>> c;
        for (int i = bstart[z.a]; i < bstart[z.b]; i++) {
            int s = sa[i].second;
            double v = rew[s] - dist[o][s];
            if (v > 0) c.push_back({-v, s});
        }
        sort(c.begin(), c.end());
        Mask have;
        double tot = 0;
        vector<int> pk;
        for (auto& cv : c) {
            if ((int)pk.size() >= min(maxSize[o], cHi)) break;
            int s = cv.second;
            Mask needNew = smask[s] & ~have;
            if (needNew.any()) {
                bool ok = true;
                if (singleSkillWorkers) {
                    for (int k = 0; k < NS && ok; k++)
                        if (needNew[k] && used[k] >= availSkill[k]) ok = false;
                } else {
                    masks.push_back(have | needNew);
                    ok = assignWorkers(masks, false);
                    masks.pop_back();
                }
                if (!ok) continue;
                have |= needNew;
            }
            pk.push_back(s);
            tot -= cv.first;
        }
        if (pk.empty() || (int)pk.size() < cLo || tot - ocost[o] <= 0) continue;
        for (int k = 0; k < NS; k++)
            if (have[k]) used[k]++;
        if (have.any()) masks.push_back(have);
        pick[o] = pk;  // sorted by profit, best first
    }
    fanLastCounts.clear();
    for (const Z& z : zs)
        if (!pick[z.o].empty()) fanLastCounts.push_back(pick[z.o].size());
    // common count window [lo, lo + A]
    int bestLo = -1;
    double bestVal = 0;
    for (const Z& z0 : zs) {
        int lo = pick[z0.o].size();
        if (lo == 0) continue;
        double v = 0;
        for (const Z& z : zs) {
            int c = pick[z.o].size();
            if (c < lo) continue;
            int keep = min(c, lo + A);
            for (int i = 0; i < keep; i++) v += rew[pick[z.o][i]] - dist[z.o][pick[z.o][i]];
            v -= ocost[z.o];
        }
        if (v > bestVal) bestVal = v, bestLo = lo;
    }
    if (bestLo < 0) return none;
    vector<int> asg(n, -1);
    for (const Z& z : zs) {
        int c = pick[z.o].size();
        if (c < bestLo) continue;
        int keep = min(c, bestLo + A);
        for (int i = 0; i < keep; i++) asg[pick[z.o][i]] = z.o;
    }
    if (poolOn) {  // wedges before the count window, plus profit prefixes at the window sizes
        for (const Z& z : zs) {
            const vector<int>& pk = pick[z.o];
            if (pk.empty()) continue;
            poolAddZone(z.o, pk);
            int c = pk.size();
            for (int len : {bestLo, bestLo + A / 2, bestLo + A})
                if (len > 0 && len < c) poolAddZone(z.o, vector<int>(pk.begin(), pk.begin() + len));
        }
        poolAddAsg(asg);
    }
    State st = fromAsg(asg);
    if (alpha > 0) {
        double lamSave = lambdaCnt, waSave = wAlpha, wcSave = wCost;
        lambdaCnt = 1e18, wAlpha = 1, wCost = 1;
        repairTasks(st);
        if (!countFeasible(st)) repairCounts(st);
        lambdaCnt = lamSave, wAlpha = waSave, wCost = wcSave;
    }
    poolAddAsg(st.asg);
    string err = validateFull(st);
    if (szDebug) fprintf(stderr, "fan: cuts=%d zones=%zu dp=%.4f obj=%.4f %s\n", nc, zs.size(), g[nc - 1], countFeasible(st) ? trueObjective(st) : -1.0, err.c_str());
    if (!err.empty() || !countFeasible(st)) return none;
    *val = trueObjective(st);
    return st.asg;
}

// ---------------------------------------------------------------- triangulation fans
// Offices in convex position (e.g. on a circle). A merge triangulation of the office polygon
// between the chains a->b (ccw) and a->b (cw) gives every triangle to its lone vertex, so each
// zone is a fan from an office across to the opposite chain. This fits distance rows whose cheap
// sites lie on the far side (instance3: row k is the distance from the opposite office).
// Zones are chosen by DP over merge sequences (per task level T), then filled greedily.
// lazy chain of 2-way merges for the triangulation fan values: level l = merge(level l - 1, A_l)
// (descending (profit, tasks); on ties level l - 1 first, as std::merge(..., greater) does)
struct LazyLevel {
    vector<pair<double, int>> buf;
    size_t pa = 0, pb = 0;
    const vector<pair<double, int>>* A = nullptr;
    bool done = false;
};
LazyLevel lzl[400];
static bool lazyExtend(int l) {
    LazyLevel& L = lzl[l];
    if (L.done) return false;
    const pair<double, int>* b = nullptr;
    if (l > 1) {
        LazyLevel& P = lzl[l - 1];
        if (L.pa >= P.buf.size()) lazyExtend(l - 1);
        if (L.pa < P.buf.size()) b = &P.buf[L.pa];
    }
    const pair<double, int>* a = L.pb < L.A->size() ? &(*L.A)[L.pb] : nullptr;
    if (!a && !b) {
        L.done = true;
        return false;
    }
    if (a && (!b || *b < *a)) L.buf.push_back(*a), L.pb++;
    else L.buf.push_back(*b), L.pa++;
    return true;
}
vector<int> triSearch(double endTime, double extEnd, double capEnd, double extCap, double rival, double* outVal) {
    struct CacheScope {  // band tables are cached for this search only
        CacheScope() { bandCacheOn = true; }
        ~CacheScope() {
            if (szDebug) fprintf(stderr, "tri band cache: %lld hits, %lld misses, %zu words\n", bcHits, bcMiss, bcWords);
            bandCacheOn = false;
            bandCacheClear();
        }
    } cacheScope;
    vector<int> none(n, -1);
    // Work-based budget (the result must not depend on CPU speed): the mode-0 sweep over all task
    // levels T (and its refinement) always completes while the triangulation is competitive (or has
    // no plan yet), and the extension makes at least extMin tries; only the hard caps capEnd / extCap
    // (fractions of the run) stop them early. On a slow or busy CPU a fixed wall-clock slice ended
    // after the first few levels (or before any plan), and a level later in the list may be the best.
    bool haveRes = false;
    double bestV = -1e300;
    int phase = 1, tries = 0;  // phase 1: mode-0 sweep, 2: mode-1 sweep, 3: extension
    static const int extMin = 8;
    static const bool triWork = true;
    auto bound = [&]() {
        if (phase == 3) return triWork && tries < extMin ? max(endTime, extCap) : endTime;
        if (!haveRes) return max(endTime, capEnd);
        if (triWork && phase == 1 && bestV >= 0.95 * rival) return max(endTime, capEnd);
        return endTime;
    };
    auto over = [&]() { return elapsed() > bound(); };
    *outVal = -1e300;
    if (n == 0 || K < 4) return none;
    vector<int> pts;
    for (int o = 0; o < K; o++)
        if (maxSize[o] > 0) pts.push_back(n + o);
    vector<int> hv;
    {
        vector<int> tmp = pts;
        buildHull(tmp, hv);  // ccw, strictly convex, deduplicated
    }
    int m = hv.size();
    int distinct;
    {
        vector<pair<double, double>> xy;
        for (int p : pts) xy.push_back({px[p], py[p]});
        sort(xy.begin(), xy.end());
        distinct = unique(xy.begin(), xy.end()) - xy.begin();
    }
    if (szDebug) fprintf(stderr, "tri: hull %d of %d distinct offices t=%.2f end=%.2f ext=%.2f\n", m, distinct, elapsed(), endTime, extEnd);
    if (m < 6 || m > 400 || m < 0.85 * distinct || (long long)m * n > 12000000LL) return none;
    // among offices sharing a hull vertex position use the first (cheapest is not tracked)
    vector<int> ho(m);
    for (int j = 0; j < m; j++) ho[j] = hv[j] - n;
    double x0 = 1e300, x1 = -1e300, y0 = 1e300, y1 = -1e300;
    for (int i = 0; i < NP; i++) x0 = min(x0, px[i]), x1 = max(x1, px[i]), y0 = min(y0, py[i]), y1 = max(y1, py[i]);
    const double margin = 20 * EPS;  // stay clearly away from rays (hull covers are conservative)
    auto side = [&](int a, int b, int s) {  // signed distance-like value of s from line a->b
        double dx = px[b] - px[a], dy = py[b] - py[a];
        double L = sqrt(dx * dx + dy * dy);
        return (dx * (py[s] - py[a]) - dy * (px[s] - px[a])) / max(L, 1e-300);
    };
    vector<char> okSite(n, 1);
    for (int s = 0; s < n; s++)
        for (int k = 0; k < NS; k++)
            if (smask[s][k] && availSkill[k] == 0) okSite[s] = 0;
    long long minTask = LLONG_MAX;  // fewest tasks of any usable site (0: some site has none)
    for (int s = 0; s < n; s++)
        if (okSite[s]) minTask = min(minTask, (long long)ntask[s]);
    // sites outside the office polygon: the edge whose outer perpendicular slab holds them (-1: inside or
    // in a gap at a vertex); slabs of a convex polygon are disjoint, so each such site counts for one fan only.
    // slabPos: relative position along that edge (0..1), used to drop sites near vertices if hulls clash
    vector<int> slab(n, -1);
    vector<double> slabPos(n, 0.5);
    vector<char> outside(n, 0);
    for (int s = 0; s < n; s++) {
        for (int e = 0; e < m; e++) {
            int a = hv[e], b = hv[(e + 1) % m];
            if (side(a, b, s) >= -margin) continue;
            outside[s] = 1;
            double dx = px[b] - px[a], dy = py[b] - py[a], L2 = dx * dx + dy * dy;
            double t = ((px[s] - px[a]) * dx + (py[s] - py[a]) * dy) / max(L2, 1e-300);
            double tm = margin / sqrt(max(L2, 1e-300));
            if (t > tm && t < 1 - tm) slab[s] = e, slabPos[s] = t;
        }
    }
    // sec[j*n+s]: edge e (v_e -> v_e+1) such that s lies strictly inside the angle at v_j between rays to v_e, v_e+1
    auto rawSec = [&](int j, int s) {
        int v = hv[j], vn = hv[(j + 1) % m], vp = hv[(j + m - 1) % m];
        if (side(v, vn, s) <= margin || side(v, vp, s) >= -margin) return -1;
        int lo = 1, hi = m - 1;  // side(v, v_{j+lo}) > 0, side(v, v_{j+hi}) < 0
        while (hi - lo > 1) {
            int mid = (lo + hi) / 2;
            if (side(v, hv[(j + mid) % m], s) > 0) lo = mid;
            else hi = mid;
        }
        if (side(v, hv[(j + lo) % m], s) <= margin || side(v, hv[(j + hi) % m], s) >= -margin) return -1;
        return (j + lo) % m;
    };
    // mode 0: the DP table leaves out sites in vertex gaps (they would count for several fans) and gives
    // an outside site only to the fan over the edge whose slab holds it; the final fill still takes a
    // gap site when exactly one chosen zone contains it. mode 1: any wedge holding an outside site counts it.
    typedef pair<double, int> PT;  // (profit, tasks)
    vector<int> sec((size_t)m * n, -1);
    vector<vector<PT>> trl((size_t)m * m);  // per apex j and edge e: profitable sites, profit desc
    auto buildTables = [&](int mode) {
        fill(sec.begin(), sec.end(), -1);
        for (int j = 0; j < m; j++) {
            for (int s = 0; s < n; s++) {
                if (!okSite[s] || (mode == 0 && outside[s] && slab[s] < 0)) continue;
                int e = rawSec(j, s);
                if (e >= 0 && (mode == 1 || slab[s] < 0 || slab[s] == e)) sec[(size_t)j * n + s] = e;
            }
            if (over()) return false;
        }
        for (int j = 0; j < m; j++) {
            int o = ho[j];
            for (int e = 0; e < m; e++) trl[(size_t)j * m + e].clear();
            for (int s = 0; s < n; s++) {
                int e = sec[(size_t)j * n + s];
                if (e < 0) continue;
                double pr = rew[s] - dist[o][s];
                if (pr > 0) trl[(size_t)j * m + e].push_back({pr, ntask[s]});
            }
            for (int e = 0; e < m; e++) sort(trl[(size_t)j * m + e].begin(), trl[(size_t)j * m + e].end(), greater<PT>());
        }
        return true;
    };
    auto inTri = [&](int a, int b, int c, int s) {
        double d1 = side(a, b, s), d2 = side(b, c, s), d3 = side(c, a, s);
        return (d1 > margin && d2 > margin && d3 > margin) || (d1 < -margin && d2 < -margin && d3 < -margin);
    };
    const long long INF_T = (long long)4e18;
    double triGam = 1.0;  // weight of the per-zone task shortfall in the DP zone values
    auto zval = [&](int o, const vector<PT>& L, long long T) {
        double v = 0;
        long long got = 0;
        int c = 0, cap = maxSize[o];
        for (const PT& p : L) {
            if (c >= cap) break;
            if (got + p.second > T) continue;
            got += p.second, v += p.first, c++;
        }
        if (alpha > 0 && T < INF_T) v -= triGam * alpha * (double)(T - got);
        v -= ocost[o];
        return max(0.0, v);
    };
    int Lm = min(m - 2, 16);
    // axes: (a, b) roughly opposite
    vector<pair<int, int>> axes;
    {
        int step = m > 64 ? (m + 31) / 32 : 1;
        for (int a = 0; a < m; a += step)
            for (int d = -1; d <= 1; d++) {
                if (m > 64 && d != 0) continue;
                int b = (a + m / 2 + d + m) % m;
                int p = (b - a + m) % m, q = m - p;
                if (p < 2 || q < 2) continue;
                pair<int, int> ax = {min(a, b), max(a, b)};
                if (find(axes.begin(), axes.end(), ax) == axes.end()) axes.push_back(ax);
            }
    }
    long long totT = 0;
    for (int s = 0; s < n; s++)
        if (okSite[s]) totT += ntask[s];
    vector<long long> Ts;
    if (alpha > 0 && totT > 0) {
        double avgT = (double)totT / m;
        for (double f : {2.0, 3.0, 1.5, 4.0, 1.0, 2.5, 5.0, 0.75, 6.0, 0.5}) Ts.push_back(max(1LL, (long long)llround(avgT * f)));
    } else
        Ts.push_back(INF_T);
    vector<double> F((size_t)m * m * Lm);
    struct Zone {
        int j;       // apex hull index
        int e, len;  // fan over edges e..e+len-1 (len 0: explicit triangle with vertices j, e, len2)
        int t1, t2;  // triangle vertices for len == 0
        double v;
    };
    vector<int> bestAsg_(n, -1);
    long long bestT = -1;
    vector<PT> cur, nxt;
    vector<int> cnt(n);
    auto evalT = [&](long long T) -> double {
        // fan values: zval of the merge of the edge lists e..e+len-1 for len = 1, 2, ... The merges
        // are lazy (a chain of 2-way merges, each level materialized only as far as some zval read
        // it; same order as std::merge), and zval stops once the cap is reached or no task fits.
        for (int j = 0; j < m; j++) {
            int o = ho[j];
            const int cap = maxSize[o];
            for (int t0 = 1; t0 <= m - 2; t0++) {
                int e = (j + t0) % m;
                for (int len = 1; len <= Lm && t0 + len - 1 <= m - 2; len++) {
                    LazyLevel& L = lzl[len];
                    L.buf.clear(), L.pa = 0, L.pb = 0, L.done = false;
                    L.A = &trl[(size_t)j * m + (e + len - 1) % m];
                    double v = 0;
                    long long got = 0;
                    int c = 0;
                    if (cap > 0)
                        for (size_t k = 0;; k++) {
                            if (k >= L.buf.size() && !lazyExtend(len)) break;
                            const PT& p = L.buf[k];
                            if (got + p.second > T) continue;
                            got += p.second, v += p.first, c++;
                            if (c >= cap || T - got < minTask) break;
                        }
                    if (alpha > 0 && T < INF_T) v -= triGam * alpha * (double)(T - got);
                    v -= ocost[o];
                    F[((size_t)j * m + e) * Lm + len - 1] = max(0.0, v);
                }
            }
            if (over()) return -1e300;
        }
        auto triVal = [&](int a, int b, int c, vector<PT>& L) {
            L.clear();
            int o = ho[a];
            for (int s = 0; s < n; s++)
                if (okSite[s] && inTri(hv[a], hv[b], hv[c], s)) {
                    double pr = rew[s] - dist[o][s];
                    if (pr > 0) L.push_back({pr, ntask[s]});
                }
            sort(L.begin(), L.end(), greater<PT>());
            return zval(o, L, T);
        };
        double bestDP = -1e300;
        vector<Zone> bestZ;
        vector<pair<double, vector<Zone>>> topZ;  // best DP partitions over the axes (distinct)
        static const int triTop = 3;
        vector<double> V;
        vector<int> BK;
        vector<Zone> BZ;
        for (auto ax : axes) {
            if (over()) break;
            int a = ax.first, b = ax.second;
            int p = (b - a + m) % m, q = m - p;
            auto U = [&](int i) { return (a + i) % m; };
            auto Lc = [&](int j) { return (a - j + m) % m; };
            int ns = p * q * 3;
            V.assign(ns, -1e300);
            BK.assign(ns, -1);
            BZ.assign(ns, Zone{0, 0, 0, 0, 0, 0});
            auto id = [&](int i, int j, int f) { return (i * q + j) * 3 + f; };
            double v0 = triVal(a, U(1), Lc(1), cur);
            V[id(1, 1, 2)] = v0;
            for (int i = 1; i <= p - 1; i++)
                for (int j = 1; j <= q - 1; j++)
                    for (int f = 0; f < 3; f++) {
                        double cv = V[id(i, j, f)];
                        if (cv < -1e299) continue;
                        if (f != 0) {  // apex L_j over U_i..U_i2
                            int ap = Lc(j), e = U(i);
                            for (int i2 = i + 1; i2 <= min(p - 1, i + Lm); i2++) {
                                double nv = cv + F[((size_t)ap * m + e) * Lm + (i2 - i) - 1];
                                int k = id(i2, j, 0);
                                if (nv > V[k]) V[k] = nv, BK[k] = id(i, j, f), BZ[k] = Zone{ap, e, i2 - i, 0, 0, 0};
                            }
                        }
                        if (f != 1) {  // apex U_i over L_j..L_j2 (edges ccw from L_j2)
                            int ap = U(i);
                            for (int j2 = j + 1; j2 <= min(q - 1, j + Lm); j2++) {
                                int e = Lc(j2);
                                double nv = cv + F[((size_t)ap * m + e) * Lm + (j2 - j) - 1];
                                int k = id(i, j2, 1);
                                if (nv > V[k]) V[k] = nv, BK[k] = id(i, j, f), BZ[k] = Zone{ap, e, j2 - j, 0, 0, 0};
                            }
                        }
                    }
            int bf = -1;
            for (int f = 0; f < 3; f++)
                if (V[id(p - 1, q - 1, f)] > -1e299 && (bf < 0 || V[id(p - 1, q - 1, f)] > V[id(p - 1, q - 1, bf)])) bf = f;
            if (bf < 0) continue;
            double ve = triVal(b, U(p - 1), Lc(q - 1), cur);
            double tot = V[id(p - 1, q - 1, bf)] + ve;
            if (topZ.empty() || (int)topZ.size() < triTop || tot > topZ.back().first) {
                vector<Zone> zl;
                zl.push_back(Zone{a, 0, 0, U(1), Lc(1), v0});
                zl.push_back(Zone{b, 0, 0, U(p - 1), Lc(q - 1), ve});
                for (int k = id(p - 1, q - 1, bf); BK[k] >= 0; k = BK[k]) {
                    Zone z = BZ[k];
                    z.v = F[((size_t)z.j * m + z.e) * Lm + z.len - 1];
                    zl.push_back(z);
                }
                auto key = [&](const vector<Zone>& v) {
                    vector<tuple<int, int, int, int, int>> r;
                    for (auto& z : v)
                        if (z.v > 0) r.push_back({z.j, z.e, z.len, z.len ? 0 : min(z.t1, z.t2), z.len ? 0 : max(z.t1, z.t2)});
                    sort(r.begin(), r.end());
                    return r;
                };
                bool dup = false;
                for (auto& tz : topZ)
                    if (key(tz.second) == key(zl)) dup = true;
                if (!dup) {
                    topZ.push_back({tot, zl});
                    sort(topZ.begin(), topZ.end(), [](auto& x, auto& y) { return x.first > y.first; });
                    if ((int)topZ.size() > triTop) topZ.pop_back();
                }
            }
        }
        if (topZ.empty()) return -1e300;
        double result = -1e300;
        for (int tzi = 0; tzi < (int)topZ.size(); tzi++) {
        if (tzi > 0 && over()) break;
        bestDP = topZ[tzi].first;
        bestZ = topZ[tzi].second;
        // membership: sites inside exactly one zone
        auto inZone = [&](const Zone& z, int s) {
            if (z.len == 0) return inTri(hv[z.j], hv[z.t1], hv[z.t2], s);
            int e = outside[s] && slab[s] < 0 ? rawSec(z.j, s) : sec[(size_t)z.j * n + s];
            return e >= 0 && (e - z.e + m) % m < z.len;
        };
        vector<int> zoneOf(n, -1);
        fill(cnt.begin(), cnt.end(), 0);
        static const bool triAll = false;
        for (int zi = 0; zi < (int)bestZ.size(); zi++) {
            if (bestZ[zi].v <= 0 && !triAll) continue;
            for (int s = 0; s < n; s++)
                if (okSite[s] && inZone(bestZ[zi], s)) cnt[s]++, zoneOf[s] = zi;
        }
        vector<int> order;
        for (int zi = 0; zi < (int)bestZ.size(); zi++)
            if (bestZ[zi].v > 0) order.push_back(zi);
        sort(order.begin(), order.end(), [&](int x, int y) { return bestZ[x].v > bestZ[y].v; });
        vector<vector<int>> zs(bestZ.size());
        for (int s = 0; s < n; s++)
            if (cnt[s] == 1) zs[zoneOf[s]].push_back(s);
        for (int attempt = 0; attempt < 3; attempt++) {
            // attempts 1, 2: drop outside sites near polygon vertices / all outside sites (hulls may meet there)
            vector<int> asg(n, -1);
            vector<int> used(NS, 0);
            vector<Mask> masks;
            for (int zi : order) {
                int o = ho[bestZ[zi].j];
                vector<pair<double, int>> c, fil;
                for (int s : zs[zi]) {
                    if (attempt == 1 && outside[s] && (slab[s] < 0 || slabPos[s] < 0.25 || slabPos[s] > 0.75)) continue;
                    if (attempt == 2 && outside[s]) continue;
                    double v = rew[s] - dist[o][s];
                    if (v > 0) c.push_back({-v, s});
                    else if (alpha > 0 && T < INF_T && ntask[s] > 0 && v > -alpha * ntask[s]) fil.push_back({-v / ntask[s], s});
                }
                sort(c.begin(), c.end());
                sort(fil.begin(), fil.end());  // fillers (lose less than the imbalance they remove), cheapest per task first
                size_t npos = c.size();
                c.insert(c.end(), fil.begin(), fil.end());
                fil.clear();
                Mask have;
                long long got = 0;
                vector<int> pk;
                for (size_t ci = 0; ci < c.size(); ci++) {
                    auto& cv = c[ci];
                    if ((int)pk.size() >= maxSize[o]) break;
                    if (ci == npos && pk.empty()) break;
                    int s = cv.second;
                    if (got + ntask[s] > T) continue;
                    Mask needNew = smask[s] & ~have;
                    if (needNew.any()) {
                        bool ok = true;
                        if (singleSkillWorkers) {
                            for (int k = 0; k < NS && ok; k++)
                                if (needNew[k] && used[k] >= availSkill[k]) ok = false;
                        } else {
                            masks.push_back(have | needNew);
                            ok = assignWorkers(masks, false);
                            masks.pop_back();
                        }
                        if (!ok) continue;
                        have |= needNew;
                    }
                    pk.push_back(s);
                    got += ntask[s];
                }
                if (pk.empty()) continue;
                for (int k = 0; k < NS; k++)
                    if (have[k]) used[k]++;
                if (have.any()) masks.push_back(have);
                for (int s : pk) asg[s] = o;
            }
            poolAddAsg(asg);
            State st = fromAsg(asg);
            double lamSave = lambdaCnt, waSave = wAlpha, wcSave = wCost;
            lambdaCnt = 1e18, wAlpha = 1, wCost = 1;
            if (alpha > 0) repairTasks(st);
            if (!countFeasible(st)) repairCounts(st);
            if (alpha > 0) repairTasks(st);
            lambdaCnt = lamSave, wAlpha = waSave, wCost = wcSave;
            poolAddAsg(st.asg);
            string err = validateFull(st);
            double val = err.empty() && countFeasible(st) ? trueObjective(st) : -1e300;
            if (szDebug) fprintf(stderr, "tri: T=%lld dp=%.6g zones=%zu attempt=%d obj=%.6g %s t=%.2f\n", T, bestDP, order.size(), attempt, val, err.c_str(), elapsed());
            if (val > -1e299) {
                result = max(result, val);
                if (val > bestV) bestV = val, bestAsg_ = st.asg, bestT = T, haveRes = true;
                break;
            }
        }
        // exact task-band selection inside the same cells (same candidate filters per attempt)
        static const bool triBand = true;
        for (int attempt = 0; triBand && attempt < 3; attempt++) {
            vector<int> zo2;
            vector<vector<int>> cd;
            vector<int> bord = order;
            if (triAll) {
                bord.clear();
                for (int zi = 0; zi < (int)bestZ.size(); zi++)
                    if (!zs[zi].empty()) bord.push_back(zi);
            }
            for (int zi : bord) {
                vector<int> cs;
                for (int s : zs[zi]) {
                    if (attempt == 1 && outside[s] && (slab[s] < 0 || slabPos[s] < 0.25 || slabPos[s] > 0.75)) continue;
                    if (attempt == 2 && outside[s]) continue;
                    cs.push_back(s);
                }
                zo2.push_back(ho[bestZ[zi].j]);
                cd.push_back(cs);
            }
            double bv;
            vector<int> basg = bandSelect(zo2, cd, &bv);
            if (basg.empty()) break;
            State sb = fromAsg(basg);
            string err = validateFull(sb);
            double val = err.empty() && countFeasible(sb) ? trueObjective(sb) : -1e300;
            if (szDebug) fprintf(stderr, "tri band: T=%lld attempt=%d est=%.6g obj=%.6g %s t=%.2f\n", T, attempt, bv, val, err.c_str(), elapsed());
            if (val > -1e299) {
                result = max(result, val);
                if (val > bestV) bestV = val, bestAsg_ = sb.asg, bestT = T, haveRes = true;
                break;
            }
        }
        }
        return result;
    };
    bool anyOutside = false;
    for (int s = 0; s < n; s++) anyOutside |= outside[s] && okSite[s];
    for (int mode = 0; mode < (anyOutside ? 2 : 1); mode++) {
        phase = mode == 0 ? 1 : 2;
        if (over() || !buildTables(mode)) break;
        long long bestT0 = -1;
        double best0 = -1e300;
        for (long long T : Ts) {
            if (over()) break;
            double v = evalT(T);
            if (v > best0) best0 = v, bestT0 = T;
        }
        if (bestT0 > 0 && bestT0 < INF_T)
            for (double f : {0.85, 1.15, 0.93, 1.07}) {
                if (over()) break;
                evalT(max(1LL, (long long)llround(bestT0 * f)));
            }
    }
    // extension: pattern search over (table mode, DP shortfall weight, T) around the best point;
    // the exact band selection makes the final value a rugged function of the DP cells.
    // Only when the triangulation already beats the best start known (rival); it stops early when
    // its first tries bring nothing.
    if (szDebug) fprintf(stderr, "tri phase1: best %.6g rival %.6g t=%.2f\n", bestV, rival, elapsed());
    if (bestV > -1e299 && bestV >= rival && bestT > 0 && bestT < INF_T && (extEnd > endTime || triWork) && alpha > 0) {
        endTime = extEnd;
        static const double gams[] = {1.0, 0.25, 0.5, 0.125, 0.75, 1.5, 0.375};
        int nm = anyOutside ? 2 : 1, curMode = -1;
        int bMode = 0, bG = 0;
        long long bT = bestT;
        // which mode produced bestT is unknown after phase 1: start from mode 0 and let flips find it
        set<tuple<int, int, long long>> seen;
        double step = 0.06;
        int fails = 0, wins = 0;
        phase = 3;
        static const int extNoWin = 6;  // tries without a win
        while (!over() && fails < 24 && (wins > 0 || tries < extNoWin)) {
            int mode = bMode, g = bG;
            long long T = bT;
            int r = irand(10);
            if (r < 6) T = max(1LL, (long long)llround(bT * (1 + step * (irand(2) ? 1 : -1) * (0.5 + urand()))));
            else if (r < 9) g = irand(7);
            else mode = irand(nm);
            if (!seen.insert({mode, g, T}).second) {
                fails++;
                step = max(0.003, step * 0.8);
                continue;
            }
            if (mode != curMode) {
                if (!buildTables(mode)) break;
                curMode = mode;
            }
            triGam = gams[g];
            double before = bestV;
            evalT(T);
            tries++;
            if (bestV > before + 1e-9) bMode = mode, bG = g, bT = T, fails = 0, wins++;
            else if (++fails % 6 == 0) step = max(0.003, step * 0.7);
        }
        if (szDebug) fprintf(stderr, "tri ext: best %.6g mode=%d gam=%.3g T=%lld tries=%d wins=%d t=%.2f\n", bestV, bMode, gams[bG], bT, tries, wins, elapsed());
    }
    if (bestV < -1e299) return none;
    *outVal = bestV;
    return bestAsg_;
}

// ---------------------------------------------------------------- chord sweep (free zigzag cuts)
// Offices on a ring with instance3-like costs (cheap sites lie across the ring): the best zones are
// fans from an office across to the far side, side by side in a zigzag. triSearch cuts them along
// lines through two offices (a triangulation of the office polygon). Here the cuts are free chords of
// the office circle, swept from the point A at angle th to the opposite point B: chord (tu, tl)
// joins the circle points at angles th + tu and th - tl (0 <= tu, tl <= pi); chords with tu and tl
// both non-decreasing do not cross inside the circle, so the cells between consecutive chords are
// disjoint and convex (cells may meet outside the circle: a site claimed twice is dropped). Every
// office lies on the circle, so a chord ending next to it puts it on the expected side whatever the
// chord's slant. A DP over chord pairs (ends at the office angles +- a small offset and at points
// inside the office gaps) picks the cells and one office inside each (its hull stays inside the
// cell), valued per task level T like triSearch; every DP plan is balanced exactly by bandSelect,
// and the best plans are refined by moving single chord ends (and swapping cell offices) under the
// exact band value.
struct ChordGeo {
    double cx, cy, R, th;
};
// side(p) = a * x + b * y + c (> 0 beyond, towards B); the ends A and B are flagged by kind
struct ChordLine {
    double a, b, c;
    int kind;  // 0 line, 1 the point A (all beyond), 2 the point B (all before)
    double at(int p) const { return kind == 1 ? 1e300 : kind == 2 ? -1e300 : a * px[p] + b * py[p] + c; }
};
static inline ChordLine chordLine(const ChordGeo& g, double tu, double tl) {
    if (tu <= 0 && tl <= 0) return {0, 0, 0, 1};
    if (tu >= M_PI && tl >= M_PI) return {0, 0, 0, 2};
    double ux = g.cx + g.R * cos(g.th + tu), uy = g.cy + g.R * sin(g.th + tu);
    double lx = g.cx + g.R * cos(g.th - tl), ly = g.cy + g.R * sin(g.th - tl);
    double dx = lx - ux, dy = ly - uy, len = hypot(dx, dy);
    if (len < 1e-300) return {0, 0, 0, 0};
    double mid = g.th + (tu + 2 * M_PI - tl) / 2;
    double rx = g.cx + g.R * cos(mid), ry = g.cy + g.R * sin(mid);
    double sr = dx * (ry - uy) - dy * (rx - ux) > 0 ? 1 : -1;
    // sr * (dx * (y - uy) - dy * (x - ux)) / len
    double a = -sr * dy / len, b = sr * dx / len;
    return {a, b, -(a * ux + b * uy), 0};
}
struct ChordPlan {
    ChordGeo g;
    vector<double> tu, tl;  // chords 0..M (0 = A, M = B)
    vector<int> off;        // office of cell j (between chords j and j + 1), -1 = empty
    double val = -1e300;
    vector<int> asg;
};
// Exact value of a chord plan: cells -> candidate sites -> bandSelect. -1e300 when an office left its
// cell or nothing pays. With check, the assignment is fully validated (else only the band estimate).
static double chordEval(const ChordPlan& P, const vector<char>& okSite, bool check, vector<int>* asgOut) {
    int M = P.tu.size() - 1;
    const double margin = 20 * EPS;
    static vector<double> sd;
    static vector<int> claim;
    static vector<vector<int>> cand;
    static vector<int> zo;
    sd.resize((size_t)(M + 1) * NP);
    claim.assign(n, 0);
    zo.clear();
    // offices first (cheap rejection), then the sites
    vector<ChordLine> Ls(M + 1);
    for (int k = 0; k <= M; k++) Ls[k] = chordLine(P.g, P.tu[k], P.tl[k]);
    for (int j = 0; j < M; j++) {
        int o = P.off[j];
        if (o >= 0 && !(Ls[j].at(n + o) > margin && Ls[j + 1].at(n + o) < -margin)) return -1e300;
    }
    for (int k = 0; k <= M; k++) {  // = Ls[k].at(p), the kind tested once per line
        double* __restrict row = &sd[(size_t)k * NP];
        const ChordLine& Lk = Ls[k];
        if (Lk.kind == 1) fill(row, row + n, 1e300);
        else if (Lk.kind == 2) fill(row, row + n, -1e300);
        else {
            const double a = Lk.a, b = Lk.b, c = Lk.c;
            for (int p = 0; p < n; p++) row[p] = a * px[p] + b * py[p] + c;
        }
    }
    int nz = 0;
    for (int j = 0; j < M; j++) {
        int o = P.off[j];
        if (o < 0) continue;
        zo.push_back(o);
        if ((int)cand.size() <= nz) cand.emplace_back();
        vector<int>& cs = cand[nz++];
        cs.clear();
        const double* A0 = &sd[(size_t)j * NP];
        const double* A1 = &sd[(size_t)(j + 1) * NP];
        for (int s = 0; s < n; s++)
            if (A0[s] > margin && A1[s] < -margin && okSite[s]) cs.push_back(s), claim[s]++;
    }
    if (zo.empty()) return -1e300;
    cand.resize(nz);
    for (auto& cs : cand) cs.erase(remove_if(cs.begin(), cs.end(), [&](int s) { return claim[s] > 1; }), cs.end());
    if (!check) return bandValueCached(zo, cand);
    double bv;
    vector<int> basg = bandSelect(zo, cand, &bv);
    if (basg.empty()) return -1e300;
    State sb = fromAsg(basg);
    if (!validateFull(sb).empty() || !countFeasible(sb)) return -1e300;
    if (asgOut) *asgOut = sb.asg;
    return trueObjective(sb);
}
// Local search over the chord ends and cell offices of a plan under the exact band value.
static void chordRefine(ChordPlan& P, const vector<char>& okSite, double minGap, double endTime, int* evalsOut) {
    int M = P.tu.size() - 1;
    double cur = P.val;
    int evals = 0;
    double step = 0.25 * minGap;
    const double minStep = 0.004 * minGap;
    static const int dU[6] = {1, -1, 0, 0, 1, -1}, dL[6] = {0, 0, 1, -1, 1, -1};
    auto tryPlan = [&](ChordPlan& Q) {
        if (n > 1500 && elapsed() >= endTime) return false;  // r41: the inner loops (offices x moves) stop at the deadline too
        evals++;
        double v = chordEval(Q, okSite, false, nullptr);
        if (v <= cur + 1e-9) return false;
        vector<int> a;
        double vc = chordEval(Q, okSite, true, &a);  // accept only fully valid improvements
        if (vc <= cur + 1e-9) return false;
        Q.val = vc, Q.asg = a;
        P = Q;
        cur = vc;
        return true;
    };
    while (step >= minStep && elapsed() < endTime) {
        bool imp = false;
        for (int k = 1; k < M && elapsed() < endTime; k++)
            for (int d = 0; d < 6; d++) {
                ChordPlan Q = P;
                Q.tu[k] = min(M_PI, max(0.0, Q.tu[k] + dU[d] * step));
                Q.tl[k] = min(M_PI, max(0.0, Q.tl[k] + dL[d] * step));
                if (Q.tu[k] < Q.tu[k - 1] || Q.tu[k] > Q.tu[k + 1] || Q.tl[k] < Q.tl[k - 1] || Q.tl[k] > Q.tl[k + 1]) continue;
                if (Q.tu[k] == P.tu[k] && Q.tl[k] == P.tl[k]) continue;
                if (tryPlan(Q)) imp = true;
            }
        // cell offices: another office inside the cell, or an empty cell / dropped zone
        for (int j = 0; j < M && elapsed() < endTime; j++)
            for (int o = -1; o < K; o++) {
                if (o == P.off[j] || (o >= 0 && maxSize[o] <= 0)) continue;
                bool used = false;
                for (int q : P.off) used |= q == o && o >= 0;
                if (used) continue;
                ChordPlan Q = P;
                Q.off[j] = o;
                if (tryPlan(Q)) imp = true;
            }
        // structure: split a cell by a new chord through its middle (the half without the office gets
        // an office inside it or stays empty), or merge two neighbouring cells (either office)
        for (int j = 0; j < M && elapsed() < endTime; j++) {
            ChordPlan Q = P;
            double mu = 0.5 * (Q.tu[j] + Q.tu[j + 1]), ml = 0.5 * (Q.tl[j] + Q.tl[j + 1]);
            if (mu == Q.tu[j] && ml == Q.tl[j]) continue;
            Q.tu.insert(Q.tu.begin() + j + 1, mu), Q.tl.insert(Q.tl.begin() + j + 1, ml);
            Q.off.insert(Q.off.begin() + j + 1, -1);
            for (int side = 0; side < 2; side++)
                for (int o = -1; o < K; o++) {
                    if (o >= 0 && maxSize[o] <= 0) continue;
                    bool used = false;
                    for (int q : P.off) used |= q == o && o >= 0;
                    if (used) continue;
                    ChordPlan R2 = Q;
                    R2.off[j + side] = side == 0 ? o : P.off[j];
                    R2.off[j + 1 - side] = side == 0 ? P.off[j] : o;
                    if (R2.off[j] == R2.off[j + 1] && R2.off[j] >= 0) continue;
                    if (tryPlan(R2)) {
                        imp = true;
                        M = P.tu.size() - 1;
                        goto nextSplit;
                    }
                }
        nextSplit:;
        }
        for (int k = 1; k < M && elapsed() < endTime; k++)
            for (int keep = 0; keep < 2; keep++) {
                ChordPlan Q = P;
                int o = keep ? Q.off[k] : Q.off[k - 1];
                Q.tu.erase(Q.tu.begin() + k), Q.tl.erase(Q.tl.begin() + k);
                Q.off.erase(Q.off.begin() + k);
                Q.off[k - 1] = o;
                if (tryPlan(Q)) {
                    imp = true;
                    M = P.tu.size() - 1;
                    break;
                }
            }
        M = P.tu.size() - 1;
        if (!imp) step *= 0.5;
    }
    if (evalsOut) *evalsOut += evals;
}
// Annealing over a plan under the exact band value: a chord end moves by a random amount (scale and
// temperature shrink over time), a cell changes office, a cell splits or two cells merge. New bests
// are fully validated before they count; the best plan is refined at the end.
static void chordSA(ChordPlan& best, const vector<char>& okSite, double minGap, double endTime, int* evalsOut) {
    double t0 = elapsed(), len = max(1e-3, endTime - t0);
    ChordPlan cur = best;
    double curV = cur.val;
    static const double saT0 = 0.004;
    double T0 = saT0 * fabs(best.val) + 1e-9;
    long long it = 0, acc = 0, wins = 0;
    while (true) {
        double now = elapsed();
        if (now >= endTime) break;
        double fr = (now - t0) / len;
        double T = T0 * pow(1e-3, fr);
        double sc = minGap * (0.3 * pow(0.03, fr));
        for (int inner = 0; inner < 20; inner++) {
            // a move costs a chord evaluation: the clock is read every 4th move
            if (inner > 0 && (inner & 3) == 0 && elapsed() >= endTime) break;
            it++;
            ChordPlan Q = cur;
            int M = Q.tu.size() - 1;
            int r = irand(100);
            if (r < 80 && M >= 2) {
                int k = 1 + irand(M - 1);
                int e = irand(3);
                double g1 = (urand() * 2 - 1) * sc, g2 = (urand() * 2 - 1) * sc;
                if (e != 1) Q.tu[k] = min(Q.tu[k + 1], max(Q.tu[k - 1], Q.tu[k] + g1));
                if (e != 0) Q.tl[k] = min(Q.tl[k + 1], max(Q.tl[k - 1], Q.tl[k] + (e == 2 && irand(2) ? g1 : g2)));
            } else if (r < 94) {
                int j = irand(M), o = irand(K + 1) - 1;
                if (o >= 0 && maxSize[o] <= 0) continue;
                bool used = false;
                for (int q : Q.off) used |= q == o && o >= 0;
                if (used || o == Q.off[j]) continue;
                Q.off[j] = o;
            } else if (r < 97) {  // split
                int j = irand(M);
                double f = 0.3 + 0.4 * urand();
                double mu = Q.tu[j] + f * (Q.tu[j + 1] - Q.tu[j]), ml = Q.tl[j] + f * (Q.tl[j + 1] - Q.tl[j]);
                Q.tu.insert(Q.tu.begin() + j + 1, mu), Q.tl.insert(Q.tl.begin() + j + 1, ml);
                int o = irand(K + 1) - 1;
                bool used = false;
                for (int q : Q.off) used |= q == o && o >= 0;
                if (used || (o >= 0 && maxSize[o] <= 0)) o = -1;
                if (irand(2)) Q.off.insert(Q.off.begin() + j + 1, o);
                else Q.off.insert(Q.off.begin() + j, o);
            } else if (M >= 2) {  // merge
                int k = 1 + irand(M - 1);
                int o = irand(2) ? Q.off[k] : Q.off[k - 1];
                Q.tu.erase(Q.tu.begin() + k), Q.tl.erase(Q.tl.begin() + k);
                Q.off.erase(Q.off.begin() + k);
                Q.off[k - 1] = o;
            } else
                continue;
            double v = chordEval(Q, okSite, false, nullptr);
            if (v < -1e299) continue;
            double d = v - curV;
            if (d >= 0 || urand() < exp(d / T)) {
                cur = std::move(Q), curV = v, acc++;
                if (curV > best.val + 1e-9) {
                    vector<int> a;
                    double vc = chordEval(cur, okSite, true, &a);
                    if (vc > best.val + 1e-9) {
                        best = cur, best.val = vc, best.asg = a, wins++;
                    }
                }
            }
        }
    }
    if (evalsOut) *evalsOut += it;
    if (szDebug) fprintf(stderr, "chord sa: %lld moves, %lld accepted, %lld wins, best %.6g t=%.2f\n", it, acc, wins, best.val, elapsed());
}
// Iterated local search: kick the best plan (a chord moved far, an office swapped) and refine.
static void chordILS(ChordPlan& best, const vector<char>& okSite, double minGap, double endTime, int* evalsOut) {
    int kicks = 0, wins = 0;
    while (elapsed() < endTime) {
        ChordPlan Q = best;
        int M = Q.tu.size() - 1;
        int nk = 1 + irand(2);
        for (int t = 0; t < nk; t++) {
            int r = irand(3);
            if (r < 2 && M >= 2) {
                int k = 1 + irand(M - 1);
                double lo = Q.tu[k - 1], hi = Q.tu[k + 1];
                if (r == 0 || irand(2)) Q.tu[k] = lo + urand() * (hi - lo);
                lo = Q.tl[k - 1], hi = Q.tl[k + 1];
                if (r == 1 || irand(2)) Q.tl[k] = lo + urand() * (hi - lo);
            } else {
                int j = irand(M), o = irand(K + 1) - 1;
                bool used = false;
                for (int q : Q.off) used |= q == o && o >= 0;
                if (!used && (o < 0 || maxSize[o] > 0)) Q.off[j] = o;
            }
        }
        Q.val = chordEval(Q, okSite, true, &Q.asg);
        if (Q.val < -1e299) Q.val = -1e299;  // refine from an invalid kick: anything valid is better
        chordRefine(Q, okSite, minGap, endTime, evalsOut);
        kicks++;
        if (Q.val > best.val + 1e-9) best = Q, wins++;
    }
    if (szDebug) fprintf(stderr, "chord ils: %d kicks, %d wins, best %.6g t=%.2f\n", kicks, wins, best.val, elapsed());
}
// the best refined plan, kept for the iterated local search that every process runs after the fork
static ChordPlan chordBest;
static vector<ChordPlan> chordTop;  // the refined plans within 1 % of the best (other processes start there)
static vector<char> chordOk;
static double chordGap = 0;
vector<int> chordSearch(double endTime, double ilsEnd, double rival, double* outVal) {
    vector<int> none;
    *outVal = -1e300;
    vector<int> offs;
    for (int o = 0; o < K; o++)
        if (maxSize[o] > 0) offs.push_back(o);
    int m = offs.size();
    if (m < 6 || n < 8 || n > 12000 || alpha <= 0) return none;  // r40: n cap 6000 -> 12000
    double cx = 0, cy = 0;
    for (int o : offs) cx += px[n + o], cy += py[n + o];
    cx /= m, cy /= m;
    double Rb = 0;
    for (int o : offs) Rb += hypot(px[n + o] - cx, py[n + o] - cy);
    Rb /= m;
    if (Rb <= 0) return none;
    const double margin = 20 * EPS;
    vector<char> okSite(n, 1);
    for (int s = 0; s < n; s++)
        for (int k = 0; k < NS; k++)
            if (smask[s][k] && availSkill[k] == 0) okSite[s] = 0;
    vector<double> so;
    for (int o : offs) so.push_back(atan2(py[n + o] - cy, px[n + o] - cx));
    sort(so.begin(), so.end());
    double minGap = 2 * M_PI;
    for (int i = 0; i < m; i++) {
        double g = (i + 1 < m ? so[i + 1] : so[0] + 2 * M_PI) - so[i];
        if (g > 1e-9) minGap = min(minGap, g);
    }
    if (minGap > M_PI / 3) return none;
    static const double cdel = 0.01;
    int cmid = m <= 16 ? 2 : m <= 24 ? 1 : 0;
    double del = cdel * minGap;
    static const double cApex = 2.5;
    double apexW = cApex * 2 * M_PI / m;
    vector<double> oang(K, 0);
    for (int o : offs) oang[o] = atan2(py[n + o] - cy, px[n + o] - cx);
    vector<double> gang;
    for (int i = 0; i < m; i++) {
        gang.push_back(so[i] - del), gang.push_back(so[i] + del);
        double g = (i + 1 < m ? so[i + 1] : so[0] + 2 * M_PI) - so[i];
        if (g < 4 * del) continue;
        for (int q = 1; q <= cmid; q++) gang.push_back(so[i] + g * q / (cmid + 1));
    }
    const int words = (n + 63) / 64;
    vector<vector<pair<double, int>>> ord(K);  // per office: profitable sites, profit desc
    for (int o : offs) {
        for (int s = 0; s < n; s++) {
            if (!okSite[s]) continue;
            double p = rew[s] - dist[o][s];
            if (p > 0) ord[o].push_back({p, s});
        }
        sort(ord[o].begin(), ord[o].end(), greater<pair<double, int>>());
    }
    long long totT = 0;
    for (int s = 0; s < n; s++)
        if (okSite[s]) totT += ntask[s];
    if (totT <= 0) return none;
    auto norm = [](double a) {
        while (a < 0) a += 2 * M_PI;
        while (a >= 2 * M_PI) a -= 2 * M_PI;
        return a;
    };
    static const double cRef = 0.5;  // share of the time for refinement
    double t0 = elapsed();
    double dpEnd = t0 + (1 - cRef) * max(0.0, endTime - t0);
    auto over = [&]() { return elapsed() > dpEnd; };
    set<uint64_t> seenPlan;
    vector<ChordPlan> top;  // best distinct plans
    static const int cTop = 4;
    long long evals = 0;
    vector<double> axes;
    for (int i = 0; i < m; i++) {
        double g = (i + 1 < m ? so[i + 1] : so[0] + 2 * M_PI) - so[i];
        for (double a : {so[i], so[i] + g / 2}) {
            double t = fmod(norm(a), M_PI);
            bool dup = false;
            for (double b : axes)
                if (fabs(b - t) < 1e-6 || fabs(fabs(b - t) - M_PI) < 1e-6) dup = true;
            if (!dup) axes.push_back(t);
        }
    }
    static const double cTstep = 0.5;
    vector<long long> Ts;
    for (double k = 4.0; k <= 12.0 + 1e-9; k += cTstep) Ts.push_back(max(1LL, (long long)llround(totT / k)));
    // scan order: the middle task levels first (most plans win there)
    // r41: levels a median office cannot reach within its maxSize (every zone capped) go last
    long long tFit = LLONG_MAX;
    const bool bigN = n > 1500;  // r41: the old order below that (#8-like rings unchanged)
    {
        vector<int> ms;
        for (int o : offs) ms.push_back(maxSize[o]);
        nth_element(ms.begin(), ms.begin() + ms.size() / 2, ms.end());
        int nOk = 0;
        for (int s = 0; s < n; s++) nOk += okSite[s] != 0;
        if (nOk > 0) tFit = (long long)ceil(ms[ms.size() / 2] * (double)totT / nOk);
    }
    stable_sort(Ts.begin(), Ts.end(), [&](long long x, long long y) {
        bool fx = x <= tFit || !bigN, fy = y <= tFit || !bigN;
        if (fx != fy) return fx;
        return fabs(totT / (double)x - 7.0) < fabs(totT / (double)y - 7.0);
    });
    // r41: the side bitsets of an axis do not depend on the task level T: they are built once per
    // axis and reused for every level (the scan below runs all levels of an axis in a row); at
    // n = 8000 the bitsets were ~90 % of a call, so the DP now sees several times more (axis, T) pairs
    double geoTh = NAN;
    vector<double> tu, tl;
    int MU = 0, ML = 0, NC = 0;
    vector<uint64_t> bey, bef, beyR, befR;
    vector<vector<char>> beyO, befO;
    vector<int> wo(K, 0);
    vector<size_t> base(K, 0);
    double geoSec = 0, dpSec = 0;
    auto runAxis = [&](double th, long long T, double gam) {
        ChordGeo G{cx, cy, Rb, th};
        auto cid = [&](int a, int b) { return a * ML + b; };
        double tg0 = szDebug ? elapsed() : 0;
        if (!(th == geoTh)) {
        geoTh = th;
        tu.assign({0.0, M_PI}), tl.assign({0.0, M_PI});
        for (double g : gang) {
            double t = norm(g - th);
            if (t > 1e-9 && t < M_PI - 1e-9) tu.push_back(t);
            double t2 = norm(th - g);
            if (t2 > 1e-9 && t2 < M_PI - 1e-9) tl.push_back(t2);
        }
        sort(tu.begin(), tu.end());
        tu.erase(unique(tu.begin(), tu.end(), [](double x, double y) { return fabs(x - y) < 1e-9; }), tu.end());
        sort(tl.begin(), tl.end());
        tl.erase(unique(tl.begin(), tl.end(), [](double x, double y) { return fabs(x - y) < 1e-9; }), tl.end());
        MU = tu.size(), ML = tl.size(), NC = MU * ML;
        bey.assign((size_t)NC * words, 0), bef.assign((size_t)NC * words, 0);
        beyO.assign(NC, vector<char>(K, 0)), befO.assign(NC, vector<char>(K, 0));
        for (int a = 0; a < MU; a++)
            for (int b = 0; b < ML; b++) {
                int c = cid(a, b);
                uint64_t* B1 = &bey[(size_t)c * words];
                uint64_t* B2 = &bef[(size_t)c * words];
                ChordLine L = chordLine(G, tu[a], tl[b]);
                for (int s = 0; s < n; s++) {
                    double v = L.at(s);
                    if (v > margin) B1[s >> 6] |= 1ULL << (s & 63);
                    else if (v < -margin) B2[s >> 6] |= 1ULL << (s & 63);
                }
                for (int o : offs) {
                    double v = L.at(n + o);
                    if (v > margin) beyO[c][o] = 1;
                    else if (v < -margin) befO[c][o] = 1;
                }
            }
        if (bigN && over()) {  // r41: an unfinished side table is never reused
            geoTh = NAN;
            return;
        }
        size_t tot = 0;
        for (int o : offs) wo[o] = ((int)ord[o].size() + 63) / 64, base[o] = tot, tot += (size_t)NC * wo[o];
        beyR.assign(tot, 0), befR.assign(tot, 0);  // the sides in each office's profit order
        for (int o : offs) {
            if (bigN && over()) {  // r48: clock check per office (this half costs ~3 s at n = 12000, m = 32)
                geoTh = NAN;
                return;
            }
            for (int c = 0; c < NC; c++) {
                uint64_t* B1 = &beyR[base[o] + (size_t)c * wo[o]];
                uint64_t* B2 = &befR[base[o] + (size_t)c * wo[o]];
                const uint64_t* S1 = &bey[(size_t)c * words];
                const uint64_t* S2 = &bef[(size_t)c * words];
                for (int r = 0; r < (int)ord[o].size(); r++) {
                    int s = ord[o][r].second;
                    if (S1[s >> 6] >> (s & 63) & 1) B1[r >> 6] |= 1ULL << (r & 63);
                    if (S2[s >> 6] >> (s & 63) & 1) B2[r >> 6] |= 1ULL << (r & 63);
                }
            }
        }
        if (bigN && over()) {
            geoTh = NAN;
            return;
        }
        }
        double tg1 = szDebug ? elapsed() : 0;
        geoSec += tg1 - tg0;
        struct DpClock { double t0; double& acc; ~DpClock() { if (szDebug) acc += elapsed() - t0; } } dpClock{tg1, dpSec};
        vector<double> V(NC, -1e300);
        vector<int> bk(NC, -1), bo(NC, -1);  // previous chord (-1: none), office (-1: empty cell)
        vector<double> ub(K, 0);             // zone value of the office over all its sites (pruning)
        for (int o : offs) {
            double v = 0;
            long long got = 0;
            int cnt = 0;
            for (auto& ps : ord[o]) {
                if (cnt >= maxSize[o]) break;
                if (got + ntask[ps.second] > T) continue;
                got += ntask[ps.second], v += ps.first, cnt++;
                if (got == T) break;
            }
            ub[o] = v - gam * alpha * (double)(T - got) - ocost[o];
        }
        V[0] = 0;
        for (int a = 0; a < MU && !over(); a++)
            for (int b = 0; b < ML && !over(); b++) {
                int c1 = cid(a, b);
                if (a > 0 && V[cid(a - 1, b)] > V[c1]) V[c1] = V[cid(a - 1, b)], bk[c1] = cid(a - 1, b), bo[c1] = -1;
                if (b > 0 && V[cid(a, b - 1)] > V[c1]) V[c1] = V[cid(a, b - 1)], bk[c1] = cid(a, b - 1), bo[c1] = -1;
                if (V[c1] < -1e299) continue;
                for (int o : offs) {
                    if (!beyO[c1][o] || ub[o] <= 0) continue;
                    const uint64_t* B1 = &beyR[base[o] + (size_t)c1 * wo[o]];
                    double cost = ocost[o];
                    int cap = maxSize[o];
                    // a fan is narrow on its office's side: that side of the cell spans at most
                    // cApex office gaps (except the cells at the poles A and B)
                    double ot = norm(oang[o] - th);
                    bool onU = ot < M_PI;
                    for (int a2 = a; a2 < MU; a2++) {
                        bool wideU = onU && c1 != 0 && tu[a2] - tu[a] > apexW;
                        if (wideU && a2 != MU - 1) continue;  // only the cell at the pole B may be wide
                        for (int b2 = (a2 == a ? b + 1 : b); b2 < ML; b2++) {
                            int c2 = cid(a2, b2);
                            bool last = c2 == NC - 1;
                            if (wideU && !last) continue;
                            if (!onU && c1 != 0 && !last && tl[b2] - tl[b] > apexW) {
                                if (a2 == MU - 1) {
                                    b2 = ML - 2;
                                    continue;
                                }
                                break;
                            }
                            if (!befO[c2][o] || V[c1] + ub[o] <= V[c2]) continue;
                            const uint64_t* B2 = &befR[base[o] + (size_t)c2 * wo[o]];
                            double v = 0;
                            long long got = 0;
                            int cnt = 0;
                            bool done = false;
                            for (int w = 0; w < wo[o] && !done; w++) {
                                uint64_t x = B1[w] & B2[w];
                                while (x) {
                                    int r = w * 64 + __builtin_ctzll(x);
                                    x &= x - 1;
                                    if (cnt >= cap) {
                                        done = true;
                                        break;
                                    }
                                    int nt = ntask[ord[o][r].second];
                                    if (got + nt > T) continue;
                                    got += nt, v += ord[o][r].first, cnt++;
                                    if (got == T) {
                                        done = true;
                                        break;
                                    }
                                }
                            }
                            evals++;
                            v -= gam * alpha * (double)(T - got) + cost;
                            if (v <= 0) continue;
                            if (V[c1] + v > V[c2]) V[c2] = V[c1] + v, bk[c2] = c1, bo[c2] = o;
                        }
                    }
                }
            }
        if (over()) return;
        int cl = cid(MU - 1, ML - 1);
        if (V[cl] < -1e299) return;
        // the plan: chord sequence from A to B, empty cells merged
        vector<int> cs, os;
        for (int c = cl; c >= 0; c = bk[c]) {
            cs.push_back(c);
            if (bk[c] >= 0) os.push_back(bo[c]);
        }
        reverse(cs.begin(), cs.end());
        reverse(os.begin(), os.end());
        ChordPlan P;
        P.g = G;
        for (size_t i = 0; i < cs.size(); i++) {
            if (i > 0 && i + 1 < cs.size() && os[i - 1] < 0 && os[i] < 0) continue;  // inside an empty run
            P.tu.push_back(tu[cs[i] / ML]), P.tl.push_back(tl[cs[i] % ML]);
            if (i + 1 < cs.size()) P.off.push_back(os[i]);
        }
        // drop the merged duplicates of empty cells
        for (size_t j = 0; j + 1 < P.off.size();)
            if (P.off[j] < 0 && P.off[j + 1] < 0) P.off.erase(P.off.begin() + j + 1);
            else j++;
        if ((int)P.off.size() != (int)P.tu.size() - 1) return;  // bookkeeping guard
        uint64_t h = 1469598103934665603ULL;
        for (size_t j = 0; j < P.off.size(); j++)
            h = (h ^ (uint64_t)(P.off[j] + 2) ^ ((uint64_t)llround(P.tu[j + 1] * 1e6) << 20) ^ ((uint64_t)llround(P.tl[j + 1] * 1e6) << 40)) * 1099511628211ULL;
        h ^= (uint64_t)llround(th * 1e6);
        if (!seenPlan.insert(h).second) return;
        P.val = chordEval(P, okSite, true, &P.asg);
        if (szDebug) fprintf(stderr, "chord: th=%.3f T=%lld dp=%.6g zones=%zu obj=%.6g evals=%lld t=%.2f\n", th, T, V[cl], P.off.size(), P.val, evals, elapsed());
        if (P.val < -1e299) return;
        poolAddAsg(P.asg);
        bool dupv = false;
        for (auto& Q : top) dupv |= fabs(Q.val - P.val) < 1e-6;
        if (dupv) return;
        if ((int)top.size() < cTop || P.val > top.back().val) {
            top.push_back(P);
            sort(top.begin(), top.end(), [](const ChordPlan& x, const ChordPlan& y) { return x.val > y.val; });
            if ((int)top.size() > cTop) top.pop_back();
        }
    };
    // the same plan comes out of many neighbouring axes: every task level first gets a quarter of
    // the axes (spread over the half turn), then the next quarter, ...
    sort(axes.begin(), axes.end());
    int na = axes.size();
    // r40: a first pass over every task level with an eighth of the axes, so that a short budget (slow
    // machine) still sees all levels (#8-like rings: the best level was 8th in the scan order)
    // r41: axis-major order (reuses the side tables) only above n = 1500; small rings (#8-like) keep
    // the level-major scan of r40 unchanged
    static const int axisMajorN = 1500;
    const bool axisMajor = n > axisMajorN;
    if (axisMajor) {
        for (int stepA : {8, 4, 2, 1})
            for (int i = 0; i < na; i += stepA) {
                if (stepA < 8 && i % (2 * stepA) == 0) continue;
                for (long long T : Ts) {
                    if (over()) break;
                    runAxis(axes[i], T, 1.0);
                }
            }
    } else
        for (int stepA : {8, 4, 2, 1})
            for (long long T : Ts)
                for (int i = 0; i < na; i += stepA) {
                    if (over() || (stepA < 8 && i % (2 * stepA) == 0)) continue;
                    runAxis(axes[i], T, 1.0);
                }
    if (top.empty()) return none;
    if (szDebug) fprintf(stderr, "chord dp: best %.6g (%zu plans) evals=%lld t=%.2f geo %.2fs dp %.2fs axes %d levels %zu (fit %zu)\n", top[0].val, top.size(), evals, elapsed(), geoSec, dpSec, na, Ts.size(), (size_t)count_if(Ts.begin(), Ts.end(), [&](long long T) { return T <= tFit; }));
    // refinement of the best plans, best first, sharing the rest of the time
    int revals = 0;
    for (size_t i = 0; i < top.size(); i++) {
        double now = elapsed();
        if (now >= endTime) break;
        double until = now + (endTime - now) / (top.size() - i);
        double before = top[i].val;
        chordRefine(top[i], okSite, minGap, until, &revals);
        poolAddAsg(top[i].asg);
        if (szDebug) fprintf(stderr, "chord refine %zu: %.6g -> %.6g evals=%d t=%.2f\n", i, before, top[i].val, revals, elapsed());
    }
    sort(top.begin(), top.end(), [](const ChordPlan& x, const ChordPlan& y) { return x.val > y.val; });
    if (ilsEnd > elapsed() && top[0].val > -1e299) {
        chordILS(top[0], okSite, minGap, ilsEnd, &revals);
        poolAddAsg(top[0].asg);
    }
    if (top[0].val > -1e299) {
        chordTop.clear();
        for (auto& P : top)
            if (P.val >= 0.99 * top[0].val) chordTop.push_back(P);
        chordBest = top[0], chordOk = okSite, chordGap = minGap;
    }
    double bestV = -1e300;
    vector<int> bestAsg;
    for (auto& P : top)
        if (P.val > bestV) bestV = P.val, bestAsg = P.asg;
    if (bestV < -1e299) return none;
    *outVal = bestV;
    return bestAsg;
}

// ---------------------------------------------------------------- power-diagram search
// Anneal over (open set, cell weights); each point is turned into a solution by powerInit
// and scored with the true objective after task-level repair.
void repairTasks(State& st);
void repairCounts(State& st);
double pdEval(const vector<char>& open, const vector<double>& w, vector<int>& asgOut) {
    vector<int> lst;
    for (int o = 0; o < K; o++)
        if (open[o]) lst.push_back(o);
    State st;
    bool built;
    asgOut = powerInit(lst, w, &st, &built);
    if (!built) st = fromAsg(asgOut);
    asgOut = st.asg;  // keeps the worker part (native worker mode)
    if (alpha > 0) {
        double lamSave = lambdaCnt, waSave = wAlpha, wcSave = wCost;
        lambdaCnt = 1e18, wAlpha = 1, wCost = 1;
        repairTasks(st);
        if (!countFeasible(st)) repairCounts(st);
        lambdaCnt = lamSave, wAlpha = waSave, wCost = wcSave;
        asgOut = st.asg;
    }
    return countFeasible(st) ? trueObjective(st) : -1e300;
}

vector<char> pdBestOpen;  // office set and weights of the best power diagram (level construction input)
vector<double> pdBestW;
vector<int> pdSearch(double endTime, double scale, int fixK = 0, double* outVal = nullptr, vector<char>* outOpen = nullptr, vector<double>* outW = nullptr) {
    vector<char> open(K, 1);
    vector<double> w(K, 0.0);
    if (fixK > 0 && fixK < K && outOpen && (int)outOpen->size() == K) {  // continue from a given start
        open = *outOpen, w = *outW;
    } else if (fixK > 0 && fixK < K) {  // exactly fixK open offices, starting from the largest ones
        vector<int> ord(K);
        for (int o = 0; o < K; o++) ord[o] = o;
        stable_sort(ord.begin(), ord.end(), [&](int a, int b) { return maxSize[a] > maxSize[b]; });
        open.assign(K, 0);
        for (int i = 0; i < fixK; i++) open[ord[i]] = 1;
    } else
        fixK = 0;
    if (!fixK) pdBestOpen = open, pdBestW = w;
    // weight step ~ squared distance to the nearest other office
    double sig = 0;
    for (int o = 0; o < K; o++) {
        double bd = 1e300;
        for (int q = 0; q < K; q++)
            if (q != o) bd = min(bd, pow(px[n + o] - px[n + q], 2) + pow(py[n + o] - py[n + q], 2));
        if (bd < 1e300) sig += bd;
    }
    sig = K > 1 ? sig / K : 1.0;
    if (sig <= 0) sig = 1.0;
    // free generators (SZ_GEN): the generator of each cell moves independently of its office;
    // "hot" point = centroid of the office's most profitable sites
    static const int genMode = 0;
    bool freeGen = genMode != 0;
    double gstep = sqrt(sig);
    vector<double> hotX(K), hotY(K);
    if (freeGen) {
        genX.assign(K, 0), genY.assign(K, 0);
        for (int o = 0; o < K; o++) {
            genX[o] = px[n + o], genY[o] = py[n + o];
            vector<pair<double, int>> pr;
            for (int s = 0; s < n; s++) pr.push_back({-(rew[s] - dist[o][s]), s});
            int m = max(1, min(n, maxSize[o]));
            nth_element(pr.begin(), pr.begin() + (m - 1), pr.end());
            double hx = 0, hy = 0;
            for (int i = 0; i < m; i++) hx += px[pr[i].second], hy += py[pr[i].second];
            hotX[o] = hx / m, hotY[o] = hy / m;
        }
        double x0 = 1e300, x1 = -1e300, y0 = 1e300, y1 = -1e300;
        for (int s = 0; s < n; s++) x0 = min(x0, px[s]), x1 = max(x1, px[s]), y0 = min(y0, py[s]), y1 = max(y1, py[s]);
        gstep = max(gstep, 0.15 * max(x1 - x0, y1 - y0));
    }
    vector<int> curAsg, bestA, tmpAsg;
    double cur = pdEval(open, w, curAsg), best = cur;
    bestA = curAsg;
    if (outOpen && outW) *outOpen = open, *outW = w;
    double T0 = scale * 5, T1 = scale * 0.01, start = elapsed();
    long long it = 0;
    while (true) {
        double t = elapsed();
        if (t > endTime) break;
        double frac = (t - start) / max(1e-9, endTime - start);
        double T = T0 * pow(T1 / T0, frac);
        vector<char> o2 = open;
        vector<double> w2 = w;
        int kind = irand(freeGen ? 5 : 3), a = irand(K);
        if (kind >= 3) {  // move the generator of an open office (cells no longer centred on offices)
            if (!o2[a]) continue;
            double ox0 = genX[a], oy0 = genY[a];
            if (kind == 3) {
                double st = gstep * (1 - 0.8 * frac);
                genX[a] += st * (urand() * 2 - 1), genY[a] += st * (urand() * 2 - 1);
            } else {
                int r = irand(3);
                if (r == 0) genX[a] = px[n + a], genY[a] = py[n + a];
                else if (r == 1) genX[a] = hotX[a], genY[a] = hotY[a];
                else {
                    int s = irand(n);
                    genX[a] = px[s], genY[a] = py[s];
                }
            }
            double v = pdEval(o2, w2, tmpAsg);
            it++;
            if (v >= cur || urand() < exp((v - cur) / T)) {
                cur = v, curAsg.swap(tmpAsg);
                poolAddAsgT(curAsg, 0.02);
                if (cur > best) best = cur, bestA = curAsg;
            } else
                genX[a] = ox0, genY[a] = oy0;
            continue;
        }
        if (kind == 0 && fixK) {  // swap an open office with a closed one
            int b = irand(K);
            if (o2[a] == o2[b]) continue;
            swap(o2[a], o2[b]);
        } else if (kind == 0) o2[a] ^= 1;
        else if (kind == 1) {
            w2[a] += sig * (urand() * 2 - 1) * (1 - 0.8 * frac);
            // every open office must stay inside its own power cell
            bool okCell = true;
            for (int q = 0; q < K && okCell && !freeGen; q++) {
                if (q == a || !o2[q]) continue;
                double d2 = pow(px[n + a] - px[n + q], 2) + pow(py[n + a] - py[n + q], 2);
                if (d2 - w2[a] < -w2[q] || d2 - w2[q] < -w2[a]) okCell = false;
            }
            if (!okCell) continue;
        }
        else {
            int b = nearOffOf(a);
            if (b < 0 || o2[a] == o2[b]) continue;
            swap(o2[a], o2[b]);
        }
        double v = pdEval(o2, w2, tmpAsg);
        it++;
        if (v >= cur || urand() < exp((v - cur) / T)) {
            open.swap(o2), w.swap(w2), cur = v, curAsg.swap(tmpAsg);
            poolAddAsgT(curAsg, 0.02);
            if (cur > best) {
                best = cur, bestA = curAsg;
                if (!fixK) pdBestOpen = open, pdBestW = w;
                if (outOpen && outW) *outOpen = open, *outW = w;
            }
        }
    }
    if (outVal) *outVal = best;
    if (szDebug) fprintf(stderr, "pdSearch(k=%d): %lld evals, best %.4f\n", fixK, it, best);
    genX.clear(), genY.clear();
    return bestA;
}


// ---------------------------------------------------------------- task-level construction
// With a task-imbalance penalty every zone should carry (almost) the same number of tasks T, and
// SA tends to lock onto whatever level it reaches first. Here, given the power cells of an office
// set, a DP picks per cell the most profitable sites with count <= maxSize and tasks in [T, T + d];
// all levels T, tolerances d and count windows [lo, lo + A] are scanned and the best plan is built.
static const bool balNativeClaim = true;
long long lvCalls = 0, lvDpCut = 0, lvScanCut = 0;
static const bool wideGate = true;  // exact-level phases at any count window
static const bool zFix = true;  // task-free sites valued in level plans
vector<int> levelBuild(vector<int> open, const vector<double>& w, double endTime, double* outVal, const vector<Mask>* forced = nullptr,
                       const vector<int>* cellOwner = nullptr, const vector<int>* team = nullptr) {
    lvCalls++;
    // the knapsack tables and the coarse level pass may run over the slice by half its length: a
    // build cut there yields nothing, so on a slow CPU every build of a phase could be lost
    // (never past the end of the search phases unless the slice itself is)
    const double lvT0 = elapsed(), lvHard = max(endTime, min(searchEnd, endTime + 0.5 * max(0.0, endTime - lvT0)));
    vector<int> none(n, -1);
    *outVal = -1e300;
    if (alpha <= 0 || !singleSkillWorkers || open.empty()) return none;
    {
        vector<int> keep;
        for (int o : open) {
            bool dup = false;
            for (int q : keep)
                if (px[n + o] == px[n + q] && py[n + o] == py[n + q]) dup = true;
            if (!dup) keep.push_back(o);
        }
        open.swap(keep);
    }
    vector<vector<int>> cell(K), zcell(K);  // task-bearing / task-free profitable sites per cell
    for (int s = 0; s < n; s++) {
        int bo = -1;
        if (cellOwner) {  // cells given by the caller (convex, pairwise separated)
            bo = (*cellOwner)[s];
        } else {
            double bv = 1e300;
            for (int o : open) {
                double dx = px[s] - px[n + o], dy = py[s] - py[n + o];
                double v = dx * dx + dy * dy - w[o];
                if (v < bv) bv = v, bo = o;
            }
        }
        if (bo >= 0 && rew[s] - dist[bo][s] > 0) (ntask[s] > 0 ? cell[bo] : zcell[bo]).push_back(s);
    }
    // skills: offices in order of cell value claim skills while workers last
    vector<double> cellVal(K, 0);
    for (int o : open) {
        sortSitesByKey(cell[o].begin(), cell[o].end(), true, [&](int a) { return rew[a] - dist[o][a]; });
        for (int i = 0; i < (int)cell[o].size() && i < maxSize[o]; i++) cellVal[o] += rew[cell[o][i]] - dist[o][cell[o][i]];
    }
    sort(open.begin(), open.end(), [&](int a, int b) { return cellVal[a] > cellVal[b]; });
    vector<int> used(NS, 0);
    vector<vector<int>> cand(K);
    long long work = 0;
    int Tcap = 0, maxCap = 0;
    vector<char> wTaken(nativeW ? W : 0, 0);
    vector<int> wOwn(nativeW ? W : 0, -1);  // office whose team claimed the worker
    vector<int> picked;
    for (int o : open) {
        Mask have;
        int lim = min(2 * maxSize[o] + 10, maxSize[o] + 60);
        for (int s : cell[o]) {
            if ((int)cand[o].size() >= lim) break;
            if (forced) {  // skill set fixed by the caller (fewSearch): only sites it covers
                if (((*forced)[o].none()) || (smask[s] & ~(*forced)[o]).any()) continue;
                cand[o].push_back(s);
                continue;
            }
            Mask needNew = smask[s] & ~have;
            if (nativeW && balNativeClaim) {
                // real (multi-skill) workers: extend the office's team greedily to cover the new skills
                Mask miss = needNew;
                picked.clear();
                bool ok = true;
                while (miss.any() && ok) {
                    int k = 0;
                    while (!miss[k]) k++;
                    int bw = -1, bc = 0, bp = INT32_MAX;
                    for (int w : skW[k]) {
                        if (wTaken[w] || find(picked.begin(), picked.end(), w) != picked.end()) continue;
                        int c = (realW[w] & miss).count(), pc = realW[w].count();
                        if (c > bc || (c == bc && pc < bp)) bc = c, bp = pc, bw = w;
                    }
                    if (bw < 0) ok = false;
                    else picked.push_back(bw), miss &= ~realW[bw];
                }
                if (!ok) continue;
                for (int w : picked) wTaken[w] = 1, wOwn[w] = o, have |= realW[w];
                cand[o].push_back(s);
                continue;
            }
            bool ok = true;
            for (int k = 0; k < NS && ok; k++)
                if (needNew[k] && used[k] >= availSkill[k]) ok = false;
            if (!ok) continue;
            for (int k = 0; k < NS; k++)
                if (needNew[k]) used[k]++;
            have |= needNew;
            cand[o].push_back(s);
        }
        if (cand[o].empty()) continue;
        int cap = min(maxSize[o], (int)cand[o].size());
        vector<int> tk;
        for (int s : cand[o]) tk.push_back(ntask[s]);
        sort(tk.rbegin(), tk.rend());
        int tt = 0;
        for (int i = 0; i < cap; i++) tt += tk[i];
        Tcap = max(Tcap, tt);
        maxCap = max(maxCap, cap);
    }
    if (Tcap == 0) return none;
    // full DP over (count, tasks) when affordable, else tasks only over the top-maxSize candidates
    for (int o : open) work += (long long)cand[o].size() * (min(maxSize[o], (int)cand[o].size()) + 1) * (Tcap + 1);
    bool full = work <= 120000000LL;
    if (!full) {
        work = 0;
        for (int o : open) {
            if ((int)cand[o].size() > maxSize[o]) cand[o].resize(maxSize[o]);
            work += (long long)cand[o].size() * (Tcap + 1);
        }
        if (work > 300000000LL) return none;
    }
    const float NEG = -1e30f;
    // tab[o][c * (Tcap + 1) + t]: best profit with c sites (full) / any count (c = 0 row), t tasks
    vector<vector<float>> tab(K);
    vector<int> capOf(K, 0);
    for (int o : open) {
        if (cand[o].empty()) continue;
        if (elapsed() > lvHard) return lvDpCut++, none;
        int C = full ? min(maxSize[o], (int)cand[o].size()) : 0;
        capOf[o] = C;
        vector<float>& dp = tab[o];
        dp.assign((size_t)(C + 1) * (Tcap + 1), NEG);
        dp[0] = 0;
        int done = 0;
        for (int s : cand[o]) {
            float pr = rew[s] - dist[o][s];
            int t = ntask[s];
            done++;
            if (full) {
                for (int c = min(C, done); c >= 1; c--) {
                    float* to = &dp[(size_t)c * (Tcap + 1)];
                    const float* fr = &dp[(size_t)(c - 1) * (Tcap + 1)];
                    for (int x = Tcap; x >= t; x--)
                        if (fr[x - t] + pr > to[x]) to[x] = fr[x - t] + pr;
                }
            } else {
                for (int x = Tcap; x >= t; x--)
                    if (dp[x - t] + pr > dp[x]) dp[x] = dp[x - t] + pr;
            }
        }
    }
    // task-free sites: count-only items. zpre[o][z] = profit of the z best ones of the cell; a zone
    // with c task sites takes z = min(free, window top - c, maxSize - c) of them (all are profitable)
    vector<vector<double>> zpre(K);
    bool anyZ = false;
    int maxTot = maxCap;
    for (int o : open) {
        if (tab[o].empty()) continue;
        sortSitesByKey(zcell[o].begin(), zcell[o].end(), true, [&](int a) { return rew[a] - dist[o][a]; });
        zpre[o].assign(zcell[o].size() + 1, 0.0);
        for (size_t i = 0; i < zcell[o].size(); i++) zpre[o][i + 1] = zpre[o][i] + rew[zcell[o][i]] - dist[o][zcell[o][i]];
        if (!zcell[o].empty()) anyZ = true;
        maxTot = max(maxTot, min(maxSize[o], capOf[o] + (int)zcell[o].size()));
    }
    if (!zFix) anyZ = false;
    // zone with c task sites, total count in [lo, hi]: number of task-free sites to add (-1: none fits)
    auto zTake = [&](int o, int c, int lo, int hi) {
        int nz = (int)zpre[o].size() - 1;
        int z = min(nz, min(hi, maxSize[o]) - c);
        return z < 0 || c + z < lo ? -1 : z;
    };
    // scan levels
    static const int dList[] = {0, 1, 2, 3, 5, 8};
    bool window = full && A < (anyZ ? maxTot : maxCap);
    double bestV = 0;
    int bT = -1, bD = 0, bLo = 0;
    vector<float> bc(maxCap + 1);
    vector<double> winSum(maxTot + 2);
    bool late = false;
    // task-free sites widen the window scan to O(top x min(C, nz + A + 1)) per (T, d, office): when
    // that is large (many task-free sites), window starts are scanned on a stride first and refined
    // around the best start at the end (same bound as the DP tables)
    int loStride = 1, loMin = 1, loMax = INT32_MAX;
    if (window && anyZ) {
        double est = 0;
        for (int o : open) {
            if (tab[o].empty()) continue;
            int nz = (int)zpre[o].size() - 1, top = min(maxSize[o], capOf[o] + nz);
            est += (double)top * min(capOf[o], nz + A + 1);
        }
        est *= 6.0 * Tcap;
        static const double zScanCap = 3e7;
        if (zScanCap > 0 && est > zScanCap) loStride = (int)min(512.0, ceil(est / zScanCap));
        loStride = max(1, min(loStride, maxTot / 2));
    }
    auto loOk = [&](int lo) { return lo >= loMin && lo <= loMax && (loStride == 1 || lo % loStride == 0); };
    // Levels are scanned coarse to fine (a strided pass, then around its best, then the rest): a scan
    // cut by the clock keeps a near-best level instead of only the lowest ones. Ties resolve as in an
    // ascending scan (lowest T, then d in list order, then lowest window), so a complete scan picks the
    // same plan whatever the order.
    int bDi = 0;
    auto better = [&](double v, int T, int di, int lo) {
        if (v != bestV) return v > bestV;
        return bT >= 0 && (T < bT || (T == bT && (di < bDi || (di == bDi && lo < bLo))));
    };
    double scanEnd = lvHard;  // the coarse pass may use the overrun allowance, later passes not
    auto scanT = [&](int T) {
        for (int di = 0; di < (int)(sizeof dList / sizeof dList[0]); di++) {
            int d = dList[di];
            if (T + d > Tcap) break;
            if (elapsed() > scanEnd) {
                late = true;
                break;
            }
            double pen = alpha * d;
            if (!window) {
                double v = -pen;
                for (int o : open) {
                    if (tab[o].empty()) continue;
                    double m = NEG;
                    for (int c = 0; c <= capOf[o]; c++) {
                        const float* row = &tab[o][(size_t)c * (Tcap + 1)];
                        float r = NEG;
                        for (int x = T; x <= T + d; x++) r = max(r, row[x]);
                        if (r <= NEG / 2) continue;
                        int z = anyZ && full ? zTake(o, c, 0, maxSize[o]) : 0;
                        if (z >= 0) m = max(m, (double)r + (z > 0 ? zpre[o][z] : 0.0));
                    }
                    if (m > NEG / 2 && m - ocost[o] > 0) v += m - ocost[o];
                }
                if (better(v, T, di, 0)) bestV = v, bT = T, bD = d, bDi = di, bLo = 0;
            } else {
                fill(winSum.begin(), winSum.end(), 0.0);
                for (int o : open) {
                    if (tab[o].empty()) continue;
                    int C = capOf[o];
                    for (int c = 0; c <= maxCap; c++) bc[c] = NEG;
                    for (int c = 1; c <= C; c++) {
                        const float* row = &tab[o][(size_t)c * (Tcap + 1)];
                        for (int x = T; x <= T + d; x++) bc[c] = max(bc[c], row[x]);
                    }
                    if (anyZ) {
                        int nz = (int)zpre[o].size() - 1, top = min(maxSize[o], C + nz);
                        for (int lo = max(1, loMin); lo <= min(top, loMax); lo++) {
                            if (!loOk(lo)) continue;
                            double m = NEG;
                            for (int c = max(1, lo - nz); c <= min(C, lo + A); c++) {
                                if (bc[c] <= NEG / 2) continue;
                                int z = zTake(o, c, lo, lo + A);
                                if (z >= 0) m = max(m, (double)bc[c] + zpre[o][z]);
                            }
                            if (m > NEG / 2 && m - ocost[o] > 0) winSum[lo] += m - ocost[o];
                        }
                    } else
                    for (int lo = 1; lo <= C; lo++) {  // windows starting above C hold nothing of o
                        float m = NEG;
                        for (int c = lo; c <= min(C, lo + A); c++) m = max(m, bc[c]);
                        if (m > NEG / 2 && m - ocost[o] > 0) winSum[lo] += m - ocost[o];
                    }
                }
                for (int lo = 1; lo <= (anyZ ? maxTot : maxCap); lo++)
                    if ((!anyZ || loOk(lo)) && better(winSum[lo] - pen, T, di, lo)) bestV = winSum[lo] - pen, bT = T, bD = d, bDi = di, bLo = lo;
            }
        }
    };
    {
        static const int lvStrideDiv = 32;
        int stride = lvStrideDiv > 0 ? max(1, Tcap / lvStrideDiv) : 1;
        vector<char> doneT(Tcap + 1, 0);
        for (int T = stride; T <= Tcap && !late; T += stride) doneT[T] = 1, scanT(T);
        scanEnd = endTime;
        if (bT > 0)
            for (int T = max(1, bT - stride + 1); T <= min(Tcap, bT + stride - 1) && !late; T++)
                if (!doneT[T]) doneT[T] = 1, scanT(T);
        for (int T = 1; T <= Tcap && !late; T++)
            if (!doneT[T]) doneT[T] = 1, scanT(T);
        if (loStride > 1 && bT > 0) {  // strided window starts: every start around the best one
            loMin = max(1, bLo - loStride + 1), loMax = bLo + loStride - 1, loStride = 1;
            scanEnd = max(scanEnd, min(lvHard, elapsed() + 0.05));
            bool lt = late;
            late = false;
            scanT(bT);
            late = late || lt;
        }
    }
    lvScanCut += late;
    if (bT < 0) return none;
    // rebuild the chosen plan (DP with decisions, one office at a time); native workers: the claimed
    // teams go along (buildWorkers reuses them instead of re-deriving teams in another order)
    vector<int> asg(nativeW && ((balNativeClaim && !forced) || team) ? AS : n, -1);
    for (int w = 0; w < (int)wOwn.size() && (int)asg.size() == AS && AS > n && !team; w++) asg[n + w] = wOwn[w];
    if (team && (int)asg.size() == AS)  // fewSearch's real (multi-skill) worker teams go along
        for (int w = 0; w < W && w < (int)team->size(); w++) asg[n + w] = (*team)[w];
    for (int o : open) {
        if (tab[o].empty()) continue;
        int C = capOf[o], M = cand[o].size();
        int cLo = window ? bLo : 0, cHi = window ? min(C, bLo + A) : C;
        // find the best end state
        double m = NEG;
        int ec = -1, et = -1, ez = 0;
        if (anyZ && full) {  // task sites + the best task-free sites, total count in the window
            int nz = (int)zpre[o].size() - 1, wlo = window ? bLo : 0, whi = window ? bLo + A : maxSize[o];
            for (int c = max(0, wlo - nz); c <= min(C, whi); c++) {
                int z = zTake(o, c, wlo, whi);
                if (z < 0) continue;
                for (int x = bT; x <= bT + bD; x++) {
                    float v = tab[o][(size_t)c * (Tcap + 1) + x];
                    if (v <= NEG / 2) continue;
                    if (v + zpre[o][z] > m) m = v + zpre[o][z], ec = c, et = x, ez = z;
                }
            }
        } else
        for (int c = cLo; c <= cHi; c++)
            for (int x = bT; x <= bT + bD; x++) {
                float v = tab[o][(size_t)c * (Tcap + 1) + x];
                if (v > m) m = v, ec = c, et = x;
            }
        if (ec < 0 || m <= NEG / 2 || m - ocost[o] <= 0) continue;
        // decisions: take[i][c][t]
        int R = full ? C + 1 : 1;
        vector<vector<char>> take(M, vector<char>((size_t)R * (Tcap + 1), 0));
        vector<float> dp((size_t)R * (Tcap + 1), NEG);
        dp[0] = 0;
        for (int i = 0; i < M; i++) {
            int s = cand[o][i];
            float pr = rew[s] - dist[o][s];
            int t = ntask[s];
            if (full) {
                for (int c = min(C, i + 1); c >= 1; c--)
                    for (int x = Tcap; x >= t; x--) {
                        float v = dp[(size_t)(c - 1) * (Tcap + 1) + x - t] + pr;
                        if (v > dp[(size_t)c * (Tcap + 1) + x]) dp[(size_t)c * (Tcap + 1) + x] = v, take[i][(size_t)c * (Tcap + 1) + x] = 1;
                    }
            } else {
                for (int x = Tcap; x >= t; x--)
                    if (dp[x - t] + pr > dp[x]) dp[x] = dp[x - t] + pr, take[i][x] = 1;
            }
        }
        int c = full ? ec : 0, x = et;
        for (int i = M - 1; i >= 0 && x > 0; i--) {
            if (!take[i][(size_t)c * (Tcap + 1) + x]) continue;
            asg[cand[o][i]] = o;
            x -= ntask[cand[o][i]];
            if (full) c--;
        }
        // task-free sites ride along up to the count limit
        int cnt = full ? ec : 0, lim = window ? cHi : maxSize[o];
        if (anyZ && full) lim = ec + ez;
        if (!full)
            for (int s : cand[o]) cnt += asg[s] == o;
        sortSitesByKey(zcell[o].begin(), zcell[o].end(), true, [&](int a) { return rew[a] - dist[o][a]; });
        for (int s : zcell[o])
            if (cnt < lim) asg[s] = o, cnt++;
    }
    State st = fromAsg(asg);
    double lamSave = lambdaCnt, waSave = wAlpha, wcSave = wCost;
    lambdaCnt = 1e18, wAlpha = 1, wCost = 1;
    if (!countFeasible(st)) repairCounts(st);
    lambdaCnt = lamSave, wAlpha = waSave, wCost = wcSave;
    if (!countFeasible(st) || !validateFull(st).empty()) {
        return none;
    }
    *outVal = trueObjective(st);
    if (szDebug) fprintf(stderr, "level: open %zu T=%d d=%d lo=%d plan %.4f -> %.4f (%s)\n", open.size(), bT, bD, bLo, bestV, *outVal, full ? "full" : "tasks");
    return st.asg;
}

// Balanced cells for the level construction: with a large task-imbalance penalty the best plans
// give every open office the same task load T, and the level reachable by levelBuild is capped by
// the weakest power cell. Power weights are adjusted (capacity-constrained power diagram) until
// every cell holds about the same number of tasks on profitable sites, keeping each office inside
// its own cell (so a zone = hull of the office and sites of its cell stays inside the convex cell).
vector<double> balanceWeights(const vector<int>& open, double endTime) {
    int k = open.size();
    vector<double> w(K, 0.0);
    if (k < 2) return w;
    double x0 = 1e300, x1 = -1e300, y0 = 1e300, y1 = -1e300;
    for (int s = 0; s < n; s++) x0 = min(x0, px[s]), x1 = max(x1, px[s]), y0 = min(y0, py[s]), y1 = max(y1, py[s]);
    double area = max(1e-12, (x1 - x0) * (y1 - y0));
    double r2 = area / k;  // typical squared cell size
    vector<int> T(K, 0), owner(n, -1);
    // minimal squared distance from each open office to another open office (own-cell constraint)
    vector<double> bestW = w;
    double bestDev = 1e300;
    static const double eta0 = 0.1;
    static const int clampOn = 0;
    double eta = eta0;
    for (int it = 0; it < 400; it++) {
        if ((it & 3) == 0 && elapsed() > endTime) break;
        for (int o : open) T[o] = 0;
        long long tot = 0;
        for (int s = 0; s < n; s++) {
            if (ntask[s] == 0) continue;
            int bo = -1;
            double bv = 1e300;
            for (int o : open) {
                double dx = px[s] - px[n + o], dy = py[s] - py[n + o];
                double v = dx * dx + dy * dy - w[o];
                if (v < bv) bv = v, bo = o;
            }
            owner[s] = bo;
            if (bo >= 0 && rew[s] - dist[bo][s] > 0) T[bo] += ntask[s], tot += ntask[s];
        }
        double tau = (double)tot / k;
        if (tau <= 0) break;
        double dev = 0;
        for (int o : open) dev = max(dev, fabs(T[o] - tau));
        if (dev < bestDev) bestDev = dev, bestW = w;
        if (dev <= 1) break;
        for (int o : open) w[o] += eta * r2 * (tau - T[o]) / tau;
        // keep every office inside its own cell: w[q] - w[o] <= d2(o, q)
        for (int rep = 0; rep < 3 * clampOn; rep++)
            for (int o : open)
                for (int q : open) {
                    if (q == o) continue;
                    double d2 = pow(px[n + o] - px[n + q], 2) + pow(py[n + o] - py[n + q], 2);
                    if (w[q] - w[o] > d2) {
                        double mid = 0.5 * (w[q] + w[o]);
                        w[q] = mid + 0.5 * d2, w[o] = mid - 0.5 * d2;
                    }
                }
        if (it % 50 == 49) eta *= 0.7;
    }
    // final projection: every office inside its own cell (the weakest cells are left to levelBuild)
    int viol = 0;
    for (int rep = 0; rep < 60; rep++) {
        viol = 0;
        for (int o : open)
            for (int q : open) {
                if (q == o) continue;
                double d2 = pow(px[n + o] - px[n + q], 2) + pow(py[n + o] - py[n + q], 2);
                if (bestW[q] - bestW[o] > d2 * (1 - 1e-9)) {
                    viol++;
                    double m = 0.5 * (bestW[q] + bestW[o]);
                    bestW[q] = m + 0.49 * d2, bestW[o] = m - 0.49 * d2;
                }
            }
        if (!viol) break;
    }
    if (viol) {  // recount after the last pass; still violated: plain Voronoi cells
        viol = 0;
        for (int o : open)
            for (int q : open)
                if (q != o && bestW[q] - bestW[o] > (pow(px[n + o] - px[n + q], 2) + pow(py[n + o] - py[n + q], 2)) * (1 - 1e-9)) viol++;
        if (viol) bestW.assign(K, 0.0);
    }
    if (szDebug) fprintf(stderr, "balanceWeights: k=%d max dev %.1f, violations left %d\n", k, bestDev, viol);
    return bestW;
}
vector<int> balancedLevel(const vector<int>& open, double endTime, double* outVal) {
    *outVal = -1e300;
    vector<int> best(n, -1), op = open;
    // offices whose balanced cell still falls short of the chosen level are closed by levelBuild;
    // rebalancing without them lets the others absorb their sites (a few rounds)
    for (int round = 0; round < 3 && op.size() >= 2; round++) {
        double left = endTime - elapsed();
        if (left <= 0) break;
        double until = elapsed() + (round == 0 ? 0.5 : 1.0) * left;
        vector<double> w = balanceWeights(op, elapsed() + 0.5 * (until - elapsed()));
        double v;
        vector<int> a = levelBuild(op, w, until, &v);
        if (v <= -1e299) break;
        vector<char> z(K, 0);
        int served = 0;
        for (int s = 0; s < n; s++)
            if (a[s] >= 0) z[a[s]] = 1, served++;
        vector<int> zs;
        for (int o : op)
            if (z[o]) zs.push_back(o);
        if (szDebug) fprintf(stderr, "balancedLevel: %zu offices -> %zu zones, served %d/%d, value %.4f\n", op.size(), zs.size(), served, n, v);
        if (v > *outVal) *outVal = v, best = a;
        if (zs.size() == op.size() || zs.size() < 2) break;
        op = zs;
    }
    return best;
}

// Line-separated balanced cells (tight count window + task penalty). A power diagram gives every
// cell about the same number of sites, but the task mix of a cell is random, so an exact common
// (count s, tasks T) per zone costs many dropped sites. Here every pair of neighbouring cells gets
// its own separating line (initially the power bisector); a cell = the sites on its side of all
// its lines (convex, the office inside), so zones built inside the cells never conflict. A local
// search shifts and tilts single lines to trade boundary sites until every cell can pick exactly
// s sites with exactly T tasks; levelBuild then picks the subsets (exact DP per cell).
struct LineCells {
    int k = 0;
    vector<int> offs;                     // cell -> office
    vector<array<double, 3>> L;           // line: nx*x + ny*y < c  <=> side of the lower cell id
    vector<vector<pair<int, int>>> adj;   // cell -> (neighbour cell, line id)
    vector<vector<int>> cand;             // site -> candidate cells
    vector<vector<int>> near;             // cell -> sites having it as a candidate
    vector<vector<double>> nearX, nearY;  // their coordinates
    vector<vector<int>> nearOwn;          // cell -> own[] of its near sites (a mirror of own, see setOwn)
    vector<vector<int>> candIdx;          // site -> its index in near[cand[site][i]]
    void syncNearOwn() {
        nearOwn.resize(near.size());
        for (size_t a = 0; a < near.size(); a++) {
            nearOwn[a].resize(near[a].size());
            for (size_t i = 0; i < near[a].size(); i++) nearOwn[a][i] = own[near[a][i]];
        }
    }
    void setOwn(int p, int nw) {
        own[p] = nw;
        for (size_t i = 0; i < cand[p].size(); i++) nearOwn[cand[p][i]][candIdx[p][i]] = nw;
    }
    vector<int> own;                      // site -> cell or -1
    vector<vector<int>> hist;             // cell -> histogram of task counts of its sites
    vector<int> cnt;
    int tmax = 0;
    // per cell, its lines with the sign folded in (s = +1 if a < neighbour, else -1): outside iff
    // s*l0*x + s*l1*y - s*l2 >= 0, which is exactly the signed test below (negation is exact)
    vector<vector<array<double, 3>>> sl;
    vector<vector<int>> slId;
    vector<array<int, 4>> lpos;  // line -> (cell, index, cell, index)
    void buildSL() {
        int kk = adj.size();
        sl.assign(kk, {}), slId.assign(kk, {});
        lpos.assign(L.size(), {-1, -1, -1, -1});
        for (int a = 0; a < kk; a++)
            for (auto [j, li] : adj[a]) {
                double s = a < j ? 1.0 : -1.0;
                auto& lp = lpos[li];
                if (lp[0] < 0) lp[0] = a, lp[1] = sl[a].size();
                else lp[2] = a, lp[3] = sl[a].size();
                sl[a].push_back({s * L[li][0], s * L[li][1], s * L[li][2]});
                slId[a].push_back(li);
            }
    }
    void setLine(int li, const array<double, 3>& nl) {
        L[li] = nl;
        const auto& lp = lpos[li];
        for (int q = 0; q < 4; q += 2) {
            int a = lp[q];
            if (a < 0) continue;
            int j = adj[a][lp[q + 1]].first;
            double sg = a < j ? 1.0 : -1.0;
            sl[a][lp[q + 1]] = {sg * nl[0], sg * nl[1], sg * nl[2]};
        }
    }
    bool inside(double x, double y, int a) const {
        for (const auto& l : sl[a])
            if (l[0] * x + l[1] * y - l[2] >= 0) return false;
        return true;
    }
    bool inside(double x, double y, int a, int skipLine, const array<double, 3>* alt) const {
        const auto& la = sl[a];
        const auto& ids = slId[a];
        for (size_t i = 0; i < la.size(); i++) {
            if (ids[i] == skipLine) {
                double sg = a < adj[a][i].first ? 1.0 : -1.0;
                if ((sg * (*alt)[0]) * x + (sg * (*alt)[1]) * y - sg * (*alt)[2] >= 0) return false;
                continue;
            }
            const auto& l = la[i];
            if (l[0] * x + l[1] * y - l[2] >= 0) return false;
        }
        return true;
    }
};
static const bool lcSq = true;  // squared defects diffuse
// defect of a cell for target (s, T): sites missing + task distance of the achievable s-subset sums
int lcA = 0;  // count window width for the line cells (counts in [s, s + lcA])
static long long lcDefect(const vector<int>& h, int c, int s, int T, int tmax) {
    if (tmax <= 2) {
        // sites with 0, 1, 2 tasks: keep c1 one-task and c2 two-task sites with c1 + 2 c2 = T
        // (as many one-task as the window allows), task-free sites fill up to the window; cost =
        // dropped sites + squared penalties for a missing level or a count outside the window
        int h0 = h[0], h1 = tmax >= 1 ? h[1] : 0, h2 = tmax >= 2 ? h[2] : 0;
        int L = s, U = s + lcA;
        if (h1 + 2 * h2 < T) {
            int d = T - h1 - 2 * h2, kept = min(c, U), under = max(0, L - c);
            return (c - kept) + 4LL * d + (long long)d * d + 3LL * under * under;
        }
        int c1min = max(0, T - 2 * h2), c1max = min(h1, T);
        if ((T - c1min) & 1) c1min++;
        if ((T - c1max) & 1) c1max--;
        if (c1min > c1max) return c + 5;  // parity: no one-task site to make T odd
        int c1 = min(c1max, 2 * U - T);
        if ((T - c1) & 1) c1--;
        if (c1 < c1min) {
            int over = (T + c1min) / 2 - U;
            return (c - U) + 3LL * over * over + 2;
        }
        int kept = (T + c1) / 2;
        kept += min(h0, U - kept);
        int under = max(0, L - kept);
        return (c - kept) + 3LL * under * under;
    }
    int m = min(c, s), lo = 0, hi = 0, left = m;
    for (int t = 0; t <= tmax && left > 0; t++) {
        int u = min(left, h[t]);
        lo += u * t, left -= u;
    }
    left = m;
    for (int t = tmax; t >= 0 && left > 0; t--) {
        int u = min(left, h[t]);
        hi += u * t, left -= u;
    }
    int miss = s - m;
    lo += miss * 0, hi += miss * tmax;
    int e = max(0, lo - T) + max(0, T - hi);
    return lcSq ? 3LL * miss * miss + (long long)e * e : 2LL * miss + e;
}
static bool lcSetup(LineCells& C, vector<double>& w, const vector<int>& openIn, int s, double endTime) {
    vector<int> none;
    for (int o : openIn) {
        bool dup = false;
        for (int q : C.offs)
            if (px[n + o] == px[n + q] && py[n + o] == py[n + q]) dup = true;
        if (!dup && maxSize[o] >= s) C.offs.push_back(o);
    }
    int k = C.k = C.offs.size();
    if (k < 2 || s <= 0) return false;
    w.assign(K, 0.0);
    {
        // power weights giving every cell about n / k sites (counts, not tasks, are balanced here)
        double x0 = 1e300, x1 = -1e300, y0 = 1e300, y1 = -1e300;
        for (int p = 0; p < n; p++) x0 = min(x0, px[p]), x1 = max(x1, px[p]), y0 = min(y0, py[p]), y1 = max(y1, py[p]);
        double r2 = max(1e-12, (x1 - x0) * (y1 - y0)) / k, tau = (double)n / k, eta = 0.1;
        vector<int> c(K);
        vector<double> bw = w;
        double bestDev = 1e300;
        for (int itw = 0; itw < 300; itw++) {
            if ((itw & 7) == 0 && elapsed() > endTime) break;
            for (int o : C.offs) c[o] = 0;
            for (int p = 0; p < n; p++) {
                int bo = -1;
                double bv = 1e300;
                for (int o : C.offs) {
                    double v = pow(px[p] - px[n + o], 2) + pow(py[p] - py[n + o], 2) - w[o];
                    if (v < bv) bv = v, bo = o;
                }
                c[bo]++;
            }
            double dev = 0;
            for (int o : C.offs) dev = max(dev, fabs(c[o] - tau));
            if (dev < bestDev) bestDev = dev, bw = w;
            if (dev <= 1) break;
            for (int o : C.offs) w[o] += eta * r2 * (tau - c[o]) / tau;
            // stay feasible while balancing: every office inside its own cell
            for (int rep = 0; rep < 2; rep++)
                for (int o : C.offs)
                    for (int q : C.offs) {
                        if (q == o) continue;
                        double d2 = pow(px[n + o] - px[n + q], 2) + pow(py[n + o] - py[n + q], 2);
                        if (w[q] - w[o] > 0.98 * d2) {
                            double mid = 0.5 * (w[q] + w[o]);
                            w[q] = mid + 0.49 * d2, w[o] = mid - 0.49 * d2;
                        }
                    }
            if (itw % 50 == 49) eta *= 0.7;
        }
        if (szDebug) fprintf(stderr, "lcSetup: count dev %.1f (tau %.1f)\n", bestDev, tau);
        w = bw;
        // keep every office inside its own cell
        for (int rep = 0; rep < 60; rep++) {
            int viol = 0;
            for (int o : C.offs)
                for (int q : C.offs) {
                    if (q == o) continue;
                    double d2 = pow(px[n + o] - px[n + q], 2) + pow(py[n + o] - py[n + q], 2);
                    if (w[q] - w[o] > d2 * (1 - 1e-9)) {
                        viol++;
                        double mid = 0.5 * (w[q] + w[o]);
                        w[q] = mid + 0.49 * d2, w[o] = mid - 0.49 * d2;
                    }
                }
            if (!viol) break;
        }
    }
    for (int s2 = 0; s2 < n; s2++) C.tmax = max(C.tmax, ntask[s2]);
    // neighbour pairs: each cell with its 10 nearest cells (symmetric)
    vector<vector<char>> isNb(k, vector<char>(k, 0));
    for (int a = 0; a < k; a++) {
        vector<pair<double, int>> v;
        int oa = C.offs[a];
        for (int b = 0; b < k; b++)
            if (b != a) v.push_back({pow(px[n + oa] - px[n + C.offs[b]], 2) + pow(py[n + oa] - py[n + C.offs[b]], 2), b});
        int m = min((int)v.size(), 16);
        partial_sort(v.begin(), v.begin() + m, v.end());
        for (int i = 0; i < m; i++) isNb[a][v[i].second] = isNb[v[i].second][a] = 1;
    }
    C.adj.assign(k, {});
    for (int a = 0; a < k; a++)
        for (int b = a + 1; b < k; b++) {
            if (!isNb[a][b]) continue;
            int oa = C.offs[a], ob = C.offs[b];
            // power bisector: 2 p.(ob - oa) < |ob|^2 - |oa|^2 + w_a - w_b on a's side
            double nx = 2 * (px[n + ob] - px[n + oa]), ny = 2 * (py[n + ob] - py[n + oa]);
            double c = px[n + ob] * px[n + ob] + py[n + ob] * py[n + ob] - px[n + oa] * px[n + oa] - py[n + oa] * py[n + oa] + w[oa] - w[ob];
            double nn = hypot(nx, ny);
            if (nn <= 0) continue;
            int li = C.L.size();
            C.L.push_back({nx / nn, ny / nn, c / nn});
            C.adj[a].push_back({b, li}), C.adj[b].push_back({a, li});
        }
    C.buildSL();
    // offices must lie strictly inside their own cells
    for (int a = 0; a < k; a++)
        if (!C.inside(px[n + C.offs[a]], py[n + C.offs[a]], a)) return false;
    // site candidates: 5 nearest cells by power distance
    C.cand.assign(n, {});
    C.candIdx.assign(n, {});
    C.near.assign(k, {});
    for (int p = 0; p < n; p++) {
        vector<pair<double, int>> v;
        for (int a = 0; a < k; a++) {
            int o = C.offs[a];
            v.push_back({pow(px[p] - px[n + o], 2) + pow(py[p] - py[n + o], 2) - w[o], a});
        }
        int m = min(k, 5);
        partial_sort(v.begin(), v.begin() + m, v.end());
        for (int i = 0; i < m; i++) C.cand[p].push_back(v[i].second), C.near[v[i].second].push_back(p);
        C.candIdx[p].clear();
        for (int i = 0; i < m; i++) C.candIdx[p].push_back((int)C.near[v[i].second].size() - 1);
    }
    C.nearX.assign(k, {}), C.nearY.assign(k, {});
    for (int a = 0; a < k; a++)
        for (int p : C.near[a]) C.nearX[a].push_back(px[p]), C.nearY[a].push_back(py[p]);
    C.own.assign(n, -1);
    C.hist.assign(k, vector<int>(C.tmax + 1, 0));
    C.cnt.assign(k, 0);
    for (int p = 0; p < n; p++)
        for (int a : C.cand[p])
            if (C.inside(px[p], py[p], a)) {
                C.own[p] = a, C.cnt[a]++, C.hist[a][ntask[p]]++;
                break;
            }
    return true;
}
vector<int> lineLevel(LineCells& C, const vector<double>& w, int s, int T, double endTime, double* outVal, long long* outDef = nullptr) {
    *outVal = -1e300;
    vector<int> none;
    int k = C.k;
    vector<long long> def(k);
    long long totDef = 0;
    for (int a = 0; a < k; a++) totDef += def[a] = lcDefect(C.hist[a], C.cnt[a], s, T, C.tmax);
    long long startDef = totDef;
    // local search on single lines: shift a line past the nearest site of the other side (one site
    // changes cell) or tilt it through two boundary sites (one site each way); accept moves that
    // lower the total defect, and level moves half of the time (defects diffuse along chains)
    vector<int> aff, newOwn;
    vector<int> h1, h2;
    vector<pair<double, int>> LA, LB;
    C.syncNearOwn();
    long long it = 0, acc = 0;
    double lsT0 = elapsed(), temp = 1.0;
    long long bestTot = totDef;
    vector<array<double, 3>> bL = C.L;
    vector<int> bOwn = C.own;
    static const double lcT0 = 1.5;
    while (totDef > 0) {
        if ((it & 15) == 0) {
            double t = elapsed();
            if (t > endTime - 0.02) break;
            double fr = (t - lsT0) / max(1e-9, endTime - lsT0);
            temp = lcT0 * pow(0.05 / lcT0, min(1.0, fr / 0.85));
        }
        it++;
        int a = irand(k);
        for (int tries = 0; def[a] == 0 && tries < 16; tries++) a = irand(k);
        if (def[a] == 0 || C.adj[a].empty() || C.near[a].empty()) continue;
        // neighbour across a real boundary: the owner of a site near a (else any neighbour)
        int b = -1, li = -1;
        for (int t = 0; t < 6 && b < 0; t++) {
            int p = C.near[a][irand(C.near[a].size())], o = C.own[p];
            if (o < 0 || o == a) continue;
            for (auto [j, l2] : C.adj[a])
                if (j == o) b = j, li = l2;
        }
        if (b < 0) {
            auto pr = C.adj[a][irand(C.adj[a].size())];
            b = pr.first, li = pr.second;
        }
        const array<double, 3> l = C.L[li];
        double sgn = a < b ? 1.0 : -1.0;
        double ux = sgn * l[0], uy = sgn * l[1];
        // what a needs
        const vector<int>& ha = C.hist[a];
        int m = min(C.cnt[a], s), lo = 0, hi = 0, left = m;
        for (int t = 0; t <= C.tmax && left > 0; t++) lo += min(left, ha[t]) * t, left -= min(left, ha[t]);
        left = m;
        for (int t = C.tmax; t >= 0 && left > 0; t--) hi += min(left, ha[t]) * t, left -= min(left, ha[t]);
        int want = 0;  // +1: a needs more tasks, -1: fewer
        if (C.cnt[a] >= s) want = lo > T ? -1 : hi < T ? 1 : 0;
        bool needCnt = C.cnt[a] < s;
        bool shrink = false;
        if (lcA > 0) {  // count window: only the task total matters (excess tasks = dropped sites)
            int tk = 0;
            for (int t = 0; t <= C.tmax; t++) tk += t * ha[t];
            needCnt = tk < T || C.cnt[a] < s;
            shrink = tk > T + 1 && C.cnt[a] > s;
            want = 0;
        }
        // the 6 smallest (key, site) pairs of each side in increasing order (the pairs are distinct,
        // so this is exactly the head of the sorted list), kept by insertion during the scan
        const int mm = 6;
        pair<double, int> topA[mm], topB[mm];
        int cntA = 0, cntB = 0;
        {
            // near sites with their coordinates and owners stored contiguously (same values as px / py / own)
            const int* np = C.near[a].data();
            const double* nx = C.nearX[a].data();
            const double* ny = C.nearY[a].data();
            const int* nown = C.nearOwn[a].data();
            const double l0 = l[0], l1 = l[1], l2 = l[2];
            auto ins = [](pair<double, int>* top, int& cnt, pair<double, int> e) {
                int j;
                if (cnt < mm) j = cnt++;
                else if (e < top[mm - 1]) j = mm - 1;
                else return;
                while (j > 0 && e < top[j - 1]) top[j] = top[j - 1], j--;
                top[j] = e;
            };
            int totA = 0, totB = 0;
            for (size_t i = 0, e = C.near[a].size(); i < e; i++) {
                int o = nown[i];
                if (o == a) {
                    double v = sgn * (l0 * nx[i] + l1 * ny[i] - l2);
                    totA++;
                    if (cntA < mm || -v <= topA[mm - 1].first) ins(topA, cntA, {-v, np[i]});
                } else if (o == b || o < 0) {
                    double v = sgn * (l0 * nx[i] + l1 * ny[i] - l2);
                    if (v > 0) {
                        totB++;
                        if (cntB < mm || v <= topB[mm - 1].first) ins(topB, cntB, {v, np[i]});
                    }
                }
            }
            if (totA == 0 && totB == 0) continue;
        }
        LA.assign(topA, topA + cntA), LB.assign(topB, topB + cntB);
        int na = cntA, nbq = cntB;
        array<double, 3> nl = l;
        int mode = needCnt ? (irand(3) ? 0 : 2) : shrink ? (irand(3) ? 1 : 2) : want != 0 ? (irand(4) ? 2 : irand(2)) : irand(2);
        if (mode == 0 && nbq > 0) {  // a grows by the nearest site across the line
            double d = LB[0].first;
            double d2 = nbq > 1 ? LB[1].first : d * 2 + 1e-9;
            nl[2] += sgn * (0.5 * (d + d2));
        } else if (mode == 1 && na > 0) {  // a shrinks by its nearest site
            double d = LA[0].first;
            double d2 = na > 1 ? LA[1].first : d * 2 + 1e-9;
            nl[2] -= sgn * (0.5 * (d + d2));
        } else if (na > 0 && nbq > 0) {  // tilt through P (to b) and Q (to a)
            int P = -1, Q = -1;
            for (int t = 0; t < 12 && (P < 0 || Q < 0); t++) {
                int i = irand(na), j = irand(nbq);
                int pp = LA[i].second, qq = LB[j].second;
                int dt = ntask[pp] - ntask[qq];
                if (want < 0 && dt <= 0) continue;
                if (want > 0 && dt >= 0) continue;
                P = pp, Q = qq;
            }
            if (P < 0) continue;
            double dpq = hypot(px[P] - px[Q], py[P] - py[Q]);
            if (dpq <= 0) continue;
            double e = 1e-7 * dpq;
            double x1 = px[P] - e * ux, y1 = py[P] - e * uy, x2 = px[Q] + e * ux, y2 = py[Q] + e * uy;
            double dx = x2 - x1, dy = y2 - y1, dn = hypot(dx, dy);
            double mx = -dy / dn, my = dx / dn;
            if (mx * ux + my * uy < 0) mx = -mx, my = -my;
            if (mx * ux + my * uy < 0.75) continue;  // too steep a turn
            double c2 = mx * x1 + my * y1;
            nl = {sgn * mx, sgn * my, sgn * c2};
        } else
            continue;
        {
            int oa = C.offs[a], ob = C.offs[b];
            double va = nl[0] * px[n + oa] + nl[1] * py[n + oa] - nl[2], vb = nl[0] * px[n + ob] + nl[1] * py[n + ob] - nl[2];
            bool okA = a < b ? va < 0 : va > 0, okB = b < a ? vb < 0 : vb > 0;
            if (!okA || !okB) continue;
        }
        // only sites on different sides of the old and the new line can change cell
        aff.clear();
        for (int q = 0; q < 2; q++) {
            const int c = q ? b : a;
            const int* np = C.near[c].data();
            const double* nx = C.nearX[c].data();
            const double* ny = C.nearY[c].data();
            const int* nown = C.nearOwn[c].data();
            for (size_t i = 0, e = C.near[c].size(); i < e; i++) {
                int o = nown[i];
                if (!(o == a || o == b || o < 0)) continue;
                int p = np[i];
                bool s1 = l[0] * nx[i] + l[1] * ny[i] - l[2] < 0, s2 = nl[0] * nx[i] + nl[1] * ny[i] - nl[2] < 0;
                if (s1 == s2) continue;
                if (q && find(C.cand[p].begin(), C.cand[p].end(), a) != C.cand[p].end()) continue;
                aff.push_back(p);
            }
        }
        if (aff.empty()) continue;
        h1 = C.hist[a], h2 = C.hist[b];
        int c1 = C.cnt[a], c2 = C.cnt[b];
        newOwn.resize(aff.size());
        for (size_t i = 0; i < aff.size(); i++) {
            int p = aff[i], o = C.own[p], nw;
            if (C.inside(px[p], py[p], a, li, &nl)) nw = a;
            else if (C.inside(px[p], py[p], b, li, &nl)) nw = b;
            else nw = (o == a || o == b) ? -1 : o;
            if (nw < 0 && o < 0) {  // a free site may belong to another candidate cell (unchanged region)
                for (int c : C.cand[p])
                    if (c != a && c != b && C.inside(px[p], py[p], c)) nw = c;
            }
            newOwn[i] = nw;
            if (nw == o) continue;
            if (o == a) h1[ntask[p]]--, c1--;
            if (o == b) h2[ntask[p]]--, c2--;
            if (nw == a) h1[ntask[p]]++, c1++;
            if (nw == b) h2[ntask[p]]++, c2++;
        }
        long long d1 = lcDefect(h1, c1, s, T, C.tmax), d2 = lcDefect(h2, c2, s, T, C.tmax);
        long long delta = d1 + d2 - def[a] - def[b];
        if (delta > 0 && urand() >= exp(-delta / temp)) continue;
        if (delta == 0 && irand(2)) continue;
        acc++;
        C.setLine(li, nl);
        for (size_t i = 0; i < aff.size(); i++) {
            int p = aff[i], o = C.own[p], nw = newOwn[i];
            if (o == nw) continue;
            if (o >= 0 && o != a && o != b) C.cnt[o]--, C.hist[o][ntask[p]]--;  // cannot happen (regions disjoint)
            if (nw >= 0 && nw != a && nw != b) C.cnt[nw]++, C.hist[nw][ntask[p]]++, def[nw] = lcDefect(C.hist[nw], C.cnt[nw], s, T, C.tmax);
            C.setOwn(p, nw);
        }
        C.hist[a] = h1, C.hist[b] = h2, C.cnt[a] = c1, C.cnt[b] = c2;
        def[a] = d1, def[b] = d2;
        totDef = 0;
        for (int x = 0; x < k; x++) totDef += def[x];
        if (totDef < bestTot) bestTot = totDef, bL = C.L, bOwn = C.own;
    }
    if (totDef > bestTot) {  // restore the best line set
        C.L = bL, C.own = bOwn;
        C.syncNearOwn();
        C.buildSL();
        for (int a = 0; a < k; a++) C.cnt[a] = 0, fill(C.hist[a].begin(), C.hist[a].end(), 0);
        for (int p = 0; p < n; p++)
            if (C.own[p] >= 0) C.cnt[C.own[p]]++, C.hist[C.own[p]][ntask[p]]++;
        totDef = 0;
        for (int a = 0; a < k; a++) totDef += def[a] = lcDefect(C.hist[a], C.cnt[a], s, T, C.tmax);
    }
    vector<int> owner(n, -1);
    for (int p = 0; p < n; p++)
        if (C.own[p] >= 0 && C.inside(px[p], py[p], C.own[p])) owner[p] = C.offs[C.own[p]];  // drop stale owners
    if (outDef) *outDef = totDef;
    double v, lsT1 = elapsed();
    vector<int> asg = levelBuild(C.offs, w, max(endTime, elapsed()) + 1.0, &v, nullptr, &owner);
    if (szDebug) fprintf(stderr, "lineLevel: k=%d s=%d T=%d defect %lld -> %lld (%lld it, %lld acc, ls %.3fs, build %.3fs) value %.4f\n", k, s, T, startDef, totDef, it, acc, lsT1 - lsT0, elapsed() - lsT1, v);
    if (v <= -1e299) return none;
    *outVal = v;
    return asg;
}
// Office set -> lineLevel plans for a few (s, T) around the capacity / task averages.
vector<int> lineLevels1(const vector<int>& op, double endTime, double* outVal) {
    *outVal = -1e300;
    vector<int> best;
    if (op.size() < 2) return best;
    long long tasks = 0;
    int prof = 0;
    for (int s = 0; s < n; s++) prof++, tasks += ntask[s];
    double mu = (double)tasks / max(1, prof);
    int k = op.size();
    vector<int> caps;
    for (int o : op) caps.push_back(maxSize[o]);
    sort(caps.begin(), caps.end());
    int s0 = min(caps[0], (int)floor(0.985 * prof / k));
    // sizes upwards from a few below the capacity / site average, tasks at the mean load: each
    // size starts from the balanced lines of the previous one; stop when a size does not balance
    vector<pair<int, int>> cfg;
    int tmaxAll = 0;
    for (int x = 0; x < n; x++) tmaxAll = max(tmaxAll, ntask[x]);
    lcA = tmaxAll <= 2 ? max(0, min(A, caps[0] / 3)) : 0;
    if (lcA > 0) {
        // count window: every cell carries T tasks (the task total split k ways, a little slack),
        // counts in a window of width A around T / mu, below the smallest capacity
        for (int dt : {0, 1, 2}) {
            int T = (int)floor((double)tasks / k) - dt;
            int U = min(caps[0], (int)lround(T / max(1e-9, mu)) + lcA / 2), L = max(1, U - lcA);
            if (T >= 1) cfg.push_back({L, T});
        }
    } else
        for (int ds = 3; ds >= 0; ds--) {
            int s = s0 - ds;
            if (s >= 1) cfg.push_back({s, (int)lround(s * mu)});
        }
    if (cfg.empty()) return best;
    LineCells C;
    vector<double> w;
    double st0 = elapsed();
    if (!lcSetup(C, w, op, cfg[0].first, elapsed() + 0.2 * max(0.0, endTime - elapsed()))) return best;
    if (szDebug) fprintf(stderr, "lineLevels: setup %.3fs, budget %.3fs\n", elapsed() - st0, endTime - elapsed());
    for (size_t i = 0; i < cfg.size(); i++) {
        double left = endTime - elapsed();
        if (left <= 0) break;
        double v;
        long long dfc = -1;
        vector<int> a = lineLevel(C, w, cfg[i].first, cfg[i].second, elapsed() + left / (cfg.size() - i), &v, &dfc);
        if (v > *outVal) *outVal = v, best = a;
        if (lcA == 0 && dfc != 0) break;
    }
    return best;
}
// The zone size is capped by the smallest maxSize of the set: also try the set with its small
// offices swapped for the nearest closed offices that can hold a site-average zone.
vector<int> lineLevels(const vector<int>& op, double endTime, double* outVal) {
    *outVal = -1e300;
    if (op.size() < 2) return {};
    int k = op.size(), sT = (int)floor(0.985 * n / k);
    vector<int> op2;
    vector<char> used(K, 0);
    for (int o : op) used[o] = 1;
    bool swapped = false;
    for (int o : op) {
        if (maxSize[o] >= sT) {
            op2.push_back(o);
            continue;
        }
        int bq = -1;
        double bd = 1e300;
        for (int q = 0; q < K; q++) {
            if (used[q] || maxSize[q] < sT) continue;
            double d = pow(px[n + o] - px[n + q], 2) + pow(py[n + o] - py[n + q], 2);
            if (d < bd) bd = d, bq = q;
        }
        if (bq >= 0) used[bq] = 1, op2.push_back(bq), swapped = true;
    }
    double t0 = elapsed(), v1 = -1e300, v2 = -1e300;
    vector<int> a1, a2;
    if (swapped && op2.size() >= 2) {
        a2 = lineLevels1(op2, t0 + 0.5 * (endTime - t0), &v2);
        a1 = lineLevels1(op, endTime, &v1);
    } else
        a1 = lineLevels1(op, endTime, &v1);
    if (v2 > v1) {
        *outVal = v2;
        return a2;
    }
    *outVal = v1;
    return a1;
}

// Office set of an assignment.
vector<int> openOfAsg(const vector<int>& asg) {
    vector<char> in(K, 0);
    for (int s = 0; s < n; s++)
        if (asg[s] >= 0) in[asg[s]] = 1;
    vector<int> op;
    for (int o = 0; o < K; o++)
        if (in[o]) op.push_back(o);
    return op;
}
// Search over the number of open offices: starting from the given sets, drop the offices with the
// smallest zones or add the closed offices farthest from the open ones, build the balanced level
// plan of each set and keep the best (step halves when neither direction improves).
inline double incumbentFloor(double inc) { return inc < -1e299 ? -1e300 : inc - 0.25 * fabs(inc); }
static const bool balKmeans = false;
static const double balFrac = 0.08;
static const double epBalFrac = 0.2;  // tight A: line cells need time
vector<int> levelSweep(const vector<int>& bestA, const vector<int>& softOp, double endTime, double incumbent, double* outV) {
    *outV = -1e300;
    vector<int> cntOf(K, 0);
    for (int s = 0; s < n; s++)
        if (bestA[s] >= 0) cntOf[bestA[s]]++;
    auto vary = [&](const vector<int>& base, int dlt) {
        vector<int> op = base;
        if (dlt < 0) {
            sort(op.begin(), op.end(), [&](int a, int b) { return cntOf[a] != cntOf[b] ? cntOf[a] > cntOf[b] : a < b; });
            if ((int)op.size() + dlt < 2) return vector<int>();
            op.resize(op.size() + dlt);
        } else {
            vector<char> in(K, 0);
            for (int o : op) in[o] = 1;
            vector<double> md(K, 1e300);
            for (int q = 0; q < K; q++)
                for (int o : op) md[q] = min(md[q], pow(px[n + o] - px[n + q], 2) + pow(py[n + o] - py[n + q], 2));
            for (int a = 0; a < dlt; a++) {
                int bo = -1;
                for (int q = 0; q < K; q++)
                    if (!in[q] && maxSize[q] > 0 && md[q] > 0 && (bo < 0 || md[q] > md[bo])) bo = q;
                if (bo < 0) break;
                in[bo] = 1, op.push_back(bo);
                for (int q = 0; q < K; q++) md[q] = min(md[q], pow(px[n + bo] - px[n + q], 2) + pow(py[n + bo] - py[n + q], 2));
            }
        }
        sort(op.begin(), op.end());
        return op;
    };
    double bestV = -1e300;
    vector<int> bestOut, bestSet;
    set<vector<int>> seen;
    auto eval = [&](const vector<int>& op) {
        if (op.size() < 2 || seen.count(op) || elapsed() > endTime) return false;
        seen.insert(op);
        double v, left = endTime - elapsed();
        vector<int> a;
        if (lineMode) v = -1e300, a.assign(n, -1);  // line cells only (dedicated phase)
        else a = balancedLevel(op, elapsed() + min(left, max(0.3, 0.2 * left)), &v);
        if (lineGate) {  // line-separated cells with one exact (count, tasks) per zone
            double lv;
            static const double llt = 0;
            vector<int> la = lineLevels(op, elapsed() + (llt > 0 ? llt : min(left, max(1.0, 0.5 * left))), &lv);
            if (lv > v) v = lv, a = la;
        }
        if (epOn && v > -1e299) {  // compare level plans after exact balancing
            State p = fromAsg(a);
            if (exactPolish(p, min(endTime + 0.5, elapsed() + max(0.3, 0.1 * left)))) a = p.asg, v = trueObjective(p);
        }
        if (szDebug) fprintf(stderr, "levelSweep: open %zu -> %.4f\n", op.size(), v);
        if (v > -1e299) poolAddAsg(a);
        if (v > bestV) {
            bestV = v, bestOut = a, bestSet = op;
            return true;
        }
        return false;
    };
    // spread office sets: k-means centroids of the task-bearing sites, each taken by the nearest
    // free office
    auto kmeansSet = [&](int k) {
        vector<int> pts;
        for (int s = 0; s < n; s++)
            if (ntask[s] > 0) pts.push_back(s);
        vector<int> op;
        if (k < 2 || (int)pts.size() < k) return op;
        vector<double> cx(k), cy(k);
        for (int i = 0; i < k; i++) {
            int s = pts[(long long)i * pts.size() / k];
            cx[i] = px[s], cy[i] = py[s];
        }
        vector<double> sx(k), sy(k), sw(k);
        for (int it = 0; it < 12 && elapsed() < endTime; it++) {
            fill(sx.begin(), sx.end(), 0), fill(sy.begin(), sy.end(), 0), fill(sw.begin(), sw.end(), 0);
            for (int s : pts) {
                int bi = 0;
                double bd = 1e300;
                for (int i = 0; i < k; i++) {
                    double d = pow(px[s] - cx[i], 2) + pow(py[s] - cy[i], 2);
                    if (d < bd) bd = d, bi = i;
                }
                sx[bi] += ntask[s] * px[s], sy[bi] += ntask[s] * py[s], sw[bi] += ntask[s];
            }
            for (int i = 0; i < k; i++)
                if (sw[i] > 0) cx[i] = sx[i] / sw[i], cy[i] = sy[i] / sw[i];
        }
        vector<char> used(K, 0);
        for (int i = 0; i < k; i++) {
            int bo = -1;
            double bd = 1e300;
            for (int o = 0; o < K; o++) {
                if (used[o] || maxSize[o] <= 0) continue;
                double d = pow(px[n + o] - cx[i], 2) + pow(py[n + o] - cy[i], 2);
                if (d < bd) bd = d, bo = o;
            }
            if (bo >= 0) used[bo] = 1, op.push_back(bo);
        }
        sort(op.begin(), op.end());
        return op;
    };
    vector<int> b0 = openOfAsg(bestA);
    eval(b0);
    if (!softOp.empty()) eval(softOp);
    if (balKmeans) {
        int k0 = b0.size();
        for (int k : {k0, (int)lround(k0 * 0.9), (int)lround(k0 * 1.1)}) {
            if (elapsed() > endTime) break;
            vector<int> op = kmeansSet(k);
            if (eval(op)) cntOf.assign(K, 0);  // a k-means set won: drop order by index
        }
    }
    if (bestSet.empty()) return {};
    // hopeless: no level plan near the incumbent (dedicated line phase: the first plan must be within 5%)
    double floorV = lineMode ? (incumbent < -1e299 ? -1e300 : incumbent - 0.05 * fabs(incumbent)) : incumbentFloor(incumbent);
    if (bestV < floorV) {
        *outV = bestV;
        return {};
    }
    int step = max(2, (int)bestSet.size() / 6);
    while (step >= 1 && elapsed() < endTime) {
        bool imp = false;
        for (int sg : {+1, -1}) {
            vector<int> op = vary(bestSet, sg * step);
            if (!op.empty() && eval(op)) {
                imp = true;
                break;
            }
        }
        if (!imp) step /= 2;
    }
    if (szDebug) fprintf(stderr, "levelSweep: best %zu offices %.4f (incumbent %.4f)\n", bestSet.size(), bestV, incumbent);
    *outV = bestV;
    return bestOut;
}

// ---------------------------------------------------------------- worker-team search
// When workers are scarce (many skills, few workers per skill) the binding decision is which
// workers go to which office. Zones are fixed to the Voronoi cells of the open offices (convex
// and disjoint, so geometry is free) and an office serves the most profitable sites of its cell
// whose skills its team covers. SA moves workers between offices and opens/closes offices.
struct WTState {
    vector<char> isOpen;
    vector<double> wgt;                 // power weights
    vector<int> nearO;                  // site -> nearest open office
    vector<vector<int>> allCell, cell;  // per office: all cell sites / profitable ones by profit desc
    vector<vector<int>> team;
    vector<int> wof;
    vector<Mask> U;
    vector<double> val;
    vector<int> cnt, tsk;
};
vector<int> wtSearch(double endTime, double scale, double* outVal, double rival) {
    *outVal = -1e300;
    vector<int> none(AS, -1);
    if (K == 0 || W == 0) return none;
    auto wm = [&](int w) -> const Mask& { return nativeW ? realW[w] : wmask[w]; };
    WTState X;
    X.wgt.assign(K, 0.0);
    // power distance (weights let cells adapt to capacities); every open office must stay in its own cell
    auto d2 = [&](int o, int s) { double dx = px[s] - px[n + o], dy = py[s] - py[n + o]; return dx * dx + dy * dy - X.wgt[o]; };
    auto pw = [&](const WTState& st, int o, int s) { double dx = px[s] - px[n + o], dy = py[s] - py[n + o]; return dx * dx + dy * dy - st.wgt[o]; };
    auto okCell = [&](const WTState& st, int a) {
        for (int q = 0; q < K; q++) {
            if (q == a || !st.isOpen[q]) continue;
            double dd = pow(px[n + a] - px[n + q], 2) + pow(py[n + a] - py[n + q], 2);
            if (dd - st.wgt[a] < -st.wgt[q] || dd - st.wgt[q] < -st.wgt[a]) return false;
        }
        return true;
    };
    double sig = 0;
    for (int o = 0; o < K; o++) {
        double bd = 1e300;
        for (int q = 0; q < K; q++)
            if (q != o && (px[n + o] != px[n + q] || py[n + o] != py[n + q])) bd = min(bd, pow(px[n + o] - px[n + q], 2) + pow(py[n + o] - py[n + q], 2));
        if (bd < 1e300) sig += bd;
    }
    sig = K > 1 ? sig / K : 1.0;
    if (!(sig > 0)) sig = 1.0;
    X.isOpen.assign(K, 0);
    for (int o = 0; o < K; o++) {  // one office per location
        bool dup = false;
        for (int q = 0; q < o && !dup; q++)
            if (X.isOpen[q] && px[n + o] == px[n + q] && py[n + o] == py[n + q]) dup = true;
        X.isOpen[o] = !dup && maxSize[o] > 0;  // an office that may serve no site is never opened
    }
    {
        bool anyOpen = false;
        for (int o = 0; o < K; o++) anyOpen |= X.isOpen[o] != 0;
        if (!anyOpen) return none;
    }
    X.nearO.assign(n, -1);
    X.allCell.assign(K, {}), X.cell.assign(K, {}), X.team.assign(K, {});
    X.wof.assign(W, -1), X.U.assign(K, Mask()), X.val.assign(K, 0), X.cnt.assign(K, 0), X.tsk.assign(K, 0);
    for (int s = 0; s < n; s++) {
        int bo = -1;
        double bv = 1e300;
        for (int o = 0; o < K; o++)
            if (X.isOpen[o] && d2(o, s) < bv) bv = d2(o, s), bo = o;
        X.nearO[s] = bo;
        X.allCell[bo].push_back(s);
    }
    auto rebuildCell = [&](WTState& st, int o) {
        st.cell[o].clear();
        for (int s : st.allCell[o])
            if (rew[s] - dist[o][s] > 0) st.cell[o].push_back(s);
        sortSitesByKey(st.cell[o].begin(), st.cell[o].end(), true, [&](int a) { return rew[a] - dist[o][a]; });
    };
    for (int o = 0; o < K; o++)
        if (X.isOpen[o]) rebuildCell(X, o);
    auto evalO = [&](const WTState& st, int o, const Mask& u, double& v, int& c, int& t) {
        v = 0, c = 0, t = 0;
        for (int s : st.cell[o]) {
            if (c >= maxSize[o]) break;
            if ((smask[s] & ~u).any()) continue;
            v += rew[s] - dist[o][s], c++, t += ntask[s];
        }
        if (c > 0) v -= ocost[o];
    };
    auto refresh = [&](WTState& st, int o) { evalO(st, o, st.U[o], st.val[o], st.cnt[o], st.tsk[o]); };
    // objective with up to two overridden offices
    auto totalWith = [&](const WTState& st, int o1, double v1, int c1, int t1, int o2, double v2, int c2, int t2) {
        double sum = 0;
        int cmin = INT32_MAX, cmax = INT32_MIN, tmin = INT32_MAX, tmax = INT32_MIN;
        for (int o = 0; o < K; o++) {
            double v = st.val[o];
            int c = st.cnt[o], t = st.tsk[o];
            if (o == o1) v = v1, c = c1, t = t1;
            if (o == o2) v = v2, c = c2, t = t2;
            if (c == 0) continue;
            sum += v;
            cmin = min(cmin, c), cmax = max(cmax, c), tmin = min(tmin, t), tmax = max(tmax, t);
        }
        if (cmax == INT32_MIN) return 0.0;
        return sum - alpha * (tmax - tmin) - 10.0 * scale * max(0, cmax - cmin - A);
    };
    auto total = [&](const WTState& st) { return totalWith(st, -1, 0, 0, 0, -1, 0, 0, 0); };
    for (int o = 0; o < K; o++)
        if (X.isOpen[o]) refresh(X, o);
    // greedy initial teams
    {
        vector<int> ord(W);
        for (int w = 0; w < W; w++) ord[w] = w;
        for (int i = W - 1; i > 0; i--) swap(ord[i], ord[irand(i + 1)]);
        for (int w : ord) {
            if (elapsed() > endTime) break;
            if (wm(w).none()) continue;
            double bg = 1e-12 * scale;
            int bo = -1;
            for (int o = 0; o < K; o++) {
                if (!X.isOpen[o] || (wm(w) & ~X.U[o]).none()) continue;
                double v;
                int c, t;
                evalO(X, o, X.U[o] | wm(w), v, c, t);
                if (v - X.val[o] > bg) bg = v - X.val[o], bo = o;
            }
            if (bo >= 0) X.team[bo].push_back(w), X.wof[w] = bo, X.U[bo] |= wm(w), refresh(X, bo);
        }
    }
    double cur = total(X), best = cur;
    WTState B = X;
    double T0 = 0.5 * scale, T1 = 0.002 * scale, t0 = elapsed(), tnow = t0;
    long long it = 0;
    bool checked = false, checkedEarly = false;
    vector<int> openL;
    auto teamMask = [&](const WTState& st, int o, int skip, int add) {
        Mask u;
        for (int w : st.team[o])
            if (w != skip) u |= wm(w);
        if (add >= 0) u |= wm(add);
        return u;
    };
    while (true) {
        int r = irand(100);
        if ((r >= 85 || (it & 63) == 0) && (tnow = elapsed()) > endTime) break;  // heavy moves: check every time
        // early in the slice give up when hopelessly behind the start we already have (wide
        // instances with merely few workers per skill), a quarter into it when still far behind
        if (!checkedEarly && tnow > t0 + 0.08 * (endTime - t0)) {
            checkedEarly = true;
            if (rival > 0 && best < 0.5 * rival) {
                if (szDebug) fprintf(stderr, "wtSearch: early abort (%.4f vs %.4f)\n", best, rival);
                *outVal = -1e300;
                return none;
            }
        }
        if (!checked && tnow > t0 + 0.25 * (endTime - t0)) {
            checked = true;
            if (rival > 0 && best < 0.85 * rival) {
                if (szDebug) fprintf(stderr, "wtSearch: abort (%.4f vs %.4f)\n", best, rival);
                *outVal = -1e300;
                return none;
            }
        }
        it++;
        double frac = (tnow - t0) / max(1e-9, endTime - t0);
        double T = T0 * pow(T1 / T0, min(1.0, frac));
        if (r < 85) {
            // move a worker to another office (or free it), or swap two workers
            int w = irand(W);
            if (wm(w).none()) continue;
            int a = X.wof[w], b;
            if (r < 8) b = -1;
            else {
                b = irand(K);
                if (!X.isOpen[b]) continue;
            }
            if (a == b) continue;
            int w2 = -1;
            if (r >= 70 && b >= 0 && !X.team[b].empty()) w2 = X.team[b][irand(X.team[b].size())];  // swap
            Mask ua, ub;
            double va = 0, vb = 0;
            int ca = 0, ta = 0, cb = 0, tb = 0;
            if (a >= 0) ua = teamMask(X, a, w, w2), evalO(X, a, ua, va, ca, ta);
            if (b >= 0) ub = teamMask(X, b, w2, w), evalO(X, b, ub, vb, cb, tb);
            double nv = totalWith(X, a, va, ca, ta, b, vb, cb, tb);
            if (nv >= cur || urand() < exp((nv - cur) / T)) {
                cur = nv;
                auto rem = [&](int o, int x) {
                    auto& v = X.team[o];
                    for (size_t i = 0; i < v.size(); i++)
                        if (v[i] == x) {
                            v[i] = v.back(), v.pop_back();
                            break;
                        }
                };
                if (a >= 0) rem(a, w);
                if (w2 >= 0) rem(b, w2);
                if (b >= 0) X.team[b].push_back(w);
                if (w2 >= 0 && a >= 0) X.team[a].push_back(w2);
                X.wof[w] = b;
                if (w2 >= 0) X.wof[w2] = a;
                if (a >= 0) X.U[a] = ua, X.val[a] = va, X.cnt[a] = ca, X.tsk[a] = ta;
                if (b >= 0) X.U[b] = ub, X.val[b] = vb, X.cnt[b] = cb, X.tsk[b] = tb;
            }
        } else if (r < 92) {
            // shift the power weight of an open office (its cell grows or shrinks)
            int o = irand(K);
            if (!X.isOpen[o]) continue;
            WTState Y = X;
            double dw = sig * (urand() * 2 - 1) * (1 - 0.8 * min(1.0, frac));
            Y.wgt[o] += dw;
            if (!okCell(Y, o)) continue;
            vector<int> touched = {o};
            if (dw > 0) {
                for (int s = 0; s < n; s++) {
                    int q = Y.nearO[s];
                    if (q != o && pw(Y, o, s) < pw(Y, q, s)) {
                        if (find(touched.begin(), touched.end(), q) == touched.end()) touched.push_back(q);
                        Y.nearO[s] = o;
                    }
                }
                for (int q : touched) {
                    if (q == o) continue;
                    vector<int> keep;
                    for (int s : Y.allCell[q])
                        if (Y.nearO[s] == q) keep.push_back(s);
                        else Y.allCell[o].push_back(s);
                    Y.allCell[q].swap(keep);
                }
            } else {
                vector<int> keep;
                for (int s : Y.allCell[o]) {
                    int bo = -1;
                    double bv = 1e300;
                    for (int q = 0; q < K; q++)
                        if (Y.isOpen[q] && pw(Y, q, s) < bv) bv = pw(Y, q, s), bo = q;
                    Y.nearO[s] = bo;
                    if (bo == o) keep.push_back(s);
                    else {
                        Y.allCell[bo].push_back(s);
                        if (find(touched.begin(), touched.end(), bo) == touched.end()) touched.push_back(bo);
                    }
                }
                Y.allCell[o].swap(keep);
            }
            if (touched.size() == 1) continue;
            for (int q : touched) rebuildCell(Y, q), refresh(Y, q);
            double nv = total(Y);
            if (nv >= cur || urand() < exp((nv - cur) / T)) cur = nv, X = std::move(Y);
        } else {
            // open or close an office; freed / free workers are re-placed greedily
            int o = irand(K);
            if (!X.isOpen[o] && maxSize[o] <= 0) continue;
            WTState Y = X;
            vector<int> touched;
            if (Y.isOpen[o]) {
                int no = 0;
                for (int q = 0; q < K; q++) no += Y.isOpen[q];
                if (no <= 1) continue;
                Y.isOpen[o] = 0;
                for (int w : Y.team[o]) Y.wof[w] = -1;
                Y.team[o].clear(), Y.U[o].reset();
                for (int s : Y.allCell[o]) {
                    int bo = -1;
                    double bv = 1e300;
                    for (int q = 0; q < K; q++)
                        if (Y.isOpen[q] && pw(Y, q, s) < bv) bv = pw(Y, q, s), bo = q;
                    Y.nearO[s] = bo, Y.allCell[bo].push_back(s);
                    if (find(touched.begin(), touched.end(), bo) == touched.end()) touched.push_back(bo);
                }
                Y.allCell[o].clear(), Y.cell[o].clear();
                Y.val[o] = 0, Y.cnt[o] = 0, Y.tsk[o] = 0;
            } else {
                bool dup = false;
                for (int q = 0; q < K && !dup; q++)
                    if (Y.isOpen[q] && px[n + o] == px[n + q] && py[n + o] == py[n + q]) dup = true;
                if (dup) continue;
                Y.isOpen[o] = 1;
                Y.wgt[o] = 0;
                if (!okCell(Y, o)) continue;
                for (int s = 0; s < n; s++) {
                    int q = Y.nearO[s];
                    if (pw(Y, o, s) < pw(Y, q, s)) {
                        if (find(touched.begin(), touched.end(), q) == touched.end()) touched.push_back(q);
                        Y.nearO[s] = o;
                    }
                }
                for (int q : touched) {
                    vector<int> keep;
                    for (int s : Y.allCell[q])
                        if (Y.nearO[s] == q) keep.push_back(s);
                        else Y.allCell[o].push_back(s);
                    Y.allCell[q].swap(keep);
                }
                touched.push_back(o);
            }
            for (int q : touched) rebuildCell(Y, q), refresh(Y, q);
            // greedy: free workers join touched offices while that pays
            for (int rep = 0; rep < 12; rep++) {
                double bg = 1e-12 * scale;
                int bw = -1, bo = -1;
                for (int w = 0; w < W; w++) {
                    if (Y.wof[w] != -1 || wm(w).none()) continue;
                    for (int q : touched) {
                        if ((wm(w) & ~Y.U[q]).none()) continue;
                        double v;
                        int c, t;
                        evalO(Y, q, Y.U[q] | wm(w), v, c, t);
                        if (v - Y.val[q] > bg) bg = v - Y.val[q], bw = w, bo = q;
                    }
                }
                if (bw < 0) break;
                Y.team[bo].push_back(bw), Y.wof[bw] = bo, Y.U[bo] |= wm(bw), refresh(Y, bo);
            }
            double nv = total(Y);
            if (nv >= cur || urand() < exp((nv - cur) / T)) cur = nv, X = std::move(Y);
        }
        if (cur > best + 1e-9 * (1 + fabs(best))) best = cur, B = X;
    }
    // build the assignment: sites and (native mode) the workers of each office
    vector<int> asg(AS, -1);
    for (int o = 0; o < K; o++) {
        if (!B.isOpen[o]) continue;
        int c = 0;
        Mask need;
        for (int s : B.cell[o]) {
            if (c >= maxSize[o]) break;
            if ((smask[s] & ~B.U[o]).any()) continue;
            asg[s] = o, c++, need |= smask[s];
        }
        if (nativeW)
            for (int w : B.team[o])
                if ((realW[w] & need).any()) asg[n + w] = o;
    }
    State st = fromAsg(asg);
    double lamSave = lambdaCnt, waSave = wAlpha, wcSave = wCost;
    lambdaCnt = 1e18, wAlpha = 1, wCost = 1;
    if (!countFeasible(st)) repairCounts(st);
    if (alpha > 0) {
        repairTasks(st);
        if (!countFeasible(st)) repairCounts(st);
    }
    lambdaCnt = lamSave, wAlpha = waSave, wCost = wcSave;
    if (!countFeasible(st) || !validateFull(st).empty()) {
        if (szDebug) fprintf(stderr, "wtSearch: invalid (%s)\n", validateFull(st).c_str());
        return none;
    }
    *outVal = trueObjective(st);
    if (szDebug) fprintf(stderr, "wtSearch: %lld iters, model %.4f, real %.4f\n", it, best, *outVal);
    return st.asg;
}

// ---------------------------------------------------------------- full validation (independent)
// ---------------------------------------------------------------- few-office enumeration
// With big zones (four offices can take half of the profitable sites) and a task-balance term,
// the optimum is a handful of large zones at one common task level, and the binding choices are
// WHICH offices open and WHICH skills each gets from the scarce single-skill workers: the
// annealer settles on a different (often poor) combination from run to run. Enumerate office
// subsets of size 1..M, every maximal split of the workers' skills over the subset and a few
// power-cell partitions; score each by the most profitable sites of each cell that its skills
// cover (up to capacity) with greedy task/count equalization; rebuild the best few exactly
// (levelBuild with the skill sets forced).
static inline bool fewSkillAvail(int k) { return nativeW ? !skW[k].empty() : availSkill[k] > 0; }
bool fewGate() {
    if (!singleSkillWorkers || alpha <= 0 || K < 2 || n == 0) return false;
    int nServ = 0;
    for (int s = 0; s < n; s++) {
        bool ok = true;
        for (int k = 0; k < NS && ok; k++)
            if (smask[s][k] && !fewSkillAvail(k)) ok = false;
        if (!ok) continue;
        for (int o = 0; o < K; o++)
            if (rew[s] - dist[o][s] > 0) { nServ++; break; }
    }
    vector<int> cs;
    for (int o = 0; o < K; o++) cs.push_back(min(maxSize[o], n));
    sort(cs.rbegin(), cs.rend());
    long long top = 0;
    for (int i = 0; i < 4 && i < (int)cs.size(); i++) top += cs[i];
    // or so few workers that no solution can open more than four offices (one worker each at least)
    if (nServ > 0 && (top >= 0.5 * nServ || min(W, K) <= 4)) return true;
    // or scarce workers (at most 8 useful ones): no solution opens more than 8 offices, so the
    // office-subset x team structure enumerated here is the whole problem
    int Wu = 0;
    for (int w = 0; w < W; w++) {
        const Mask& wm = nativeW ? realW[w] : wmask[w];
        bool use = false;
        for (int k = 0; k < NS && !use; k++)
            if (wm[k] && fewSkillAvail(k)) use = true;
        Wu += use;
    }
    if (Wu > 8) return false;
    // ... unless task-free sites (no workers needed) could fill offices beyond the staffed ones
    int nFree = 0;
    for (int s = 0; s < n; s++) {
        if (smask[s].any()) continue;
        for (int o = 0; o < K; o++)
            if (rew[s] - dist[o][s] > 0) { nFree++; break; }
    }
    if (nFree > 0.5 * top) return false;
    return nServ > 0 && Wu > 0;
}

struct FewCfg {
    double v;
    vector<int> sub;
    vector<double> w;
    int split;
};

vector<vector<int>> fewSearch(double endTime, vector<double>* vals, double curBest = -1e300) {
    vector<vector<int>> outs;
    bool dbg = szDebug;
    double t0 = elapsed();
    vector<char> needed(NS, 0);
    for (int s = 0; s < n; s++)
        for (int k = 0; k < NS; k++)
            if (smask[s][k]) needed[k] = 1;
    vector<int> sk;  // skills in play
    for (int k = 0; k < NS; k++)
        if (needed[k] && fewSkillAvail(k)) sk.push_back(k);
    int ns = sk.size();
    if (ns > 5 || ns == 0) return outs;
    vector<int> sm(n, 0);
    vector<char> serv(n, 1);
    for (int s = 0; s < n; s++) {
        for (int k = 0; k < NS; k++)
            if (smask[s][k] && !fewSkillAvail(k)) serv[s] = 0;
        for (int i = 0; i < ns; i++)
            if (smask[s][sk[i]]) sm[s] |= 1 << i;
    }
    // per office: servable profitable sites by profit (desc); single-office value for ranking
    vector<vector<int>> ord(K);
    vector<double> sv(K, -1e300);
    for (int o = 0; o < K; o++) {
        for (int s = 0; s < n; s++)
            if (serv[s] && rew[s] - dist[o][s] > 0) ord[o].push_back(s);
        sortSitesByKey(ord[o].begin(), ord[o].end(), true, [&](int a) { return rew[a] - dist[o][a]; });
        double v = -ocost[o];
        for (int i = 0; i < (int)ord[o].size() && i < maxSize[o]; i++) v += rew[ord[o][i]] - dist[o][ord[o][i]];
        sv[o] = v;
        if (elapsed() > endTime) return outs;
    }
    vector<int> offs;
    for (int o = 0; o < K; o++) {
        if (sv[o] <= 0 || maxSize[o] <= 0) continue;
        bool dup = false;
        for (int q : offs)
            if (px[n + o] == px[n + q] && py[n + o] == py[n + q]) dup = true;
        if (!dup) offs.push_back(o);
    }
    sort(offs.begin(), offs.end(), [&](int a, int b) { return sv[a] > sv[b]; });
    if (offs.empty()) return outs;
    // worker types over the skills in play (single-skill: one type per skill; native mode: the
    // distinct real skill sets, so one multi-skill worker can serve several skills of its office)
    vector<int> tMask;
    vector<vector<int>> tWs;
    for (int w = 0; w < W; w++) {
        const Mask& wm = nativeW ? realW[w] : wmask[w];
        int mk = 0;
        for (int i = 0; i < ns; i++)
            if (wm[sk[i]]) mk |= 1 << i;
        if (!mk) continue;
        int j = find(tMask.begin(), tMask.end(), mk) - tMask.begin();
        if (j == (int)tMask.size()) tMask.push_back(mk), tWs.push_back({});
        tWs[j].push_back(w);
    }
    int q = tMask.size(), Wp = 0;
    for (auto& t : tWs) Wp += t.size();
    if (q == 0) return outs;
    // many worker types: the team splits explode (and multi-skill teams are left to the other searches)
    if (nativeW && (q > 8 || Wp > 16)) return outs;
    // maximal team splits for m offices: per worker type, the subset of offices that get one worker
    // of it; per office the union skill mask (nonempty); maximal = no idle worker adds a skill anywhere
    struct Split {
        vector<int> mk, sub;
    };
    auto genSplits = [&](int m, vector<Split>& res) {
        res.clear();
        unordered_set<unsigned long long> seen;
        vector<int> sub(q, 0), mk(m);
        long long leaves = 0, nodes = 0;
        bool late = false;
        function<void(int)> rec = [&](int j) {
            if (late || res.size() >= 4000 || leaves > 300000) return;
            if ((++nodes & 1023) == 0 && elapsed() > endTime) { late = true; return; }
            if (j == q) {
                leaves++;
                fill(mk.begin(), mk.end(), 0);
                for (int t = 0; t < q; t++)
                    for (int i = 0; i < m; i++)
                        if (sub[t] >> i & 1) mk[i] |= tMask[t];
                for (int i = 0; i < m; i++)
                    if (!mk[i]) return;
                for (int t = 0; t < q; t++)
                    if (__builtin_popcount(sub[t]) < (int)tWs[t].size())
                        for (int i = 0; i < m; i++)
                            if (!(sub[t] >> i & 1) && (tMask[t] & ~mk[i])) return;
                unsigned long long key = 0;
                for (int i = 0; i < m; i++) key = key * 32 + mk[i];
                if (!seen.insert(key).second) return;
                res.push_back({mk, sub});
                return;
            }
            int c = tWs[j].size();
            for (int b = (1 << m) - 1; b >= 0 && res.size() < 4000; b--) {  // fuller teams first
                if (__builtin_popcount(b) > c) continue;
                sub[j] = b;
                rec(j + 1);
            }
            sub[j] = 0;
        };
        rec(0);
    };
    int Mmax = offs.size() <= 12 || Wp <= 4 ? 4 : 3;
    Mmax = min(min(Mmax, 8), max(1, Wp));
    // growth beyond the enumerated sizes (more, narrower teams): up to one office per worker
    int MG = min(8, Wp);
    MG = max(Mmax, min(MG, min(8, (int)offs.size())));
    vector<vector<Split>> splits(MG + 1);
    vector<char> splitsDone(MG + 1, 0);
    auto getSplits = [&](int m) -> const vector<Split>& {
        if (!splitsDone[m]) genSplits(m, splits[m]), splitsDone[m] = 1;
        return splits[m];
    };
    for (int m = 1; m <= Mmax; m++) getSplits(m);
    // scoring
    vector<int> owner(n);
    vector<vector<int>> lst(MG), taken(MG);
    vector<vector<char>> keep(MG);
    // per (office slot, skill mask) cache of the covered most-profitable sites of the cell
    vector<array<vector<int>, 32>> cTk(MG);
    vector<array<double, 32>> cV(MG);
    vector<array<int, 32>> cT(MG), cStamp(MG);
    for (auto& a : cStamp) a.fill(-1);
    int scoreId = 0;
    auto score = [&](const vector<int>& sub, const vector<double>& w, int* bestSplit) -> double {
        int m = sub.size();
        scoreId++;
        const vector<Split>& SP = getSplits(m);
        for (int s = 0; s < n; s++) {
            int bo = 0;
            double bv = 1e300;
            for (int i = 0; i < m; i++) {
                double dx = px[s] - px[n + sub[i]], dy = py[s] - py[n + sub[i]];
                double v = dx * dx + dy * dy - w[i];
                if (v < bv) bv = v, bo = i;
            }
            owner[s] = bo;
        }
        for (int i = 0; i < m; i++) {
            lst[i].clear();
            for (int s : ord[sub[i]])
                if (owner[s] == i) lst[i].push_back(s);
        }
        double best = -1e300;
        int bs = -1;
        double costSum = 0;
        for (int i = 0; i < m; i++) costSum += ocost[sub[i]];
        int sidx = 0;
        for (const auto& sp : SP) {
            double V[8];
            int T[8], C[8];
            const vector<int>* tk[8];
            bool bad = false;
            double ub = -costSum;
            for (int i = 0; i < m && !bad; i++) {
                int o = sub[i], mk = sp.mk[i];
                if (cStamp[i][mk] != scoreId) {
                    vector<int>& t = cTk[i][mk];
                    t.clear();
                    double v = 0;
                    int tt = 0;
                    for (int s : lst[i]) {
                        if (sm[s] & ~mk) continue;
                        t.push_back(s);
                        v += rew[s] - dist[o][s];
                        tt += ntask[s];
                        if ((int)t.size() >= maxSize[o]) break;
                    }
                    cV[i][mk] = v, cT[i][mk] = tt, cStamp[i][mk] = scoreId;
                }
                tk[i] = &cTk[i][mk];
                V[i] = cV[i][mk], T[i] = cT[i][mk], C[i] = tk[i]->size();
                ub += V[i];
                if (C[i] == 0) bad = true;
            }
            // trimming only removes profitable sites and the task gap is a penalty: skip hopeless splits
            if (bad || ub <= best) { sidx++; continue; }
            for (int i = 0; i < m; i++) keep[i].assign(C[i], 1);
            // untrimmed value (task gap paid) if the count window holds
            {
                int cmn = INT32_MAX, cmx = 0, tmn = INT32_MAX, tmx = 0;
                double v = -costSum;
                for (int i = 0; i < m; i++) v += V[i], cmn = min(cmn, C[i]), cmx = max(cmx, C[i]), tmn = min(tmn, T[i]), tmx = max(tmx, T[i]);
                if (cmx - cmn <= A) {
                    v -= alpha * (tmx - tmn);
                    if (v > best) best = v, bs = sidx;
                }
            }
            // greedy equalization: tasks down to the lowest office, counts into the window
            for (int round = 0; round < 3; round++) {
                int tmn = INT32_MAX;
                for (int i = 0; i < m; i++) tmn = min(tmn, T[i]);
                for (int i = 0; i < m; i++) {
                    int o = sub[i];
                    for (int j = C[i] > 0 ? (int)tk[i]->size() - 1 : -1; j >= 0 && T[i] > tmn; j--) {
                        int s = (*tk[i])[j];
                        if (!keep[i][j] || T[i] - ntask[s] < tmn) continue;
                        keep[i][j] = 0, T[i] -= ntask[s], V[i] -= rew[s] - dist[o][s], C[i]--;
                    }
                }
                int cmn = INT32_MAX;
                for (int i = 0; i < m; i++) cmn = min(cmn, C[i]);
                bool moved = false;
                for (int i = 0; i < m; i++) {
                    int o = sub[i];
                    for (int j = (int)tk[i]->size() - 1; j >= 0 && C[i] > cmn + A; j--) {
                        if (!keep[i][j]) continue;
                        int s = (*tk[i])[j];
                        keep[i][j] = 0, T[i] -= ntask[s], V[i] -= rew[s] - dist[o][s], C[i]--, moved = true;
                    }
                }
                if (!moved) break;
            }
            {
                int cmn = INT32_MAX, cmx = 0, tmn = INT32_MAX, tmx = 0;
                double v = -costSum;
                for (int i = 0; i < m; i++) v += V[i], cmn = min(cmn, C[i]), cmx = max(cmx, C[i]), tmn = min(tmn, T[i]), tmx = max(tmx, T[i]);
                if (cmx - cmn <= A && cmn > 0) {
                    v -= alpha * (tmx - tmn);
                    if (v > best) best = v, bs = sidx;
                }
            }
            sidx++;
        }
        *bestSplit = bs;
        return best;
    };
    // own-cell check: each office must stay inside its own power cell
    auto ownCells = [&](const vector<int>& sub, const vector<double>& w) {
        int m = sub.size();
        for (int i = 0; i < m; i++) {
            double own = -w[i];
            for (int j = 0; j < m; j++) {
                if (j == i) continue;
                double dx = px[n + sub[i]] - px[n + sub[j]], dy = py[n + sub[i]] - py[n + sub[j]];
                if (dx * dx + dy * dy - w[j] <= own) return false;
            }
        }
        return true;
    };
    // enumeration: all subsets of size m among the top offices (fewer for larger m)
    bool grow = true;
    double enumEnd = t0 + (grow ? 0.35 : 0.6) * (endTime - t0);
    vector<FewCfg> top;  // best configs (distinct subsets)
    const size_t TOPN = 12;
    auto sameSet = [](vector<int> a, vector<int> b) {
        sort(a.begin(), a.end()), sort(b.begin(), b.end());
        return a == b;
    };
    auto offer = [&](double v, const vector<int>& sub, const vector<double>& w, int split) {
        if (split < 0 || v <= -1e299) return;
        if (top.size() >= TOPN && v <= top.back().v) return;
        for (auto& c : top)
            if (c.sub.size() == sub.size() && sameSet(c.sub, sub)) {
                if (v > c.v) c = {v, sub, w, split};
                sort(top.begin(), top.end(), [](const FewCfg& a, const FewCfg& b) { return a.v > b.v; });
                return;
            }
        top.push_back({v, sub, w, split});
        sort(top.begin(), top.end(), [](const FewCfg& a, const FewCfg& b) { return a.v > b.v; });
        if (top.size() > TOPN) top.pop_back();
    };
    long long evals = 0;
    bool stop = false;
    int sizeT[] = {0, (int)offs.size(), 60, 24, 12};
    for (int m = 1; m <= Mmax && !stop; m++) {
        if (splits[m].empty()) continue;
        int T = min((int)offs.size(), sizeT[min(m, 4)]);
        if (T < m) break;
        vector<int> idx(m);
        for (int i = 0; i < m; i++) idx[i] = i;
        while (true) {
            vector<int> sub(m);
            for (int i = 0; i < m; i++) sub[i] = offs[idx[i]];
            vector<double> w(m, 0.0);
            int sp;
            double v = score(sub, w, &sp);
            evals++;
            offer(v, sub, w, sp);
            if ((evals & 7) == 0 && elapsed() > enumEnd) { stop = true; break; }
            int i = m - 1;
            while (i >= 0 && idx[i] == T - m + i) i--;
            if (i < 0) break;
            idx[i]++;
            for (int j = i + 1; j < m; j++) idx[j] = idx[j - 1] + 1;
        }
    }
    if (top.empty()) return outs;
    // hopeless (the estimate is far below the current best): skip growth, refinement and rebuilds
    if (curBest > 0 && top[0].v < 0.8 * curBest) {
        if (dbg) fprintf(stderr, "few: best est %.4f < 0.8 * current %.4f, giving up\n", top[0].v, curBest);
        return outs;
    }
    // office swaps (any office, not only the best-ranked ones: spread-out teams use edge offices)
    // and growth (one more office = narrower teams), equal weights
    if (grow) {
        double growEnd = t0 + 0.55 * (endTime - t0), lsEnd = t0 + 0.65 * (endTime - t0);
        auto swapLS = [&](FewCfg& c, int maxSweeps, double until) {
            int m = c.sub.size();
            bool imp = true;
            for (int sw = 0; imp && sw < maxSweeps && elapsed() < until; sw++) {
                imp = false;
                for (int i = 0; i < m && elapsed() < until; i++)
                    for (int o : offs) {
                        if (elapsed() > until) break;
                        if (find(c.sub.begin(), c.sub.end(), o) != c.sub.end()) continue;
                        vector<int> s2 = c.sub;
                        s2[i] = o;
                        vector<double> w(m, 0.0);
                        int sp;
                        double v = score(s2, w, &sp);
                        evals++;
                        if (sp >= 0 && v > c.v + 1e-9) c = {v, s2, w, sp}, imp = true;
                    }
            }
        };
        if (dbg) fprintf(stderr, "few: enum done t=%.2fs\n", elapsed() - t0);
        // growth from the best config of each size (one more office = narrower teams)
        for (int m = 1; m < MG && elapsed() < growEnd; m++) {
            const FewCfg* base = nullptr;
            for (auto& c : top)
                if ((int)c.sub.size() == m && (!base || c.v > base->v)) base = &c;
            if (!base) continue;
            if ((int)offs.size() <= m) break;
            if (getSplits(m + 1).empty()) break;
            FewCfg bestAdd{-1e300, {}, {}, -1};
            vector<int> bsub = base->sub;
            for (int o : offs) {
                if (find(bsub.begin(), bsub.end(), o) != bsub.end()) continue;
                vector<int> s2 = bsub;
                s2.push_back(o);
                vector<double> w(m + 1, 0.0);
                int sp;
                double v = score(s2, w, &sp);
                evals++;
                if (sp >= 0 && v > bestAdd.v) bestAdd = {v, s2, w, sp};
                if (elapsed() > growEnd) break;
            }
            if (dbg) fprintf(stderr, "few: grow m=%d base %.4f add %.4f splits %zu t=%.2fs\n", m + 1, base->v, bestAdd.v, splits[m + 1].size(), elapsed() - t0);
            if (bestAdd.split < 0) continue;
            swapLS(bestAdd, 1, growEnd);
            offer(bestAdd.v, bestAdd.sub, bestAdd.w, bestAdd.split);
        }
        // office swaps on the two best configs (any office, not only the best-ranked ones)
        vector<FewCfg> work(top.begin(), top.begin() + min(top.size(), (size_t)2));
        for (auto& c : work) {
            if (elapsed() > lsEnd) break;
            swapLS(c, 8, lsEnd);
            offer(c.v, c.sub, c.w, c.split);
        }
    }
    // power-weight refinement of the best configs (coordinate search, offices kept in own cells)
    double span2 = 0;
    for (int i = 0; i < n; i++) span2 = max(span2, (px[i] - px[0]) * (px[i] - px[0]) + (py[i] - py[0]) * (py[i] - py[0]));
    double refEnd = t0 + 0.8 * (endTime - t0);
    for (auto& c : top) {
        int m = c.sub.size();
        if (m < 2) continue;
        double step = 0.02 * span2;
        for (int sweep = 0; sweep < 6 && elapsed() < refEnd; sweep++, step *= 0.5) {
            bool imp = true;
            while (imp && elapsed() < refEnd) {
                imp = false;
                for (int i = 0; i < m; i++)
                    for (int dir = -1; dir <= 1; dir += 2) {
                        vector<double> w = c.w;
                        w[i] += dir * step;
                        if (!ownCells(c.sub, w)) continue;
                        int sp;
                        double v = score(c.sub, w, &sp);
                        evals++;
                        if (v > c.v + 1e-9) c.v = v, c.w = w, c.split = sp, imp = true;
                    }
            }
        }
    }
    sort(top.begin(), top.end(), [](const FewCfg& a, const FewCfg& b) { return a.v > b.v; });
    if (dbg) fprintf(stderr, "few: offices %zu types %d Mmax %d MG %d evals %lld best est %.4f (m=%zu) %.2fs\n", offs.size(), q, Mmax, MG, evals, top[0].v, top[0].sub.size(),
                     elapsed() - t0);
    // exact rebuild of the best few: forced skill sets (and teams), common task level by levelBuild's DP
    for (size_t r = 0; r < top.size() && r < 6; r++) {
        if (elapsed() > endTime) break;
        const FewCfg& c = top[r];
        int m = c.sub.size();
        const Split& sp = splits[m][c.split];
        vector<double> wK(K, 0.0);
        vector<Mask> forced(K);
        vector<int> team(W, -1);
        for (int i = 0; i < m; i++) {
            wK[c.sub[i]] = c.w[i];
            for (int b = 0; b < ns; b++)
                if (sp.mk[i] >> b & 1) forced[c.sub[i]][sk[b]] = 1;
        }
        for (int t = 0; t < q; t++) {
            int u = 0;
            for (int i = 0; i < m; i++)
                if (sp.sub[t] >> i & 1) team[tWs[t][u++]] = c.sub[i];
        }
        double v;
        vector<int> a = levelBuild(c.sub, wK, endTime, &v, &forced, nullptr, nativeW ? &team : nullptr);
        if (dbg) fprintf(stderr, "few: cfg %zu m=%d est %.4f exact %.4f\n", r, m, c.v, v);
        if (v > -1e299) outs.push_back(a), vals->push_back(v);
    }
    return outs;
}


// ---------------------------------------------------------------- team local search
// fewSearch enumerates every maximal skill split and so stops at 5 skills in play (and at a few
// worker types). With more skills (one or two workers per skill) the binding choice is the same:
// which few offices open and how the scarce workers are grouped into teams, but the space is too
// large to enumerate. Local search over (office subset, allocation of worker types to offices):
// cells = power diagram of the subset (equal weights while searching, refined for the best few),
// each office takes the most profitable sites of its cell that its team covers, all offices at a
// joint task level (exact for 0..2 tasks per site, a tasks-only DP otherwise), count window A.
// The best configurations are rebuilt exactly by levelBuild with the skill sets (and teams) forced.
bool teamGate() {
    if (!singleSkillWorkers || alpha <= 0 || K < 2 || n == 0) return false;
    int inPlay = 0;
    for (int k = 0; k < NS; k++) inPlay += fewSkillAvail(k);
    if (inPlay == 0 || inPlay > 64) return false;
    int Wu = 0;
    for (int w = 0; w < W; w++) {
        const Mask& wm = nativeW ? realW[w] : wmask[w];
        bool use = false;
        for (int k = 0; k < NS && !use; k++)
            if (wm[k] && fewSkillAvail(k)) use = true;
        Wu += use;
    }
    if (Wu < 2 || Wu > 16) return false;
    // task-free sites need no workers: with many of them the offices are not worker-bound
    int nFree = 0, nTask = 0;
    for (int s = 0; s < n; s++) (smask[s].any() ? nTask : nFree)++;
    return nTask > 0 && nFree <= nTask / 2;
}

vector<vector<int>> teamSearch(double endTime, vector<double>* vals, double curBest) {
    vector<vector<int>> outs;
    bool dbg = szDebug;
    double t0 = elapsed();
    vector<int> sk;  // skills in play -> bit
    vector<int> bitOf(NS, -1);
    for (int k = 0; k < NS; k++)
        if (fewSkillAvail(k)) bitOf[k] = sk.size(), sk.push_back(k);
    int nb = sk.size();
    if (nb == 0 || nb > 64) return outs;
    vector<uint64_t> sm(n, 0);
    vector<char> serv(n, 1);
    int Cmax = 0;
    for (int s = 0; s < n; s++) {
        for (int k = 0; k < NS; k++)
            if (smask[s][k]) {
                if (bitOf[k] < 0) serv[s] = 0;
                else sm[s] |= 1ULL << bitOf[k];
            }
        if (serv[s]) Cmax = max(Cmax, ntask[s]);
    }
    // worker types (real skill sets in native mode)
    vector<uint64_t> tMask;
    vector<vector<int>> tWs;
    for (int w = 0; w < W; w++) {
        const Mask& wm = nativeW ? realW[w] : wmask[w];
        uint64_t mk = 0;
        for (int i = 0; i < nb; i++)
            if (wm[sk[i]]) mk |= 1ULL << i;
        if (!mk) continue;
        int j = find(tMask.begin(), tMask.end(), mk) - tMask.begin();
        if (j == (int)tMask.size()) tMask.push_back(mk), tWs.push_back({});
        tWs[j].push_back(w);
    }
    int U = tMask.size(), Wu = 0;
    for (auto& t : tWs) Wu += t.size();
    if (U == 0) return outs;
    // candidate offices: best single-office values (distinct positions), top 16
    vector<double> sv(K, -1e300);
    for (int o = 0; o < K; o++) {
        if (maxSize[o] <= 0) continue;
        vector<double> pr;
        for (int s = 0; s < n; s++)
            if (serv[s] && rew[s] - dist[o][s] > 0) pr.push_back(rew[s] - dist[o][s]);
        int c = min((int)pr.size(), maxSize[o]);
        if (c == 0) continue;
        nth_element(pr.begin(), pr.begin() + (c - 1), pr.end(), greater<double>());
        double v = -ocost[o];
        for (int i = 0; i < c; i++) v += pr[i];
        sv[o] = v;
        if (elapsed() > endTime) return outs;
    }
    vector<int> offs;
    {
        vector<int> all;
        for (int o = 0; o < K; o++)
            if (sv[o] > -1e299) all.push_back(o);
        sort(all.begin(), all.end(), [&](int a, int b) { return sv[a] > sv[b]; });
        for (int o : all) {
            bool dup = false;
            for (int q : offs)
                if (px[n + o] == px[n + q] && py[n + o] == py[n + q]) dup = true;
            if (!dup) offs.push_back(o);
            if (offs.size() >= 16) break;
        }
    }
    if (offs.size() < 1) return outs;
    vector<vector<int>> ord(K);
    for (int o : offs) {
        for (int s = 0; s < n; s++)
            if (serv[s] && rew[s] - dist[o][s] > 0) ord[o].push_back(s);
        sortSitesByKey(ord[o].begin(), ord[o].end(), true, [&](int a) { return rew[a] - dist[o][a]; });
    }
    int Mmax = min(min(8, Wu), (int)offs.size());
    double span2 = 0;
    for (int i = 0; i < n; i++) span2 = max(span2, (px[i] - px[0]) * (px[i] - px[0]) + (py[i] - py[0]) * (py[i] - py[0]));
    struct Cfg {
        vector<int> sub;
        vector<vector<int>> al;  // al[i][t]: workers of type t at office i
        vector<double> w;
        double v;
    };
    auto maskOf = [&](const Cfg& c, int i) {
        uint64_t m = 0;
        for (int t = 0; t < U; t++)
            if (c.al[i][t] > 0) m |= tMask[t];
        return m;
    };
    auto valid = [&](const Cfg& c) {
        for (size_t i = 0; i < c.sub.size(); i++)
            if (!maskOf(c, i)) return false;
        for (int t = 0; t < U; t++) {
            int tot = 0;
            for (size_t i = 0; i < c.sub.size(); i++) tot += c.al[i][t];
            if (tot > (int)tWs[t].size()) return false;
        }
        return true;
    };
    // scoring buffers
    vector<int> owner(n);
    vector<vector<double>> F(8);  // per office: best value at exactly T tasks
    vector<vector<int>> Cn(8);    // count at that choice
    vector<double> G0, G1, G2;
    vector<int> L1, L2;
    vector<float> dpT;
    // joint-level windows: a spread of D tasks costs alpha * D; wider spreads never pay against
    // the per-site profits once alpha * D exceeds a few sites' worth
    vector<int> Ds;
    {
        double pmax = 0;
        for (int o : offs)
            if (!ord[o].empty()) pmax = max(pmax, rew[ord[o][0]] - dist[o][ord[o][0]]);
        static const int cand[] = {0, 1, 2, 3, 5, 8, 13, 21, 34, 55};
        for (int D : cand)
            if (D == 0 || alpha * D <= 40 * pmax) Ds.push_back(D);
    }
    auto officeTable = [&](int o, uint64_t mk, int i) {
        vector<double>& f = F[i];
        vector<int>& cn = Cn[i];
        int cp = maxSize[o];
        G0.assign(1, 0.0), G1.assign(1, 0.0), G2.assign(1, 0.0);
        L1.clear(), L2.clear();
        bool gen = Cmax > 2;
        for (int s : ord[o]) {
            if (owner[s] != i || (sm[s] & ~mk)) continue;
            double p = rew[s] - dist[o][s];
            if (ntask[s] == 0) G0.push_back(G0.back() + p);
            else if (gen) L1.push_back(s);
            else if (ntask[s] == 1) G1.push_back(G1.back() + p);
            else G2.push_back(G2.back() + p);
        }
        int n0 = G0.size() - 1;
        if (!gen) {
            int n1 = G1.size() - 1, n2 = G2.size() - 1;
            int Tm = min(n1 + 2 * n2, 2 * cp);
            f.assign(Tm + 1, -1e300), cn.assign(Tm + 1, 0);
            for (int T = 0; T <= Tm; T++) {
                int lo = max(0, T - cp), hi = min(n2, T / 2);
                if (T - n1 > 0) lo = max(lo, (T - n1 + 1) / 2);
                if (lo > hi) continue;
                auto fv = [&](int b) { return G1[T - 2 * b] + G2[b]; };  // concave in b
                int l = lo, h = hi;
                while (h - l > 2) {
                    int m1 = l + (h - l) / 3, m2 = h - (h - l) / 3;
                    if (fv(m1) < fv(m2)) l = m1 + 1;
                    else h = m2;
                }
                int bb = l;
                for (int b = l + 1; b <= h; b++)
                    if (fv(b) > fv(bb)) bb = b;
                int c = T - bb, z = min(n0, cp - c);
                f[T] = fv(bb) + G0[z], cn[T] = c + z;
            }
        } else {  // general task counts: tasks-only DP over the best cap + 60 sites
            // bounded work (huge zones x many tasks per site): at most 400 sites and lim * Tm <= 2e7
            int lim = min((int)L1.size(), min(cp + 60, 400));
            int Tm = 0;
            for (int j = 0; j < lim; j++) Tm += ntask[L1[j]];
            while (lim > 1 && (long long)lim * Tm > 20000000LL) Tm -= ntask[L1[--lim]];
            dpT.assign(Tm + 1, -1e30f);
            vector<int> dc(Tm + 1, 0);
            dpT[0] = 0;
            for (int j = 0; j < lim; j++) {
                int s = L1[j], t = ntask[s];
                float p = rew[s] - dist[o][s];
                for (int x = Tm; x >= t; x--)
                    if (dpT[x - t] + p > dpT[x]) dpT[x] = dpT[x - t] + p, dc[x] = dc[x - t] + 1;
            }
            f.assign(Tm + 1, -1e300), cn.assign(Tm + 1, 0);
            for (int T = 0; T <= Tm; T++)
                if (dpT[T] > -1e29f && dc[T] <= cp) {
                    int z = min(n0, cp - dc[T]);
                    f[T] = dpT[T] + G0[z], cn[T] = dc[T] + z;
                }
        }
    };
    long long evals = 0;
    auto score = [&](const Cfg& c) -> double {
        if (elapsed() > endTime) return -1e300;  // slow scores (huge inputs): never past the slice
        int m = c.sub.size();
        evals++;
        for (int s = 0; s < n; s++) {
            int bo = 0;
            double bv = 1e300;
            for (int i = 0; i < m; i++) {
                double dx = px[s] - px[n + c.sub[i]], dy = py[s] - py[n + c.sub[i]];
                double v = dx * dx + dy * dy - c.w[i];
                if (v < bv) bv = v, bo = i;
            }
            owner[s] = bo;
        }
        int Tm = INT32_MAX;
        double cost = 0;
        for (int i = 0; i < m; i++) {
            officeTable(c.sub[i], maskOf(c, i), i);
            Tm = min(Tm, (int)F[i].size() - 1);
            cost += ocost[c.sub[i]];
        }
        double best = -1e300;
        for (int D : Ds) {
            for (int t = 0; t <= Tm; t++) {
                double v = -cost - alpha * D;
                int cmn = INT32_MAX, cmx = 0;
                bool ok = true;
                for (int i = 0; i < m && ok; i++) {
                    const vector<double>& f = F[i];
                    int bt = -1;
                    double bv = -1e300;
                    for (int T = t; T <= t + D && T < (int)f.size(); T++)
                        if (f[T] > bv) bv = f[T], bt = T;
                    if (bt < 0 || bv < -1e299) ok = false;
                    else v += bv, cmn = min(cmn, Cn[i][bt]), cmx = max(cmx, Cn[i][bt]);
                }
                if (ok && cmx - cmn <= A && v > best) best = v;
            }
        }
        return best;
    };
    auto ownCells = [&](const Cfg& c) {
        int m = c.sub.size();
        for (int i = 0; i < m; i++)
            for (int j = 0; j < m; j++) {
                if (i == j) continue;
                double dx = px[n + c.sub[i]] - px[n + c.sub[j]], dy = py[n + c.sub[i]] - py[n + c.sub[j]];
                if (dx * dx + dy * dy - c.w[j] <= -c.w[i]) return false;
            }
        return true;
    };
    auto randomCfg = [&]() {
        Cfg c;
        int m = 1 + irand(Mmax);
        vector<int> pool = offs;
        for (int i = 0; i < m; i++) swap(pool[i], pool[i + irand(pool.size() - i)]);
        c.sub.assign(pool.begin(), pool.begin() + m);
        c.al.assign(m, vector<int>(U, 0));
        for (int t = 0; t < U; t++)
            for (size_t k = 0; k < tWs[t].size(); k++)
                if (irand(8)) c.al[irand(m)][t]++;
        for (int i = 0; i < m; i++)
            if (!maskOf(c, i)) c.al[i][irand(U)]++;
        for (int t = 0; t < U; t++) {
            int tot = 0;
            for (int i = 0; i < m; i++) tot += c.al[i][t];
            while (tot > (int)tWs[t].size()) {
                int i = irand(m);
                if (c.al[i][t] > 0) c.al[i][t]--, tot--;
            }
        }
        c.w.assign(m, 0.0);
        c.v = -1e300;
        return c;
    };
    double lsEnd = t0 + 0.6 * (endTime - t0);
    vector<Cfg> elite;
    int restarts = 0;
    Cfg best;
    best.v = -1e300;
    vector<Cfg> nbh;
    while (elapsed() < lsEnd) {
        // nothing feasible after many restarts (e.g. a count window no config meets): give up
        if (restarts >= 40 && best.v <= -1e299) break;
        Cfg c = randomCfg();
        if (!valid(c)) continue;
        c.v = score(c);
        restarts++;
        bool imp = true;
        while (imp && elapsed() < lsEnd) {
            imp = false;
            int m = c.sub.size();
            nbh.clear();
            for (int t = 0; t < U; t++) {  // move one worker of type t: office/pool -> office/pool
                int used = 0;
                for (int i = 0; i < m; i++) used += c.al[i][t];
                for (int i = 0; i <= m; i++) {
                    if (i < m && c.al[i][t] == 0) continue;
                    if (i == m && used >= (int)tWs[t].size()) continue;
                    for (int j = 0; j <= m; j++) {
                        if (j == i) continue;
                        Cfg e = c;
                        if (i < m) e.al[i][t]--;
                        if (j < m) e.al[j][t]++;
                        if (valid(e)) nbh.push_back(e);
                    }
                }
            }
            for (int i = 0; i < m; i++)  // another office in slot i
                for (int o : offs) {
                    if (find(c.sub.begin(), c.sub.end(), o) != c.sub.end()) continue;
                    Cfg e = c;
                    e.sub[i] = o;
                    nbh.push_back(e);
                }
            if (m < Mmax)  // one more office, staffed by one worker from another office or the pool
                for (int o : offs) {
                    if (find(c.sub.begin(), c.sub.end(), o) != c.sub.end()) continue;
                    for (int t = 0; t < U; t++)
                        for (int i = 0; i <= m; i++) {
                            Cfg e = c;
                            e.sub.push_back(o), e.al.push_back(vector<int>(U, 0));
                            if (i < m) {
                                if (e.al[i][t] == 0) continue;
                                e.al[i][t]--;
                            }
                            e.al[m][t]++;
                            if (valid(e)) nbh.push_back(e);
                        }
                }
            if (m > 1)  // close an office (its workers go to the pool)
                for (int i = 0; i < m; i++) {
                    Cfg e = c;
                    e.sub.erase(e.sub.begin() + i), e.al.erase(e.al.begin() + i);
                    nbh.push_back(e);
                }
            for (size_t k = 0; k + 1 < nbh.size(); k++) swap(nbh[k], nbh[k + irand(nbh.size() - k)]);
            for (auto& e : nbh) {
                e.w.assign(e.sub.size(), 0.0);
                e.v = score(e);
                if (e.v > c.v + 1e-9) {
                    c = e, imp = true;
                    break;
                }
                if (elapsed() > lsEnd) break;
            }
        }
        if (c.v <= -1e299) continue;
        bool dup = false;
        for (auto& e : elite) {
            if (e.sub.size() != c.sub.size()) continue;
            vector<pair<int, uint64_t>> a, b;  // same offices with the same skill sets
            for (size_t i = 0; i < c.sub.size(); i++) a.push_back({c.sub[i], maskOf(c, i)}), b.push_back({e.sub[i], maskOf(e, i)});
            sort(a.begin(), a.end()), sort(b.begin(), b.end());
            if (a == b) dup = true;
        }
        if (!dup) {
            elite.push_back(c);
            sort(elite.begin(), elite.end(), [](const Cfg& a, const Cfg& b) { return a.v > b.v; });
            if (elite.size() > 8) elite.pop_back();
        }
        if (c.v > best.v) best = c;
    }
    if (elite.empty()) return outs;
    if (dbg) fprintf(stderr, "team: skills %d types %d useful %d offs %zu restarts %d evals %lld best est %.4f (m=%zu) %.2fs\n", nb, U, Wu, offs.size(), restarts, evals,
                     elite[0].v, elite[0].sub.size(), elapsed() - t0);
    if (curBest > 0 && elite[0].v < 0.8 * curBest) return outs;
    // power-weight refinement (coordinate search, offices kept inside their own cells)
    double refEnd = t0 + 0.8 * (endTime - t0);
    for (size_t r = 0; r < elite.size() && elapsed() < refEnd; r++) {
        Cfg& c = elite[r];
        int m = c.sub.size();
        if (m < 2) continue;
        double until = min(refEnd, elapsed() + (refEnd - elapsed()) / (elite.size() - r));
        double step = 0.02 * span2;
        for (int sweep = 0; sweep < 7 && elapsed() < until; sweep++, step *= 0.5) {
            bool imp = true;
            while (imp && elapsed() < until) {
                imp = false;
                for (int i = 0; i < m && elapsed() < until; i++)
                    for (int dir = -1; dir <= 1; dir += 2) {
                        if (elapsed() > until) break;
                        Cfg d = c;
                        d.w[i] += dir * step;
                        if (!ownCells(d)) continue;
                        double v = score(d);
                        if (v > c.v + 1e-9) d.v = v, c = d, imp = true;
                    }
            }
        }
    }
    sort(elite.begin(), elite.end(), [](const Cfg& a, const Cfg& b) { return a.v > b.v; });
    // exact rebuild: skill sets (and native teams) forced, common level by levelBuild's DP
    for (size_t r = 0; r < elite.size() && r < 6; r++) {
        if (elapsed() > endTime) break;
        const Cfg& c = elite[r];
        int m = c.sub.size();
        vector<double> wK(K, 0.0);
        vector<Mask> forced(K);
        vector<int> team(W, -1);
        vector<int> usedT(U, 0);
        for (int i = 0; i < m; i++) {
            wK[c.sub[i]] = c.w[i];
            uint64_t mk = maskOf(c, i);
            for (int b = 0; b < nb; b++)
                if (mk >> b & 1) forced[c.sub[i]][sk[b]] = 1;
            for (int t = 0; t < U; t++)
                for (int k = 0; k < c.al[i][t]; k++) team[tWs[t][usedT[t]++]] = c.sub[i];
        }
        double v;
        vector<int> a = levelBuild(c.sub, wK, endTime, &v, &forced, nullptr, nativeW ? &team : nullptr);
        if (dbg) fprintf(stderr, "team: cfg %zu m=%d est %.4f exact %.4f\n", r, m, c.v, v);
        if (v > -1e299) outs.push_back(a), vals->push_back(v);
    }
    return outs;
}

string validateFull(const State& st) {
    vector<int> tmp;
    vector<vector<int>> covs;
    vector<int> open;
    for (int o = 0; o < K; o++)
        if (st.cnt[o] > 0) open.push_back(o);
    vector<Mask> masks;
    for (int o : open) {
        if (st.cnt[o] > maxSize[o]) return "capacity";
        Mask m;
        for (int s : st.mem[o]) m |= smask[s];
        if (m.any()) masks.push_back(m);
    }
    for (int a : open)
        for (int b : open)
            if (abs(st.cnt[a] - st.cnt[b]) > A) return "count balance";
    if (nativeW) {
        vector<int> seen(W, 0);
        for (int o = 0; o < K; o++) {
            Mask c;
            for (int w : st.owk[o]) {
                if (seen[w]++ || st.cnt[o] == 0) return "skills";
                c |= realW[w];
            }
            if (st.cnt[o] > 0 && (st.omask[o] & ~c).any()) return "skills";
        }
    } else if (!assignWorkers(masks, false)) return "skills";
    vector<int> cover(NP, 0);
    for (int o : open) {
        Hull h;
        computeHullOf(o, st.mem[o], h, tmp);
        vector<int> cv;
        computeCov(h, cv);
        for (int p : cv)
            if (cover[p]++) return "hull conflict";
    }
    return "";
}

// validateFull for a state fresh from fromAsg: its hulls and coverage are exactly the ones
// validateFull rebuilds, so a hull conflict is a point covered twice
string validateBuilt(const State& st) {
    vector<int> tmp;
    vector<vector<int>> covs;
    vector<int> open;
    for (int o = 0; o < K; o++)
        if (st.cnt[o] > 0) open.push_back(o);
    vector<Mask> masks;
    for (int o : open) {
        if (st.cnt[o] > maxSize[o]) return "capacity";
        Mask m;
        for (int s : st.mem[o]) m |= smask[s];
        if (m.any()) masks.push_back(m);
    }
    for (int a : open)
        for (int b : open)
            if (abs(st.cnt[a] - st.cnt[b]) > A) return "count balance";
    if (nativeW) {
        vector<int> seen(W, 0);
        for (int o = 0; o < K; o++) {
            Mask c;
            for (int w : st.owk[o]) {
                if (seen[w]++ || st.cnt[o] == 0) return "skills";
                c |= realW[w];
            }
            if (st.cnt[o] > 0 && (st.omask[o] & ~c).any()) return "skills";
        }
    } else if (!assignWorkers(masks, false)) return "skills";
    if (st.multiCov > 0) return "hull conflict";
    return "";
}

void writeSolution(const State& st, const char* path) {
    vector<int> open;
    vector<Mask> masks;
    vector<int> openWithMask;
    for (int o = 0; o < K; o++)
        if (st.cnt[o] > 0) {
            open.push_back(o);
            Mask m;
            for (int s : st.mem[o]) m |= smask[s];
            if (m.any()) masks.push_back(m), openWithMask.push_back(o);
        }
    vector<vector<int>> wk(K);
    if (nativeW) {
        for (int o = 0; o < K; o++) wk[o] = st.owk[o];
    } else if (assignWorkers(masks, true)) {
        for (int w = 0; w < W; w++)
            if (assignWorkersResult[w] >= 0) wk[openWithMask[assignWorkersResult[w]]].push_back(w);
    }
    string out = "[";
    bool first = true;
    for (int o : open) {
        if (!first) out += ",";
        first = false;
        out += "{\"officeId\":" + to_string(o) + ",\"sites\":[";
        vector<int> ss = st.mem[o];
        sort(ss.begin(), ss.end());
        for (size_t i = 0; i < ss.size(); i++) out += (i ? "," : "") + to_string(ss[i]);
        out += "],\"workers\":[";
        for (size_t i = 0; i < wk[o].size(); i++) out += (i ? "," : "") + to_string(wk[o][i]);
        out += "]}";
    }
    out += "]\n";
    FILE* f = fopen(path, "w");
    if (!f) return;
    fwrite(out.data(), 1, out.size(), f);
    fclose(f);
}

// Promote the current best to the validated fallback if it passes the full check.
void refreshValid() {
    if (bestObj > validObj + 1e-9 && validateFull(fromAsg(bestAsg)).empty()) validObj = bestObj, validAsg = bestAsg;
}

// ---------------------------------------------------------------- parallelism
// Number of CPUs we can actually use: spin children briefly and measure their CPU time.
int effectiveCores() {
    int maxP = min(8, (int)thread::hardware_concurrency());
#ifdef __linux__
    {  // CPUs this process may run on (a container's cpuset can be smaller than the machine)
        cpu_set_t cs;
        CPU_ZERO(&cs);
        if (sched_getaffinity(0, sizeof cs, &cs) == 0 && CPU_COUNT(&cs) > 0) maxP = min(maxP, (int)CPU_COUNT(&cs));
    }
#endif
    if (maxP <= 1) return 1;
    const double spin = 0.3;
    vector<pid_t> kids;
    for (int i = 0; i < maxP; i++) {
        pid_t pid = fork();
        if (pid == 0) {
            auto t0 = chrono::steady_clock::now();
            volatile double x = 0;
            while (chrono::duration<double>(chrono::steady_clock::now() - t0).count() < spin)
                for (int k = 0; k < 1000; k++) x += k * 0.5;
            _exit(0);
        }
        if (pid > 0) kids.push_back(pid);
    }
    for (pid_t pid : kids) waitpid(pid, nullptr, 0);
    struct rusage ru;
    getrusage(RUSAGE_CHILDREN, &ru);
    double cpu = ru.ru_utime.tv_sec + ru.ru_utime.tv_usec * 1e-6 + ru.ru_stime.tv_sec + ru.ru_stime.tv_usec * 1e-6;
    return max(1, min(maxP, (int)(cpu / spin + 0.3)));
}

bool writeAll(int fd, const void* buf, size_t len) {
    const char* p = (const char*)buf;
    while (len) {
        ssize_t w = write(fd, p, len);
        if (w <= 0) return false;
        p += w, len -= w;
    }
    return true;
}
bool readAll(int fd, void* buf, size_t len) {
    char* p = (char*)buf;
    while (len) {
        ssize_t r = read(fd, p, len);
        if (r <= 0) return false;
        p += r, len -= r;
    }
    return true;
}

// ---------------------------------------------------------------- MIP over the zone pool
// Columns = candidate zones; choose a set maximising sum(value) - alpha*(tmax - tmin) such that
// every point (site or office location) is covered by at most one chosen zone hull (conservative
// EPS covers, as in validateFull), the count window |cnt_a - cnt_b| <= A holds over chosen zones
// and the workers suffice: per skill counting (single-skill / primary-skill workers) or, with
// multi-skill workers, binary "worker type -> zone" variables covering every needed skill.
// The solver is HiGHS in-process (USE_HIGHS) or an external process through stdout/stdin
// (SZ_MIPPIPE=1, see mip_driver.py). Without either the stage is skipped.
struct MipModel {
    int nc = 0, nr = 0;
    vector<double> cost, clo, chi, rlo, rhi;  // maximise cost.x
    vector<char> isInt;
    vector<int> start, idx;  // column-wise
    vector<double> val;
};
bool mipPipe() { return getenv("SZ_MIPPIPE") != nullptr; }
bool mipAvailable() {
#ifdef USE_HIGHS
    return true;
#else
    return mipPipe();
#endif
}
// returns column values ({} on failure); *status: 2 optimal, 1 feasible (time limit), 0 none
vector<double> solveMip(const MipModel& m, const vector<double>& warm, double tl, int* status) {
    *status = 0;
    if (tl < 0.5 || m.nc == 0) return {};
#ifdef USE_HIGHS
    if (!mipPipe()) {
        HighsModel model;
        HighsLp& lp = model.lp_;
        lp.num_col_ = m.nc;
        lp.num_row_ = m.nr;
        lp.sense_ = ObjSense::kMaximize;
        lp.col_cost_ = m.cost;
        lp.col_lower_ = m.clo;
        lp.col_upper_ = m.chi;
        lp.row_lower_ = m.rlo;
        lp.row_upper_ = m.rhi;
        lp.a_matrix_.format_ = MatrixFormat::kColwise;
        lp.a_matrix_.num_col_ = m.nc;
        lp.a_matrix_.num_row_ = m.nr;
        lp.a_matrix_.start_ = m.start;
        lp.a_matrix_.index_ = m.idx;
        lp.a_matrix_.value_ = m.val;
        lp.integrality_.resize(m.nc);
        for (int j = 0; j < m.nc; j++) lp.integrality_[j] = m.isInt[j] ? HighsVarType::kInteger : HighsVarType::kContinuous;
        Highs h;
        h.setOptionValue("output_flag", false);
        h.setOptionValue("time_limit", tl);
        h.setOptionValue("mip_rel_gap", 1e-6);
        // one thread: the MIP is solved serially anyway and the idle workers of HiGHS's task pool spin
        // (yield loops), which on a shared CPU takes time from the solve itself
        static const int mipThreads = 1;
        if (mipThreads > 0) h.setOptionValue("threads", mipThreads);
        if (h.passModel(model) != HighsStatus::kError) {
            if (!warm.empty()) {
                HighsSolution s0;
                s0.col_value = warm;
                s0.value_valid = true;
                h.setSolution(s0);
            }
            h.run();
            HighsModelStatus ms = h.getModelStatus();
            const HighsInfo& info = h.getInfo();
            if (info.primal_solution_status == kSolutionStatusFeasible) {
                *status = ms == HighsModelStatus::kOptimal ? 2 : 1;
                if (szDebug) fprintf(stderr, "mip: %s obj=%.6f bound=%.6f gap=%.3g\n", h.modelStatusToString(ms).c_str(), info.objective_function_value, info.mip_dual_bound, info.mip_gap);
                return h.getSolution().col_value;
            }
            if (szDebug) fprintf(stderr, "mip: %s, no solution\n", h.modelStatusToString(ms).c_str());
        }
        return {};
    }
#endif
    if (!mipPipe()) return {};
    // external solver: binary model on stdout, column values back on stdin
    vector<char> buf;
    auto put = [&](const void* p, size_t len) { buf.insert(buf.end(), (const char*)p, (const char*)p + len); };
    int32_t hdr[5] = {0x4D495031, m.nc, m.nr, (int32_t)m.idx.size(), warm.empty() ? 0 : 1};
    put(hdr, sizeof hdr);
    put(&tl, sizeof tl);
    put(m.cost.data(), 8 * m.nc), put(m.clo.data(), 8 * m.nc), put(m.chi.data(), 8 * m.nc);
    put(m.isInt.data(), m.nc);
    put(m.rlo.data(), 8 * m.nr), put(m.rhi.data(), 8 * m.nr);
    put(m.start.data(), 4 * (m.nc + 1)), put(m.idx.data(), 4 * m.idx.size()), put(m.val.data(), 8 * m.val.size());
    if (!warm.empty()) put(warm.data(), 8 * m.nc);
    if (!writeAll(1, buf.data(), buf.size())) return {};
    int32_t st = 0;
    struct pollfd pf = {0, POLLIN, 0};
    if (poll(&pf, 1, (int)((tl + 15) * 1000)) <= 0 || !readAll(0, &st, sizeof st) || st <= 0) return {};
    vector<double> x(m.nc);
    if (!readAll(0, x.data(), 8 * m.nc)) return {};
    *status = st;
    return x;
}
void mipFinish() {  // tell an external driver that no (more) models follow
    if (mipPipe()) {
        int32_t hdr[5] = {0x4D495031, 0, 0, 0, 0};
        double tl = 0;
        writeAll(1, hdr, sizeof hdr), writeAll(1, &tl, sizeof tl);
    }
}

// Pick the best compatible zone set from the pool; returns an assignment (size AS) better than
// incObj that passes validateFull, or {}.
int mipStreamFd = -1;  // child process: every improvement is sent at once (the parent may kill us)
vector<int> mipImprove(double deadline, const vector<int>& incAsg, double incObj) {
    double t0 = elapsed();
    static const size_t maxCols = 6000;
    static const int enrich = 3;  // bit 1 closure, bit 2 trims
    static const double baseShare = 0.5;
    bool dbg = szDebug;
    poolAddAsg(incAsg);
    // per-site profit by office is dist-dependent; zone value = sum(rew - dist) - cost
    auto zval = [&](int o, const vector<int>& s) {
        double v = -ocost[o];
        for (int x : s) v += rew[x] - dist[o][x];
        return v;
    };
    // incumbent zones are always kept
    unordered_set<uint64_t> inc;
    {
        vector<vector<int>> z(K);
        for (int s = 0; s < n; s++)
            if (incAsg[s] >= 0) z[incAsg[s]].push_back(s);
        for (int o = 0; o < K; o++)
            if (!z[o].empty()) inc.insert(zoneHash(o, z[o]));
    }
    // prune the pool: per office keep the most valuable zones
    vector<int> keep;
    {
        vector<vector<pair<double, int>>> byO(K);
        for (size_t i = 0; i < pool.size(); i++) {
            double v = zval(pool[i].o, pool[i].s);
            if (v > 1e-9 || inc.count(pool[i].h)) byO[pool[i].o].push_back({inc.count(pool[i].h) ? 1e300 : v, (int)i});
        }
        int nonEmpty = 0;
        for (int o = 0; o < K; o++) nonEmpty += !byO[o].empty();
        size_t quota = max<size_t>(4, (size_t)((enrich ? baseShare : 1.0) * maxCols) / max(1, nonEmpty));
        for (int o = 0; o < K; o++) {
            auto& v = byO[o];
            sort(v.begin(), v.end(), [](auto& a, auto& b) { return a.first > b.first; });
            for (size_t i = 0; i < v.size() && i < quota; i++) keep.push_back(v[i].second);
        }
    }
    // columns: zones with hull coverage; closures (free covered profitable sites with no new
    // skill: same hull) and trims (drop the least profitable sites: smaller sizes for the window)
    struct Col {
        int o;
        vector<int> s, cov;
        double v;
        int cnt, t;
        Mask m;
        uint64_t h;
    };
    vector<Col> cols;
    unordered_set<uint64_t> have;
    vector<int> tmp;
    auto addCol = [&](int o, vector<int> s, const vector<int>* cov) -> bool {
        if (s.empty() || (int)s.size() > maxSize[o]) return false;
        sort(s.begin(), s.end());
        uint64_t h = zoneHash(o, s);
        if (have.count(h)) return false;
        Col c;
        c.o = o, c.h = h, c.v = zval(o, s), c.cnt = s.size(), c.t = 0;
        if (c.v <= 1e-9 && !inc.count(h)) return false;
        for (int x : s) c.t += ntask[x], c.m |= smask[x];
        if (cov) c.cov = *cov;
        else {
            Hull hl;
            computeHullOf(o, s, hl, tmp);
            computeCov(hl, c.cov);
        }
        c.s = std::move(s);
        have.insert(h);
        cols.push_back(std::move(c));
        return true;
    };
    for (int i : keep) {
        if (elapsed() > t0 + 0.3 * (deadline - t0)) break;
        addCol(pool[i].o, pool[i].s, nullptr);
    }
    size_t nBase = cols.size();
    vector<char> isSite(NP, 0);
    for (size_t ci = 0; ci < nBase && cols.size() < maxCols; ci++) {
        if (elapsed() > t0 + 0.35 * (deadline - t0)) break;
        int o = cols[ci].o;
        // closure
        vector<pair<double, int>> fr;
        {
            const Col& c = cols[ci];
            for (int x : c.s) isSite[x] = 1;
            for (int p : c.cov)
                if (p < n && !isSite[p] && rew[p] - dist[o][p] > 0 && (smask[p] & ~c.m).none()) fr.push_back({-(rew[p] - dist[o][p]), p});
            for (int x : c.s) isSite[x] = 0;
        }
        if ((enrich & 1) && !fr.empty() && cols[ci].cnt < maxSize[o]) {
            sort(fr.begin(), fr.end());
            vector<int> s = cols[ci].s;
            for (auto& f : fr)
                if ((int)s.size() < maxSize[o]) s.push_back(f.second);
            vector<int> cv = cols[ci].cov;
            addCol(o, s, &cv);
        }
        // trims
        vector<pair<double, int>> pr;
        for (int x : cols[ci].s) pr.push_back({rew[x] - dist[o][x], x});
        sort(pr.begin(), pr.end());
        for (int r : {1, 3}) {
            if (!(enrich & 2) || r >= (int)pr.size() || cols.size() >= maxCols) break;
            vector<int> s;
            for (size_t i = r; i < pr.size(); i++) s.push_back(pr[i].second);
            addCol(o, s, nullptr);
        }
    }
    int nc = cols.size();
    if (dbg) fprintf(stderr, "mip: pool %zu kept %zu base %zu cols %d (%.2fs)\n", pool.size(), keep.size(), nBase, nc, elapsed() - t0);
    if (nc == 0) return {};
    const double INF = 1e30;
    // incumbent (improved in place) and its zones
    vector<int> cur = incAsg;
    cur.resize(AS, -1);
    double curObj = incObj;
    struct IZ {
        vector<int> cov;
        int cnt = 0, t = 0;
        Mask m;
    };
    vector<IZ> iz(K);
    auto loadInc = [&] {
        vector<vector<int>> z(K);
        for (int s = 0; s < n; s++)
            if (cur[s] >= 0) z[cur[s]].push_back(s);
        for (int o = 0; o < K; o++) {
            iz[o] = IZ();
            if (z[o].empty()) continue;
            Hull hl;
            computeHullOf(o, z[o], hl, tmp);
            computeCov(hl, iz[o].cov);
            iz[o].cnt = z[o].size();
            for (int s : z[o]) iz[o].t += ntask[s], iz[o].m |= smask[s];
        }
    };
    loadInc();
    unordered_map<uint64_t, int> colOf;
    for (int j = 0; j < nc; j++) colOf[cols[j].h] = j;
    // worker types (multi-skill workers): binary type->zone variables in the model
    vector<Mask> types;
    vector<int> typeOfW(W, -1);
    if (nativeW) {
        map<string, int> tid;
        for (int w = 0; w < W; w++) {
            if (realW[w].none()) continue;
            string key = realW[w].to_string();
            auto it = tid.find(key);
            if (it == tid.end()) typeOfW[w] = types.size(), tid[key] = types.size(), types.push_back(realW[w]);
            else typeOfW[w] = it->second;
        }
    }
    static const long long zCap = 300000;
    long long totalNnz = 0;
    // One MIP over the offices in F; the other offices keep their incumbent zones (and workers),
    // which block their covered points and fix bounds of the count window and the task range.
    // Returns an improved full assignment or {}; *optimal tells whether the MIP was solved.
    auto sub = [&](const vector<char>& inF, double tl, bool* optimal) -> vector<int> {
        *optimal = false;
        double ts = elapsed();
        vector<char> blocked(NP, 0);
        int nf = 0, fcmin = INT32_MAX, fcmax = 0, ftmin = INT32_MAX, ftmax = 0;
        vector<int> availK = availSkill;
        for (int o = 0; o < K; o++) {
            if (inF[o] || iz[o].cnt == 0) continue;
            nf++;
            for (int p : iz[o].cov) blocked[p] = 1;
            fcmin = min(fcmin, iz[o].cnt), fcmax = max(fcmax, iz[o].cnt);
            ftmin = min(ftmin, iz[o].t), ftmax = max(ftmax, iz[o].t);
            for (int k = 0; k < NS; k++)
                if (iz[o].m[k]) availK[k]--;
        }
        vector<int> typeCnt(types.size(), 0);
        for (int w = 0; w < W; w++)
            if (typeOfW[w] >= 0 && (cur[n + w] < 0 || inF[cur[n + w]])) typeCnt[typeOfW[w]]++;
        vector<int> cj;  // candidate columns
        for (int j = 0; j < nc; j++) {
            const Col& c = cols[j];
            if (!inF[c.o]) continue;
            if (nf && (c.cnt < fcmax - A || c.cnt > fcmin + A)) continue;
            bool ok = true;
            for (int p : c.cov)
                if (blocked[p]) {
                    ok = false;
                    break;
                }
            if (ok && !nativeW)
                for (int k = 0; k < NS && ok; k++)
                    if (c.m[k] && availK[k] <= 0) ok = false;
            if (ok) cj.push_back(j);
        }
        int m = cj.size();
        if (m == 0) return {};
        int Lv = -1, tmaxV = -1, tminV = -1;
        bool typed = false;
        if (nativeW) {
            long long nz = 0;
            for (int j : cj)
                for (auto& tm : types) nz += (tm & cols[j].m).any();
            typed = nz <= zCap;
        }
        MipModel M;
        vector<vector<pair<int, double>>> colEnt;
        auto newVar = [&](double c, double lo, double hi, bool in) {
            M.cost.push_back(c), M.clo.push_back(lo), M.chi.push_back(hi), M.isInt.push_back(in);
            colEnt.push_back({});
            return (int)M.cost.size() - 1;
        };
        auto newRow = [&](double lo, double hi) {
            M.rlo.push_back(lo), M.rhi.push_back(hi);
            return (int)M.rlo.size() - 1;
        };
        for (int j : cj) newVar(cols[j].v, 0, 1, true);
        // point packing rows: the office point rows make the columns of one office exclusive, so
        // other points need a row only if covered by columns of two or more offices; identical
        // rows and rows contained in a larger row are dropped
        {
            unordered_map<int, vector<int>> byPt;
            for (int a = 0; a < m; a++)
                for (int p : cols[cj[a]].cov) byPt[p].push_back(a);
            vector<vector<int>> rows;
            unordered_set<uint64_t> seenRow;
            for (auto& kv : byPt) {
                auto& js = kv.second;
                if (js.size() < 2) continue;
                bool multi = kv.first >= n;
                for (size_t i = 1; i < js.size() && !multi; i++) multi = cols[cj[js[i]]].o != cols[cj[js[0]]].o;
                if (!multi) continue;
                sort(js.begin(), js.end());
                if (!seenRow.insert(zoneHash(-1, js)).second) continue;
                rows.push_back(std::move(js));
            }
            sort(rows.begin(), rows.end(), [](auto& a, auto& b) { return a.size() > b.size(); });
            vector<vector<int>> rowsOf(m);
            vector<int> mark(m, 0);
            long long work = 0;
            for (size_t qi = 0; qi < rows.size(); qi++) {
                auto& js = rows[qi];
                bool dom = false;
                if (work < 200000000LL) {
                    int jm = js[0];
                    for (int j : js)
                        if (rowsOf[j].size() < rowsOf[jm].size()) jm = j;
                    for (int j : js) mark[j] = 1;
                    for (int q : rowsOf[jm]) {
                        int hit = 0;
                        for (int j : rows[q]) hit += mark[j];
                        work += rows[q].size();
                        if (hit == (int)js.size()) {
                            dom = true;
                            break;
                        }
                    }
                    for (int j : js) mark[j] = 0;
                }
                if (dom) continue;
                for (int j : js) rowsOf[j].push_back(qi);
                int r = newRow(-INF, 1);
                for (int j : js) colEnt[j].push_back({r, 1.0});
            }
        }
        // workers
        vector<vector<pair<int, int>>> zOf(m);
        if (typed) {
            vector<int> typeRow(types.size(), -1);
            for (int a = 0; a < m; a++) {
                const Col& c = cols[cj[a]];
                if (c.m.none()) continue;
                vector<int> skRow(NS, -1);
                for (int k = 0; k < NS; k++)
                    if (c.m[k]) {
                        skRow[k] = newRow(0, INF);  // sum z - x >= 0
                        colEnt[a].push_back({skRow[k], -1.0});
                    }
                for (size_t t = 0; t < types.size(); t++) {
                    Mask mm = types[t] & c.m;
                    if (mm.none() || typeCnt[t] == 0) continue;
                    if (typeRow[t] < 0) typeRow[t] = newRow(-INF, typeCnt[t]);
                    int v = newVar(0, 0, 1, true);
                    zOf[a].push_back({(int)t, v});
                    colEnt[v].push_back({typeRow[t], 1.0});
                    for (int k = 0; k < NS; k++)
                        if (mm[k]) colEnt[v].push_back({skRow[k], 1.0});
                }
            }
        } else {
            for (int k = 0; k < NS; k++) {
                vector<int> js;
                for (int a = 0; a < m; a++)
                    if (cols[cj[a]].m[k]) js.push_back(a);
                if ((int)js.size() <= availK[k]) continue;
                int r = newRow(-INF, max(0, availK[k]));
                for (int a : js) colEnt[a].push_back({r, 1.0});
            }
        }
        // count window: chosen => L <= cnt <= L + A; fixed zones: fcmax - A <= L <= fcmin
        int cmin = nf ? fcmin : INT32_MAX, cmax = nf ? fcmax : 0;
        for (int j : cj) cmin = min(cmin, cols[j].cnt), cmax = max(cmax, cols[j].cnt);
        if (cmax - cmin > A) {
            double lo = cmin, hi = cmax;
            if (nf) lo = max(lo, (double)fcmax - A), hi = min(hi, (double)fcmin);
            Lv = newVar(0, lo, hi, false);
            double Mb = cmax - cmin;
            for (int a = 0; a < m; a++) {
                int c = cols[cj[a]].cnt;
                if (c - A > lo) {
                    int r = newRow(c - A - Mb, INF);
                    colEnt[Lv].push_back({r, 1.0}), colEnt[a].push_back({r, -Mb});
                }
                if (c < hi) {
                    int r = newRow(-INF, c + Mb);
                    colEnt[Lv].push_back({r, 1.0}), colEnt[a].push_back({r, Mb});
                }
            }
        }
        // task range: tmax >= t_j x_j, tmin <= t_j + T(1 - x_j); fixed zones bound both
        double constTerm = 0;
        if (alpha > 0) {
            int thi = nf ? ftmax : 0;
            for (int j : cj) thi = max(thi, cols[j].t);
            tmaxV = newVar(-alpha, nf ? ftmax : 0, thi, false);
            tminV = newVar(alpha, 0, nf ? ftmin : thi, false);
            int r0 = newRow(0, INF);
            colEnt[tmaxV].push_back({r0, 1.0}), colEnt[tminV].push_back({r0, -1.0});
            for (int a = 0; a < m; a++) {
                int t = cols[cj[a]].t;
                if (t > (nf ? ftmax : 0)) {
                    int r = newRow(0, INF);
                    colEnt[tmaxV].push_back({r, 1.0}), colEnt[a].push_back({r, -(double)t});
                }
                if (t < (nf ? ftmin : thi)) {
                    int r = newRow(-INF, t + thi);
                    colEnt[tminV].push_back({r, 1.0}), colEnt[a].push_back({r, (double)thi});
                }
            }
        }
        (void)constTerm;
        M.nc = M.cost.size();
        M.nr = M.rlo.size();
        M.start.assign(1, 0);
        for (int v = 0; v < M.nc; v++) {
            for (auto& e : colEnt[v]) M.idx.push_back(e.first), M.val.push_back(e.second);
            M.start.push_back(M.idx.size());
        }
        vector<vector<pair<int, double>>>().swap(colEnt);
        totalNnz += M.idx.size();
        // warm start: the incumbent zones of F (when all are columns)
        vector<double> warm;
        {
            vector<vector<int>> z(K);
            for (int s = 0; s < n; s++)
                if (cur[s] >= 0 && inF[cur[s]]) z[cur[s]].push_back(s);
            unordered_map<int, int> posOf;
            for (int a = 0; a < m; a++) posOf[cj[a]] = a;
            vector<int> chosen;
            bool all = true;
            for (int o = 0; o < K && all; o++) {
                if (z[o].empty()) continue;
                auto it = colOf.find(zoneHash(o, z[o]));
                auto it2 = it == colOf.end() ? posOf.end() : posOf.find(it->second);
                if (it2 == posOf.end()) all = false;
                else chosen.push_back(it2->second);
            }
            if (all) {
                warm.assign(M.nc, 0.0);
                int c0 = nf ? fcmin : INT32_MAX, t0_ = nf ? ftmin : INT32_MAX, t1 = nf ? ftmax : 0;
                for (int a : chosen) {
                    warm[a] = 1;
                    c0 = min(c0, cols[cj[a]].cnt), t0_ = min(t0_, cols[cj[a]].t), t1 = max(t1, cols[cj[a]].t);
                }
                if (c0 == INT32_MAX) c0 = 0, t0_ = 0;
                if (Lv >= 0) warm[Lv] = max(M.clo[Lv], min(M.chi[Lv], (double)c0));
                if (tmaxV >= 0) warm[tmaxV] = t1, warm[tminV] = t0_;
                if (typed)
                    for (int a : chosen)
                        for (int w = 0; w < W; w++)
                            if (cur[n + w] == cols[cj[a]].o && typeOfW[w] >= 0)
                                for (auto& tv : zOf[a])
                                    if (tv.first == typeOfW[w]) warm[tv.second] = 1;
            }
        }
        int status = 0;
        vector<double> x = solveMip(M, warm, min(tl, deadline - elapsed()), &status);
        if (dbg) fprintf(stderr, "mip sub: |F|=%d fixed=%d cols=%d vars=%d rows=%d nnz=%zu warm=%d status=%d %.2fs t=%.2f\n", (int)count(inF.begin(), inF.end(), 1), nf, m, M.nc, M.nr, M.idx.size(), !warm.empty(), status, elapsed() - ts, elapsed());
        *optimal = status == 2;
        if (x.empty()) return {};
        // assemble: fixed offices keep zones and workers, F gets the chosen columns
        vector<int> asg = cur;
        for (int s = 0; s < n; s++)
            if (asg[s] >= 0 && inF[asg[s]]) asg[s] = -1;
        vector<vector<int>> freeW(types.size());
        if (nativeW) {
            for (int w = W - 1; w >= 0; w--)
                if (asg[n + w] >= 0 && inF[asg[n + w]]) asg[n + w] = -1;
            for (int w = W - 1; w >= 0; w--)
                if (asg[n + w] < 0 && typeOfW[w] >= 0) freeW[typeOfW[w]].push_back(w);
        }
        for (int a = 0; a < m; a++) {
            if (x[a] < 0.5) continue;
            const Col& c = cols[cj[a]];
            for (int s : c.s) {
                if (asg[s] != -1) return {};
                asg[s] = c.o;
            }
            if (typed)
                for (auto& tv : zOf[a])
                    if (x[tv.second] > 0.5 && !freeW[tv.first].empty()) asg[n + freeW[tv.first].back()] = c.o, freeW[tv.first].pop_back();
        }
        State st = fromAsg(asg);
        if (!countFeasible(st)) return {};
        double obj = trueObjective(st);
        if (obj <= curObj + 1e-9 * max(1.0, fabs(curObj))) return {};
        string err = validateFull(st);
        if (!err.empty()) {
            if (dbg) fprintf(stderr, "mip sub: answer rejected (%s)\n", err.c_str());
            return {};
        }
        return st.asg;
    };
    // global MIP first when small enough, then neighbourhoods of k nearby offices (LNS)
    vector<int> offs;
    {
        vector<char> hasCol(K, 0);
        for (auto& c : cols) hasCol[c.o] = 1;
        for (int o = 0; o < K; o++)
            if (hasCol[o] || iz[o].cnt > 0) offs.push_back(o);
    }
    long long covAll = 0;
    for (auto& c : cols) covAll += c.cov.size();
    int improved = 0, subs = 0;
    auto accept = [&](vector<int>& a) {
        State st = fromAsg(a);
        curObj = trueObjective(st);
        cur = st.asg;
        cur.resize(AS, -1);
        loadInc();
        improved++;
        if (mipStreamFd >= 0) {
            int len = cur.size();
            writeAll(mipStreamFd, &len, sizeof len);
            writeAll(mipStreamFd, cur.data(), sizeof(int) * len);
        }
    };
    static const long long globalNnz = 400000;
    if (covAll <= globalNnz) {
        vector<char> all(K, 1);
        bool opt;
        vector<int> a = sub(all, 0.5 * (deadline - elapsed()), &opt);
        subs++;
        if (!a.empty()) accept(a);
        if (opt) {
            if (dbg) fprintf(stderr, "mip: global MIP optimal, obj %.6f\n", curObj);
            return improved ? cur : vector<int>();
        }
    }
    int k = 8;
    k = max(2, min(k, (int)offs.size()));
    double subT = 4.0;
    vector<int> order = offs;
    size_t oi = order.size();
    int sinceImp = 0;
    while (elapsed() < deadline - 0.3 && !offs.empty()) {
        if (oi >= order.size()) {
            for (size_t i = order.size(); i > 1; i--) swap(order[i - 1], order[irand(i)]);
            oi = 0;
        }
        int o0 = order[oi++];
        vector<pair<double, int>> dd;
        for (int o = 0; o < K; o++) dd.push_back({hypot(px[n + o] - px[n + o0], py[n + o] - py[n + o0]), o});
        sort(dd.begin(), dd.end());
        vector<char> inF(K, 0);
        for (int i = 0; i < k && i < K; i++) inF[dd[i].second] = 1;
        bool opt;
        double ts = elapsed();
        vector<int> a = sub(inF, min(subT, deadline - elapsed()), &opt);
        subs++;
        if (!a.empty()) {
            accept(a);
            sinceImp = 0;
            if (dbg) fprintf(stderr, "mip: LNS k=%d improved to %.6f\n", k, curObj);
        } else
            sinceImp++;
        if (opt && elapsed() - ts < 0.25 * subT) k = min((int)offs.size(), k + 1);
        else if (!opt) k = max(2, k - 1);
        if (sinceImp > 3 * (int)offs.size() && k >= (int)offs.size()) break;  // nothing left to find
    }
    fprintf(stderr, "mip: %d sub-MIPs, %d improvements, final k=%d, obj %.6f (start %.6f), %.1fs\n", subs, improved, k, curObj, incObj, elapsed() - t0);
    return improved ? cur : vector<int>();
}

// ---------------------------------------------------------------- skill-subset zone MIP (rounds)
// For single-skill workers and few skills: each round builds a fresh candidate pool around the
// incumbent (its zones, one-step perturbations, power-diagram cells of its open offices with noisy
// weights, the same with random closed offices added), and for every region and every skill subset
// Q emits the most profitable prefixes of its sites needing only skills in Q. The MIP picks <= 1
// zone per office, no point covered twice (validator coverage), workers per skill through z[o,k],
// count window and task range aggregated per office. Warm start = the incumbent (full vector).
bool origSingleSkill = true;  // input workers all single-skill (before any primary-skill strip)
bool recipeGate() {
    if (!(origSingleSkill && !nativeW && NS >= 1 && NS <= 4 && n > 0 && K > 0)) return false;
    // only where it pays (benchmarks): scarce capacity (total maxSize well below n, so every office
    // is packed and the skill mix per office decides), a binding count window, and small zones
    // (mean maxSize <= 64: with larger zones the round MIPs hit their time limit without
    // improving). Elsewhere the recipe stalls early or is too slow, and the SA time it takes
    // costs more than it brings: keep the plain search + pool MIP there.
    static const double capMax = 0.8;
    static const double zoneMax = 64;
    double capSum = 0;
    for (int o = 0; o < K; o++) capSum += min(maxSize[o], n);
    return capSum <= capMax * n && 2.0 * A < n && capSum <= zoneMax * K;
}
vector<int> recipeImprove(double deadline, const vector<int>& incAsg, double incObj) {
    double t0 = elapsed();
    bool dbg = szDebug;
    static const int NW = 16;
    static const double RTL = 30.0;
    static const double XF = 0.25;
    static const size_t candCap = 60000;
    mt19937_64 rr(rng() ^ 0x5DEECE66DULL);
    normal_distribution<double> nd(0.0, 1.0);
    const double INF = 1e30;
    vector<char> serv(n, 1);
    vector<uint32_t> bm(n, 0);
    uint32_t availMask = 0;
    for (int k = 0; k < NS && k < 32; k++)
        if (availSkill[k] > 0) availMask |= 1u << k;
    for (int s = 0; s < n; s++)
        for (int k = 0; k < NS; k++)
            if (smask[s][k]) {
                bm[s] |= 1u << k;
                if (availSkill[k] <= 0) serv[s] = 0;
            }
    vector<uint32_t> subsets = {0xFFFFFFFFu};  // no filter
    {
        vector<int> sk;
        for (int k = 0; k < NS; k++)
            if (availMask >> k & 1) sk.push_back(k);
        if (sk.size() <= 4)
            for (uint32_t q = 1; q < (1u << sk.size()); q++) {
                uint32_t m = 0;
                for (size_t i = 0; i < sk.size(); i++)
                    if (q >> i & 1) m |= 1u << sk[i];
                if (m != availMask) subsets.push_back(m);  // the full set equals "no filter"
            }
    }
    auto P = [&](int o, int s) { return rew[s] - dist[o][s]; };
    vector<int> cur = incAsg;
    cur.resize(AS, -1);
    double curObj = incObj;
    int stall = 0, improved = 0, rounds = 0;
    struct Cand {
        int o, cnt, t;
        vector<int> s, cov;
        double v;
        uint32_t m;
    };
    vector<int> tmp;
    while (true) {
        double left = deadline - elapsed();
        if (left < 4) break;
        double tr = elapsed();
        vector<Cand> C;
        unordered_map<uint64_t, int> key;
        bool full = false;
        auto add = [&](int o, vector<int> s, bool force) -> int {
            if (!force) s.erase(remove_if(s.begin(), s.end(), [&](int x) { return !serv[x]; }), s.end());
            sort(s.begin(), s.end());
            s.erase(unique(s.begin(), s.end()), s.end());
            if (s.empty() || (!force && (int)s.size() > maxSize[o])) return -1;
            uint64_t h = zoneHash(o, s);
            auto it = key.find(h);
            if (it != key.end()) return it->second;
            if (!force && (C.size() >= candCap || full)) return -1;
            Cand c;
            c.o = o, c.cnt = s.size(), c.t = 0, c.v = -ocost[o], c.m = 0;
            for (int x : s) c.t += ntask[x], c.v += P(o, x), c.m |= bm[x];
            Hull hl;
            computeHullOf(o, s, hl, tmp);
            computeCov(hl, c.cov);
            c.s = std::move(s);
            key[h] = C.size();
            C.push_back(std::move(c));
            return (int)C.size() - 1;
        };
        // incumbent zones
        vector<vector<int>> Z(K);
        for (int s = 0; s < n; s++)
            if (cur[s] >= 0) Z[cur[s]].push_back(s);
        vector<int> open, incIdx;
        for (int o = 0; o < K; o++)
            if (!Z[o].empty()) open.push_back(o), incIdx.push_back(add(o, Z[o], true));
        int lo = INT32_MAX, hi = 0;
        for (int o : open) lo = min(lo, (int)Z[o].size()), hi = max(hi, (int)Z[o].size());
        if (open.empty()) lo = hi = 1;
        // regions -> prefixes per skill subset and size
        vector<int> R, RR;
        auto emit = [&](int o, const vector<int>& reg) {
            R.clear();
            for (int s : reg)
                if (serv[s] && P(o, s) > 0) R.push_back(s);
            if (R.empty()) return;
            sort(R.begin(), R.end(), [&](int a, int b) { return P(o, a) > P(o, b) || (P(o, a) == P(o, b) && a < b); });
            for (uint32_t Q : subsets) {
                RR.clear();
                for (int s : R)
                    if ((bm[s] & ~Q) == 0) RR.push_back(s);
                if (RR.empty()) continue;
                int L = min((int)RR.size(), maxSize[o]);
                int cand[6] = {L, lo, hi, (lo + hi) / 2, max(1, hi - A), lo + A};
                int nc = A < n ? 6 : 1;
                sort(cand, cand + nc);
                for (int i = 0; i < nc; i++) {
                    int m = cand[i];
                    if (m < 1 || m > L || (i && m == cand[i - 1])) continue;
                    add(o, vector<int>(RR.begin(), RR.begin() + m), false);
                }
            }
        };
        // perturbations of the incumbent zones
        for (int o : open) {
            if (elapsed() > deadline - 3) break;
            const vector<int>& ss = Z[o];
            Hull hl;
            computeHullOf(o, ss, hl, tmp);
            vector<int> hv;
            for (int v : hl.v)
                if (v < n) hv.push_back(v);
            for (int v : hv) {
                vector<int> t;
                for (int x : ss)
                    if (x != v) t.push_back(x);
                add(o, t, false);
            }
            double cx = 0, cy = 0;
            for (int x : ss) cx += px[x], cy += py[x];
            cx /= ss.size(), cy /= ss.size();
            vector<pair<double, int>> fr;
            for (int s = 0; s < n; s++)
                if (cur[s] < 0 && serv[s] && P(o, s) > 0) fr.push_back({hypot(px[s] - cx, py[s] - cy), s});
            int nn = min((int)fr.size(), 10);
            partial_sort(fr.begin(), fr.begin() + nn, fr.end());
            if (nn > 0) {
                int worst = ss[0];
                for (int x : ss)
                    if (P(o, x) < P(o, worst)) worst = x;
                for (int k : {1, 2, 3, 5}) {
                    if ((int)ss.size() + k > maxSize[o] || k > nn) continue;
                    vector<int> t = ss;
                    for (int i = 0; i < k; i++) t.push_back(fr[i].second);
                    add(o, t, false);
                }
                for (int i = 0; i < min(nn, 5); i++) {
                    int xa = fr[i].second;
                    vector<int> drops = {worst};
                    for (size_t j = 0; j < hv.size() && j < 6; j++) drops.push_back(hv[j]);
                    for (int d : drops) {
                        vector<int> t;
                        for (int x : ss)
                            if (x != d) t.push_back(x);
                        t.push_back(xa);
                        add(o, t, false);
                    }
                }
            }
            emit(o, ss);
        }
        // power-diagram cells: open offices (sigma 0.3), plus random closed ones (sigma 0.4)
        auto power = [&](int extra, double sigma) {
            vector<int> offs = open;
            if (extra > 0) {
                vector<int> closed;
                for (int o = 0; o < K; o++)
                    if (Z[o].empty()) closed.push_back(o);
                for (int i = 0; i < extra && !closed.empty(); i++) {
                    int j = rr() % closed.size();
                    offs.push_back(closed[j]);
                    closed[j] = closed.back(), closed.pop_back();
                }
            }
            {  // one office per location
                vector<int> keep;
                for (int o : offs) {
                    bool dup = false;
                    for (int q : keep)
                        if (px[n + o] == px[n + q] && py[n + o] == py[n + q]) dup = true;
                    if (!dup) keep.push_back(o);
                }
                offs.swap(keep);
            }
            int m = offs.size();
            if (m == 0) return;
            vector<double> r2(m, 0), w(m);
            for (int i = 0; i < m; i++)
                for (int s : Z[offs[i]]) r2[i] = max(r2[i], pow(px[s] - px[n + offs[i]], 2) + pow(py[s] - py[n + offs[i]], 2));
            vector<double> pos;
            for (double v : r2)
                if (v > 0) pos.push_back(v);
            double base = 0.01;
            if (!pos.empty()) {
                nth_element(pos.begin(), pos.begin() + pos.size() / 2, pos.end());
                base = pos[pos.size() / 2];
            }
            for (double& v : r2)
                if (v <= 0) v = base * 0.3;
            vector<vector<int>> cell(m);
            for (int it = 0; it < NW; it++) {
                if (elapsed() > deadline - 3 || full) break;
                for (int i = 0; i < m; i++) w[i] = it ? r2[i] * exp(sigma * nd(rr)) : r2[i];
                for (auto& c : cell) c.clear();
                for (int s = 0; s < n; s++) {
                    int bi = 0;
                    double bv = 1e300;
                    for (int i = 0; i < m; i++) {
                        double dx = px[s] - px[n + offs[i]], dy = py[s] - py[n + offs[i]];
                        double v = dx * dx + dy * dy - w[i];
                        if (v < bv) bv = v, bi = i;
                    }
                    cell[bi].push_back(s);
                }
                for (int i = 0; i < m; i++) emit(offs[i], cell[i]);
                if (C.size() >= candCap) full = true;
            }
        };
        // after rounds without gain the cells get noisier and more closed offices join
        power(0, 0.3 * (1 + 0.5 * stall));
        power(max(3, (int)(K * XF * (1 + 0.5 * stall))), 0.4 * (1 + 0.5 * stall));
        int m = C.size();
        double tgen = elapsed() - tr;
        // ---- model
        MipModel M;
        vector<vector<pair<int, double>>> colEnt;
        auto newVar = [&](double c, double l, double h, bool in) {
            M.cost.push_back(c), M.clo.push_back(l), M.chi.push_back(h), M.isInt.push_back(in);
            colEnt.push_back({});
            return (int)M.cost.size() - 1;
        };
        auto newRow = [&](double l, double h) {
            M.rlo.push_back(l), M.rhi.push_back(h);
            return (int)M.rlo.size() - 1;
        };
        for (int j = 0; j < m; j++) newVar(C[j].v, 0, 1, true);
        int nconf = 0;
        {  // point rows (office point rows make the zones of one office exclusive)
            vector<vector<int>> byPt(NP);
            for (int j = 0; j < m; j++)
                for (int p : C[j].cov) byPt[p].push_back(j);
            vector<vector<int>> rows;
            unordered_set<uint64_t> seenRow;
            for (int p = 0; p < NP; p++) {
                auto& js = byPt[p];
                if (js.size() < 2) continue;
                bool multi = p >= n;
                for (size_t i = 1; i < js.size() && !multi; i++) multi = C[js[i]].o != C[js[0]].o;
                if (!multi) continue;
                if (!seenRow.insert(zoneHash(-1, js)).second) continue;  // js is sorted (ascending j)
                rows.push_back(std::move(js));
            }
            vector<vector<int>>().swap(byPt);
            stable_sort(rows.begin(), rows.end(), [](auto& a, auto& b) { return a.size() > b.size(); });
            vector<vector<int>> rowsOf(m);
            vector<int> mark(m, 0);
            long long work = 0;
            for (size_t qi = 0; qi < rows.size(); qi++) {
                auto& js = rows[qi];
                bool dom = false;
                if (work < 300000000LL) {
                    int jm = js[0];
                    for (int j : js)
                        if (rowsOf[j].size() < rowsOf[jm].size()) jm = j;
                    for (int j : js) mark[j] = 1;
                    for (int q : rowsOf[jm]) {
                        int hit = 0;
                        for (int j : rows[q]) hit += mark[j];
                        work += rows[q].size();
                        if (hit == (int)js.size()) {
                            dom = true;
                            break;
                        }
                    }
                    for (int j : js) mark[j] = 0;
                }
                if (dom) continue;
                for (int j : js) rowsOf[j].push_back(qi);
                int r = newRow(-INF, 1);
                nconf++;
                for (int j : js) colEnt[j].push_back({r, 1.0});
            }
        }
        // per office: its candidates
        vector<vector<int>> byO(K);
        for (int j = 0; j < m; j++) byO[C[j].o].push_back(j);
        // workers: y_j <= z[o,k] for k in needs(j); sum_o z[o,k] <= avail_k
        map<pair<int, int>, int> zv;
        for (int k = 0; k < NS; k++) {
            vector<int> offk;
            for (int o = 0; o < K; o++) {
                bool any = false;
                for (int j : byO[o])
                    if (C[j].m >> k & 1) {
                        any = true;
                        break;
                    }
                if (any) offk.push_back(o);
            }
            if ((int)offk.size() <= availSkill[k]) continue;
            int rk = newRow(-INF, max(0, availSkill[k]));
            for (int o : offk) {
                int z = newVar(0, 0, 1, false);
                zv[{o, k}] = z;
                colEnt[z].push_back({rk, 1.0});
                int r = newRow(-INF, 0);
                colEnt[z].push_back({r, -1.0});
                for (int j : byO[o])
                    if (C[j].m >> k & 1) colEnt[j].push_back({r, 1.0});
            }
        }
        // count window
        int cmaxV = -1, cminV = -1, tmaxV = -1, tminV = -1;
        int mincnt = INT32_MAX, maxcnt = 0, maxt = 0;
        for (auto& c : C) mincnt = min(mincnt, c.cnt), maxcnt = max(maxcnt, c.cnt), maxt = max(maxt, c.t);
        if (m && maxcnt - mincnt > A) {
            cmaxV = newVar(0, 0, maxcnt, false);
            cminV = newVar(0, 0, maxcnt, false);
            int r0 = newRow(-INF, A);
            colEnt[cmaxV].push_back({r0, 1.0}), colEnt[cminV].push_back({r0, -1.0});
            double Mb = maxcnt;
            for (int o = 0; o < K; o++) {
                if (byO[o].empty()) continue;
                int r1 = newRow(-INF, 0), r2 = newRow(-Mb, INF);
                colEnt[cmaxV].push_back({r1, -1.0});
                colEnt[cminV].push_back({r2, -1.0});
                for (int j : byO[o]) {
                    colEnt[j].push_back({r1, (double)C[j].cnt});
                    colEnt[j].push_back({r2, (double)C[j].cnt - Mb});
                }
            }
        }
        // task range
        if (alpha > 0 && m) {
            double MT = maxt;
            tmaxV = newVar(-alpha, 0, MT, false);
            tminV = newVar(alpha, 0, MT, false);
            int r0 = newRow(0, INF);
            colEnt[tmaxV].push_back({r0, 1.0}), colEnt[tminV].push_back({r0, -1.0});
            for (int o = 0; o < K; o++) {
                if (byO[o].empty()) continue;
                int r1 = newRow(-INF, 0), r2 = newRow(-MT, INF);
                colEnt[tmaxV].push_back({r1, -1.0});
                colEnt[tminV].push_back({r2, -1.0});
                for (int j : byO[o]) {
                    colEnt[j].push_back({r1, (double)C[j].t});
                    colEnt[j].push_back({r2, (double)C[j].t - MT});
                }
            }
        }
        M.nc = M.cost.size();
        M.nr = M.rlo.size();
        M.start.assign(1, 0);
        for (int v = 0; v < M.nc; v++) {
            for (auto& e : colEnt[v]) M.idx.push_back(e.first), M.val.push_back(e.second);
            M.start.push_back(M.idx.size());
        }
        vector<vector<pair<int, double>>>().swap(colEnt);
        // full warm start: y, z, count window, task range
        vector<double> warm(M.nc, 0.0);
        {
            int c0 = INT32_MAX, c1 = 0, t0_ = INT32_MAX, t1 = 0;
            for (size_t i = 0; i < open.size(); i++) {
                const Cand& c = C[incIdx[i]];
                warm[incIdx[i]] = 1;
                c0 = min(c0, c.cnt), c1 = max(c1, c.cnt), t0_ = min(t0_, c.t), t1 = max(t1, c.t);
                for (int k = 0; k < NS; k++)
                    if (c.m >> k & 1) {
                        auto it = zv.find({c.o, k});
                        if (it != zv.end()) warm[it->second] = 1;
                    }
            }
            if (open.empty()) c0 = c1 = t0_ = t1 = 0;
            if (cmaxV >= 0) warm[cmaxV] = c1, warm[cminV] = c0;
            if (tmaxV >= 0) warm[tmaxV] = t1, warm[tminV] = t0_;
        }
        left = deadline - elapsed();
        double tl = min(RTL, left - 1.0);
        if (left - 1.0 - tl < 12) tl = left - 1.0;
        if (tl < 2) break;
        int status = 0;
        double ts = elapsed();
        vector<double> x = solveMip(M, warm, tl, &status);
        rounds++;
        bool imp = false;
        if (!x.empty()) {
            vector<int> asg(AS, -1);
            bool clash = false;
            for (int j = 0; j < m && !clash; j++) {
                if (x[j] < 0.5) continue;
                for (int s : C[j].s) {
                    if (asg[s] != -1) clash = true;
                    asg[s] = C[j].o;
                }
            }
            if (!clash) {
                State st = fromAsg(asg);
                if (countFeasible(st)) {
                    double obj = trueObjective(st);
                    if (obj > curObj + 1e-9 * max(1.0, fabs(curObj))) {
                        string err = validateFull(st);
                        if (err.empty()) {
                            cur = st.asg;
                            cur.resize(AS, -1);
                            curObj = obj;
                            imp = true;
                            improved++;
                            if (mipStreamFd >= 0) {
                                int len = cur.size();
                                writeAll(mipStreamFd, &len, sizeof len);
                                writeAll(mipStreamFd, cur.data(), sizeof(int) * len);
                            }
                        } else if (dbg)
                            fprintf(stderr, "recipe: answer rejected (%s)\n", err.c_str());
                    }
                }
            } else if (dbg)
                fprintf(stderr, "recipe: answer rejected (site clash)\n");
        }
        if (dbg) fprintf(stderr, "recipe round %d: cand=%d rows=%d conf=%d nnz=%zu gen=%.1fs mip=%.1fs status=%d obj=%.6f%s t=%.1f\n", rounds, m, M.nr, nconf, M.idx.size(), tgen, elapsed() - ts, status, curObj, imp ? " (improved)" : "", elapsed());
        if (imp) stall = 0;
        else if (++stall >= 6) break;
    }
    fprintf(stderr, "recipe: %d rounds, %d improvements, obj %.6f (start %.6f), %.1fs\n", rounds, improved, curObj, incObj, elapsed() - t0);
    return improved ? cur : vector<int>();
}

// ---------------------------------------------------------------- main
// ---- r25: independent simple solver (site->office SA with exact hull ownership), used as a start phase
namespace simple_sz {

// ---------------------------------------------------------------- timing / rng
static chrono::steady_clock::time_point T_START;
static double elapsed() { return chrono::duration<double>(chrono::steady_clock::now() - T_START).count(); }
struct RNG {
    uint64_t s;
    explicit RNG(uint64_t seed = 88172645463325252ULL) : s(seed ? seed : 1) {}
    uint64_t next() { s ^= s << 7; s ^= s >> 9; return s; }
    int nextInt(int n) { return (int)(next() % (uint64_t)n); }
    double nextDouble() { return (next() >> 11) * (1.0 / 9007199254740992.0); }
};

// ---------------------------------------------------------------- instance
struct Instance {
    int n = 0, m = 0, W = 0, NS = 0;
    vector<double> sx, sy, rew;
    vector<vector<pair<int,int>>> sk; // distinct skills with multiplicity
    vector<int> ntask;
    vector<double> ox, oy, cost;
    vector<int> maxSize;
    vector<vector<int>> workers;
    vector<double> dist;            // m*n
    int A = 0;
    double alpha = 0;
    double tol = 0;                 // geometric tolerance (0 = derive from the coordinates)
    double deadline = 1e300;        // seconds since T_START
    double d(int o, int i) const { return dist[(size_t)o * n + i]; }
};

// ---------------------------------------------------------------- solver
struct Solver {
    const Instance& I;
    int n, m, P, NS, W;
    vector<double> X, Y;  // points: sites then offices
    double tol = 1e-9;
    // grid
    double gx0, gy0, gcs; int GX, GY;
    vector<int> cellStart, cellPts;
    vector<vector<int>> knn;      // site neighbours
    vector<vector<int>> nearOff;  // offices sorted by distance per site (top few)
    vector<char> skillUseless;    // site has a skill no worker has
    RNG rng;

    // ---- state
    vector<int> assign, cnt, T, owner;
    vector<char> isVert;
    vector<vector<int>> hull;
    vector<double> hbx0, hby0, hbx1, hby1;
    double profit = 0, costSum = 0;
    vector<int> workerOf;
    vector<int> need, have; // m*NS
    vector<vector<int>> offWorkers;
    vector<int> freeWorkers; vector<int> freePos;

    // undo log
    struct LogE { int type; int a, b, c; };  // type 0: owner(p, old), 1: assign(i, old), 2: worker(w, oldOffice)
    vector<LogE> lg;
    vector<pair<int, vector<int>>> hullLog;
    bool logging = false;

    Solver(const Instance& I_, uint64_t seed) : I(I_), rng(seed) {
        n = I.n; m = I.m; P = n + m; NS = max(1, I.NS); W = I.W;
        X.resize(P); Y.resize(P);
        for (int i = 0; i < n; ++i) { X[i] = I.sx[i]; Y[i] = I.sy[i]; }
        for (int o = 0; o < m; ++o) { X[n + o] = I.ox[o]; Y[n + o] = I.oy[o]; }
        double x0 = 1e300, y0 = 1e300, x1 = -1e300, y1 = -1e300;
        for (int p = 0; p < P; ++p) { x0 = min(x0, X[p]); y0 = min(y0, Y[p]); x1 = max(x1, X[p]); y1 = max(y1, Y[p]); }
        double ext = max({x1 - x0, y1 - y0, 1e-12});
        double amax = max({fabs(x0), fabs(y0), fabs(x1), fabs(y1), 1e-12});
        tol = I.tol > 0 ? I.tol : max(ext * 1e-9, amax * 1e-12);
        // the grid covers the sites only (offices far outside are clamped into border cells)
        if (n > 0) {
            x0 = y0 = 1e300; x1 = y1 = -1e300;
            for (int p = 0; p < n; ++p) { x0 = min(x0, X[p]); y0 = min(y0, Y[p]); x1 = max(x1, X[p]); y1 = max(y1, Y[p]); }
        }
        gx0 = x0 - tol * 4; gy0 = y0 - tol * 4;
        double area = (x1 - x0 + tol * 8) * (y1 - y0 + tol * 8);
        gcs = sqrt(max(area, 1e-24) / max(1, max(n, 2) / 2));
        if (gcs <= 0 || !isfinite(gcs)) gcs = 1;
        GX = min(4096, max(1, (int)((x1 - gx0) / gcs) + 2)); GY = min(4096, max(1, (int)((y1 - gy0) / gcs) + 2));
        gcs = max((x1 - gx0) / (GX - 1), (y1 - gy0) / (GY - 1)) * 1.000001 + 1e-300;
        cellStart.assign(GX * GY + 1, 0);
        vector<int> cid(P);
        for (int p = 0; p < P; ++p) { cid[p] = cellOf(X[p], Y[p]); cellStart[cid[p] + 1]++; }
        for (int c = 0; c < GX * GY; ++c) cellStart[c + 1] += cellStart[c];
        cellPts.resize(P); vector<int> fill(cellStart.begin(), cellStart.end() - 1);
        for (int p = 0; p < P; ++p) cellPts[fill[cid[p]]++] = p;
        for (int c = 0; c < GX * GY; ++c) if (cellStart[c + 1] - cellStart[c] > 2000) { broken = true; return; }  // degenerate geometry
        // knn among sites
        int K = min(10, n - 1);
        knn.assign(n, {});
        for (int i = 0; i < n && K > 0; ++i) {
            if ((i & 255) == 0 && elapsed() > I.deadline) { broken = true; return; }
            int cx = cx_(X[i]), cy = cy_(Y[i]);
            vector<pair<double,int>> cand;
            for (int r = 0; ; ++r) {
                for (int gx = cx - r; gx <= cx + r; ++gx) for (int gy = cy - r; gy <= cy + r; ++gy) {
                    if (max(abs(gx - cx), abs(gy - cy)) != r) continue;
                    if (gx < 0 || gy < 0 || gx >= GX || gy >= GY) continue;
                    int c = gy * GX + gx;
                    for (int k = cellStart[c]; k < cellStart[c + 1]; ++k) { int q = cellPts[k]; if (q < n && q != i) cand.push_back({sq(X[q]-X[i]) + sq(Y[q]-Y[i]), q}); }
                }
                if ((int)cand.size() >= K && r >= 1) {
                    nth_element(cand.begin(), cand.begin() + (K - 1), cand.end());
                    if (cand[K - 1].first <= sq(r * gcs)) break;
                    if (cand.size() > 4096) { cand.resize(K); }  // keep the K nearest so far
                }
                if (r > max(GX, GY)) break;
            }
            sort(cand.begin(), cand.end());
            for (int k = 0; k < K && k < (int)cand.size(); ++k) knn[i].push_back(cand[k].second);
        }
        int NO = min(m, 6);
        nearOff.assign(n, {});
        for (int i = 0; i < n; ++i) {
            vector<pair<double,int>> v; for (int o = 0; o < m; ++o) if (I.maxSize[o] > 0) v.push_back({I.d(o, i), o});
            partial_sort(v.begin(), v.begin() + min((int)v.size(), NO), v.end());
            for (int k = 0; k < NO && k < (int)v.size(); ++k) nearOff[i].push_back(v[k].second);
        }
        vector<char> hasSkill(NS, 0);
        for (auto& w : I.workers) for (int s : w) hasSkill[s] = 1;
        skillUseless.assign(n, 0);
        for (int i = 0; i < n; ++i) for (auto& kv : I.sk[i]) if (!hasSkill[kv.first]) skillUseless[i] = 1;
        reset();
    }
    bool broken = false;
    bool late() const { return elapsed() > I.deadline; }
    static double sq(double v) { return v * v; }
    // clamp in double before the cast: a far point's quotient can exceed INT_MAX (UB in the cast)
    int cx_(double x) const { double q = (x - gx0) / gcs; q = max(0.0, min(q, (double)(GX - 1))); return (int)q; }
    int cy_(double y) const { double q = (y - gy0) / gcs; q = max(0.0, min(q, (double)(GY - 1))); return (int)q; }
    int cellOf(double x, double y) const { return cy_(y) * GX + cx_(x); }

    void reset() {
        assign.assign(n, -1); cnt.assign(m, 0); T.assign(m, 0); owner.assign(P, -1); isVert.assign(P, 0);
        hull.assign(m, {}); hbx0.assign(m, 0); hby0.assign(m, 0); hbx1.assign(m, 0); hby1.assign(m, 0);
        profit = 0; costSum = 0;
        workerOf.assign(W, -1); need.assign((size_t)m * NS, 0); have.assign((size_t)m * NS, 0);
        offWorkers.assign(m, {}); freeWorkers.clear(); freePos.assign(W, -1);
        for (int w = 0; w < W; ++w) { freePos[w] = freeWorkers.size(); freeWorkers.push_back(w); }
        lg.clear(); hullLog.clear();
    }

    // ---- geometry
    inline double cross(int o, int a, int b) const { return (X[a] - X[o]) * (Y[b] - Y[o]) - (Y[a] - Y[o]) * (X[b] - X[o]); }
    inline double crossP(int o, int a, double px, double py) const { return (X[a] - X[o]) * (py - Y[o]) - (Y[a] - Y[o]) * (px - X[o]); }
    vector<int> hullOf(vector<int> pts) const {
        sort(pts.begin(), pts.end(), [&](int a, int b) { return X[a] < X[b] || (X[a] == X[b] && (Y[a] < Y[b] || (Y[a] == Y[b] && a < b))); });
        // dedupe coordinates
        vector<int> u; for (int p : pts) if (u.empty() || X[u.back()] != X[p] || Y[u.back()] != Y[p]) u.push_back(p);
        if (u.size() <= 2) return u;
        vector<int> h(2 * u.size()); int k = 0;
        for (size_t i = 0; i < u.size(); ++i) { while (k >= 2 && cross(h[k-2], h[k-1], u[i]) <= 0) --k; h[k++] = u[i]; }
        for (int i = (int)u.size() - 2, t = k + 1; i >= 0; --i) { while (k >= t && cross(h[k-2], h[k-1], u[i]) <= 0) --k; h[k++] = u[i]; }
        h.resize(k - 1);
        if (h.size() < 2) h = {u.front(), u.back()};
        return h;
    }
    bool coveredH(const vector<int>& h, double px, double py) const {
        if (h.empty()) return false;
        if (h.size() == 1) return sq(px - X[h[0]]) + sq(py - Y[h[0]]) <= tol * tol;
        if (h.size() == 2) {
            double ax = X[h[0]], ay = Y[h[0]], bx = X[h[1]], by = Y[h[1]];
            double dx = bx - ax, dy = by - ay, L2 = dx * dx + dy * dy;
            double t = L2 > 0 ? ((px - ax) * dx + (py - ay) * dy) / L2 : 0; t = max(0.0, min(1.0, t));
            return sq(px - ax - t * dx) + sq(py - ay - t * dy) <= tol * tol;
        }
        int k = h.size();
        for (int i = 0; i < k; ++i) {
            int a = h[i], b = h[i + 1 == k ? 0 : i + 1];
            double c = crossP(a, b, px, py);
            if (c < 0) { double L = sqrt(sq(X[b] - X[a]) + sq(Y[b] - Y[a])); if (c < -tol * L) return false; }
        }
        return true;
    }
    bool inTri(int a, int b, int c, double px, double py) const {  // closed triangle with tolerance (orientation-agnostic)
        vector<int> h = hullOf({a, b, c});
        return coveredH(h, px, py);
    }
    template <class F> void scanBox(double x0, double y0, double x1, double y1, F f) const {
        int cx0 = cx_(x0 - tol * 2), cx1 = cx_(x1 + tol * 2), cy0 = cy_(y0 - tol * 2), cy1 = cy_(y1 + tol * 2);
        for (int gy = cy0; gy <= cy1; ++gy) for (int gx = cx0; gx <= cx1; ++gx) {
            int c = gy * GX + gx;
            for (int k = cellStart[c]; k < cellStart[c + 1]; ++k) f(cellPts[k]);
        }
    }
    // visit points in grid cells meeting the convex polygon poly (CCW or any order; convex), expanded by tol
    template <class F> void scanPoly(const vector<int>& poly, F f) const {
        if (poly.empty()) return;
        double y0 = 1e300, y1 = -1e300;
        for (int p : poly) { y0 = min(y0, Y[p]); y1 = max(y1, Y[p]); }
        int cy0 = cy_(y0 - tol * 2), cy1 = cy_(y1 + tol * 2);
        int k = poly.size();
        for (int gy = cy0; gy <= cy1; ++gy) {
            double yl = gy0 + gy * gcs - tol * 2, yh = yl + gcs + tol * 4;
            if (gy == 0) yl = -1e300;
            if (gy == GY - 1) yh = 1e300;
            double xl = 1e300, xh = -1e300;
            for (int e = 0; e < k; ++e) {
                int a = poly[e], b = poly[(e + 1) % k];
                double ay = Y[a], by = Y[b], ax = X[a], bx = X[b];
                if (max(ay, by) < yl || min(ay, by) > yh) continue;
                if (ay == by) { xl = min({xl, ax, bx}); xh = max({xh, ax, bx}); continue; }
                double ta = (max(yl, min(ay, by)) - ay) / (by - ay), tb = (min(yh, max(ay, by)) - ay) / (by - ay);
                double xa = ax + (bx - ax) * ta, xb = ax + (bx - ax) * tb;
                xl = min({xl, xa, xb}); xh = max({xh, xa, xb});
            }
            if (k == 1) { xl = min(xl, X[poly[0]]); xh = max(xh, X[poly[0]]); }
            if (xl > xh) continue;
            int cx0 = cx_(xl - tol * 2), cx1 = cx_(xh + tol * 2);
            for (int gx = cx0; gx <= cx1; ++gx) {
                int c = gy * GX + gx;
                for (int q = cellStart[c]; q < cellStart[c + 1]; ++q) f(cellPts[q]);
            }
        }
    }
    void bboxOf(const vector<int>& h, double& x0, double& y0, double& x1, double& y1) const {
        x0 = y0 = 1e300; x1 = y1 = -1e300;
        for (int p : h) { x0 = min(x0, X[p]); y0 = min(y0, Y[p]); x1 = max(x1, X[p]); y1 = max(y1, Y[p]); }
    }
    int offPt(int o) const { return n + o; }

    // ---- objective pieces
    double rangePen() const {  // alpha*(maxT-minT)
        int mx = INT_MIN, mn = INT_MAX;
        for (int o = 0; o < m; ++o) if (cnt[o] > 0) { mx = max(mx, T[o]); mn = min(mn, T[o]); }
        return mx == INT_MIN ? 0.0 : I.alpha * (mx - mn);
    }
    int cntRange() const {
        int mx = INT_MIN, mn = INT_MAX;
        for (int o = 0; o < m; ++o) if (cnt[o] > 0) { mx = max(mx, cnt[o]); mn = min(mn, cnt[o]); }
        return mx == INT_MIN ? 0 : mx - mn;
    }
    double objective() const { return profit - costSum - rangePen(); }
    // evaluates count range and task range after moving i from a to b (either may be -1)
    void afterRanges(int a, int b, int ti, int& cr, int& tr) const {
        int cmx = INT_MIN, cmn = INT_MAX, tmx = INT_MIN, tmn = INT_MAX;
        for (int o = 0; o < m; ++o) {
            int c = cnt[o], t = T[o];
            if (o == a) { c--; t -= ti; }
            if (o == b) { c++; t += ti; }
            if (c > 0) { cmx = max(cmx, c); cmn = min(cmn, c); tmx = max(tmx, t); tmn = min(tmn, t); }
        }
        cr = cmx == INT_MIN ? 0 : cmx - cmn; tr = tmx == INT_MIN ? 0 : tmx - tmn;
    }
    double siteVal(int o, int i) const { return o < 0 ? 0.0 : I.rew[i] - I.d(o, i); }

    // ---- logging helpers
    void setOwner(int p, int o) { if (logging) lg.push_back({0, p, owner[p], 0}); owner[p] = o; }
    void setHull(int o, vector<int>&& h) {
        if (logging) hullLog.push_back({o, hull[o]}), lg.push_back({3, o, (int)hullLog.size() - 1, 0});
        for (int p : hull[o]) isVert[p] = 0;
        hull[o] = std::move(h);
        for (int p : hull[o]) isVert[p] = 1;
        if (!hull[o].empty()) bboxOf(hull[o], hbx0[o], hby0[o], hbx1[o], hby1[o]);
    }
    void wTake(int w, int o) {  // move worker w to office o (or -1 = free)
        int old = workerOf[w];
        if (logging) lg.push_back({2, w, old, 0});
        if (old >= 0) {
            auto& v = offWorkers[old]; v.erase(find(v.begin(), v.end(), w));
            for (int s : I.workers[w]) have[(size_t)old * NS + s]--;
        } else {
            int pos = freePos[w]; int last = freeWorkers.back(); freeWorkers[pos] = last; freePos[last] = pos; freeWorkers.pop_back(); freePos[w] = -1;
        }
        workerOf[w] = o;
        if (o >= 0) { offWorkers[o].push_back(w); for (int s : I.workers[w]) have[(size_t)o * NS + s]++; }
        else { freePos[w] = freeWorkers.size(); freeWorkers.push_back(w); }
    }
    void setAssign(int i, int b) {
        int a = assign[i];
        if (logging) lg.push_back({1, i, a, 0});
        if (a >= 0) {
            profit -= siteVal(a, i); cnt[a]--; T[a] -= I.ntask[i];
            if (cnt[a] == 0) costSum -= I.cost[a];
            for (auto& kv : I.sk[i]) need[(size_t)a * NS + kv.first] -= kv.second;
        }
        if (b >= 0) {
            profit += siteVal(b, i); if (cnt[b] == 0) costSum += I.cost[b]; cnt[b]++; T[b] += I.ntask[i];
            for (auto& kv : I.sk[i]) need[(size_t)b * NS + kv.first] += kv.second;
        }
        assign[i] = b;
    }
    void rollback(size_t mark, size_t hmark) {
        bool lgs = logging; logging = false;
        while (lg.size() > mark) {
            LogE e = lg.back(); lg.pop_back();
            if (e.type == 0) owner[e.a] = e.b;
            else if (e.type == 1) setAssign(e.a, e.b);
            else if (e.type == 2) wTake(e.a, e.b);
            else { auto h = hullLog[e.b].second; setHull(e.a, std::move(h)); }
        }
        hullLog.resize(hmark);
        logging = lgs;
    }

    // release workers of office a that are not needed
    void releaseWorkers(int a) {
        auto ws = offWorkers[a];
        sort(ws.begin(), ws.end(), [&](int u, int v) { return I.workers[u].size() > I.workers[v].size(); });
        for (int w : ws) {
            bool redundant = true;
            for (int s : I.workers[w]) if (need[(size_t)a * NS + s] > 0 && have[(size_t)a * NS + s] < 2) { redundant = false; break; }
            if (redundant) wTake(w, -1);
        }
    }
    // grab free workers so office b covers the skills of site i; false if impossible (no change then)
    bool grabWorkers(int b, int i) {
        vector<int> miss;
        for (auto& kv : I.sk[i]) if (have[(size_t)b * NS + kv.first] == 0) miss.push_back(kv.first);
        if (miss.empty()) return true;
        vector<int> took;
        while (!miss.empty()) {
            int best = -1; double bs = -1e18;
            for (int w : freeWorkers) {
                int c = 0; for (int s : miss) if (binary_search(I.workers[w].begin(), I.workers[w].end(), s)) c++;
                if (!c) continue;
                double sc = c * 1000.0 - I.workers[w].size();
                if (sc > bs) { bs = sc; best = w; }
            }
            if (best < 0) { for (int w : took) wTake(w, -1); return false; }
            wTake(best, b); took.push_back(best);
            vector<int> nm; for (int s : miss) if (!binary_search(I.workers[best].begin(), I.workers[best].end(), s)) nm.push_back(s);
            miss.swap(nm);
        }
        return true;
    }
    // quick worker feasibility pre-check (exact for single skill workers, optimistic otherwise)
    bool workersMaybe(int b, int i) const {
        for (auto& kv : I.sk[i]) if (have[(size_t)b * NS + kv.first] == 0) {
            bool ok = false;
            for (int w : freeWorkers) if (binary_search(I.workers[w].begin(), I.workers[w].end(), kv.first)) { ok = true; break; }
            if (!ok) {
                int a = assign[i];
                if (a < 0) return false;
                // a may release a worker with this skill if i is the only one needing it there
                if (need[(size_t)a * NS + kv.first] == kv.second) ok = true;
                if (!ok) return false;
            }
        }
        return true;
    }

    // ---- the core: geometric move with ownership update. Returns false (state unchanged) if infeasible.
    vector<int> tmpL; vector<char> inL; vector<int> tmpAdd;
    bool moveSite(int i, int b) {
        int a = assign[i];
        if (a == b) return true;
        if (b >= 0 && skillUseless[i]) return false;
        if ((int)inL.size() != P) inL.assign(P, 0);
        vector<int> newHa; bool aCh = false;
        tmpL.clear();
        if (a >= 0) {
            if (cnt[a] == 1) {
                aCh = true;
                scanPoly(hull[a], [&](int q) { if (owner[q] == a) tmpL.push_back(q); });
            } else if (isVert[i]) {
                aCh = true;
                const auto& h = hull[a]; int k = h.size(); int pos = find(h.begin(), h.end(), i) - h.begin();
                vector<int> reg;  // region polygon around i
                if (k <= 3) reg = h; else reg = {h[(pos + k - 1) % k], i, h[(pos + 1) % k]};
                vector<int> regH = hullOf(reg);
                vector<int> pts; for (int p : h) if (p != i) pts.push_back(p);
                vector<int> inReg;
                scanPoly(regH, [&](int q) {
                    if (owner[q] != a || q == i) return;
                    if (!coveredH(regH, X[q], Y[q])) return;
                    inReg.push_back(q);
                    if ((q < n && assign[q] == a) || q == offPt(a)) pts.push_back(q);
                });
                newHa = hullOf(pts);
                if (!coveredH(newHa, X[i], Y[i])) tmpL.push_back(i);
                for (int q : inReg) if (!coveredH(newHa, X[q], Y[q])) tmpL.push_back(q);
                sort(tmpL.begin(), tmpL.end()); tmpL.erase(unique(tmpL.begin(), tmpL.end()), tmpL.end());
            }
        }
        // a's ownership of i must vanish if i goes to another office
        if (b >= 0 && owner[i] == a && a >= 0) {
            bool leaves = false; for (int q : tmpL) if (q == i) leaves = true;
            if (!leaves) return false;
        }
        for (int q : tmpL) inL[q] = 1;
        vector<int> newHb; bool bCh = false; tmpAdd.clear();
        bool ok = true;
        if (b >= 0) {
            if (cnt[b] > 0 && owner[i] == b) { /* already inside b's hull */ }
            else {
                bCh = true;
                vector<int> pts = cnt[b] > 0 ? hull[b] : vector<int>{offPt(b)};
                pts.push_back(i);
                newHb = hullOf(pts);
                int k = newHb.size();
                int pos = find(newHb.begin(), newHb.end(), i) - newHb.begin();
                vector<int> reg;
                bool triMode = !(k <= 3 || pos == k || cnt[b] == 0);
                if (!triMode) reg = newHb; else reg = {newHb[(pos + k - 1) % k], i, newHb[(pos + 1) % k]};
                double L0 = 0, L1 = 0, L2 = 0;
                if (triMode) {
                    L0 = tol * sqrt(sq(X[reg[1]] - X[reg[0]]) + sq(Y[reg[1]] - Y[reg[0]]));
                    L1 = tol * sqrt(sq(X[reg[2]] - X[reg[1]]) + sq(Y[reg[2]] - Y[reg[1]]));
                    L2 = tol * sqrt(sq(X[reg[0]] - X[reg[2]]) + sq(Y[reg[0]] - Y[reg[2]]));
                }
                scanPoly(reg, [&](int q) {
                    if (!ok) return;
                    int ow = owner[q];
                    if (ow == b && cnt[b] > 0) return;
                    if (triMode) {
                        if (crossP(reg[0], reg[1], X[q], Y[q]) < -L0 || crossP(reg[1], reg[2], X[q], Y[q]) < -L1 || crossP(reg[2], reg[0], X[q], Y[q]) < -L2) return;
                    } else if (!coveredH(newHb, X[q], Y[q])) return;
                    if (ow == -1 || ow == b || (ow == a && inL[q])) tmpAdd.push_back(q);
                    else ok = false;
                });
            }
        }
        for (int q : tmpL) inL[q] = 0;
        if (!ok) return false;
        // workers
        size_t wm = lg.size(), hm = hullLog.size();
        bool lgs = logging; logging = true;
        setAssign(i, b);
        if (a >= 0) releaseWorkers(a);
        if (b >= 0 && !grabWorkers(b, i)) { rollback(wm, hm); logging = lgs; return false; }
        if (!lgs) { lg.resize(wm); hullLog.resize(hm); }
        logging = lgs;
        // commit geometry
        if (a >= 0 && aCh) {
            for (int q : tmpL) setOwner(q, -1);
            setHull(a, cnt[a] == 0 ? vector<int>{} : std::move(newHa));
        }
        if (b >= 0 && bCh) {
            for (int q : tmpAdd) setOwner(q, b);
            setHull(b, std::move(newHb));
        }
        return true;
    }

    // ---- full validation (independent of incremental structures)
    string validateFull(const vector<int>& as, const vector<int>& wo, double* objOut) const {
        vector<vector<int>> mem(m);
        for (int i = 0; i < n; ++i) if (as[i] >= 0) mem[as[i]].push_back(i);
        vector<int> cov(P, 0);
        int cmx = INT_MIN, cmn = INT_MAX, tmx = INT_MIN, tmn = INT_MAX; double obj = 0;
        vector<vector<char>> hs(m, vector<char>(NS, 0));
        for (int w = 0; w < W; ++w) if (wo[w] >= 0) for (int s : I.workers[w]) hs[wo[w]][s] = 1;
        for (int o = 0; o < m; ++o) if (!mem[o].empty()) {
            if ((int)mem[o].size() > I.maxSize[o]) return "capacity";
            int t = 0;
            for (int i : mem[o]) { t += I.ntask[i]; obj += I.rew[i] - I.d(o, i); for (auto& kv : I.sk[i]) if (!hs[o][kv.first]) return "skills"; }
            obj -= I.cost[o];
            cmx = max(cmx, (int)mem[o].size()); cmn = min(cmn, (int)mem[o].size()); tmx = max(tmx, t); tmn = min(tmn, t);
            vector<int> pts = mem[o]; pts.push_back(offPt(o));
            auto h = hullOf(pts);
            double x0, y0, x1, y1; bboxOf(h, x0, y0, x1, y1);
            scanBox(x0, y0, x1, y1, [&](int q) { if (coveredH(h, X[q], Y[q])) cov[q]++; });
        }
        for (int w = 0; w < W; ++w) if (wo[w] >= 0 && mem[wo[w]].empty()) return "worker at closed office";
        if (cmx != INT_MIN && cmx - cmn > I.A) return "balance";
        for (int q = 0; q < P; ++q) if (cov[q] > 1) return "hull";
        if (tmx != INT_MIN) obj -= I.alpha * (tmx - tmn);
        if (objOut) *objOut = obj;
        return "";
    }

    // ---- remove hull-vertex sites from the biggest offices until counts are balanced
    bool fixCounts(int limit = INT_MAX) {
        for (int guard = 0; guard < 4 * n + 10; ++guard) {
            int mx = INT_MIN, mn = INT_MAX, om = -1, excess = 0;
            for (int o = 0; o < m; ++o) if (cnt[o] > 0) { if (cnt[o] > mx) { mx = cnt[o]; om = o; } mn = min(mn, cnt[o]); }
            if (om < 0 || mx - mn <= I.A) return true;
            for (int o = 0; o < m; ++o) if (cnt[o] > mn + I.A) excess += cnt[o] - mn - I.A;
            if (excess > limit) return false;
            limit = INT_MAX;
            // remove worst vertex site of om
            int bi = -1; double bv = 1e300;
            for (int p : hull[om]) if (p < n && assign[p] == om) { double v = siteVal(om, p); if (v < bv) { bv = v; bi = p; } }
            if (bi < 0) {  // no site vertex (degenerate) -> remove any site
                for (int i = 0; i < n; ++i) if (assign[i] == om) { bi = i; break; }
            }
            moveSite(bi, -1);
        }
        return true;
    }

    // ---- facility-location style choice of open sets (geometry ignored)
    vector<int> openOrder; vector<double> openGain;
    int kNatural() { if (openOrder.empty()) chooseOpen(1); int k = 0; while (k < (int)openGain.size() && openGain[k] > 0) ++k; return max(1, k); }
    vector<char> chooseOpen(int k) {
        if (openOrder.empty()) { auto all = chooseOpenRaw(m); (void)all; }
        vector<char> op(m, 0);
        for (int t = 0; t < k && t < (int)openOrder.size(); ++t) op[openOrder[t]] = 1;
        return op;
    }
    vector<char> chooseOpenRaw(int k) {
        // greedy: start empty, add office with best gain of sum max(0, r-d) - cost (with capacity cut), up to k offices
        vector<char> op(m, 0);
        vector<double> best(n, 0.0);
        for (int it = 0; it < k; ++it) {
            if (late()) break;
            int bo = -1; double bg = -1e300;
            for (int o = 0; o < m; ++o) if (!op[o] && I.maxSize[o] > 0) {
                vector<double> gains;
                for (int i = 0; i < n; ++i) { double v = I.rew[i] - I.d(o, i); if (v > best[i]) gains.push_back(v - best[i]); }
                if ((int)gains.size() > I.maxSize[o]) { nth_element(gains.begin(), gains.begin() + I.maxSize[o], gains.end(), greater<double>()); gains.resize(I.maxSize[o]); }
                double g = -I.cost[o]; for (double x : gains) g += x;
                g += rng.nextDouble() * 1e-9;
                if (g > bg) { bg = g; bo = o; }
            }
            if (bo < 0) break;
            op[bo] = 1; openOrder.push_back(bo); openGain.push_back(bg);
            for (int i = 0; i < n; ++i) best[i] = max(best[i], I.rew[i] - I.d(bo, i));
        }
        return op;
    }

    // ---- SA
    struct Snapshot { vector<int> assign, workerOf; double obj = -1e300; };
    Snapshot best;
    void snapshot() { best.assign = assign; best.workerOf = workerOf; best.obj = objective(); }
    void loadState(const vector<int>& as, const vector<int>& wo) {
        // rebuild incremental state from scratch
        reset();
        vector<vector<int>> mem(m);
        for (int i = 0; i < n; ++i) if (as[i] >= 0 && as[i] < m) mem[as[i]].push_back(i);
        for (int o = 0; o < m; ++o) {
            vector<int>& pts = mem[o];
            if (pts.empty()) continue;
            for (int i : pts) setAssign(i, o);
            pts.push_back(offPt(o));
            setHull(o, hullOf(pts));
            double x0, y0, x1, y1; bboxOf(hull[o], x0, y0, x1, y1);
            scanBox(x0, y0, x1, y1, [&](int q) { if (coveredH(hull[o], X[q], Y[q])) owner[q] = o; });
        }
        for (int w = 0; w < W; ++w) if (wo[w] >= 0) wTake(w, wo[w]);
    }

    double scale = 1;
    void computeScale() {
        vector<double> v;
        for (int i = 0; i < n; ++i) { double b = -1e300; for (int o : nearOff[i]) b = max(b, siteVal(o, i)); if (b > 0) v.push_back(b); }
        if (v.empty()) { scale = 1; return; }
        sort(v.begin(), v.end()); scale = v[v.size() / 2];
        if (scale <= 0) scale = 1;
    }

    vector<vector<int>> byDistCache;
    const vector<int>& byDist(int o) {
        if (byDistCache.empty()) byDistCache.resize(m);
        auto& v = byDistCache[o];
        if (v.empty() && n > 0) { v.resize(n); iota(v.begin(), v.end(), 0); sort(v.begin(), v.end(), [&](int a, int b) { return I.d(o, a) < I.d(o, b); }); }
        return v;
    }
    vector<vector<int>> byEucCache;
    const vector<int>& byEuc(int o) {
        if (byEucCache.empty()) byEucCache.resize(m);
        auto& v = byEucCache[o];
        if (v.empty() && n > 0) { v.resize(n); iota(v.begin(), v.end(), 0); double ox = X[offPt(o)], oy = Y[offPt(o)]; sort(v.begin(), v.end(), [&](int a, int b) { return sq(X[a] - ox) + sq(Y[a] - oy) < sq(X[b] - ox) + sq(Y[b] - oy); }); }
        return v;
    }
    // big perturbation of the office set / a large region (no acceptance test)
    void perturb(int kind) {
        vector<int> openL, closedL;
        for (int o = 0; o < m; ++o) { if (cnt[o] > 0) openL.push_back(o); else if (I.maxSize[o] > 0) closedL.push_back(o); }
        vector<char> forced(m, 0);
        vector<int> removed;
        if (kind == 3 || (kind == 0 && openL.size() <= 1) || (kind != 3 && closedL.empty() && kind != 0)) kind = 3;
        if (kind == 0 || kind == 2) {  // close
            if (openL.size() > 1) {
                int a = openL[rng.nextInt(openL.size())];
                for (int s2 = 0; s2 < n; ++s2) if (assign[s2] == a) removed.push_back(s2);
                for (int s2 : removed) moveSite(s2, -1);
            }
        }
        if ((kind == 1 || kind == 2) && !closedL.empty()) {  // open
            int b = closedL[rng.nextInt(closedL.size())];
            forced[b] = 1;
            int Kc = max(5, n / max(1, (int)openL.size() + 1)); Kc = min(Kc, I.maxSize[b]);
            const auto& v = byDist(b);
            for (int t = 0; t < (int)v.size() && t < Kc; ++t) { int s2 = v[t]; if (assign[s2] >= 0) moveSite(s2, -1); removed.push_back(s2); }
            if (owner[offPt(b)] >= 0) {
                int o2 = owner[offPt(b)];
                for (int g = 0; g < 200 && owner[offPt(b)] == o2 && cnt[o2] > 0; ++g) {
                    int bi = -1; double bd = 1e300;
                    for (int p : hull[o2]) if (p < n && assign[p] == o2) { double dd = sq(X[p] - X[offPt(b)]) + sq(Y[p] - Y[offPt(b)]); if (dd < bd) { bd = dd; bi = p; } }
                    if (bi < 0) break;
                    moveSite(bi, -1); removed.push_back(bi);
                }
            }
        }
        if (kind == 3) {  // region ruin ~15% of the sites around a random site (Euclidean)
            int c = rng.nextInt(n);
            vector<pair<double,int>> v; v.reserve(n);
            for (int s2 = 0; s2 < n; ++s2) v.push_back({sq(X[s2] - X[c]) + sq(Y[s2] - Y[c]), s2});
            int K = max(5, n * (5 + rng.nextInt(20)) / 100);
            nth_element(v.begin(), v.begin() + min(K, n - 1), v.end());
            for (int t = 0; t < K && t < n; ++t) { int s2 = v[t].second; if (assign[s2] >= 0) moveSite(s2, -1); removed.push_back(s2); }
        }
        int mt = maxTry; maxTry = 8;
        recreate(removed, &forced);
        maxTry = mt;
        fixCounts();
    }
    long long iters = 0, accepted = 0, geoFail = 0, geoOk = 0;
    // ---- search penalty: w*alpha*[(1-beta)*(maxT-minT) + beta*sum|T_o - median|]
    double pw = 1, pbeta = 0.3; int pdead = 0;
    vector<int> scratch;
    double penFrom(int a, int b, int ti, int& cr) {
        scratch.clear();
        int cmx = INT_MIN, cmn = INT_MAX, tmx = INT_MIN, tmn = INT_MAX;
        for (int o = 0; o < m; ++o) {
            int c = cnt[o], t = T[o];
            if (o == a) { c--; t -= ti; }
            if (o == b) { c++; t += ti; }
            if (c > 0) { cmx = max(cmx, c); cmn = min(cmn, c); tmx = max(tmx, t); tmn = min(tmn, t); scratch.push_back(t); }
        }
        cr = cmx == INT_MIN ? 0 : cmx - cmn;
        if (scratch.empty() || I.alpha == 0 || pw == 0) return 0;
        double p = (1 - pbeta) * (tmx - tmn);
        if (pbeta > 0) {
            size_t h = scratch.size() / 2;
            nth_element(scratch.begin(), scratch.begin() + h, scratch.end());
            int med = scratch[h]; long long sd = 0;
            for (int t : scratch) sd += max(0, abs(t - med) - pdead);
            p += pbeta * sd;
        }
        return pw * I.alpha * p;
    }
    double penNow() { int cr; return penFrom(-1, -1, 0, cr); }
    double searchObj() { return profit - costSum - penNow(); }
    int medianT() {
        scratch.clear(); for (int o = 0; o < m; ++o) if (cnt[o] > 0) scratch.push_back(T[o]);
        if (scratch.empty()) return 0;
        size_t h = scratch.size() / 2; nth_element(scratch.begin(), scratch.begin() + h, scratch.end()); return scratch[h];
    }

    // greedy insertion of a list of sites; forced offices count as open (no opening cost)
    int recreateL = -1; int maxTry = 4; vector<char> memo;
    void recreate(vector<int> sites, const vector<char>* forced, bool requirePositive = true) {
        int L = recreateL >= 0 ? recreateL : medianT();
        double lam = pw * I.alpha * pbeta;
        vector<pair<double,int>> ord;
        for (int i : sites) {
            if (assign[i] >= 0) continue;
            double bv = -1e300;
            for (int o : nearOff[i]) bv = max(bv, siteVal(o, i));
            ord.push_back({-bv, i});
        }
        sort(ord.begin(), ord.end());
        for (int pass = 0; pass < 2; ++pass)
        for (auto& pr : ord) {
            int i = pr.second;
            if (assign[i] >= 0) continue;
            int cand[32]; double cv[32]; int nc = 0;
            auto addc = [&](int o) {
                if (o < 0) return; for (int k = 0; k < nc; ++k) if (cand[k] == o) return;
                if (nc >= 32) return;
                bool isOpen = cnt[o] > 0 || (forced && (*forced)[o]);
                if (!isOpen || cnt[o] >= I.maxSize[o]) return;
                int t = I.ntask[i];
                double v = siteVal(o, i) - lam * (abs(T[o] + t - L) - abs(T[o] - L));
                cand[nc] = o; cv[nc] = v; nc++;
            };
            for (int o : nearOff[i]) addc(o);
            for (int j : knn[i]) addc(assign[j]);
            if (owner[i] >= 0) addc(owner[i]);
            int idx[32]; for (int k = 0; k < nc; ++k) idx[k] = k;
            sort(idx, idx + nc, [&](int u, int v) { return cv[u] > cv[v]; });
            for (int kk = 0; kk < nc && kk < maxTry; ++kk) {
                int o = cand[idx[kk]];
                if (requirePositive && cv[idx[kk]] <= 0) break;
                if (owner[i] >= 0 && owner[i] != o) continue;
                if (moveSite(i, o)) break;
            }
        }
    }

    void buildFrom(const vector<char>& op) {
        reset();
        vector<int> all(n); iota(all.begin(), all.end(), 0);
        int k = 0; for (char c : op) k += c;
        long long tt = 0; for (int i = 0; i < n; ++i) { double bv = -1e300; for (int o : nearOff[i]) bv = max(bv, siteVal(o, i)); if (bv > 0) tt += I.ntask[i]; }
        recreateL = (int)(tt / max(1, k));
        recreate(all, &op);
        recreateL = -1;
        fixCounts();
    }

    // ---- balanced region growing: open offices take turns grabbing their nearest feasible site while T_o + t <= L
    void growBuild(const vector<char>& op, int L, int mode = 0, int Lcnt = INT_MAX) {
        reset();
        vector<int> offs; for (int o = 0; o < m; ++o) if (op[o] && I.maxSize[o] > 0 && owner[offPt(o)] < 0) offs.push_back(o);
        int k = offs.size(); if (!k) return;
        vector<vector<int>> order(k); vector<size_t> ptr(k, 0);
        for (int t = 0; t < k; ++t) {
            int o = offs[t];
            const auto& src = mode == 0 ? byDist(o) : byEuc(o);
            for (int i : src) if (siteVal(o, i) > 0 && !skillUseless[i]) order[t].push_back(i);
        }
        vector<char> done(k, 0);
        // priority: office with the fewest tasks (then fewest sites) grows next
        long long tries = 0;  // moveSite attempts (failed ones too: each scans the zone polygon)
        bool stop = false;
        for (int guard = 0; guard < 2 * n + 10 && !stop; ++guard) {
            if ((guard & 63) == 0 && late()) break;
            int bt = -1;
            for (int t = 0; t < k; ++t) if (!done[t]) {
                int o = offs[t];
                if (bt < 0 || T[o] < T[offs[bt]] || (T[o] == T[offs[bt]] && cnt[o] < cnt[offs[bt]])) bt = t;
            }
            if (bt < 0) break;
            int o = offs[bt];
            bool grew = false;
            while (ptr[bt] < order[bt].size()) {
                int i = order[bt][ptr[bt]++];
                if (assign[i] >= 0) continue;
                if (T[o] + I.ntask[i] > L || cnt[o] >= min(I.maxSize[o], Lcnt)) continue;
                if (owner[i] >= 0 && owner[i] != o) continue;
                if ((++tries & 31) == 0 && late()) {  // with n ~ 1e6 the failed attempts alone took minutes
                    stop = true;
                    break;
                }
                if (moveSite(i, o)) { grew = true; break; }
            }
            if (stop) break;
            if (!grew) done[bt] = 1;
        }
        fixCounts();
    }

    // ---- make every open office carry exactly L tasks (trim / fill / close), logged by caller
    // remove a subset of o's task sites whose task sum is exactly e (or the smallest sum >= e), minimal value loss
    void trimExact(int o, int e) {
        if (e <= 0) return;
        vector<int> it; for (int i = 0; i < n; ++i) if (assign[i] == o && I.ntask[i] > 0) it.push_back(i);
        int tot = 0; for (int i : it) tot += I.ntask[i];
        if (tot <= e) { for (int i : it) moveSite(i, -1); return; }
        int cap = min(tot, e + 64);
        if ((double)it.size() * (cap + 1) > 2e7) {  // too big for the DP: peel the cheapest tasks greedily
            sort(it.begin(), it.end(), [&](int u, int v) { return siteVal(o, u) / I.ntask[u] < siteVal(o, v) / I.ntask[v]; });
            int rem = e;
            for (int i : it) { if (rem <= 0) break; moveSite(i, -1); rem -= I.ntask[i]; }
            return;
        }
        const double INF = 1e300;
        vector<double> dp(cap + 1, INF); dp[0] = 0;
        vector<vector<char>> take(it.size(), vector<char>(cap + 1, 0));
        for (size_t k = 0; k < it.size(); ++k) {
            int w = I.ntask[it[k]]; double v = siteVal(o, it[k]);
            for (int c = cap; c >= w; --c) if (dp[c - w] < INF && dp[c - w] + v < dp[c]) { dp[c] = dp[c - w] + v; take[k][c] = 1; }
        }
        int c = -1; for (int x = e; x <= cap; ++x) if (dp[x] < INF) { c = x; break; }
        if (c < 0) { for (int i : it) moveSite(i, -1); return; }
        vector<int> rem;
        for (int k = (int)it.size() - 1; k >= 0 && c > 0; --k) if (take[k][c]) { rem.push_back(it[k]); c -= I.ntask[it[k]]; }
        for (int i : rem) moveSite(i, -1);
    }
    void levelize(int L) {
        for (int o = 0; o < m; ++o) if (cnt[o] > 0 && T[o] > L && !late()) trimExact(o, T[o] - L);
        // fill offices below L and add free zero-task sites
        vector<pair<double,int>> cand;
        for (int o = 0; o < m; ++o) {
            if (cnt[o] == 0 || late()) continue;
            cand.clear();
            if (memo.size() != (size_t)n) memo.assign(n, 0);
            vector<int> touched;
            for (int s2 = 0; s2 < n; ++s2) if (assign[s2] == o) for (int i : knn[s2]) if (!memo[i] && assign[i] < 0 && (owner[i] == -1 || owner[i] == o)) { memo[i] = 1; touched.push_back(i); }
            for (int i = 0; i < n; ++i) if (!memo[i] && assign[i] < 0 && owner[i] == o) { memo[i] = 1; touched.push_back(i); }
            for (int i : touched) {
                memo[i] = 0;
                double v = siteVal(o, i);
                if (I.ntask[i] == 0 ? v > 0 : (I.ntask[i] <= L - T[o] && v > 0)) cand.push_back({-v, i});
            }
            sort(cand.begin(), cand.end());
            int tries = 0;
            for (auto& c : cand) {
                if (++tries > 64) break;
                int i = c.second;
                if (assign[i] >= 0 || cnt[o] >= I.maxSize[o]) continue;
                if (I.ntask[i] > 0 && T[o] + I.ntask[i] > L) continue;
                if (I.ntask[i] == 0 && -c.first <= 0) continue;
                if (I.ntask[i] > 0 && T[o] >= L) continue;
                moveSite(i, o);
            }
        }
        fixCounts();
        // close offices that stay below L if that helps
        for (int o = 0; o < m; ++o) {
            if (cnt[o] == 0 || T[o] >= L) continue;
            double before = objective();
            size_t mk = lg.size(), hm = hullLog.size();
            vector<int> mem; for (int i = 0; i < n; ++i) if (assign[i] == o) mem.push_back(i);
            for (int i : mem) moveSite(i, -1);
            fixCounts();
            if (objective() <= before) rollback(mk, hm);
        }
    }
    // try several levels, keep the best (true objective); returns objective
    double bestLevelize() {
        if (I.alpha <= 0) return objective();
        vector<int> Ls;
        for (int o = 0; o < m; ++o) if (cnt[o] > 0) Ls.push_back(T[o]);
        if (Ls.empty()) return objective();
        sort(Ls.begin(), Ls.end());
        int med = Ls[Ls.size() / 2];
        for (int d = -3; d <= 3; ++d) Ls.push_back(med + d);
        sort(Ls.begin(), Ls.end()); Ls.erase(unique(Ls.begin(), Ls.end()), Ls.end());
        if (Ls.size() > 24) { vector<int> t; for (size_t k = 0; k < Ls.size(); k += (Ls.size() + 23) / 24) t.push_back(Ls[k]); Ls = t; }
        bool lgs = logging; logging = true;
        size_t mk = lg.size(), hm = hullLog.size();
        double bo = objective(); int bL = -1;
        for (int L : Ls) {
            if (L <= 0) continue;
            if (late()) break;
            levelize(L);
            double v = objective();
            if (v > bo + 1e-9) { bo = v; bL = L; }
            rollback(mk, hm);
        }
        if (bL >= 0) levelize(bL);
        logging = lgs;
        if (!lgs) { lg.clear(); hullLog.clear(); }
        return objective();
    }

    double trueObj() const { return objective(); }
    void anneal(double tEnd, double T0, double T1, double w0 = 1, double w1 = 1, double beta = 0.3) {
        double tStart = elapsed();
        double dur = max(1e-3, tEnd - tStart);
        double temp = T0;
        pbeta = beta; pw = w0;
        double penCur = penNow();
        if (best.assign.empty() || trueObj() > best.obj) snapshot();
        vector<int> openList;
        bool lastBig = false;
        for (long long it = 0; ; ++it) {
            if ((it & 255) == 0 || lastBig) {
                lastBig = false;
                double t = elapsed();
                if (t >= tEnd) break;
                double fr = (t - tStart) / dur;
                temp = T0 * pow(T1 / T0, fr);
                double nw = fr < 0.7 ? w0 + (w1 - w0) * fr / 0.7 : w1;
                if (nw != pw) { pw = nw; }
                penCur = penNow();
            }
            iters++;
            int r = rng.nextInt(1000);
            if (r >= 960 && n > 2000 && rng.nextInt(n) >= 2000) r = rng.nextInt(900);
            bool changed = false;
            if (r < 900) {
                int i = rng.nextInt(n);
                int a = assign[i];
                int b;
                int rr = rng.nextInt(10);
                if (rr < 6) b = assign[knn[i].empty() ? i : knn[i][rng.nextInt(knn[i].size())]];
                else if (rr < 8) b = nearOff[i].empty() ? -1 : nearOff[i][rng.nextInt(nearOff[i].size())];
                else b = -1;
                if (b == a) continue;
                if (a >= 0 && b >= 0 && !isVert[i]) continue;
                if (b >= 0) {
                    if (cnt[b] >= I.maxSize[b]) continue;
                    if (owner[i] >= 0 && owner[i] != b && owner[i] != a) continue;
                    if (!workersMaybe(b, i)) continue;
                }
                int cr; double np = penFrom(a, b, I.ntask[i], cr);
                if (cr > I.A) continue;
                double dv = siteVal(b, i) - siteVal(a, i);
                if (a >= 0 && cnt[a] == 1) dv += I.cost[a];
                if (b >= 0 && cnt[b] == 0) dv -= I.cost[b];
                double delta = dv - (np - penCur);
                if (delta < 0 && rng.nextDouble() >= exp(delta / temp)) continue;
                if (!moveSite(i, b)) { geoFail++; continue; }
                geoOk++;
                accepted++; penCur = np; changed = true;
            } else if (r < 930) {
                // replace: i (in a) leaves, an unassigned neighbour j joins a
                int i = rng.nextInt(n); int a = assign[i];
                if (a < 0 || knn[i].empty() || !isVert[i]) continue;
                int j = knn[i][rng.nextInt(knn[i].size())];
                if (assign[j] >= 0 || (owner[j] >= 0 && owner[j] != a)) continue;
                double before = profit - costSum - penCur;
                size_t mk = lg.size(), hm = hullLog.size(); logging = true;
                bool ok = moveSite(i, -1) && moveSite(j, a);
                int cr = 0; double np = 0;
                if (ok) { np = penFrom(-1, -1, 0, cr); if (cr > I.A) ok = false; }
                double delta = ok ? (profit - costSum - np) - before : 0;
                if (!ok || (delta < 0 && rng.nextDouble() >= exp(delta / temp))) { rollback(mk, hm); logging = false; lg.clear(); hullLog.clear(); continue; }
                logging = false; lg.clear(); hullLog.clear();
                penCur = np; accepted++; changed = true;
            } else if (r < 960) {
                int i = rng.nextInt(n); int a = assign[i];
                if (a < 0 || knn[i].empty()) continue;
                int j = knn[i][rng.nextInt(knn[i].size())]; int b = assign[j];
                if (b < 0 || b == a) continue;
                double before = profit - costSum - penCur;
                size_t mk = lg.size(), hm = hullLog.size(); logging = true;
                bool ok = moveSite(i, b) && moveSite(j, a);
                if (!ok) { rollback(mk, hm); ok = moveSite(j, a) && moveSite(i, b); }
                int cr2 = 0; double np = ok ? penFrom(-1, -1, 0, cr2) : 0;
                if (ok && cr2 > I.A) ok = false;
                double delta = ok ? (profit - costSum - np) - before : 0;
                if (!ok || (delta < 0 && rng.nextDouble() >= exp(delta / temp))) { rollback(mk, hm); logging = false; lg.clear(); hullLog.clear(); continue; }
                logging = false; lg.clear(); hullLog.clear();
                penCur = np; accepted++; changed = true;
            } else {
                lastBig = true;
                double before = profit - costSum - penCur;
                size_t mk = lg.size(), hm = hullLog.size(); logging = true;
                vector<char> forced(m, 0);
                vector<int> removed;
                int kind = rng.nextInt(12);
                bool skip = false;
                if (kind >= 10) {
                    // relabel: the zone of open office a moves to closed office b
                    openList.clear(); for (int o = 0; o < m; ++o) if (cnt[o] > 0) openList.push_back(o);
                    vector<int> closed; for (int o = 0; o < m; ++o) if (cnt[o] == 0 && I.maxSize[o] > 0) closed.push_back(o);
                    if (openList.empty() || closed.empty()) skip = true;
                    else {
                        int a = openList[rng.nextInt(openList.size())];
                        vector<int> Z; for (int s2 = 0; s2 < n; ++s2) if (assign[s2] == a) Z.push_back(s2);
                        vector<pair<double,int>> cb;
                        for (int o : closed) { double sd = 0; for (int s2 : Z) sd += I.d(o, s2); cb.push_back({sd - I.cost[a] + I.cost[o], o}); }
                        sort(cb.begin(), cb.end());
                        int b = cb[rng.nextInt(min((int)cb.size(), 3))].second;
                        for (int s2 : Z) moveSite(s2, -1);
                        sort(Z.begin(), Z.end(), [&](int u, int v) { return I.d(b, u) < I.d(b, v); });
                        if (owner[offPt(b)] < 0) for (int s2 : Z) if (cnt[b] < I.maxSize[b] && (owner[s2] < 0 || owner[s2] == b)) moveSite(s2, b);
                        removed = Z;
                    }
                } else if (kind < 6) {
                    int c = rng.nextInt(n);
                    int K = 3 + rng.nextInt(max(4, min(60, n / max(1, m))));
                    vector<int> q = {c}; set<int> seen = {c};
                    for (size_t h = 0; h < q.size() && (int)q.size() < K; ++h) for (int j : knn[q[h]]) if (!seen.count(j) && (int)q.size() < K) { seen.insert(j); q.push_back(j); }
                    for (int s : q) { if (assign[s] >= 0) moveSite(s, -1); removed.push_back(s); }
                    for (int s : q) for (int j : knn[s]) if (assign[j] < 0 && !seen.count(j)) { seen.insert(j); removed.push_back(j); }
                } else if (kind < 8) {
                    int c = rng.nextInt(n);
                    int b = nearOff[c].empty() ? -1 : nearOff[c][rng.nextInt(nearOff[c].size())];
                    if (b < 0 || cnt[b] > 0) skip = true;
                    else {
                        forced[b] = 1;
                        int opened = 0; for (int o = 0; o < m; ++o) opened += cnt[o] > 0;
                        // target: median task level if alpha matters, else a fair share of sites
                        int L = medianT();
                        int Kc = max(5, n / max(1, opened + 1));
                        Kc = min(Kc, I.maxSize[b]);
                        const auto& v = byDist(b);
                        int kk = min((int)v.size(), Kc * 2);
                        int tsum = 0, taken = 0;
                        for (int t = 0; t < kk; ++t) {
                            int s = v[t];
                            if (I.alpha > 0 && L > 0 && tsum >= L * 1.2 && taken >= 3) break;
                            if ((I.alpha == 0 || L == 0) && taken >= Kc * 1.3) break;
                            if (assign[s] >= 0) moveSite(s, -1);
                            removed.push_back(s); tsum += I.ntask[s]; taken++;
                        }
                        if (owner[offPt(b)] >= 0) {
                            int o2 = owner[offPt(b)];
                            for (int g = 0; g < 80 && owner[offPt(b)] == o2 && cnt[o2] > 0; ++g) {
                                int bi = -1; double bd = 1e300;
                                for (int p : hull[o2]) if (p < n && assign[p] == o2) { double dd = I.d(b, p); if (dd < bd) { bd = dd; bi = p; } }
                                if (bi < 0) break;
                                moveSite(bi, -1); removed.push_back(bi);
                            }
                        }
                    }
                } else if (kind == 8 && W > 0) {
                    // skill drop: office a gives up skill s (its s-sites leave, workers are freed), then recreate
                    openList.clear(); for (int o = 0; o < m; ++o) if (cnt[o] > 0) openList.push_back(o);
                    if (openList.empty()) skip = true;
                    else {
                        int a = openList[rng.nextInt(openList.size())];
                        vector<int> sks; for (int t = 0; t < NS; ++t) if (need[(size_t)a * NS + t] > 0) sks.push_back(t);
                        if (sks.empty()) skip = true;
                        else {
                            int sk = sks[rng.nextInt(sks.size())];
                            vector<char> mark(n, 0);
                            for (int i2 = 0; i2 < n; ++i2) if (assign[i2] == a) for (auto& kv : I.sk[i2]) if (kv.first == sk) { removed.push_back(i2); mark[i2] = 1; }
                            for (int i2 : removed) moveSite(i2, -1);
                            {
                                vector<pair<double,int>> extra;
                                for (int i2 = 0; i2 < n; ++i2) if (assign[i2] < 0 && !mark[i2]) {
                                    bool has = false; for (auto& kv : I.sk[i2]) if (kv.first == sk) has = true;
                                    if (has) { double bv = -1e300; for (int o : nearOff[i2]) bv = max(bv, siteVal(o, i2)); if (bv > 0) extra.push_back({-bv, i2}); }
                                }
                                int cap = 200 + (int)removed.size();
                                if ((int)extra.size() > cap) { nth_element(extra.begin(), extra.begin() + cap, extra.end()); extra.resize(cap); }
                                for (auto& e : extra) { removed.push_back(e.second); mark[e.second] = 1; }
                            }
                            size_t base = removed.size();
                            for (size_t h = 0; h < base; ++h) for (int j : knn[removed[h]]) if (assign[j] < 0 && !mark[j]) { mark[j] = 1; removed.push_back(j); }
                            for (int i2 = 0; i2 < n; ++i2) if (assign[i2] < 0 && !mark[i2] && owner[i2] == a) { mark[i2] = 1; removed.push_back(i2); }
                        }
                    }
                } else {
                    openList.clear(); for (int o = 0; o < m; ++o) if (cnt[o] > 0) openList.push_back(o);
                    if (openList.size() <= 1) skip = true;
                    else {
                        int a = openList[rng.nextInt(openList.size())];
                        for (int s = 0; s < n; ++s) if (assign[s] == a) removed.push_back(s);
                        for (int s : removed) moveSite(s, -1);
                    }
                }
                if (skip) { rollback(mk, hm); logging = false; lg.clear(); hullLog.clear(); continue; }
                recreate(removed, &forced);
                bool fc = fixCounts(40);
                double np = penNow();
                double delta = (profit - costSum - np) - before;
                if (!fc || (delta < 0 && rng.nextDouble() >= exp(delta / temp))) { rollback(mk, hm); }
                else { penCur = np; accepted++; changed = true; }
                logging = false; lg.clear(); hullLog.clear();
            }
            if (changed && profit - costSum > best.obj) {
                double to = trueObj();
                if (to > best.obj + 1e-9) snapshot();
            }
        }
    }
};

struct Params { double TM = 0.3, T1M = 0.003, BANDF = 0.6, H = 2.0, SWEEP = 0.12, FINAL = 0.35; int NT = 6; bool ILS = false, dbg = false, verbose = false; };
// whole search; time limit TL seconds from the call. Returns false if nothing usable.
static bool solveSimple(const Instance& I, double TL, uint64_t seed, const Params& P, vector<int>& asOut, vector<int>& woOut, double& objOut) {
    T_START = chrono::steady_clock::now();
    double tEnd = TL * 0.97;
    Solver S(I, seed);
    if (S.broken) return false;
    S.computeScale();
    if (P.verbose) fprintf(stderr, "read %.2fs n=%d m=%d W=%d NS=%d scale=%.4g\n", elapsed(), I.n, I.m, I.W, I.NS, S.scale);
        double TM = P.TM, T1M = P.T1M, BANDF = P.BANDF;
    int hdead = 0;
    { long long tt = 0; for (int i = 0; i < I.n; ++i) tt += I.ntask[i]; hdead = max(1, (int)llround(P.H * tt / max(1, I.n))); }
    // one SA unit: band phase (alpha>0) + levelize + exact phase. Continues from the current state.
    auto unit = [&](double dur) {
        double t0 = elapsed();
        S.best.assign.clear();
        if (I.alpha > 0) {
            S.pdead = hdead;
            S.anneal(t0 + dur * BANDF, S.scale * TM, S.scale * T1M, 1, 1, 1.0);
            S.pdead = 0;
            double tl0 = elapsed();
            S.bestLevelize();
            if (P.dbg) fprintf(stderr, "    band done at %.2f (target %.2f), levelize %.2fs\n", tl0, t0 + dur * BANDF, elapsed() - tl0);
            if (S.objective() > S.best.obj) S.snapshot();
            S.loadState(S.best.assign, S.best.workerOf);
            S.anneal(t0 + dur, S.scale * TM * 0.5, S.scale * T1M, 1, 1, 0.0);
        } else S.anneal(t0 + dur, S.scale * TM, S.scale * T1M, 1, 1, 0.0);
    };
    struct Cand { double v; int k, L, mode; vector<int> as, wo; };
    vector<Cand> cs;
    double bestAll = -1e300; vector<int> bestA(I.n, -1), bestW(I.W, -1);
    {
        long long totT = 0; for (int i = 0; i < I.n; ++i) totT += I.ntask[i];
        vector<int> kl;
        {
            int kn = S.kNatural();
            vector<int> raw = {kn, kn - 1, kn + 1, (int)(kn * 0.8), (int)(kn * 1.25), kn - 2, kn + 2, (int)(kn * 0.65), (int)(kn * 1.5), (int)(kn * 0.5), (int)(kn * 2), 1, I.m, (int)(kn * 0.35), (int)(kn * 3)};
            set<int> st; for (int k : raw) { k = max(1, min(I.m, k)); if (!st.count(k)) { st.insert(k); kl.push_back(k); } }
            if (P.verbose) fprintf(stderr, "kNatural=%d\n", kn);
        }
        double tSweep = elapsed() + (tEnd - elapsed()) * P.SWEEP;
        // pass 0: L = unlimited, both growth orders, for every k; pass 1: level grid
        for (int pass = 0; pass < 2; ++pass)
        for (int k : kl) {
            if (elapsed() > tSweep) break;
            auto op = S.chooseOpen(k);
            int Lmax = (int)(totT / k) + 1;
            vector<int> Ls;
            if (pass == 0) Ls.push_back(INT_MAX / 2);
            else if (I.alpha > 0) { for (int q = 11; q >= 1; --q) Ls.push_back(max(1, (int)(Lmax * (0.25 + 0.75 * q / 12.0)))); }
            for (int L : Ls) for (int mode = 0; mode < 2; ++mode) {
                if (elapsed() > tSweep) break;
                double tb0 = elapsed();
                S.growBuild(op, L, mode);
                double v = S.objective();
                if (P.dbg) fprintf(stderr, "   build k=%d L=%d mode=%d: %.4f in %.2fs\n", k, L, mode, v, elapsed() - tb0);
                cs.push_back({v, k, L, mode, S.assign, S.workerOf});
                if (v > bestAll) { bestAll = v; bestA = S.assign; bestW = S.workerOf; }
            }
        }
        sort(cs.begin(), cs.end(), [](const Cand& a, const Cand& b) { return a.v > b.v; });
        { vector<Cand> d; set<int> seenK; for (auto& c : cs) if (!seenK.count(c.k)) { seenK.insert(c.k); d.push_back(c); } cs = d; }
        int nt = min((int)cs.size(), P.NT);
        cs.resize(nt);
        if (P.verbose) fprintf(stderr, "sweep: %d candidates t=%.2f\n", nt, elapsed());
    }
    // successive halving over candidates
    double rest = tEnd - elapsed();
    int rounds = 0; for (int c = cs.size(); c > 1; c = (c + 1) / 2) rounds++;
    double finalShare = P.FINAL;
    double perRound = rest * (1 - finalShare) / max(1, rounds);
    while (cs.size() > 1) {
        double per = perRound / cs.size();
        for (auto& c : cs) {
            S.loadState(c.as, c.wo);
            unit(per);
            c.as = S.best.assign; c.wo = S.best.workerOf; c.v = S.best.obj;
            if (P.verbose) fprintf(stderr, "  k=%d -> %.4f t=%.1f\n", c.k, c.v, elapsed());
            if (c.v > bestAll) { bestAll = c.v; bestA = c.as; bestW = c.wo; }
        }
        sort(cs.begin(), cs.end(), [](const Cand& a, const Cand& b) { return a.v > b.v; });
        cs.resize((cs.size() + 1) / 2);
    }
    if (!cs.empty() && cs[0].v >= bestAll) { bestA = cs[0].as; bestW = cs[0].wo; bestAll = cs[0].v; }
    S.loadState(bestA, bestW);
    if (P.ILS) {
        double t0 = elapsed();
        unit((tEnd - t0) * 0.3);
        if (S.best.obj > bestAll) { bestAll = S.best.obj; bestA = S.best.assign; bestW = S.best.workerOf; }
        vector<int> curA = bestA, curW = bestW; double curV = bestAll;
        int it = 0, acc = 0;
        while (elapsed() < tEnd - 0.05) {
            double rem = tEnd - elapsed();
            double dt = min(rem, max(0.2, min(3.0, (tEnd - t0) / 25)));
            S.loadState(curA, curW);
            S.perturb(S.rng.nextInt(4));
            unit(dt);
            it++;
            if (S.best.obj > curV) { curV = S.best.obj; curA = S.best.assign; curW = S.best.workerOf; acc++; }
            if (curV > bestAll) { bestAll = curV; bestA = curA; bestW = curW; }
        }
        if (P.verbose) fprintf(stderr, "ils: %d perturbations, %d improvements\n", it, acc);
        S.best.assign = bestA; S.best.workerOf = bestW; S.best.obj = bestAll;
    } else
    unit(tEnd - elapsed());
    if (S.best.obj < bestAll) { S.best.assign = bestA; S.best.workerOf = bestW; S.best.obj = bestAll; }
    double obj = 0;
    string err = S.validateFull(S.best.assign, S.best.workerOf, &obj);
    if (P.verbose) fprintf(stderr, "final %.4f check='%s' fullobj=%.4f iters=%lld acc=%lld t=%.2f\n", S.best.obj, err.c_str(), obj, S.iters, S.accepted, elapsed());
    if (!err.empty()) return false;
    asOut = S.best.assign; woOut = S.best.workerOf; objOut = obj;
    return true;
}

}  // namespace simple_sz
static vector<int> simpleStart(double seconds, uint64_t seed) {
    simple_sz::Instance I;
    I.n = n; I.m = K; I.W = W; I.NS = max(1, NS);
    I.sx.resize(n); I.sy.resize(n); I.rew.resize(n); I.sk.resize(n); I.ntask.resize(n);
    for (int i = 0; i < n; i++) {
        I.sx[i] = px[i]; I.sy[i] = py[i]; I.rew[i] = rew[i]; I.ntask[i] = ntask[i];
        for (int k = 0; k < NS; k++) if (smask[i][k]) I.sk[i].push_back({k, 1});
    }
    I.ox.resize(K); I.oy.resize(K); I.cost.resize(K); I.maxSize.resize(K);
    for (int o = 0; o < K; o++) { I.ox[o] = px[n + o]; I.oy[o] = py[n + o]; I.cost[o] = ocost[o]; I.maxSize[o] = maxSize[o]; }
    I.workers.assign(W, {});
    for (int w = 0; w < W; w++) for (int k = 0; k < NS; k++) if (wmask[w][k]) I.workers[w].push_back(k);
    I.dist.assign((size_t)n * K, 0);
    for (int o = 0; o < K; o++) for (int i = 0; i < n; i++) I.dist[(size_t)o * n + i] = dist[o][i];
    I.A = A; I.alpha = alpha;
    I.tol = EPS;            // the main solver's geometric tolerance
    I.deadline = seconds;   // hard stop for the construction phases (seconds since the call)
    simple_sz::Params P;
    vector<int> as, wo; double obj = 0;
    if (!simple_sz::solveSimple(I, seconds, seed, P, as, wo, obj)) return {};
    if (szDebug) fprintf(stderr, "simpleStart: %.6f in %.2fs\n", obj, seconds);
    return as;
}

// ---- r28: equal-level zones by recursive ham-sandwich bisection (tight count window, heavy
// task-balance penalty). With A ~ 0 every zone needs the same site count AND the same task count;
// power cells / line cells / SA leave ~10 % of the sites out to get there. Here the sites are cut
// recursively by straight lines: each cut puts exactly the proportional share of sites on each
// side (k1 : k - k1 zones) and, over 180 directions, the one whose task share is closest to
// proportional (discrete ham-sandwich cut), with enough offices on each side; ties go to the
// smaller nearest-office distance. Each leaf is a convex cell holding ~n/k sites with the global
// task mix, and a DP picks (office, exactly c in [s, s + A] sites with exactly T tasks) in it.
// Zone counts k and levels (s, T) are scanned; the best plan is a start for the main search.
namespace eqpart {
static const int ND = 180;
struct Leaf {
    vector<int> P, Q;
};
static double cs_[ND], sn_[ND];
static double tw_ = 10;  // weight of one task off the proportional share (vs the distance proxy)
static vector<pair<int, int>> pairs_;  // sibling leaves (the two halves of a 2-zone region)
// per-leaf integer targets (sites, tasks) as prefix sums over the leaf order: every cut asks for
// the exact sums of its two leaf ranges, so the leaves end with the same size and task count +-1
static vector<long long> mP_, tP_;
static double end_ = 1e300;  // hard stop of a plan (time budget)
static void splitRec(vector<int>& P, vector<int>& Q, int l, int kr, vector<Leaf>& out) {
    int m = P.size();
    if (kr <= 1 || (int)Q.size() < 2 || m < 2 || elapsed() > end_) {
        out.push_back({P, Q});
        return;
    }
    long long tsum = 0;
    for (int s : P) tsum += ntask[s];
    struct Cand {
        double sc;
        int j, k1;
        double c;
    };
    vector<Cand> cands;
    vector<double> pr(m), tmp(m), qr(Q.size());
    for (int k1 : {kr / 2, (kr + 1) / 2}) {
        if (k1 < 1 || k1 >= kr) continue;
        if (!cands.empty() && k1 == cands.back().k1) continue;
        double fm = (double)(mP_[l + k1] - mP_[l]) / max(1LL, mP_[l + kr] - mP_[l]);
        double ft = (double)(tP_[l + k1] - tP_[l]) / max(1LL, tP_[l + kr] - tP_[l]);
        int tgt = max(1, min(m - 1, (int)lround(m * fm)));
        double ttg = (double)tsum * ft;
        for (int j = 0; j < ND; j++) {
            for (int i = 0; i < m; i++) pr[i] = px[P[i]] * cs_[j] + py[P[i]] * sn_[j];
            tmp = pr;
            nth_element(tmp.begin(), tmp.begin() + tgt, tmp.end());
            double a = tmp[tgt], b = *max_element(tmp.begin(), tmp.begin() + tgt);
            if (!(b < a)) continue;
            double c = 0.5 * (a + b);
            long long tl = 0;
            for (int i = 0; i < m; i++)
                if (pr[i] < c) tl += ntask[P[i]];
            int ql = 0;
            for (size_t q = 0; q < Q.size(); q++) ql += px[n + Q[q]] * cs_[j] + py[n + Q[q]] * sn_[j] < c;
            if (ql < k1 || (int)Q.size() - ql < kr - k1) continue;
            cands.push_back({fabs((double)tl - ttg), j, k1, c});
        }
    }
    if (cands.empty()) {
        out.push_back({P, Q});
        return;
    }
    sort(cands.begin(), cands.end(), [](const Cand& x, const Cand& y) { return x.sc < y.sc; });
    double best = 1e300;
    int bi = 0;
    static const int eqNC = 8;
    static const double eqTol = 1.0;
    for (int ci = 0; ci < (int)cands.size() && ci < eqNC && cands[ci].sc <= cands[0].sc + eqTol; ci++) {
        const Cand& cd = cands[ci];
        vector<int> Ql, Qr;
        for (int q : Q) (px[n + q] * cs_[cd.j] + py[n + q] * sn_[cd.j] < cd.c ? Ql : Qr).push_back(q);
        double cst = 0;
        for (int s : P) {
            bool l = px[s] * cs_[cd.j] + py[s] * sn_[cd.j] < cd.c;
            double md = 1e300;
            for (int q : (l ? Ql : Qr)) md = min(md, dist[q][s]);
            cst += md;
        }
        double sc = tw_ * cd.sc + cst;
        if (sc < best) best = sc, bi = ci;
    }
    const Cand& cd = cands[bi];
    vector<int> Pl, Pr, Ql, Qr;
    for (int s : P) (px[s] * cs_[cd.j] + py[s] * sn_[cd.j] < cd.c ? Pl : Pr).push_back(s);
    for (int q : Q) (px[n + q] * cs_[cd.j] + py[n + q] * sn_[cd.j] < cd.c ? Ql : Qr).push_back(q);
    vector<int>().swap(P);
    vector<int>().swap(Q);
    size_t i0 = out.size();
    splitRec(Pl, Ql, l, cd.k1, out);
    splitRec(Pr, Qr, l + cd.k1, kr - cd.k1, out);
    if (kr == 2 && out.size() == i0 + 2) pairs_.push_back({(int)i0, (int)i0 + 1});
}
// sites with at most 2 tasks: best zone of office o on sites P with c in [s, min(maxSize, s + A)]
// sites and exactly T tasks = the most profitable x two-task, y one-task, z task-free sites
// (profit - office cost; -1e300 if none); the chosen sites in *sel
static double fastVal(int o, const vector<int>& P, int s, int T, vector<int>* sel) {
    static vector<pair<double, int>> cl[3];
    static vector<double> pre[3];
    for (int k = 0; k < 3; k++) cl[k].clear();
    for (int i : P) cl[ntask[i]].push_back({rew[i] - dist[o][i], i});
    for (int k = 0; k < 3; k++) {
        sort(cl[k].begin(), cl[k].end(), greater<pair<double, int>>());
        pre[k].assign(cl[k].size() + 1, 0);
        for (size_t i = 0; i < cl[k].size(); i++) pre[k][i + 1] = pre[k][i] + cl[k][i].first;
    }
    int n0 = cl[0].size(), n1 = cl[1].size(), n2 = cl[2].size();
    int ce = min(maxSize[o], s + A);
    double best = -1e300;
    int bx = -1, by = -1, bz = -1;
    for (int c = s; c <= ce; c++) {
        // admissible x: y = T - 2x in [0, n1], z = c - T + x in [0, n0], x in [0, n2]
        int xlo = max({0, T - c, (T - n1 + 1) / 2}), xhi = min({n2, T / 2, n0 + T - c});
        if (T - n1 < 0) xlo = max(0, T - c);
        if (xlo > xhi) continue;
        auto f = [&](int x) { return pre[2][x] + pre[1][T - 2 * x] + pre[0][c - T + x]; };
        if (xhi - xlo > 64) {  // f is concave (sorted gains): bisect on the step sign
            int a = xlo, b = xhi;
            while (a < b) {
                int mid = (a + b) / 2;
                if (f(mid + 1) > f(mid)) a = mid + 1;
                else b = mid;
            }
            double v = f(a);
            if (v > best) best = v, bx = a, by = T - 2 * a, bz = c - T + a;
            continue;
        }
        for (int x = xlo; x <= xhi; x++) {
            int y = T - 2 * x, z = c - x - y;
            double v = pre[2][x] + pre[1][y] + pre[0][z];
            if (v > best) best = v, bx = x, by = y, bz = z;
        }
    }
    if (bx < 0) return -1e300;
    if (sel) {
        sel->clear();
        for (int i = 0; i < bx; i++) sel->push_back(cl[2][i].second);
        for (int i = 0; i < by; i++) sel->push_back(cl[1][i].second);
        for (int i = 0; i < bz; i++) sel->push_back(cl[0][i].second);
    }
    return best - ocost[o];
}
// best (office, value) of a leaf at level (s, T) over its offices nearest to the sites' centroid
static double leafBest(const vector<int>& P, const vector<int>& Q, int s, int T, int* bo, vector<int>* sel) {
    *bo = -1;
    if ((int)P.size() < s || Q.empty()) return 0;
    double cx = 0, cy = 0;
    for (int i : P) cx += px[i], cy += py[i];
    cx /= P.size(), cy /= P.size();
    int qs[3], nq = 0;
    double qd[3];
    for (int q : Q) {
        double d = (px[n + q] - cx) * (px[n + q] - cx) + (py[n + q] - cy) * (py[n + q] - cy);
        int at = nq < 3 ? nq++ : 3;
        if (at == 3 && d >= qd[2]) continue;
        if (at == 3) at = 2;
        while (at > 0 && qd[at - 1] > d) qd[at] = qd[at - 1], qs[at] = qs[at - 1], at--;
        qd[at] = d, qs[at] = q;
    }
    double best = 0;
    for (int i = 0; i < nq; i++) {
        double v = fastVal(qs[i], P, s, T, nullptr);
        if (v > best) best = v, *bo = qs[i];
    }
    if (*bo >= 0 && sel) fastVal(*bo, P, s, T, sel);
    return best;
}
// re-cut each 2-zone region (sibling leaves) by the best line over all directions and site splits
static bool pairImprove(vector<Leaf>& leaves, vector<double>& lv, int s, int T) {
    bool any = false;
    vector<int> U, ord;
    vector<double> pr;
    for (auto& pq : pairs_) {
        if (elapsed() > end_) return any;
        Leaf& La = leaves[pq.first];
        Leaf& Lb = leaves[pq.second];
        U = La.P;
        U.insert(U.end(), Lb.P.begin(), Lb.P.end());
        vector<int> QU = La.Q;
        QU.insert(QU.end(), Lb.Q.begin(), Lb.Q.end());
        int m = U.size();
        if (m < 2 * s && m < s) continue;
        double cur = lv[pq.first] + lv[pq.second], best = cur + 1e-9;
        int bj = -1;
        double bc = 0;
        pr.resize(m);
        ord.resize(m);
        vector<int> L, R, QL, QR;
        for (int j = 0; j < ND; j++) {
            if (elapsed() > end_) break;
            for (int i = 0; i < m; i++) pr[i] = px[U[i]] * cs_[j] + py[U[i]] * sn_[j], ord[i] = i;
            sort(ord.begin(), ord.end(), [&](int a, int b) { return pr[a] < pr[b]; });
            for (int p = min(s, m); p <= max(m - s, 0) || p == min(s, m); p++) {
                if (p <= 0 || p >= m || !(pr[ord[p - 1]] < pr[ord[p]])) continue;
                double c = 0.5 * (pr[ord[p - 1]] + pr[ord[p]]);
                L.clear(), R.clear(), QL.clear(), QR.clear();
                for (int i = 0; i < m; i++) (i < p ? L : R).push_back(U[ord[i]]);
                for (int q : QU) (px[n + q] * cs_[j] + py[n + q] * sn_[j] < c ? QL : QR).push_back(q);
                int o1, o2;
                double v = leafBest(L, QL, s, T, &o1, nullptr) + leafBest(R, QR, s, T, &o2, nullptr);
                if (v > best) best = v, bj = j, bc = c;
                if (p > m - s || elapsed() > end_) break;
            }
        }
        if (bj < 0) continue;
        vector<int> Pa, Pb, Qa, Qb;
        for (int i : U) (px[i] * cs_[bj] + py[i] * sn_[bj] < bc ? Pa : Pb).push_back(i);
        for (int q : QU) (px[n + q] * cs_[bj] + py[n + q] * sn_[bj] < bc ? Qa : Qb).push_back(q);
        La.P = Pa, La.Q = Qa, Lb.P = Pb, Lb.Q = Qb;
        int o;
        lv[pq.first] = leafBest(La.P, La.Q, s, T, &o, nullptr);
        lv[pq.second] = leafBest(Lb.P, Lb.Q, s, T, &o, nullptr);
        any = true;
    }
    return any;
}
// best profit of exactly c sites with exactly t tasks (c <= C, t <= Tm) for office o over sites P;
// with take != nullptr also the choice bits for backtracking
static void leafDP(int o, const vector<int>& P, int C, int Tm, vector<double>& dp, vector<char>* take) {
    const double NEG = -1e300;
    int m = P.size(), W1 = Tm + 1;
    // (too large: no zone here; an empty table, nothing allocated -- (C + 1) x W1 alone can be
    // O(n x tasks))
    if ((double)m * (C + 1) * W1 > 2e7 || (double)(C + 1) * W1 > 2e7) {
        dp.clear();
        if (take) take->clear();
        return;
    }
    dp.assign((size_t)(C + 1) * W1, NEG);
    dp[0] = 0;
    if (take) take->assign((size_t)m * (C + 1) * W1, 0);
    for (int i = 0; i < m; i++) {
        int s = P[i], ti = ntask[s];
        double p = rew[s] - dist[o][s];
        if (ti > Tm) continue;
        for (int c = min(i + 1, C); c >= 1; c--) {
            double* row = &dp[(size_t)c * W1];
            const double* prv = &dp[(size_t)(c - 1) * W1];
            for (int t = Tm; t >= ti; t--) {
                double v = prv[t - ti];
                if (v > NEG && v + p > row[t]) {
                    row[t] = v + p;
                    if (take) (*take)[((size_t)i * (C + 1) + c) * W1 + t] = 1;
                }
            }
        }
    }
}
}  // namespace eqpart
// count- and level-preserving greedy polish: swap two sites of equal task count between zones,
// or a zone's site for a free one of equal task count, whenever the distance drops (geometry as
// always checked by tryChange)
static void eqPolish(State& st, double endTime) {
    double lamSave = lambdaCnt, waSave = wAlpha, wcSave = wCost, l1Save = l1Cost;
    int lvSave = lvTarget;
    lambdaCnt = 1e18, wAlpha = 1, wCost = 1, l1Cost = 0, lvTarget = -1, wLv = 0;
    Change ch[2];
    // the clock is read every 16 members: one member scans up to n sites of nearOrder (huge n: a pass over
    // a zone of 1e5 sites would take minutes - ring200k, A = 0, maxSize n/2)
    long long tick = 0;
    bool late = false;
    for (int pass = 0; pass < 6 && !late && elapsed() < endTime; pass++) {
        int acc = 0;
        for (int a = 0; a < K && !late && elapsed() < endTime; a++) {
            if (st.cnt[a] == 0) continue;
            vector<int> mem = st.mem[a];
            for (int s1 : mem) {
                if ((++tick & 15) == 0 && elapsed() >= endTime) {
                    late = true;
                    break;
                }
                if (st.asg[s1] != a) continue;
                double d1 = dist[a][s1];
                // a free site of the same task count nearer to a
                bool done = false;
                for (int f : nearOrder[a]) {
                    if (dist[a][f] >= d1 - 1e-12) break;
                    if (st.asg[f] != -1 || ntask[f] != ntask[s1]) continue;
                    ch[0] = {s1, a, -1}, ch[1] = {f, -1, a};
                    if (tryChange(st, ch, 2, 1e-12)) {
                        acc++, done = true;
                        break;
                    }
                }
                if (done) continue;
                // a swap with a neighbouring zone
                for (int b : nearOff[s1]) {
                    if (b == a || st.cnt[b] == 0) continue;
                    double g1 = d1 - dist[b][s1];
                    int bs = -1;
                    double bg = 1e-9;
                    int lim = min(n, 3 * st.cnt[b] + 10), seen = 0;
                    for (int t : nearOrder[a]) {
                        if (seen++ > lim) break;
                        if (st.asg[t] != b || ntask[t] != ntask[s1]) continue;
                        double g = g1 + dist[b][t] - dist[a][t];
                        if (g > bg) bg = g, bs = t;
                    }
                    if (bs < 0) continue;
                    ch[0] = {s1, a, b}, ch[1] = {bs, b, a};
                    if (tryChange(st, ch, 2, 1e-12)) {
                        acc++;
                        break;
                    }
                }
            }
        }
        if (!acc) break;
    }
    lambdaCnt = lamSave, wAlpha = waSave, wCost = wcSave, l1Cost = l1Save, lvTarget = lvSave;
}
// returns the best assignment (empty if none); *outVal its true value
static vector<int> eqStart(double endTime, int k0, double* outVal) {
    using namespace eqpart;
    *outVal = -1e300;
    vector<int> caps;
    for (int o = 0; o < K; o++)
        if (maxSize[o] > 0) caps.push_back(maxSize[o]);
    if (caps.size() < 2 || n < 4) return {};
    sort(caps.begin(), caps.end());
    long long tAll = 0;
    for (int s = 0; s < n; s++) tAll += ntask[s];
    double r = (double)tAll / n;
    // zone counts: around the incumbent's and around full coverage at the median capacity
    vector<int> ks;
    auto addK = [&](int k) {
        if (k >= 2 && k <= (int)caps.size() && find(ks.begin(), ks.end(), k) == ks.end()) ks.push_back(k);
    };
    // (zone count for full coverage at the median capacity, up to 30 % more, then around the
    // incumbent's; independent of the incumbent first, so the scan does not depend on timing)
    int kFull = (int)ceil(n / (double)caps[caps.size() / 2]);
    for (int k = kFull; k <= (int)ceil(1.3 * kFull); k++) addK(k);
    for (int d = 0; d <= 6; d++) addK(k0 + d), addK(k0 - d);
    for (int k = kFull - 1; k >= (int)(0.8 * kFull); k--) addK(k);
    vector<int> best;
    double bestV = -1e300;
    vector<double> dp;
    vector<char> take;
    int tried = 0;
    const double t00 = elapsed();
    // rounds: every zone count once with the plain directions, then randomized variants (direction
    // offset, task weight) of the zone counts that did best so far
    vector<pair<double, int>> kVal;
    static const int eqVar = 0;
    for (int it = 0;; it++) {
        int k;
        double off = 0;
        static const double tw0 = 10;
        tw_ = tw0;
        if (it < (int)ks.size()) k = ks[it];
        else {
            if (!eqVar || kVal.empty()) break;
            sort(kVal.begin(), kVal.end(), greater<pair<double, int>>());
            int top = min<int>(kVal.size(), 4);
            k = kVal[irand(top)].second;
            off = urand();
            static const double tws[4] = {3, 10, 10, 30};
            tw_ = tws[irand(4)];
        }
        if (elapsed() > endTime) break;
        end_ = endTime + 0.5 * (endTime - t00);
        for (int j = 0; j < ND; j++) cs_[j] = cos(M_PI * (j + off) / ND), sn_[j] = sin(M_PI * (j + off) / ND);
        double t0 = elapsed();
        int sHi = (int)floor(0.995 * n / k), sLo = (int)floor(0.85 * n / k);
        sHi = min(sHi, caps.back());
        if (sLo < 1 || sHi < sLo) continue;
        vector<int> P(n), Q;
        for (int s = 0; s < n; s++) P[s] = s;
        for (int o = 0; o < K; o++)
            if (maxSize[o] >= sLo) {
                bool dup = false;
                for (int q : Q) dup |= px[n + q] == px[n + o] && py[n + q] == py[n + o];
                if (!dup) Q.push_back(o);
            }
        if ((int)Q.size() < k) continue;
        vector<Leaf> leaves;
        pairs_.clear();
        mP_.assign(k + 1, 0), tP_.assign(k + 1, 0);
        for (int i = 0; i < k; i++) {
            mP_[i + 1] = mP_[i] + n / k + (i < n % k);
            // extra tasks go to the leaves without an extra site first (keeps one-task counts even)
            int ex = (int)(tAll % k), j = (i + k - n % k) % k;
            tP_[i + 1] = tP_[i] + tAll / k + (j < ex);
        }
        static const int eqExact = 0;
        if (!eqExact)  // proportional shares
            for (int i = 0; i <= k; i++) mP_[i] = i, tP_[i] = i;
        splitRec(P, Q, 0, k, leaves);
        int TLo = max(0, (int)floor(sLo * r) - 4), THi = (int)ceil((sHi + A) * r) + 4;
        int cMax = sHi + A;
        // per leaf and office: dp rows for c in [sLo, cMax], t in [TLo, THi]
        int nc = cMax - sLo + 1, nt = THi - TLo + 1;
        if ((double)nc * nt > 2e7 || (double)nc * nt * 4 * leaves.size() > 4e7) continue;  // (level tables too large)
        struct Tab {
            int o;
            vector<double> v;  // nc x nt
        };
        vector<vector<Tab>> tabs(leaves.size());
        for (size_t li = 0; li < leaves.size(); li++) {
            if (elapsed() > end_) break;
            Leaf& L = leaves[li];
            if ((int)L.P.size() < sLo) continue;
            double cx = 0, cy = 0;
            for (int s : L.P) cx += px[s], cy += py[s];
            cx /= L.P.size(), cy /= L.P.size();
            vector<int> Qs = L.Q;
            sort(Qs.begin(), Qs.end(), [&](int a, int b) { return hypot(px[n + a] - cx, py[n + a] - cy) < hypot(px[n + b] - cx, py[n + b] - cy); });
            if (Qs.size() > 4) Qs.resize(4);
            for (int o : Qs) {
                int C = min(maxSize[o], min(cMax, (int)L.P.size()));
                if (C < sLo) continue;
                leafDP(o, L.P, C, THi, dp, nullptr);
                if (dp.empty()) continue;  // (table too large: no zone of this office)
                Tab tb{o, vector<double>((size_t)nc * nt, -1e300)};
                for (int c = sLo; c <= C; c++)
                    for (int t = TLo; t <= THi; t++) tb.v[(size_t)(c - sLo) * nt + (t - TLo)] = dp[(size_t)c * (THi + 1) + t];
                tabs[li].push_back(std::move(tb));
            }
        }
        double bv = -1e300;
        int bs = -1, bT = -1;
        vector<double> sV(sHi + 1, -1e300);
        vector<int> sT(sHi + 1, -1);
        for (int s = sLo; s <= sHi; s++)
            for (int T = TLo; T <= THi; T++) {
                double v = 0;
                for (auto& tl : tabs) {
                    double z = 0;
                    for (auto& tb : tl) {
                        int ce = min(s + A, min(maxSize[tb.o], cMax));
                        for (int c = s; c <= ce; c++) z = max(z, tb.v[(size_t)(c - sLo) * nt + (T - TLo)] - ocost[tb.o]);
                    }
                    v += z;
                }
                if (v > bv) bv = v, bs = s, bT = T;
                if (v > sV[s]) sV[s] = v, sT[s] = T;
            }
        tried++;
        if (bs < 0) continue;
        // rebuild the chosen plan (sites with <= 2 tasks: pair re-cuts first, greedy class picks)
        vector<int> asg(AS, -1);
        int maxT = 0;
        for (int i = 0; i < n; i++) maxT = max(maxT, ntask[i]);
        static const int eqPair = 1;
        if (maxT <= 2) {
            vector<double> lv(leaves.size());
            vector<int> sel;
            int o;
            // the pair re-cuts can rescue leaves that miss a larger zone size: try the best level
            // of each size up to 3 above the table's choice
            static const int eqUp = 3;
            double cBest = -1e300;
            vector<Leaf> cLeaves;
            for (int s = bs; s <= min(sHi, bs + eqUp); s++) {
                if (sT[s] < 0 || (s > bs && elapsed() > endTime)) continue;
                vector<Leaf> lc = leaves;
                for (size_t li = 0; li < lc.size(); li++) lv[li] = leafBest(lc[li].P, lc[li].Q, s, sT[s], &o, nullptr);
                for (int pass = 0; pass < eqPair && elapsed() < endTime + 0.5 * (endTime - t00); pass++)
                    if (!pairImprove(lc, lv, s, sT[s])) break;
                double tot = 0;
                for (double x : lv) tot += x;
                if (tot > cBest) cBest = tot, cLeaves.swap(lc), bs = s, bT = sT[s];
            }
            leaves.swap(cLeaves);
            for (size_t li = 0; li < leaves.size(); li++) {
                leafBest(leaves[li].P, leaves[li].Q, bs, bT, &o, &sel);
                if (o >= 0)
                    for (int i : sel) asg[i] = o;
            }
        } else
        for (size_t li = 0; li < leaves.size(); li++) {
            double z = 0;
            int zo = -1, zc = -1;
            for (auto& tb : tabs[li]) {
                int ce = min(bs + A, min(maxSize[tb.o], cMax));
                for (int c = bs; c <= ce; c++) {
                    double v = tb.v[(size_t)(c - sLo) * nt + (bT - TLo)] - ocost[tb.o];
                    if (v > z) z = v, zo = tb.o, zc = c;
                }
            }
            if (zo < 0) continue;
            const vector<int>& PP = leaves[li].P;
            int C = min(maxSize[zo], min(cMax, (int)PP.size()));
            leafDP(zo, PP, C, bT, dp, &take);
            if (take.empty() || dp.empty()) continue;
            int c = zc, t = bT, W1 = bT + 1;
            for (int i = (int)PP.size() - 1; i >= 0 && c > 0; i--)
                if (take[((size_t)i * (C + 1) + c) * W1 + t]) asg[PP[i]] = zo, c--, t -= ntask[PP[i]];
        }
        State st = fromAsg(asg);
        bool ok = countFeasible(st) && validateFull(st).empty();
        // too few workers for every zone: drop the least valuable zones until the cover exists
        for (int drop = 0; !ok && drop < k / 3 && countFeasible(st) && elapsed() < endTime; drop++) {
            int wo = -1;
            double wv = 1e300;
            for (int o = 0; o < K; o++) {
                if (st.cnt[o] == 0) continue;
                double v = -ocost[o];
                for (int i : st.mem[o]) v += rew[i] - dist[o][i];
                if (v < wv) wv = v, wo = o;
            }
            if (wo < 0) break;
            for (int i = 0; i < n; i++)
                if (asg[i] == wo) asg[i] = -1;
            st = fromAsg(asg);
            ok = countFeasible(st) && validateFull(st).empty();
        }
        double v = ok ? trueObjective(st) : -1e300;
        if (szDebug && it < (int)ks.size() + 40) fprintf(stderr, "eq: k=%d leaves=%zu s=%d T=%d tw=%g plan %.4f -> %s %.4f (%.2fs)\n", k, leaves.size(), bs, bT, tw_, bv, ok ? "valid" : validateFull(st).c_str(), v, elapsed() - t0);
        if (ok) {
            bool f = false;
            for (auto& kv : kVal)
                if (kv.second == k) kv.first = max(kv.first, v), f = true;
            if (!f) kVal.push_back({v, k});
        }
        if (ok && v > bestV) bestV = v, best = st.asg;
    }
    static const bool eqPol = true;
    if (eqPol && !best.empty()) {
        State st = fromAsg(best);
        eqPolish(st, endTime + 0.5 * (endTime - t00));
        double v = trueObjective(st);
        if (szDebug) fprintf(stderr, "eq polish %.4f -> %.4f\n", bestV, v);
        if (countFeasible(st) && validateFull(st).empty() && v > bestV) bestV = v, best = st.asg;
    }
    *outVal = bestV;
    return best;
}


// ---- r33: exact-composition plans. With a tight count window and a heavy task-balance penalty
// every zone carries the same number of sites of each task count (A = 0, tasks in {1, 2}: same
// size and level <=> same number of one-task and two-task sites). eqStart cuts by proportional
// shares, so leaves miss the common composition by a few sites and the level drops for all zones
// (~8 % of the sites unserved). Here the composition z (per task-count class) is fixed first
// (z_c = floor(N_c (1 - rho) / k), trimmed to the capacity), and every straight cut must leave on
// each side at least (zones on that side) x z_c sites of every class and as many offices as zones:
// then every leaf can host a full zone and only the slack sites stay out. The cuts form a tree
// whose value is the sum of the leaves' best zones (exact level); a region without an admissible
// cut gets one zone less. The tree is improved by rebuilding random subtrees with randomized cut
// choices (accepted when the subtree's value grows): the regions are convex and nested, so a
// subtree never interacts with the rest of the plan.
namespace eqx {
static int NCL = 0;
static vector<int> z_;
static int s_ = 0, T_ = 0;
static double end_ = 1e300, offs_ = 0, tol_ = 3, noise_ = 0, wq_ = 1.0;
static int ncand_ = 12;
static long long calls_ = 0, callCap_ = 1 << 30;
static bool dbgFail_ = false;
struct TN {
    vector<int> P, Q;
    int kr, l, r, par, zones;
    double val;
};
static vector<TN> tn_;
static int trK_ = 4, trN_ = 3, krMax_ = 16;
static bool rpos_ = false;
static int scMode_ = 1, scCur_ = 1;
static double rposP_ = 0;
static void freeSub(int v) {
    if (v < 0) return;
    freeSub(tn_[v].l), freeSub(tn_[v].r);
    vector<int>().swap(tn_[v].P), vector<int>().swap(tn_[v].Q);
    tn_[v].l = tn_[v].r = -1;
}
static int newNode(vector<int>& P, vector<int>& Q, int kr) {
    tn_.push_back(TN());
    TN& t = tn_.back();
    t.P.swap(P), t.Q.swap(Q);
    t.kr = kr, t.l = t.r = t.par = -1, t.zones = 0, t.val = 0;
    return tn_.size() - 1;
}
static int mkLeaf(vector<int>& P, vector<int>& Q, int kr) {
    int v = newNode(P, Q, kr);
    int o;
    tn_[v].val = eqpart::leafBest(tn_[v].P, tn_[v].Q, s_, T_, &o, nullptr);
    tn_[v].zones = o >= 0;
    return v;
}
// can kr zones (c in [s, s + A] sites, exactly T tasks each) be drawn from class counts N (tasks
// 0, 1, 2)? Free variable: the number of two-task sites Z2; *margin = width of its range
static bool feas(const vector<int>& N, int kr, long long& margin) {
    long long N0 = N[0], N1 = NCL > 1 ? N[1] : 0, N2 = NCL > 2 ? N[2] : 0;
    long long krT = (long long)kr * T_;
    long long lo = max((long long)kr * max(0, T_ - s_ - A), (krT - N1 + 1) / 2);
    if (krT - N1 < 0) lo = max((long long)kr * max(0, T_ - s_ - A), 0LL);
    long long hi = min({(long long)kr * (T_ / 2), N2, N0 + (long long)kr * (T_ - s_)});
    margin = hi - lo;
    return hi >= lo;
}
static vector<int> rTmp_;
static const vector<int>& preR(const vector<int>& pre, const vector<int>& N) {
    rTmp_.resize(N.size());
    for (size_t c = 0; c < N.size(); c++) rTmp_[c] = N[c] - pre[c];
    return rTmp_;
}
// builds the subtree of region (P, Q) with kr zones; returns its node
static int build(vector<int> P, vector<int> Q, int kr) {
    calls_++;
    int m = P.size();
    if (kr <= 1 || elapsed() > end_ || m < 2) return mkLeaf(P, Q, kr);
    vector<int> N(NCL, 0);
    for (int s : P) N[ntask[s]]++;
    struct Cand {
        double imb, cs, sn, c, cost;
        int k1;
    };
    vector<Cand> cands;
    vector<double> pr(m), qp(Q.size());
    vector<int> ord(m), pre(NCL);
    // admissible cuts: every side keeps (its zones) x z_c sites of every class and enough offices
    vector<pair<double, int>> arr(m);
    auto gen = [&](const vector<int>& k1s, int nd) {
        int nk = k1s.size();
        vector<double> bImb(nk), bC(nk);
        // only cut positions with >= k1 s sites left and >= (kr - k1) s right can be admissible:
        // order just that window (selection around it)
        int pLo = m, pHi = 0;
        for (int k1 : k1s) pLo = min(pLo, k1 * s_), pHi = max(pHi, m - (kr - k1) * s_);
        pLo = max(pLo, 1), pHi = min(pHi, m - 1);
        if (pLo > pHi) return;
        for (int j = 0; j < nd; j++) {
            if (j > 0 && elapsed() > end_) break;
            double ang = M_PI * (j + offs_) / nd, cs = cos(ang), sn = sin(ang);
            for (int i = 0; i < m; i++) arr[i] = {px[P[i]] * cs + py[P[i]] * sn, P[i]};
            fill(pre.begin(), pre.end(), 0);
            if (pLo - 1 > 0) {
                nth_element(arr.begin(), arr.begin() + (pLo - 1), arr.end());
                for (int i = 0; i < pLo - 1; i++) pre[ntask[arr[i].second]]++;
            }
            if (pHi + 1 < m) nth_element(arr.begin() + (pLo - 1), arr.begin() + (pHi + 1), arr.end());
            sort(arr.begin() + (pLo - 1), arr.begin() + min(m, pHi + 1));
            // (the element at pHi + 1, if any, is >= all of the window: not needed for the checks)
            for (size_t q = 0; q < Q.size(); q++) qp[q] = px[n + Q[q]] * cs + py[n + Q[q]] * sn;
            sort(qp.begin(), qp.end());
            fill(bImb.begin(), bImb.end(), 1e300);
            vector<int> cntOk(nk, 0);
            for (int p = pLo; p <= pHi; p++) {
                pre[ntask[arr[p - 1].second]]++;
                if (!(arr[p - 1].first < arr[p].first)) continue;
                double c = 0.5 * (arr[p - 1].first + arr[p].first);
                int ql = lower_bound(qp.begin(), qp.end(), c) - qp.begin();
                for (int t = 0; t < nk; t++) {
                    int k1 = k1s[t];
                    if (ql < k1 || (int)Q.size() - ql < kr - k1) continue;
                    double imb = wq_ * fabs(ql - (k1 + (double)((int)Q.size() - kr) * k1 / kr));
                    long long mL, mR;
                    bool ok = feas(pre, k1, mL) && feas(preR(pre, N), kr - k1, mR);
                    if (scCur_ == 1) {  // distance of each class count from its proportional share of the slack
                        for (int cl = 0; cl < NCL; cl++) imb += fabs(pre[cl] - (k1 * z_[cl] + (double)(N[cl] - kr * z_[cl]) * k1 / kr));
                    } else  // the smaller per-zone margin of the two sides (larger is better)
                        imb -= min((double)mL / k1, (double)mR / (kr - k1));
                    if (ok) {
                        if (rpos_) {  // a random admissible position (reservoir)
                            if (++cntOk[t] == 1 || irand(cntOk[t]) == 0) bImb[t] = imb, bC[t] = c;
                        } else if (imb < bImb[t]) bImb[t] = imb, bC[t] = c;
                    }
                }
            }
            for (int t = 0; t < nk; t++)
                if (bImb[t] < 1e299) cands.push_back({bImb[t] / (k1s[t] * (double)(kr - k1s[t])) * (kr * kr / 4.0), cs, sn, bC[t], 0, k1s[t]});
        }
    };
    static const int ndMul = 2;
    int nd0 = m > 600 ? eqpart::ND : ndMul * eqpart::ND;
    if (m > 200000) nd0 = max(12, (int)(eqpart::ND * 2e5 / m));  // huge regions: fewer directions
    vector<int> halves = {kr / 2};
    if ((kr + 1) / 2 != kr / 2) halves.push_back((kr + 1) / 2);
    gen(halves, nd0);
    if (cands.empty() && elapsed() < end_) {  // any split of the zones
        vector<int> all;
        for (int k1 = 1; k1 < kr; k1++) all.push_back(k1);
        gen(all, 2 * nd0);
    }
    if (cands.empty()) {
        if (szDebug && dbgFail_) {
            long long co = 0;
            for (int cl = 0; cl < NCL; cl++) co += N[cl] - kr * z_[cl];
            fprintf(stderr, "  eqx fail m=%d kr=%d Q=%zu slack=%lld\n", m, kr, Q.size(), co);
        }
        // one zone less here: its sites become slack for the others
        vector<int> P2 = P, Q2 = Q;
        int c = build(P2, Q2, kr - 1);
        int v = newNode(P, Q, kr);
        tn_[v].l = c, tn_[c].par = v, tn_[v].val = tn_[c].val, tn_[v].zones = tn_[c].zones;
        return v;
    }
    sort(cands.begin(), cands.end(), [](const Cand& x, const Cand& y) { return x.imb < y.imb; });
    int lim = 0;
    while (lim < (int)cands.size() && cands[lim].imb <= cands[0].imb + tol_) lim++;
    // spread the distance evaluations over the admissible directions
    int step = max(1, lim / ncand_);
    vector<Cand> ev;
    for (int ci = 0; ci < lim; ci += step) {
        if (!ev.empty() && elapsed() > end_) break;
        Cand cd = cands[ci];
        vector<int> Ql, Qr;
        for (int q : Q) (px[n + q] * cd.cs + py[n + q] * cd.sn < cd.c ? Ql : Qr).push_back(q);
        double cst = 0;
        for (int s : P) {
            bool l = px[s] * cd.cs + py[s] * cd.sn < cd.c;
            double md = 1e300;
            for (int q : (l ? Ql : Qr)) md = min(md, dist[q][s]);
            cst += md;
        }
        if (noise_ > 0) cst *= 1 + noise_ * urand();
        cd.cost = cst;
        ev.push_back(cd);
    }
    sort(ev.begin(), ev.end(), [](const Cand& x, const Cand& y) { return x.cost < y.cost; });
    // the next cuts when a sub-region loses zones (small regions: the best value of all tries)
    int tries = calls_ > callCap_ ? 1 : (kr <= trK_ ? trN_ : 2);
    int bl = -1, br = -1;
    double bv = -1e300;
    int bz = -1;
    for (int ti = 0; ti < (int)ev.size() && ti < tries; ti++) {
        const Cand& cd = ev[ti];
        vector<int> Pl, Pr, Ql, Qr;
        for (int s : P) (px[s] * cd.cs + py[s] * cd.sn < cd.c ? Pl : Pr).push_back(s);
        for (int q : Q) (px[n + q] * cd.cs + py[n + q] * cd.sn < cd.c ? Ql : Qr).push_back(q);
        int a = build(Pl, Ql, cd.k1);
        int b = build(Pr, Qr, kr - cd.k1);
        int zz = tn_[a].zones + tn_[b].zones;
        double vv = tn_[a].val + tn_[b].val;
        if (zz > bz || (zz == bz && vv > bv)) {
            freeSub(bl), freeSub(br);
            bl = a, br = b, bv = vv, bz = zz;
        } else freeSub(a), freeSub(b);
        if ((bz == kr && kr > trK_) || elapsed() > end_) break;
    }
    int v = newNode(P, Q, kr);
    tn_[v].l = bl, tn_[v].r = br, tn_[bl].par = v, tn_[br].par = v;
    tn_[v].val = bv, tn_[v].zones = bz;
    return v;
}
static void leavesOf(int v, vector<int>& out) {
    if (v < 0) return;
    if (tn_[v].l < 0 && tn_[v].r < 0) {
        out.push_back(v);
        return;
    }
    leavesOf(tn_[v].l, out), leavesOf(tn_[v].r, out);
}
static void nodesOf(int v, vector<int>& out) {
    if (v < 0) return;
    out.push_back(v);
    nodesOf(tn_[v].l, out), nodesOf(tn_[v].r, out);
}
// keeps only the nodes reachable from root (the rebuilds leave freed nodes behind); new root
static int compact(int root) {
    vector<int> keep;
    nodesOf(root, keep);
    vector<int> id(tn_.size(), -1);
    for (size_t i = 0; i < keep.size(); i++) id[keep[i]] = i;
    vector<TN> nt(keep.size());
    for (size_t i = 0; i < keep.size(); i++) {
        nt[i] = std::move(tn_[keep[i]]);
        nt[i].l = nt[i].l >= 0 ? id[nt[i].l] : -1;
        nt[i].r = nt[i].r >= 0 ? id[nt[i].r] : -1;
        nt[i].par = nt[i].par >= 0 ? id[nt[i].par] : -1;
    }
    tn_.swap(nt);
    return id[root];
}
// subtree rebuilds with randomized cut choices; returns the (possibly new) root
static double lnsTemp_ = 0;  // annealing temperature at the start of a call (0 = descent)
static int lns(int root, double endT, int* acc, int* its) {
    vector<int> nodes;
    root = compact(root);
    const double tS = elapsed(), span = max(1e-9, endT - tS);
    vector<TN> bestT;
    int bestR = -1;
    double bestV = tn_[root].val;
    for (int it = 0; elapsed() < endT; it++) {
        if (tn_.size() > 60000) root = compact(root), nodes.clear(), nodesOf(root, nodes);
        if (it % 16 == 0) nodes.clear(), nodesOf(root, nodes);
        int v = nodes[irand(nodes.size())];
        if (tn_[v].kr < 2 || tn_[v].kr > krMax_ || tn_[v].P.empty()) continue;
        (*its)++;
        offs_ = urand(), noise_ = 0.3 * urand(), tol_ = 1 + 6 * urand();
        rpos_ = urand() < rposP_;
        if (rpos_) tol_ = 1e9;
        calls_ = 0, callCap_ = 6LL * tn_[v].kr;
        vector<int> P = tn_[v].P, Q = tn_[v].Q;
        int w = build(P, Q, tn_[v].kr);
        rpos_ = false;
        double temp = lnsTemp_ * (1 - (elapsed() - tS) / span);
        bool better = tn_[w].val > tn_[v].val + 1e-9;
        if (!better && temp > 0 && tn_[w].val > tn_[v].val - 1e-9 + temp * log(urand() + 1e-300)) better = true;
        if (!better) {
            freeSub(w);
            continue;
        }
        (*acc)++;
        int p = tn_[v].par;
        tn_[w].par = p;
        if (p < 0) root = w;
        else (tn_[p].l == v ? tn_[p].l : tn_[p].r) = w;
        double dv = tn_[w].val - tn_[v].val;
        int dz = tn_[w].zones - tn_[v].zones;
        freeSub(v);
        for (int u = p; u >= 0; u = tn_[u].par) tn_[u].val += dv, tn_[u].zones += dz;
        nodes.clear(), nodesOf(root, nodes);
        if (lnsTemp_ > 0) {
            if (tn_[root].val > bestV + 1e-9) {
                root = compact(root), nodes.clear(), nodesOf(root, nodes);
                bestT = tn_, bestR = root, bestV = tn_[root].val;
            }
        }
    }
    if (lnsTemp_ > 0 && bestR >= 0 && bestV > tn_[root].val) tn_.swap(bestT), root = bestR;
    return root;
}
}  // namespace eqx

static int eqxHintK = 0;  // zone count of the last exact plan (later calls start around it)
static vector<int> eqExact(double endTime, double* outVal) {
    *outVal = -1e300;
    int maxT = 0;
    for (int s = 0; s < n; s++) maxT = max(maxT, ntask[s]);
    if (maxT > 2 || n < 4) return {};
    eqx::NCL = maxT + 1;
    vector<int> Nc(eqx::NCL, 0);
    for (int s = 0; s < n; s++) Nc[ntask[s]]++;
    // offices with distinct positions
    vector<int> offs;
    for (int o = 0; o < K; o++) {
        if (maxSize[o] <= 0) continue;
        bool dup = false;
        for (int q : offs) dup |= px[n + q] == px[n + o] && py[n + q] == py[n + o] && maxSize[q] >= maxSize[o];
        if (!dup) offs.push_back(o);
    }
    if (offs.size() < 2) return {};
    vector<int> caps;
    for (int o : offs) caps.push_back(maxSize[o]);
    sort(caps.begin(), caps.end(), greater<int>());
    double avgCost = 0, avgRew = 0;
    for (int o : offs) avgCost += ocost[o];
    avgCost /= offs.size();
    for (int s = 0; s < n; s++) avgRew += rew[s];
    avgRew /= n;
    double dNear = 0;  // mean distance to the nearest office (all offices open)
    for (int s = 0; s < n; s++) {
        double md = 1e300;
        for (int o : offs) md = min(md, dist[o][s]);
        dNear += md;
    }
    dNear /= n;
    // compositions per zone count
    struct Plan {
        int k;
        vector<int> z;
        double est;
        int sh;  // window shift: zones of s - sh .. s - sh + A sites (A > 0)
    };
    vector<Plan> plans;
    int kLo = max(2, (int)ceil(0.9 * n / caps[0]));
    int kHi = min({(int)offs.size(), n / 2, (int)ceil(1.8 * n / caps[caps.size() / 2])});
    static const double rhos[4] = {0.0, 0.004, 0.012, 0.025};
    for (int k = kLo; k <= kHi; k++)
        for (double rho : rhos) {
            vector<int> z(eqx::NCL);
            int s = 0;
            for (int c = 0; c < eqx::NCL; c++) z[c] = max(0, (int)floor(Nc[c] * (1 - rho) / k)), s += z[c];
            int cap = caps[k - 1];
            while (s > cap) {  // trim the largest class
                int bc = 0;
                for (int c = 1; c < eqx::NCL; c++)
                    if (z[c] > z[bc]) bc = c;
                z[bc]--, s--;
            }
            if (s < 2) continue;
            double cov = (double)k * s;
            double est = cov * (avgRew - dNear * sqrt((double)offs.size() / k)) - k * avgCost;
            bool dupP = false;
            for (auto& q : plans) dupP |= q.k == k && q.z == z;
            int elig = 0;
            for (int o : offs) elig += maxSize[o] >= s;
            if (!dupP && elig >= k) {
                plans.push_back({k, z, est, 0});
                static const int shOn = 1;
                if (shOn && A >= 2) plans.push_back({k, z, est - 1e-6, A / 2});
                if (shOn && A >= 1) plans.push_back({k, z, est - 2e-6, A});
            }
        }
    if (plans.empty()) return {};
    static const double tolE = 3;
    static const int ncE = 12;
    static const int pairE = 1;
    static const int capE = 12;
    static const double lnsF = 0.5;  // share of the time for subtree rebuilds
    eqx::ncand_ = ncE;
    eqx::trK_ = 4;
    eqx::trN_ = 3;
    eqx::wq_ = 1.0;
    eqx::krMax_ = 16;
    eqx::rposP_ = 0.5;
    eqx::lnsTemp_ = 0;
    eqx::scMode_ = 2;
    const double t00 = elapsed();
    const double planEnd = t00 + (1 - lnsF) * (endTime - t00);
    eqx::end_ = endTime + 0.1 * (endTime - t00);
    eqpart::end_ = eqx::end_;
    for (int j = 0; j < eqpart::ND; j++) eqpart::cs_[j] = cos(M_PI * j / eqpart::ND), eqpart::sn_[j] = sin(M_PI * j / eqpart::ND);
    // schedule: a coarse grid of zone counts (middle reserve), then every plan near the best zone
    // count (by estimate), then randomized variants of the best three
    vector<int> sched;
    if (eqxHintK > 0) {  // a later call: the zone counts near the earlier best first
        for (int i = 0; i < (int)plans.size(); i++)
            if (abs(plans[i].k - eqxHintK) <= 2) sched.push_back(i);
        sort(sched.begin(), sched.end(), [&](int a, int b) { return plans[a].est > plans[b].est; });
        if ((int)sched.size() > 6) sched.resize(6);
    } else {  // zone counts around full coverage at the median capacity, outwards
        int kFull = (int)ceil((double)n / caps[caps.size() / 2]);
        for (double f : {1.0, 1.08, 1.16, 0.92, 1.25, 1.04, 1.12, 0.84, 1.35}) {
            int k = (int)lround(f * kFull);
            vector<int> ofk;
            for (int i = 0; i < (int)plans.size(); i++)
                if (plans[i].k == k && plans[i].sh == (A >= 2 ? A / 2 : 0)) ofk.push_back(i);
            int pk = ofk.empty() ? -1 : ofk[min<int>(1, ofk.size() - 1)];
            if (pk >= 0 && find(sched.begin(), sched.end(), pk) == sched.end()) sched.push_back(pk);
        }
    }
    vector<char> tried(plans.size(), 0);
    vector<pair<double, int>> pv;  // (tree value, plan index)
    // the best trees so far (each with its own node store)
    struct Kept {
        double v;
        int plan, root;
        vector<eqx::TN> tree;
        int sc;
    };
    vector<Kept> kept;
    static const int keepN = 4;
    size_t sp = 0;
    int phase = 1, built = 0;
    auto setPlan = [&](int pi) {
        eqx::z_ = plans[pi].z;
        eqx::s_ = 0, eqx::T_ = 0;
        for (int c = 0; c < eqx::NCL; c++) eqx::s_ += plans[pi].z[c], eqx::T_ += c * plans[pi].z[c];
        eqx::s_ = max(1, eqx::s_ - plans[pi].sh);
    };
    for (int it = 0; elapsed() < planEnd; it++) {
        int pi = -1;
        eqx::offs_ = 0, eqx::noise_ = 0, eqx::tol_ = tolE;
        if (phase == 1 && sp >= sched.size()) {
            phase = 2;
            if (pv.empty()) break;
            double top = -1e300;
            for (auto& q : pv) top = max(top, q.first);
            if (top <= 0) break;  // no grid plan has a profitable zone: not this family
            sort(pv.begin(), pv.end(), greater<pair<double, int>>());
            // the zone counts of the two best grid plans (when apart), alternating
            int kb = plans[pv[0].second].k, kb2 = -100;
            for (auto& q : pv)
                if (abs(plans[q.second].k - kb) > 4) {
                    kb2 = plans[q.second].k;
                    break;
                }
            vector<int> near[2];
            for (int i = 0; i < (int)plans.size(); i++) {
                if (tried[i]) continue;
                if (abs(plans[i].k - kb) <= 3) near[0].push_back(i);
                else if (abs(plans[i].k - kb2) <= 2) near[1].push_back(i);
            }
            for (auto& v : near) sort(v.begin(), v.end(), [&](int a, int b) { return plans[a].est > plans[b].est; });
            sched.clear(), sp = 0;
            for (size_t i = 0; i < max(near[0].size(), near[1].size()); i++) {
                if (i < near[0].size()) sched.push_back(near[0][i]);
                if (i < near[1].size() && i % 2 == 0) sched.push_back(near[1][i]);
            }
        }
        if (phase == 2 && sp >= sched.size()) phase = 3;
        if (phase <= 2) pi = sched[sp++];
        else {
            if (pv.empty()) break;
            sort(pv.begin(), pv.end(), greater<pair<double, int>>());
            pi = pv[irand(min<int>(pv.size(), 3))].second;
            eqx::offs_ = urand(), eqx::noise_ = 0.05 * urand();
            eqx::tol_ = tolE * (0.5 + 1.5 * urand());
        }
        tried[pi] = 1;
        setPlan(pi);
        eqx::scCur_ = eqx::scMode_ == 2 ? (phase == 3 ? irand(2) : it % 2) : eqx::scMode_;
        int k = plans[pi].k, s = eqx::s_;
        double t0 = elapsed();
        vector<int> P(n), Q;
        for (int i = 0; i < n; i++) P[i] = i;
        for (int o : offs)
            if (maxSize[o] >= s) Q.push_back(o);
        if ((int)Q.size() < k) continue;
        eqx::tn_.clear();
        eqx::calls_ = 0, eqx::callCap_ = (long long)capE * k;
        int root = eqx::build(P, Q, k);
        double v = eqx::tn_[root].val;
        built++;
        if (szDebug && it < 60)
            fprintf(stderr, "eqx: calls=%lld k=%d s=%d T=%d zones=%d tree %.4f (%.2fs)\n", eqx::calls_, k, s, eqx::T_, eqx::tn_[root].zones, v, elapsed() - t0);
        pv.push_back({v, pi});
        if ((int)kept.size() < keepN || v > kept.back().v) {
            if ((int)kept.size() >= keepN) kept.pop_back();
            kept.push_back({v, pi, root, eqx::tn_, eqx::scCur_});
            sort(kept.begin(), kept.end(), [](const Kept& a, const Kept& b) { return a.v > b.v; });
        }
    }
    if (kept.empty() || kept[0].v <= 0) return {};
    // subtree rebuilds: a slice for each kept tree, then the rest for the best of them
    {
        double L = max(0.0, endTime - elapsed());
        int nk = kept.size();
        double slice = nk > 1 ? 0.6 * L / nk : 0;
        for (int i = 0; i < nk && nk > 1; i++) {
            setPlan(kept[i].plan);
            eqx::scCur_ = kept[i].sc;
            eqx::tn_.swap(kept[i].tree);
            int acc = 0, its = 0;
            double v0 = eqx::tn_[kept[i].root].val;
            kept[i].root = eqx::lns(kept[i].root, elapsed() + slice, &acc, &its);
            kept[i].v = eqx::tn_[kept[i].root].val;
            if (szDebug) fprintf(stderr, "eqx lns slice: k=%d s=%d tree %.4f -> %.4f (%d/%d)\n", plans[kept[i].plan].k, eqx::s_, v0, kept[i].v, acc, its);
            eqx::tn_.swap(kept[i].tree);
        }
        sort(kept.begin(), kept.end(), [](const Kept& a, const Kept& b) { return a.v > b.v; });
    }
    int bPlan = kept[0].plan;
    eqxHintK = plans[bPlan].k;
    setPlan(bPlan);
    eqx::tn_.swap(kept[0].tree);
    eqx::scCur_ = kept[0].sc;
    int root = kept[0].root, acc = 0, its = 0;
    kept.clear();
    double v0 = eqx::tn_[root].val;
    root = eqx::lns(root, endTime, &acc, &its);
    if (szDebug) fprintf(stderr, "eqx lns: plans=%d k=%d s=%d tree %.4f -> %.4f (%d/%d rebuilds)\n", built, plans[bPlan].k, eqx::s_, v0, eqx::tn_[root].val, acc, its);
    // sibling re-cuts by value, then the zones
    vector<int> lf;
    eqx::leavesOf(root, lf);
    vector<eqpart::Leaf> leaves;
    for (int v : lf) leaves.push_back({eqx::tn_[v].P, eqx::tn_[v].Q});
    eqpart::pairs_.clear();
    for (size_t i = 0; i + 1 < lf.size(); i++) {
        int p = eqx::tn_[lf[i]].par;
        if (p >= 0 && p == eqx::tn_[lf[i + 1]].par && eqx::tn_[p].kr == 2) eqpart::pairs_.push_back({(int)i, (int)i + 1});
    }
    int s = eqx::s_, T = eqx::T_, k = plans[bPlan].k;
    vector<double> lv(leaves.size());
    int o;
    for (size_t li = 0; li < leaves.size(); li++) lv[li] = eqpart::leafBest(leaves[li].P, leaves[li].Q, s, T, &o, nullptr);
    for (int pass = 0; pass < pairE && elapsed() < eqx::end_; pass++)
        if (!eqpart::pairImprove(leaves, lv, s, T)) break;
    vector<int> asg(AS, -1), sel;
    for (size_t li = 0; li < leaves.size(); li++) {
        eqpart::leafBest(leaves[li].P, leaves[li].Q, s, T, &o, &sel);
        if (o >= 0)
            for (int i : sel) asg[i] = o;
    }
    eqx::tn_.clear(), eqx::tn_.shrink_to_fit();
    State st = fromAsg(asg);
    bool ok = countFeasible(st) && validateFull(st).empty();
    // too few workers for every zone: drop the least valuable zones until the cover exists
    for (int drop = 0; !ok && drop < k / 3 && countFeasible(st) && elapsed() < eqx::end_; drop++) {
        int wo = -1;
        double wv = 1e300;
        for (int q = 0; q < K; q++) {
            if (st.cnt[q] == 0) continue;
            double v = -ocost[q];
            for (int i : st.mem[q]) v += rew[i] - dist[q][i];
            if (v < wv) wv = v, wo = q;
        }
        if (wo < 0) break;
        for (int i = 0; i < n; i++)
            if (asg[i] == wo) asg[i] = -1;
        st = fromAsg(asg);
        ok = countFeasible(st) && validateFull(st).empty();
    }
    if (!ok) {
        if (szDebug) fprintf(stderr, "eqx: plan rejected (%s)\n", validateFull(st).c_str());
        return {};
    }
    double bestV = trueObjective(st);
    vector<int> best = st.asg;
    eqPolish(st, endTime + 0.5 * (endTime - t00));
    double v = trueObjective(st);
    if (szDebug) fprintf(stderr, "eqx polish %.4f -> %.4f\n", bestV, v);
    if (countFeasible(st) && validateFull(st).empty() && v > bestV) bestV = v, best = st.asg;
    *outVal = bestV;
    return best;
}

// ---- r29: portfolio of simple structures as a short start phase (tight count balance + big alpha traps)
namespace r29s {
typedef bitset<256> Mask;
int n, K, W, NP, A; double alpha, EPS, SPAN;
vector<double> X, Y, rew, cost; vector<int> ms, nt; vector<vector<double>> D;
vector<Mask> sm, wm; int NSK = 0;
mt19937_64 rng(1);
double urand() { return (rng() >> 11) * (1.0 / 9007199254740992.0); }
chrono::steady_clock::time_point T0; double TL;
bool lsTp = false;  // levelSearchG runs inside the team phase (tp): its cap is the phase clock
double el() { return chrono::duration<double>(chrono::steady_clock::now() - T0).count(); }
inline double prof(int o, int s) { return rew[s] - D[o][s]; }
inline double ed2(int a, int b) { double dx = X[a] - X[b], dy = Y[a] - Y[b]; return dx * dx + dy * dy; }

// ---------- grid over all points
int G; double gx0, gy0, gcs; vector<vector<int>> gcell;
inline int gidx(double v) { return (int)max(0.0, min((double)(G - 1), v)); }  // clamp in double before the cast
void buildGrid() {
  double x0 = 1e300, x1 = -1e300, y0 = 1e300, y1 = -1e300;
  for (int i = 0; i < NP; i++) x0 = min(x0, X[i]), x1 = max(x1, X[i]), y0 = min(y0, Y[i]), y1 = max(y1, Y[i]);
  G = max(1, (int)sqrt(NP / 3.0)); gx0 = x0; gy0 = y0; gcs = max(max(x1 - x0, y1 - y0), max(1e-12, 1e3 * EPS)) / G * (1 + 1e-9);
  gcell.assign(G * G, {});
  for (int i = 0; i < NP; i++) { int cx = gidx((X[i] - x0) / gcs), cy = gidx((Y[i] - y0) / gcs); gcell[cx * G + cy].push_back(i); }
}
inline double cr(int o, int a, int b) { return (X[a] - X[o]) * (Y[b] - Y[o]) - (Y[a] - Y[o]) * (X[b] - X[o]); }
void hullOf(vector<int> pts, vector<int>& H) {
  sort(pts.begin(), pts.end(), [](int a, int b) { return X[a] < X[b] || (X[a] == X[b] && Y[a] < Y[b]); });
  pts.erase(unique(pts.begin(), pts.end(), [](int a, int b) { return X[a] == X[b] && Y[a] == Y[b]; }), pts.end());
  H.clear(); if (pts.size() <= 2) { H = pts; return; }
  vector<int> h(2 * pts.size()); int k = 0;
  for (size_t i = 0; i < pts.size(); i++) { while (k >= 2 && cr(h[k - 2], h[k - 1], pts[i]) <= 0) k--; h[k++] = pts[i]; }
  for (int i = (int)pts.size() - 2, t = k + 1; i >= 0; i--) { while (k >= t && cr(h[k - 2], h[k - 1], pts[i]) <= 0) k--; h[k++] = pts[i]; }
  h.resize(k - 1); H = h;
}
bool inHull(const vector<int>& H, int p) {
  if (H.size() == 1) return fabs(X[p] - X[H[0]]) <= EPS && fabs(Y[p] - Y[H[0]]) <= EPS;
  if (H.size() == 2) { int a = H[0], b = H[1]; double L = sqrt(ed2(a, b)); if (fabs(cr(a, b, p)) / L > EPS) return false;
    double t = ((X[p] - X[a]) * (X[b] - X[a]) + (Y[p] - Y[a]) * (Y[b] - Y[a])) / L; return t >= -EPS && t <= L + EPS; }
  for (size_t i = 0; i < H.size(); i++) { int a = H[i], b = H[(i + 1) % H.size()]; double L = sqrt(ed2(a, b)); if (cr(a, b, p) / L < -EPS) return false; }
  return true;
}
void covOfH(const vector<int>& H, vector<int>& cov) {
  cov.clear(); double x0 = 1e300, x1 = -1e300, y0 = 1e300, y1 = -1e300;
  for (int h : H) x0 = min(x0, X[h]), x1 = max(x1, X[h]), y0 = min(y0, Y[h]), y1 = max(y1, Y[h]);
  int cx0 = gidx((x0 - EPS - gx0) / gcs), cx1 = gidx((x1 + EPS - gx0) / gcs);
  int cy0 = gidx((y0 - EPS - gy0) / gcs), cy1 = gidx((y1 + EPS - gy0) / gcs);
  for (int cx = cx0; cx <= cx1; cx++) for (int cy = cy0; cy <= cy1; cy++) for (int p : gcell[cx * G + cy]) {
    if (X[p] < x0 - EPS || X[p] > x1 + EPS || Y[p] < y0 - EPS || Y[p] > y1 + EPS) continue;
    if (inHull(H, p)) cov.push_back(p);
  }
  sort(cov.begin(), cov.end());
}
void covOf(int o, const vector<int>& sites, vector<int>& cov, vector<int>* Hout = nullptr) {
  vector<int> pts = sites; pts.push_back(n + o); vector<int> H; hullOf(pts, H); covOfH(H, cov); if (Hout) *Hout = H;
}

// ---------- solutions
struct Sol { vector<vector<int>> mem, wk; double val = -1e300; string tag; };
Mask teamMask(const vector<int>& w) { Mask m; for (int x : w) m |= wm[x]; return m; }

double evalFull(const Sol& s, string* why = nullptr) {
  vector<int> cc(NP, 0), cov; vector<char> useS(n, 0), useW(W, 0);
  double v = 0; int lmn = INT_MAX, lmx = INT_MIN, cmn = INT_MAX, cmx = INT_MIN; bool any = false;
  for (int o = 0; o < K; o++) {
    if (s.mem[o].empty()) continue;
    any = true;
    if ((int)s.mem[o].size() > ms[o]) { if (why) *why = "cap"; return -1e300; }
    Mask m = teamMask(s.wk[o]);
    for (int w : s.wk[o]) { if (useW[w]) { if (why) *why = "dupw"; return -1e300; } useW[w] = 1; }
    int L = 0;
    for (int x : s.mem[o]) { if (useS[x]) { if (why) *why = "dups"; return -1e300; } useS[x] = 1;
      if ((sm[x] & ~m).any()) { if (why) *why = "skill"; return -1e300; } L += nt[x]; v += prof(o, x); }
    v -= cost[o]; lmn = min(lmn, L); lmx = max(lmx, L); cmn = min(cmn, (int)s.mem[o].size()); cmx = max(cmx, (int)s.mem[o].size());
    covOf(o, s.mem[o], cov); for (int p : cov) if (++cc[p] > 1) { if (why) *why = "hull"; return -1e300; }
  }
  if (!any) return 0;
  if (cmx - cmn > A) { if (why) *why = "bal"; return -1e300; }
  return v - alpha * (lmx - lmn);
}

string summary(const Sol& s) {
  ostringstream os; int k = 0, served = 0; vector<int> L, C; vector<int> tw;
  for (int o = 0; o < K; o++) if (!s.mem[o].empty()) { k++; served += s.mem[o].size(); int l = 0; for (int x : s.mem[o]) l += nt[x]; L.push_back(l); C.push_back(s.mem[o].size()); tw.push_back(s.wk[o].size()); }
  os << "k=" << k << " served=" << served << "/" << n << " loads=";
  for (size_t i = 0; i < L.size(); i++) os << (i ? "," : "") << L[i];
  os << " cnts="; for (size_t i = 0; i < C.size(); i++) os << (i ? "," : "") << C[i];
  os << " team="; for (size_t i = 0; i < tw.size(); i++) os << (i ? "," : "") << tw[i];
  return os.str();
}

// removal-only hull repair
void repairHull(vector<vector<int>>& mem) {
  vector<vector<int>> cov(K); vector<int> cc(NP, 0);
  for (int o = 0; o < K; o++) if (!mem[o].empty()) { covOf(o, mem[o], cov[o]); for (int p : cov[o]) cc[p]++; }
  for (int it = 0; it < 100000; it++) {
    if (el() > TL) { for (auto& m : mem) m.clear(); return; }  // out of time: give the plan up
    int bad = -1; for (int p = 0; p < NP; p++) if (cc[p] > 1) { bad = p; break; }
    if (bad < 0) return;
    int bz = -1; double bl = 1e300; vector<int> brem;
    vector<int> zs; for (int o = 0; o < K; o++) if (!mem[o].empty() && binary_search(cov[o].begin(), cov[o].end(), bad)) zs.push_back(o);
    for (int z : zs) {
      if (bad == n + z) continue;
      double ux = X[bad] - X[n + z], uy = Y[bad] - Y[n + z]; double ul = hypot(ux, uy); if (ul <= EPS) continue;
      vector<int> rem; double loss = 0;
      for (int s : mem[z]) if ((X[s] - X[bad]) * ux + (Y[s] - Y[bad]) * uy >= -EPS * ul) rem.push_back(s), loss += max(0.0, prof(z, s)) + 1e-12;
      if (loss < bl) bl = loss, bz = z, brem = rem;
    }
    if (bz < 0) bz = zs.back(), brem = mem[bz];  // cannot separate: close a zone
    if (brem.empty()) brem = mem[bz];  // no progress from the cut (tolerance): close the zone
    for (int p : cov[bz]) cc[p]--;
    vector<int> keep; sort(brem.begin(), brem.end());
    for (int s : mem[bz]) if (!binary_search(brem.begin(), brem.end(), s)) keep.push_back(s);
    mem[bz] = keep; cov[bz].clear();
    if (!keep.empty()) { covOf(bz, keep, cov[bz]); for (int p : cov[bz]) cc[p]++; }
  }
}

// ---------- level search: given per-office eligible candidate sites (any subset is hull-valid), choose sites
struct LevelRes { double val = -1e300; vector<vector<int>> mem; int T = -1; };
// select for one office with load <= T and count <= cap; two greedy orders; returns profit
bool NEG = true;
static void pick(int o, const vector<int>& cand_ratio, const vector<int>& cand_prof, const vector<int>& cand_neg, int T, int cap, vector<int>& out) {
  vector<int> a, b, c; double pa = 0, pb = 0, pc = 0; int la = 0, lb = 0, lc = 0;
  if (NEG && !cand_neg.empty()) {
    for (int s : cand_ratio) { if ((int)c.size() >= cap) break; if (lc + nt[s] <= T) c.push_back(s), lc += nt[s], pc += prof(o, s); }
    for (int s : cand_neg) { if ((int)c.size() >= cap || lc >= T) break; if (lc + nt[s] <= T) c.push_back(s), lc += nt[s], pc += prof(o, s); }
  }
  for (int s : cand_ratio) { if ((int)a.size() >= cap) break; if (la + nt[s] <= T) a.push_back(s), la += nt[s], pa += prof(o, s); }
  for (int s : cand_prof) { if ((int)b.size() >= cap) break; if (lb + nt[s] <= T) b.push_back(s), lb += nt[s], pb += prof(o, s); }
  out = pa >= pb ? a : b;
  if (!c.empty()) { double sa = max(pa + alpha * la, pb + alpha * lb); if (pc + alpha * lc > sa + 1e-12) out = c; }
}
// r32: equal count AND equal load. Every open zone takes exactly c sites with task load exactly T. With no
// task-free sites (or few) the greedy level picks of levelSearch cannot equalize loads at a common count, so
// plans with one more office score far too low there (s1-like A=0 traps: 1.68x single kept, 2.41x exists).
// Per zone and c: Lagrangian curve f(T) = max profit of c sites with load T (keys prof - lam*nt, top c),
// common T maximizing sum f_i(T); the chosen T is materialized exactly (lam search + load-raising swaps).
static const bool eqLvOn = true;
static void topC(int o, const vector<int>& cand, int c, double lam, vector<pair<double, int>>& buf, int& L, double& P, vector<int>* out) {
  buf.clear(); for (int s : cand) buf.push_back({prof(o, s) - lam * nt[s], s});
  nth_element(buf.begin(), buf.begin() + (c - 1), buf.end(), [](const pair<double, int>& a, const pair<double, int>& b) { return a.first > b.first || (a.first == b.first && a.second < b.second); });
  L = 0; P = 0; if (out) out->clear();
  for (int j = 0; j < c; j++) { int s = buf[j].second; L += nt[s]; P += prof(o, s); if (out) out->push_back(s); }
}
// exact pick for one zone: c sites, load as close to T as possible from below, then raise it by swaps
static void exactPick(int o, const vector<int>& cand, int c, int T, double mp, vector<pair<double, int>>& buf, vector<int>& sel, int& L, double& P) {
  double lo = -10 * mp - 1, hi = 10 * mp + 1;  // L(lo) = max load, L(hi) = min load
  int l; double pv;
  for (int it = 0; it < 40; it++) { double mid = 0.5 * (lo + hi); topC(o, cand, c, mid, buf, l, pv, nullptr); if (l <= T) hi = mid; else lo = mid; }
  topC(o, cand, c, hi, buf, L, P, &sel);
  if (L >= T) return;
  vector<char> in(n, 0); for (int s : sel) in[s] = 1;
  int maxNt = 0; for (int s : cand) maxNt = max(maxNt, nt[s]);
  vector<int> bo(maxNt + 1), bi(maxNt + 1);
  for (int step = 0; step < 64 && L < T; step++) {
    fill(bo.begin(), bo.end(), -1); fill(bi.begin(), bi.end(), -1);
    for (int s : cand) { int v = nt[s];
      if (in[s]) { if (bo[v] < 0 || prof(o, s) < prof(o, bo[v])) bo[v] = s; }
      else if (bi[v] < 0 || prof(o, s) > prof(o, bi[v])) bi[v] = s; }
    int ba = -1, bb = -1; double bg = -1e300; int need = T - L;
    for (int a = 0; a <= maxNt; a++) if (bo[a] >= 0) for (int b = a + 1; b <= maxNt && b - a <= need; b++) if (bi[b] >= 0) {
      double g = prof(o, bi[b]) - prof(o, bo[a]) + 1e-9 * (b - a);  // prefer the larger step on ties
      if (g > bg) bg = g, ba = bo[a], bb = bi[b]; }
    if (ba < 0) break;
    in[ba] = 0; in[bb] = 1; L += nt[bb] - nt[ba]; P += prof(o, bb) - prof(o, ba);
    for (int& s : sel) if (s == ba) { s = bb; break; }
  }
}
LevelRes eqLevel(const vector<int>& open, const vector<vector<int>>& elig) {
  LevelRes best; int k = open.size(); if (k < 2 || alpha <= 0) return best;
  vector<vector<int>> cand(k); int cmax = INT_MAX; double mp = 0;
  for (int i = 0; i < k; i++) { int o = open[i];
    if (el() > TL) return best;
    for (int s : elig[i]) if (prof(o, s) > 0) cand[i].push_back(s), mp = max(mp, prof(o, s));
    cmax = min(cmax, min(ms[o], (int)cand[i].size())); }
  if (cmax < 1 || mp <= 0) return best;
  vector<int> cs = {cmax};
  for (double f : {0.93, 0.85}) { int c = (int)(f * cmax); if (c >= 1 && c != cs.back()) cs.push_back(c); }
  vector<double> lams; lams.push_back(10 * mp + 1); for (int j = 0; j <= 48; j++) lams.push_back(1.05 * mp * (1 - 2.0 * j / 48)); lams.push_back(-10 * mp - 1);
  vector<pair<double, int>> buf; double costSum = 0; for (int o : open) costSum += cost[o];
  for (int c : cs) {
    if (el() > TL) break;
    vector<vector<pair<int, double>>> hull(k); int Tlo = INT_MIN, Thi = INT_MAX;
    for (int i = 0; i < k; i++) {
      if (el() > TL) return best;
      vector<pair<int, double>> pts;
      for (double lam : lams) { int L; double P; topC(open[i], cand[i], c, lam, buf, L, P, nullptr); pts.push_back({L, P}); }
      sort(pts.begin(), pts.end());
      vector<pair<int, double>> u;  // max P per L, then upper concave hull
      for (auto& q : pts) { if (!u.empty() && u.back().first == q.first) { u.back().second = max(u.back().second, q.second); continue; } u.push_back(q); }
      vector<pair<int, double>> h;
      for (auto& q : u) {
        while (h.size() >= 2) { auto& a = h[h.size() - 2]; auto& b = h.back();
          double crs = (double)(b.first - a.first) * (q.second - a.second) - (b.second - a.second) * (double)(q.first - a.first);
          if (crs >= 0) h.pop_back(); else break; }
        h.push_back(q); }
      hull[i] = h; Tlo = max(Tlo, h.front().first); Thi = min(Thi, h.back().first);
    }
    if (Tlo > Thi) continue;
    vector<int> Ts = {Tlo, Thi}; for (auto& h : hull) for (auto& q : h) if (q.first > Tlo && q.first < Thi) Ts.push_back(q.first);
    sort(Ts.begin(), Ts.end()); Ts.erase(unique(Ts.begin(), Ts.end()), Ts.end());
    int bT = -1; double bv = -1e300;
    for (int T : Ts) { double v = -costSum;
      for (auto& h : hull) { size_t j = 0; while (j + 1 < h.size() && h[j + 1].first < T) j++;
        if (h[j].first >= T || j + 1 >= h.size()) v += h[j].second;
        else { auto& a = h[j]; auto& b = h[j + 1]; v += a.second + (b.second - a.second) * (double)(T - a.first) / (double)(b.first - a.first); } }
      if (v > bv) bv = v, bT = T; }
    if (bT < 0 || bv <= best.val) continue;
    LevelRes r; r.mem.assign(K, {}); r.T = bT; double v = -costSum; int lmn = INT_MAX, lmx = INT_MIN;
    if (el() > TL) break;
    for (int i = 0; i < k; i++) { vector<int> sel; int L; double P; exactPick(open[i], cand[i], c, bT, mp, buf, sel, L, P);
      v += P; lmn = min(lmn, L); lmx = max(lmx, L); r.mem[open[i]] = sel; }
    r.val = v - alpha * (lmx - lmn);
    if (r.val > best.val) best = r;
  }
  return best;
}
LevelRes levelSearchG(const vector<int>& open, const vector<vector<int>>& elig, bool fine);
LevelRes levelSearch(const vector<int>& open, const vector<vector<int>>& elig, bool fine = false) {
  LevelRes b = levelSearchG(open, elig, fine);
  if (eqLvOn) { LevelRes e = eqLevel(open, elig); if (e.val > b.val + 1e-9 * max(1.0, fabs(b.val))) b = e; }
  return b;
}
LevelRes levelSearchG(const vector<int>& open, const vector<vector<int>>& elig, bool fine) {
  LevelRes best; int k = open.size(); if (!k) return best;
  vector<vector<int>> cr_(k), cp_(k), cn_(k); int maxL = 0;
  for (int i = 0; i < k; i++) {
    int o = open[i]; vector<int> c; for (int s : elig[i]) if (prof(o, s) > 0) c.push_back(s);
    cp_[i] = c; sort(cp_[i].begin(), cp_[i].end(), [&](int a, int b) { return prof(o, a) > prof(o, b); });
    cr_[i] = c; sort(cr_[i].begin(), cr_[i].end(), [&](int a, int b) { double ka = prof(o, a) / max(nt[a], 0) , kb = prof(o, b) / max(nt[b], 0);
      if (nt[a] == 0 || nt[b] == 0) { if ((nt[a] == 0) != (nt[b] == 0)) return nt[a] == 0; return prof(o, a) > prof(o, b); } return ka > kb; });
    for (int s : elig[i]) if (nt[s] > 0 && prof(o, s) <= 0 && prof(o, s) > -alpha * nt[s]) cn_[i].push_back(s);
    sort(cn_[i].begin(), cn_[i].end(), [&](int a, int b) { return prof(o, a) / nt[a] > prof(o, b) / nt[b]; });
    int L = 0, c2 = 0; for (int s : cp_[i]) { if (c2 >= ms[o]) break; L += nt[s]; c2++; } maxL = max(maxL, L);
  }
  vector<int> Ts;
  if (maxL <= 600 || fine) for (int t = 0; t <= maxL; t++) Ts.push_back(t);
  else { for (int i = 0; i <= 400; i++) Ts.push_back((int)llround((double)maxL * i / 400)); Ts.erase(unique(Ts.begin(), Ts.end()), Ts.end()); }
  vector<vector<int>> sel(k), sel0(k); vector<double> P(k), P0(k); vector<int> L(k), C(k), C0(k);
  vector<vector<double>> pp(k), pp0(k); vector<vector<int>> pl(k);
  auto prep = [&](int i, vector<int>& sl, double& Pi, int& Li, int& Ci, vector<double>& ppi, vector<int>* pli) {
    int o = open[i]; Pi = 0; Li = 0; for (int s : sl) Pi += prof(o, s), Li += nt[s]; Ci = sl.size();
    vector<int> srt = sl; sort(srt.begin(), srt.end(), [&](int a, int b) { return prof(o, a) < prof(o, b); });
    ppi.assign(Ci + 1, 0); if (pli) pli->assign(Ci + 1, 0);
    for (int j = 0; j < Ci; j++) { ppi[j + 1] = ppi[j] + prof(o, srt[j]); if (pli) (*pli)[j + 1] = (*pli)[j] + nt[srt[j]]; }
  };
  auto build = [&](const vector<int>& who, const vector<char>& zero, int cmn) {
    vector<vector<int>> mm(K);
    for (int i : who) { int o = open[i]; vector<int> m = zero[i] ? sel0[i] : sel[i];
      sort(m.begin(), m.end(), [&](int a, int b) { return prof(o, a) > prof(o, b); }); if ((int)m.size() > cmn + A) m.resize(cmn + A); mm[o] = m; }
    return mm;
  };
  for (int i = 0; i < k; i++) { pick(open[i], cr_[i], cp_[i], cn_[i], 0, ms[open[i]], sel0[i]); int l0; prep(i, sel0[i], P0[i], l0, C0[i], pp0[i], nullptr); }
  auto tryT = [&](int T) {
    for (int i = 0; i < k; i++) { pick(open[i], cr_[i], cp_[i], cn_[i], T, ms[open[i]], sel[i]); prep(i, sel[i], P[i], L[i], C[i], pp[i], &pl[i]); }
    vector<int> ord(k); iota(ord.begin(), ord.end(), 0); sort(ord.begin(), ord.end(), [&](int a, int b) { return L[a] < L[b]; });
    vector<int> sufMin(k + 1, INT_MAX); for (int j = k - 1; j >= 0; j--) sufMin[j] = min(sufMin[j + 1], C[ord[j]]);
    for (int drop = 0; drop < k; drop++) {
      int cmn = sufMin[drop]; if (cmn == 0) continue;
      double v = 0; int lmn = INT_MAX, lmx = INT_MIN;
      for (int j = drop; j < k; j++) { int i = ord[j]; int ex = max(0, C[i] - cmn - A);
        double p = P[i] - pp[i][ex]; int l = L[i] - pl[i][ex]; v += p - cost[open[i]]; lmn = min(lmn, l); lmx = max(lmx, l); }
      v -= alpha * (lmx - lmn);
      if (v > best.val + 1e-12) { vector<int> who(ord.begin() + drop, ord.end()); best.val = v; best.mem = build(who, vector<char>(k, 0), cmn); best.T = T; }
    }
    // mixed: some offices at level 0 (task-free sites only), others at level T; min load = 0
    { vector<char> z(k, 0); vector<int> who; int cmn = INT_MAX;
      for (int i = 0; i < k; i++) { double vf = P[i] - cost[open[i]], v0 = P0[i] - cost[open[i]];
        if (C0[i] > 0 && v0 >= vf && v0 > 0) { z[i] = 1; who.push_back(i); cmn = min(cmn, C0[i]); }
        else if (C[i] > 0 && vf > 0) { who.push_back(i); cmn = min(cmn, C[i]); } }
      bool anyZ = false; for (int i : who) anyZ |= z[i];
      if (anyZ && !who.empty() && cmn > 0) {
        double v = 0; int lmx = 0;
        for (int i : who) { int c = z[i] ? C0[i] : C[i]; int ex = max(0, c - cmn - A);
          if (z[i]) v += P0[i] - pp0[i][ex] - cost[open[i]]; else { v += P[i] - pp[i][ex] - cost[open[i]]; lmx = max(lmx, L[i] - pl[i][ex]); } }
        v -= alpha * lmx;
        if (v > best.val + 1e-12) { best.val = v; best.mem = build(who, z, cmn); best.T = T; }
      }
    }
  };
  // runaway cap: one T costs ~k n log n, so with huge n (ring200k: ~25 ms per T, 400+ T per call, calls in a
  // loop) an unclocked scan overran by minutes. The pre-fork phases (r29, r36, r37) stop at 0.6 x the time limit
  // (real time since the start: they end long before it, even slow big3-like runs keep their full scans); the
  // late team phase (tp) at its own phase clock + 0.5 s (calls take milliseconds at ordinary sizes)
  auto lsLate = [] { return lsTp ? el() > TL + 0.5 : chrono::duration<double>(chrono::steady_clock::now() - ::T0).count() > ::lsCutoff; };
  for (int T : Ts) { if (lsLate()) break; tryT(T); }
  if (!fine && maxL > 600 && best.T >= 0) { int step = max(1, maxL / 400); for (int t = max(0, best.T - step); t <= best.T + step && !lsLate(); t++) tryT(t); }
  return best;
}

// ---------- structure: open set + power weights + teams -> cells -> level search
vector<double> pw;  // power weights per office (global scratch)
void cellsOf(const vector<int>& open, const vector<double>& w, vector<vector<int>>& cell) {
  int k = open.size(); cell.assign(k, {});
  for (int s = 0; s < n; s++) { int bi = -1; double bd = 1e300;
    for (int i = 0; i < k; i++) { double d = ed2(s, n + open[i]) - w[i]; if (d < bd) bd = d, bi = i; }
    cell[bi].push_back(s); }
}
bool ownCell(const vector<int>& open, const vector<double>& w) {
  int k = open.size();
  for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) if (i != j && ed2(n + open[i], n + open[j]) - w[j] < -w[i] - 1e-12 * SPAN * SPAN) return false;
  return true;
}
// team greedy: fractional marginal gain, team size cap
vector<vector<int>> teamGreedy(const vector<int>& open, const vector<vector<int>>& cell, int tcap) {
  int k = open.size(); vector<vector<double>> wsk(k, vector<double>(NSK, 0));
  for (int i = 0; i < k; i++) for (int s : cell[i]) { double p = prof(open[i], s); if (p <= 0 || nt[s] == 0) continue; for (int b = 0; b < NSK; b++) if (sm[s][b]) wsk[i][b] += p / sm[s].count(); }
  vector<vector<int>> team(k); vector<Mask> M(k); vector<char> used(W, 0);
  while (true) {
    int bi = -1, bw = -1; double bg = 1e-12;
    for (int i = 0; i < k; i++) { if ((int)team[i].size() >= tcap) continue;
      for (int w = 0; w < W; w++) if (!used[w]) { Mask nw = wm[w] & ~M[i]; if (nw.none()) continue; double g = 0; for (int b = 0; b < NSK; b++) if (nw[b]) g += wsk[i][b]; if (g > bg) bg = g, bi = i, bw = w; } }
    if (bi < 0) break; used[bw] = 1; team[bi].push_back(bw); M[bi] |= wm[bw];
  }
  return team;
}
struct Plan { vector<int> open; vector<double> w; vector<vector<int>> team; double val = -1e300; LevelRes lr; };
double evalPlan(Plan& p, int tmode) {  // tmode: team cap (>=1); 0 = keep p.team
  if (p.w.size() != p.open.size()) p.w.assign(p.open.size(), 0);
  if (!ownCell(p.open, p.w)) { p.val = -1e300; return p.val; }
  vector<vector<int>> cell; cellsOf(p.open, p.w, cell);
  auto score = [&](vector<vector<int>>& team, LevelRes& lr) {
    vector<vector<int>> el(p.open.size());
    for (size_t i = 0; i < p.open.size(); i++) { Mask m = teamMask(team[i]); for (int s : cell[i]) if ((sm[s] & ~m).none()) el[i].push_back(s); }
    lr = levelSearch(p.open, el); return lr.val;
  };
  if (tmode > 0) p.team = teamGreedy(p.open, cell, tmode);
  p.val = score(p.team, p.lr);
  // balanced team sizes as a second plan: the fractional greedy lets the first office take every skill
  int k = p.open.size(), bal = max(1, W / max(1, k));
  if (tmode >= 99 && k >= 2 && bal < tmode) {
    vector<vector<int>> t2 = teamGreedy(p.open, cell, bal); LevelRes l2;
    if (score(t2, l2) > p.val) p.team = t2, p.lr = l2, p.val = l2.val;
  }
  return p.val;
}
Sol planToSol(const Plan& p, const string& tag) {
  Sol s; s.mem.assign(K, {}); s.wk.assign(K, {}); s.tag = tag;
  if (p.lr.mem.empty()) { s.val = 0; return s; }
  for (size_t i = 0; i < p.open.size(); i++) { int o = p.open[i]; s.mem[o] = p.lr.mem[o]; if (!s.mem[o].empty()) s.wk[o] = p.team[i]; }
  return s;
}

// ---------- generic finisher: from an arbitrary assignment (site->office) build a valid solution
Sol finishAsg(const vector<int>& asg, const vector<vector<int>>& wkIn, const string& tag) {
  vector<vector<int>> mem(K); for (int s = 0; s < n; s++) if (asg[s] >= 0) mem[asg[s]].push_back(s);
  vector<vector<int>> wk = wkIn;
  for (int o = 0; o < K; o++) { Mask m = teamMask(wk[o]); vector<int> k2; for (int s : mem[o]) if ((sm[s] & ~m).none() && prof(o, s) > 0) k2.push_back(s); mem[o] = k2; }
  repairHull(mem);
  vector<int> open; vector<vector<int>> el; vector<vector<int>> tm;
  for (int o = 0; o < K; o++) if (!mem[o].empty()) open.push_back(o), el.push_back(mem[o]), tm.push_back(wk[o]);
  LevelRes lr = levelSearch(open, el);
  Sol s; s.mem.assign(K, {}); s.wk.assign(K, {}); s.tag = tag;
  if (lr.mem.empty()) { s.val = 0; return s; }
  for (size_t i = 0; i < open.size(); i++) { int o = open[i]; s.mem[o] = lr.mem[o]; if (!s.mem[o].empty()) s.wk[o] = tm[i]; }
  s.val = lr.val; return s;
}

Sol BEST; map<string, double> modeBest; map<string, string> modeSum;
void consider(Sol s) {
  if (s.mem.empty()) return;
  string why; double v = evalFull(s, &why);
  if (v <= -1e299) { // try a repair
    repairHull(s.mem);
    vector<int> open; vector<vector<int>> el; vector<vector<int>> tm;
    for (int o = 0; o < K; o++) if (!s.mem[o].empty()) open.push_back(o), el.push_back(s.mem[o]), tm.push_back(s.wk[o]);
    LevelRes lr = levelSearch(open, el); Sol t; t.mem.assign(K, {}); t.wk.assign(K, {}); t.tag = s.tag;
    if (!lr.mem.empty()) for (size_t i = 0; i < open.size(); i++) { t.mem[open[i]] = lr.mem[open[i]]; if (!t.mem[open[i]].empty()) t.wk[open[i]] = tm[i]; }
    s = t; v = evalFull(s, &why);
    if (v <= -1e299) return;
  }
  s.val = v;
  string m = s.tag.substr(0, 1);
  if (!modeBest.count(m) || v > modeBest[m]) modeBest[m] = v, modeSum[m] = s.tag + " " + summary(s);
  if (v > BEST.val) BEST = s;
}

vector<double> single;  // single-office value
vector<int> bySingle;

// ---------- strategy (a): greedy add offices, Voronoi cells, teams greedy
void stratA(double until) {
  for (int st = 0; st < min(3, K) && el() < until; st++) {
    vector<int> open = {bySingle[st]}; double bestV = -1e300; int stall = 0;
    while ((int)open.size() < K && el() < until) {
      int bo = -1; double bv = -1e300; Plan bp;
      for (int o = 0; o < K && el() < until; o++) { if (find(open.begin(), open.end(), o) != open.end()) continue;
        Plan p; p.open = open; p.open.push_back(o); evalPlan(p, 99); if (p.val > bv) bv = p.val, bo = o, bp = p; }
      if (bo < 0) break;
      open.push_back(bo); consider(planToSol(bp, "a_greedyadd"));
      if (bv > bestV + 1e-9) bestV = bv, stall = 0; else if (++stall >= 4) break;
    }
  }
}
// (c): all open, close worst
void stratC(double until) {
  for (int tc : {99, 2, 1}) {
    vector<int> open(K); iota(open.begin(), open.end(), 0);
    { Plan p; p.open = open; evalPlan(p, tc); consider(planToSol(p, "c_allopen")); }
    while (open.size() > 1 && el() < until) {
      int bi = -1; double bv = -1e300; Plan bp;
      for (size_t i = 0; i < open.size() && el() < until; i++) { Plan p; p.open = open; p.open.erase(p.open.begin() + i); evalPlan(p, tc); if (p.val > bv) bv = p.val, bi = i, bp = p; }
      if (bi < 0) break; open.erase(open.begin() + bi); consider(planToSol(bp, "c_close_t" + to_string(tc)));
    }
  }
}
// (b)/(g): one worker per office (team cap 1), or cap 2; greedy add
void stratB(double until) {
  for (int tc : {1, 2}) {
    vector<int> open = {bySingle[0]}; double bestV = -1e300; int stall = 0;
    while ((int)open.size() < K && el() < until) {
      int bo = -1; double bv = -1e300; Plan bp;
      for (int o = 0; o < K && el() < until; o++) { if (find(open.begin(), open.end(), o) != open.end()) continue;
        Plan p; p.open = open; p.open.push_back(o); evalPlan(p, tc); if (p.val > bv) bv = p.val, bo = o, bp = p; }
      if (bo < 0) break; open.push_back(bo); consider(planToSol(bp, "b_team" + to_string(tc)));
      if (bv > bestV + 1e-9) bestV = bv, stall = 0; else if (++stall >= 4) break;
    }
  }
}
// (d): for each k, random restarts + swap local search on open set, then team local search + power weights
Plan improveTeams(Plan p, double until) {
  // hill climb: move one worker to another office or free
  evalPlan(p, 0); int k = p.open.size();
  for (int it = 0; it < 400 && el() < until; it++) {
    Plan q = p;
    int a = rng() % k; if (q.team[a].empty()) continue; int wi = rng() % q.team[a].size(); int w = q.team[a][wi];
    q.team[a].erase(q.team[a].begin() + wi);
    if (urand() < 0.8) { int b = rng() % k; q.team[b].push_back(w); }
    evalPlan(q, 0); if (q.val > p.val + 1e-12) p = q;
    // swap
    Plan r = p; int c = rng() % k, d2 = rng() % k; if (c == d2 || r.team[c].empty() || r.team[d2].empty()) continue;
    swap(r.team[c][rng() % r.team[c].size()], r.team[d2][rng() % r.team[d2].size()]); evalPlan(r, 0); if (r.val > p.val + 1e-12) p = r;
  }
  return p;
}
Plan improveWeights(Plan p, double until) {
  evalPlan(p, 0); int k = p.open.size(); double sc = 0.02 * SPAN * SPAN;
  for (int it = 0; it < 300 && el() < until; it++) {
    Plan q = p; int i = rng() % k; q.w[i] += (urand() < 0.5 ? -1 : 1) * sc * urand();
    evalPlan(q, 0); if (q.val > p.val + 1e-12) p = q; if (it % 100 == 99) sc *= 0.5;
  }
  return p;
}
void stratD(double until) {
  int kmax = min(K, max(12, (int)(2 * sqrt((double)K) + 6)));
  double t0 = el(); double per = (until - t0) / kmax;
  vector<pair<double, Plan>> top;
  for (int k = 1; k <= kmax && el() < until; k++) {
    double kend = t0 + per * k; Plan best;
    for (int rs = 0; el() < kend; rs++) {
      // init: k-means++ style on offices weighted by single value
      vector<int> open;
      if (rs == 0) open.assign(bySingle.begin(), bySingle.begin() + k);
      else { vector<int> all(K); iota(all.begin(), all.end(), 0); shuffle(all.begin(), all.end(), rng); open.assign(all.begin(), all.begin() + k); }
      Plan p; p.open = open; evalPlan(p, 99);
      for (int it = 0; it < 6 * K && el() < kend; it++) {  // swap search
        Plan q = p; int i = rng() % k; int o = rng() % K; if (find(q.open.begin(), q.open.end(), o) != q.open.end()) continue;
        q.open[i] = o; q.w.assign(k, 0); evalPlan(q, 99); if (q.val > p.val + 1e-12) p = q;
      }
      if (p.val > best.val) best = p;
    }
    if (best.val > -1e299) { consider(planToSol(best, "d_k" + to_string(k))); top.push_back({best.val, best}); }
  }
  sort(top.begin(), top.end(), [](auto& a, auto& b) { return a.first > b.first; });
  for (size_t i = 0; i < top.size() && i < 3; i++) {
    if (el() >= until) break;
    Plan p = improveTeams(top[i].second, min(until, el() + 0.5)); consider(planToSol(p, "d_team"));
    p = improveWeights(p, min(until, el() + 0.5)); consider(planToSol(p, "d_pw"));
  }
}
// (e): task-free first — every open office only serves zero-task sites (load 0), choose open set greedily
void stratE(double until) {
  vector<int> open; double cur = 0;
  vector<int> order = bySingle;
  for (int rep = 0; rep < 2 && el() < until; rep++)
    for (int o : order) { if (el() > until) break; if (find(open.begin(), open.end(), o) != open.end()) continue;
      vector<int> t = open; t.push_back(o); vector<double> w(t.size(), 0); vector<vector<int>> cell; cellsOf(t, w, cell);
      for (auto& c : cell) { vector<int> z; for (int s : c) if (nt[s] == 0) z.push_back(s); c = z; }
      LevelRes lr = levelSearch(t, cell);
      if (lr.val > cur) { cur = lr.val; open = t; Plan p; p.open = t; p.w = w; p.team.assign(t.size(), {}); p.lr = lr; consider(planToSol(p, "e_taskfree")); }
    }
  // mixed: zero-task zones + the best plan zones with a level: use team plan of BEST and add task-free offices
}
// (n): nearest-by-D assignment for top-k offices + hull repair + level (strategy a-variant without Voronoi)
void stratN(double until) {
  for (int k = 1; k <= K && el() < until; k++) {
    vector<int> open(bySingle.begin(), bySingle.begin() + k);
    vector<int> asg(n, -1);
    for (int s = 0; s < n; s++) { int bo = -1; double bd = 1e300; for (int o : open) if (D[o][s] < bd) bd = D[o][s], bo = o; if (prof(bo, s) > 0) asg[s] = bo; }
    vector<vector<int>> cell(k); for (int s = 0; s < n; s++) if (asg[s] >= 0) cell[find(open.begin(), open.end(), asg[s]) - open.begin()].push_back(s);
    auto team = teamGreedy(open, cell, 99); vector<vector<int>> wk(K); for (int i = 0; i < k; i++) wk[open[i]] = team[i];
    consider(finishAsg(asg, wk, "n_nearestD"));
  }
}

// ---------- (f)/(h): plain SA over site->office with exact objective (hard constraints), workers movable
struct SA {
  vector<int> asg, cnt, load; vector<double> psum; vector<vector<int>> mem, cov, H; vector<int> cc; vector<int> wof; vector<vector<int>> prov; vector<vector<int>> need;
  vector<vector<int>> nearO;
  double aEff;
  void init(const Sol& s) {
    asg.assign(n, -1); cnt.assign(K, 0); load.assign(K, 0); psum.assign(K, 0); mem.assign(K, {}); cov.assign(K, {}); H.assign(K, {}); cc.assign(NP, 0);
    wof.assign(W, -1); prov.assign(K, vector<int>(NSK, 0)); need.assign(K, vector<int>(NSK, 0));
    for (int o = 0; o < K; o++) { for (int w : s.wk[o]) { wof[w] = o; for (int b = 0; b < NSK; b++) if (wm[w][b]) prov[o][b]++; }
      for (int x : s.mem[o]) add0(x, o);
      if (!mem[o].empty()) { covOf(o, mem[o], cov[o], &H[o]); for (int p : cov[o]) cc[p]++; } }
    int nn = min(K, 6); nearO.assign(n, {});
    for (int x = 0; x < n; x++) { vector<int> os(K); iota(os.begin(), os.end(), 0); partial_sort(os.begin(), os.begin() + nn, os.end(), [&](int a, int b) { return ed2(x, n + a) < ed2(x, n + b); }); nearO[x].assign(os.begin(), os.begin() + nn); }
  }
  void add0(int x, int o) { asg[x] = o; cnt[o]++; load[o] += nt[x]; psum[o] += prof(o, x); mem[o].push_back(x); for (int b = 0; b < NSK; b++) if (sm[x][b]) need[o][b]++; }
  void rem0(int x, int o) { asg[x] = -1; cnt[o]--; load[o] -= nt[x]; psum[o] -= prof(o, x); auto& m = mem[o]; m.erase(find(m.begin(), m.end(), x)); for (int b = 0; b < NSK; b++) if (sm[x][b]) need[o][b]--; }
  double value(int o1 = -1, int dc1 = 0, int dl1 = 0, double dp1 = 0, int o2 = -1, int dc2 = 0, int dl2 = 0, double dp2 = 0, bool* balOk = nullptr) {
    double v = 0; int lmn = INT_MAX, lmx = INT_MIN, cmn = INT_MAX, cmx = INT_MIN;
    for (int o = 0; o < K; o++) { int c = cnt[o], l = load[o]; double p = psum[o];
      if (o == o1) c += dc1, l += dl1, p += dp1; if (o == o2) c += dc2, l += dl2, p += dp2;
      if (c <= 0) continue; v += p - cost[o]; lmn = min(lmn, l); lmx = max(lmx, l); cmn = min(cmn, c); cmx = max(cmx, c); }
    if (balOk) *balOk = cmx < cmn || cmx - cmn <= A;
    if (lmx >= lmn) v -= aEff * (lmx - lmn); return v;
  }
  bool skillOk(int x, int o) { for (int b = 0; b < NSK; b++) if (sm[x][b] && prov[o][b] == 0) return false; return true; }
  // try to set zone o to members+x; returns false if conflict. On success updates cov/H/cc.
  bool tryAdd(int x, int o, bool commit) {
    if (!mem[o].empty() && inHull(H[o], x)) { if (commit) add0(x, o); return true; }
    vector<int> pts = H[o]; if (pts.empty()) pts.push_back(n + o); pts.push_back(x); vector<int> nh; hullOf(pts, nh); vector<int> nc; covOfH(nh, nc);
    // conflict if any point in nc has cc>0 not from own old cov
    for (int p : nc) if (cc[p] > 0 && !binary_search(cov[o].begin(), cov[o].end(), p)) return false;
    if (!commit) return true;
    for (int p : cov[o]) cc[p]--; cov[o] = nc; H[o] = nh; for (int p : nc) cc[p]++; add0(x, o); return true;
  }
  void doRem(int x, int o) {
    rem0(x, o); bool vert = find(H[o].begin(), H[o].end(), x) != H[o].end();
    if (mem[o].empty()) { for (int p : cov[o]) cc[p]--; cov[o].clear(); H[o].clear(); return; }
    if (vert) { for (int p : cov[o]) cc[p]--; covOf(o, mem[o], cov[o], &H[o]); for (int p : cov[o]) cc[p]++; }
  }
  Sol toSol(const string& tag) { Sol s; s.mem = mem; s.wk.assign(K, {}); for (int w = 0; w < W; w++) if (wof[w] >= 0 && !mem[wof[w]].empty()) s.wk[wof[w]].push_back(w); s.tag = tag; return s; }
  void run(double until, double aStart, double aEnd, const string& tag) {
    double avgp = 0; int c = 0; for (int x = 0; x < n; x++) for (int o : nearO[x]) { avgp += fabs(prof(o, x)); c++; } avgp = max(1e-12, avgp / max(1, c));
    double T0s = 0.5 * avgp, T1s = 0.002 * avgp; double tS = el(); double T = T0s;
    aEff = aStart; double cur = value(); double bestV = -1e300; long it = 0;
    while (true) {
      if ((it & 255) == 0) { double t = el(); if (t > until) break; double f = (t - tS) / max(1e-9, until - tS); T = T0s * pow(T1s / T0s, f);
        double na = aStart + (aEnd - aStart) * min(1.0, f / 0.7); if (na != aEff) { aEff = na; cur = value(); } }
      it++;
      double r = urand();
      if (r < 0.9 || W == 0) {
        int x = rng() % n; int from = asg[x]; int to;
        double q = urand(); if (q < 0.15) to = -1; else to = nearO[x][rng() % nearO[x].size()];
        if (to == from) continue;
        if (to >= 0 && (cnt[to] + 1 > ms[to] || !skillOk(x, to))) continue;
        bool bal; double nv = value(from, from >= 0 ? -1 : 0, from >= 0 ? -nt[x] : 0, from >= 0 ? -prof(from, x) : 0, to, to >= 0 ? 1 : 0, to >= 0 ? nt[x] : 0, to >= 0 ? prof(to, x) : 0, &bal);
        if (!bal) continue;
        if (!(nv >= cur || urand() < exp((nv - cur) / T))) continue;
        if (from < 0) { if (!tryAdd(x, to, true)) continue; }
        else { doRem(x, from); if (to >= 0 && !tryAdd(x, to, true)) { tryAdd(x, from, true); continue; } }  // own old cover released first
        cur = nv;
      } else {  // worker move
        int w = rng() % W; int a = wof[w]; int b = (urand() < 0.2) ? -1 : (int)(rng() % K); if (a == b) continue;
        if (a >= 0) { bool ok = true; for (int s = 0; s < NSK; s++) if (wm[w][s] && prov[a][s] == 1 && need[a][s] > 0) { ok = false; break; } if (!ok) continue;
          for (int s = 0; s < NSK; s++) if (wm[w][s]) prov[a][s]--; }
        if (b >= 0) for (int s = 0; s < NSK; s++) if (wm[w][s]) prov[b][s]++;
        wof[w] = b;
      }
      if (cur > bestV + 1e-12 && aEff == aEnd) { bestV = cur; if ((it & 1023) == 0 || true) { /* snapshot lazily */ } }
      if ((it & 4095) == 0 && aEff == aEnd && cur >= bestV - 1e-12) consider(toSol(tag));
    }
    aEff = aEnd; consider(toSol(tag));
  }
};
void stratF(double until, const Sol& start, double aStart, const string& tag) {
  SA sa; sa.init(start); sa.run(until, aStart, alpha, tag);
}

// fill the namespace data from the main solver's arrays (its own skill model: wmask, or realW in native mode)
void load() {
  n = ::n; K = ::K; NP = n + K; A = ::A; alpha = ::alpha;
  X.assign(::px.begin(), ::px.begin() + NP); Y.assign(::py.begin(), ::py.begin() + NP);
  rew = ::rew; cost = ::ocost; ms = ::maxSize; nt = ::ntask; D = ::dist; sm = ::smask;
  W = ::W; wm.assign(W, Mask()); for (int w = 0; w < W; w++) wm[w] = ::nativeW ? ::realW[w] : ::wmask[w];
  NSK = min(256, max(1, ::NS));
  double x0 = 1e300, x1 = -1e300, y0 = 1e300, y1 = -1e300;
  for (int i = 0; i < NP; i++) x0 = min(x0, X[i]), x1 = max(x1, X[i]), y0 = min(y0, Y[i]), y1 = max(y1, Y[i]);
  SPAN = max(max(x1 - x0, y1 - y0), 1e-12); EPS = ::EPS;
  buildGrid();
  Mask have; for (auto& m : wm) have |= m;
  single.assign(K, 0);
  for (int o = 0; o < K; o++) { vector<double> pr; for (int s = 0; s < n; s++) if ((sm[s] & ~have).none() && prof(o, s) > 0) pr.push_back(prof(o, s));
    sort(pr.rbegin(), pr.rend()); double v = -cost[o]; for (int i = 0; i < (int)pr.size() && i < ms[o]; i++) v += pr[i]; single[o] = v; }
  bySingle.resize(K); iota(bySingle.begin(), bySingle.end(), 0); sort(bySingle.begin(), bySingle.end(), [&](int a, int b) { return single[a] > single[b]; });
  BEST = Sol(); BEST.mem.assign(K, {}); BEST.wk.assign(K, {}); BEST.val = 0; BEST.tag = "empty"; modeBest.clear(); modeSum.clear();
}
vector<int> asgOf(const Sol& s) { vector<int> a(n, -1); for (int o = 0; o < K; o++) for (int x : s.mem[o]) a[x] = o; return a; }
// with native workers also the teams (asg[n + w] = office, the main solver's layout), so fromAsg keeps them
vector<int> asgOfW(const Sol& s) {
  vector<int> a = asgOf(s);
  if (::nativeW && ::AS == n + W) { a.resize(n + W, -1); for (int o = 0; o < K; o++) if (!s.mem[o].empty()) for (int w : s.wk[o]) a[n + w] = o; }
  return a;
}
// exact best single office: the most profitable coverable sites up to maxSize at each office, best office kept
vector<int> singleAsg() {
  Mask have; for (auto& m : wm) have |= m;
  int o = bySingle[0]; vector<int> c; for (int x = 0; x < n; x++) if ((sm[x] & ~have).none() && prof(o, x) > 0) c.push_back(x);
  sort(c.begin(), c.end(), [&](int a, int b) { return prof(o, a) > prof(o, b); }); if ((int)c.size() > ms[o]) c.resize(ms[o]);
  vector<int> a(n, -1); if (single[o] > 0) for (int x : c) a[x] = o; return a;
}
// portfolio of simple structures (Voronoi/power cells, greedy teams, a common task level) for `seconds`
vector<int> run(double seconds, uint64_t seed, const string& modes, double* outVal) {
  T0 = chrono::steady_clock::now(); TL = seconds; rng.seed(seed);
  { Sol s; s.mem.assign(K, {}); s.wk.assign(K, {}); vector<int> a = singleAsg(); for (int x = 0; x < n; x++) if (a[x] >= 0) s.mem[a[x]].push_back(x);
    Mask need; int o = bySingle[0]; for (int x : s.mem[o]) need |= sm[x]; for (int w = 0; w < W; w++) if ((wm[w] & need).any()) s.wk[o].push_back(w); s.tag = "s_single"; consider(s); }
  vector<string> ml; { stringstream ms_(modes); string t; while (getline(ms_, t, ',')) ml.push_back(t); }
  int nm = ml.size(); double tStart = el();
  for (int i = 0; i < nm && el() < TL; i++) {
    double until = tStart + (TL - tStart) * (i + 1) / nm; const string& m = ml[i];
    if (m == "a") stratA(until); else if (m == "b") stratB(until); else if (m == "c") stratC(until);
    else if (m == "d") stratD(until); else if (m == "e") stratE(until); else if (m == "n") stratN(until);
    else if (m == "h") { Sol st = BEST; if (st.val <= 0) st.mem.assign(K, {}); stratF(until, st, 0.0, "h_rampSA"); }
  }
  if (outVal) *outVal = BEST.val;
  return asgOfW(BEST);
}
}  // namespace r29s

// ---- r36: exact structure enumeration for few offices (tight count window, alpha > 0)
// Open sets of the best <= 8 offices (2..6 zones) x maximal skill allocations of the worker types x power
// diagrams with free generators (x, y, weight per zone; office i must lie in cell i, so every zone hull stays
// inside its convex cell). Every structure gets the exact equal-count / equal-load level: with at most two
// task-count classes (v1 < v2) every zone takes c sites, x of them from class v2 (same x everywhere -> same
// load); the profit is concave in x, so the best x is a bisection; otherwise eqLevel (Lagrangian curves).
// Generators start at the offices (weight 0) and move by a coordinate search; fan starts (generators far out
// in the office directions from an apex) for the best structures. Screening: every structure with a short
// search; the best ones get the full search; the best few are built and checked (evalFull, hull repair).
// Runs before the fork, so every process starts from its answer.
namespace r29s {
// mask bit per class of needed skills held by exactly the same workers: such skills are interchangeable for
// every team (a zone covers one iff it covers all), so the structure search is exact on the classes.
// Returns the number of bits used; idx[b] = bit of skill b (-1: not needed).
inline int skillBits(const Mask& need, vector<int>& idx) {
  idx.assign(NSK, -1); int R = 0;
  map<vector<int>, int> cls;
  for (int b = 0; b < NSK; b++) if (need[b]) {
    vector<int> hold; for (int w = 0; w < W; w++) if (wm[w][b]) hold.push_back(w);
    auto it = cls.find(hold);
    if (it == cls.end()) it = cls.emplace(hold, R++).first;
    idx[b] = it->second;
  }
  return R;
}
namespace r36 {
int R = 0, nv = 0, v1 = 0, v2 = 0, kk = 0;
vector<uint64_t> sMask;                       // per site: relevant skill bits (all ones: unservable)
vector<uint64_t> tMask; vector<vector<int>> tWork;  // worker types: mask, workers
vector<vector<int>> cand; vector<vector<double>> S1, S2; vector<vector<int>> I1, I2;
double dl_ = 0; long long evals = 0;
vector<vector<int>> ordO; vector<signed char> cellOf;  // r38w: per pool office its profitable sites, best first
double levelOf(const vector<int>& open, int cmax, double costSum, vector<vector<int>>* mem, int* cOut);
int poolCap = 8;  // r39: the pool = the best poolCap offices by single-office value
bool wide = false;  // r38w: called through the wide gate (early exit after the screening)
static const bool dbg = false;

// generators: G[3 i] = x, G[3 i + 1] = y, G[3 i + 2] = weight; cell of p = argmin |p - g_i|^2 - w_i
inline double pd(int p, const vector<double>& G, int i) { double dx = X[p] - G[3 * i], dy = Y[p] - G[3 * i + 1]; return dx * dx + dy * dy - G[3 * i + 2]; }
bool ownG(const vector<int>& open, const vector<double>& G) {
  int k = open.size();
  for (int i = 0; i < k; i++) { double di = pd(n + open[i], G, i);
    for (int j = 0; j < k; j++) if (j != i && pd(n + open[i], G, j) <= di + 1e-9 * SPAN * SPAN) return false; }
  return true;
}
vector<double> officeG(const vector<int>& open) {
  vector<double> G; for (int o : open) G.push_back(X[n + o]), G.push_back(Y[n + o]), G.push_back(0.0); return G;
}
// fan start: generators far out (one span) from the apex in the direction of each office; the apex office
// (or a coincident one) gets direction rot * 90 degrees
vector<double> fanG(const vector<int>& open, int apexIdx, int rot) {
  int k = open.size(); double ax = 0, ay = 0;
  if (apexIdx < 0) { for (int o : open) ax += X[n + o], ay += Y[n + o]; ax /= k; ay /= k; } else ax = X[n + open[apexIdx]], ay = Y[n + open[apexIdx]];
  vector<double> G;
  for (int i = 0; i < k; i++) { double dx = X[n + open[i]] - ax, dy = Y[n + open[i]] - ay, ang;
    if (i == apexIdx || hypot(dx, dy) <= 1e-9 * SPAN) ang = rot * M_PI / 2; else ang = atan2(dy, dx);
    G.push_back(ax + SPAN * cos(ang)); G.push_back(ay + SPAN * sin(ang)); G.push_back(0.0); }
  return G;
}
// value of a structure (exact for nv <= 2); mem (size K) gets the zone members when given
double evalW0(const vector<int>& open, const vector<uint64_t>& tm, const vector<double>& w, vector<vector<int>>* mem, int* cOut);
// SZ_R36CHK: every evaluation also runs the plain path and compares (tests)
double evalW(const vector<int>& open, const vector<uint64_t>& tm, const vector<double>& w, vector<vector<int>>* mem, int* cOut = nullptr) {
  static const bool chk = false;
  double v = evalW0(open, tm, w, mem, cOut);
  if (chk && !ordO.empty()) {
    vector<vector<int>> keep; keep.swap(ordO); vector<vector<int>> m2; int c2 = -1;
    double v2 = evalW0(open, tm, w, mem ? &m2 : nullptr, &c2); keep.swap(ordO);
    if (v != v2 || (mem && *mem != m2)) { fprintf(stderr, "r36 CHK MISMATCH %.9f %.9f\n", v, v2); exit(3); }
  }
  return v;
}
double evalW0(const vector<int>& open, const vector<uint64_t>& tm, const vector<double>& w, vector<vector<int>>* mem, int* cOut) {
  int k = open.size(); evals++;
  if (!ownG(open, w)) return -1e300;
  double costSum = 0; for (int o : open) costSum += cost[o];
  if (nv <= 2 && !ordO.empty()) {
    // r38w fast path (same result): cell labels, then each zone scans its office's presorted profitable sites
    cellOf.resize(n);
    for (int s = 0; s < n; s++) {
      if (sMask[s] == ~0ull) { cellOf[s] = -1; continue; }
      int bi = 0; double bd = pd(s, w, 0);
      for (int i = 1; i < k; i++) { double d = pd(s, w, i); if (d < bd) bd = d, bi = i; }
      cellOf[s] = (sMask[s] & ~tm[bi]) == 0 ? (signed char)bi : (signed char)-1;
    }
    S1.assign(k, {0.0}); S2.assign(k, {0.0}); I1.assign(k, {}); I2.assign(k, {});
    int cmax = INT_MAX;
    for (int i = 0; i < k; i++) {
      int o = open[i];
      for (int s : ordO[o]) if (cellOf[s] == i) {
        if (nv == 2 && nt[s] == v2) I2[i].push_back(s), S2[i].push_back(S2[i].back() + prof(o, s));
        else I1[i].push_back(s), S1[i].push_back(S1[i].back() + prof(o, s));
      }
      cmax = min(cmax, min(ms[o], (int)(I1[i].size() + I2[i].size())));
    }
    return levelOf(open, cmax, costSum, mem, cOut);
  }
  cand.assign(k, {});
  for (int s = 0; s < n; s++) {
    if (sMask[s] == ~0ull) continue;
    int bi = 0; double bd = pd(s, w, 0);
    for (int i = 1; i < k; i++) { double d = pd(s, w, i); if (d < bd) bd = d, bi = i; }
    if ((sMask[s] & ~tm[bi]) == 0 && prof(open[bi], s) > 0) cand[bi].push_back(s);
  }
  if (nv > 2) {
    LevelRes r = eqLevel(open, cand);
    if (r.val <= -1e299) return -1e300;
    if (mem) *mem = r.mem;
    return r.val;
  }
  S1.assign(k, {0.0}); S2.assign(k, {0.0}); I1.assign(k, {}); I2.assign(k, {});
  int cmax = INT_MAX;
  for (int i = 0; i < k; i++) {
    int o = open[i];
    for (int s : cand[i]) (nv == 2 && nt[s] == v2 ? I2[i] : I1[i]).push_back(s);
    auto byP = [&](int a, int b) { double pa = prof(o, a), pb = prof(o, b); return pa > pb || (pa == pb && a < b); };
    sort(I1[i].begin(), I1[i].end(), byP); sort(I2[i].begin(), I2[i].end(), byP);
    for (int s : I1[i]) S1[i].push_back(S1[i].back() + prof(o, s));
    for (int s : I2[i]) S2[i].push_back(S2[i].back() + prof(o, s));
    cmax = min(cmax, min(ms[o], (int)cand[i].size()));
  }
  return levelOf(open, cmax, costSum, mem, cOut);
}
// the best common count c / class-2 count x for the zone lists in S1/S2/I1/I2 (nv <= 2)
double levelOf(const vector<int>& open, int cmax, double costSum, vector<vector<int>>* mem, int* cOut) {
  int k = open.size();
  if (cmax < 1) return -1e300;
  int n2min = INT_MAX; for (int i = 0; i < k; i++) n2min = min(n2min, (int)I2[i].size());
  auto V = [&](int c, int x) { double v = 0; for (int i = 0; i < k; i++) v += S2[i][x] + S1[i][c - x]; return v; };
  double bv = -1e300; int bc = -1, bx = -1;
  vector<int> cs; for (int c = cmax; c >= max(1, cmax - 8); c--) cs.push_back(c);
  for (double f : {0.95, 0.9, 0.85, 0.8}) { int c = (int)(f * cmax); if (c >= 1 && c < cmax - 8) cs.push_back(c); }
  for (int c : cs) {
    int xlo = 0, xhi = min(c, n2min);
    for (int i = 0; i < k; i++) xlo = max(xlo, c - (int)I1[i].size());
    if (xlo > xhi) continue;
    int lo = xlo, hi = xhi;
    while (lo < hi) { int mid = (lo + hi) / 2; if (V(c, mid + 1) > V(c, mid)) lo = mid + 1; else hi = mid; }
    double v = V(c, lo);
    if (v > bv) bv = v, bc = c, bx = lo;
  }
  if (bc < 0) return -1e300;
  if (cOut) *cOut = bc;
  if (mem) {
    mem->assign(K, {});
    for (int i = 0; i < k; i++) { auto& m = (*mem)[open[i]];
      m.assign(I2[i].begin(), I2[i].begin() + bx); m.insert(m.end(), I1[i].begin(), I1[i].begin() + (bc - bx)); }
  }
  return bv - costSum;
}
double optW(const vector<int>& open, const vector<uint64_t>& tm, vector<double>& w, double v, int iters) {
  int k = open.size(); double step = 0.05 * SPAN;
  for (int it = 0; it < iters && el() < dl_; it++) {
    bool imp = false;
    for (int i = 0; i < 3 * k && el() < dl_; i++) for (int sg = 1; sg >= -1; sg -= 2) {
      vector<double> w2 = w; w2[i] += sg * (i % 3 == 2 ? step * SPAN : step); double v2 = evalW(open, tm, w2, nullptr);
      if (v2 > v + 1e-9 * max(1.0, fabs(v))) { v = v2; w = w2; imp = true; break; }
    }
    if (!imp) { step *= 0.5; if (step < 1e-4 * SPAN) break; }
  }
  return v;
}
// maximal allocations of the worker types to k zones: type t goes to min(count, k) zones (more never hurts);
// returns per allocation the zone subset of every type, deduplicated by zone masks, dominated ones removed.
// All of them when there are at most `cap` combinations, else `cap` random draws (fixed seed).
vector<vector<vector<uint32_t>>> CH(8); vector<char> sampled(8, 0);  // r38w: per k the zone subsets of every type
vector<vector<uint32_t>> allocs(int k, size_t cap) {
  int T = tMask.size(); vector<vector<uint32_t>> ch(T); double prod = 1;
  for (int t = 0; t < T; t++) { int m = min((int)tWork[t].size(), k);
    for (uint32_t s = 0; s < (1u << k); s++) if (__builtin_popcount(s) == m) ch[t].push_back(s);
    prod *= ch[t].size(); }
  CH[k] = ch; sampled[k] = prod > cap;
  vector<vector<uint32_t>> out; vector<vector<uint64_t>> masks; set<vector<uint64_t>> seen;
  vector<uint32_t> cur(T); vector<uint64_t> zm(k, 0);
  auto leaf = [&]() { fill(zm.begin(), zm.end(), 0u);
    for (int t = 0; t < T; t++) for (int z = 0; z < k; z++) if (cur[t] >> z & 1) zm[z] |= tMask[t];
    if (seen.insert(zm).second) out.push_back(cur), masks.push_back(zm); };
  if (prod <= cap) {
    vector<size_t> ix(T, 0);
    while (true) {
      for (int t = 0; t < T; t++) cur[t] = ch[t][ix[t]];
      leaf();
      int t = T - 1; while (t >= 0 && ++ix[t] == ch[t].size()) ix[t] = 0, t--;
      if (t < 0 || el() > dl_) break;
    }
  } else {
    mt19937_64 g(12345 + k);
    for (size_t d = 0; d < cap && el() <= dl_; d++) { for (int t = 0; t < T; t++) cur[t] = ch[t][g() % ch[t].size()]; leaf(); }
  }
  vector<char> dom(out.size(), 0);
  for (size_t a = 0; a < out.size() && el() <= dl_; a++) for (size_t b = 0; b < out.size() && !dom[a]; b++) if (a != b && !dom[b]) {
    bool sub = true; for (int z = 0; z < k && sub; z++) if (masks[a][z] & ~masks[b][z]) sub = false;
    if (sub && masks[a] != masks[b]) dom[a] = 1; }
  vector<vector<uint32_t>> res; for (size_t a = 0; a < out.size(); a++) if (!dom[a]) res.push_back(out[a]);
  return res;
}
struct Cfg { vector<int> open; vector<uint32_t> al; vector<uint64_t> tm; vector<double> w; double v = -1e300; };
vector<uint64_t> zoneMasks(const vector<uint32_t>& al, int k) {
  vector<uint64_t> tm(k, 0); for (size_t t = 0; t < al.size(); t++) for (int z = 0; z < k; z++) if (al[t] >> z & 1) tm[z] |= tMask[t]; return tm;
}
// r38w: team search for sampled allocations (many worker types): move one type to another zone subset while
// the structure gains (coordinate search over the types)
double optT(Cfg& c, int iters) {
  int k = c.open.size();
  for (int it = 0; it < iters && el() < dl_; it++) {
    bool imp = false;
    for (size_t t = 0; t < c.al.size() && el() < dl_; t++) for (uint32_t o : CH[k][t]) {
      if (el() >= dl_) break;
      if (o == c.al[t]) continue;
      vector<uint32_t> al2 = c.al; al2[t] = o; vector<uint64_t> tm2 = zoneMasks(al2, k);
      double v2 = evalW(c.open, tm2, c.w, nullptr);
      if (v2 > c.v + 1e-9 * max(1.0, fabs(c.v))) { c.v = v2; c.al = al2; c.tm = tm2; imp = true; }
    }
    if (!imp) break;
  }
  return c.v;
}
// count window (0 < A <= 16, at most two task-count classes, after evalW filled S1/S2/I1/I2): zone counts in
// [c, c + A] with one common load T (x_i = (T - c_i v1) / (v2 - v1) sites of class v2); exhaustive over T and
// a few base counts; returns the value (without office costs) and fills mem when it beats `than`
double windowLevel(const vector<int>& open, double than, vector<vector<int>>& mem) {
  int k = open.size(); if (A <= 0 || A > 16 || nv > 2 || nv < 1) return -1e300;
  int d = nv == 2 ? v2 - v1 : 0, cmx = INT_MAX;
  for (int i = 0; i < k; i++) cmx = min(cmx, min(ms[open[i]], (int)(I1[i].size() + I2[i].size())));
  double bv = -1e300; int bc = -1, bT = -1;
  vector<int> bestCi(k), bestXi(k), ci(k), xi(k);
  vector<char> okr(max(1, d));
  for (int c = cmx; c >= max(1, cmx - A - 2) && el() < dl_; c--) {
    int Tlo = c * v1, Thi = (c + A) * (nv == 2 ? v2 : v1);
    // a load T is reachable only with T = cc v1 (mod d) for some count cc in [c, c + A] (the other T are skipped)
    if (d > 0) { fill(okr.begin(), okr.end(), 0); for (int a = 0; a <= A; a++) okr[(long long)(c + a) * v1 % d] = 1; }
    for (int T = Tlo; T <= Thi && el() < dl_; T++) {
      if (d > 0 ? !okr[T % d] : (v1 > 0 && T % v1 != 0)) continue;
      double v = 0; bool ok = true;
      for (int i = 0; i < k && ok; i++) { double bi = -1e300; int cap = min(ms[open[i]], (int)(I1[i].size() + I2[i].size()));
        for (int a = 0; a <= A && c + a <= cap; a++) { int cc = c + a, r = T - cc * v1, x;
          if (d == 0) { if (r != 0) continue; x = 0; } else { if (r < 0 || r % d) continue; x = r / d; }
          if (x > cc || x > (int)I2[i].size() || cc - x > (int)I1[i].size()) continue;
          double val = S2[i][x] + S1[i][cc - x]; if (val > bi) bi = val, ci[i] = cc, xi[i] = x; }
        if (bi <= -1e299) ok = false; else v += bi; }
      if (ok && v > bv) bv = v, bc = c, bT = T, bestCi = ci, bestXi = xi;
    }
  }
  if (bc < 0 || bv <= than) return bv;
  mem.assign(K, {});
  for (int i = 0; i < k; i++) { auto& m = mem[open[i]];
    m.assign(I2[i].begin(), I2[i].begin() + bestXi[i]); m.insert(m.end(), I1[i].begin(), I1[i].begin() + (bestCi[i] - bestXi[i])); }
  return bv;
}
// build, check and repair a structure; returns its true value (evalFull) or -1e300
double finish(const Cfg& c, Sol& s) {
  vector<vector<int>> mem; double est = evalW(c.open, c.tm, c.w, &mem);
  if (est <= -1e299) return -1e300;
  if (A > 0 && nv <= 2) { double cs = 0; for (int o : c.open) cs += cost[o];
    double wv = windowLevel(c.open, est + cs, mem); if (dbg) fprintf(stderr, "r36 window: %.4f vs %.4f\n", wv - cs, est); }
  int k = c.open.size(); s = Sol(); s.mem = mem; s.wk.assign(K, {}); s.tag = "r36";
  for (size_t t = 0; t < c.al.size(); t++) { int j = 0;
    for (int z = 0; z < k; z++) if (c.al[t] >> z & 1) { if (!s.mem[c.open[z]].empty()) s.wk[c.open[z]].push_back(tWork[t][j]); j++; } }
  string why; double v = evalFull(s, &why);
  if (dbg) fprintf(stderr, "r36 finish: est %.4f full %.4f %s %s\n", est, v, why.c_str(), summary(s).c_str());
  if (v > -1e299) { s.val = v; return v; }
  if (el() > 0.97 * TL || n > 50000) return -1e300;  // repair (hull cut + levelSearch) only with time left
  repairHull(s.mem);
  if (el() > TL) return -1e300;
  vector<int> open; vector<vector<int>> el2; vector<vector<int>> tw;
  for (int o = 0; o < K; o++) if (!s.mem[o].empty()) open.push_back(o), el2.push_back(s.mem[o]), tw.push_back(s.wk[o]);
  LevelRes lr = levelSearch(open, el2); Sol t; t.mem.assign(K, {}); t.wk.assign(K, {}); t.tag = "r36r";
  if (!lr.mem.empty()) for (size_t i = 0; i < open.size(); i++) { t.mem[open[i]] = lr.mem[open[i]]; if (!t.mem[open[i]].empty()) t.wk[open[i]] = tw[i]; }
  v = evalFull(t, &why); if (dbg) fprintf(stderr, "r36 repaired: %.4f %s\n", v, why.c_str());
  if (v <= -1e299) return -1e300;
  s = t; s.val = v; return v;
}
// r53: "far rows" starts. When the distance row of an office is cheapest far from the office itself (rows of
// another office, e.g. the opposite one on a ring of offices outside the site cloud, rot = K/2), the best zones
// lie beyond the bisector with a neighbour ("pinwheel": 3 wedges for K = 4) and the generator search that starts
// at the offices never gets there. For every open set of 2..4 pool offices (its best screened teams): (a) each
// generator moved toward the centroid of its office's best sites (blend 0.25..1), weights solved so that every
// office owns its cell (difference constraints, Bellman-Ford); (b) random free generators (expanded site box),
// the office -> cell map read off the diagram (one office per cell); then the usual coordinate search on the
// best starts. Gate: >= 2 and >= half of the pool offices have their best-site centroid nearer to another
// office. Fixed seed;
// share SZ_R53 (0.2) of what is left of the phase, at most 8 s.
static bool ownWeights(const vector<int>& open, vector<double>& G) {
  int k = open.size(); const double mg = 1e-6 * SPAN * SPAN;
  // w_j <= w_i + (d_ij - d_ii) - mg for every office i and other generator j (office i strictly in cell i)
  vector<double> w(k, 0.0);
  for (int it = 0; it <= k; it++) { bool ch = false;
    for (int i = 0; i < k; i++) { double dii = pd(n + open[i], G, i) + G[3 * i + 2];
      for (int j = 0; j < k; j++) if (j != i) { double dij = pd(n + open[i], G, j) + G[3 * j + 2];
        double lim = w[i] + (dij - dii) - mg; if (w[j] > lim) { w[j] = lim; ch = true; } } }
    if (!ch) break; if (it == k) return false; }
  for (int i = 0; i < k; i++) G[3 * i + 2] = w[i];
  return ownG(open, G);
}
bool farRowStarts(const map<vector<int>, Cfg>& bestSet, const vector<int>& pool, double seconds, vector<Cfg>& top) {
  static const double frac = 0.2;
  if (frac <= 0 || bestSet.empty() || el() >= 0.9 * seconds) return false;
  // centroid of each pool office's best sites (up to maxSize, by profit)
  vector<double> cx(K, 0), cy(K, 0); int far = 0;
  for (int o : pool) {
    vector<pair<double, int>> ps;
    for (int s = 0; s < n; s++) if (sMask[s] != ~0ull && prof(o, s) > 0) ps.push_back({-prof(o, s), s});
    if (ps.empty()) continue;
    size_t m = min(ps.size(), (size_t)max(1, ms[o]));
    nth_element(ps.begin(), ps.begin() + (m - 1), ps.end());
    for (size_t i = 0; i < m; i++) cx[o] += X[ps[i].second], cy[o] += Y[ps[i].second];
    cx[o] /= m, cy[o] /= m;
    int bo = o; double bd = hypot(X[n + o] - cx[o], Y[n + o] - cy[o]);
    for (int q : pool) { double d = hypot(X[n + q] - cx[o], Y[n + q] - cy[o]); if (d < bd - 1e-12 * SPAN) bd = d, bo = q; }
    if (bo != o) far++;
  }
  if (dbg) fprintf(stderr, "r53: %d of %zu pool offices with far rows\n", far, pool.size());
  if (far < 2 || 2 * far < (int)pool.size()) return false;  // at least half of the pool (k50m_s24: 2 of 8 -> off)
  double x0 = 1e300, x1 = -1e300, y0 = 1e300, y1 = -1e300;
  for (int s = 0; s < n; s++) x0 = min(x0, X[s]), x1 = max(x1, X[s]), y0 = min(y0, Y[s]), y1 = max(y1, Y[s]);
  double ex = 0.25 * (x1 - x0), ey = 0.25 * (y1 - y0);
  double t0 = el(), end = t0 + min(8.0, frac * max(0.0, 0.95 * seconds - t0));
  mt19937_64 g(5353); uniform_real_distribution<double> ux(x0 - ex, x1 + ex), uy(y0 - ey, y1 + ey);
  vector<const Cfg*> sets; for (auto& kv : bestSet) if (kv.first.size() >= 2) sets.push_back(&kv.second);
  // r53f: at most 24 open sets (pool of 8: 154), the best screened first (ties: map order)
  stable_sort(sets.begin(), sets.end(), [](const Cfg* a, const Cfg* b) { return a->v > b->v; });
  if (sets.size() > 24) sets.resize(24);
  int nS = sets.size(), wins = 0; double keepDl = dl_;
  // r53f: fixed work (random probes per set by n; optW bounded by its iteration count), the clock only as a guard
  // at 0.9 x the phase: the result no longer depends on the machine speed (time-bounded probes gave 836 / 799 on one ring)
  const double guard = 0.9 * seconds; (void)end;
  const int nProbe = max(50, min(3000, (int)(6e7 / ((double)max(1, n) * max(1, nS)))));
  for (int si = 0; si < nS && el() < guard; si++) {
    const Cfg& c0 = *sets[si]; int k = c0.open.size();
    double sEnd = guard;
    vector<Cfg> st;
    for (double lam : {0.25, 0.5, 0.75, 1.0}) {
      Cfg c = c0; c.w.assign(3 * k, 0.0);
      for (int i = 0; i < k; i++) { int o = c.open[i]; c.w[3 * i] = X[n + o] + lam * (cx[o] - X[n + o]); c.w[3 * i + 1] = Y[n + o] + lam * (cy[o] - Y[n + o]); }
      if (!ownWeights(c.open, c.w)) continue;
      c.v = evalW(c.open, c.tm, c.w, nullptr); if (c.v > -1e299) st.push_back(c);
    }
    Cfg bestR; vector<double> G(3 * k), H(3 * k); vector<int> cellO(k);
    for (int pr = 0; pr < nProbe && ((pr & 15) != 15 || el() < guard); pr++) {  // r57: clock every 16 probes
      for (int i = 0; i < k; i++) G[3 * i] = ux(g), G[3 * i + 1] = uy(g), G[3 * i + 2] = 0.0;
      vector<char> used(k, 0); bool ok = true;
      for (int i = 0; i < k && ok; i++) { int b = 0; double bd = pd(n + c0.open[i], G, 0);
        for (int j = 1; j < k; j++) { double d = pd(n + c0.open[i], G, j); if (d < bd) bd = d, b = j; }
        if (used[b]) ok = false; else used[b] = 1, cellO[i] = b; }
      if (!ok) continue;
      for (int i = 0; i < k; i++) for (int t = 0; t < 3; t++) H[3 * i + t] = G[3 * cellO[i] + t];
      double v = evalW(c0.open, c0.tm, H, nullptr);
      if (v > bestR.v) { bestR = c0; bestR.w = H; bestR.v = v; }
    }
    if (bestR.v > -1e299) st.push_back(bestR);
    sort(st.begin(), st.end(), [](const Cfg& a, const Cfg& b) { return a.v > b.v; });
    for (size_t i = 0; i < st.size() && i < 3 && el() < sEnd; i++) {
      dl_ = sEnd;
      st[i].v = optW(st[i].open, st[i].tm, st[i].w, st[i].v, 80);
      if (dbg) fprintf(stderr, "r53 set %d (k=%d): start %zu -> %.4f (screened %.4f)\n", si, k, i, st[i].v, c0.v);
      if (st[i].v > c0.v + 1e-9 * max(1.0, fabs(c0.v))) { top.push_back(st[i]); wins++; }
    }
  }
  dl_ = keepDl;
  if (dbg) fprintf(stderr, "r53: %d sets, %d starts better than screened (%.2fs)\n", nS, wins, el() - t0);
  return true;
}
// r53e: Y starts for 3 zones, after the far-row starts. A 3-cell convex partition with a common
// centre ("Y": centre + one ray in every angular gap between the three offices, all angles < pi) is the power
// diagram of three generators equidistant from the centre, mirror images across the rays. Centres: a 6 x 6
// grid over the site box expanded by half its size each side (far centres ~ strips), the office centroid, and
// points just beyond each office (zones that are wedges with their apex at the office). The geometry is first
// rated with every skill in every zone, then the 6 best with every team allocation (the screened teams belong to
// the office-generator geometry); the best 3 per open set get the generator search with team moves (optT).
// Fixed grid, at most 20 % of the phase.
bool yGen(const vector<int>& open, double cx, double cy, const double* fr, vector<double>& G) {
  double a[3]; int ord[3] = {0, 1, 2};
  for (int i = 0; i < 3; i++) { double dx = X[n + open[i]] - cx, dy = Y[n + open[i]] - cy;
    if (hypot(dx, dy) <= 1e-6 * SPAN) return false; a[i] = atan2(dy, dx); }
  sort(ord, ord + 3, [&](int p, int q) { return a[p] < a[q]; });
  double rho[3];  // ray m between the wedges of ord[m] and ord[m + 1] (ccw)
  for (int m = 0; m < 3; m++) { double lo = a[ord[m]], hi = a[ord[(m + 1) % 3]]; if (m == 2) hi += 2 * M_PI;
    rho[m] = lo + fr[m] * (hi - lo); }
  for (int m = 0; m < 3; m++) { double lo = m == 0 ? rho[2] - 2 * M_PI : rho[m - 1]; if (rho[m] - lo >= M_PI - 1e-6) return false; }
  double r = 0.25 * SPAN, psi0 = rho[2] - rho[1] + rho[0];
  for (int flip = 0; flip < 2; flip++) {
    double ps[3]; ps[0] = psi0 + flip * M_PI; ps[1] = 2 * rho[0] - ps[0]; ps[2] = 2 * rho[1] - ps[1];
    G.assign(9, 0.0);
    for (int m = 0; m < 3; m++) { G[3 * ord[m]] = cx + r * cos(ps[m]); G[3 * ord[m] + 1] = cy + r * sin(ps[m]); }
    if (ownG(open, G)) return true;
  }
  return false;
}
void yStarts(const vector<int>& pool, vector<vector<vector<uint32_t>>>& AL, vector<Cfg>& top, double seconds) {
  if ((int)AL.size() <= 3 || AL[3].empty()) return;
  double t0 = el(), xEnd = min(0.95 * seconds, t0 + 0.2 * seconds); long long e0 = evals;
  if (xEnd - t0 < 0.01) return;
  double dlKeep = dl_; dl_ = xEnd;
  // open sets: those of 3 offices in the first 12 distinct structures of top, then the 3-subsets of the best 4
  vector<vector<int>> ys; int nd = 0;
  for (size_t i = 0; i < top.size() && nd < 12; i++) {
    bool dup = false; for (size_t j = 0; j < i && !dup; j++) dup = top[j].open == top[i].open && top[j].tm == top[i].tm;
    if (dup || top[i].v <= -1e299) continue; nd++;
    if (top[i].open.size() == 3 && find(ys.begin(), ys.end(), top[i].open) == ys.end()) ys.push_back(top[i].open);
  }
  int P4 = min((int)pool.size(), 4);
  for (int a = 0; a < P4; a++) for (int b = a + 1; b < P4; b++) for (int d = b + 1; d < P4; d++) {
    vector<int> o = {pool[a], pool[b], pool[d]}; if (find(ys.begin(), ys.end(), o) == ys.end()) ys.push_back(o); }
  double sx0 = 1e300, sx1 = -1e300, sy0 = 1e300, sy1 = -1e300;
  for (int s = 0; s < n; s++) if (sMask[s] != ~0ull) sx0 = min(sx0, X[s]), sx1 = max(sx1, X[s]), sy0 = min(sy0, Y[s]), sy1 = max(sy1, Y[s]);
  if (ys.empty() || sx0 > sx1) { dl_ = dlKeep; return; }
  // r53f: grid density by n (fixed work; was a timing pilot)
  vector<uint64_t> allT(3, ~0ull);
  int gN = n <= 8000 ? 6 : 4, fN = n <= 8000 ? 4 : n <= 20000 ? 3 : 2;
  vector<double> frs; for (int f = 0; f < fN; f++) frs.push_back((f + 0.5) / fN);
  double ex = 0.5 * (sx1 - sx0), ey = 0.5 * (sy1 - sy0), mx = 0.5 * (sx0 + sx1), my = 0.5 * (sy0 + sy1);
  vector<Cfg> cand;
  for (auto& open : ys) {
    if (el() >= xEnd) break;
    vector<pair<double, double>> cs;
    for (int gx = 0; gx < gN; gx++) for (int gy = 0; gy < gN; gy++)
      cs.push_back({sx0 - ex + (gx + 0.5) / gN * (sx1 - sx0 + 2 * ex), sy0 - ey + (gy + 0.5) / gN * (sy1 - sy0 + 2 * ey)});
    { double ox = 0, oy = 0; for (int o : open) ox += X[n + o], oy += Y[n + o]; cs.push_back({ox / 3, oy / 3}); }
    for (int o : open) { double ux = X[n + o] - mx, uy = Y[n + o] - my, L = hypot(ux, uy);
      if (L > 1e-9 * SPAN) for (double d : {0.01, 0.04}) cs.push_back({X[n + o] + d * SPAN * ux / L, Y[n + o] + d * SPAN * uy / L}); }
    vector<pair<double, vector<double>>> geo;
    for (auto& cc : cs) {
      if (el() >= xEnd) break;
      for (double f0 : frs) for (double f1 : frs) for (double f2 : frs) {
        double fr[3] = {f0, f1, f2}; vector<double> G;
        if (yGen(open, cc.first, cc.second, fr, G)) { double v = evalW(open, allT, G, nullptr); if (v > -1e299) geo.push_back({v, G}); }
      }
    }
    stable_sort(geo.begin(), geo.end(), [](const pair<double, vector<double>>& p, const pair<double, vector<double>>& q) { return p.first > q.first; });
    if (geo.size() > 6) geo.resize(6);
    vector<Cfg> cs3;
    for (auto& gg : geo) for (size_t q = 0; q < AL[3].size() && q < 32 && el() < xEnd; q++) {
      Cfg c; c.open = open; c.al = AL[3][q]; c.tm = zoneMasks(c.al, 3); c.w = gg.second;
      c.v = evalW(open, c.tm, c.w, nullptr); if (c.v > -1e299) cs3.push_back(c); }
    stable_sort(cs3.begin(), cs3.end(), [](const Cfg& p, const Cfg& q) { return p.v > q.v; });
    for (size_t i = 0; i < cs3.size() && i < 3; i++) cand.push_back(cs3[i]);
  }
  // generator search with team moves on the starts, best first, while the share lasts
  stable_sort(cand.begin(), cand.end(), [](const Cfg& p, const Cfg& q) { return p.v > q.v; });
  if (cand.size() > 16) cand.resize(16);
  int done = 0;
  for (size_t i = 0; i < cand.size() && el() < xEnd; i++) {
    dl_ = xEnd;  // r53f: bounded by the iteration counts, the clock only as a guard
    Cfg& c = cand[i]; double v0 = c.v;
    c.v = optW(c.open, c.tm, c.w, c.v, 80); done++;
    if (c.v > -1e299 && AL[3].size() > 1)
      for (int r = 0; r < 3 && el() < dl_; r++) { double v1 = c.v; optT(c, 4); c.v = optW(c.open, c.tm, c.w, c.v, 30);
        if (c.v <= v1 + 1e-9 * max(1.0, fabs(v1))) break; }
    if (dbg) { fprintf(stderr, "r53e y %zu: %.4f -> %.4f open", i, v0, c.v); for (int o : c.open) fprintf(stderr, " %d", o); fprintf(stderr, "\n"); }
    if (c.v > -1e299) top.push_back(c);
  }
  dl_ = dlKeep;
  if (dbg) fprintf(stderr, "r53e y: %zu open sets, %d starts searched (%.2fs, %lld evals)\n", ys.size(), done, el() - t0, evals - e0);
}
// the phase: returns the best assignment (site -> office) and its value
vector<int> run(double seconds, double inc, double* outVal) {
  T0 = chrono::steady_clock::now(); TL = seconds; dl_ = seconds; evals = 0; *outVal = -1e300;
  // relevant skills: needed by some site that a pool office could serve at a profit, and held by a worker
  int P = min(K, poolCap); vector<int> pool;
  {  // r56: one office per location first (co-located offices can never be open together: the office point lies in
     // both hulls), then the duplicates; the same as the best P by single value when no two of them share a point
    double tol = max(EPS, 1e-9 * SPAN); vector<int> dupl;
    for (int o : bySingle) {
      if ((int)pool.size() >= P) break;
      if (D[o].empty()) continue;  // (big path: rows only for the best offices)
      bool dup = false; for (int q : pool) if (fabs(X[n + o] - X[n + q]) <= tol && fabs(Y[n + o] - Y[n + q]) <= tol) { dup = true; break; }
      (dup ? dupl : pool).push_back(o);
    }
    for (int o : dupl) { if ((int)pool.size() >= P) break; pool.push_back(o); }
    P = pool.size();
    if (P < 2) return {};
  }
  Mask have; for (auto& m : wm) have |= m;
  Mask need; for (int s = 0; s < n; s++) { if ((sm[s] & ~have).any()) continue; bool pos = false;
    for (int o : pool) if (prof(o, s) > 0) { pos = true; break; } if (pos) need |= sm[s]; }
  vector<int> idx; R = skillBits(need, idx);
  if (R > 63) { if (dbg) fprintf(stderr, "r36: %d skill classes, skipped\n", R); return {}; }
  sMask.assign(n, 0);
  for (int s = 0; s < n; s++) { if ((sm[s] & ~have).any() || (sm[s] & ~need).any()) { sMask[s] = ~0ull; continue; }
    for (int b = 0; b < NSK; b++) if (sm[s][b]) sMask[s] |= 1ull << idx[b]; }
  map<uint64_t, vector<int>> types;
  for (int w = 0; w < W; w++) { uint64_t m = 0; for (int b = 0; b < NSK; b++) if (wm[w][b] && idx[b] >= 0) m |= 1ull << idx[b]; if (m) types[m].push_back(w); }
  tMask.clear(); tWork.clear(); for (auto& t : types) tMask.push_back(t.first), tWork.push_back(t.second);
  set<int> cls; for (int s = 0; s < n; s++) if (sMask[s] != ~0ull) cls.insert(nt[s]);
  nv = cls.size(); v1 = nv ? *cls.begin() : 0; v2 = nv ? *cls.rbegin() : 0;
  ordO.assign(K, {});
  if (nv <= 2) for (int o : pool) {  // sorted by profit (descending), then site index
    vector<pair<double, int>> ps;
    for (int s = 0; s < n; s++) if (sMask[s] != ~0ull && prof(o, s) > 0) ps.push_back({-prof(o, s), s});
    sort(ps.begin(), ps.end());
    auto& L = ordO[o]; L.reserve(ps.size()); for (auto& q : ps) L.push_back(q.second); }
  int kmax = min(P, 6);
  vector<vector<vector<uint32_t>>> AL(kmax + 1); vector<double> nCfg(kmax + 1, 0); double tot = 0;
  for (int k = 2; k <= kmax; k++) {
    AL[k] = allocs(k, 3000); double cmb = 1; for (int j = 0; j < k; j++) cmb = cmb * (P - j) / (j + 1);
    nCfg[k] = cmb * AL[k].size(); tot += nCfg[k];
  }
  if (dbg) { fprintf(stderr, "r36: pool %d skills %d types %zu classes %d (%d,%d) configs", P, R, tMask.size(), nv, v1, v2);
    for (int k = 2; k <= kmax; k++) fprintf(stderr, " k%d:%zux%.0f", k, AL[k].size(), nCfg[k] / max<size_t>(1, AL[k].size())); fprintf(stderr, "\n"); }
  if (tot < 1) return {};
  // screening: every structure, a short weight search; per-k time shares (unused time rolls over)
  map<vector<int>, Cfg> bestSet;  // r53: best screened structure per open set (k <= 4)
  const size_t M = 48; vector<Cfg> top; auto worst = [&]() { double m = 1e300; for (auto& c : top) m = min(m, c.v); return top.size() < M ? -1e300 : m; };
  double scrEnd = 0.55 * seconds, used = 0; int coarse = 3, nK = 0;
  for (int k = 2; k <= kmax; k++) if (!AL[k].empty()) nK++;
  // seconds per evaluation, from a pilot on the best offices (then a running mean)
  double tE0 = el(); long long eE0 = evals;
  { vector<int> open(pool.begin(), pool.begin() + 2); for (int r = 0; r < 4; r++) evalW(open, vector<uint64_t>(2, ~0ull), officeG(open), nullptr); }
  auto tEval = [&]() { return (el() - tE0) / max(1LL, evals - eE0); };
  for (int k = 2; k <= kmax && el() < scrEnd; k++) {
    if (AL[k].empty()) continue;
    // time share: half equal per zone count, half by the number of structures (unused time rolls over)
    double left = scrEnd - el(), kEnd = el() + left * (0.5 / nK + 0.5 * nCfg[k] / max(1.0, tot - used)); used += nCfg[k]; nK--;
    double per = (kEnd - el()) / max(1.0, nCfg[k]);
    coarse = max(0, min(3, (int)((per / max(1e-9, tEval()) - 1) / (6.0 * k))));
    vector<int> sel(k); for (int j = 0; j < k; j++) sel[j] = j;
    long done = 0;
    // too many structures for the share: every open set gets a quota of allocations (a rotating window of a
    // fixed shuffle), so all open sets are seen
    size_t nA = AL[k].size(), nSub = (size_t)llround(nCfg[k] / max<size_t>(1, nA)), quota = nA, off = 0;
    double canDo = (kEnd - el()) / max(1e-9, tEval() * (1 + 6.0 * k * coarse));
    if (canDo < nCfg[k]) { quota = max<size_t>(1, (size_t)(canDo / max<size_t>(1, nSub)));
      mt19937_64 g(777 + k); shuffle(AL[k].begin(), AL[k].end(), g); }
    while (el() < kEnd) {
      vector<int> open(k); for (int j = 0; j < k; j++) open[j] = pool[sel[j]];
      for (size_t q = 0; q < min(quota, nA); q++) {
        auto& al = AL[k][(off + q) % nA];
        if (el() > kEnd) break;
        Cfg c; c.open = open; c.al = al; c.tm = zoneMasks(al, k); c.w = officeG(open);
        c.v = evalW(open, c.tm, c.w, nullptr);
        if (c.v > -1e299 && coarse > 0) c.v = optW(open, c.tm, c.w, c.v, coarse);
        if (k <= 4) { auto it = bestSet.find(open); if (it == bestSet.end() || c.v > it->second.v) bestSet[open] = c; }  // r53
        done++;
        if (c.v > worst()) { if (top.size() >= M) { size_t wi = 0; for (size_t j = 1; j < top.size(); j++) if (top[j].v < top[wi].v) wi = j; top[wi] = c; } else top.push_back(c); }
      }
      off = (off + quota) % nA;
      int j = k - 1; while (j >= 0 && sel[j] == P - k + j) j--;
      if (j < 0) break;
      sel[j]++; for (int q = j + 1; q < k; q++) sel[q] = sel[q - 1] + 1;
    }
    if (dbg) fprintf(stderr, "r36: k=%d screened %ld/%.0f coarse %d (%.2fs, eval %.2gms)\n", k, done, nCfg[k], coarse, el(), 1e3 * tEval());
  }
  sort(top.begin(), top.end(), [](const Cfg& a, const Cfg& b) { return a.v > b.v; });
  // r38w (wide gate): stop when the screened structures stay far below the incumbent (the full generator
  // search lifts a structure by ~30 % at most: Voronoi 1.75x -> moved generators 2.27x on n3500_s7)
  static const double wideFail = 0.75;
  if ((wide || K > 8) && inc > 0 && (top.empty() || top[0].v < wideFail * inc)) {
    if (dbg) fprintf(stderr, "r36 wide: screened best %.4f < %.2f x incumbent %.4f, stop (%.2fs)\n", top.empty() ? -1.0 : top[0].v, wideFail, inc, el());
    return {};
  }
  // full search on the best ones (from the screened generators), then fan starts for the best few
  double fEnd = 0.9 * seconds;
  sort(top.begin(), top.end(), [](const Cfg& a, const Cfg& b) { return a.v > b.v; });
  double fanEnd = fEnd; fEnd = el() + 0.75 * (fanEnd - el());
  for (size_t i = 0; i < top.size() && el() < fEnd; i++) {
    dl_ = min(fEnd, el() + max(0.05, 2.0 * (fEnd - el()) / (top.size() - i)));
    if (sampled[top[i].open.size()] && top[i].v > -1e299) {  // r38w: teams and generators in turn
      for (int r = 0; r < 3 && el() < dl_; r++) { double v0 = top[i].v; optT(top[i], 4); top[i].v = optW(top[i].open, top[i].tm, top[i].w, top[i].v, 30);
        if (top[i].v <= v0 + 1e-9 * max(1.0, fabs(v0))) break; }
    } else
    top[i].v = optW(top[i].open, top[i].tm, top[i].w, top[i].v, 80);
  }
  fEnd = fanEnd;
  sort(top.begin(), top.end(), [](const Cfg& a, const Cfg& b) { return a.v > b.v; });
  vector<Cfg> fans;
  size_t nFan = min(top.size(), (size_t)4);
  for (size_t i = 0; i < nFan && el() < fEnd; i++) {
    int k = top[i].open.size();
    for (int a = -1; a < k && el() < fEnd; a++) {
      dl_ = min(fEnd, el() + max(0.05, (fEnd - el()) / ((nFan - i) * (k + 1) - (a + 1))));
      Cfg c = top[i]; c.w = fanG(c.open, a, 0); c.v = evalW(c.open, c.tm, c.w, nullptr);
      c.v = optW(c.open, c.tm, c.w, c.v, 80);
      if (dbg) fprintf(stderr, "r36 fan %zu apex %d: %.4f (was %.4f)\n", i, a, c.v, top[i].v);
      if (c.v > -1e299) fans.push_back(c);
    }
  }
  for (auto& c : fans) top.push_back(c);
  sort(top.begin(), top.end(), [](const Cfg& a, const Cfg& b) { return a.v > b.v; });
  bool farFired = farRowStarts(bestSet, pool, seconds, top);  // r53
  if (farFired) yStarts(pool, AL, top, seconds);  // r53e
  sort(top.begin(), top.end(), [](const Cfg& a, const Cfg& b) { return a.v > b.v; });
  // perturbation restarts of the best two (fixed seed) while the share lasts
  static const int ilsOn = 1;
  if (ilsOn && !top.empty() && top[0].v > inc - 0.01 * fabs(inc)) {  // only when the structure competes
    mt19937_64 g(4242); normal_distribution<double> nd(0.0, 1.0); int tries = 0, wins = 0;
    // r53e: after the far-row starts every 4th restart goes to the best structure of another zone count (2..4) or
    // of another open set (at most 3 of them, in turn): a 3-zone pinwheel can screen below the best 2-zone plan
    // and reach its level only after the generator search. top[0] keeps half of the restarts, top[1] a quarter.
    vector<size_t> extra;
    if (farFired) {
      for (int k = 2; k <= 4; k++) { bool have = false;
        for (size_t i = 0; i < top.size() && i < 2; i++) have |= (int)top[i].open.size() == k;
        if (!have) for (size_t i = 2; i < top.size(); i++) if ((int)top[i].open.size() == k && top[i].v > -1e299) { extra.push_back(i); break; } }
      for (size_t i = 2; i < top.size() && extra.size() < 3; i++) { bool nw = top[i].v > -1e299 && top[i].open != top[0].open && (top.size() < 2 || top[i].open != top[1].open);
        for (size_t q : extra) nw = nw && top[q].open != top[i].open && q != i;
        if (nw) extra.push_back(i); }
      if (extra.size() > 3) extra.resize(3);
    }
    double iEnd = 0.95 * seconds;
    for (int r = 0; el() < iEnd && r < 100000; r++) {
      size_t i = top.size() > 1 && (r & 1) ? 1 : 0; if ((r & 3) == 3 && !extra.empty()) i = extra[(r >> 2) % extra.size()];
      Cfg c = top[i]; double sc = (r % 3 == 0 ? 0.1 : 0.03) * SPAN;
      for (size_t j = 0; j < c.w.size(); j++) c.w[j] += nd(g) * (j % 3 == 2 ? sc * SPAN : sc);
      c.v = evalW(c.open, c.tm, c.w, nullptr); if (c.v <= -1e299) continue;
      dl_ = min(iEnd, el() + 0.25 * (iEnd - el()) + 0.05); c.v = optW(c.open, c.tm, c.w, c.v, 80); tries++;
      if (c.v > top[i].v + 1e-9 * max(1.0, fabs(top[i].v))) { if (dbg) fprintf(stderr, "r36 ils %zu: %.4f -> %.4f\n", i, top[i].v, c.v); top[i] = c; wins++; }
    }
    if (dbg) fprintf(stderr, "r36 ils: %d restarts, %d wins (%.2fs)\n", tries, wins, el());
  }
  dl_ = seconds;
  sort(top.begin(), top.end(), [](const Cfg& a, const Cfg& b) { return a.v > b.v; });
  if (dbg) for (size_t i = 0; i < top.size() && i < 5; i++) {
    fprintf(stderr, "r36 top %zu: %.4f open", i, top[i].v); for (int o : top[i].open) fprintf(stderr, " %d", o);
    fprintf(stderr, " masks"); for (uint64_t m : top[i].tm) fprintf(stderr, " %llx", (unsigned long long)m); fprintf(stderr, "\n"); }
  { vector<Cfg> u; for (auto& c : top) { bool dup = false;  // distinct (open set, teams) for the finish slots
      for (auto& d : u) if (d.open == c.open && d.tm == c.tm) { dup = true; break; } if (!dup) u.push_back(c); } top = u; }
  Sol best; double bv = -1e300;
  for (size_t i = 0; i < top.size() && i < 4 && el() < seconds; i++) {
    if (top[i].v <= -1e299) break;
    Sol s; double v = finish(top[i], s); if (v > bv) bv = v, best = s;
  }
  if (dbg) fprintf(stderr, "r36: %lld evals, best %.4f (%.2fs)\n", evals, bv, el());
  if (bv <= -1e299) return {};
  *outVal = bv; return asgOfW(best);
}
}  // namespace r36
}  // namespace r29s
// ---- r37: structure local search for the equal-load regime with a loose count window
// Target: instance0-like inputs (huge alpha, count window that never binds, many task-free sites, single-skill
// teams): the best plans have MORE zones at a LOWER common task level T, with skill-specialised teams. A structure
// is (open offices, worker types per zone, power diagram with free generators); its value is exact for the
// cells: per zone the best profit with load exactly T and at most maxSize sites (DP over the task-count classes,
// free sites fill the rest; a Lagrangian count price when maxSize binds), maximised over the common T.
// Search: seeds (incumbent structure, greedy office additions), then a beam of hill climbs over add / drop /
// swap office moves (quick evaluation of every move, polish of the best few: team transfers + generator
// coordinate search), then perturbation restarts. Runs before the fork, deterministic.
namespace r29s {
namespace r37 {
static const bool dbg = false;
int R = 0, NT = 0, VM = 0;
vector<uint32_t> sMask;                       // per site: relevant skill bits (~0u: unservable)
vector<uint32_t> tMask; vector<int> tCnt; vector<vector<int>> tWork;
double dl_ = 0; long long evals = 0;
static const int kmaxEnv = 0;
int KMAX = 12;  // most zones of a structure: max(12, incumbent zones + 6), at most 30 (set in run)
int TCMAX = 50000;  // common levels above this are not considered (DP size): min(50000, max(5000, 4e6 / (VM + 1))), set in run

struct St { vector<int> open; vector<uint32_t> ts; vector<double> G; double v = -1e300; int T = -1; };

inline double pd(int p, const vector<double>& G, int i) { double dx = X[p] - G[3 * i], dy = Y[p] - G[3 * i + 1]; return dx * dx + dy * dy - G[3 * i + 2]; }
bool ownG(const vector<int>& open, const vector<double>& G) {
  int k = open.size();
  for (int i = 0; i < k; i++) { double di = pd(n + open[i], G, i);
    for (int j = 0; j < k; j++) if (j != i && pd(n + open[i], G, j) <= di + 1e-9 * SPAN * SPAN) return false; }
  return true;
}
uint32_t zmask(uint32_t ts) { uint32_t m = 0; for (int t = 0; t < NT; t++) if (ts >> t & 1) m |= tMask[t]; return m; }

// ---- per-zone curve: f[T] = best profit with load exactly T and at most cap sites
struct Zone {
  vector<vector<int>> cl;           // cl[v]: candidate sites with v tasks, sorted by profit (desc)
  vector<vector<double>> P;         // prefix sums
  int Tl = 0, cap = 0;
  vector<double> f; vector<int> fm;  // f[T], index of the count price used at T (-1: infeasible)
  vector<double> mus;
};
vector<Zone> Z;
// DP over the loaded classes with count price mu: g[T] (profit - mu*count), c[T] (count); ch[v][T] = x choice.
// Per class the step is a max-plus convolution with a concave sequence (sorted prefix sums minus mu*x): along each
// residue chain the (largest) optimal source index is monotone, so divide and conquer over the chain.
static vector<double> dcG, dcH; static vector<int> dcX;
static void dcRun(const vector<double>& P, double mu, int m, int lo, int hi, int optL, int optR) {
  while (lo <= hi) {
    int mid = (lo + hi) >> 1; double best = -1e300; int bj = -1;
    int jl = max(optL, mid - m), jr = min(optR, mid);
    for (int j = jl; j <= jr; j++) { double gv = dcG[j]; if (gv <= -1e299) continue;
      double val = gv + P[mid - j] - mu * (mid - j); if (val >= best) best = val, bj = j; }
    dcH[mid] = best; dcX[mid] = bj >= 0 ? mid - bj : -1;
    int split = bj >= 0 ? bj : jl;
    // recurse on the smaller half, loop on the other
    if (mid - lo < hi - mid) { dcRun(P, mu, m, lo, mid - 1, optL, split); lo = mid + 1; optL = split; }
    else { dcRun(P, mu, m, mid + 1, hi, split, optR); hi = mid - 1; optR = split; }
  }
}
static void dpRun(const Zone& z, double mu, vector<double>& g, vector<int>& c, vector<vector<int>>* ch) {
  int Tl = z.Tl; g.assign(Tl + 1, -1e300); c.assign(Tl + 1, 0); g[0] = 0;
  static vector<double> ng; static vector<int> nc; ng.assign(Tl + 1, -1e300); nc.assign(Tl + 1, 0);
  if (ch) ch->assign(VM + 1, vector<int>());
  for (int v = 1; v <= VM; v++) {
    int m = z.cl[v].size(); if (m == 0 || v > Tl) continue;
    const vector<double>& P = z.P[v];
    if (ch) (*ch)[v].assign(Tl + 1, 0);
    for (int r = 0; r < v && r <= Tl; r++) {
      int L = (Tl - r) / v + 1;
      dcG.resize(L); dcH.assign(L, -1e300); dcX.assign(L, -1);
      for (int j = 0; j < L; j++) dcG[j] = g[r + v * j];
      dcRun(P, mu, m, 0, L - 1, 0, L - 1);
      for (int j = 0; j < L; j++) { int T = r + v * j, x = dcX[j];
        if (x < 0) { ng[T] = -1e300; nc[T] = 0; if (ch) (*ch)[v][T] = 0; continue; }
        ng[T] = dcH[j]; nc[T] = c[T - v * x] + x; if (ch) (*ch)[v][T] = x; }
    }
    g.swap(ng); c.swap(nc);
  }
}
static void dpRunBF(const Zone& z, double mu, vector<double>& g, vector<int>& c) {
  int Tl = z.Tl; g.assign(Tl + 1, -1e300); c.assign(Tl + 1, 0); g[0] = 0;
  vector<double> ng(Tl + 1); vector<int> nc(Tl + 1);
  for (int v = 1; v <= VM; v++) {
    int m = z.cl[v].size(); if (m == 0 || v > Tl) continue;
    const vector<double>& P = z.P[v];
    for (int T = 0; T <= Tl; T++) {
      double bv = g[T]; int bc = c[T];
      int xm = min(m, T / v);
      for (int x = 1; x <= xm; x++) { double gv = g[T - v * x]; if (gv <= -1e299) continue;
        double val = gv + P[x] - mu * x; if (val > bv) bv = val, bc = c[T - v * x] + x; }
      ng[T] = bv; nc[T] = bc;
    }
    g.swap(ng); c.swap(nc);
  }
}
static long long chkN = 0, chkBad = 0; static const bool chkOn = false;
// returns -1e300 when the phase is out of time (the curve is then incomplete and must not be used)
static double zoneCurve(Zone& z) {
  int Tl = z.Tl; z.f.assign(Tl + 1, -1e300); z.fm.assign(Tl + 1, -1);
  const vector<double>& P0 = z.P[0]; int n0 = z.cl[0].size();
  vector<double> g; vector<int> c;
  z.mus.assign(1, 0.0);
  for (size_t mi = 0; mi < z.mus.size(); mi++) {
    if (el() > TL) return -1e300;
    double mu = z.mus[mi]; dpRun(z, mu, g, c, nullptr);
    if (chkOn) { vector<double> g2; vector<int> c2; dpRunBF(z, mu, g2, c2); chkN++;
      for (int T = 0; T <= z.Tl; T++) if ((g[T] <= -1e299) != (g2[T] <= -1e299) || (g[T] > -1e299 && fabs(g[T] - g2[T]) > 1e-6 * max(1.0, fabs(g2[T])))) { chkBad++; if (chkBad < 5) fprintf(stderr, "CHK T=%d dc %.3f bf %.3f\n", T, g[T], g2[T]); break; } }
    bool binds = false;
    for (int T = 0; T <= Tl; T++) { if (g[T] <= -1e299 || c[T] > z.cap) continue;
      int f0 = min(n0, z.cap - c[T]); if (c[T] + n0 > z.cap) binds = true;
      double v = g[T] + mu * c[T] + P0[f0];
      if (v > z.f[T]) z.f[T] = v, z.fm[T] = mi; }
    if (mi == 0 && binds && n0 > 0) {  // count prices: marginal free site at the cap boundary for a few levels
      for (double fr : {0.25, 0.5, 0.75, 1.0}) { int T = (int)(fr * Tl); if (T < 0 || g[T] <= -1e299) continue;
        int idx = z.cap - c[T]; if (idx >= 1 && idx <= n0) { double mu2 = P0[idx] - P0[idx - 1]; if (mu2 > 0) z.mus.push_back(mu2); } }
      sort(z.mus.begin() + 1, z.mus.end()); z.mus.erase(unique(z.mus.begin() + 1, z.mus.end()), z.mus.end());
    }
  }
  return el() > TL ? -1e300 : 0.0;
}
// members of zone z at load T
static void zonePick(const Zone& z, int o, int T, vector<int>& out) {
  out.clear(); if (T < 0 || T > z.Tl || z.fm[T] < 0) return;
  double mu = z.mus[z.fm[T]]; vector<double> g; vector<int> c; vector<vector<int>> ch;
  dpRun(z, mu, g, c, &ch);
  int t = T;
  for (int v = VM; v >= 1; v--) { if (ch[v].empty()) continue; int x = ch[v][t]; for (int j = 0; j < x; j++) out.push_back(z.cl[v][j]); t -= v * x; }
  int f0 = min((int)z.cl[0].size(), z.cap - (int)out.size());
  for (int j = 0; j < f0; j++) out.push_back(z.cl[0][j]);
  (void)o;
}
// curve cache per office: (team mask, hash of the candidate set) -> f up to some level (most evaluations change
// one or two zones only: a generator step or a team move)
struct CEnt { uint32_t ts = 0; uint64_t h = 0; int Tl = -1; vector<double> f; };
vector<vector<CEnt>> cache; vector<int> cacheNext; vector<uint64_t> zob; bool useCache = true;
vector<double> cellG, cellD; vector<int> cellOf;  // power-cell memo of evalS
long long cHit = 0, cMiss = 0, cacheD = 0;  // cacheD: doubles held by the cache (capped: 160 MB)
// value of a structure; fills Z (curves; members only when full) and returns the best common level in *Tout
double evalS(const vector<int>& open, const vector<uint32_t>& ts, const vector<double>& G, int* Tout, bool full = false) {
  int k = open.size(); evals++;
  if (k == 0 || el() > TL) return -1e300;
  if (!ownG(open, G)) return -1e300;
  if ((int)Z.size() < k) Z.resize(k);
  static vector<uint32_t> zm; zm.assign(k, 0); for (int i = 0; i < k; i++) zm[i] = zmask(ts[i]);
  static vector<uint64_t> hh; hh.assign(k, 0); static vector<vector<int>> cnt; cnt.assign(k, vector<int>(VM + 1, 0));
  static vector<int> zoneOf; zoneOf.assign(n, -1);
  // power cells, memoised: same generators -> reused, one generator changed -> incremental update
  int chg = -1, nchg = 0;
  if (cellG.size() == G.size() && (int)cellOf.size() == n) {
    for (int i = 0; i < k && nchg < 2; i++) if (G[3 * i] != cellG[3 * i] || G[3 * i + 1] != cellG[3 * i + 1] || G[3 * i + 2] != cellG[3 * i + 2]) chg = i, nchg++;
  } else nchg = 2;
  if (nchg >= 2) {
    cellOf.assign(n, -1); cellD.assign(n, 0.0);
    for (int s = 0; s < n; s++) { if (sMask[s] == ~0u) continue;
      int bi = 0; double bd = pd(s, G, 0);
      for (int i = 1; i < k; i++) { double d = pd(s, G, i); if (d < bd) bd = d, bi = i; }
      cellOf[s] = bi; cellD[s] = bd; }
  } else if (nchg == 1) {
    for (int s = 0; s < n; s++) { if (sMask[s] == ~0u) continue;
      if (cellOf[s] == chg) { int bi = 0; double bd = pd(s, G, 0);
        for (int i = 1; i < k; i++) { double d = pd(s, G, i); if (d < bd) bd = d, bi = i; }
        cellOf[s] = bi; cellD[s] = bd; }
      else { double d = pd(s, G, chg); if (d < cellD[s] || (d == cellD[s] && chg < cellOf[s])) cellOf[s] = chg, cellD[s] = d; } }
  }
  if (nchg > 0) cellG = G;
  for (int s = 0; s < n; s++) {
    if (sMask[s] == ~0u) continue;
    int bi = cellOf[s];
    if (sMask[s] & ~zm[bi]) continue;
    double p = prof(open[bi], s);
    if (nt[s] == 0 ? p > 0 : p > -alpha * nt[s]) { zoneOf[s] = bi; hh[bi] ^= zob[s]; cnt[bi][nt[s]]++; }
  }
  int Tc = INT_MAX; double costSum = 0;
  static vector<int> ml; ml.assign(k, 0);
  for (int i = 0; i < k; i++) {
    int o = open[i]; costSum += cost[o];
    int left = ms[o], m = 0;  // max load with at most maxSize sites
    for (int v = VM; v >= 1 && left > 0; v--) { int x = min(left, cnt[i][v]); m += x * v; left -= x; }
    ml[i] = m; Tc = min(Tc, m);
  }
  if (Tc == INT_MAX) return -1e300;
  Tc = min(Tc, TCMAX);
  static vector<const vector<double>*> fp; fp.assign(k, nullptr);
  static vector<int> need; need.clear();
  for (int i = 0; i < k; i++) {
    if (useCache && !full) { for (auto& e : cache[open[i]]) if (e.ts == ts[i] && e.h == hh[i] && e.Tl >= Tc) { fp[i] = &e.f; break; } }
    if (fp[i]) { cHit++; continue; }
    cMiss++; need.push_back(i); Zone& z = Z[i]; z.cl.resize(VM + 1); for (int v = 0; v <= VM; v++) { z.cl[v].clear(); z.cl[v].reserve(cnt[i][v]); }
  }
  if (!need.empty()) {
    static vector<int> slot; slot.assign(k, -1); for (int i : need) slot[i] = 1;
    for (int s = 0; s < n; s++) { int i = zoneOf[s]; if (i >= 0 && slot[i] > 0) Z[i].cl[nt[s]].push_back(s); }
    for (int i : need) {
      Zone& z = Z[i]; int o = open[i]; z.cap = ms[o]; z.P.resize(VM + 1);
      for (int v = 0; v <= VM; v++) { auto& L = z.cl[v];
        sort(L.begin(), L.end(), [&](int a, int b) { double pa = prof(o, a), pb = prof(o, b); return pa > pb || (pa == pb && a < b); });
        z.P[v].assign(L.size() + 1, 0.0); for (size_t j = 0; j < L.size(); j++) z.P[v][j + 1] = z.P[v][j] + prof(o, L[j]); }
      z.Tl = full ? Tc : min(ml[i], Tc + Tc / 4 + 8);
      if (zoneCurve(z) <= -1e299) return -1e300;  // out of time: nothing incomplete reaches the cache
      fp[i] = &z.f;
      if (useCache && !full) { auto& C = cache[o]; int j = C.size() < 8 ? -1 : cacheNext[o];
        long long freed = j >= 0 ? (long long)C[j].f.size() : 0;  // the round-robin victim's doubles
        if (cacheD - freed + (long long)z.f.size() <= 20000000LL) {
          if (j < 0) { C.push_back(CEnt()); j = C.size() - 1; } else cacheNext[o] = (j + 1) % 8;
          cacheD += (long long)z.f.size() - freed;
          C[j].ts = ts[i]; C[j].h = hh[i]; C[j].Tl = z.Tl; C[j].f = z.f; fp[i] = &C[j].f; } }
    }
  }
  double bv = -1e300; int bT = -1;
  for (int T = 0; T <= Tc; T++) { double v = 0; bool ok = true;
    for (int i = 0; i < k && ok; i++) { double f = (*fp[i])[T]; if (f <= -1e299) ok = false; else v += f; }
    if (ok && v > bv) bv = v, bT = T; }
  if (bT < 0) return -1e300;
  if (Tout) *Tout = bT;
  return bv - costSum;
}
double evalSt(St& s) { s.v = evalS(s.open, s.ts, s.G, &s.T); return s.v; }

// ---- teams
void usedOf(const St& s, vector<int>& used) { used.assign(NT, 0); for (uint32_t t : s.ts) for (int j = 0; j < NT; j++) if (t >> j & 1) used[j]++; }
// spare workers go to the zones that gain most from them (adding a type never lowers a zone's curve)
void spareFill(St& s) {
  vector<int> used; usedOf(s, used); int k = s.open.size();
  for (int t = 0; t < NT; t++) {
    while (used[t] < tCnt[t] && el() < dl_) {
      int bi = -1; double bv = s.v;
      int lack = 0; for (int i = 0; i < k; i++) if (!(s.ts[i] >> t & 1)) lack++;
      if (lack == 0) break;
      if (lack <= tCnt[t] - used[t]) { for (int i = 0; i < k; i++) s.ts[i] |= 1u << t; used[t] += lack; evalSt(s); break; }
      for (int i = 0; i < k; i++) if (!(s.ts[i] >> t & 1)) {
        s.ts[i] |= 1u << t; int T; double v = evalS(s.open, s.ts, s.G, &T); s.ts[i] &= ~(1u << t);
        if (v > bv + 1e-9 * max(1.0, fabs(bv)) || bi < 0) { if (bi < 0 || v > bv) bv = v, bi = i; } }
      if (bi < 0) break;
      s.ts[bi] |= 1u << t; used[t]++; evalSt(s);
    }
  }
}
// first-improvement team moves: remove a type, move a type from one zone to another, swap types between zones
bool improveTeams(St& s, int passes) {
  int k = s.open.size(); bool any = false;
  for (int p = 0; p < passes && el() < dl_; p++) {
    bool imp = false; vector<int> used; usedOf(s, used);
    for (int t = 0; t < NT && el() < dl_; t++) {
      for (int i = 0; i < k && el() < dl_; i++) {
        if (s.ts[i] >> t & 1) continue;
        // i lacks t: take it from a zone j (or from the spare pool)
        if (used[t] < tCnt[t]) { s.ts[i] |= 1u << t; double old = s.v; St b = s; evalSt(s); if (s.v > old + 1e-9 * max(1.0, fabs(old))) { imp = true; used[t]++; continue; } s = b; continue; }
        for (int j = 0; j < k && el() < dl_; j++) if (j != i && (s.ts[j] >> t & 1)) {
          St b = s; s.ts[j] &= ~(1u << t); s.ts[i] |= 1u << t; double old = b.v; evalSt(s);
          if (s.v > old + 1e-9 * max(1.0, fabs(old))) { imp = true; break; }
          s = b;
        }
      }
    }
    // pair transfers: zone i gets types t and u from zones j1, j2 (joint skills such as {2,3})
    if (!imp && NT <= 12) {
      for (int i = 0; i < k && !imp && el() < dl_; i++)
        for (int t = 0; t < NT && !imp; t++) if (!(s.ts[i] >> t & 1))
          for (int u = t + 1; u < NT && !imp; u++) if (!(s.ts[i] >> u & 1)) {
            // donors: the zones with t (u) whose loss is smallest = try each (bounded)
            vector<int> dt, du; if (used[t] < tCnt[t]) dt.push_back(-1); if (used[u] < tCnt[u]) du.push_back(-1);
            for (int j = 0; j < k; j++) { if (j != i && (s.ts[j] >> t & 1)) dt.push_back(j); if (j != i && (s.ts[j] >> u & 1)) du.push_back(j); }
            if (dt.empty() || du.empty() || dt.size() * du.size() > 30) continue;
            for (int a : dt) { for (int b : du) {
              St bk = s; if (a >= 0) s.ts[a] &= ~(1u << t); if (b >= 0) s.ts[b] &= ~(1u << u); s.ts[i] |= (1u << t) | (1u << u);
              double old = bk.v; evalSt(s);
              if (s.v > old + 1e-9 * max(1.0, fabs(old))) { imp = true; break; }
              s = bk; } if (imp) break; }
          }
    }
    if (!imp) break;
    any = true; spareFill(s);
  }
  return any;
}
// generator coordinate search
double optW(St& s, int iters) {
  int k = s.open.size(); double step = 0.04 * SPAN; double v = s.v;
  for (int it = 0; it < iters && el() < dl_; it++) {
    bool imp = false;
    for (int i = 0; i < 3 * k && el() < dl_; i++) for (int sg = 1; sg >= -1; sg -= 2) {
      vector<double> w2 = s.G; w2[i] += sg * (i % 3 == 2 ? step * SPAN : step); int T; double v2 = evalS(s.open, s.ts, w2, &T);
      if (v2 > v + 1e-9 * max(1.0, fabs(v))) { v = v2; s.G = w2; s.T = T; imp = true; break; }
    }
    if (!imp) { step *= 0.5; if (step < 2e-4 * SPAN) break; }
  }
  s.v = v; return v;
}
// generator for a new zone at office o (index i in s): at the office, weight inside the ownership window
bool placeGen(St& s, int i) {
  int k = s.open.size(), o = s.open[i]; double lo = -1e300, hi = 1e300;
  s.G[3 * i] = X[n + o]; s.G[3 * i + 1] = Y[n + o];
  for (int j = 0; j < k; j++) if (j != i) {
    lo = max(lo, -pd(n + o, s.G, j));                                   // o in its own cell: -w < pd(o, j)
    double d2 = ed2(n + s.open[j], n + o); hi = min(hi, d2 - pd(n + s.open[j], s.G, j));  // o_j stays in cell j
  }
  if (lo >= hi - 1e-9 * SPAN * SPAN) return false;
  double w = (lo < 0 && hi > 0) ? 0.0 : (lo > -1e299 && hi < 1e299 ? 0.5 * (lo + hi) : (lo > -1e299 ? lo + 0.01 * SPAN * SPAN : hi - 0.01 * SPAN * SPAN));
  s.G[3 * i + 2] = w; return ownG(s.open, s.G);
}
void polish(St& s, int wIters) {
  spareFill(s); improveTeams(s, 3); optW(s, wIters); improveTeams(s, 2);
}
// ---- moves
bool mvDrop(const St& s, int i, St& r) {
  if (s.open.size() <= 1) return false;
  r = s; r.open.erase(r.open.begin() + i); r.ts.erase(r.ts.begin() + i); r.G.erase(r.G.begin() + 3 * i, r.G.begin() + 3 * i + 3);
  evalSt(r); spareFill(r); return r.v > -1e299;
}
bool mvAdd(const St& s, int o, St& r) {
  r = s; r.open.push_back(o); r.ts.push_back(0); r.G.insert(r.G.end(), {0.0, 0.0, 0.0});
  if (!placeGen(r, r.open.size() - 1)) return false;
  evalSt(r); spareFill(r); return r.v > -1e299;
}
bool mvSwap(const St& s, int i, int o, St& r) {
  r = s; r.open[i] = o;
  if (!ownG(r.open, r.G) && !placeGen(r, i)) return false;
  evalSt(r); spareFill(r); return r.v > -1e299;
}
vector<int> key(const St& s) { vector<int> o = s.open; sort(o.begin(), o.end()); return o; }

// ---- build, check and repair a structure
double finish(const St& c, Sol& s) {
  int T = -1; double est = evalS(c.open, c.ts, c.G, &T, true);
  if (est <= -1e299 || T < 0) return -1e300;
  int k = c.open.size(); s = Sol(); s.mem.assign(K, {}); s.wk.assign(K, {}); s.tag = "r37";
  vector<int> next(NT, 0);
  for (int i = 0; i < k; i++) {
    int o = c.open[i]; zonePick(Z[i], o, T, s.mem[o]);
    if (s.mem[o].empty()) continue;
    for (int t = 0; t < NT; t++) if (c.ts[i] >> t & 1) { if (next[t] < (int)tWork[t].size()) s.wk[o].push_back(tWork[t][next[t]++]); }
  }
  string why; double v = evalFull(s, &why);
  if (dbg) fprintf(stderr, "r37 finish: est %.4f full %.4f %s %s\n", est, v, why.c_str(), summary(s).c_str());
  if (v > -1e299) { s.val = v; return v; }
  if (el() > 0.97 * TL || n > 50000) return -1e300;
  repairHull(s.mem);
  if (el() > TL) return -1e300;
  vector<int> open; vector<vector<int>> el2; vector<vector<int>> tw;
  for (int o = 0; o < K; o++) if (!s.mem[o].empty()) open.push_back(o), el2.push_back(s.mem[o]), tw.push_back(s.wk[o]);
  LevelRes lr = levelSearch(open, el2); Sol t; t.mem.assign(K, {}); t.wk.assign(K, {}); t.tag = "r37r";
  if (!lr.mem.empty()) for (size_t i = 0; i < open.size(); i++) { t.mem[open[i]] = lr.mem[open[i]]; if (!t.mem[open[i]].empty()) t.wk[open[i]] = tw[i]; }
  why.clear(); v = evalFull(t, &why); if (dbg) fprintf(stderr, "r37 repaired: %.4f %s\n", v, why.c_str());
  if (v <= -1e299) return -1e300;
  s = t; s.val = v; return v;
}
string brief(const St& s) {
  char buf[96]; snprintf(buf, sizeof buf, "k=%d T=%d v=%.1f open", (int)s.open.size(), s.T, s.v); string r = buf;
  for (size_t i = 0; i < s.open.size(); i++) { snprintf(buf, sizeof buf, " %d:%x", s.open[i], s.ts[i]); r += buf; }
  return r;
}
// structure of an assignment (site -> office): open offices, teams covering the served skills
bool fromAsg(const vector<int>& a, St& s) {
  s = St(); vector<uint32_t> need(K, 0); vector<char> op(K, 0);
  for (int x = 0; x < n && x < (int)a.size(); x++) if (a[x] >= 0 && a[x] < K) { op[a[x]] = 1; if (sMask[x] != ~0u) need[a[x]] |= sMask[x]; }
  for (int o = 0; o < K; o++) if (op[o]) s.open.push_back(o);
  int k = s.open.size(); if (k == 0 || k > KMAX) return false;
  s.ts.assign(k, 0); vector<int> used(NT, 0);
  for (int i = 0; i < k; i++) { uint32_t nd = need[s.open[i]], cov = 0;
    for (int b = 0; b < R; b++) if ((nd >> b & 1) && !(cov >> b & 1)) {
      int bt = -1; for (int t = 0; t < NT; t++) if ((tMask[t] >> b & 1) && used[t] < tCnt[t] && (bt < 0 || __builtin_popcount(tMask[t]) < __builtin_popcount(tMask[bt]))) bt = t;
      if (bt >= 0) { s.ts[i] |= 1u << bt; used[bt]++; cov |= tMask[bt]; } } }
  s.G.clear(); for (int o : s.open) s.G.push_back(X[n + o]), s.G.push_back(Y[n + o]), s.G.push_back(0.0);
  return ownG(s.open, s.G);
}

// the phase: returns the best assignment (site -> office [+ workers]) and its value
vector<int> run(double seconds, const vector<int>& incAsg, double inc, double* outVal) {
  T0 = chrono::steady_clock::now(); TL = seconds; dl_ = 0.9 * seconds; evals = 0; *outVal = -1e300;
  Mask have; for (auto& m : wm) have |= m;
  Mask need; for (int s = 0; s < n; s++) { if ((sm[s] & ~have).any()) continue; need |= sm[s]; }
  vector<int> idx; R = skillBits(need, idx);
  if (R > 24) { if (dbg) fprintf(stderr, "r37: %d skill classes, skipped\n", R); return {}; }
  sMask.assign(n, 0); VM = 0;
  for (int s = 0; s < n; s++) { if ((sm[s] & ~have).any()) { sMask[s] = ~0u; continue; }
    for (int b = 0; b < NSK; b++) if (sm[s][b]) sMask[s] |= 1u << idx[b];
    VM = max(VM, nt[s]); }
  if (VM > 64) { if (dbg) fprintf(stderr, "r37: %d tasks per site, skipped\n", VM); return {}; }
  TCMAX = min(50000, max(5000, 4000000 / (VM + 1)));  // one curve costs ~VM x level: bounded work per zone
  map<uint32_t, vector<int>> types;
  for (int w = 0; w < W; w++) { uint32_t m = 0; for (int b = 0; b < NSK; b++) if (wm[w][b] && idx[b] >= 0) m |= 1u << idx[b]; if (m) types[m].push_back(w); }
  tMask.clear(); tWork.clear(); tCnt.clear();
  for (auto& t : types) tMask.push_back(t.first), tWork.push_back(t.second), tCnt.push_back(t.second.size());
  NT = tMask.size();
  if (NT == 0 || NT > 20) { if (dbg) fprintf(stderr, "r37: %d worker types, skipped\n", NT); return {}; }
  cache.assign(K, {}); cacheNext.assign(K, 0); zob.resize(n); { mt19937_64 zg(31337); for (auto& z : zob) z = zg(); } cHit = cMiss = cacheD = 0; cellG.clear(); cellOf.clear(); cellD.clear();
  // offices ordered by single value; candidates for additions = the best ones (all when K is small)
  static const int poolEnv = 40;
  int P = min(K, max(1, poolEnv)); vector<int> pool(bySingle.begin(), bySingle.begin() + P);
  map<vector<int>, St> seen;  // best state per open set
  vector<St> beam; const size_t B = 6;
  auto offerS = [&](const St& s) {
    if (s.v <= -1e299) return;
    vector<int> kk = key(s); auto it = seen.find(kk);
    if (it != seen.end() && it->second.v >= s.v) return;
    seen[kk] = s;
    for (auto& b : beam) if (key(b) == kk) { if (s.v > b.v) b = s; goto sorted; }
    beam.push_back(s);
  sorted:
    sort(beam.begin(), beam.end(), [](const St& a, const St& b) { return a.v > b.v; });
    if (beam.size() > B) beam.resize(B);
  };
  { int k0 = 0; vector<char> u(K, 0); for (int x = 0; x < n && x < (int)incAsg.size(); x++) if (incAsg[x] >= 0 && incAsg[x] < K && !u[incAsg[x]]) u[incAsg[x]] = 1, k0++;
    KMAX = kmaxEnv > 0 ? kmaxEnv : min(30, max(12, k0 + 6)); }
  // seeds: the incumbent structure, the best single office
  // tEval: one evaluation from scratch (no cached curve), the yardstick for the time finish() needs
  double tEval = 0;
  { St s; if (fromAsg(incAsg, s)) { double te0 = el(); evalSt(s); tEval = el() - te0; double dl0 = dl_; dl_ = 0.25 * seconds; polish(s, 30); dl_ = dl0; if (dbg) fprintf(stderr, "r37 seed inc: %s (inc %.1f, %.2fs, eval %.3fs)\n", brief(s).c_str(), inc, el(), tEval); offerS(s); } }
  St cur; cur.open = {pool[0]}; cur.ts = {0}; cur.G = {X[n + pool[0]], Y[n + pool[0]], 0.0}; evalSt(cur); spareFill(cur);
  // greedy chain: best addition (quick scan of the pool, polish of the best 3) up to KMAX zones
  double chainEnd = 0.35 * seconds, chainBest = cur.v; int chainBestK = 1;
  for (int k = 2; k <= min(KMAX, K) && el() < chainEnd; k++) {
    vector<pair<double, int>> sc; vector<char> isOpen(K, 0); for (int o : cur.open) isOpen[o] = 1;
    for (int o : pool) if (!isOpen[o] && el() < chainEnd) { St r; if (mvAdd(cur, o, r)) sc.push_back({r.v, o}); }
    if (sc.empty()) break;
    sort(sc.rbegin(), sc.rend());
    St bst; bst.v = -1e300;
    for (size_t j = 0; j < sc.size() && j < 3 && el() < chainEnd; j++) { St r; if (!mvAdd(cur, sc[j].second, r)) continue; polish(r, 20); if (r.v > bst.v) bst = r; }
    if (bst.v <= -1e299) break;
    cur = bst; offerS(cur);
    if (dbg) fprintf(stderr, "r37 chain: %s (%.2fs, %lld evals)\n", brief(cur).c_str(), el(), evals);
    if (cur.v > chainBest + 1e-9 * max(1.0, fabs(chainBest))) chainBest = cur.v, chainBestK = k;
    else if (k >= chainBestK + 4 && k >= 8) break;  // four additions without a gain: more zones do not pay
  }
  // one scan: quick evaluation of every move (drop, add from the pool, swap with the 6 nearest closed offices),
  // polish of the best few; returns the best polished neighbour
  auto scan = [&](const St& s, double until, int nPol) {
    int k = s.open.size(); vector<char> isOpen(K, 0); for (int o : s.open) isOpen[o] = 1;
    vector<pair<double, int>> sc; vector<St> rs;
    auto push = [&](St& r) { sc.push_back({r.v, (int)rs.size()}); rs.push_back(r); };
    for (int i = 0; i < k && k > 2 && el() < until; i++) { St r; if (mvDrop(s, i, r)) push(r); }
    if (k < KMAX) for (int o : pool) if (!isOpen[o] && el() < until) { St r; if (mvAdd(s, o, r)) push(r); }
    for (int i = 0; i < k && el() < until; i++) {
      vector<pair<double, int>> nb; for (int o : pool) if (!isOpen[o]) nb.push_back({ed2(n + o, n + s.open[i]), o});
      sort(nb.begin(), nb.end());
      for (size_t j = 0; j < nb.size() && j < 6 && el() < until; j++) { St r; if (mvSwap(s, i, nb[j].second, r)) push(r); }
    }
    sort(sc.rbegin(), sc.rend());
    St bst; bst.v = -1e300;
    for (size_t j = 0; j < sc.size() && (int)j < nPol && el() < until; j++) { St r = rs[sc[j].second]; polish(r, 25); if (r.v > bst.v) bst = r; }
    return bst;
  };
  // climb to a local optimum (best polished neighbour while it improves)
  auto climb = [&](St s, double until) {
    for (int it = 0; it < 50 && el() < until; it++) {
      St b = scan(s, until, 4);
      if (b.v > s.v + 1e-9 * max(1.0, fabs(s.v))) s = b; else break;
    }
    return s;
  };
  // finish() of beam[0] (a full evaluation, the member picks, evalFull) must fit before the end
  double reserve = min(0.3 * seconds, 3 * tEval);
  double climbEnd = min(0.8 * seconds, seconds - reserve);
  { vector<St> b0 = beam; for (auto& s : b0) { if (el() > climbEnd) break; St r = climb(s, climbEnd); offerS(r);
      if (dbg) fprintf(stderr, "r37 climb: %s -> %s (%.2fs, %lld evals)\n", brief(s).c_str(), brief(r).c_str(), el(), evals); } }
  // perturbation restarts (iterated local search) from the beam
  mt19937_64 g(9137); int kicks = 0, wins = 0;
  while (el() < climbEnd && !beam.empty()) {
    St s = beam[kicks % min<size_t>(beam.size(), 3)]; kicks++;
    double before = beam[0].v;
    int nm = 1 + (int)(g() % 2);
    for (int m = 0; m < nm; m++) {
      vector<char> isOpen(K, 0); for (int o : s.open) isOpen[o] = 1;
      vector<int> cand; for (int o : pool) if (!isOpen[o]) cand.push_back(o);
      int typ = g() % 3; St r;
      if (typ == 0 && !cand.empty() && (int)s.open.size() < KMAX) { if (mvAdd(s, cand[g() % cand.size()], r)) s = r; }
      else if (typ == 1 && s.open.size() > 2) { if (mvDrop(s, g() % s.open.size(), r)) s = r; }
      else if (!cand.empty()) { if (mvSwap(s, g() % s.open.size(), cand[g() % cand.size()], r)) s = r; }
    }
    polish(s, 30); s = climb(s, climbEnd); offerS(s);
    if (beam[0].v > before) { wins++; if (dbg) fprintf(stderr, "r37 kick %d: %s (%.2fs)\n", kicks, brief(beam[0]).c_str(), el()); }
  }
  if (dbg) fprintf(stderr, "r37 ils: %d kicks, %d wins (%.2fs, %lld evals)\n", kicks, wins, el(), evals);
  // full generator search for the best few
  dl_ = min(0.95 * seconds, seconds - reserve);
  for (size_t i = 0; i < beam.size() && i < 3 && el() < dl_; i++) { optW(beam[i], 80); improveTeams(beam[i], 2); }
  sort(beam.begin(), beam.end(), [](const St& a, const St& b) { return a.v > b.v; });
  dl_ = seconds;
  Sol best; double bv = -1e300;
  for (size_t i = 0; i < beam.size() && i < 3 && el() < seconds && (i == 0 || el() <= 0.97 * seconds); i++) {
    if (dbg) fprintf(stderr, "r37 top %zu: %s\n", i, brief(beam[i]).c_str());
    Sol s; double v = finish(beam[i], s); if (v > bv) bv = v, best = s;
  }
  if (dbg) fprintf(stderr, "r37: %lld evals (curve cache %lld hits, %lld misses), best %.4f (%.2fs)\n", evals, cHit, cMiss, bv, el());
  cache.clear(); cache.shrink_to_fit();
  if (chkOn) fprintf(stderr, "r37 check: %lld curves, %lld differ\n", chkN, chkBad);
  if (bv <= -1e299) return {};
  *outVal = bv; return asgOfW(best);
}
}  // namespace r37
}  // namespace r29s


// ---- teamperm: re-pairing of whole teams with the open offices (post-step on an incumbent)
// With unique multi-skill workers the annealer moves one worker at a time: moving a worker strips the
// skills of its zone, so exchanging whole teams between zones (#6-like H12 copy: the 3 right offices with
// the teams at the wrong offices, 1.90x single, against 2.29x with the right pairing) is out of its reach.
// Here: the open offices of the incumbent and its teams; power cells (weights from 0); every permutation
// of the teams over the offices (k <= 6) screened by a cheap proxy (common count c, no load term), the best
// ones built exactly (levelSearch: common count / window and common level), then single-worker moves /
// swaps / free workers and a coordinate search on the cell weights; the result is checked by evalFull and
// offered only when better. Deterministic (no RNG), every loop watches the clock.
namespace r29s {
namespace tp {
static const bool dbg = false;
vector<int> open; int k = 0;
vector<double> wt; vector<vector<int>> cell;
vector<vector<int>> team;  // team i works in zone i (after the permutation stage)
vector<int> freeW;
double DL = 0;  // deadline on r29s::el()
inline bool late() { return el() > DL; }
LevelRes exact(const vector<vector<int>>& tm, const vector<vector<int>>& cl) {
  vector<vector<int>> elig(k);
  for (int i = 0; i < k; i++) { Mask m = teamMask(tm[i]); for (int s : cl[i]) if ((sm[s] & ~m).none()) elig[i].push_back(s); }
  return levelSearch(open, elig);
}
// proxy for one (zone, team mask): prefix sums of the positive profits of the coverable cell sites
void prefixOf(int i, const Mask& m, const vector<int>& cl, vector<double>& pre) {
  int o = open[i]; vector<double> p;
  for (int s : cl) if ((sm[s] & ~m).none()) { double v = prof(o, s); if (v > 0) p.push_back(v); }
  sort(p.rbegin(), p.rend()); if ((int)p.size() > ms[o]) p.resize(ms[o]);
  pre.assign(p.size() + 1, 0); for (size_t j = 0; j < p.size(); j++) pre[j + 1] = pre[j] + p[j];
}
// best common count over the zones (equal counts; with a window A the smallest zone sets c, others up to c + A)
double proxyOf(const vector<const vector<double>*>& P) {
  int cm = INT_MAX; for (auto* p : P) cm = min(cm, (int)p->size() - 1);
  double best = -1e300, cs = 0; for (int i = 0; i < k; i++) cs += cost[open[i]];
  for (int c = 1; c <= cm; c++) { double v = -cs; for (auto* p : P) v += (*p)[min((int)p->size() - 1, c + A)]; best = max(best, v); }
  return best;
}
bool run(double seconds, const vector<int>& openIn, const vector<vector<int>>& teamIn, const vector<int>& freeIn,
         double inc, double* outVal, Sol& out) {
  T0 = chrono::steady_clock::now(); TL = seconds; DL = 0.92 * seconds;
  struct TpFlag { TpFlag() { lsTp = true; } ~TpFlag() { lsTp = false; } } tpFlag;
  open = openIn; k = open.size(); team = teamIn; freeW = freeIn;
  if (k < 2 || k > 6) return false;
  wt.assign(k, 0);
  if (!ownCell(open, wt)) return false;
  cellsOf(open, wt, cell);
  // 1) permutations of the teams, proxy screen
  vector<vector<vector<double>>> pre(k, vector<vector<double>>(k));
  for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) prefixOf(i, teamMask(team[j]), cell[i], pre[i][j]);
  vector<int> perm(k); iota(perm.begin(), perm.end(), 0);
  vector<pair<double, vector<int>>> scr;
  do {
    vector<const vector<double>*> P(k); for (int i = 0; i < k; i++) P[i] = &pre[i][perm[i]];
    scr.push_back({proxyOf(P), perm});
  } while (next_permutation(perm.begin(), perm.end()) && !late());
  stable_sort(scr.begin(), scr.end(), [](const pair<double, vector<int>>& a, const pair<double, vector<int>>& b) { return a.first > b.first; });
  // exact on the best few (the identity always among them)
  vector<int> idp(k); iota(idp.begin(), idp.end(), 0);
  vector<vector<int>> cand; for (size_t q = 0; q < scr.size() && cand.size() < 6; q++) cand.push_back(scr[q].second);
  if (find(cand.begin(), cand.end(), idp) == cand.end()) cand.push_back(idp);
  double bv = -1e300; vector<vector<int>> bt; LevelRes blr;
  for (auto& pm : cand) {
    if (late()) break;
    vector<vector<int>> tm(k); for (int i = 0; i < k; i++) tm[i] = team[pm[i]];
    LevelRes lr = exact(tm, cell);
    if (dbg) fprintf(stderr, "tp perm"); if (dbg) { for (int x : pm) fprintf(stderr, " %d", x); fprintf(stderr, ": exact %.4f\n", lr.val); }
    if (lr.val > bv + 1e-9 * max(1.0, fabs(bv))) bv = lr.val, bt = tm, blr = lr;
  }
  if (bv <= -1e299) return false;
  team = bt;
  // 2) single workers: move between teams, swap across teams, bring a free worker in (proxy-ranked, exact-checked)
  auto zonePre = [&](int i, const vector<int>& tm, vector<double>& p) { prefixOf(i, teamMask(tm), cell[i], p); };
  for (int round = 0; round < 50 && !late(); round++) {
    vector<vector<double>> cp(k); for (int i = 0; i < k; i++) zonePre(i, team[i], cp[i]);
    struct Mv { double px; int kind, a, ia, b, ib; };  // kind 0 move team[a][ia] -> b, 1 swap with team[b][ib], 2 free[ia] -> b
    vector<Mv> mv;
    // at most 2000 candidates per round; every enumeration loop watches the clock (big native teams at large n)
    auto more = [&]() { return !late() && mv.size() < 2000; };
    auto proxyWith = [&](int a, const vector<int>& ta, int b, const vector<int>& tb) {
      vector<double> pa, pb; if (a >= 0) zonePre(a, ta, pa); zonePre(b, tb, pb);
      vector<const vector<double>*> P(k); for (int i = 0; i < k; i++) P[i] = i == a ? &pa : i == b ? &pb : &cp[i];
      return proxyOf(P);
    };
    for (int a = 0; a < k && more(); a++) for (int ia = 0; ia < (int)team[a].size() && more(); ia++) for (int b = 0; b < k && more(); b++) {
      if (b == a) continue;
      vector<int> ta = team[a], tb = team[b]; int w = ta[ia]; ta.erase(ta.begin() + ia); tb.push_back(w);
      mv.push_back({proxyWith(a, ta, b, tb), 0, a, ia, b, -1});
      if (b > a) for (int ib = 0; ib < (int)team[b].size() && more(); ib++) {
        vector<int> sa = team[a], sb = team[b]; swap(sa[ia], sb[ib]);
        mv.push_back({proxyWith(a, sa, b, sb), 1, a, ia, b, ib});
      }
    }
    for (int f = 0; f < (int)freeW.size() && more(); f++) for (int b = 0; b < k && more(); b++) {
      vector<int> tb = team[b]; tb.push_back(freeW[f]); mv.push_back({proxyWith(-1, {}, b, tb), 2, -1, f, b, -1});
    }
    stable_sort(mv.begin(), mv.end(), [](const Mv& x, const Mv& y) { return x.px > y.px; });
    bool imp = false;
    for (size_t q = 0; q < mv.size() && q < 4 && !late(); q++) {
      const Mv& m = mv[q]; vector<vector<int>> tm = team; vector<int> fw = freeW;
      if (m.kind == 0) { int w = tm[m.a][m.ia]; tm[m.a].erase(tm[m.a].begin() + m.ia); tm[m.b].push_back(w); }
      else if (m.kind == 1) swap(tm[m.a][m.ia], tm[m.b][m.ib]);
      else { tm[m.b].push_back(fw[m.ia]); fw.erase(fw.begin() + m.ia); }
      LevelRes lr = exact(tm, cell);
      if (lr.val > bv + 1e-9 * max(1.0, fabs(bv))) { bv = lr.val; team = tm; freeW = fw; blr = lr; imp = true; if (dbg) fprintf(stderr, "tp worker move kind %d: %.4f\n", m.kind, bv); break; }
    }
    if (!imp) break;
  }
  // 3) cell weights: coordinate search (exact), cells stay convex with every office inside its own cell
  vector<vector<int>> bcell = cell; vector<double> bw = wt;
  for (double step = 0.02 * SPAN * SPAN; step > 1e-4 * SPAN * SPAN && !late(); step *= 0.5) {
    bool any = true;
    for (int pass = 0; pass < 3 && any && !late(); pass++) {
      any = false;
      for (int i = 0; i < k && !late(); i++) for (int sg = -1; sg <= 1 && !late(); sg += 2) {
        vector<double> w2 = bw; w2[i] += sg * step;
        if (!ownCell(open, w2)) continue;
        vector<vector<int>> c2; cellsOf(open, w2, c2);
        LevelRes lr = exact(team, c2);
        if (lr.val > bv + 1e-9 * max(1.0, fabs(bv))) { bv = lr.val; bw = w2; bcell = c2; blr = lr; any = true; }
      }
    }
  }
  if (dbg) fprintf(stderr, "tp: level value %.4f (inc %.4f, %.3fs)\n", bv, inc, el());
  if (bv <= inc + 1e-9 * max(1.0, fabs(inc)) || blr.mem.empty()) return false;
  // 4) exact check (hulls on the cell borders: removal repair + level again)
  Sol s; s.mem.assign(K, {}); s.wk.assign(K, {}); s.tag = "tp";
  for (int i = 0; i < k; i++) { int o = open[i]; s.mem[o] = blr.mem[o]; if (!s.mem[o].empty()) s.wk[o] = team[i]; }
  TL = max(TL, el() + 0.1 * seconds);
  string why; double v = evalFull(s, &why);
  if (v <= -1e299) {
    repairHull(s.mem);
    vector<int> op; vector<vector<int>> el2, tm2;
    for (int o = 0; o < K; o++) if (!s.mem[o].empty()) op.push_back(o), el2.push_back(s.mem[o]), tm2.push_back(s.wk[o]);
    LevelRes lr = levelSearch(op, el2); Sol t; t.mem.assign(K, {}); t.wk.assign(K, {}); t.tag = "tp";
    if (!lr.mem.empty()) for (size_t i = 0; i < op.size(); i++) { t.mem[op[i]] = lr.mem[op[i]]; if (!t.mem[op[i]].empty()) t.wk[op[i]] = tm2[i]; }
    s = t; v = evalFull(s, &why);
  }
  if (dbg) fprintf(stderr, "tp: final %.4f %s (%.3fs)\n", v, why.c_str(), el());
  if (v <= inc + 1e-9 * max(1.0, fabs(inc))) return false;
  s.val = v; out = s; *outVal = v; return true;
}
}  // namespace tp
}  // namespace r29s

// teamperm driver: open offices and teams of an assignment (native: asg[n + w]; else the counting assignment
// of writeSolution), then r29s::tp::run; returns the new assignment (empty when no gain)
vector<int> teamPermStep(const vector<int>& asg, double inc, double seconds, double* outVal) {
  if ((int)asg.size() < n) return {};
  State st = fromAsg(asg);
  vector<int> open; for (int o = 0; o < K; o++) if (st.cnt[o] > 0) open.push_back(o);
  if (open.size() < 2 || open.size() > 6) return {};
  vector<vector<int>> wk(K);
  if (nativeW) { for (int o = 0; o < K; o++) wk[o] = st.owk[o]; }
  else {
    vector<Mask> masks; vector<int> om;
    for (int o : open) { Mask m; for (int s : st.mem[o]) m |= smask[s]; if (m.any()) masks.push_back(m), om.push_back(o); }
    if (!assignWorkers(masks, true)) return {};
    for (int w = 0; w < W; w++) if (assignWorkersResult[w] >= 0) wk[om[assignWorkersResult[w]]].push_back(w);
  }
  vector<vector<int>> team; vector<char> used(W, 0);
  for (int o : open) { team.push_back(wk[o]); for (int w : wk[o]) used[w] = 1; }
  vector<int> fr; for (int w = 0; w < W; w++) if (!used[w]) fr.push_back(w);
  r29s::Sol s; double v = -1e300;
  if (!r29s::tp::run(seconds, open, team, fr, inc, &v, s)) return {};
  *outVal = v;
  return r29s::asgOfW(s);
}

int main(int argc, char** argv) {
    T0 = chrono::steady_clock::now();
    T0w = chrono::system_clock::now();
    signal(SIGPIPE, SIG_IGN);  // a dead MIP driver must not kill the solver
    double timeLimit = argc > 1 ? atof(argv[1]) : 250.0;
    hardDeadline = timeLimit + 5;
    lsCutoff = 0.6 * timeLimit;
    searchEnd = timeLimit;
    if (argc > 2) rng.seed(strtoull(argv[2], nullptr, 10));
    const char* inPath = "instance.json";
    const char* outPath = "solution.json";

    string text;
    if (FILE* f = fopen(inPath, "rb")) {  // the whole file in one read (the stream copy went char by char)
        char buf[1 << 16];
        size_t got;
        while ((got = fread(buf, 1, sizeof buf, f)) > 0) text.append(buf, got);
        fclose(f);
    }
    Parser ps{text.c_str()};
    J d = ps.parse();
    const J& sites = d["sites"];
    const J& offices = d["offices"];
    const J& workers = d["workers"];
    n = sites.size();
    K = offices.size();
    W = workers.size();
    NP = n + K;
    A = (int)min(max(d["maxDifference"].num, -1.0), (double)n + 1);
    alpha = d["balanceCoefficient"].num;
    px.resize(NP);
    py.resize(NP);
    rew.resize(n);
    ntask.resize(n);
    smask.assign(n, Mask());
    NS = 0;
    map<long long, int> skillIds;  // raw skill id -> compact id
    bool skillOverflow = false;
    {   // more than MAXSK distinct task skills: the MAXSK - 1 most frequent get ids, the rest share the
        // reserved id MAXSK - 1, which no worker gets (those sites stay unserved; the rest is solved)
        map<long long, long long> freq;
        for (int i = 0; i < n; i++) {
            const J& t = sites[i]["tasks"];
            for (size_t k = 0; k < t.size(); k++) freq[(long long)t.at(k)]++;
        }
        if ((int)freq.size() > MAXSK) {
            vector<pair<long long, long long>> v;
            for (auto& kv : freq) v.push_back({-kv.second, kv.first});
            sort(v.begin(), v.end());
            for (int k = 0; k < MAXSK - 1; k++) skillIds[v[k].second] = k;
            skillOverflow = true;
            NS = MAXSK;  // ids 0..MAXSK-2 plus the reserved one
        }
    }
    auto skillId = [&](double raw) {
        auto it = skillIds.find((long long)raw);
        if (it != skillIds.end()) return it->second;
        if (skillOverflow) return MAXSK - 1;  // a rare skill: reserved id, not in skillIds -> no worker holds it
        int id = (int)skillIds.size();
        skillIds[(long long)raw] = id;
        NS = max(NS, id + 1);
        return id;
    };
    for (int i = 0; i < n; i++) {
        px[i] = sites[i]["x"].num;
        py[i] = sites[i]["y"].num;
        rew[i] = sites[i]["reward"].num;
        const J& t = sites[i]["tasks"];
        ntask[i] = t.size();
        for (size_t k = 0; k < t.size(); k++) {
            smask[i].set(skillId(t.at(k)));
        }
    }
    ocost.resize(K);
    maxSize.resize(K);
    for (int o = 0; o < K; o++) {
        px[n + o] = offices[o]["x"].num;
        py[n + o] = offices[o]["y"].num;
        ocost[o] = offices[o]["cost"].num;
        maxSize[o] = (int)min(max(offices[o]["maxSize"].num, 0.0), (double)n);
    }
    wmask.assign(W, Mask());
    for (int w = 0; w < W; w++) {
        for (size_t k = 0; k < workers[w].size(); k++) {
            auto it = skillIds.find((long long)workers[w].at(k));
            if (it != skillIds.end()) wmask[w].set(it->second);  // skills no task needs are irrelevant
        }
        if (wmask[w].count() > 1) singleSkillWorkers = false, origSingleSkill = false;
    }
    // Multi-skill workers: give every worker one "primary" skill and solve the single-skill
    // problem (fast exact worker check, fan and power-diagram starts all apply). Any answer is
    // valid for the real workers, whose skill sets contain their primary skill.
    if (!singleSkillWorkers && NS > 0) {
        vector<int> ms;
        for (int o = 0; o < K; o++) ms.push_back(maxSize[o]);
        sort(ms.begin(), ms.end());
        double m = K ? max(1, min(ms[K / 2], max(1, n / max(1, K / 2)))) : 1;
        vector<double> f(NS, 0), dem(NS, 0);
        for (int i = 0; i < n; i++)
            for (int k = 0; k < NS; k++)
                if (smask[i][k]) f[k] += 1.0 / max(1, n);
        for (int k = 0; k < NS; k++) dem[k] = 1 - pow(1 - f[k], m) + 1e-9;
        vector<int> cnt(NS, 0), prim(W, -1), ord(W);
        for (int w = 0; w < W; w++) ord[w] = w;
        stable_sort(ord.begin(), ord.end(), [&](int a, int b) { return wmask[a].count() < wmask[b].count(); });
        for (int w : ord) {
            int bk = -1;
            double bv = -1;
            for (int k = 0; k < NS; k++)
                if (wmask[w][k] && dem[k] / (cnt[k] + 1) > bv) bv = dem[k] / (cnt[k] + 1), bk = k;
            if (bk >= 0) prim[w] = bk, cnt[bk]++;
        }
        // local improvement: move a worker to another of its skills while the scarcest skill gains
        for (int pass = 0; pass < 20; pass++) {
            bool imp = false;
            for (int w = 0; w < W; w++) {
                int a = prim[w];
                if (a < 0) continue;
                for (int k = 0; k < NS; k++) {
                    if (k == a || !wmask[w][k]) continue;
                    // ratio of the two skills involved, before and after
                    double before = min(cnt[a] / dem[a], cnt[k] / dem[k]);
                    double after = min((cnt[a] - 1) / dem[a], (cnt[k] + 1) / dem[k]);
                    if (after > before + 1e-12) {
                        cnt[a]--, cnt[k]++, prim[w] = k, a = k, imp = true;
                    }
                }
            }
            if (!imp) break;
        }
        realW = wmask;
        // native covers only pay when workers are scarce: every office could otherwise get one
        // primary-skill worker per needed skill anyway
        int minCnt = INT32_MAX;
        for (int k = 0; k < NS; k++)
            if (f[k] > 0) minCnt = min(minCnt, cnt[k]);
        nativeW = minCnt < K;
        if (nativeW) {
            skW.assign(NS, {});
            for (int w = 0; w < W; w++)
                for (int k = 0; k < NS; k++)
                    if (realW[w][k]) skW[k].push_back(w), anyW.set(k);
        }
        for (int w = 0; w < W; w++) {
            wmask[w].reset();
            if (prim[w] >= 0) wmask[w].set(prim[w]);
        }
        singleSkillWorkers = true;
    }
    AS = n + (nativeW ? W : 0);
    availSkill.assign(NS, 0);
    for (int w = 0; w < W; w++)
        for (int s = 0; s < NS; s++)
            if (wmask[w][s]) availSkill[s]++;
    dist.assign(K, vector<double>(n));
    {
        const J& dj = d["distances"];
        for (int o = 0; o < K; o++)
            for (int s = 0; s < n; s++) dist[o][s] = dj[o].at(s);
    }
    if ((double)n * K <= 1e7) {
        distT.resize((size_t)n * K);
        for (int o = 0; o < K; o++)
            for (int s = 0; s < n; s++) distT[(size_t)s * K + o] = dist[o][s];
    }
    d = J();
    string().swap(text);
    double span = 0;
    for (int i = 0; i < NP; i++) span = max(span, max(fabs(px[i]), fabs(py[i])));
    EPS = max(1e-9, span * 1e-9);
    buildGrid();
    buildRanks();
    buildSiteKeyOrder();
    buildSkillLists();
    // MIP stage over the zone pool: the search phases end early and leave it a time reserve
    {
        // exact task balance when the count window is tight against the zone sizes
        vector<int> ms;
        for (int o = 0; o < K; o++)
            if (maxSize[o] > 0) ms.push_back(maxSize[o]);
        sort(ms.begin(), ms.end());
        int medCap = ms.empty() ? 0 : ms[ms.size() / 2];
        // only for sites with 1-2 (or 0) tasks and enough capacity to serve (almost) every site:
        // there the zones are cut by the common task level, not by maxSize
        double capSum = 0;
        int tmx = 0;
        for (int o = 0; o < K; o++) capSum += min(maxSize[o], n);
        for (int s = 0; s < n; s++) tmx = max(tmx, ntask[s]);
        bool fam = alpha > 0 && K >= 2 && tmx <= 2 && capSum >= 0.9 * n;
        int zoneLim = min(medCap, max(1, n / max(1, K / 2)));
        // a wide window is never a reason to switch the exact-level machinery off: any plan with a
        // narrow window is feasible there too (wide A without it lost 3-7 % on the s1 family);
        // exactPolish only for really wide windows (at zoneLim / 4 <= A < zoneLim / 2 it cost ~1 %)
        epOn = fam && (4 * A < zoneLim || (wideGate && 2 * A >= zoneLim));
        // line cells only with a count window narrow against the zone size (wide window: they rarely help)
        lineGate = lineOn && fam && singleSkillWorkers && (wideGate || 2 * A < zoneLim);
    }
    const bool useMip = mipAvailable();
    poolOn = useMip;
    const double fullLimit = timeLimit;
    // single-skill workers, few skills: the search ends early and the skill-subset zone MIP rounds
    // (recipeImprove) get most of the time, after a short run of the pool MIP
    const bool gate = useMip && recipeGate();
    if (useMip) {
        double R = min(30.0, max(3.0, 0.12 * fullLimit));
        timeLimit = max(0.5 * fullLimit, fullLimit - R);
        if (gate) timeLimit = fullLimit * 0.36;
        hardDeadline = timeLimit + 5;
        searchEnd = timeLimit;
    }
    if (szDebug) fprintf(stderr, "recipe gate=%d (origSingle=%d NS=%d) search limit %.1fs\n", (int)gate, (int)origSingleSkill, NS, timeLimit);
    auto mipStage = [&](double dl) -> vector<int> {
        if (!gate) return mipImprove(dl, bestAsg, bestObj);
        double oldShare = min(25.0, 0.1 * fullLimit);
        vector<int> r = oldShare > 0.5 ? mipImprove(min(dl, elapsed() + oldShare), bestAsg, bestObj) : vector<int>();
        vector<int> inc = r.empty() ? bestAsg : r;
        double incObj = r.empty() ? bestObj : trueObjective(fromAsg(r));
        vector<int> r2 = recipeImprove(dl, inc, incObj);
        return r2.empty() ? r : r2;
    };

    // empty solution is always valid
    initState(S);
    bestAsg = S.asg;
    bestObj = trueObjective(S);
    validAsg = S.asg;
    validObj = bestObj;
    writeSolution(S, outPath);
    if (n == 0 || K == 0) return 0;

    // temperature scale from per-site values
    vector<double> vals;
    for (int s = 0; s < n; s++) {
        double bv = -1e300;
        for (int o = 0; o < K; o++) bv = max(bv, rew[s] - dist[o][s]);
        vals.push_back(fabs(bv));
    }
    sort(vals.begin(), vals.end());
    double scale = max(1e-9, vals[vals.size() / 2]);
    double Tstart = scale * 2.0;
    double Tend = scale * 1e-4;
    double lamStart = scale * 0.1, lamEnd = scale * 100.0 + alpha * 10;

    nearOrder.assign(K, {});
    for (int o = 0; o < K; o++) {
        for (int s = 0; s < n; s++) nearOrder[o].push_back(s);
        sort(nearOrder[o].begin(), nearOrder[o].end(), [&](int a, int b) { return dist[o][a] < dist[o][b]; });
    }
    const int L = min(K, 8);
    nearOff.assign(n, {});
    for (int s = 0; s < n; s++) {
        vector<int> ord(K);
        for (int o = 0; o < K; o++) ord[o] = o;
        partial_sort(ord.begin(), ord.begin() + L, ord.end(), [&](int a, int b) { return dist[a][s] < dist[b][s]; });
        nearOff[s].assign(ord.begin(), ord.begin() + L);
    }
    // fan construction: tried when most offices stand outside the sites' bounding box
    vector<int> fanAsg;
    double fanVal = -1e300;
    FanGeo fanGeo{0, 0, 0};
    // best fan of the other kind (strips vs. apex fans): SA from it can end higher (second arm)
    vector<int> fanAsgB;
    double fanValB = -1e300;
    FanGeo fanGeoB{0, 0, 0};
    {
        double x0 = 1e300, x1 = -1e300, y0 = 1e300, y1 = -1e300, sx = 0, sy = 0, cx = 0, cy = 0;
        for (int s = 0; s < n; s++) x0 = min(x0, px[s]), x1 = max(x1, px[s]), y0 = min(y0, py[s]), y1 = max(y1, py[s]), sx += px[s], sy += py[s];
        int outside = 0;
        for (int o = 0; o < K; o++) {
            double x = px[n + o], y = py[n + o];
            if (x < x0 || x > x1 || y < y0 || y > y1) outside++;
            cx += px[n + o], cy += py[n + o];
        }
        sx /= n, sy /= n, cx /= K, cy /= K;
        // r35: remote-source distance rows (an office's row measures from a point far from the office,
        // like instance3's opposite office) make zones cones from the office to its far source region;
        // power cells around the office cannot express them, the fan/strip DP can. Measured by the
        // median over offices of |office - its nearest site in its own row| relative to the span:
        // ~1 on such rings (also with offices standing on sites), <= 0.11 on the other open instances
        double remoteMed = 0;
        {
            double span = max(max(x1 - x0, y1 - y0), 1e-300);
            vector<double> rem;
            for (int o = 0; o < K; o++) {
                int j = 0;
                for (int s = 1; s < n; s++)
                    if (dist[o][s] < dist[o][j]) j = s;
                rem.push_back(hypot(px[j] - px[n + o], py[j] - py[n + o]) / span);
            }
            nth_element(rem.begin(), rem.begin() + K / 2, rem.end());
            remoteMed = rem[K / 2];
        }
        static const double remoteF = 0.4;
        // (not where the regime phase below would run - task-free sites or a tight window: a fan there
        // switches it off, and on that family it is worth more: g0024 -12 %, g0030 -3.5 % with fans)
        bool rgLike = false;
        {
            int zs = 0;
            for (int i = 0; i < n; i++) zs += ntask[i] == 0;
            static const int rgMaxN0 = 1200;
            rgLike = alpha > 0 && alpha >= 0.05 * scale && n <= rgMaxN0 && (zs >= 0.1 * n || A < max(2.0, 0.02 * n));
        }
        bool remoteFan = remoteF > 0 && remoteMed >= remoteF && !rgLike;
        bool tryFan = (2 * outside >= K || remoteFan) && singleSkillWorkers;
        if (szDebug) fprintf(stderr, "fan: outside %d/%d remote %.3f try=%d\n", outside, K, remoteMed, (int)tryFan);
        if (tryFan) {
            double fanFrac = 0.1;
            double fanEnd = elapsed() + fanFrac * max(0.0, timeLimit - elapsed()), rate = 5e7;
            double fanSoft = elapsed() + 0.5 * (fanEnd - elapsed());  // coarse/local search share
            int G1 = 200;
            int G2 = 800;
            int wLo = 0, wHi = n;  // count window of the best fan so far
            vector<int> fanCounts;
            bool stripNow = false, fanIsStrip = false;
            double kindVal[2] = {-1e300, -1e300};
            vector<int> kindAsg[2];
            FanGeo kindGeo[2] = {{0, 0, 0}, {0, 0, 0}};
            auto run = [&](const FanGeo& fg, int G, double until, int cLo, int cHi) {
                double t0 = elapsed(), ops, v;
                if (t0 >= until) return -1e300;
                vector<int> asg = fanInit(fg, G, (until - t0) * rate, &ops, &v, cLo, cHi);
                bool ran = ops <= (until - t0) * rate;
                if (!ran && G > 16 && ops > 0) {  // too expensive: retry with proportionally fewer cuts
                    int Gs = max(16, (int)(G * (until - t0) * rate / ops * 0.7));
                    if (Gs < G) {
                        G = Gs;
                        asg = fanInit(fg, G, (until - t0) * rate, &ops, &v, cLo, cHi);
                        ran = ops <= (until - t0) * rate;
                    }
                }
                double dt = elapsed() - t0;
                if (ran && dt > 0.02) rate = max(1e6, ops / dt);
                if (szDebug) fprintf(stderr, "fan geo P=(%.3f,%.3f) G=%d ops=%.3g t=%.2fs val=%.6g%s\n", fg.px, fg.py, G, ops, dt, v, ran ? "" : " (skipped)");
                if (v > fanVal) fanVal = v, fanAsg = asg, fanGeo = fg, wLo = cLo, wHi = cHi, fanCounts = fanLastCounts, fanIsStrip = stripNow;
                if (v > kindVal[stripNow]) kindVal[stripNow] = v, kindAsg[stripNow] = asg, kindGeo[stripNow] = fg;
                return v;
            };
            // parallel strips (apex far away, direction th): offices all around the sites (a ring)
            // give near-parallel blades, each holding an office from either end of its strip
            // (only when the offices surround the sites: every angular gap around the site centroid < pi)
            int stripDirs = 12;
            {
                vector<double> a0;
                for (int o = 0; o < K; o++)
                    if (hypot(px[n + o] - sx, py[n + o] - sy) > EPS * 1e3) a0.push_back(atan2(py[n + o] - sy, px[n + o] - sx));
                sort(a0.begin(), a0.end());
                double gap = a0.empty() ? 2 * M_PI : a0[0] + 2 * M_PI - a0.back();
                for (size_t i = 1; i < a0.size(); i++) gap = max(gap, a0[i] - a0[i - 1]);
                if (gap >= M_PI) stripDirs = 0;
                if (szDebug) fprintf(stderr, "fan: widest office gap %.3f strips=%d\n", gap, stripDirs);
            }
            // the strips get their own time slice (half the fan share) so the apex search keeps its budget
            double stripEnd = elapsed() + (stripDirs > 0 ? 0.5 * fanFrac * max(0.0, timeLimit - elapsed()) : 0.0);
            double sbv = -1e300, sbt = 0, sspan = max(x1 - x0, y1 - y0) * 50 + 1;
            auto stripGeo = [&](double th) { return FanGeo{sx - sspan * cos(th), sy - sspan * sin(th), th}; };
            stripNow = true;
            for (int i = 0; i < stripDirs; i++) {
                double th = M_PI * i / stripDirs, v = run(stripGeo(th), G1, stripEnd, 0, n);
                if (v > sbv) sbv = v, sbt = th;
            }
            if (stripDirs > 0 && sbv >= fanVal && sbv > -1e299) {
                double st = M_PI / stripDirs / 2;
                for (int it = 0; it < 8; it++, st *= 0.5)
                    for (int d = -1; d <= 1; d += 2) {
                        double v = run(stripGeo(sbt + d * st), G1, stripEnd, 0, n);
                        if (v > sbv) sbv = v, sbt += d * st;
                    }
            }
            stripNow = false;
            fanEnd = elapsed() + fanFrac * max(0.0, timeLimit - elapsed());
            fanSoft = elapsed() + 0.5 * (fanEnd - elapsed());
            double D = hypot(sx - cx, sy - cy);
            // apex behind the office cluster: P = c - lam * D * u(theta), u = direction to the sites
            auto geoOf = [&](double lam, double th) {
                double ux = (sx - cx) / D, uy = (sy - cy) / D;
                double rx = ux * cos(th) - uy * sin(th), ry = ux * sin(th) + uy * cos(th);
                return FanGeo{cx - lam * D * rx, cy - lam * D * ry, atan2(ry, rx)};
            };
            bool line = D > EPS * 1e3;
            double bl = 0, bt = 0, bv = -1e300;
            if (line)
                for (double lam : {0.5, 1.0, 0.25, 2.0, 4.0, 8.0}) {
                    double v = run(geoOf(lam, 0), G1, fanSoft, 0, n);
                    if (v > bv) bv = v, bl = lam;
                }
            // sectors around the office centroid / the site centroid; the seam goes through the widest office gap
            for (int cen = 0; cen < 2; cen++) {
                double qx = cen ? sx : cx, qy = cen ? sy : cy;
                vector<double> a0;
                for (int o = 0; o < K; o++)
                    if (hypot(px[n + o] - qx, py[n + o] - qy) > EPS * 1e3) a0.push_back(atan2(py[n + o] - qy, px[n + o] - qx));
                sort(a0.begin(), a0.end());
                if (a0.empty()) continue;
                double bg = -1, base = 0;
                for (size_t i = 0; i < a0.size(); i++) {
                    double g = (i + 1 < a0.size() ? a0[i + 1] : a0[0] + 2 * M_PI) - a0[i];
                    if (g > bg) bg = g, base = a0[i] + g / 2 + M_PI;
                }
                run(FanGeo{qx, qy, base}, G1, fanSoft, 0, n);
            }
            // local search over (lam, tilt) around the best apex, then a fine final pass
            bool lineBest = line && bv >= fanVal;
            if (lineBest) {
                double sl = 0.2, st = 0.02;
                bool out = false;
                for (int it = 0; it < 10 && !out; it++) {
                    bool imp = false;
                    for (int d = 0; d < 4 && !out; d++) {
                        double l = d == 0 ? bl * exp(sl) : d == 1 ? bl * exp(-sl) : bl, t = d == 2 ? bt + st : d == 3 ? bt - st : bt;
                        double v = run(geoOf(l, t), G1, fanSoft, 0, n);
                        if (v < -1e299) out = true;  // out of budget (or unusable apex)
                        if (v > bv) bv = v, bl = l, bt = t, imp = true;
                    }
                    if (!imp) sl *= 0.5, st *= 0.5;
                }
            }
            FanGeo fin = fanGeo;
            stripNow = fanIsStrip;
            if (A < n && fanVal > -1e299) {  // tight count balance: wedges with a common count window
                vector<int> cs = fanCounts;  // zone sizes of the best fan before the count window
                sort(cs.begin(), cs.end());
                vector<int> los;
                for (double q : {0.5, 0.3, 0.7, 0.15, 0.85, 0.4, 0.6, 0.05, 0.95}) {
                    int lo = cs.empty() ? 0 : max(1, cs[min(cs.size() - 1, (size_t)(q * cs.size()))] - A / 2);
                    if (find(los.begin(), los.end(), lo) == los.end()) los.push_back(lo);
                }
                for (int lo : los) run(fin, G1, fanEnd, lo, lo + A);
            }
            int fLo = wLo, fHi = wHi;
            for (int G = G2; G > G1 && fanVal > -1e299; G /= 2) {
                double v = run(fin, G, fanEnd, fLo, fHi);
                if (fLo != 0 || fHi != n) v = max(v, run(fin, G, fanEnd, 0, n));
                if (v > -1e299) break;
            }
            int ok = !fanIsStrip;  // the other kind
            if (kindVal[ok] > -1e299 && kindVal[ok] >= 0.5 * fanVal) fanValB = kindVal[ok], fanAsgB = kindAsg[ok], fanGeoB = kindGeo[ok];
            if (szDebug) fprintf(stderr, "fan best %.4f (%s), second arm %.4f\n", fanVal, fanIsStrip ? "strips" : "apex", fanValB);
        }
        if (fanVal > -1e299) {
            considerBest(fromAsg(fanAsg), true);
            refreshValid();
            writeSolution(fromAsg(validAsg), outPath);
        }
    }
    // triangulation fans: offices in convex position (instance3-like opposite-side costs)
    vector<int> triAsg;
    double triVal = -1e300, triPlain = -1e300;  // triPlain: the triangulation before the chord plans
    vector<int> triPlainAsg;
    {
        bool tryTri = true;
        if (tryTri) {
            double triFrac = 0.06;
            double t0 = elapsed();
            double triExt = 0.25;
            static const double triCap = 0.3;
            static const double triExtCap = 0.4;
            double R = max(0.0, timeLimit - t0);
            triAsg = triSearch(t0 + triFrac * R, t0 + triExt * R, t0 + triCap * R, t0 + max(triCap, triExtCap) * R, max(fanVal, bestObj), &triVal);
            if (szDebug) fprintf(stderr, "tri: val=%.6f t=%.2fs\n", triVal, elapsed() - t0);
            // free chord cuts on rings of a few dozen offices: DP over chord pairs and refinement of the
            // best plans here; the iterated local search runs after the fork in every process
            static const double chordFrac = 0.08;
            int mOpen = 0;
            for (int o = 0; o < K; o++) mOpen += maxSize[o] > 0;
            static const int chordN = 12000;  // r40: was 1500 (#1: rings of n ~ 8000)
            if (chordFrac > 0 && triVal > -1e299 && n <= chordN && mOpen >= 6 && mOpen <= 32 && alpha > 0) {
                triPlain = triVal;
                double cv;
                double ct0 = elapsed();
                double cE = ct0 + chordFrac * max(0.0, timeLimit - ct0);
                vector<int> ca = chordSearch(cE, cE, triVal, &cv);
                if (szDebug) fprintf(stderr, "chord: val=%.6f (tri %.6f) t=%.2fs\n", cv, triVal, elapsed() - ct0);
                if (cv > triVal) triPlainAsg = triAsg, triVal = cv, triAsg = ca;
            }
            if (triVal > -1e299) {
                considerBest(fromAsg(triAsg), true);
                refreshValid();
                writeSolution(fromAsg(validAsg), outPath);
            }
        }
    }
    // r25: the independent simple solver gets a short slice (single-skill workers, task balance on):
    // it often lands in the "many offices, low task level" basin that the SA below misses
    {
        static const double simpleFrac = 0.08;
        bool triWonBig = triVal > -1e299 && triVal > 2 * max(fanVal, 0.0);
        // K <= 300: the greedy open-set choice (chooseOpenRaw) is O(K^2 n) and would eat the slice
        if (simpleFrac > 0 && alpha > 0 && origSingleSkill && n > 0 && K > 3 && K <= 300 && !triWonBig && (long long)n * K <= 4000000LL) {
            double t0 = elapsed();
            vector<int> sa = simpleStart(simpleFrac * max(0.0, timeLimit - t0), rng());
            if ((int)sa.size() == n) {
                State st = fromAsg(sa);
                // only answers that pass the main solver's own checks may become the incumbent
                if (validateFull(st).empty() && countFeasible(st)) {
                    considerBest(st, true);
                    refreshValid();
                    writeSolution(fromAsg(validAsg), outPath);
                } else if (szDebug) fprintf(stderr, "simple phase: answer rejected by validateFull\n");
            }
            if (szDebug) fprintf(stderr, "simple phase %.2fs, best %.6f\n", elapsed() - t0, bestObj);
        }
    }
    // r28: equal-level bisection plans (see eqStart), gated to a tight count window under a heavy
    // task-balance penalty. The plan joins the search when exploration ends (before the level
    // ladder), if it beats what exploration found: the exploration path stays as before
    vector<int> eqAsg;
    double eqVal = -1e300;
    bool eqFromX = false;  // r33: the plan came from eqExact
    static const bool eqLate = true;
    {
        static const double eqFrac = 0.04;
        static const double eqA = 0.06;  // (A = 5 of ~53 per zone: mixed, -1.2 % / +1.4 %)
        int k0 = 0;
        if (haveBest || !bestAsg.empty()) k0 = openOfAsg(bestAsg).size();
        if (k0 < 2) k0 = 2;
        if (eqFrac > 0 && alpha >= scale && n >= 50 && K >= 3 && A <= eqA * n / k0 && (long long)n * K <= 4000000LL) {
            double t0 = elapsed(), v;
            // r33: exact-composition plans first; the proportional plans (eqStart) when they do not
            // apply (eqOld = 2), or always (eqOld = 1)
            static const int eqOld = 2;
            static const double eqxFrac = 0.15;
            vector<int> ea;
            v = -1e300;
            if (eqxFrac > 0) {
                double t1 = elapsed(), xv;
                vector<int> xa = eqExact(t1 + eqxFrac * max(0.0, timeLimit - t0), &xv);
                if (szDebug) fprintf(stderr, "eqx phase %.2fs, plan %.4f\n", elapsed() - t1, xv);
                if (!xa.empty() && xv > 0) eqAsg = xa, eqVal = xv, ea = xa, v = xv, eqFromX = true;
            }
            if (eqOld == 1 || (eqOld == 2 && ea.empty())) {
                double t1 = elapsed(), ov;
                // only what is left of the combined eq budget (eqExact's share) when eqExact ran
                double oEnd = t1 + eqFrac * max(0.0, timeLimit - t0);
                if (eqxFrac > 0) oEnd = min(oEnd, max(t1, t0 + eqxFrac * max(0.0, timeLimit - t0)));
                vector<int> oa = eqStart(oEnd, k0, &ov);
                if (szDebug) fprintf(stderr, "eq (proportional) %.2fs, plan %.4f\n", elapsed() - t1, ov);
                if (!oa.empty() && ov > eqVal) eqAsg = oa, eqVal = ov, ea = oa, v = ov, eqFromX = false;
            }
            if (!ea.empty() && !eqLate) {
                considerBest(fromAsg(ea), true);
                refreshValid();
                writeSolution(fromAsg(validAsg), outPath);
            }
            if (szDebug) fprintf(stderr, "eq phase %.2fs, plan %.4f, best %.6f\n", elapsed() - t0, v, bestObj);
        }
    }
    // r29: exact best single office (always) and the simple-structure portfolio (tight count window +
    // task-balance penalty: the annealer cannot change the number of offices when every zone must keep
    // the same size; the simple builds land in the "one more office at a common lower level" basin)
    if (n > 0 && K > 0 && (long long)n * K <= 4000000LL && K <= 300 && W <= 4000) {
        double t0 = elapsed();
        r29s::load();
        auto offer = [&](const vector<int>& a, const char* what) {
            if ((int)a.size() != n && (int)a.size() != AS) return;
            State st = fromAsg(a);
            if (validateFull(st).empty() && countFeasible(st)) {
                considerBest(st, true);
                refreshValid();
                writeSolution(fromAsg(validAsg), outPath);
            } else if (szDebug) fprintf(stderr, "r29 %s: rejected by validateFull\n", what);
        };
        // offered only when it beats the incumbent: otherwise the search path stays exactly as before
        if (r29s::single[r29s::bySingle[0]] > bestObj + 1e-9 * max(1.0, fabs(bestObj))) offer(r29s::singleAsg(), "single");
        static const double r29Frac = 0.05;
        static const string r29Modes = "a,d,n";
        double avgZone = (double)n / K;
        bool gate = alpha > 0 && A <= max(2.0, 0.1 * avgZone);
        if (gate && r29Frac > 0) {
            double R = max(0.0, timeLimit - t0);
            double secs = min(25.0, max(r29Frac * R, min(6.0, 0.1 * R)));
            double v = -1e300;
            vector<int> a = r29s::run(secs, rng(), r29Modes, &v);
            if (v > bestObj + 1e-9 * max(1.0, fabs(bestObj))) offer(a, "portfolio");
            if (szDebug) fprintf(stderr, "r29 phase %.2fs val %.6f best %.6f\n", elapsed() - t0, v, bestObj);
        }
        // r36: exact structure enumeration over the best <= 8 offices (before the fork: every process starts from it)
        static const double r36Frac = 0.06;
        int openNow = 0;
        { vector<char> u(K, 0); for (int s = 0; s < n; s++) if (bestAsg.size() >= (size_t)n && bestAsg[s] >= 0 && !u[bestAsg[s]]) u[bestAsg[s]] = 1, openNow++; }
        bool gate36 = alpha > 0 && A >= 0 && A <= max(2.0, 0.1 * avgZone) && (K <= 8 || (K <= 40 && openNow <= 5));
        // r38w: wide gate (more offices, a wider count window, more incumbent zones); cheaper budget and an
        // early exit when the screened structures stay far below the incumbent
        static const int r36Wide = 1;
        static const int r36WOpen = 10;
        // few big zones can win: the 6 best single offices hold >= 25 % of the sites some of the 8 best can
        // serve at a profit (#6 family 0.5; tight-A many-zone families ~0.1). Not "few workers": on a natural
        // K = 40, n = 27000, W = 7 input (cover 0.10) the r36 start (6 zones, 2191) kept SA from 2485
        double cover36 = 0;
        if (!gate36 && r36Wide) {
            int P8 = min(K, 8), P6 = min(K, 6); long long msSum = 0, prof8 = 0;
            for (int j = 0; j < P6; j++) msSum += maxSize[r29s::bySingle[j]];
            for (int s = 0; s < n; s++) for (int j = 0; j < P8; j++) if (r29s::prof(r29s::bySingle[j], s) > 0) { prof8++; break; }
            cover36 = prof8 > 0 ? (double)msSum / prof8 : 0;
        }
        bool wide36 = !gate36 && r36Wide && alpha > 0 && A >= 0 &&
                      A <= max(10.0, 0.15 * avgZone) && openNow <= r36WOpen && cover36 >= 0.25;
        if (szDebug) fprintf(stderr, "r36 gate: old %d wide %d (K %d A %d openNow %d avgZone %.1f cover %.3f)\n", (int)gate36, (int)wide36, K, A, openNow, avgZone, cover36);
        if ((gate36 || wide36) && r36Frac > 0 && K >= 2) {
            double t1 = elapsed(), R = max(0.0, timeLimit - t1);
            double secs = min(20.0, max(r36Frac * R, min(5.0, 0.1 * R)));
            // r38w: no halving for K > 8 any more (the phase stops after the screening when it cannot compete)
            double v = -1e300;
            r29s::r36::wide = wide36;
            vector<int> a;
            if (K > 5) {
                // r39: more offices than the pool screens with weight optimisation (#6-like: a few big offices among
                // many small ones). With a pool of 6-8 the screening of k = 4..6 runs without weight optimisation
                // (coarse 0) and misses the few-big-office structures; first the complete screening of the best 4
                // offices by single value (as for K = 4, f6t), then the usual pool of 8 (the old x0.5 cut for K > 8 dropped)
                static const int r39Cap = 4;
                static const double r39Share = 0.45;
                double v5 = -1e300;
                vector<int> a5;
                if (r39Cap >= 2 && r39Cap < 8) {
                    r29s::r36::poolCap = r39Cap;
                    a5 = r29s::r36::run(r39Share * secs, bestObj, &v5);
                    if (szDebug) fprintf(stderr, "r39 small pool %d: %.6f (%.2fs)\n", r39Cap, v5, elapsed() - t1);
                }
                r29s::r36::poolCap = 8;
                double rest = max(0.5, secs - (elapsed() - t1));
                a = r29s::r36::run(rest, max(bestObj, v5), &v);
                if (!a5.empty() && (a.empty() || v5 > v)) a = a5, v = v5;
            } else
                a = r29s::r36::run(secs, bestObj, &v);
            r29s::r36::wide = false;
            vector<vector<int>>().swap(r29s::r36::ordO); vector<signed char>().swap(r29s::r36::cellOf);
            if (!a.empty() && v > bestObj + 1e-9 * max(1.0, fabs(bestObj))) offer(a, "r36");
            if (szDebug) fprintf(stderr, "r36 phase %.2fs val %.6f best %.6f\n", elapsed() - t1, v, bestObj);
        }
        // r37: structure local search for the equal-load regime with a loose count window (before the fork)
        static const double r37Frac = 0.08;
        int maxMs = 0; for (int o = 0; o < K; o++) maxMs = max(maxMs, maxSize[o]);
        // (structures of up to 30 zones: the incumbent may have at most 24)
        static const int r37OpenMax = 24;
        // r45: also a middle count window (A >= 0.4 maxSize, e.g. instance1-style A ~ 0.45 n/K): the equal-load
        // zones rarely differ by more than A sites, and every plan is checked (validateFull + countFeasible).
        // The regime phase stays on there (r43 skips it only after r37 in the loose window A >= maxSize)
        static const double r45A = 0.4;
        bool loose37 = A >= maxMs;
        bool gate37 = alpha > 0 && alpha >= 1.0 * scale && (loose37 || (r45A > 0 && A >= r45A * maxMs)) && K >= 3 && openNow <= r37OpenMax;
        if (gate37 && r37Frac > 0) {
            if (loose37) r37Fired = true;
            double t1 = elapsed(), R = max(0.0, timeLimit - t1);
            double secs = min(25.0, max(r37Frac * R, min(6.0, 0.1 * R)));
            double v = -1e300;
            vector<int> a = r29s::r37::run(secs, bestAsg, bestObj, &v);
            if (!a.empty() && v > bestObj + 1e-9 * max(1.0, fabs(bestObj))) offer(a, "r37");
            if (szDebug) fprintf(stderr, "r37 phase %.2fs val %.6f best %.6f\n", elapsed() - t1, v, bestObj);
        }
        // teamperm: the open offices of the incumbent with every pairing of its teams, single-worker moves and
        // cell weights (r29s::tp); unique multi-skill workers keep the annealer from exchanging whole teams
        static const double tpFrac = 0.01;
        if (n <= 50000 && alpha > 0 && K >= 2 && A <= max(10.0, 0.15 * avgZone) && tpFrac > 0) {
            double t1 = elapsed(), v = -1e300;
            vector<int> a = teamPermStep(bestAsg, bestObj, min(1.5, tpFrac * timeLimit), &v);
            if (!a.empty() && v > bestObj + 1e-9 * max(1.0, fabs(bestObj))) offer(a, "teamperm");
            if (szDebug) fprintf(stderr, "teamperm phase %.2fs val %.6f best %.6f\n", elapsed() - t1, v, bestObj);
        }
    }
    long long iters = 0, accepted = 0, macroOk = 0;
    double lastCheckpoint = 0, lastRepair = 0, lastCheckT = 0;
    long long checkMask = 255;  // check the clock every 256 iterations, or every one when iterations are slow
    int procs = effectiveCores();
    // fork worker processes; each anneals with its own seed and reports through a pipe
    int worker = 0;
    vector<pair<pid_t, int>> kids;
    for (int k = 1; k < procs; k++) {
        int fds[2];
        if (pipe(fds) != 0) break;
        pid_t pid = fork();
        if (pid == 0) {
            close(fds[0]);
            for (auto& kd : kids) close(kd.second);
            kids.clear();
            worker = k;
            rng.seed(rng() ^ (0x9E3779B97F4A7C15ULL * (k + 1)));
            kids.push_back({-1, fds[1]});  // our own write end
            break;
        }
        close(fds[1]);
        if (pid > 0) kids.push_back({pid, fds[0]});
        else close(fds[0]);
    }
    // chord plans (rings): every process kicks and refines the best plan with its own seed
    // (only when the chord plans are competitive with the triangulation). Annealing from the
    // triangulation can reach other structures (thin strips whose hulls overlap in empty space near
    // the offices, which no chord cells express), so with several processes the odd ones run the
    // usual search from the triangulation; a single process does so unless the chords lead by 1 %.
    bool chordRun = chordBest.val > -1e299 && !chordOk.empty() && chordBest.val >= triPlain - 0.02 * fabs(triPlain);
    bool chordMine = procs > 1 ? worker % 2 == 0 : chordBest.val >= triPlain + 0.01 * fabs(triPlain);
    if (chordRun && !chordMine && !triPlainAsg.empty()) triAsg = triPlainAsg, triVal = triPlain;
    // r41: one process whose chord plan led the triangulation: the chord anneal takes 35 % (was 70 %) and
    // every other exploration run below starts from the plain triangulation instead of the chord plan
    // (rings with rotated / permuted distance rows: the usual search from the triangulation reaches
    // fewer, larger zones that the chord anneal never leaves; #1-like rings keep the chord result)
    static const int cAlt = 1;
    bool chordAlt = cAlt && procs == 1 && chordRun && chordMine && !triPlainAsg.empty() && n > 1500;
    if (chordRun && chordMine) {
        static const double cIls = chordAlt ? 0.35 : 0.7;
        double until = elapsed() + cIls * max(0.0, timeLimit - elapsed());
        int ev = 0;
        ChordPlan P = chordTop.empty() ? chordBest : chordTop[worker % chordTop.size()];
        static const int cMode = 1;
        if (cMode == 1) {
            chordSA(P, chordOk, chordGap, elapsed() + 0.85 * (until - elapsed()), &ev);
            chordRefine(P, chordOk, chordGap, until, &ev);
            if (elapsed() < until) chordILS(P, chordOk, chordGap, until, &ev);
        } else
            chordILS(P, chordOk, chordGap, until, &ev);
        poolAddAsg(P.asg);
        if (P.val > triVal) {
            triVal = P.val, triAsg = P.asg;
            considerBest(fromAsg(triAsg), true);
            refreshValid();
            if (worker == 0) writeSolution(fromAsg(validAsg), outPath);
        }
    }
    int runs = procs > 1 ? 2 : 4;
    double wa0 = 1.0;
    double wc0 = 0.2;
    int macroRate = 3;
    // exploration runs from scratch, then a refinement phase starting from the best found
    double refineFrac = 0.25;
    double rt0 = 0.05;
    bool noSoft = false;
    double softW = 0.02;
    bool noPD = false;
    // structure search pays off with many offices; with several processes alternate it
    double pdFrac = K <= 5 ? 0.1 : 0.3;
    if (triVal > -1e299 && triVal > 2 * max(fanVal, 0.0)) pdFrac = min(pdFrac, 0.1);  // the triangulation already found the structure
    if (procs > 1 && worker % 2 == 1) pdFrac = 0;
    vector<int> pdBest(n, -1);
    // fewest workers with some needed skill (skills nobody has cannot be served anyway: they do not count)
    int minAvail = INT32_MAX;
    {
        vector<char> needed(NS, 0);
        for (int s = 0; s < n; s++)
            for (int k = 0; k < NS; k++)
                if (smask[s][k]) needed[k] = 1;
        for (int k = 0; k < NS; k++) {
            int av = nativeW ? (int)skW[k].size() : availSkill[k];
            if (needed[k] && av > 0) minAvail = min(minAvail, av);
        }
    }
    if (!singleSkillWorkers) pdFrac = 0;  // with multi-skill workers powerInit only uses task-free sites
    // regime phase ahead (see there): the power-diagram plans collapse to the same few zones on that
    // family, so the free search gets a short slice and no k scan; the regime samples get the time
    bool rgPre = false;
    {
        static const int rgOn = 1;
        int zeroSites = 0, kUse = 0;
        for (int i = 0; i < n; i++) zeroSites += ntask[i] == 0;
        for (int o = 0; o < K; o++) {
            if (maxSize[o] <= 0) continue;
            bool dup = false;
            for (int q = 0; q < o && !dup; q++) dup = maxSize[q] > 0 && px[n + q] == px[n + o] && py[n + q] == py[n + o];
            kUse += !dup;
        }
        // (small inputs only: a sample is an SA run from scratch, and it needs time ~ n to settle)
        static const int rgMaxN = 1200;
        // (not after a winning fan: that helps some fan instances (+19 %) and hurts others (-15 %))
        static const bool rgFan = false;
        // r30: the regime phase also pays at a small balance coefficient (alpha ~ 0.1 x the per-site
        // value: +1..9 % on r30's small-alpha grid shapes with task-free sites or a tight window)
        static const double rgAlphaF = 0.05;
        bool rgTight = A < max(2.0, 0.02 * n);
        // r43: after r37 the regime phase (SA samples from scratch at fixed levels, ~54 % of the time) never
        // reaches the r37 incumbent (#5-like r0 n=1000 K=80..100: best sample 12.0M / polished 14.8M vs 15.6M);
        // the main loop (ladder + refinement from the incumbent) gets that time instead. SZ_RG37=0: old path
        static const int rg37 = 1;
        rgPre = !(rg37 && r37Fired) && rgOn && alpha > 0 && alpha >= rgAlphaF * scale && singleSkillWorkers && triVal <= -1e299 && (fanVal <= -1e299 || rgFan) && kUse >= 3 && refineFrac > 0 &&
                n <= rgMaxN && (rgOn == 2 || zeroSites >= 0.1 * n || rgTight);
        static const double rgPdF = 0.1;
        if (rgPre) pdFrac = min(pdFrac, rgPdF);
        if (szDebug && worker == 0) fprintf(stderr, "regime: gate %d (kUse %d, zero sites %d/%d)\n", (int)rgPre, kUse, zeroSites, n);
    }
    if (pdFrac > 0 && K > 0) {
        double pdLen = pdFrac * (timeLimit - elapsed());
        pdBest = pdSearch(elapsed() + pdLen, scale);
        // regime scan: the free search settles on whatever number of open offices it drifts to;
        // when it opens more offices than there are workers with the scarcest needed skill (m),
        // "m large zones that all have that skill" and "many small zones, some without it" are
        // separate basins. Then searches with exactly k = m - 1, m, m + 1 open offices (starting
        // from the largest offices) get a quick pass, and if one comes close to the free result,
        // the two best k get the rest of a budget of 0.4 x the free search time.
        static const int kScanOn = 1;
        vector<char> isOpen(K, 0);
        for (int s = 0; s < n; s++)
            if (pdBest[s] >= 0) isOpen[pdBest[s]] = 1;
        int kf = 0;
        for (int o = 0; o < K; o++) kf += isOpen[o];
        bool kscan = kScanOn && !rgPre && K >= 4 && minAvail < INT32_MAX && (kScanOn == 2 || minAvail < kf);
        double pdEnd = elapsed() + (kscan ? 0.4 * pdLen : 0.0);
        if (kscan) {
            double pdV = -1e300;
            {
                State p0 = fromAsg(pdBest);
                if (countFeasible(p0)) pdV = trueObjective(p0);
            }
            vector<int> ks;
            for (int k = minAvail - 1; k <= minAvail + 1; k++)
                if (k >= 1 && k < kf && k < K) ks.push_back(k);
            double quick = 0.3 * max(0.0, pdEnd - elapsed()) / max<size_t>(1, ks.size());
            vector<pair<double, int>> res;
            vector<vector<char>> kOpen(K + 1);
            vector<vector<double>> kW(K + 1);
            auto runK = [&](int k, double until) {
                double v;
                vector<char> op = kOpen[k];
                vector<double> w = kW[k];
                vector<int> a = pdSearch(until, scale, k, &v, &op, &w);
                kOpen[k] = op, kW[k] = w;
                if (v > pdV) {
                    pdV = v, pdBest = a, pdBestOpen = op, pdBestW = w;
                    State p0 = fromAsg(a);
                    considerBest(p0, true);
                }
                return v;
            };
            for (int k : ks) {
                if (elapsed() > pdEnd) break;  // slow evaluations (huge inputs): stop on time
                res.push_back({runK(k, elapsed() + quick), k});
            }
            sort(res.rbegin(), res.rend());
            int top = min((int)res.size(), 2);
            if (!res.empty() && res[0].first < pdV - 0.02 * fabs(pdV)) top = 0;  // not promising: leave the time to SA
            for (int i = 0; i < top && elapsed() < pdEnd; i++) {
                double v = runK(res[i].second, elapsed() + max(0.0, pdEnd - elapsed()) / (top - i));
                if (szDebug && worker == 0) fprintf(stderr, "kscan: k=%d quick %.4f long %.4f\n", res[i].second, res[i].first, v);
            }
            if (szDebug && worker == 0) fprintf(stderr, "kscan: free k=%d, m=%d, %zu values, best %.4f\n", kf, minAvail, ks.size(), pdV);
        }
        State p0 = fromAsg(pdBest);
        considerBest(p0, true);
        refreshValid();
        if (worker == 0) writeSolution(fromAsg(validAsg), outPath);
    }
    // task-level construction: Voronoi cells of all offices and the best power diagram's cells
    vector<int> lvAllAsg;  // the plan from all offices' cells (the odd workers' start: they skip pdSearch)
    if (alpha > 0 && singleSkillWorkers) {
        double lvEnd = elapsed() + 0.05 * max(0.0, timeLimit - elapsed());
        double curVal = -1e300;
        {
            State p0 = fromAsg(pdBest);
            bool any = false;
            for (int s = 0; s < n; s++) any |= pdBest[s] >= 0;
            if (any && countFeasible(p0)) curVal = trueObjective(p0);
        }
        vector<int> all(K);
        for (int o = 0; o < K; o++) all[o] = o;
        double v;
        vector<int> a = levelBuild(all, vector<double>(K, 0.0), lvEnd, &v);
        if (v > -1e299) poolAddAsg(a), lvAllAsg = a;
        if (v > curVal) curVal = v, pdBest = a;
        if (!pdBestOpen.empty()) {
            vector<int> lst;
            for (int o = 0; o < K; o++)
                if (pdBestOpen[o]) lst.push_back(o);
            a = levelBuild(lst, pdBestW, lvEnd, &v);
            if (v > -1e299) poolAddAsg(a);
            if (v > curVal) curVal = v, pdBest = a;
        }
        if (curVal > -1e299) {
            State p0 = fromAsg(pdBest);
            considerBest(p0, true);
            refreshValid();
            if (worker == 0) writeSolution(fromAsg(validAsg), outPath);
        }
    }
    // tight count window: line-separated cells with one exact (count, tasks) for every zone
    if (lineGate) {
        static const double lsFrac = 0.12;
        double v;
        lineMode = true;
        vector<int> a = levelSweep(bestAsg, {}, elapsed() + lsFrac * max(0.0, timeLimit - elapsed()), bestObj, &v);
        lineMode = false;
        if (v > -1e299 && !a.empty()) {
            State p0 = fromAsg(a);
            double curVal = -1e300;
            {
                State q = fromAsg(pdBest);
                bool any = false;
                for (int s = 0; s < n; s++) any |= pdBest[s] >= 0;
                if (any && countFeasible(q)) curVal = trueObjective(q);
            }
            if (szDebug && worker == 0) fprintf(stderr, "line sweep %.4f vs start %.4f\n", v, curVal);
            if (v > curVal) pdBest = a;
            considerBest(p0, true);
            refreshValid();
            if (worker == 0) writeSolution(fromAsg(validAsg), outPath);
        }
    }
    // few big zones + task balance: enumerate office subsets x skill splits (fewSearch)
    bool fewWon = false;
    vector<int> fewAsg;
    if (fewGate()) {
        double fewFrac = 0.08;
        double curVal = -1e300;
        {
            State p0 = fromAsg(pdBest);
            bool any = false;
            for (int s = 0; s < n; s++) any |= pdBest[s] >= 0;
            if (any && countFeasible(p0)) curVal = trueObjective(p0);
        }
        vector<double> fv;
        vector<vector<int>> fc = fewSearch(elapsed() + fewFrac * max(0.0, timeLimit - elapsed()), &fv, curVal);
        double startVal = curVal;
        for (size_t i = 0; i < fc.size(); i++) {
            poolAddAsg(fc[i]);
            State p0 = fromAsg(fc[i]);
            considerBest(p0, true);
            if (fv[i] > curVal) curVal = fv[i], fewAsg = fc[i], fewWon = true;
        }
        if (szDebug && worker == 0) fprintf(stderr, "few: %zu rebuilt, best %.4f vs start %.4f\n", fc.size(), curVal, startVal);
        if (!fc.empty()) {
            refreshValid();
            if (worker == 0) writeSolution(fromAsg(validAsg), outPath);
        }
    }
    // more skills / worker types than fewSearch enumerates: local search over subsets x teams
    if (teamGate()) {
        static const double teamFrac = 0.06;
        double curVal = -1e300;
        {
            State p0 = fromAsg(fewWon ? fewAsg : pdBest);
            bool any = false;
            for (int s = 0; s < n; s++) any |= p0.asg[s] >= 0;
            if (any && countFeasible(p0)) curVal = trueObjective(p0);
        }
        curVal = max(curVal, bestObj);
        vector<double> tv;
        vector<vector<int>> tc = teamSearch(elapsed() + teamFrac * max(0.0, timeLimit - elapsed()), &tv, curVal);
        double startVal = curVal;
        for (size_t i = 0; i < tc.size(); i++) {
            poolAddAsg(tc[i]);
            State p0 = fromAsg(tc[i]);
            considerBest(p0, true);
            if (tv[i] > curVal) curVal = tv[i], fewAsg = tc[i], fewWon = true;
        }
        if (szDebug && worker == 0) fprintf(stderr, "team: %zu rebuilt, best %.4f vs start %.4f\n", tc.size(), curVal, startVal);
        if (!tc.empty()) {
            refreshValid();
            if (worker == 0) writeSolution(fromAsg(validAsg), outPath);
        }
    }
    // worker-team search when workers are scarce (fewer workers with some needed skill than offices)
    {
        bool tryWT = K >= 2 && minAvail < K && singleSkillWorkers;
        if (szDebug && worker == 0) fprintf(stderr, "wt: minAvail %d K %d try %d\n", minAvail, K, (int)tryWT);
        if (tryWT) {
            double wtFrac = 0.15;
            double v;
            double curVal = -1e300;
            {
                State p0 = fromAsg(pdBest);
                bool any = false;
                for (int s = 0; s < n; s++) any |= pdBest[s] >= 0;
                if (any && countFeasible(p0)) curVal = trueObjective(p0);
            }
            vector<int> a = wtSearch(elapsed() + wtFrac * max(0.0, timeLimit - elapsed()), scale, &v, max(curVal, bestObj));
            if (szDebug && worker == 0) fprintf(stderr, "wt %.4f vs start %.4f\n", v, curVal);
            if (v > -1e299) poolAddAsg(a);
            if (v > curVal) {
                pdBest = a;
                State p0 = fromAsg(pdBest);
                considerBest(p0, true);
                refreshValid();
                if (worker == 0) writeSolution(fromAsg(validAsg), outPath);
            }
        }
    }
    bool fanWon = false;
    vector<int> pdOrig = pdBest;  // the power-diagram result (pdBest may become the fan below)
    if (fanVal > -1e299) {  // the fan beats the power-diagram result: start from it instead
        double pdVal = -1e300;
        State p0 = fromAsg(pdBest);
        if (countFeasible(p0)) pdVal = trueObjective(p0);
        if (fanVal > pdVal) pdBest = fanAsg, fanWon = true;
        if (szDebug && worker == 0) fprintf(stderr, "fan %.4f vs pd %.4f\n", fanVal, pdVal);
    }
    bool triWon = false;
    if (triVal > -1e299) {  // the triangulation fans beat both: start from them
        double curVal = -1e300;
        State p0 = fromAsg(pdBest);
        if (countFeasible(p0)) curVal = trueObjective(p0);
        if (triVal > curVal) pdBest = triAsg, triWon = true, fanWon = false;
        if (szDebug && worker == 0) fprintf(stderr, "tri %.4f vs start %.4f\n", triVal, curVal);
    }
    // Fan arms: SA from the best fan (A), from the best fan of the other kind (B: strips vs apex),
    // and plain runs (P: from scratch / the power diagram, distance neighbourhoods). A fan start can
    // trap SA in a poor basin, so with one process the first runs try each arm once and the
    // remaining exploration runs go to the arm that reached the best objective; with several
    // processes each process cycles through the arms from its own offset.
    static const int fanArms = 1;
    vector<vector<int>> nearOffStd, nearOrderStd;
    if (fanWon && fanArms) nearOffStd = nearOff, nearOrderStd = nearOrder;
    auto fanNeighbours = [&](const FanGeo& fg, const vector<int>& fasg) {  // angular neighbours
        static const int fanNear = 3;
        vector<double> sang(n), oang(K);
        for (int s = 0; s < n; s++) sang[s] = fanAngle(px[s], py[s], fg);
        for (int o = 0; o < K; o++) oang[o] = fanAngle(px[n + o], py[n + o], fg);
        if (fanNear & 1) {
            vector<char> isOpen(K, 0);
            for (int s = 0; s < n; s++)
                if (fasg[s] >= 0) isOpen[fasg[s]] = 1;
            // offices (all / open in the fan) sorted by angle; per site take the angularly closest ones
            vector<int> all(K), opn;
            for (int o = 0; o < K; o++) all[o] = o;
            sort(all.begin(), all.end(), [&](int a, int b) { return oang[a] < oang[b]; });
            for (int o : all)
                if (isOpen[o]) opn.push_back(o);
            auto closest = [&](const vector<int>& lst, double a, vector<int>& out) {
                out.clear();
                int r = int(lower_bound(lst.begin(), lst.end(), a, [&](int o, double v) { return oang[o] < v; }) - lst.begin()), l = r - 1;
                while ((int)out.size() < L && (l >= 0 || r < (int)lst.size())) {
                    if (r >= (int)lst.size() || (l >= 0 && a - oang[lst[l]] <= oang[lst[r]] - a)) out.push_back(lst[l--]);
                    else out.push_back(lst[r++]);
                }
            };
            vector<int> c1, c2, nl;
            for (int s = 0; s < n; s++) {
                closest(opn, sang[s], c1);
                closest(all, sang[s], c2);
                nl.clear();
                size_t i1 = 0, i2 = 0;
                while ((int)nl.size() < L && (i1 < c1.size() || i2 < c2.size())) {
                    bool fromOpen = (nl.size() % 2 == 0 && i1 < c1.size()) || i2 >= c2.size();
                    int o = fromOpen ? c1[i1++] : c2[i2++];
                    if (find(nl.begin(), nl.end(), o) == nl.end()) nl.push_back(o);
                }
                nearOff[s] = nl;
            }
        }
        if (fanNear & 2)
            for (int o = 0; o < K; o++)
                sort(nearOrder[o].begin(), nearOrder[o].end(), [&](int a, int b) {
                    double da = fabs(sang[a] - oang[o]), db = fabs(sang[b] - oang[o]);
                    return da < db || (da == db && dist[o][a] < dist[o][b]);
                });
    };
    if (fanWon) fanNeighbours(fanGeo, fanAsg);
    int curNb = 0;  // arm whose neighbourhoods are loaded: 0 = A, 1 = B, 2 = plain
    vector<int> arms = {0};
    if (fanWon && fanArms) {
        arms.push_back(2);
        if (fanValB > -1e299) arms.push_back(1);
    }
    double armBest[3] = {-1e300, -1e300, -1e300};
    int bestArm = 0, plainRuns = 0;
    bool havePdOrig = false;
    for (int o : pdOrig)
        if (o >= 0) havePdOrig = true;
    static const int fanRuns = 1;
    bool havePD = false;
    for (int o : pdBest)
        if (o >= 0) havePD = true;
    double pdT = 0.1;
    double exploreEnd = timeLimit - refineFrac * (timeLimit - elapsed());
    // level ladder (heavy task-balance penalty): SA keeps every zone at the common task level it
    // reached first, and moving all zones to another level together is a deep valley for it.
    // Between exploration and refinement, short runs from the best solution pull every zone toward
    // a target level (lvTarget) one step above / below the current one; the step adapts (grow it and
    // keep the direction while it improves, else turn, else halve). Probes get 1/6 of the ladder
    // time each; what is left goes to refinement.
    static const int ladOn = 1;
    // (off with a tight count window: there the probes mostly break the counts and the
    // refinement time they take is worth more)
    // (r24: also with a tight count window - there SA locks onto the first, high task level even
    // harder, and the lower-level / more-offices basin is only reached by probes)
    static const int ladTight = 1;
    int nLad = (ladOn && alpha > 0 && refineFrac > 0 && (ladOn == 2 || ladTight || A >= max(2.0, 0.02 * n))) ? 12 : 0;
    // The probe phase after exploration, in this order (every probe is a short SA run from a start
    // solution with a level target; only what beats the best is kept):
    //  1. runner-ups (below): other office sets from the exploration runs get small ladders of their own;
    //  2. two regime probes: carve out half as many closed offices as there are zones / dissolve the
    //     least valuable third of the zones, level target scaled to keep the total task load;
    //  3. the level ladder on the best; once its step was halved, level probes alternate with
    //     structure probes: one closed office carved out of the zones around it (doInsert) or, when
    //     no insertion looks useful, the least valuable zone dissolved, at the current level.
    // SA alone can hardly change the set of open offices once zones have grown (a closed office
    // inside a zone's hull cannot be opened at all, and at a heavy balance penalty a new or
    // vanishing zone is a deep valley), so the office set of the first good run used to stay, and
    // with task-free sites the regimes (few large zones at a high level / many small ones at a low
    // one) differ by up to ~8 % (instance0: 3 zones 5.17M, 6 zones 5.64M). Candidates are ranked by
    // the profit change of the bare operation; structure probes run twice as long as level probes;
    // the probe window grows from 1/2 to 3/4 of the time after exploration (refinement gets the rest).
    // only with task-free sites (>= 10 %): they make the regimes (a zone at a lower level still
    // covers the task-free sites around it); elsewhere the probe phase is the plain ladder
    // (only on the regime phase's family, see there: alpha > 0, task-free sites >= 10 %, wide count window)
    const bool regimeFam = rgPre;
    static const int sProbeOn = 1;
    static const double sLenMul = 2.0;  // a structure probe has more to rebuild
    const bool sProbes = nLad > 0 && sProbeOn && K >= 3 && regimeFam;
    if (nLad && regimeFam) nLad = 40;
    double ladderEnd50 = exploreEnd + (nLad ? 0.5 : 0.0) * (timeLimit - exploreEnd);
    double ladderEnd = sProbes ? exploreEnd + 0.75 * (timeLimit - exploreEnd) : ladderEnd50;
    // a probe that wins when the window is (nearly) over buys one more probe, up to 9/10 of the time
    // after exploration: an unconverged level costs more than the shorter refinement
    static const double ladMaxF = 0.9;
    double ladderMax = nLad && regimeFam ? exploreEnd + max(ladderEnd - exploreEnd, ladMaxF * (timeLimit - exploreEnd)) : ladderEnd;
    bool ladHalved = false, sTurn = false;  // structure probes alternate with level probes once the level step was halved
    int ladLevel = -1, ladStep = 0, ladDir = 1;
    double probeLen = 0;
    bool sStale = true;                // candidates must be ranked again (new best solution)
    vector<pair<double, int>> sIns, sDel;  // (profit change, office): insert a closed / dissolve an open office
    vector<char> sDoneI(K, 0), sDoneD(K, 0);
    int sKind = 0, sOff = -1;          // this probe: 0 level, 1 insert, 2 dissolve, 3 / 4 regime (several at once)
    // regime probes (once each, right after the runner-ups): k zones at level T -> k' zones at T k / k'
    static const int regOn = 1;
    bool regDone[2] = {!regOn, !regOn};
    // Runner-up starts: an exploration run that ended in another office set within 5 % of the best
    // has not converged its level yet either, and at a heavy balance penalty the regimes (few large
    // zones at a high task level / many small zones at a low one) differ by up to ~8 %. Up to two
    // such results first get level probes of their own (at most 4 each, dropped once 3 % behind
    // after two); whatever they reach goes through considerBest, then the ladder continues.
    struct RunCand {
        double v;
        vector<int> asg;
        int step = 0, dir = 1, probes = 0;
    };
    const int upOn = 1 && regimeFam;
    vector<RunCand> runCands, upQ;
    bool upPicked = false;
    int upCur = -1, upTarget = -1;
    Change ch[2];
    static const bool balLevelOn = true;
    double softBestBase = -1e300;
    // level sweep only where capacity does not bind (zones are cut by the task level, not maxSize)
    bool balGate = true;
    static const bool balMid = true;
    bool balHopeless = false;
    static const bool l1On = false;
    static const double l1C = 0.5;
    static const double l1F = 3.0;
    {
        double capSum = 0;
        for (int o = 0; o < K; o++) capSum += min(maxSize[o], n);
        static const double gateCap = 0.9;
        balGate = capSum >= gateCap * n;
    }
    vector<int> softOpen;
    bool lvFirm = false;  // regime samples (see saLoop)
    bool fewOwed = false;  // a few-office start was taken by the mid-way level plan: next even run gets it
    // one SA run on S (the main loop below and the regime phase): temperature Ts -> Tend over [runStart, runEnd]
    auto saLoop = [&](double runStart, double runEnd, double Ts, bool refine, bool soft) {
    double T = Ts;
    opDeadline = runEnd + 1.0;
    struct OpReset { ~OpReset() { opDeadline = 1e300; } } opReset;
    // nearest offices per site, flat (a copy of nearOff for this run: one load less per move)
    static vector<int> nearFlat;
    nearFlat.resize((size_t)n * L);
    for (int s = 0; s < n; s++)
        for (int j = 0; j < L; j++) nearFlat[(size_t)s * L + j] = nearOff[s][j];
    while (true) {
        if ((iters & checkMask) == 0) {
            double t = elapsed();
            {  // check the clock every 0.1-1 ms
                double gap = t - lastCheckT;
                if (gap < 1e-4 && checkMask < 4095) checkMask = checkMask * 2 + 1;
                else if (gap > 1e-3 && checkMask > 0) checkMask >>= 1;
            }
            lastCheckT = t;
            if (t > runEnd) break;
            double frac = (t - runStart) / (runEnd - runStart);
            T = Ts * pow(Tend / Ts, frac);
            lambdaCnt = refine ? lamEnd : lamStart * pow(lamEnd / lamStart, min(1.0, frac * 1.7));
            double ramp = refine ? 1.0 : min(1.0, frac / 0.7);
            wAlpha = soft ? softW : wa0 + (1 - wa0) * ramp;
            if (soft && l1On && balGate) {
                // the pull grows over the run; the level follows the mean load of open offices
                double c0 = min(alpha, l1C * scale), c1 = min(alpha, l1F * scale);
                l1Cost = c0 * min(1.0, frac / 0.5) + max(0.0, c1 - c0) * max(0.0, (frac - 0.7) / 0.3);
                long long ts = 0;
                int no = 0;
                for (int o = 0; o < K; o++)
                    if (S.cnt[o] > 0) ts += S.tsum[o], no++;
                l1Tau = no ? (double)ts / no : 0;
            } else
                l1Cost = 0;
            // (regime samples: the true balance weight comes back over the last 40 % of the run,
            // so a sample ends near-balanced and its repaired value compares fairly across levels)
            if (lvTarget >= 0) wAlpha = lvFirm ? softW + (1 - softW) * max(0.0, (frac - 0.6) / 0.4) : softW, wLv = 0.2 + 0.8 * ramp;
            wCost = wc0 + (1 - wc0) * ramp;
            if (szDebug && worker == 0 && (iters & ((1 << 22) - 1)) == 0) {
                int c0, c1, t0, t1, no = 0;
                extremes(S, nullptr, 0, c0, c1, t0, t1);
                for (int o = 0; o < K; o++) no += S.cnt[o] > 0;
                fprintf(stderr, "t=%.1f T=%.3g open=%d cnt=[%d,%d] tasks=[%d,%d] base=%.1f E=%.1f lam=%.3g best=%.1f\n", t, T, no, c0, c1, t0, t1, S.base, energy(S), lambdaCnt, bestObj);
            }
            if (t - lastCheckpoint > 10) {
                lastCheckpoint = t;
                refreshValid();
                if (worker == 0) writeSolution(fromAsg(validAsg), outPath);
            }
            if (t - lastRepair > 0.5) {
                lastRepair = t;
                considerBest(S, true);
            }
        }
        iters++;
        int mt = irand(10000);
        bool ok = false;
        if (mt < macroRate) {
            ok = macroMove(S, T);
            macroOk += ok;
        } else if (mt < 7000) {
            // relocate a site: mostly to one of its nearest offices
            int s = irand(n);
            int r = irand(16);
            int to = r < 3 ? -1 : r == 3 ? irand(K) : nearFlat[(size_t)s * L + irand(L)];
            if (to == S.asg[s]) continue;
            ch[0] = {s, S.asg[s], to};
            ok = tryChange(S, ch, 1, T);
        } else if (mt < 8500) {
            // swap sites between neighbouring offices
            int s1 = irand(n);
            int a = S.asg[s1], b = nearFlat[(size_t)s1 * L + irand(L)];
            if (a == b || S.cnt[b] == 0) continue;
            int s2 = S.mem[b][irand(S.cnt[b])];
            ch[0] = {s1, a, b};
            ch[1] = {s2, b, a};
            ok = tryChange(S, ch, 2, T);
        } else {
            // replace an office's site by a free site near that office
            int a = irand(K);
            if (S.cnt[a] == 0) continue;
            int s1 = S.mem[a][irand(S.cnt[a])];
            int s2 = nearOrder[a][irand(min(n, 3 * S.cnt[a] + 10))];
            if (S.asg[s2] != -1) continue;
            ch[0] = {s1, a, -1};
            ch[1] = {s2, -1, a};
            ok = tryChange(S, ch, 2, T);
        }
        if (ok) {
            accepted++;
            if (countFeasible(S)) considerBest(S, false);
        }
    }
    };
    bool pdIsTri = triWon;  // power-diagram start is still the triangulation plan (colder start)
    // ---- regime phase. With a task-balance penalty every zone sits at one common task level, and
    // the level fixes how many zones open: few large zones at a high level or many small ones at a
    // low level are separate basins (instance0: 3 zones at level 149 5.17M, 6 at 59 5.64M, 7 at 54
    // 5.72M). SA cannot cross between them (a closed office inside an open zone's hull cannot be
    // opened, and a zone appearing or vanishing at a heavy balance penalty is a deep valley), and the
    // power-diagram plans with k open offices collapse to the same 2-3 zones (their cells cannot
    // express zones that serve only some skills), so the office set of the first good run used to
    // stay. Here the regimes are sampled on purpose: short SA runs from scratch with every zone pulled
    // toward a fixed level T = 0.55 x (tasks on profitable sites) / k for a spread of zone counts k
    // (a zone stops growing at T, so about k offices open), then more runs around the levels of the
    // three best zone counts. The best distinct office sets are polished by successive halving (four
    // get a short polish - SA from the sample, level probes, office insert / dissolve probes, a cold
    // run -, the two best of those a long one), and the main loop continues from the overall best
    // with level probes and refinement only (the samples are its exploration). Several processes:
    // every one samples its own shifted levels.
    if (rgPre && nLad > 0) {
        static const double rgSampF = 0.28;
        static const double rgPol1 = 0.06;
        static const double rgPol2 = 0.15;
        static const int rgTop1 = 4;
        static const int rgTop2 = 2;
        static const int rgStruct = 1;
        static const bool rgFirm = false;
        long long tTot = 0;  // tasks on sites some office serves at a profit
        int zeroSites = 0;
        for (int s = 0; s < n; s++) {
            double bv = -1e300;
            for (int o = 0; o < K; o++)
                if (maxSize[o] > 0) bv = max(bv, rew[s] - dist[o][s]);
            if (bv > 0) tTot += ntask[s];
            zeroSites += ntask[s] == 0;
        }
        int kUse = 0, k0 = openOfAsg(bestAsg).size();
        for (int o = 0; o < K; o++) {
            if (maxSize[o] <= 0) continue;
            bool dup = false;
            for (int q = 0; q < o && !dup; q++) dup = maxSize[q] > 0 && px[n + q] == px[n + o] && py[n + q] == py[n + o];
            kUse += !dup;
        }
        if (tTot > 0) {
            const double t0 = elapsed(), left = max(0.0, timeLimit - t0);
            const double sampleEnd = t0 + rgSampF * left;
            const double shift = 1 + 0.06 * (worker % 3 == 1 ? 1 : worker % 3 == 2 ? -1 : 0);
            // zone counts 2 .. max(10, 2 k0 + 4) (at most the usable offices), about 1.3x apart
            int kMax = min(kUse, max(10, 2 * k0 + 4));
            vector<int> grid;
            for (double k = 2; k <= kMax + 1e-9; k = max(k + 1, k * 1.3)) {
                int T = max(1, (int)lround(0.55 * shift * tTot / (int)k));
                if (find(grid.begin(), grid.end(), T) == grid.end()) grid.push_back(T);
            }
            if (zeroSites >= 0.2 * n) grid.push_back(0);  // level 0: task-free zones without workers
            const double runLen = (sampleEnd - t0) / max<size_t>(1, 2 * grid.size());
            struct Smp {
                int T;
                double v;
                vector<int> asg;
            };
            vector<Smp> smp;
            auto tRun = [&](int T, double until) {  // SA from scratch pulled toward level T; its repaired best
                vector<int> gA = bestAsg;
                double gO = bestObj;
                initState(S);
                bestAsg = S.asg, bestObj = trueObjective(S);
                runBestObj = -1e300;
                lvTarget = T, lvFirm = rgFirm;
                saLoop(elapsed(), until, Tstart, false, false);
                lvTarget = -1, wLv = 0, lvFirm = false;
                considerBest(S, true);
                if (bestObj > -1e299) smp.push_back({T, bestObj, bestAsg}), poolAddAsg(bestAsg);
                if (gO > bestObj) bestObj = gO, bestAsg = gA;
            };
            for (int T : grid) tRun(T, elapsed() + runLen);
            for (int i = 0; elapsed() + 0.5 * runLen < sampleEnd; i++) {
                // more samples: the best level of each of the three best zone counts in turn, jittered
                vector<int> bases, zs;
                vector<int> ord(smp.size());
                for (int j = 0; j < (int)smp.size(); j++) ord[j] = j;
                sort(ord.begin(), ord.end(), [&](int a, int b) { return smp[a].v > smp[b].v; });
                for (int j : ord) {
                    int z = openOfAsg(smp[j].asg).size();
                    if (z == 0 || find(zs.begin(), zs.end(), z) != zs.end()) continue;  // (an empty plan: T out of reach)
                    zs.push_back(z), bases.push_back(smp[j].T);
                    if (bases.size() >= 3) break;
                }
                if (bases.empty()) break;
                int base = bases[i % bases.size()];
                int T = base == 0 ? 0 : max(1, (int)lround(base * (1 + 0.2 * (urand() - 0.5))));
                tRun(T, min(sampleEnd, elapsed() + runLen));
            }
            sort(smp.begin(), smp.end(), [](const Smp& a, const Smp& b) { return a.v > b.v; });
            if (szDebug && worker == 0)
                for (auto& m : smp) fprintf(stderr, "regime sample: T=%d -> %d zones, %.4f\n", m.T, (int)openOfAsg(m.asg).size(), m.v);
            // polish one regime: SA from the start, level probes (the ladder); once its step was
            // halved they alternate with structure probes: a closed office carved out of the zones
            // around it (doInsert) or an open zone dissolved, at the current level (ranked by the
            // profit change of the bare operation); a cold run at the end. Returns its best.
            auto polish = [&](const vector<int>& start, double until) {
                vector<int> gA = bestAsg;
                double gO = bestObj;
                double len = max(0.0, until - elapsed());
                {
                    State s0 = fromAsg(start);
                    bestAsg = start, bestObj = countFeasible(s0) ? trueObjective(s0) : -1e300;
                    S = s0;
                }
                runBestObj = -1e300;
                lvTarget = -1, wLv = 0;
                saLoop(elapsed(), elapsed() + 0.3 * len, Tstart * pdT, false, false);
                considerBest(S, true);
                int step = 0, dir = 1, lv0 = -1;
                bool halved = false, sTurnP = false, stale = true;
                vector<pair<double, int>> ins, del;
                vector<char> doneI(K, 0), doneD(K, 0);
                double probe = max(0.1 * len, min(0.25 * len, 2.0));
                while (elapsed() + 0.5 * probe < until - 0.15 * len) {
                    State b = fromAsg(bestAsg);
                    int lo = INT32_MAX, no = 0;
                    for (int o = 0; o < K; o++)
                        if (b.cnt[o] > 0) lo = min(lo, b.tsum[o]), no++;
                    if (no < 1 || lo == INT32_MAX || !countFeasible(b)) break;
                    if (lv0 < 0) step = max(1, (int)lround(0.06 * lo));
                    lv0 = lo;
                    int kind = 0, off = -1;  // 0 level, 1 insert, 2 dissolve
                    if (rgStruct && ((halved && sTurnP) || step < 1 || no < 2 || lo <= 0)) {
                        if (stale) {
                            stale = false;
                            ins.clear(), del.clear();
                            fill(doneI.begin(), doneI.end(), 0), fill(doneD.begin(), doneD.end(), 0);
                            double rankEnd = elapsed() + 0.25 * probe;
                            vector<int> ord(K);
                            for (int o = 0; o < K; o++) ord[o] = o;
                            for (int i = K - 1; i > 0; i--) swap(ord[i], ord[irand(i + 1)]);
                            for (int q : ord) {
                                if (elapsed() > rankEnd) break;
                                if (maxSize[q] <= 0) continue;
                                State c = b;
                                if (b.cnt[q] > 0) {
                                    if (no < 2) continue;
                                    vector<int> m = c.mem[q];
                                    doUnassign(c, m);
                                    doRefill(c, m);
                                    del.push_back({c.base - b.base, q});
                                } else {
                                    bool dup = false;
                                    for (int o = 0; o < K && !dup; o++)
                                        dup = b.cnt[o] > 0 && px[n + o] == px[n + q] && py[n + o] == py[n + q];
                                    if (dup || doInsert(c, q) == 0) continue;
                                    if (c.base > b.base) ins.push_back({c.base - b.base, q});
                                }
                            }
                            sort(ins.rbegin(), ins.rend());
                            sort(del.rbegin(), del.rend());
                        }
                        for (auto& e : ins)
                            if (!doneI[e.second]) {
                                kind = 1, off = e.second;
                                break;
                            }
                        if (!kind)
                            for (auto& e : del)
                                if (!doneD[e.second]) {
                                    kind = 2, off = e.second;
                                    break;
                                }
                    }
                    if (!kind && (step < 1 || no < 2 || lo <= 0)) break;
                    if (halved) sTurnP = !sTurnP;
                    double before = bestObj;
                    S = b;
                    if (kind == 1) doInsert(S, off), doneI[off] = 1;
                    if (kind == 2) {
                        vector<int> m = S.mem[off];
                        doUnassign(S, m);
                        doRefill(S, m);
                        doneD[off] = 1;
                    }
                    lvTarget = kind ? lo : max(0, lo + dir * step);
                    runBestObj = -1e300;
                    saLoop(elapsed(), min(until - 0.15 * len, elapsed() + probe * (kind ? 1.5 : 1.0)), Tstart * pdT, false, false);
                    lvTarget = -1, wLv = 0;
                    considerBest(S, true);
                    bool won = bestObj > before + 1e-9 * max(1.0, fabs(before));
                    if (won) stale = true;
                    if (szDebug && worker == 0) fprintf(stderr, "regime probe: %s %d level %d target %d -> %s %.4f\n", kind == 1 ? "insert" : kind == 2 ? "dissolve" : "level", off, lo, kind ? lo : lo + dir * step, won ? "better" : "no", bestObj);
                    if (kind) continue;
                    if (won) step = max(step + 1, step * 3 / 2);
                    else if (dir > 0) dir = -1;
                    else dir = 1, step /= 2, halved = true;
                }
                S = fromAsg(bestAsg);
                runBestObj = -1e300;
                saLoop(elapsed(), until, Tstart * rt0, true, false);
                considerBest(S, true);
                pair<double, vector<int>> res = {bestObj, bestAsg};
                if (gO > bestObj) bestObj = gO, bestAsg = gA;
                return res;
            };
            // successive halving over the best distinct office sets
            vector<pair<double, vector<int>>> stage;
            {
                vector<vector<int>> seen;
                for (int i = 0; i < (int)smp.size() && (int)stage.size() < rgTop1; i++) {
                    vector<int> op = openOfAsg(smp[i].asg);
                    if (find(seen.begin(), seen.end(), op) != seen.end()) continue;
                    seen.push_back(op);
                    stage.push_back({smp[i].v, smp[i].asg});
                }
            }
            for (int round = 0; round < 2 && !stage.empty(); round++) {
                double len = (round == 0 ? rgPol1 : rgPol2) * left;
                for (auto& c : stage) {
                    if (elapsed() + 0.5 * len > timeLimit - 0.12 * left) break;
                    int z = openOfAsg(c.second).size();
                    double v0 = c.first;
                    c = polish(c.second, elapsed() + len);
                    if (szDebug && worker == 0) fprintf(stderr, "regime polish %d: %d zones, %.4f -> %.4f (best %.4f)\n", round, z, v0, c.first, bestObj);
                    poolAddAsg(c.second);
                }
                sort(stage.begin(), stage.end(), [](auto& a, auto& b) { return a.first > b.first; });
                if ((int)stage.size() > rgTop2) stage.resize(rgTop2);
            }
            lvTarget = -1, wLv = 0;
            refreshValid();
            if (worker == 0) writeSolution(fromAsg(validAsg), outPath);
            if (szDebug && worker == 0) fprintf(stderr, "regime phase: %.1fs, %zu samples, best %.4f\n", elapsed() - t0, smp.size(), bestObj);
            // the main loop continues from the overall best in the time left: level probes and refinement
            static const int rgRuns = 0;
            runs = rgRuns;
            exploreEnd = timeLimit - refineFrac * (timeLimit - elapsed());
            ladderEnd50 = exploreEnd + (nLad ? 0.5 : 0.0) * (timeLimit - exploreEnd);
            ladderEnd = sProbes ? exploreEnd + 0.75 * (timeLimit - exploreEnd) : ladderEnd50;
            ladderMax = nLad && regimeFam ? exploreEnd + max(ladderEnd - exploreEnd, ladMaxF * (timeLimit - exploreEnd)) : ladderEnd;
        }
    }
    auto rankOps = [&](const State& b, int no) {  // rank the operations on the current best (bounded share of a probe)
        if (!sStale) return;
        sStale = false;
        sIns.clear(), sDel.clear();
        fill(sDoneI.begin(), sDoneI.end(), 0), fill(sDoneD.begin(), sDoneD.end(), 0);
        double rankEnd = elapsed() + 0.25 * probeLen;
        vector<int> ord(K);
        for (int o = 0; o < K; o++) ord[o] = o;
        for (int i = K - 1; i > 0; i--) swap(ord[i], ord[irand(i + 1)]);  // fair when the clock cuts the ranking
        for (int q : ord) {
            if (elapsed() > rankEnd) break;
            if (maxSize[q] <= 0) continue;
            State c = b;
            if (b.cnt[q] > 0) {
                if (no < 2) continue;
                vector<int> m = c.mem[q];
                doUnassign(c, m);
                doRefill(c, m);
                sDel.push_back({c.base - b.base, q});
            } else {
                bool dup = false;
                for (int o = 0; o < K && !dup; o++)
                    dup = b.cnt[o] > 0 && px[n + o] == px[n + q] && py[n + o] == py[n + q];
                if (dup || doInsert(c, q) == 0) continue;
                if (c.base > b.base) sIns.push_back({c.base - b.base, q});
            }
        }
        sort(sIns.rbegin(), sIns.rend());
        sort(sDel.rbegin(), sDel.rend());
    };
    for (int run = 0; run <= runs + nLad; run++) {
        bool refine = run == runs + nLad;
        bool ladder = run >= runs && !refine;  // level-ladder probes between exploration and refinement
        if ((ladder || refine) && !eqAsg.empty()) {
            if (szDebug && worker == 0) fprintf(stderr, "eq plan %.4f joins (best %.4f)\n", eqVal, bestObj);
            bool lead = eqVal > bestObj;
            if (lead) considerBest(fromAsg(eqAsg), true);
            eqAsg.clear();
            // r33: the exact plan leads: more plans and subtree rebuilds around its zone count
            static const double eqxLate = 0.3;
            if (lead && eqFromX && eqxLate > 0 && eqxLate * (timeLimit - elapsed()) >= 3.0) {
                double t1 = elapsed(), xv = -1e300;
                vector<int> xa = eqExact(t1 + eqxLate * max(0.0, timeLimit - t1), &xv);
                if (szDebug) fprintf(stderr, "[w%d] eqx late %.2fs, plan %.4f (best %.4f)\n", worker, elapsed() - t1, xv, bestObj);
                if (!xa.empty() && xv > bestObj) considerBest(fromAsg(xa), true);
            }
        }
        if (refine && refineFrac <= 0) break;
        if (ladder) {  // pick this probe's target level from the current best
            State b = fromAsg(bestAsg);
            int lo = INT32_MAX, no = 0;
            for (int o = 0; o < K; o++)
                if (b.cnt[o] > 0) lo = min(lo, b.tsum[o]), no++;
            if (probeLen <= 0) probeLen = max(0.0, ladderEnd50 - elapsed()) / 6;
            if (ladLevel < 0) ladStep = max(1, (int)lround(0.06 * lo)), ladDir = 1;
            ladLevel = lo;
            sKind = 0, sOff = -1;
            if (!upPicked) {  // runner-ups: other office sets among the exploration results
                upPicked = true;
                auto openOf = [&](const vector<int>& a) {
                    vector<char> op(K, 0);
                    for (int i = 0; i < n; i++)
                        if (a[i] >= 0) op[a[i]] = 1;
                    return op;
                };
                vector<vector<char>> seen = {openOf(bestAsg)};
                // exploration results within 5 % of the best, the best first, distinct office sets
                vector<pair<double, int>> order;
                for (int i = 0; i < (int)runCands.size(); i++)
                    if (runCands[i].v >= bestObj - 0.05 * fabs(bestObj)) order.push_back({runCands[i].v, i});
                sort(order.rbegin(), order.rend());
                for (auto& e : order) {
                    if (!upOn || upQ.size() >= 2) break;
                    RunCand& c = runCands[e.second];
                    vector<char> op = openOf(c.asg);
                    if (find(seen.begin(), seen.end(), op) != seen.end()) continue;
                    seen.push_back(op);
                    upQ.push_back(c);
                    if (szDebug && worker == 0) {
                        State q = fromAsg(c.asg);
                        int z = 0, lv = INT32_MAX;
                        for (int o = 0; o < K; o++)
                            if (q.cnt[o] > 0) z++, lv = min(lv, q.tsum[o]);
                        fprintf(stderr, "runner-up %zu: %.4f, %d zones, level %d\n", upQ.size() - 1, c.v, z, lv);
                    }
                }
                runCands.clear();
            }
            upCur = -1;
            for (int round = 0; round < 4 && upCur < 0; round++)  // round robin: every runner-up gets a probe in turn
            for (int i = 0; i < (int)upQ.size() && upCur < 0; i++) {
                RunCand& c = upQ[i];
                if (c.probes != round) continue;
                if (c.probes >= 4 || (c.probes >= 2 && c.v < bestObj - 0.03 * fabs(bestObj)) || c.v >= bestObj - 1e-9 * max(1.0, fabs(bestObj))) continue;
                State b2 = fromAsg(c.asg);
                int lo2 = INT32_MAX, no2 = 0;
                for (int o = 0; o < K; o++)
                    if (b2.cnt[o] > 0) lo2 = min(lo2, b2.tsum[o]), no2++;
                if (no2 < 1 || lo2 <= 0) {
                    c.probes = 4;
                    continue;
                }
                if (c.step == 0) c.step = max(1, (int)lround(0.06 * lo2));
                upCur = i, upTarget = max(1, lo2 + c.dir * c.step);
            }
            if (upCur >= 0 && elapsed() + 0.5 * probeLen <= ladderEnd) goto ladderGo;
            if (sProbes && !(regDone[0] && regDone[1]) && no >= 1 && lo > 0 && countFeasible(b) && elapsed() + 0.5 * probeLen <= ladderEnd) {
                rankOps(b, no);
                if (!regDone[0]) {
                    regDone[0] = true;
                    if (sIns.size() >= 2) sKind = 3;
                }
                if (sKind == 0 && !regDone[1]) {
                    regDone[1] = true;
                    if (no >= 3 && !sDel.empty()) sKind = 4;
                }
                if (sKind) goto ladderGo;
            }
            if (sProbes && no >= 1 && lo > 0 && countFeasible(b) && ((ladHalved && sTurn) || ladStep < 1 || no < 2)) {
                rankOps(b, no);
                for (auto& e : sIns)
                    if (!sDoneI[e.second]) {
                        sKind = 1, sOff = e.second;
                        break;
                    }
                if (sKind == 0)
                    for (auto& e : sDel)
                        if (!sDoneD[e.second]) {
                            sKind = 2, sOff = e.second;
                            break;
                        }
            }
            // nothing to shift, no step left (and no structure probe), or no time for a probe: the rest goes to refinement
            if (no < 1 || lo <= 0 || !countFeasible(b) || (sKind == 0 && (ladStep < 1 || no < 2)) || elapsed() + 0.5 * probeLen > ladderEnd) {
                run = runs + nLad - 1;
                continue;
            }
            if (ladHalved) sTurn = !sTurn;
        }
    ladderGo:
        // every other exploration run nearly ignores task imbalance (repairs fix it when recording)
        bool soft = !refine && !ladder && alpha > 0 && run % 2 == 1 && !noSoft;
        double runStart = elapsed();
        double runEnd = refine ? timeLimit : ladder ? min(ladderEnd, runStart + probeLen * (sKind ? sLenMul : 1.0)) : runStart + (exploreEnd - runStart) / (runs - run);
        double Ts = refine ? Tstart * rt0 : ladder ? Tstart * pdT : Tstart;
        bool pdStart = havePD && !refine && !noPD && run % 2 == 0 && (procs > 1 || run == 2);
        if (fanWon && fanRuns == 1) pdStart = !refine;
        if (triWon) pdStart = !refine;
        bool fewStart = fewWon && !fanWon && !triWon && !refine && !ladder && run % 2 == 0 && (!havePD || (run / 2 + worker) % 2 == 0 || fewOwed);
        if (fewStart) pdStart = false;
        // one process (few CPUs on the judge): runs 0..3 copy what the workers of a multi-process run
        // do instead of the old scratch/soft/plan/soft order (scratch run 0 and soft run 3 rarely ended
        // best): run 0 starts from the power-diagram plan like worker 0's first run (or the few-office
        // structure, as before), run 1 stays soft, run 2 takes the mid-way level plan as before, and
        // run 3 is the odd workers' run: the hot run from scratch, or, when the few-office start won,
        // the all-offices level plan the odd workers start from (they skip pdSearch)
        static const int r0Mode = 1;
        static const int r3Mode = 4;
        bool lvStart = false;
        if (procs == 1 && !fanWon && !triWon && !refine && !ladder) {
            bool lvAlt = !lvAllAsg.empty() && lvAllAsg != pdBest;
            if (run == 0 && !fewStart) {
                if (r0Mode == 1 && havePD) pdStart = true;
                else if (r0Mode == 2 && lvAlt) lvStart = true;
            } else if (run == 3) {
                if ((r3Mode == 1 || (r3Mode == 4 && fewWon)) && lvAlt) lvStart = true, soft = false;
                else if (r3Mode == 2 && havePD) pdStart = true, soft = false;
                else if (r3Mode >= 3) soft = false, pdStart = false;  // the hot run from scratch
            }
        }
        if (lvStart) pdStart = false;
        if (fanWon && fanRuns == 2) pdStart = !refine && run % 2 == 0;
        int arm = 0;
        if (fanWon && fanArms) {
            int m = arms.size();
            if (refine || ladder) arm = bestArm;
            else if (procs > 1) arm = arms[(worker + run) % m];
            else if (run < m) arm = arms[run];
            else {
                arm = arms[0];
                for (int a : arms)
                    if (armBest[a] > armBest[arm]) arm = a;
            }
            if (arm != curNb) {
                if (arm == 2) nearOff = nearOffStd, nearOrder = nearOrderStd;
                else fanNeighbours(arm == 0 ? fanGeo : fanGeoB, arm == 0 ? fanAsg : fanAsgB);
                curNb = arm;
            }
        }
        int midRun = runs >= 4 ? 2 : (procs > 1 && worker % 2 == 1 ? 1 : -1);
        if (!refine && !ladder && run == midRun && balMid && alpha > 0 && singleSkillWorkers && balLevelOn && balGate) {
            // mid-way: the level plan becomes the start of this run (and later power-diagram starts)
            double bf = lineGate ? epBalFrac : balFrac;
            double budget = min(0.5 * bf * timeLimit, (lineGate ? 0.25 : 0.2) * max(0.0, timeLimit - elapsed()));
            double lvV = -1e300;
            vector<int> a = levelSweep(bestAsg, softOpen, elapsed() + budget, bestObj, &lvV);
            if (lvV < bestObj - 0.03 * fabs(bestObj)) balHopeless = true;  // not close: no final sweep
            if (!a.empty() && lvV >= bestObj - 0.03 * fabs(bestObj)) {
                State p0 = fromAsg(a);
                if (countFeasible(p0) && validateFull(p0).empty()) {
                    pdBest = p0.asg, havePD = true, pdIsTri = false;
                    considerBest(p0, true);
                    if (!(fanWon && fanArms)) soft = false, pdStart = true;  // this run starts from the plan
                    if (fewStart) fewStart = false, fewOwed = true;  // rotate: level plan now, few structure next
                }
            }
        }
        if (refine && alpha > 0 && singleSkillWorkers && balLevelOn && balGate && !balHopeless) {
            // balanced-cell level construction around the open sets of the best solution and of
            // the best soft run (which serves more sites, but unevenly): every office at one level
            double bf = lineGate ? epBalFrac : balFrac;
            double budget = min(bf * timeLimit, (lineGate ? 0.5 : 0.4) * max(0.0, timeLimit - elapsed()));
            double lvV;
            vector<int> a = levelSweep(bestAsg, softOpen, elapsed() + budget, bestObj, &lvV);
            if (!a.empty() && lvV > bestObj) considerBest(fromAsg(a), true);
        }
        double bestBefore = bestObj;
        runBestObj = -1e300;
        static const int ladZero = 1;  // r24: level 0 (task-free zones) is a target too
        const int runLv = ladder ? (upCur >= 0 ? upTarget : sKind ? ladLevel : max(ladZero ? 0 : 1, ladLevel + ladDir * ladStep)) : -1;
        int runTgt = runLv;  // the level target of this run (a regime probe rescales it below)
        // the target is set after the structure operations: their refills run without a level term
        // (a stale wLv from the previous run would bias them)
        lvTarget = -1;
        if (refine || ladder) {
            S = fromAsg(ladder && upCur >= 0 ? upQ[upCur].asg : bestAsg);
            if (ladder && sKind == 1) doInsert(S, sOff), sDoneI[sOff] = 1;
            if (ladder && sKind >= 3) {  // regime probe
                int k0 = 0;
                for (int o = 0; o < K; o++) k0 += S.cnt[o] > 0;
                int m = sKind == 3 ? max(2, (k0 + 1) / 2) : max(1, k0 / 3), done = 0;
                if (sKind == 3) {
                    for (size_t i = 0; i < sIns.size() && done < m; i++) done += doInsert(S, sIns[i].second) > 0;
                } else {
                    for (size_t i = 0; i < sDel.size() && done < m; i++) {
                        vector<int> mm = S.mem[sDel[i].second];
                        doUnassign(S, mm);
                        doRefill(S, mm);
                        done++;
                    }
                }
                int k1 = sKind == 3 ? k0 + done : k0 - done;
                if (k1 > 0) runTgt = max(1, (int)lround((double)ladLevel * k0 / k1));
                sOff = done;
            }
            if (ladder && sKind == 2) {
                vector<int> m = S.mem[sOff];
                doUnassign(S, m);
                doRefill(S, m);
                sDoneD[sOff] = 1;
            }
            lvTarget = runTgt;
        } else if (fanWon && fanArms) {
            if (arm == 2) {
                if (plainRuns++ % 2 == 1 && havePdOrig) {
                    S = fromAsg(pdOrig);
                    considerBest(S, true);
                    Ts = Tstart * pdT;
                } else
                    initState(S);
            } else {
                S = fromAsg(arm == 0 ? fanAsg : fanAsgB);
                considerBest(S, true);
                Ts = Tstart * pdT;
            }
        } else if (lvStart) {
            S = fromAsg(lvAllAsg);
            considerBest(S, true);
            Ts = Tstart * pdT;
        } else if (fewStart) {  // the few-office structure (pdBest keeps the power-diagram start)
            fewOwed = false;
            S = fromAsg(fewAsg);
            considerBest(S, true);
            Ts = Tstart * pdT;
        } else if (pdStart) {
            S = fromAsg(chordAlt && pdIsTri && !ladder && run % 2 == 1 ? triPlainAsg : pdBest);
            considerBest(S, true);
            static const double triT = 0.01;
            Ts = Tstart * (pdIsTri ? triT : pdT);
        } else
            initState(S);
        saLoop(runStart, runEnd, Ts, refine, soft);
        l1Cost = 0, lvTarget = -1;  // soft terms end with the SA run
        if (soft && S.base > softBestBase) {
            softBestBase = S.base;
            softOpen.clear();
            for (int o = 0; o < K; o++)
                if (S.cnt[o] > 0) softOpen.push_back(o);
        }
        considerBest(S, elapsed() < timeLimit);  // no late repairs past the limit
        poolAddAsg(S.asg);
        poolAddAsg(bestAsg);
        if (!refine && !ladder && nLad && upOn) {  // exploration result: a possible runner-up start
            vector<int> a;
            double v = repairedValue(S, a);
            if (v > -1e299) runCands.push_back({v, a});
        }
        if (ladder && upCur >= 0) {  // runner-up probe: its own small ladder
            RunCand& c = upQ[upCur];
            vector<int> a;
            double v = repairedValue(S, a);
            bool won = v > c.v + 1e-9 * max(1.0, fabs(c.v));
            if (szDebug && worker == 0) fprintf(stderr, "runner-up %d: target %d -> %s %.4f (best %.4f)\n", upCur, runLv, won ? "better" : "no", v, bestObj);
            if (won) c.v = v, c.asg = a, c.step = max(c.step + 1, c.step * 3 / 2);
            else if (c.dir > 0) c.dir = -1;
            else c.dir = 1, c.step /= 2;
            if (c.step < 1) c.probes = 4;
            c.probes++;
            if (bestObj > bestBefore + 1e-9 * max(1.0, fabs(bestBefore))) sStale = true;
            if (won && elapsed() + 0.5 * probeLen > ladderEnd) ladderEnd = min(ladderMax, ladderEnd + probeLen);
        } else if (ladder && sKind) {  // structure probe: a new best needs a new ranking
            bool won = bestObj > bestBefore + 1e-9 * max(1.0, fabs(bestBefore));
            if (szDebug && worker == 0) fprintf(stderr, "sprobe: %s %d at level %d (target %d) -> %s %.4f\n", sKind == 1 ? "insert" : sKind == 2 ? "dissolve" : sKind == 3 ? "regime+" : "regime-", sOff, runLv, runTgt, won ? "better" : "no", runBestObj);
            if (won) sStale = true;
            if (won && elapsed() + 0.5 * probeLen > ladderEnd) ladderEnd = min(ladderMax, ladderEnd + sLenMul * probeLen);
        } else if (ladder) {  // adapt the ladder: keep a winning direction, else turn, else halve the step
            bool won = bestObj > bestBefore + 1e-9 * max(1.0, fabs(bestBefore));
            if (won) sStale = true;
            if (szDebug && worker == 0) fprintf(stderr, "ladder: level %d target %d -> %s %.4f\n", ladLevel, runLv, won ? "better" : "no", runBestObj);
            if (won) ladStep = max(ladStep + 1, ladStep * 3 / 2);
            else if (ladDir > 0) ladDir = -1;
            else ladDir = 1, ladStep /= 2, ladHalved = true;
            if (won && elapsed() + 0.5 * probeLen > ladderEnd) ladderEnd = min(ladderMax, ladderEnd + probeLen);
        } else if (!refine) {
            armBest[arm] = max(armBest[arm], runBestObj);
            if (bestObj > bestBefore + 1e-9) bestArm = arm;
        }
        if (szDebug && worker == 0 && fanWon && fanArms) fprintf(stderr, "run %d arm %d: run best %.4f\n", run, arm, runBestObj);
        if (worker == 0) fprintf(stderr, "run %d: best so far %.6f (run best %.6f, level %d)\n", run, bestObj, runBestObj, runLv);
    }
    refreshValid();
    if (worker != 0) {
        int fd = kids[0].second;
        writeAll(fd, &validObj, sizeof validObj);
        writeAll(fd, validAsg.data(), sizeof(int) * AS);
        {  // the zone pool: count, then (office, size, sites...) per zone
            vector<int> buf = {(int)pool.size()};
            for (auto& z : pool) {
                buf.push_back(z.o), buf.push_back(z.s.size());
                buf.insert(buf.end(), z.s.begin(), z.s.end());
            }
            writeAll(fd, buf.data(), sizeof(int) * buf.size());
        }
        close(fd);
        _exit(0);
    }
    // collect worker results
    vector<pair<double, vector<int>>> cands;
    cands.push_back({validObj, validAsg});
    for (auto& kd : kids) {
        double obj;
        vector<int> asg(AS);
        double waitLeft = min(timeLimit + 20, fullLimit + 0.3) - elapsed();
        struct pollfd pf = {kd.second, POLLIN, 0};
        if (waitLeft > 0 && poll(&pf, 1, (int)(waitLeft * 1000)) > 0 && readAll(kd.second, &obj, sizeof obj) &&
            readAll(kd.second, asg.data(), sizeof(int) * AS)) {
            cands.push_back({obj, asg});
            int cnt = 0;
            if (readAll(kd.second, &cnt, sizeof cnt)) {
                size_t cap = poolCap;
                poolCap = max(poolCap, (size_t)200000);  // the merged pool may be larger than one process's
                for (int i = 0; i < cnt; i++) {
                    int hd[2];
                    if (!readAll(kd.second, hd, sizeof hd) || hd[0] < 0 || hd[0] >= K || hd[1] < 0 || hd[1] > n) break;
                    vector<int> s(hd[1]);
                    if (hd[1] && !readAll(kd.second, s.data(), sizeof(int) * hd[1])) break;
                    poolAddZone(hd[0], s);
                }
                poolCap = max(cap, poolCap);
            }
        } else
            kill(kd.first, SIGKILL);
        close(kd.second);
        waitpid(kd.first, nullptr, 0);
    }
    sort(cands.begin(), cands.end(), [](auto& a, auto& b) { return a.first > b.first; });
    string objs;
    for (auto& c : cands) objs += to_string(c.first) + " ";
    fprintf(stderr, "procs=%d results: %s\n", procs, objs.c_str());
    for (auto& c : cands) {
        if (validateFull(fromAsg(c.second)).empty()) {
            bestObj = c.first;
            bestAsg = c.second;
            break;
        }
    }
    // teamperm on the best answers before the final choice (every process's result is in cands; no child can be
    // killed for it); only a valid, count-feasible strict improvement replaces the best
    {
        static const double tpEndFrac = 0.01;
        if (tpEndFrac > 0 && r29s::n == n && r29s::K == K && n > 0 && n <= 50000 && alpha > 0 && K >= 2 && A <= max(10.0, 0.15 * n / K)) {
            double budget = min(1.5, tpEndFrac * fullLimit), tEnd = elapsed() + budget, t1 = elapsed();
            int tried = 0;
            for (size_t i = 0; i < cands.size() && tried < 3 && elapsed() < tEnd - 0.05; i++) {
                if (i > 0 && cands[i].second == cands[i - 1].second) continue;
                if (!validateFull(fromAsg(cands[i].second)).empty()) continue;
                double v = -1e300;
                vector<int> a = teamPermStep(cands[i].second, bestObj, (tEnd - elapsed()) / (3 - tried), &v);
                tried++;
                if (a.empty() || !(v > bestObj + 1e-9 * max(1.0, fabs(bestObj)))) continue;
                State ts = fromAsg(a);
                if (validateFull(ts).empty() && countFeasible(ts) && trueObjective(ts) > bestObj + 1e-9 * max(1.0, fabs(bestObj)))
                    bestObj = trueObjective(ts), bestAsg = a;
            }
            if (szDebug) fprintf(stderr, "teamperm end: %d tried, %.2fs, best %.6f\n", tried, elapsed() - t1, bestObj);
        }
    }
    State best = fromAsg(bestAsg);
    string err = validateFull(best);
    if (szDebug) fprintf(stderr, "trim calls=%lld wins=%lld time=%.2fs; levelBuild calls=%lld dpcut=%lld scancut=%lld\n", trimCalls, trimWins, trimTime, lvCalls, lvDpCut, lvScanCut);
    if (szDebug) fprintf(stderr, "exactPolish on=%d calls=%lld wins=%lld time=%.2fs\n", (int)epOn, epCalls, epWins, epTime);
    fprintf(stderr, "iters=%lld accepted=%lld macro=%lld best=%.6f check=%s\n", iters, accepted, macroOk, bestObj, err.empty() ? "ok" : err.c_str());
    if (!err.empty()) {  // fall back to the last validated assignment; empty only if that fails too
        State vb = fromAsg(validAsg);
        if (validateFull(vb).empty()) best = vb;
        else {
            State empty;
            initState(empty);
            best = empty;
        }
    }
    writeSolution(best, outPath);
    bool mipKilled = false;  // the MIP child was killed: the driver pipe may hold a partial model
    if (useMip && err.empty()) {
        double t0 = elapsed();
        // the MIP runs in a child process: a hard kill bounds its time even if the solver
        // overruns its own limit, and a crash there cannot hurt the answer already written
        vector<int> m;
        int fds[2];
        if (pipe(fds) == 0) {
            pid_t pid = fork();
            if (pid == 0) {
                close(fds[0]);
                mipStreamFd = fds[1];
                mipStage(fullLimit - 1);
                close(fds[1]);
                _exit(0);
            }
            close(fds[1]);
            if (pid > 0) {
                // read improvements as they come; keep the last complete one
                // HiGHS presolve (probing / clique merging) does not watch its time limit and on a busy
                // CPU runs far past it: improvements are streamed, so stop the child right at the limit
                static const double killPad = -0.2;
                double hardKill = fullLimit + killPad;
                bool late = true;
                while (true) {
                    struct pollfd pf = {fds[0], POLLIN, 0};
                    double waitLeft = hardKill - elapsed();
                    if (waitLeft <= 0) break;
                    // short slices: elapsed() may run ahead of the monotonic clock poll() waits on
                    int pr = poll(&pf, 1, (int)(min(waitLeft, 0.25) * 1000) + 1);
                    if (pr == 0) continue;
                    if (pr < 0) break;
                    int len = 0;
                    if (!readAll(fds[0], &len, sizeof len)) {  // EOF: the child finished
                        late = false;
                        break;
                    }
                    if (len != AS) break;
                    vector<int> r(len);
                    if (!readAll(fds[0], r.data(), sizeof(int) * len)) break;
                    m.swap(r);
                }
                if (late) fprintf(stderr, "mip: stopped at the hard deadline (kept %s)\n", m.empty() ? "nothing" : "the last improvement");
                mipKilled = late;
                kill(pid, SIGKILL);
                waitpid(pid, nullptr, 0);
            }
            close(fds[0]);
        }
        if (!m.empty()) {
            State mb = fromAsg(m);
            // only ever an improvement: valid, count-feasible and strictly better than the SA best
            if (validateFull(mb).empty() && countFeasible(mb) && trueObjective(mb) > bestObj + 1e-9 * max(1.0, fabs(bestObj))) {
                fprintf(stderr, "mip improved %.6f -> %.6f (%.1fs)\n", bestObj, trueObjective(mb), elapsed() - t0);
                writeSolution(mb, outPath);
            }
        }
    }
    // after a kill the driver may be blocked on a reply nobody reads: writing to it could hang;
    // exiting closes both pipes and ends the driver
    if (!mipKilled) mipFinish();
    return 0;
}
