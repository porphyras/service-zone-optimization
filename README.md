# Service Zone Optimization — TechArena 2026

A solver for the **Service Zone Optimization** track of TechArena 2026 (judged on NSUts),
written by team **Шмяндекс**. Given infrastructure sites and candidate service offices, it decides
which offices to open, which sites each office serves and which specialists work in each office.
Every zone must be convex and must not contain another zone's sites.

The solver is a single C++17 file (~14k lines). It combines a portfolio of constructive heuristics,
an exact search over zone structures for small numbers of offices, simulated annealing with
incremental convex-hull checks, and an optional MIP stage on top of HiGHS.
It runs in the judge's Docker container and uses the whole time budget: it stops at ~250 s,
against a 300 s limit.

**Highlights**

- **Every constraint is strict.** Convex, non-overlapping zones, a hard cap on the difference
  in site counts between any two zones, office capacities and skill coverage all hold in every
  answer. Each answer is checked by an independent validator inside the solver before it is written.
- **Structure search for the hard cases.** A plain local search gets stuck on one or two offices
  when the count window is tight and the imbalance penalty is huge, so the solver also enumerates
  which 2–6 offices to open. For each choice it fits a power diagram and allocates worker teams.
- **Built for unseen inputs.** It was tested on 50 to 1.3 million sites, 2 to 2000 offices and
  up to 300 skills. It was fuzzed with 171 random large inputs and stress-tested in Docker with
  1–4 CPUs and an 8 GB cap. Every phase watches the clock.
- **Measured, not guessed.** Every change went through A/B runs on a bench of instance families
  built to match the hidden tests, a regression suite and a Docker simulation of the judge.

The full write-up in Russian, with the model, every phase, the validation process and the lessons
learned: [docs/solution_ru.md](docs/solution_ru.md).

## The problem

**Input** (`instance.json`):
- sites with coordinates, a reward and a list of tasks, where each task needs one skill;
- offices with coordinates, an opening cost and a capacity `maxSize`;
- workers, each with a set of skills;
- an office × site matrix of road distances;
- the count window `A` and the imbalance weight `α`.

**Output** (`solution.json`): a list of open zones, each `{"officeId", "sites", "workers"}`.

**Maximize**

```
Σ reward(s) over assigned sites  −  Σ distance(o, s)  −  Σ cost(o) over open offices
                                 −  α · (max tasks(o) − min tasks(o))  over open offices
```

**Subject to:**

| Constraint | Rule |
|---|---|
| Sites | each site goes to at most one office |
| Capacity | an office serves at most `maxSize(o)` sites |
| Balance | the site counts of any two open offices differ by at most `A` |
| Skills | each worker goes to at most one office, and every task in a zone is covered by a skill of a worker in that office |
| Geometry | a zone, meaning its sites plus the office itself, is convex, and no site lies in the intersection of two zones |

**Scoring:** on each of 11 hidden tests the score is `our value / best value among all teams`.
Each test runs 3 times and the runs are averaged. The final score is the sum over the tests,
so 11 is the maximum.

## Approach

```
read instance ─► preprocessing: spatial grid, profits, skill masks, worker types
              ─► portfolio of starts
                   · fan / strip partitions around a centre (DP over angular order)
                   · triangulation and chord DP for offices on a ring
                   · power diagrams (weighted Voronoi) with fitted weights
                   · "simple" builder: Voronoi + greedy teams + equal-load levels
                   · best single office (exact)
              ─► structure search (small number of open offices)
                   · enumerate which offices open, fit power-diagram weights,
                     allocate worker teams; far-row and Y-partition starts
                   · large-K structure search with an exact
                     "profit at load exactly T" DP per zone
              ─► simulated annealing in forked worker processes
                   · moves: single sites, zone moves, open/close office, team changes
                   · incremental hull maintenance on a spatial grid
                   · ladder of common task levels for the α term
              ─► MIP polish (HiGHS): zone selection over a pool of candidate zones
              ─► validate ─► solution.json
```

Each answer is validated independently before it is written. If the final candidate ever failed
validation, the last answer that passed would be written instead of an empty one.

## Result

The best judge measurements reached **10.48 out of 11**, relative to the best result of any team
on each test. Most tests scored 0.99–1.00. The hardest test stayed at about 0.76 throughout.
The team did not place in the prize-winning top 3.

The final submission is the version in [`solution/`](solution).
- **Robustness:** it carries every timing fix found by fuzzing. Three hidden worst cases were
  removed, one of which took tens of minutes on a 10⁶-site ring.
- **Against its predecessor:** +5.0 % on the A/B bench at 250 s.
- **Against an older reference version, at 110 s:** +8.8 %. That run imitates a slower judge.

## Repository layout

```
solution/            exactly the package submitted to the judge
  main.cpp           the solver (C++17, no dependencies; HiGHS optional)
  Makefile           make build / make run, as the judge calls them
  build.sh           builds ./solve, then tries to link HiGHS into ./solve_mip
  run.sh             runs the best available route, nothing on stdout
  mip_driver.py      fallback MIP route through highspy over pipes
examples/tiny.json   a 3-site instance for a smoke test
docs/solution_ru.md  full write-up (Russian)
```

## Build and run

On Linux with g++ (C++17):

```sh
cd solution
make build                       # ./solve always; ./solve_mip if HiGHS can be linked
cp ../examples/tiny.json instance.json
make --silent run                # reads instance.json, writes solution.json
```

The solver can also be called directly: `./solve [time_limit_seconds] [seed]`.
It reads `instance.json` from the current directory and writes `solution.json` there.
With no arguments it uses the contest settings: about 250 s, and all available cores
(at most 8) as forked workers.

`build.sh` never fails the build. It looks for a preinstalled HiGHS in `/usr/local`, `/usr` or
`/opt`, then tries `pkg-config`, then builds HiGHS v1.15.1 from source. If none of those works,
it falls back to a Python venv with `highspy`. `run.sh` picks the best route that exists, and the
pure solver is always available as a last resort.

To submit, zip the contents of `solution/` and choose the "Docker (zip with Makefile)" language.
