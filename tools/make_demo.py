"""Generate the clustered 2400-site demo instance shown in the README.

Usage: python3 tools/make_demo.py > instance.json
"""
import json
import math
import random
import sys

random.seed(7)
W, H = 1000, 700
centers = [(180, 160), (420, 520), (760, 220), (850, 560),
           (300, 380), (600, 380), (130, 560), (560, 120)]

sites = []
for _ in range(2400):
    if random.random() < 0.75:
        cx, cy = random.choice(centers)
        x, y = random.gauss(cx, 70), random.gauss(cy, 60)
    else:
        x, y = random.uniform(20, W - 20), random.uniform(20, H - 20)
    x, y = min(max(x, 5), W - 5), min(max(y, 5), H - 5)
    tasks = random.sample(range(6), random.choice([0, 1, 1, 2]))
    sites.append({"x": round(x, 1), "y": round(y, 1),
                  "reward": random.randint(140, 260), "tasks": tasks})

offices = []
for i in range(14):
    if i < len(centers):
        cx, cy = centers[i]
        x, y = cx + random.uniform(-40, 40), cy + random.uniform(-40, 40)
    else:
        x, y = random.uniform(80, W - 80), random.uniform(80, H - 80)
    offices.append({"x": round(x, 1), "y": round(y, 1),
                    "cost": random.randint(3000, 6000),
                    "maxSize": random.randint(260, 420)})

workers = [random.sample(range(6), random.choice([1, 2, 2, 3])) for _ in range(60)]
distances = [[round(math.hypot(o["x"] - s["x"], o["y"] - s["y"]) * random.uniform(1.05, 1.3), 1)
              for s in sites] for o in offices]

json.dump({"sites": sites, "offices": offices, "workers": workers,
           "distances": distances, "maxDifference": 120,
           "balanceCoefficient": 2.0}, sys.stdout)
