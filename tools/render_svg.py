"""Draw instance.json + solution.json as an SVG map of the service zones.

Usage: python3 tools/render_svg.py instance.json solution.json > zones.svg
"""
import json
import sys

PALETTE = ["#4e79a7", "#f28e2b", "#e15759", "#76b7b2", "#59a14f",
           "#edc948", "#b07aa1", "#ff9da7", "#9c755f", "#6b4c9a",
           "#d37295", "#499894"]


def convex_hull(points):
    pts = sorted(set(points))
    if len(pts) < 3:
        return pts

    def cross(o, a, b):
        return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])

    lower, upper = [], []
    for p in pts:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], p) <= 0:
            lower.pop()
        lower.append(p)
    for p in reversed(pts):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], p) <= 0:
            upper.pop()
        upper.append(p)
    return lower[:-1] + upper[:-1]


def main(instance_path, solution_path):
    inst = json.load(open(instance_path))
    zones = json.load(open(solution_path))
    sites, offices = inst["sites"], inst["offices"]
    xs = [s["x"] for s in sites] + [o["x"] for o in offices]
    ys = [s["y"] for s in sites] + [o["y"] for o in offices]
    x0, x1, y0, y1 = min(xs), max(xs), min(ys), max(ys)
    pad = 20
    width, height = x1 - x0, y1 - y0

    def px(x):
        return x - x0

    def py(y):
        return y1 - y  # SVG y grows downwards

    owner = {s: zi for zi, z in enumerate(zones) for s in z["sites"]}
    opened = {z["officeId"]: zi for zi, z in enumerate(zones)}
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="{-pad} {-pad} {width + 2 * pad} '
           f'{height + 2 * pad + 40}" font-family="Helvetica,Arial,sans-serif">',
           f'<rect x="{-pad}" y="{-pad}" width="{width + 2 * pad}" height="{height + 2 * pad + 40}" '
           'fill="#ffffff"/>']

    for zi, z in enumerate(zones):
        o = offices[z["officeId"]]
        hull = convex_hull([(sites[s]["x"], sites[s]["y"]) for s in z["sites"]] + [(o["x"], o["y"])])
        color = PALETTE[zi % len(PALETTE)]
        points = " ".join(f"{px(x):.1f},{py(y):.1f}" for x, y in hull)
        out.append(f'<polygon points="{points}" fill="{color}" fill-opacity="0.16" '
                   f'stroke="{color}" stroke-width="2"/>')

    for i, s in enumerate(sites):
        color = PALETTE[owner[i] % len(PALETTE)] if i in owner else "#b8b8b8"
        out.append(f'<circle cx="{px(s["x"]):.1f}" cy="{py(s["y"]):.1f}" r="2.2" fill="{color}"/>')

    for oi, o in enumerate(offices):
        x, y = px(o["x"]), py(o["y"])
        if oi in opened:
            color = PALETTE[opened[oi] % len(PALETTE)]
            out.append(f'<rect x="{x - 8:.1f}" y="{y - 8:.1f}" width="16" height="16" '
                       f'fill="{color}" stroke="#222" stroke-width="2"/>')
        else:
            out.append(f'<rect x="{x - 7:.1f}" y="{y - 7:.1f}" width="14" height="14" fill="#fff" '
                       'stroke="#888" stroke-width="2" stroke-dasharray="3 2"/>')

    sizes = [len(z["sites"]) for z in zones]
    legend = (f'{len(sites)} sites · {len(offices)} candidate offices · {len(zones)} opened (■) · '
              f'{len(offices) - len(zones)} closed (□) · {len(owner)} sites served, grey = not served · '
              f'zone sizes {min(sizes)}–{max(sizes)} (A = {inst["maxDifference"]})')
    out.append(f'<text x="0" y="{height + pad + 22}" font-size="17" fill="#333">{legend}</text>')
    out.append('</svg>')
    print("\n".join(out))


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
