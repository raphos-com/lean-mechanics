"""Generate the SVG figures of papers/Nexorade/README.md (no dependencies).

All curves use the formulas proved in Lean (`Nexorade/Optimum.lean`):
  qShape(x)      = x^2 + (1-x)^2
  momentShape(x) = q(x) / (1-x)                 (nexor moment m / (M l))
  eulerShape(x)  = (1-x)^2 / ((3-4x) q(x))      (stiffness, shear-rigid members)
  softShape(x)   = x (1-x)^2 / q(x)             (stiffness / GS, soft members)
Run:  python3 generate.py   (from this directory)
"""
import math

STYLE = """<style>
  .bg{fill:#fcfcfb}.ink{fill:#0b0b0b}.ink2{fill:#52514e}.grid{stroke:#e4e3df}
  .axis{stroke:#8a8984}.s1{stroke:#2a78d6;fill:none}.s2{stroke:#eb6834;fill:none}
  .f1{fill:#2a78d6}.f2{fill:#eb6834}.node{fill:#fcfcfb;stroke:#0b0b0b}
  .cell{fill:none;stroke:#8a8984;stroke-dasharray:4 3}
  .fade{stroke:#b9b8b2}
  @media (prefers-color-scheme: dark){
    .bg{fill:#1a1a19}.ink{fill:#f0efec}.ink2{fill:#c3c2b7}.grid{stroke:#33322f}
    .axis{stroke:#6f6e69}.s1{stroke:#3987e5}.s2{stroke:#d95926}
    .f1{fill:#3987e5}.f2{fill:#d95926}.node{fill:#1a1a19;stroke:#f0efec}
    .fade{stroke:#4a4945}
  }
  text{font-family:-apple-system,Segoe UI,Helvetica,Arial,sans-serif}
</style>"""


def svg(w, h, body, title):
    return (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {w} {h}" width="{w}" '
            f'height="{h}" role="img" aria-label="{title}"><title>{title}</title>{STYLE}'
            f'<rect class="bg" width="{w}" height="{h}" rx="8"/>{body}</svg>\n')


def q(x): return x * x + (1 - x) ** 2
def moment(x): return q(x) / (1 - x)
def euler(x): return (1 - x) ** 2 / ((3 - 4 * x) * q(x))
def soft(x): return x * (1 - x) ** 2 / q(x)


def root():  # 2x^3 - 2x^2 + 3x - 1 = 0 on (0, 1/2), by bisection
    lo, hi = 0.0, 0.5
    for _ in range(60):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if 2*mid**3 - 2*mid**2 + 3*mid - 1 < 0 else (lo, mid)
    return lo


# ---------------------------------------------------------------- unit cell
def unit_cell(phi=math.atan(0.5), L=100.0):
    a, b = L * math.sin(phi), L * (math.cos(phi) - math.sin(phi))
    l = 2 * a + b
    p1, p2 = (a + b, -a), (a, a + b)           # lattice vectors
    W, H, ox, oy = 560, 420, 280, 210
    body, nodes = [], set()
    def P(x, y): return ox + x, oy - y
    lines = []
    for m in range(-4, 5):
        for n in range(-4, 5):
            tx, ty = m * p1[0] + n * p2[0], m * p1[1] + n * p2[1]
            h = ((tx, ty), (tx + l, ty))            # h beam
            v = ((tx + a, ty), (tx + a, ty + l))    # v beam
            lines.append((h, (m, n) == (0, 0), 'h'))
            lines.append((v, (m, n) == (0, 0), 'v'))
    def inside(pt): x, y = P(*pt); return 10 < x < W - 10 and 40 < y < H - 10
    for (s, e), main, kind in lines:
        if not (inside(s) and inside(e)):
            continue
        (x1, y1), (x2, y2) = P(*s), P(*e)
        cls = ('s1' if kind == 'h' else 's2') if main else 'fade'
        wdt = 4 if main else 2
        body.append(f'<line class="{cls}" x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" '
                    f'y2="{y2:.1f}" stroke-width="{wdt}" stroke-linecap="round"/>')
    # contact points of the unit-cell beams
    for t in (0, a, a + b, l):
        for pt in ((t, 0), (a, t)):
            x, y = P(*pt); body.append(f'<circle class="node" cx="{x:.1f}" cy="{y:.1f}" r="4" stroke-width="1.5"/>')
    # periodicity cell (parallelogram spanned by p1, p2 at the origin)
    c = [(0, 0), p1, (p1[0] + p2[0], p1[1] + p2[1]), p2]
    body.append('<polygon class="cell" stroke-width="1.5" points="' +
                ' '.join(f'{P(*pt)[0]:.1f},{P(*pt)[1]:.1f}' for pt in c) + '"/>')
    (hx, hy), (vx, vy) = P(l / 2, 0), P(a, l * 0.8)
    body.append(f'<text class="ink" x="{hx-8:.0f}" y="{hy+20:.0f}" font-size="14">h</text>')
    body.append(f'<text class="ink" x="{vx+8:.0f}" y="{vy:.0f}" font-size="14">v</text>')
    body.append('<text class="ink" x="16" y="26" font-size="15" font-weight="600">'
                'Square nexorade (φ = arctan ½): unit cell h, v and periodicity cell</text>')
    return svg(W, H, ''.join(body), 'Square nexorade pattern and unit cell')


# ---------------------------------------------------------- four-point bending
def four_point():
    W, H = 560, 300
    a, b = 1.0, 1.4
    l = 2 * a + b
    x0, x1 = 60, 520
    X = lambda s: x0 + (x1 - x0) * s / l
    body = ['<text class="ink" x="16" y="26" font-size="15" font-weight="600">'
            'Four-point bending of each nexor under the plate moment M</text>']
    # shear panel
    ys, amp = 105, 32
    body.append(f'<line class="axis" x1="{x0}" y1="{ys}" x2="{x1}" y2="{ys}" stroke-width="1"/>')
    pts = [(0, 1), (a, 1), (a, 0), (a + b, 0), (a + b, -1), (l, -1)]
    path = ' '.join(f'{"M" if i == 0 else "L"}{X(s):.1f},{ys - amp*v:.1f}' for i, (s, v) in enumerate(pts))
    body.append(f'<path class="s1" d="{path}" stroke-width="2"/>')
    body.append(f'<text class="ink2" x="{x0}" y="{ys-amp-10}" font-size="13">shear r = M / (cos φ sin φ)</text>')
    # moment panel
    ym, amp2 = 250, 60
    body.append(f'<line class="axis" x1="{x0}" y1="{ym}" x2="{x1}" y2="{ym}" stroke-width="1"/>')
    pts = [(0, 0), (a, 1), (a + b, 1), (l, 0)]
    path = ' '.join(f'{"M" if i == 0 else "L"}{X(s):.1f},{ym - amp2*v:.1f}' for i, (s, v) in enumerate(pts))
    body.append(f'<path class="s2" d="{path}" stroke-width="2"/>')
    body.append(f'<text class="ink2" x="{X(a)+6:.0f}" y="{ym-amp2-8}" font-size="13">moment m = M L / cos φ</text>')
    for s, lab in ((a / 2, 'a'), (a + b / 2, 'b'), (a + b + a / 2, 'a')):
        body.append(f'<text class="ink2" x="{X(s)-4:.0f}" y="{ym+20}" font-size="13">{lab}</text>')
    for s in (0, a, a + b, l):
        body.append(f'<circle class="node" cx="{X(s):.1f}" cy="{ym}" r="4" stroke-width="1.5"/>')
    return svg(W, H, ''.join(body), 'Shear and moment diagrams of a nexor')


# ------------------------------------------------------------------ plots
def plot(curves, ylabel, title, ymin, ymax, marks, yticks, label_pos):
    W, H = 560, 340
    L_, R, T, B = 64, 24, 68, 52
    X = lambda x: L_ + (W - L_ - R) * x / 0.5
    Y = lambda y: T + (H - T - B) * (1 - (y - ymin) / (ymax - ymin))
    body = [f'<text class="ink" x="16" y="26" font-size="15" font-weight="600">{title}</text>']
    for yt in yticks:
        body.append(f'<line class="grid" x1="{L_}" x2="{W-R}" y1="{Y(yt):.1f}" y2="{Y(yt):.1f}" stroke-width="1"/>')
        body.append(f'<text class="ink2" x="{L_-8}" y="{Y(yt)+4:.1f}" font-size="12" text-anchor="end">{yt:g}</text>')
    for xt in (0, 0.1, 0.2, 0.3, 0.4, 0.5):
        body.append(f'<text class="ink2" x="{X(xt):.1f}" y="{H-B+18}" font-size="12" text-anchor="middle">{xt:g}</text>')
    body.append(f'<line class="axis" x1="{L_}" x2="{W-R}" y1="{H-B}" y2="{H-B}" stroke-width="1"/>')
    body.append(f'<text class="ink2" x="{(L_+W-R)/2:.0f}" y="{H-12}" font-size="13" text-anchor="middle">relative engagement length a / l</text>')
    body.append(f'<text class="ink2" x="16" y="{T-10}" font-size="13">{ylabel}</text>')
    for (f, cls, fill, lab), (lx, ly) in zip(curves, label_pos):
        xs = [0.002 + i * (0.498 - 0.002) / 300 for i in range(301)]
        d = ' '.join(f'{"M" if i == 0 else "L"}{X(x):.1f},{Y(f(x)):.1f}' for i, x in enumerate(xs))
        body.append(f'<path class="{cls}" d="{d}" stroke-width="2" stroke-linejoin="round"/>')
        body.append(f'<text class="ink" x="{X(lx):.1f}" y="{Y(ly):.1f}" font-size="13">{lab}</text>')
    for x, y, fill, lab, dx, dy in marks:
        anchor = 'end' if dx < 0 else 'start' if dx > 0 else 'middle'
        body.append(f'<circle class="{fill}" cx="{X(x):.1f}" cy="{Y(y):.1f}" r="5"/>')
        body.append(f'<text class="ink" x="{X(x)+dx:.1f}" y="{Y(y)+dy:.1f}" font-size="12" text-anchor="{anchor}">{lab}</text>')
    return svg(W, H, ''.join(body), title)


def moment_plot():
    xs = 1 - math.sqrt(2) / 2
    return plot([(moment, 's2', 'f2', '')], 'm / (M l)', 'Nexor moment: minimal at a/l = 1 − √2/2',
                0.8, 1.02, [(xs, moment(xs), 'f2', f'a/l = 1 − √2/2 ≈ {xs:.3f},  m = (2√2 − 2) M l ≈ 0.828 M l', 0, 20)],
                [0.8, 0.85, 0.9, 0.95, 1.0], [(0, 0)])


def stiffness_plot():
    x0 = root()
    e = lambda x: euler(x) / euler(0.5)
    s = lambda x: soft(x) / soft(x0)
    return plot([(e, 's1', 'f1', 'shear-rigid members'), (s, 's2', 'f2', 'soft members')],
                'D / D_max', 'Plate stiffness: optimal engagement length', 0, 1.08,
                [(0.5, 1.0, 'f1', 'a/l = 0.5', -8, -10), (x0, 1.0, 'f2', f'a/l ≈ {x0:.4f}', -8, -10)],
                [0, 0.25, 0.5, 0.75, 1.0], [(0.02, 0.88), (0.2, 0.42)])


if __name__ == '__main__':
    for name, fig in (('unit-cell', unit_cell()), ('four-point-bending', four_point()),
                      ('moment', moment_plot()), ('stiffness', stiffness_plot())):
        with open(f'{name}.svg', 'w') as fh:
            fh.write(fig)
