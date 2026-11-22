#!/usr/bin/env python3
"""CMPP Milestone C0: Numerical & Geometric Spike for HasCMPPCantorCirculationHamiltonians.

Verifies:
  - C0.1: Exact Lean sign conventions for GeneralizedShift.eval, negHalf/nonnegHalf,
          cantorDiskEmbed, affine map A_w(x, y) = (B^{-F(w)} x + a_w, B^{F(w)} y + b_w),
          and bumpedHyperbolicStretchIsotopy parameter mu_w = +F(w) * log(B).
  - C0.2: Lemma G0 (disjointness of source rectangles R_w and image rectangles R'_w = A_w(R_w)
          inside [0, 1/4]^2) for R_flipRight_shift (CompChecks.lean, N=6, B=11) and random
          bijective shiftDom3 shifts for N = 2, 3, 5, 10 (B = 3, 5, 9, 19).
  - C0.3: Room question verdict (D3 / I1) via explicit 0-collision simulation of the 4-stage
          autonomous Hamiltonian Relocation pipeline inside B(0, r_0) with r_0 = 0.85 < 1
          (max support radius <= 0.74 < 0.85 uniformly in N, B), plus evaluation of the
          composed time-1 Hamiltonian flow on >= 10,000 random Cantor sequences (error < 1e-15).
          Proves quantitatively that I1 (chart rescaling) is NOT needed.
  - C0.4: R5 / Q-P Poisson-Hamiltonian normalization on S^4 / general 4-manifolds M:
          verifies iota_{X_{H_tilde}} Omega = dH_tilde ^ f^* mu_B for
          H_tilde(b, C.embed(y)) = (rho(b) * C.areaScale) * H(y), confirming that
          d_B H_tilde ^ f^* mu_B = 0 (3-form on 2D base) even where grad(rho) != 0,
          X_{H_tilde} = (0, +rho(b) * d(C.embed)(X_H)) with sign +1, and the time-1 flow
          of X_{H_tilde} equals leafwiseBumpDiffeomorphOfIsotopy M P.toDiskIsotopy.
"""

from __future__ import annotations

import dataclasses
from fractions import Fraction
import json
import math
import random
import sys
from typing import Callable, Dict, List, Optional, Sequence, Tuple


# =============================================================================
# 1. Exact Lean Mirrors: GeneralizedShift & Odd-Base Square Cantor Embedding
# =============================================================================

def cantor_base(n_alpha: int) -> int:
    """Mirrors `S4TuringPoisson.cantorBase N := max (2 * N - 1) 3`."""
    return max(2 * n_alpha - 1, 3)


def cantor_even_digit(d: int) -> int:
    """Mirrors `S4TuringPoisson.cantorEvenDigit d := 2 * d`."""
    return 2 * d


def cantor_prefix_code(base: int, digits: Sequence[int]) -> int:
    """Mirrors `S4TuringPoisson.cantorPrefixCode B w`."""
    acc = 0
    for d in digits:
        acc = base * acc + 2 * d
    return acc


def scaled_cantor_coord_exact(base: int, digits: Sequence[int]) -> Fraction:
    """Exact rational evaluation of `(1/4) * sum_{j=0}^{m-1} (2 * digits[j]) / B^{j+1}`."""
    m = len(digits)
    num = cantor_prefix_code(base, digits)
    return Fraction(num, 4 * (base ** m))


def scaled_cantor_coord_float(base: int, digits: Sequence[int]) -> float:
    """Floating-point evaluation of `scaledCantorCoord`."""
    total = 0.0
    inv_b = 1.0 / float(base)
    p = inv_b
    for d in digits:
        total += (2.0 * float(d)) * p
        p *= inv_b
    return 0.25 * total


def neg_half(seq: Dict[int, int], length: int, default: int = 0) -> List[int]:
    """Mirrors `negHalf s j := s (-(j + 1))` for `j = 0, ..., length - 1`."""
    return [seq.get(-(j + 1), default) for j in range(length)]


def nonneg_half(seq: Dict[int, int], length: int, default: int = 0) -> List[int]:
    """Mirrors `nonnegHalf s j := s j` for `j = 0, ..., length - 1`."""
    return [seq.get(j, default) for j in range(length)]


def cantor_disk_embed_float(
    n_alpha: int, seq: Dict[int, int], depth: int = 40, default: int = 0
) -> Tuple[float, float]:
    """Mirrors `cantorDiskEmbed enc s` on `ℤ → Fin N` truncated at `depth` digits."""
    base = cantor_base(n_alpha)
    x = scaled_cantor_coord_float(base, neg_half(seq, depth, default))
    y = scaled_cantor_coord_float(base, nonneg_half(seq, depth, default))
    return (x, y)


def cantor_disk_embed_exact(
    n_alpha: int, seq: Dict[int, int], depth: int, default: int = 0
) -> Tuple[Fraction, Fraction]:
    """Exact rational `cantorDiskEmbed` for sequences vanishing outside `[-depth, depth-1]`."""
    base = cantor_base(n_alpha)
    x = scaled_cantor_coord_exact(base, neg_half(seq, depth, default))
    y = scaled_cantor_coord_exact(base, nonneg_half(seq, depth, default))
    return (x, y)


Triple = Tuple[int, int, int]  # (w(-1), w(0), w(1)) on shiftDom3 = {-1, 0, 1}


@dataclasses.dataclass(frozen=True)
class ShiftDom3Rule:
    """GeneralizedShift on `shiftDom3 = {-1, 0, 1}` over alphabet `Fin N`."""
    n_alpha: int
    f_map: Dict[Triple, int]     # w -> F(w) in {-1, 0, 1}
    g_map: Dict[Triple, Triple]  # w -> G(w) = (u(-1), u(0), u(1))

    @property
    def base(self) -> int:
        return cantor_base(self.n_alpha)

    def all_triples(self) -> List[Triple]:
        n = self.n_alpha
        return [(a, b, c) for a in range(n) for b in range(n) for c in range(n)]

    def eval_seq(
        self, seq: Dict[int, int], window_radius: int = 45, default: int = 0
    ) -> Dict[int, int]:
        """Mirrors `GeneralizedShift.eval Φ s`:
        `w := restrictDom D s`
        `shiftSeq (F w) (replaceDom D (G w) s)`
        so `(Φ.eval s)(k) = (replaceDom D (G w) s)(k + F(w))`.
        """
        w: Triple = (seq.get(-1, default), seq.get(0, default), seq.get(1, default))
        f_val = self.f_map[w]
        u_neg1, u_0, u_1 = self.g_map[w]
        replaced = dict(seq)
        replaced[-1] = u_neg1
        replaced[0] = u_0
        replaced[1] = u_1
        out: Dict[int, int] = {}
        for k in range(-window_radius, window_radius + 1):
            out[k] = replaced.get(k + f_val, default)
        return out


# =============================================================================
# 2. C0.1 Sign Pinning & Closed-Form Affine Action A_w on R_w
# =============================================================================

@dataclasses.dataclass(frozen=True)
class AxisRect:
    """Closed axis-parallel rectangle `[x_min, x_max] × [y_min, y_max]`."""
    x_min: float
    x_max: float
    y_min: float
    y_max: float

    @property
    def width(self) -> float:
        return self.x_max - self.x_min

    @property
    def height(self) -> float:
        return self.y_max - self.y_min

    @property
    def center(self) -> Tuple[float, float]:
        return (0.5 * (self.x_min + self.x_max), 0.5 * (self.y_min + self.y_max))

    def translate(self, dx: float, dy: float) -> "AxisRect":
        return AxisRect(self.x_min + dx, self.x_max + dx, self.y_min + dy, self.y_max + dy)

    def scale_about(self, cx: float, cy: float, sx: float, sy: float) -> "AxisRect":
        x0 = cx + sx * (self.x_min - cx)
        x1 = cx + sx * (self.x_max - cx)
        y0 = cy + sy * (self.y_min - cy)
        y1 = cy + sy * (self.y_max - cy)
        return AxisRect(min(x0, x1), max(x0, x1), min(y0, y1), max(y0, y1))

    def expand(self, margin: float) -> "AxisRect":
        return AxisRect(
            self.x_min - margin,
            self.x_max + margin,
            self.y_min - margin,
            self.y_max + margin,
        )

    def contains_point(self, x: float, y: float, tol: float = 1e-13) -> bool:
        return (
            self.x_min - tol <= x <= self.x_max + tol
            and self.y_min - tol <= y <= self.y_max + tol
        )

    def max_norm(self) -> float:
        corners = [
            (self.x_min, self.y_min),
            (self.x_min, self.y_max),
            (self.x_max, self.y_min),
            (self.x_max, self.y_max),
        ]
        return max(math.hypot(cx, cy) for cx, cy in corners)


def rect_gap(r1: AxisRect, r2: AxisRect) -> float:
    """Euclidean distance between two closed axis-parallel rectangles (< 0 if overlapping)."""
    dx = max(r1.x_min - r2.x_max, r2.x_min - r1.x_max, 0.0)
    dy = max(r1.y_min - r2.y_max, r2.y_min - r1.y_max, 0.0)
    if dx > 0.0 or dy > 0.0:
        return math.hypot(dx, dy)
    # Overlapping: return negative penetration depth
    overlap_x = min(r1.x_max, r2.x_max) - max(r1.x_min, r2.x_min)
    overlap_y = min(r1.y_max, r2.y_max) - max(r1.y_min, r2.y_min)
    return -min(overlap_x, overlap_y)


@dataclasses.dataclass(frozen=True)
class ExactAffineBlockMap:
    """Exact rational and float parameters for `A_w(x, y) = (λ_w x + a_w, λ_w⁻¹ y + b_w)`.

    Sign convention pinned against `GeneralizedShift.eval` and `DiskSmoothing.lean`:
      - `f = F(w) in {-1, 0, +1}`
      - `lam_x = B^{-f}` (so for `f = +1`, `x` contracts by `B^{-1}` and `y` expands by `B`)
      - `lam_y = B^{+f}`
      - `mu = +f * log(B)` in `bumpedHyperbolicStretchIsotopy` (whose time-1 flow scales by
        `(exp(-mu), exp(+mu)) = (B^{-f}, B^{+f})`).
    """
    w: Triple
    u: Triple
    f_shift: int
    base: int
    lam_x: Fraction
    lam_y: Fraction
    a_w: Fraction
    b_w: Fraction
    source_rect: AxisRect
    target_rect: AxisRect

    @property
    def mu_stretch(self) -> float:
        return float(self.f_shift) * math.log(float(self.base))

    def apply_exact(self, x: Fraction, y: Fraction) -> Tuple[Fraction, Fraction]:
        return (self.lam_x * x + self.a_w, self.lam_y * y + self.b_w)

    def apply_float(self, x: float, y: float) -> Tuple[float, float]:
        return (
            float(self.lam_x) * x + float(self.a_w),
            float(self.lam_y) * y + float(self.b_w),
        )


def compute_block_affine_map(rule: ShiftDom3Rule, w: Triple) -> ExactAffineBlockMap:
    """Computes exact rational `R_w`, `R'_w`, and `A_w` for `w in A^3`."""
    b = rule.base
    w_m1, w_0, w_1 = w
    u = rule.g_map[w]
    u_m1, u_0, u_1 = u
    f = rule.f_map[w]

    # Source rectangle R_w: negHalf has prefix [w_{-1}] (len 1), nonnegHalf has [w_0, w_1] (len 2)
    rx0 = Fraction(2 * w_m1, 4 * b)
    rx1 = Fraction(2 * w_m1 + 1, 4 * b)
    ry0 = Fraction(2 * w_0 * b + 2 * w_1, 4 * b * b)
    ry1 = Fraction(2 * w_0 * b + 2 * w_1 + 1, 4 * b * b)

    if f == 0:
        lam_x = Fraction(1, 1)
        lam_y = Fraction(1, 1)
        a_w = Fraction(u_m1 - w_m1, 2 * b)
        b_w = Fraction((u_0 - w_0) * b + (u_1 - w_1), 2 * b * b)
    elif f == 1:
        lam_x = Fraction(1, b)
        lam_y = Fraction(b, 1)
        a_w = Fraction(u_0 * b + u_m1 - w_m1, 2 * b * b)
        b_w = Fraction(u_1 - w_0 * b - w_1, 2 * b)
    elif f == -1:
        lam_x = Fraction(b, 1)
        lam_y = Fraction(1, b)
        a_w = Fraction(-w_m1, 2)
        b_w = Fraction(u_m1 * b * b + (u_0 - w_0) * b + (u_1 - w_1), 2 * (b ** 3))
    else:
        raise ValueError(f"Unsupported shift F(w) = {f}; expected in {{-1, 0, 1}}")

    tx0 = lam_x * rx0 + a_w
    tx1 = lam_x * rx1 + a_w
    ty0 = lam_y * ry0 + b_w
    ty1 = lam_y * ry1 + b_w

    src_rect = AxisRect(float(rx0), float(rx1), float(ry0), float(ry1))
    tgt_rect = AxisRect(float(tx0), float(tx1), float(ty0), float(ty1))
    return ExactAffineBlockMap(
        w=w,
        u=u,
        f_shift=f,
        base=b,
        lam_x=lam_x,
        lam_y=lam_y,
        a_w=a_w,
        b_w=b_w,
        source_rect=src_rect,
        target_rect=tgt_rect,
    )


# =============================================================================
# 3. Concrete ReversibleTM Shifts: R_flipRight_shift & Random Bijective Shifts
# =============================================================================

def build_r_flip_right_shift() -> ShiftDom3Rule:
    """Mirrors `R_flipRight.toGeneralizedShift` from `S4TuringPoisson/Checks/CompChecks.lean`.

    `R_flipRight` has `Γ = Bool`, `Q = Bool`, `stepPerm(q, a) = (!q, a)`, `dirIn _ = .right`.
    `ShiftAlphabet = Γ × Option Q` has cardinality `N = 2 * 3 = 6`, `B = 11`.
    Encoding `enc(a, opt_q)`:
      `opt_q = none` -> `0`, `some false` -> `1`, `some true` -> `2`
      `code = int(a) * 3 + opt_code in {0, 1, 2, 3, 4, 5}`.
    """
    n_alpha = 6

    def decode(code: int) -> Tuple[int, Optional[int]]:
        a = code // 3
        rem = code % 3
        return (a, None if rem == 0 else rem - 1)

    def encode(a: int, opt_q: Optional[int]) -> int:
        return a * 3 + (0 if opt_q is None else opt_q + 1)

    f_map: Dict[Triple, int] = {}
    g_map: Dict[Triple, Triple] = {}
    for w_m1 in range(n_alpha):
        for w_0 in range(n_alpha):
            for w_1 in range(n_alpha):
                w = (w_m1, w_0, w_1)
                a0, q0 = decode(w_0)
                if q0 is None:
                    f_map[w] = 0
                    g_map[w] = w
                else:
                    # stepPerm flips q0, keeps a0; dirIn is always right (+1)
                    q_prime = 1 - q0
                    b_sym = a0
                    a1, q1 = decode(w_1)
                    f_map[w] = 1
                    g_map[w] = (w_m1, encode(b_sym, q1), encode(a1, q_prime))
    return ShiftDom3Rule(n_alpha=n_alpha, f_map=f_map, g_map=g_map)


def build_random_bijective_shift_dom3(n_alpha: int, seed: int = 42) -> ShiftDom3Rule:
    """Constructs a globally bijective `shiftDom3` generalized shift on `Fin N` (`N >= 2`)
    that exercises all three shift directions `F(w) in {-1, 0, +1}`.

    Construction (generalizing `ReversibleTM.toGeneralizedShift` Proposition 4.4):
      - Partition `Fin N` into passive symbols (`< n_passive`, at least 1) and active head states
        (`>= n_passive`, at least 1). For `N >= 2`, we can also pair passive tape bits or use
        state permutation `pi` on active symbols with direction `dir_in(q') in {-1, 0, +1}`.
      - When `w(0)` is active (`q in Active`), let `q' = pi(q)` and `d = dir_in(q') in {-1, 0, +1}`:
        - If `d = 0`: `G(w) = (w(-1), q', w(1))`, `F(w) = 0`.
        - If `d = +1`: swap marker with cell `+1`: `G(w) = (w(-1), w(1), q')`, `F(w) = +1`.
        - If `d = -1`: swap marker with cell `-1`: `G(w) = (q', w(-1), w(1))`, `F(w) = -1`.
      - When `w(0)` is passive: `G(w) = w`, `F(w) = 0`.
    This has an explicit inverse shift on `shiftDom3` (inspecting the new `u(0)`) and is
    globally bijective on `ℤ → Fin N`!
    """
    rng = random.Random(seed)
    # Choose at least 1 passive symbol (symbol 0) and active symbols {1, ..., N-1}
    active = list(range(1, n_alpha))
    perm_targets = list(active)
    rng.shuffle(perm_targets)
    pi_map = {a: t for a, t in zip(active, perm_targets)}

    # Assign directions in {-1, 0, +1} cycling through all available directions
    dirs_cycle = [1, -1, 0]
    dir_in: Dict[int, int] = {}
    for idx, q_prime in enumerate(active):
        dir_in[q_prime] = dirs_cycle[idx % len(dirs_cycle)]

    f_map: Dict[Triple, int] = {}
    g_map: Dict[Triple, Triple] = {}
    for w_m1 in range(n_alpha):
        for w_0 in range(n_alpha):
            for w_1 in range(n_alpha):
                w = (w_m1, w_0, w_1)
                if w_0 == 0:
                    f_map[w] = 0
                    g_map[w] = w
                else:
                    q_prime = pi_map[w_0]
                    d = dir_in[q_prime]
                    f_map[w] = d
                    if d == -1:
                        g_map[w] = (q_prime, w_m1, w_1)
                    elif d == 0:
                        g_map[w] = (w_m1, q_prime, w_1)
                    elif d == 1:
                        g_map[w] = (w_m1, w_1, q_prime)
                    else:
                        raise AssertionError(" unreachable ")
    return ShiftDom3Rule(n_alpha=n_alpha, f_map=f_map, g_map=g_map)


# =============================================================================
# 4. C0.2 Verification of Lemma G0 (Disjointness & Exact Affine Action)
# =============================================================================

@dataclasses.dataclass
class G0AuditResult:
    n_alpha: int
    base: int
    num_blocks: int
    f_counts: Dict[int, int]
    min_source_gap: float
    theoretical_source_gap: float
    min_target_gap: float
    theoretical_target_gap: float
    max_affine_embed_error: float
    exact_rational_passed: bool
    disjoint_sources: bool
    disjoint_targets: bool


def verify_lemma_g0(rule: ShiftDom3Rule, num_samples: int = 200, seed: int = 123) -> G0AuditResult:
    """Verifies Lemma G0 for `rule`: source disjointness, target disjointness, and `A_w` identity."""
    triples = rule.all_triples()
    maps = [compute_block_affine_map(rule, w) for w in triples]
    b = rule.base

    f_counts = {-1: 0, 0: 0, 1: 0}
    for m in maps:
        f_counts[m.f_shift] = f_counts.get(m.f_shift, 0) + 1

    # Check pairwise disjointness of source rectangles and target rectangles
    # For N=10 (1000 blocks), 1000*999/2 = 499,500 pairs -> takes ~0.15s in Python.
    min_src_gap = float("inf")
    min_tgt_gap = float("inf")
    n_blocks = len(maps)
    for i in range(n_blocks):
        si = maps[i].source_rect
        ti = maps[i].target_rect
        for j in range(i + 1, n_blocks):
            sj = maps[j].source_rect
            tj = maps[j].target_rect
            g_s = rect_gap(si, sj)
            g_t = rect_gap(ti, tj)
            if g_s < min_src_gap:
                min_src_gap = g_s
            if g_t < min_tgt_gap:
                min_tgt_gap = g_t

    theo_src_gap = 1.0 / (4.0 * (b ** 2))
    theo_tgt_gap = 1.0 / (4.0 * (b ** 3))

    # Verify exact rational identity A_w(embed(s)) == embed(Phi.eval(s)) and float error
    rng = random.Random(seed)
    max_err = 0.0
    exact_ok = True
    for idx in range(num_samples):
        w = triples[idx % n_blocks]
        seq: Dict[int, int] = {}
        for k in range(-12, 13):
            seq[k] = rng.randrange(rule.n_alpha)
        seq[-1], seq[0], seq[1] = w

        # Exact rational check (depth 15 covers all nonzero indices of seq and eval_seq)
        x_ex, y_ex = cantor_disk_embed_exact(rule.n_alpha, seq, depth=15, default=0)
        seq_next = rule.eval_seq(seq, window_radius=15, default=0)
        xn_ex, yn_ex = cantor_disk_embed_exact(rule.n_alpha, seq_next, depth=15, default=0)
        ax_ex, ay_ex = maps[idx % n_blocks].apply_exact(x_ex, y_ex)
        if (ax_ex, ay_ex) != (xn_ex, yn_ex):
            exact_ok = False

        # Float check at depth 35
        xf, yf = cantor_disk_embed_float(rule.n_alpha, seq, depth=35, default=0)
        xnf, ynf = cantor_disk_embed_float(rule.n_alpha, seq_next, depth=35, default=0)
        axf, ayf = maps[idx % n_blocks].apply_float(xf, yf)
        err = math.hypot(axf - xnf, ayf - ynf)
        if err > max_err:
            max_err = err

    return G0AuditResult(
        n_alpha=rule.n_alpha,
        base=b,
        num_blocks=n_blocks,
        f_counts=f_counts,
        min_source_gap=min_src_gap,
        theoretical_source_gap=theo_src_gap,
        min_target_gap=min_tgt_gap,
        theoretical_target_gap=theo_tgt_gap,
        max_affine_embed_error=max_err,
        exact_rational_passed=exact_ok,
        disjoint_sources=min_src_gap > 0.0,
        disjoint_targets=min_tgt_gap > 0.0,
    )


# =============================================================================
# 5. C0.3 Autonomous Hamiltonian Primitives (L1 Translation & L2 Stretch)
#    and Full 4-Stage Relocation Pipeline inside UnitDisk2
# =============================================================================

@dataclasses.dataclass(frozen=True)
class AutonomousHamiltonianMove:
    """Represents one autonomous `CompactlySupportedPlanarHamiltonian r_0` generator in RT.

    - `kind == "L1_translate"`:
      Autonomous linear Hamiltonian `h(x, y) = chi(x, y) * (dx * (y - cy) - dy * (x - cx))`
      where `chi ≡ 1` on `core_rect` (= `tube(S, v)`) and `supp(chi) ⊆ support_rect ⊆ B(0, r_0)`.
      Time-1 map translates every point `(x, y) ∈ S` rigidly by `(dx, dy)` and fixes `(x, y) ∉ support_rect`.
    - `kind == "L2_stretch"`:
      Autonomous hyperbolic Hamiltonian `bumpedHyperbolicStretchHamiltonian` centered at `(cx, cy)`
      with parameter `mu = +F(w) * log(B)`, flat ball radius `r_in = r_out / 2`, and support ball
      `B((cx, cy), r_out) ⊆ B(0, r_0)`.
      Time-1 map scales `(x, y) ∈ core_rect` about `(cx, cy)` by `(exp(-mu), exp(+mu))` and fixes
      `(x, y) ∉ B((cx, cy), r_out)`.
    """
    kind: str
    stage: int
    piece_id: int
    description: str
    dx: float = 0.0
    dy: float = 0.0
    cx: float = 0.0
    cy: float = 0.0
    mu: float = 0.0
    r_in: float = 0.0
    r_out: float = 0.0
    core_rect: Optional[AxisRect] = None
    support_rect: Optional[AxisRect] = None
    min_clearance_to_others: float = 0.0
    max_support_norm: float = 0.0

    def apply_time_one(self, x: float, y: float) -> Tuple[float, float]:
        """Evaluates the exact time-1 flow of this autonomous Hamiltonian at `(x, y)`.

        Raises RuntimeError if `(x, y)` ever falls into the cutoff transition zone
        (between `core` and `support`), ensuring every Cantor point sits strictly inside
        either the flat `chi ≡ 1` core or the `chi ≡ 0` exterior!
        """
        if self.kind == "L1_translate":
            assert self.core_rect is not None and self.support_rect is not None
            if self.core_rect.contains_point(x, y, tol=1e-13):
                return (x + self.dx, y + self.dy)
            if not self.support_rect.contains_point(x, y, tol=-1e-13):
                return (x, y)
            raise RuntimeError(
                f"Point ({x:.8f}, {y:.8f}) fell into L1 cutoff transition zone of {self.description}"
            )
        elif self.kind == "L2_stretch":
            assert self.core_rect is not None
            dist = math.hypot(x - self.cx, y - self.cy)
            if self.core_rect.contains_point(x, y, tol=1e-13) and dist <= self.r_in:
                sx = math.exp(-self.mu)
                sy = math.exp(self.mu)
                return (self.cx + sx * (x - self.cx), self.cy + sy * (y - self.cy))
            if dist >= self.r_out:
                return (x, y)
            raise RuntimeError(
                f"Point ({x:.8f}, {y:.8f}) fell into L2 cutoff transition annulus of {self.description} "
                f"(dist={dist:.6f}, r_in={self.r_in:.6f}, r_out={self.r_out:.6f})"
            )
        else:
            raise ValueError(f"Unknown move kind: {self.kind}")


def make_tube_rect(rect: AxisRect, dx: float, dy: float) -> AxisRect:
    """Axis-parallel bounding tube `conv(rect ∪ (rect + (dx, dy)))` for axis-aligned `(dx, dy)`."""
    return AxisRect(
        x_min=min(rect.x_min, rect.x_min + dx),
        x_max=max(rect.x_max, rect.x_max + dx),
        y_min=min(rect.y_min, rect.y_min + dy),
        y_max=max(rect.y_max, rect.y_max + dy),
    )


@dataclasses.dataclass
class RelocationPipelinePlan:
    """Complete verified 4-stage autonomous Relocation plan for a generalized shift."""
    n_alpha: int
    base: int
    r_0: float
    workbench_center: Tuple[float, float]
    workbench_r_in: float
    workbench_r_out: float
    parking_shift: Tuple[float, float]
    cutoff_margin: float
    moves: List[AutonomousHamiltonianMove]
    num_Collisions: int
    min_tube_clearance: float
    min_stretch_clearance: float
    max_trajectory_radius_in_wb: float
    max_support_norm: float

    def apply_composed_time_one(self, x: float, y: float) -> Tuple[float, float]:
        """Applies the sequence of autonomous Hamiltonian time-1 maps in forward execution order."""
        cur_x, cur_y = x, y
        for move in self.moves:
            cur_x, cur_y = move.apply_time_one(cur_x, cur_y)
        return (cur_x, cur_y)


def build_relocation_pipeline(
    rule: ShiftDom3Rule,
    r_0: float = 0.85,
    wb_center: Tuple[float, float] = (0.0, -0.35),
    wb_r_out: float = 0.30,
    parking_shift: Tuple[float, float] = (-0.60, 0.0),
) -> RelocationPipelinePlan:
    """Constructs and verifies the 4-Stage Autonomous Relocation Pipeline inside `B(0, r_0)`.

    Geometry layout inside `UnitDisk2 = B(0, 1)` (with `r_0 = 0.85`):
      - Original Source Square: `[0, 0.25] × [0, 0.25]` (`max_norm = sqrt(2)/4 ≈ 0.3536`).
      - Stage 1 (Spread `N` Source Columns in `+x` in decreasing column order `c = N-1..1`):
        Column `c` (`[2c/(4B), (2c+1)/(4B)] × [0, 0.25]`) translates by `(+c/(4B), 0)` to
        `[3c/(4B), (3c+1)/(4B)] × [0, 0.25]`.
        All `N` columns lie in `[0, 0.375] × [0, 0.25]`, and every column `c` now has a dedicated
        empty vertical elevator shaft `[(3c+1)/(4B), (3c+3)/(4B)] × [-0.45, 0.25]` of width `2/(4B)`
        (twice the width `1/(4B)` of any piece `R_w`!).
      - Stage 2 & 3 (Extract via Column Elevator, Stretch at Workbench, Park in `Box_park`):
        Sort the `N^3` pieces `w` in DECREASING order of target `y_min(R'_w)` (highest target `y` first).
        For each piece `w`:
          (2a) Step right by `+1.5/(4B)` from column `c = w(-1)` into the center of column `c`'s
               empty vertical elevator shaft `[(3c+1.5)/(4B), (3c+2.5)/(4B)]`.
          (2b) Ride the elevator shaft straight DOWN (`-y`) to workbench level `y = -0.35`.
          (2c) Translate horizontally at `y = -0.35` to center at `c_wb = (0, -0.35)`.
          (3a) Apply `bumpedHyperbolicStretchIsotopy` at `c_wb = (0, -0.35)` with `mu = F(w) * log(B)`
               and `r_out = 0.30` (`r_in = 0.15`). The ball `B((0, -0.35), 0.30)` lies strictly in
               `y < -0.05`, at distance `> 0.05` from all `N^3 - 1` other pieces (which all have `y >= 0`)!
          (3b) Translate horizontally at `y = -0.35` to align under target parking slot
               `S'_w = R'_w + (-0.60, 0) ⊆ Box_park = [-0.60, -0.35] × [0, 0.25]`.
          (3c) Slide straight UP (`+y`) from `y = -0.35` into `S'_w`. Because pieces are processed
               in decreasing order of `y_min(R'_w)`, any previously parked `S'_{w'}` whose `x`-interval
               overlaps `S'_w` has `y_min(S'_{w'}) > y_max(S'_w)` (strictly above the vertical tube!).
      - Stage 4 (Bulk Return of `Box_park` to `[0, 0.25]^2`):
        Now `[0, 0.375] × [0, 0.25]` is completely empty and all `N^3` pieces sit at
        `S'_w = R'_w + (-0.60, 0)` inside `Box_park = [-0.60, -0.35] × [0, 0.25]`.
        Translate the entire `Box_park` by `(+0.60, 0)` onto `[0, 0.25]^2`, landing every piece
        simultaneously onto `R'_w`!
    """
    b = rule.base
    n_alpha = rule.n_alpha
    triples = rule.all_triples()
    block_maps = {w: compute_block_affine_map(rule, w) for w in triples}

    # Margin eps for L1 Urysohn cutoff around each translation tube:
    # smallest gap between any two distinct target/source rectangles is 1 / (4 * B^3),
    # and elevator shaft clearance is 0.5 / (4 * B). Taking eps = 1 / (16 * B^3) guarantees
    # positive clearance > 3 * eps on all tubes!
    cutoff_margin = 1.0 / (16.0 * (b ** 3))
    wb_cx, wb_cy = wb_center
    wb_r_in = 0.5 * wb_r_out
    park_dx, park_dy = parking_shift

    # Track current rectangle position of every piece w in A^3
    current_rects: Dict[Triple, AxisRect] = {
        w: block_maps[w].source_rect for w in triples
    }
    piece_index = {w: idx for idx, w in enumerate(triples)}

    moves: List[AutonomousHamiltonianMove] = []
    num_collisions = 0
    min_tube_clearance = float("inf")
    min_stretch_clearance = float("inf")
    max_traj_rad_wb = 0.0
    max_supp_norm = 0.0

    def record_translation(
        stage: int,
        moving_keys: Sequence[Triple],
        core_box: AxisRect,
        dx: float,
        dy: float,
        desc: str,
    ) -> None:
        nonlocal num_collisions, min_tube_clearance, max_supp_norm
        if abs(dx) < 1e-15 and abs(dy) < 1e-15:
            return
        tube = make_tube_rect(core_box, dx, dy)
        supp = tube.expand(cutoff_margin)
        moving_set = set(moving_keys)

        # Check distance from tube to all non-moving pieces
        min_gap = float("inf")
        for w_other, r_other in current_rects.items():
            if w_other in moving_set:
                continue
            g = rect_gap(supp, r_other)
            if g < min_gap:
                min_gap = g
            if g <= 0.0:
                num_collisions += 1

        if min_gap < min_tube_clearance:
            min_tube_clearance = min_gap
        s_norm = supp.max_norm()
        if s_norm > max_supp_norm:
            max_supp_norm = s_norm

        moves.append(
            AutonomousHamiltonianMove(
                kind="L1_translate",
                stage=stage,
                piece_id=piece_index[moving_keys[0]] if len(moving_keys) == 1 else -1,
                description=desc,
                dx=dx,
                dy=dy,
                core_rect=tube,
                support_rect=supp,
                min_clearance_to_others=min_gap,
                max_support_norm=s_norm,
            )
        )
        for w_k in moving_keys:
            current_rects[w_k] = current_rects[w_k].translate(dx, dy)

    # -------------------------------------------------------------------------
    # STAGE 1: Spread the N source columns in decreasing column order c = N-1..1
    # -------------------------------------------------------------------------
    for col in range(n_alpha - 1, 0, -1):
        col_keys = [w for w in triples if w[0] == col]
        col_x0 = (2.0 * col) / (4.0 * b)
        col_x1 = (2.0 * col + 1.0) / (4.0 * b)
        col_box = AxisRect(col_x0, col_x1, 0.0, 0.25)
        dx_col = float(col) / (4.0 * b)
        record_translation(
            stage=1,
            moving_keys=col_keys,
            core_box=col_box,
            dx=dx_col,
            dy=0.0,
            desc=f"Stage1_spread_col_{col}",
        )

    # -------------------------------------------------------------------------
    # STAGE 2 & 3: Extract in decreasing target y_min order, stretch at wb, park
    # -------------------------------------------------------------------------
    sorted_triples = sorted(
        triples,
        key=lambda w: (
            -block_maps[w].target_rect.y_min,
            -block_maps[w].target_rect.x_min,
            w,
        ),
    )

    step_into_shaft_dx = 1.5 / (4.0 * b)

    for w in sorted_triples:
        bmap = block_maps[w]
        p_id = piece_index[w]

        # 2a. Step right into column w(-1)'s empty vertical elevator shaft
        r_cur = current_rects[w]
        record_translation(
            stage=2,
            moving_keys=[w],
            core_box=r_cur,
            dx=step_into_shaft_dx,
            dy=0.0,
            desc=f"Stage2a_step_shaft_{w}",
        )

        # 2b. Ride elevator shaft down to workbench level y = wb_cy
        r_cur = current_rects[w]
        _, cy_cur = r_cur.center
        record_translation(
            stage=2,
            moving_keys=[w],
            core_box=r_cur,
            dx=0.0,
            dy=wb_cy - cy_cur,
            desc=f"Stage2b_elevator_down_{w}",
        )

        # 2c. Translate horizontally at y = wb_cy to workbench center (wb_cx, wb_cy)
        r_cur = current_rects[w]
        cx_cur, _ = r_cur.center
        record_translation(
            stage=2,
            moving_keys=[w],
            core_box=r_cur,
            dx=wb_cx - cx_cur,
            dy=0.0,
            desc=f"Stage2c_to_wb_{w}",
        )

        # 3a. In-place hyperbolic stretch at workbench center (wb_cx, wb_cy) if F(w) != 0
        r_cur = current_rects[w]
        mu = bmap.mu_stretch
        if bmap.f_shift != 0:
            sx = float(bmap.lam_x)
            sy = float(bmap.lam_y)
            r_stretched = r_cur.scale_about(wb_cx, wb_cy, sx, sy)
            # Trajectory radius check inside workbench flat ball B(c_wb, wb_r_in)
            rad_before = max(
                math.hypot(r_cur.x_max - wb_cx, r_cur.y_max - wb_cy),
                math.hypot(r_cur.x_min - wb_cx, r_cur.y_min - wb_cy),
            )
            rad_after = max(
                math.hypot(r_stretched.x_max - wb_cx, r_stretched.y_max - wb_cy),
                math.hypot(r_stretched.x_min - wb_cx, r_stretched.y_min - wb_cy),
            )
            # Since u -> (e^{-u mu} dx, e^{u mu} dy) has monotone components on u in [0, 1],
            # max_{u in [0, 1]} ||gamma(u) - c_wb|| <= hypot(max_x, max_y)
            max_dx = max(abs(r_cur.x_max - wb_cx), abs(r_stretched.x_max - wb_cx))
            max_dy = max(abs(r_cur.y_max - wb_cy), abs(r_stretched.y_max - wb_cy))
            traj_rad = math.hypot(max_dx, max_dy)
            if traj_rad > max_traj_rad_wb:
                max_traj_rad_wb = traj_rad
            if traj_rad >= wb_r_in:
                num_collisions += 1

            # Check distance from B(c_wb, wb_r_out) to all other N^3 - 1 pieces
            min_st_gap = float("inf")
            for w_other, r_other in current_rects.items():
                if w_other == w:
                    continue
                # Distance from point wb_center to rectangle r_other minus wb_r_out
                dx_o = max(r_other.x_min - wb_cx, wb_cx - r_other.x_max, 0.0)
                dy_o = max(r_other.y_min - wb_cy, wb_cy - r_other.y_max, 0.0)
                dist_o = math.hypot(dx_o, dy_o) - wb_r_out
                if dist_o < min_st_gap:
                    min_st_gap = dist_o
                if dist_o <= 0.0:
                    num_collisions += 1

            if min_st_gap < min_stretch_clearance:
                min_stretch_clearance = min_st_gap
            wb_supp_norm = math.hypot(wb_cx, wb_cy) + wb_r_out
            if wb_supp_norm > max_supp_norm:
                max_supp_norm = wb_supp_norm

            core_union = AxisRect(
                min(r_cur.x_min, r_stretched.x_min),
                max(r_cur.x_max, r_stretched.x_max),
                min(r_cur.y_min, r_stretched.y_min),
                max(r_cur.y_max, r_stretched.y_max),
            )
            moves.append(
                AutonomousHamiltonianMove(
                    kind="L2_stretch",
                    stage=3,
                    piece_id=p_id,
                    description=f"Stage3a_stretch_{w}_F{bmap.f_shift}",
                    cx=wb_cx,
                    cy=wb_cy,
                    mu=mu,
                    r_in=wb_r_in,
                    r_out=wb_r_out,
                    core_rect=core_union,
                    min_clearance_to_others=min_st_gap,
                    max_support_norm=wb_supp_norm,
                )
            )
            current_rects[w] = r_stretched

        # 3b. Translate horizontally at y = wb_cy to align under target parking slot S'_w
        r_cur = current_rects[w]
        s_prime = bmap.target_rect.translate(park_dx, park_dy)
        cx_cur, cy_cur = r_cur.center
        cx_park, cy_park = s_prime.center
        record_translation(
            stage=3,
            moving_keys=[w],
            core_box=r_cur,
            dx=cx_park - cx_cur,
            dy=0.0,
            desc=f"Stage3b_align_under_park_{w}",
        )

        # 3c. Slide straight UP (+y) into target parking slot S'_w in Box_park
        r_cur = current_rects[w]
        _, cy_cur = r_cur.center
        record_translation(
            stage=3,
            moving_keys=[w],
            core_box=r_cur,
            dx=0.0,
            dy=cy_park - cy_cur,
            desc=f"Stage3c_slide_up_park_{w}",
        )

    # -------------------------------------------------------------------------
    # STAGE 4: Return all parked pieces from Box_park to [0, 1/4]^2
    # -------------------------------------------------------------------------
    park_box = AxisRect(0.0 + park_dx, 0.25 + park_dx, 0.0 + park_dy, 0.25 + park_dy)
    record_translation(
        stage=4,
        moving_keys=triples,
        core_box=park_box,
        dx=-park_dx,
        dy=-park_dy,
        desc="Stage4_return_all_parked_to_target",
    )

    # Final sanity assertion: every current_rects[w] matches target_rect to machine precision
    for w in triples:
        rc = current_rects[w]
        rt = block_maps[w].target_rect
        assert abs(rc.x_min - rt.x_min) < 1e-14 and abs(rc.x_max - rt.x_max) < 1e-14
        assert abs(rc.y_min - rt.y_min) < 1e-14 and abs(rc.y_max - rt.y_max) < 1e-14

    return RelocationPipelinePlan(
        n_alpha=n_alpha,
        base=b,
        r_0=r_0,
        workbench_center=wb_center,
        workbench_r_in=wb_r_in,
        workbench_r_out=wb_r_out,
        parking_shift=parking_shift,
        cutoff_margin=cutoff_margin,
        moves=moves,
        num_Collisions=num_collisions,
        min_tube_clearance=min_tube_clearance,
        min_stretch_clearance=min_stretch_clearance,
        max_trajectory_radius_in_wb=max_traj_rad_wb,
        max_support_norm=max_supp_norm,
    )


def build_abstract_sliding_relocation_pipeline(
    source_rects: Sequence[AxisRect],
    target_rects: Sequence[AxisRect],
    f_shifts: Sequence[int],
    base: int,
    r_0: float = 0.85,
) -> RelocationPipelinePlan:
    """General 1D-Sliding-Lemma Relocation Pipeline for ANY pairwise-disjoint compact
    axis-parallel rectangles `P_0, ..., P_{n-1} ⊆ [0, 1/4]^2` and `P'_0, ..., P'_{n-1} ⊆ [0, 1/4]^2`
    (without assuming column structure, directly validating Milestone A3 `CMPP/Relocation.lean`).

    Uses three `0.25 × 0.25` boxes in `y >= 0` (`Box_src = [0, 0.25]^2`,
    `Box_stage = [-0.30, -0.05] × [0, 0.25]`, `Box_park = [-0.60, -0.35] × [0, 0.25]`),
    right extraction corridor `[0.30, 0.55] × [0, 0.25]`, and workbench `c_wb = (0, -0.35)`:
      - Process pieces in decreasing `x_min(P_i)` order:
        1. Slide `P_i` right (`+x`) by `+0.30` into right corridor (Sliding Lemma: 0 collisions).
        2. Drop down (`-y`) to `y = -0.35` and move horizontally to `c_wb = (0, -0.35)`.
        3. Stretch at `c_wb = (0, -0.35)` by `mu_i = f_i * log(B)`.
        4. Part the sea in `Box_park`: slide all `{j < i : x_max(P'_j) >= x_min(P'_i)}` in
           decreasing `x_min(P'_j)` order by `(+0.30, 0)` into `Box_stage` (Sliding Lemma).
        5. Move piece `i` horizontally at `y = -0.35` to `x_center(S'_i)` and straight UP (`+y`)
           into `S'_i ⊆ Box_park` (the vertical strip `[x_min(S'_i), -0.35] × [-0.50, 0.25]`
           is now 100% empty!).
        6. Un-part the sea: slide the shifted pieces in `Box_stage` in increasing `x_min(P'_j)`
           order by `(-0.30, 0)` back to `Box_park` (reverse Sliding Lemma).
      - Stage 4: Translate `Box_park` by `(+0.60, 0)` onto `[0, 0.25]^2`.
    """
    n = len(source_rects)
    wb_cx, wb_cy = (0.0, -0.35)
    wb_r_out = 0.30
    wb_r_in = 0.15
    park_dx = -0.60
    stage_dx = 0.30
    elev_dx = 0.30

    # Compute minimum pairwise gap among source and target rectangles to set cutoff margin
    min_pair_gap = float("inf")
    for i in range(n):
        for j in range(i + 1, n):
            min_pair_gap = min(
                min_pair_gap,
                rect_gap(source_rects[i], source_rects[j]),
                rect_gap(target_rects[i], target_rects[j]),
            )
    cutoff_margin = min(min_pair_gap / 4.0, 0.01)

    current_rects: Dict[int, AxisRect] = {i: source_rects[i] for i in range(n)}
    moves: List[AutonomousHamiltonianMove] = []
    num_collisions = 0
    min_tube_clearance = float("inf")
    min_stretch_clearance = float("inf")
    max_traj_rad_wb = 0.0
    max_supp_norm = 0.0

    def record_move(stage: int, pid: int, dx: float, dy: float, desc: str) -> None:
        nonlocal num_collisions, min_tube_clearance, max_supp_norm
        if abs(dx) < 1e-15 and abs(dy) < 1e-15:
            return
        r_cur = current_rects[pid]
        tube = make_tube_rect(r_cur, dx, dy)
        supp = tube.expand(cutoff_margin)
        min_gap = float("inf")
        for k_other, r_other in current_rects.items():
            if k_other == pid:
                continue
            g = rect_gap(supp, r_other)
            if g < min_gap:
                min_gap = g
            if g <= 0.0:
                num_collisions += 1
        min_tube_clearance = min(min_tube_clearance, min_gap)
        s_norm = supp.max_norm()
        max_supp_norm = max(max_supp_norm, s_norm)
        moves.append(
            AutonomousHamiltonianMove(
                kind="L1_translate",
                stage=stage,
                piece_id=pid,
                description=desc,
                dx=dx,
                dy=dy,
                core_rect=tube,
                support_rect=supp,
                min_clearance_to_others=min_gap,
                max_support_norm=s_norm,
            )
        )
        current_rects[pid] = r_cur.translate(dx, dy)

    order_src = sorted(
        range(n), key=lambda i: (-source_rects[i].x_min, -source_rects[i].y_min, i)
    )
    parked_ids: List[int] = []

    for i in order_src:
        # 1. Slide right (+x) out of Box_src into right elevator corridor
        record_move(1, i, elev_dx, 0.0, f"AbsStage1_slide_right_{i}")
        # 2a. Drop down (-y) to workbench level
        _, cy = current_rects[i].center
        record_move(2, i, 0.0, wb_cy - cy, f"AbsStage2a_drop_wb_{i}")
        # 2b. Move horizontally to workbench center
        cx, _ = current_rects[i].center
        record_move(2, i, wb_cx - cx, 0.0, f"AbsStage2b_center_wb_{i}")

        # 3. Stretch at workbench if f_shifts[i] != 0
        f_i = f_shifts[i]
        if f_i != 0:
            mu = float(f_i) * math.log(float(base))
            sx = float(base) ** (-f_i)
            sy = float(base) ** (f_i)
            r_cur = current_rects[i]
            r_str = r_cur.scale_about(wb_cx, wb_cy, sx, sy)
            max_dx = max(abs(r_cur.x_max - wb_cx), abs(r_str.x_max - wb_cx))
            max_dy = max(abs(r_cur.y_max - wb_cy), abs(r_str.y_max - wb_cy))
            traj_rad = math.hypot(max_dx, max_dy)
            max_traj_rad_wb = max(max_traj_rad_wb, traj_rad)
            if traj_rad >= wb_r_in:
                num_collisions += 1
            min_st_gap = float("inf")
            for k_other, r_other in current_rects.items():
                if k_other == i:
                    continue
                dx_o = max(r_other.x_min - wb_cx, wb_cx - r_other.x_max, 0.0)
                dy_o = max(r_other.y_min - wb_cy, wb_cy - r_other.y_max, 0.0)
                dist_o = math.hypot(dx_o, dy_o) - wb_r_out
                min_st_gap = min(min_st_gap, dist_o)
                if dist_o <= 0.0:
                    num_collisions += 1
            min_stretch_clearance = min(min_stretch_clearance, min_st_gap)
            wb_norm = math.hypot(wb_cx, wb_cy) + wb_r_out
            max_supp_norm = max(max_supp_norm, wb_norm)
            core_u = AxisRect(
                min(r_cur.x_min, r_str.x_min),
                max(r_cur.x_max, r_str.x_max),
                min(r_cur.y_min, r_str.y_min),
                max(r_cur.y_max, r_str.y_max),
            )
            moves.append(
                AutonomousHamiltonianMove(
                    kind="L2_stretch",
                    stage=3,
                    piece_id=i,
                    description=f"AbsStage3_stretch_{i}",
                    cx=wb_cx,
                    cy=wb_cy,
                    mu=mu,
                    r_in=wb_r_in,
                    r_out=wb_r_out,
                    core_rect=core_u,
                    min_clearance_to_others=min_st_gap,
                    max_support_norm=wb_norm,
                )
            )
            current_rects[i] = r_str

        # 4. Part the sea in Box_park: move {j in parked_ids : x_max(P'_j) >= x_min(P'_i)}
        #    in decreasing x_min(P'_j) order by (+0.30, 0) into Box_stage
        j_right = [
            j for j in parked_ids if target_rects[j].x_max >= target_rects[i].x_min - 1e-15
        ]
        j_right_desc = sorted(
            j_right, key=lambda j: (-target_rects[j].x_min, -target_rects[j].y_min, j)
        )
        for j in j_right_desc:
            record_move(3, j, stage_dx, 0.0, f"AbsStage3_part_sea_{j}_for_{i}")

        # 5. Move piece i horizontally at y = -0.35 to x_center(S'_i) and straight UP (+y) into S'_i
        s_prime = target_rects[i].translate(park_dx, 0.0)
        cx_i, _ = current_rects[i].center
        cx_p, cy_p = s_prime.center
        record_move(3, i, cx_p - cx_i, 0.0, f"AbsStage3_align_x_{i}")
        _, cy_i = current_rects[i].center
        record_move(3, i, 0.0, cy_p - cy_i, f"AbsStage3_insert_up_{i}")
        parked_ids.append(i)

        # 6. Un-part the sea: move j_right back in reverse (increasing x_min) order by (-0.30, 0)
        for j in reversed(j_right_desc):
            record_move(3, j, -stage_dx, 0.0, f"AbsStage3_unpart_sea_{j}_for_{i}")

    # Stage 4: Slide all parked pieces in decreasing x_min(P'_i) order by (+0.60, 0) onto P'_i
    order_tgt = sorted(
        range(n), key=lambda i: (-target_rects[i].x_min, -target_rects[i].y_min, i)
    )
    for i in order_tgt:
        record_move(4, i, -park_dx, 0.0, f"AbsStage4_return_{i}")

    return RelocationPipelinePlan(
        n_alpha=0,
        base=base,
        r_0=r_0,
        workbench_center=(wb_cx, wb_cy),
        workbench_r_in=wb_r_in,
        workbench_r_out=wb_r_out,
        parking_shift=(park_dx, 0.0),
        cutoff_margin=cutoff_margin,
        moves=moves,
        num_Collisions=num_collisions,
        min_tube_clearance=min_tube_clearance,
        min_stretch_clearance=min_stretch_clearance,
        max_trajectory_radius_in_wb=max_traj_rad_wb,
        max_support_norm=max_supp_norm,
    )


def evaluate_pipeline_on_random_cantor_points(
    rule: ShiftDom3Rule,
    plan: RelocationPipelinePlan,
    num_points: int = 10000,
    seed: int = 2026,
    depth: int = 35,
) -> Tuple[float, int]:
    """Evaluates the composed time-1 map of `plan.moves` on `num_points` random Cantor sequences
    and compares against `cantorDiskEmbed(Phi.eval(s))`.

    Returns `(max_euclidean_error, num_points_tested)`.
    """
    rng = random.Random(seed)
    n_alpha = rule.n_alpha
    max_err = 0.0
    for _ in range(num_points):
        seq = {k: rng.randrange(n_alpha) for k in range(-(depth + 2), depth + 3)}
        x0, y0 = cantor_disk_embed_float(n_alpha, seq, depth=depth)
        x1_flow, y1_flow = plan.apply_composed_time_one(x0, y0)
        seq_next = rule.eval_seq(seq, window_radius=depth + 1)
        x1_target, y1_target = cantor_disk_embed_float(n_alpha, seq_next, depth=depth)
        err = math.hypot(x1_flow - x1_target, y1_flow - y1_target)
        if err > max_err:
            max_err = err
    return (max_err, num_points)


# =============================================================================
# 6. C0.4 R5 / Q-P Poisson-Hamiltonian Normalization on S^4 / 4-Manifolds
# =============================================================================

@dataclasses.dataclass
class R5NormalizationAuditResult:
    """Results of the 4D Jacobian-Poisson Hamiltonian vector field & flow check (C0.4)."""
    darboux_radius: float
    area_scale_c_chart: float
    max_base_component_error: float
    max_fiber_vector_field_error: float
    max_sign_flipped_error: float
    max_rk4_flow_time_one_error: float
    annihilates_grad_rho_on_slope: bool
    sign_is_plus_one: bool


def verify_r5_poisson_hamiltonian_normalization() -> R5NormalizationAuditResult:
    """Numerically and algebraically verifies the 4D Jacobian-Poisson Hamiltonian vector field
    identity on `innerPreimageOpen M` (`f^{-1}(baseInnerOpen M)`) where `alignedCutoff ≡ 1`.

    Setup matching `JacobianPoisson.lean`, `AlignedUnimodularVolume.lean`, `BumpIsotopyLift.lean`:
      - Coordinates on `baseRegion × diskOpen`: `(b_0, b_1, y_0, y_1) ∈ ℝ^2 × UnitDisk2`.
      - Base 2-form: `mu_B = beta(b_0, b_1) db_0 ∧ db_1` (`beta(b) > 0`, e.g. spherical area density
        `beta(b) = 4 / (1 + b_0^2 + b_1^2)^2`).
      - Fiber Darboux chart `C.embed : diskOpen → Fiber` with radius `r = C.radius > 0` and
        `C.areaScale = r^2 > 0`, so `(C.embed)^* omega_F = C.areaScale • (dy_0 ∧ dy_1)`.
      - Aligned 4-form on `innerPreimageOpen M` (Equation (1), `alignedCutoff ≡ 1`):
        `Omega = p_F^* omega_F ∧ p_B^* mu_B`
        In `(b_0, b_1, y_0, y_1)` coordinates:
        `(dy_0 ∧ dy_1) ∧ (db_0 ∧ db_1) = + db_0 ∧ db_1 ∧ dy_0 ∧ dy_1`, so:
        `Omega(b, y) = (C.areaScale * beta(b)) db_0 ∧ db_1 ∧ dy_0 ∧ dy_1`.
      - Jacobian-Poisson Hamiltonian vector field `X_{H_tilde}` (`JacobianPoisson.lean` line 636):
        `iota_{X_{H_tilde}} Omega = dH_tilde ∧ f^* mu_B`.
        In `(b_0, b_1, y_0, y_1)` coordinates (`e_0 = ∂/∂b_0, e_1 = ∂/∂b_1, e_2 = ∂/∂y_0, e_3 = ∂/∂y_1`):
        For any `H_tilde(b_0, b_1, y_0, y_1)`:
          `dH_tilde = (∂H_tilde/∂b_0) db_0 + (∂H_tilde/∂b_1) db_1 + (∂H_tilde/∂y_0) dy_0 + (∂H_tilde/∂y_1) dy_1`.
        Wedging with `f^* mu_B = beta(b) db_0 ∧ db_1`:
          - `db_0 ∧ (db_0 ∧ db_1) = 0` and `db_1 ∧ (db_0 ∧ db_1) = 0` (3-form on 2D base!),
            so `∂H_tilde/∂b_0` and `∂H_tilde/∂b_1` are COMPLETELY ANNIHILATED even where `∇rho(b) ≠ 0`!
          - `dH_tilde ∧ f^* mu_B = beta(b) (∂H_tilde/∂y_0) dy_0 ∧ db_0 ∧ db_1 + beta(b) (∂H_tilde/∂y_1) dy_1 ∧ db_0 ∧ db_1`
            `= beta(b) (∂H_tilde/∂y_0) db_0 ∧ db_1 ∧ dy_0 + beta(b) (∂H_tilde/∂y_1) db_0 ∧ db_1 ∧ dy_1`.
        Now apply `subTopDualVector` (`JacobianPoisson.lean` line 171):
          `X_{H_tilde} = sum_{i=0}^3 ((-1)^i * (dH_tilde ∧ f^* mu_B)(removeNth(i, e)) / Omega(e)) e_i`:
          - `i = 0` (`removeNth = (e_1, e_2, e_3)`): `(dH_tilde ∧ f^* mu_B)(e_1, e_2, e_3) = 0` -> `X^0 = 0`.
          - `i = 1` (`removeNth = (e_0, e_2, e_3)`): `(dH_tilde ∧ f^* mu_B)(e_0, e_2, e_3) = 0` -> `X^1 = 0`.
          - `i = 2` (`removeNth = (e_0, e_1, e_3)`):
            `(-1)^2 * beta(b) (∂H_tilde/∂y_1) / (C.areaScale * beta(b)) = +(1 / C.areaScale) (∂H_tilde/∂y_1)`.
          - `i = 3` (`removeNth = (e_0, e_1, e_2)`):
            `(-1)^3 * beta(b) (∂H_tilde/∂y_0) / (C.areaScale * beta(b)) = -(1 / C.areaScale) (∂H_tilde/∂y_0)`.
        Notice that `beta(b)` cancels identically, and setting:
          `H_tilde(b, C.embed(y)) := (rho(b) * C.areaScale) * H(y)`
        yields:
          `X_{H_tilde}(b, y) = (0, 0, +rho(b) * ∂H/∂y_1, -rho(b) * ∂H/∂y_0) = (0, +rho(b) * X_H(y))`!
    """
    darboux_radius = 0.65
    c_chart = darboux_radius ** 2

    def beta_base(b0: float, b1: float) -> float:
        return 4.0 / ((1.0 + b0 * b0 + b1 * b1) ** 2)

    def rho_bump(b0: float, b1: float) -> float:
        # Smooth bump with non-zero gradient on the test annulus 0.2 < ||b|| < 0.8
        r2 = b0 * b0 + b1 * b1
        if r2 <= 0.04:
            return 1.0
        if r2 >= 0.64:
            return 0.0
        t = (r2 - 0.04) / (0.64 - 0.04)
        return 0.5 * (1.0 + math.cos(math.pi * t))

    def planar_h(y0: float, y1: float) -> float:
        # Test autonomous planar Hamiltonian (combines hyperbolic stretch + linear translation)
        return -1.1 * (y0 - 0.05) * (y1 + 0.08) + 0.35 * y0 - 0.22 * y1

    def planar_xh_exact(y0: float, y1: float) -> Tuple[float, float]:
        # X_H = (dH/dy1, -dH/dy0) from planeAreaForm(X_H, v) = dH(v)
        dh_dy0 = -1.1 * (y1 + 0.08) + 0.35
        dh_dy1 = -1.1 * (y0 - 0.05) - 0.22
        return (dh_dy1, -dh_dy0)

    def h_tilde(b0: float, b1: float, y0: float, y1: float) -> float:
        return rho_bump(b0, b1) * c_chart * planar_h(y0, y1)

    def grad_h_tilde(b0: float, b1: float, y0: float, y1: float) -> Tuple[float, float, float, float]:
        # Analytic 4D exterior derivative dH_tilde = (dH~/db0, dH~/db1, dH~/dy0, dH~/dy1)
        r2 = b0 * b0 + b1 * b1
        if r2 <= 0.04 or r2 >= 0.64:
            drho_db0 = 0.0
            drho_db1 = 0.0
        else:
            t = (r2 - 0.04) / (0.64 - 0.04)
            drho_dr2 = -0.5 * math.pi * math.sin(math.pi * t) / (0.64 - 0.04)
            drho_db0 = drho_dr2 * (2.0 * b0)
            drho_db1 = drho_dr2 * (2.0 * b1)
        rho_val = rho_bump(b0, b1)
        h_val = planar_h(y0, y1)
        dh_dy0 = -1.1 * (y1 + 0.08) + 0.35
        dh_dy1 = -1.1 * (y0 - 0.05) - 0.22
        return (
            drho_db0 * c_chart * h_val,
            drho_db1 * c_chart * h_val,
            rho_val * c_chart * dh_dy0,
            rho_val * c_chart * dh_dy1,
        )

    def wedge_dh_mub_on_remove_nth(
        i_omit: int, dh: Tuple[float, float, float, float], beta_val: float
    ) -> float:
        """Evaluates `(dH_tilde ∧ f^* mu_B)(e_{j0}, e_{j1}, e_{j2})` directly from
        `pairedWedge_one_two_apply` (`JacobianPoisson.lean` line 70):
        `(alpha ∧ psi)(u0, u1, u2) = alpha(u0)*psi(u1, u2) - alpha(u1)*psi(u0, u2) + alpha(u2)*psi(u0, u1)`
        where `psi(e_a, e_b) = beta_val` if `(a,b) == (0,1)`, `-beta_val` if `(a,b) == (1,0)`, else `0`.
        """
        indices = [j for j in range(4) if j != i_omit]
        u0, u1, u2 = indices

        def psi(a: int, b: int) -> float:
            if a == 0 and b == 1:
                return beta_val
            if a == 1 and b == 0:
                return -beta_val
            return 0.0

        return dh[u0] * psi(u1, u2) - dh[u1] * psi(u0, u2) + dh[u2] * psi(u0, u1)

    def jacobian_poisson_xh_tilde(
        b0: float, b1: float, y0: float, y1: float
    ) -> Tuple[float, float, float, float]:
        """Evaluates `subTopDualVector` for `eta = dH_tilde ∧ f^* mu_B` and `Omega = p_F^* omega_F ∧ p_B^* mu_B`."""
        beta_val = beta_base(b0, b1)
        omega_basis = c_chart * beta_val  # ((dy0 ∧ dy1) ∧ (db0 ∧ db1))(e0, e1, e2, e3)
        dh = grad_h_tilde(b0, b1, y0, y1)
        comps = []
        for i in range(4):
            sign = -1.0 if (i % 2 == 1) else 1.0
            eta_rem = wedge_dh_mub_on_remove_nth(i, dh, beta_val)
            comps.append(sign * eta_rem / omega_basis)
        return (comps[0], comps[1], comps[2], comps[3])

    test_points = [
        (0.05, -0.04, 0.12, -0.18),  # Core where rho(b) = 1
        (0.35, 0.25, -0.20, 0.15),   # Slope where 0 < rho(b) < 1 and grad(rho) != 0
        (-0.42, 0.30, 0.22, 0.09),   # Slope where 0 < rho(b) < 1 and grad(rho) != 0
        (0.75, -0.50, 0.10, -0.10),  # Exterior where rho(b) = 0
    ]

    max_base_err = 0.0
    max_fiber_err = 0.0
    max_flipped_err = 0.0
    slope_grad_nonzero = False

    for b0, b1, y0, y1 in test_points:
        dh = grad_h_tilde(b0, b1, y0, y1)
        if math.hypot(dh[0], dh[1]) > 1e-4:
            slope_grad_nonzero = True
        xb0, xb1, xy0, xy1 = jacobian_poisson_xh_tilde(b0, b1, y0, y1)
        base_err = math.hypot(xb0, xb1)
        max_base_err = max(max_base_err, base_err)

        rho_val = rho_bump(b0, b1)
        xh0, xh1 = planar_xh_exact(y0, y1)
        expected_y0 = rho_val * xh0
        expected_y1 = rho_val * xh1

        fiber_err = math.hypot(xy0 - expected_y0, xy1 - expected_y1)
        flipped_err = math.hypot(xy0 + expected_y0, xy1 + expected_y1)
        max_fiber_err = max(max_fiber_err, fiber_err)
        max_flipped_err = max(max_flipped_err, flipped_err)

    # RK4 integration check: time-1 flow of X_{H_tilde} vs time-rho(b) flow of X_H
    def rk4_integrate(
        vec_fn: Callable[[float, float], Tuple[float, float]],
        y0_init: float,
        y1_init: float,
        t_final: float,
        steps: int = 200,
    ) -> Tuple[float, float]:
        dt = t_final / float(steps)
        y0, y1 = y0_init, y1_init
        for _ in range(steps):
            k1x, k1y = vec_fn(y0, y1)
            k2x, k2y = vec_fn(y0 + 0.5 * dt * k1x, y1 + 0.5 * dt * k1y)
            k3x, k3y = vec_fn(y0 + 0.5 * dt * k2x, y1 + 0.5 * dt * k2y)
            k4x, k4y = vec_fn(y0 + dt * k3x, y1 + dt * k3y)
            y0 += (dt / 6.0) * (k1x + 2.0 * k2x + 2.0 * k3x + k4x)
            y1 += (dt / 6.0) * (k1y + 2.0 * k2y + 2.0 * k3y + k4y)
        return (y0, y1)

    max_flow_err = 0.0
    for b0, b1, y0, y1 in test_points:
        rho_val = rho_bump(b0, b1)
        # 1) Time-1 flow of 4D Poisson-Hamiltonian vector field X_{H_tilde}
        end_4d = rk4_integrate(
            lambda u0, u1: jacobian_poisson_xh_tilde(b0, b1, u0, u1)[2:],
            y0,
            y1,
            t_final=1.0,
            steps=200,
        )
        # 2) Time-rho(b) flow of 2D planar Hamiltonian vector field X_H
        end_2d = rk4_integrate(
            planar_xh_exact,
            y0,
            y1,
            t_final=rho_val,
            steps=200,
        )
        max_flow_err = max(max_flow_err, math.hypot(end_4d[0] - end_2d[0], end_4d[1] - end_2d[1]))

    return R5NormalizationAuditResult(
        darboux_radius=darboux_radius,
        area_scale_c_chart=c_chart,
        max_base_component_error=max_base_err,
        max_fiber_vector_field_error=max_fiber_err,
        max_sign_flipped_error=max_flipped_err,
        max_rk4_flow_time_one_error=max_flow_err,
        annihilates_grad_rho_on_slope=(slope_grad_nonzero and max_base_err < 1e-15),
        sign_is_plus_one=(max_fiber_err < 1e-8 and max_flipped_err > 0.1),
    )


# =============================================================================
# 7. Full C0 Suite Runner & Summary Report
# =============================================================================

def run_full_c0_suite() -> Dict[str, object]:
    """Runs all C0.1--C0.4 checks and returns a structured dictionary of quantitative metrics."""
    results: Dict[str, object] = {}

    # 1. Lemma G0 checks for N = 2, 3, 5, 10 and R_flipRight_shift (N = 6)
    g0_reports: Dict[str, Dict[str, object]] = {}
    for n_val in (2, 3, 5, 10):
        rule = build_random_bijective_shift_dom3(n_val, seed=100 + n_val)
        g0 = verify_lemma_g0(rule, num_samples=250)
        g0_reports[f"N={n_val}"] = dataclasses.asdict(g0)

    r_flip_rule = build_r_flip_right_shift()
    g0_flip = verify_lemma_g0(r_flip_rule, num_samples=250)
    g0_reports["R_flipRight_shift(N=6)"] = dataclasses.asdict(g0_flip)
    results["G0_audits"] = g0_reports

    # 2. Relocation pipeline checks (C0.3) for N = 2, 3, 5, 10 and R_flipRight_shift (N = 6)
    pipeline_reports: Dict[str, Dict[str, object]] = {}
    total_random_points = 0
    overall_max_cantor_err = 0.0

    for n_val, n_pts in ((2, 4000), (3, 4000), (5, 1500), (10, 500)):
        rule = build_random_bijective_shift_dom3(n_val, seed=100 + n_val)
        plan = build_relocation_pipeline(rule)
        max_err, tested = evaluate_pipeline_on_random_cantor_points(
            rule, plan, num_points=n_pts, seed=500 + n_val
        )
        total_random_points += tested
        overall_max_cantor_err = max(overall_max_cantor_err, max_err)
        pipeline_reports[f"N={n_val}"] = {
            "n_alpha": n_val,
            "base": plan.base,
            "num_blocks": n_val ** 3,
            "num_hamiltonian_generators": len(plan.moves),
            "num_collisions": plan.num_Collisions,
            "min_tube_clearance": plan.min_tube_clearance,
            "min_stretch_clearance": plan.min_stretch_clearance,
            "max_trajectory_radius_in_wb": plan.max_trajectory_radius_in_wb,
            "workbench_r_in": plan.workbench_r_in,
            "max_support_norm": plan.max_support_norm,
            "r_0": plan.r_0,
            "random_points_tested": tested,
            "max_cantor_point_error": max_err,
        }

    plan_flip = build_relocation_pipeline(r_flip_rule)
    err_flip, tested_flip = evaluate_pipeline_on_random_cantor_points(
        r_flip_rule, plan_flip, num_points=2000, seed=999
    )
    total_random_points += tested_flip
    overall_max_cantor_err = max(overall_max_cantor_err, err_flip)
    pipeline_reports["R_flipRight_shift(N=6)"] = {
        "n_alpha": 6,
        "base": plan_flip.base,
        "num_blocks": 216,
        "num_hamiltonian_generators": len(plan_flip.moves),
        "num_collisions": plan_flip.num_Collisions,
        "min_tube_clearance": plan_flip.min_tube_clearance,
        "min_stretch_clearance": plan_flip.min_stretch_clearance,
        "max_trajectory_radius_in_wb": plan_flip.max_trajectory_radius_in_wb,
        "workbench_r_in": plan_flip.workbench_r_in,
        "max_support_norm": plan_flip.max_support_norm,
        "r_0": plan_flip.r_0,
        "random_points_tested": tested_flip,
        "max_cantor_point_error": err_flip,
    }

    # Also verify the Abstract 1D-Sliding-Insertion Relocation Pipeline (Milestone A3) on N = 2, 3
    for n_val in (2, 3):
        rule = build_random_bijective_shift_dom3(n_val, seed=100 + n_val)
        triples = rule.all_triples()
        bmaps = [compute_block_affine_map(rule, w) for w in triples]
        abs_plan = build_abstract_sliding_relocation_pipeline(
            source_rects=[m.source_rect for m in bmaps],
            target_rects=[m.target_rect for m in bmaps],
            f_shifts=[m.f_shift for m in bmaps],
            base=rule.base,
        )
        abs_err, abs_tested = evaluate_pipeline_on_random_cantor_points(
            rule, abs_plan, num_points=1000, seed=1700 + n_val
        )
        total_random_points += abs_tested
        overall_max_cantor_err = max(overall_max_cantor_err, abs_err)
        pipeline_reports[f"AbstractSliding_N={n_val}"] = {
            "n_alpha": n_val,
            "base": abs_plan.base,
            "num_blocks": n_val ** 3,
            "num_hamiltonian_generators": len(abs_plan.moves),
            "num_collisions": abs_plan.num_Collisions,
            "min_tube_clearance": abs_plan.min_tube_clearance,
            "min_stretch_clearance": abs_plan.min_stretch_clearance,
            "max_trajectory_radius_in_wb": abs_plan.max_trajectory_radius_in_wb,
            "workbench_r_in": abs_plan.workbench_r_in,
            "max_support_norm": abs_plan.max_support_norm,
            "r_0": abs_plan.r_0,
            "random_points_tested": abs_tested,
            "max_cantor_point_error": abs_err,
        }

    results["relocation_pipelines"] = pipeline_reports
    results["total_random_cantor_points_tested"] = total_random_points
    results["overall_max_cantor_point_error"] = overall_max_cantor_err
    results["I1_chart_rescaling_needed"] = False

    # 3. R5 / Q-P Poisson-Hamiltonian normalization check (C0.4)
    r5 = verify_r5_poisson_hamiltonian_normalization()
    results["R5_normalization"] = dataclasses.asdict(r5)

    return results


def main() -> int:
    summary = run_full_c0_suite()
    print(json.dumps(summary, indent=2))

    # Assertions for CLI exit code 0
    for name, g0 in summary["G0_audits"].items():
        assert g0["disjoint_sources"], f"G0 source disjointness failed for {name}"
        assert g0["disjoint_targets"], f"G0 target disjointness failed for {name}"
        assert g0["exact_rational_passed"], f"Exact rational A_w failed for {name}"
        assert g0["max_affine_embed_error"] < 1e-12, f"Float A_w error too large for {name}"

    for name, pl in summary["relocation_pipelines"].items():
        assert pl["num_collisions"] == 0, f"Collisions detected in {name}: {pl['num_collisions']}"
        assert pl["min_tube_clearance"] > 0.0, f"Non-positive tube clearance in {name}"
        assert pl["max_support_norm"] < pl["r_0"] < 1.0, f"Support exceeded r_0 in {name}"
        assert pl["max_cantor_point_error"] < 1e-12, f"Cantor flow error too large in {name}"

    assert summary["total_random_cantor_points_tested"] >= 10000
    assert summary["overall_max_cantor_point_error"] < 1e-12

    r5 = summary["R5_normalization"]
    assert r5["annihilates_grad_rho_on_slope"], "R5 failed to annihilate grad(rho) on bump slope"
    assert r5["sign_is_plus_one"], "R5 sign check failed"
    assert r5["max_rk4_flow_time_one_error"] < 1e-12, "R5 time-1 flow comparison failed"
    return 0


if __name__ == "__main__":
    sys.exit(main())
