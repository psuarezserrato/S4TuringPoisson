# CMPP Milestone C0: Geometric, Dynamical & Poisson-Hamiltonian Specification

This document records the verified mathematical formulas, sign conventions, coordinate layouts,
clearance bounds, **D3 verdict on I1 (chart rescaling)**, and **finalized R5 / Q-P
Poisson–Hamiltonian normalization and Lean 4 statements** produced by Milestone C0
(`tools/cmpp_planner.py` and `tests/test_cmpp_planner.py`).

---

## 1. Sign Pinning & Closed-Form Block Affine Action $A_w$ (C0.1)

### 1.1 Exact Lean Conventions (`S4TuringPoisson/Dynamics/GeneralizedShift.lean`)

Let $A$ be a finite alphabet of cardinality $N \ge 2$ with numbering $\mathrm{enc} : A \simeq \mathrm{Fin}\,N$,
and let
$$B := \mathrm{cantorBase}(N) = \max(2N - 1, 3) = 2N - 1 \ge 3.$$

1. **Shift Evaluation (`GeneralizedShift.eval`)**:
   - `shiftSeq m s k = s (k + m)`
   - `replaceDom D u s k = if hk : k ∈ D then u ⟨k, hk⟩ else s k`
   - For $\Phi : \mathrm{GeneralizedShift}\,A$ with $\Phi.D = \mathrm{shiftDom3} = \{-1, 0, 1\}$ and
     $w := \mathrm{restrictDom}\,\Phi.D\,s = (w_{-1}, w_0, w_1) \in A^3$, let
     $u := \Phi.G(w) = (u_{-1}, u_0, u_1) \in A^3$ and $f := \Phi.F(w) \in \{-1, 0, 1\}$. Then:
     $$(\Phi.\mathrm{eval}\,s)(k) = (\mathrm{replaceDom}\,\{-1, 0, 1\}\,u\,s)(k + f).$$

2. **Half-Sequences & Square Cantor Embedding (`cantorDiskEmbed`)**:
   - Coordinate $0$ ($x$-axis) encodes the **negative** indices via `negHalf s j = s (-(j + 1))`
     ($j = 0 \mapsto s(-1)$, $j = 1 \mapsto s(-2)$, $\dots$).
   - Coordinate $1$ ($y$-axis) encodes the **non-negative** indices via `nonnegHalf s j = s j`
     ($j = 0 \mapsto s(0)$, $j = 1 \mapsto s(1)$, $\dots$).
   - Each coordinate is scaled by $\tfrac{1}{4}$ via `scaledCantorCoord`:
     $$x(s) = \frac{1}{4} \sum_{j=0}^{\infty} \frac{2\,\mathrm{enc}(s(-j-1))}{B^{j+1}} \in \left[0, \frac{1}{4}\right], \qquad
       y(s) = \frac{1}{4} \sum_{j=0}^{\infty} \frac{2\,\mathrm{enc}(s(j))}{B^{j+1}} \in \left[0, \frac{1}{4}\right].$$
   - decomposing $(x(s), y(s))$ on the $D = \{-1, 0, 1\}$ cylinder
     $\mathrm{cyl}(w) = \{s : \mathbb{Z} \to A \mid s(-1)=w_{-1},\; s(0)=w_0,\; s(1)=w_1\}$ into
     prefix plus tail ($x_{\mathrm{tail}}, y_{\mathrm{tail}} \in [0, 1]$):
     $$x(s) = \frac{2 w_{-1} + x_{\mathrm{tail}}}{4B}, \qquad
       y(s) = \frac{2 w_0 B + 2 w_1 + y_{\mathrm{tail}}}{4B^2},$$
     where $x_{\mathrm{tail}} = \mathrm{cantorCoord}(j \mapsto \mathrm{enc}(s(-j-2)))$ and
     $y_{\mathrm{tail}} = \mathrm{cantorCoord}(j \mapsto \mathrm{enc}(s(j+2)))$ depend **only** on
     coordinates $k \notin \{-1, 0, 1\}$.

### 1.2 Pinned Sign Table for $F(w) \in \{-1, 0, +1\}$

Because coordinate $0$ ($x$) carries `negHalf` ($k \le -1$) and $\Phi.\mathrm{eval}$ shifts indices by $+f$
($s'(k) = s_{\mathrm{rep}}(k + f)$):
- When $f = +1$ (sequence shifts **left**): `negHalf` gains a leading digit ($x$ **contracts** by $B^{-1}$),
  while `nonnegHalf` drops a leading digit ($y$ **expands** by $B$).
- When $f = -1$ (sequence shifts **right**): `negHalf` drops its leading digit $w_{-1}$ ($x$ **expands** by $B$),
  while `nonnegHalf` gains a leading digit ($y$ **contracts** by $B^{-1}$).
- In `S4TuringPoisson/Smoothing/DiskSmoothing.lean`, `stretchQuad c μ y = -μ * (y₀ - c₀) * (y₁ - c₁)`
  generates the time-$1$ flow $(e^{-\mu}, e^{+\mu})$ (`bumpedHyperbolicStretchIsotopy_timeOne_of_mem_closedBall`).
  Therefore, the stretch parameter is **$\mu_w = +F(w)\,\log B$** (with sign **$+1$**):
  $$(e^{-\mu_w}, e^{+\mu_w}) = (B^{-F(w)}, B^{+F(w)}) = (\lambda_w, \lambda_w^{-1}).$$

| $f = F(w)$ | $\lambda_w = B^{-f}$ ($x$-scale) | $\lambda_w^{-1} = B^{+f}$ ($y$-scale) | Stretch parameter $\mu_w$ | Translation offset $a_w$ | Translation offset $b_w$ | Image rectangle $R'_w = A_w(R_w)$ size |
|---|---|---|---|---|---|---|
| $+1$ | $B^{-1}$ (contracts $x$) | $B$ (expands $y$) | $+\log B$ | $\dfrac{u_0 B + u_{-1} - w_{-1}}{2 B^2}$ | $\dfrac{u_1 - w_0 B - w_1}{2 B}$ | $\dfrac{1}{4B^2} \times \dfrac{1}{4B}$ |
| $0$ | $1$ | $1$ | $0$ | $\dfrac{u_{-1} - w_{-1}}{2 B}$ | $\dfrac{(u_0 - w_0)B + (u_1 - w_1)}{2 B^2}$ | $\dfrac{1}{4B} \times \dfrac{1}{4B^2}$ |
| $-1$ | $B$ (expands $x$) | $B^{-1}$ (contracts $y$) | $-\log B$ | $-\dfrac{w_{-1}}{2}$ | $\dfrac{u_{-1} B^2 + (u_0 - w_0)B + (u_1 - w_1)}{2 B^3}$ | $\dfrac{1}{4} \times \dfrac{1}{4B^3}$ |

### 1.3 Source and Image Rectangle Formulas ($R_w$ and $R'_w$)

For every $w = (w_{-1}, w_0, w_1) \in \{0, \dots, N-1\}^3$ with $u = G(w) = (u_{-1}, u_0, u_1)$:
- **Source rectangle** $R_w$ (size $\tfrac{1}{4B} \times \tfrac{1}{4B^2}$):
  $$R_w = \left[\frac{2 w_{-1}}{4B},\; \frac{2 w_{-1} + 1}{4B}\right] \times
          \left[\frac{2 w_0 B + 2 w_1}{4B^2},\; \frac{2 w_0 B + 2 w_1 + 1}{4B^2}\right] \subseteq \left[0, \frac{1}{4}\right]^2.$$
- **Target rectangle** $R'_w = A_w(R_w) \subseteq [0, 1/4]^2$ where $A_w(x, y) = (B^{-f} x + a_w,\; B^{f} y + b_w)$:
  - For $f = +1$ (cylinder fixed at $D - 1 = \{-2, -1, 0\}$ with values $(u_{-1}, u_0, u_1)$):
    $$R'_w = \left[\frac{2 u_0 B + 2 u_{-1}}{4B^2},\; \frac{2 u_0 B + 2 u_{-1} + 1}{4B^2}\right] \times
             \left[\frac{2 u_1}{4B},\; \frac{2 u_1 + 1}{4B}\right].$$
  - For $f = 0$ (cylinder fixed at $D = \{-1, 0, 1\}$ with values $(u_{-1}, u_0, u_1)$):
    $$R'_w = \left[\frac{2 u_{-1}}{4B},\; \frac{2 u_{-1} + 1}{4B}\right] \times
             \left[\frac{2 u_0 B + 2 u_1}{4B^2},\; \frac{2 u_0 B + 2 u_1 + 1}{4B^2}\right].$$
  - For $f = -1$ (cylinder fixed at $D + 1 = \{0, 1, 2\}$ with values $(u_{-1}, u_0, u_1)$, $0$ negative digits fixed):
    $$R'_w = \left[0,\; \frac{1}{4}\right] \times
             \left[\frac{2 u_{-1} B^2 + 2 u_0 B + 2 u_1}{4B^3},\; \frac{2 u_{-1} B^2 + 2 u_0 B + 2 u_1 + 1}{4B^3}\right].$$

---

## 2. Lemma G0 Verification & Minimum Gap Bounds (C0.2)

### 2.1 Analytical Proof Sketch for Milestone A1 (`CMPP/Digits.lean`)

1. **Prefix-Interval Inclusion & Compatibility**:
   For any prefix $p : \mathrm{Fin}\,m \to \mathrm{Fin}\,N$ with integer code $K = \mathrm{cantorPrefixCode}\,B\,p$,
   define the closed rescaled middle-Cantor interval
   $$I(p) := \left[\frac{K}{4 B^m},\; \frac{K + 1}{4 B^m}\right] \subseteq \left[0, \frac{1}{4}\right].$$
   - If $m_1 \le m_2$ and $p_1 : \mathrm{Fin}\,m_1 \to \mathrm{Fin}\,N$, $p_2 : \mathrm{Fin}\,m_2 \to \mathrm{Fin}\,N$:
     - If $p_1$ is a prefix of $p_2$ ($\forall j < m_1,\; p_1(j) = p_2(j)$), then $I(p_2) \subseteq I(p_1)$.
     - If $p_1$ is **not** a prefix of $p_2$, let $p_2|_{m_1}$ be the length-$m_1$ truncation of $p_2$. Then
       $p_1 \ne p_2|_{m_1}$, so by `two_le_abs_cantorPrefixCode_sub` (`GeneralizedShift.lean` line 1070),
       $|K(p_1) - K(p_2|_{m_1})| \ge 2$, which implies $\mathrm{dist}(I(p_1), I(p_2)) \ge \mathrm{dist}(I(p_1), I(p_2|_{m_1})) \ge \frac{1}{4 B^{m_1}} > 0$.
2. **Disjointness of $R'_w$ when $\Phi.\mathrm{eval}$ is Injective (Lemma G0)**:
   Each target rectangle is a product of closed prefix intervals $R'_w = I(p^-_w) \times I(p^+_w)$ of lengths
   $(m^-_w, m^+_w) \in \{(2, 1), (1, 2), (0, 3)\}$ with $m^-_w + m^+_w = 3$.
   If $R'_{w_1} \cap R'_{w_2} \ne \emptyset$, then $I(p^-_{w_1}) \cap I(p^-_{w_2}) \ne \emptyset$ and
   $I(p^+_{w_1}) \cap I(p^+_{w_2}) \ne \emptyset$. By prefix compatibility, one negative prefix extends the other
   and one non-negative prefix extends the other, so there exists a bi-infinite sequence $y : \mathbb{Z} \to A$
   matching both cylinder constraints $\Phi.\mathrm{eval}(\mathrm{cyl}(w_1))$ and $\Phi.\mathrm{eval}(\mathrm{cyl}(w_2))$.
   Constructing $s_1 \in \mathrm{cyl}(w_1)$ and $s_2 \in \mathrm{cyl}(w_2)$ with $\Phi.\mathrm{eval}(s_1) = y = \Phi.\mathrm{eval}(s_2)$
   forces $s_1 = s_2$ by injectivity of $\Phi.\mathrm{eval}$, hence $w_1 = w_2$.
   Moreover, for $w_1 \ne w_2$, the Euclidean distance between $R'_{w_1}$ and $R'_{w_2}$ is at least
   $$\mathrm{gap}(R'_{w_1}, R'_{w_2}) \ge \frac{1}{4 B^3} > 0, \qquad
     \mathrm{gap}(R_{w_1}, R_{w_2}) \ge \frac{1}{4 B^2} > 0.$$

### 2.2 Numerical G0 Audit Table (`tools/cmpp_planner.py`)

| Shift Case | $N$ | $B = 2N-1$ | $N^3$ Blocks | $(|F=-1|, |F=0|, |F=+1|)$ | Measured $\min \mathrm{gap}(R_w)$ | Formula $\frac{1}{4B^2}$ | Measured $\min \mathrm{gap}(R'_w)$ | Bound $\frac{1}{4B^3}$ | Exact Rational $A_w$ | Max Float Error |
|---|---|---|---|---|---|---|---|---|---|---|
| Random Bijective | $2$ | $3$ | $8$ | $(0, 4, 4)$ | $0.02777778$ | $0.02777778$ | $0.02777778$ | $0.00925926$ | **PASS** ($0$) | $1.39 \times 10^{-16}$ |
| Random Bijective | $3$ | $5$ | $27$ | $(9, 9, 9)$ | $0.01000000$ | $0.01000000$ | $0.00200000$ | $0.00200000$ | **PASS** ($0$) | $3.19 \times 10^{-16}$ |
| Random Bijective | $5$ | $9$ | $125$ | $(25, 50, 50)$ | $0.00308642$ | $0.00308642$ | $0.00034294$ | $0.00034294$ | **PASS** ($0$) | $5.28 \times 10^{-16}$ |
| `R_flipRight_shift` | $6$ | $11$ | $216$ | $(0, 72, 144)$ | $0.00206612$ | $0.00206612$ | $0.00206612$ | $0.00018783$ | **PASS** ($0$) | $7.22 \times 10^{-16}$ |
| Random Bijective | $10$ | $19$ | $1000$ | $(300, 400, 300)$ | $0.00069252$ | $0.00069252$ | $3.6448 \times 10^{-5}$ | $3.6448 \times 10^{-5}$ | **PASS** ($0$) | $1.78 \times 10^{-15}$ |

---

## 3. Room Question Verdict (D3 / I1) & 4-Stage Relocation Architecture (C0.3)

### 3.1 Explicit Quantitative Verdict on I1 (Chart Rescaling)

> **VERDICT ON I1 (`MISSION_DIRECTIVE_CMPP.md` §4.3, §5, D3): I1 (chart rescaling) is NOT NEEDED.**
> Keep `scaledCantorCoord` and `cantorDiskEmbed` **100% frozen as-is** (Milestone A0 is skipped).

**Quantitative Proof:**
1. Under the frozen `cantorDiskEmbed` chart (`scaledCantorCoord = (1/4) * cantorCoord`), **all** $N^3$
   source rectangles $R_w$ and **all** $N^3$ target rectangles $R'_w$ (including the $F = -1$ strips of width
   $\tfrac{1}{4}$ and height $\tfrac{1}{4B^3}$) lie inside the $\tfrac{1}{4} \times \tfrac{1}{4}$ square
   $$\mathrm{Box}_{\mathrm{src}} = \left[0, \frac{1}{4}\right]^2 \subset \mathrm{UnitDisk2} = B(0, 1),$$
   which has maximum Euclidean norm $\frac{\sqrt{2}}{4} \approx 0.353553$.
2. Why the earlier draft's 1D row count overflowed while the 2D Target Parking Box does not:
   Parking $N^3$ pieces of width $\tfrac{1}{4B}$ in a **single 1D horizontal row** of $N^3$ disjoint
   $x$-intervals would require width $\ge \frac{N^3}{4B} \sim \frac{N^2}{8}$, which overflows $B(0, 1)$ for $N \ge 3$.
   **However**, because the $N^3$ target rectangles $R'_w \subseteq [0, 1/4]^2$ are **pairwise disjoint**
   by Lemma G0, their translated copies
   $$S'_w := R'_w + v_{\mathrm{park}}, \qquad v_{\mathrm{park}} = (-0.60, 0),$$
   are **automatically pairwise disjoint** inside the single $\tfrac{1}{4} \times \tfrac{1}{4}$
   **Target Parking Box**
   $$\mathrm{Box}_{\mathrm{park}} := \left[0, \frac{1}{4}\right]^2 + (-0.60, 0) = [-0.60, -0.35] \times [0, 0.25] \subset B(0, 0.65)$$
   for **all $N \ge 2$ simultaneously**!

### 3.2 Two Verified 0-Collision Autonomous Relocation Pipelines inside $B(0, r_0)$ ($r_0 = 0.85 < 1$)

Both pipelines use the same fixed support radius $r_0 = 0.85 \in (0, 1)$, workbench center
$c_{\mathrm{wb}} = (0, -0.35)$, workbench outer cutoff radius $r_{\mathrm{out}} = 0.30$
(inner flat radius $r_{\mathrm{in}} = r_{\mathrm{out}} / 2 = 0.15$), and Urysohn tube cutoff margin
$\varepsilon_{\mathrm{tube}} = \frac{1}{16 B^3}$.

#### Pipeline A: General 1D-Sliding-Insertion Pipeline (for Milestone A3 `CMPP/Relocation.lean`)
Works for **any** $n$ pairwise-disjoint compact axis-parallel source rectangles
$P_0, \dots, P_{n-1} \subseteq [0, 1/4]^2$ and pairwise-disjoint target rectangles
$P'_0 = A_0(P_0), \dots, P'_{n-1} = A_{n-1}(P_{n-1}) \subseteq [0, 1/4]^2$, using **only the 1D Horizontal Sliding Lemma**:
- **Fixed Zones**:
  - $\mathrm{Box}_{\mathrm{src}} = [0, 0.25] \times [0, 0.25]$
  - Right Extraction Corridor: $[0.30, 0.55] \times [0, 0.25]$ ($v_{\mathrm{elev}} = (+0.30, 0)$)
  - Target Staging Box: $\mathrm{Box}_{\mathrm{stage}} = [-0.30, -0.05] \times [0, 0.25]$ ($v_{\mathrm{stage}} = (-0.30, 0)$)
  - Target Parking Box: $\mathrm{Box}_{\mathrm{park}} = [-0.60, -0.35] \times [0, 0.25]$ ($v_{\mathrm{park}} = (-0.60, 0)$)
  - Workbench Ball: $B(c_{\mathrm{wb}}, r_{\mathrm{out}}) = B((0, -0.35), 0.30) \subset \{y \le -0.05\}$ (strictly separated in $y$ by $\ge 0.05$ from all boxes in $y \in [0, 0.25]$!).
- **Execution Loop** (sort indices $i \in \{0, \dots, n-1\}$ in **decreasing order of $x_{\min}(P_i)$**):
  1. **Extract $P_i$ right (`+x`) by $(+0.30, 0)$ into Right Corridor**: Collision-free by the 1D Horizontal Sliding Lemma on $\{P_k : k \ge i\} \subseteq \mathrm{Box}_{\mathrm{src}}$.
  2. **Drop to Workbench**: Translate vertically in $-y$ inside $x \in [0.30, 0.55]$ down to $y = -0.35$ (strictly separated in $x$ from all other pieces, which have $x \le 0.25$), then translate horizontally at $y = -0.35$ to center at $c_{\mathrm{wb}} = (0, -0.35)$ (strictly separated in $y$ from all other pieces, which have $y \ge 0$).
  3. **Stretch at Workbench**: Apply `bumpedHyperbolicStretchIsotopy` at $c_{\mathrm{wb}} = (0, -0.35)$ with $\mu_i = F(w_i)\log B$ and $r_{\mathrm{out}} = 0.30$.
  4. **Part the Sea in $\mathrm{Box}_{\mathrm{park}}$**: Among already-parked pieces $j < i$, let
     $J_{\mathrm{right}}(i) := \{j < i \mid x_{\max}(P'_j) \ge x_{\min}(P'_i)\}$.
     In **decreasing order of $x_{\min}(P'_j)$**, translate each $S'_j = P'_j + v_{\mathrm{park}}$ by $(+0.30, 0)$ into $\mathrm{Box}_{\mathrm{stage}}$ (collision-free by the 1D Horizontal Sliding Lemma!).
  5. **Insert Stretched Piece $i$ into $S'_i = P'_i + v_{\mathrm{park}} \subseteq \mathrm{Box}_{\mathrm{park}}$**:
     Translate piece $i$ horizontally at $y = -0.35$ to $x_{\mathrm{center}}(S'_i)$, then translate **straight UP (`+y`)** into $S'_i$.
     *Why 0 collisions without even a vertical Sliding Lemma?* Every remaining piece $k$ in $\mathrm{Box}_{\mathrm{park}}$ has $x_{\max}(S'_k) < x_{\min}(S'_i)$ (strictly to the left in $x$), and every piece in $\mathrm{Box}_{\mathrm{stage}} \cup \mathrm{Box}_{\mathrm{src}}$ has $x_{\min} \ge -0.30 > -0.35 \ge x_{\max}(S'_i)$ (strictly to the right in $x$)!
  6. **Un-part the Sea**: In **increasing order of $x_{\min}(P'_j)$** (reverse of Step 4), translate each $j \in J_{\mathrm{right}}(i)$ from $\mathrm{Box}_{\mathrm{stage}}$ by $(-0.30, 0)$ back to $S'_j \subseteq \mathrm{Box}_{\mathrm{park}}$ (collision-free by the reverse 1D Horizontal Sliding Lemma!).
- **Stage 4 (Return to $\mathrm{Box}_{\mathrm{src}}$)**: Once all $n$ pieces are in $\mathrm{Box}_{\mathrm{park}}$, translate $\mathrm{Box}_{\mathrm{park}}$ by $(+0.60, 0)$ onto $[0, 0.25]^2$ (either as 1 bulk L1 translation or piece-by-piece in decreasing $x_{\min}(P'_i)$ order).

#### Pipeline B: Fast $O(N^3)$ Column-Elevator Pipeline (Exploiting the $N$ Columns of $R_w$)
- **Stage 1**: Slide the $N$ source columns $c = N-1, \dots, 1$ in $+x$ by $+c/(4B)$ into $[0, 0.375] \times [0, 0.25]$, creating an empty vertical elevator shaft $[(3c+1)/(4B), (3c+3)/(4B)]$ of width $2/(4B)$ to the right of every column $c$.
- **Stages 2–3**: Process $w \in A^3$ in **decreasing order of $y_{\min}(R'_w)$**: step right by $+1.5/(4B)$ into column $w_{-1}$'s elevator shaft, ride straight down to $y = -0.35$, center at $c_{\mathrm{wb}} = (0, -0.35)$, stretch by $\mu_w = F(w)\log B$, align under $S'_w = R'_w + (-0.60, 0)$, and slide straight up into $S'_w \subseteq \mathrm{Box}_{\mathrm{park}}$.
- **Stage 4**: Translate $\mathrm{Box}_{\mathrm{park}}$ by $(+0.60, 0)$ onto $[0, 0.25]^2$.

### 3.3 Workbench Trajectory Radius & Milestone A2 L2 Rectangle-Wrapper Specification

In `DiskSmoothing.lean` (line 1314), `bumpedHyperbolicStretchIsotopy_timeOne_of_mem_closedBall` was proved
for an isotropic closed ball `Metric.closedBall c δ` using the coarse time interval $u \in (-2, 2)$, resulting
in the hypothesis `Real.exp (2 * |μ|) * δ < r_out / 2` ($B^2 \delta < r_{\mathrm{out}} / 2$).
- For a centered Cantor rectangle $[c_0 - \delta_0, c_0 + \delta_0] \times [c_1 - \delta_1, c_1 + \delta_1]$ of half-widths
  $\delta_0 = \frac{1}{8B}$ and $\delta_1 = \frac{1}{8B^2}$ and $\mu = F(w)\log B$ ($F(w) \in \{-1, +1\}$):
  along the entire flow $u \in [0, 1]$, the trajectory $\gamma(u) = c + (e^{-u\mu} v_0, e^{u\mu} v_1)$ satisfies:
  - For $F = +1$ ($\mu = +\log B$): $|e^{-u\mu} v_0| \le \frac{1}{8B}$ and $|e^{u\mu} v_1| \le B \cdot \frac{1}{8B^2} = \frac{1}{8B}$, so
    $$\max_{u \in [0, 1]} \|\gamma(u) - c_{\mathrm{wb}}\| \le \frac{\sqrt{2}}{8B} \le \frac{\sqrt{2}}{24} \approx 0.05893 < 0.15 = \frac{r_{\mathrm{out}}}{2}.$$
  - For $F = -1$ ($\mu = -\log B$): $|e^{-u\mu} v_0| \le B \cdot \frac{1}{8B} = \frac{1}{8} = 0.125$ and $|e^{u\mu} v_1| \le \frac{1}{8B^2} \le \frac{1}{72}$, so
    $$\max_{u \in [0, 1]} \|\gamma(u) - c_{\mathrm{wb}}\| \le \sqrt{\left(\frac{1}{8}\right)^2 + \left(\frac{1}{8B^2}\right)^2} \le 0.12577 < 0.15 = \frac{r_{\mathrm{out}}}{2}.$$
- **Specification for Milestone A2 (`CMPP/Primitives.lean` L2 wrapper)**:
  Prove `bumpedHyperbolicStretchIsotopy_timeOne_of_mem_rect` on
  $\{y \mid |y_0 - c_0| \le \delta_0 \land |y_1 - c_1| \le \delta_1\}$ using the tight open time interval
  $(a, b) = (-\varepsilon, 1 + \varepsilon)$ in `TauCeti.timeDependentFlowOf_eq_of_hasMFDerivAt`, requiring only
  $$\max(\delta_0, e^{-\mu}\delta_0)^2 + \max(\delta_1, e^{\mu}\delta_1)^2 < \left(\frac{r_{\mathrm{out}}}{2}\right)^2,$$
  which holds unconditionally for **all** $B \ge 3$ with $r_{\mathrm{out}} = 0.30$ ($r_{\mathrm{out}}/2 = 0.15 > 0.1258$).

### 3.4 Quantitative Relocation Pipeline Table (`r_0 = 0.85 < 1`)

| Pipeline & Shift Case | $N$ | $B$ | Blocks $N^3$ | Generators | Collisions | Min Tube Clearance | Min Stretch Clearance | Max WB Traj Radius ($< 0.15$) | Max Support Norm ($< 0.85$) | Random Cantor Points | Max Time-1 Flow Error |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Column-Elevator | $2$ | $3$ | $8$ | $46$ | **$0$** | $2.546 \times 10^{-2}$ | $0.0500$ | $0.05893$ | **$0.71973$** | $4,000$ | $3.62 \times 10^{-16}$ |
| Column-Elevator | $3$ | $5$ | $27$ | $156$ | **$0$** | $1.500 \times 10^{-3}$ | $0.0500$ | $0.12510$ | **$0.70824$** | $4,000$ | $6.39 \times 10^{-16}$ |
| Column-Elevator | $5$ | $9$ | $125$ | $705$ | **$0$** | $2.572 \times 10^{-4}$ | $0.0500$ | $0.12501$ | **$0.70184$** | $1,500$ | $1.28 \times 10^{-15}$ |
| `R_flipRight_shift` | $6$ | $11$ | $216$ | $1230$ | **$0$** | $2.019 \times 10^{-3}$ | $0.0500$ | $0.01607$ | **$0.70048$** | $2,000$ | $1.09 \times 10^{-15}$ |
| Column-Elevator | $10$ | $19$ | $1000$ | $5610$ | **$0$** | $2.734 \times 10^{-5}$ | $0.0500$ | $0.12500$ | **$0.69797$** | $500$ | $2.22 \times 10^{-15}$ |
| Abstract 1D-Sliding | $2$ | $3$ | $8$ | $102$ | **$0$** | $2.083 \times 10^{-2}$ | $0.0500$ | $0.05893$ | **$0.72614$** | $1,000$ | $3.62 \times 10^{-16}$ |
| Abstract 1D-Sliding | $3$ | $5$ | $27$ | $834$ | **$0$** | $1.500 \times 10^{-3}$ | $0.0500$ | $0.12510$ | **$0.70824$** | $1,000$ | $6.25 \times 10^{-16}$ |
| **Total / Bound** | **All** | $\ge 3$ | — | — | **$0$** | $> \frac{3}{16 B^3}$ | $\ge 0.0500$ | $< 0.1258 < 0.15$ | **$\le 0.7262 < 0.85$** | **$14,000$** | **$2.22 \times 10^{-15}$** |

---

## 4. R5 / Q-P Poisson–Hamiltonian Normalization & Finalized Lean Statements (C0.4)

### 4.1 Exact Normalization Derivation across `JacobianPoisson.lean`, `AlignedUnimodularVolume.lean`, and `BumpIsotopyLift.lean`

1. **Exact Volume Equality on $\mathrm{innerPreimageOpen}\,M$ (No base-dependent density $c(b)$)**:
   - By `tsupport_bumpProfile_subset_baseInnerOpen` (`BumpIsotopyLift.lean` line 639),
     $\mathrm{tsupport}(\rho) \subseteq \mathrm{baseInnerOpen}\,M$, where $\rho := \mathrm{bumpProfile}\,M : \mathrm{Sphere2} \to \mathbb{R}$.
   - On $\mathrm{innerPreimageOpen}\,M = f^{-1}(\mathrm{baseInnerOpen}\,M)$, `alignedCutoff` ($\chi$) is identically $1$, so by **Equation (1)** (`mpullback_innerPreimageOpen_alignedVolumeForm`, `AlignedUnimodularVolume.lean` line 1057):
     $$\Omega|_{\mathrm{innerPreimageOpen}\,M} = \Phi^*\!\left(p_F^* \omega_F \wedge p_B^* \mu_B\right)$$
     with coefficient **$1$** (the positive factor $c(x) > 0$ from `trivialization_pos_cooriented` only relates $\Phi^*(p_F^* \omega_F \wedge p_B^* \mu_B)$ to the unaligned ambient form $\Omega_0$ outside $\mathrm{innerPreimageOpen}\,M$, where $\rho \equiv 0$).

2. **Darboux Disk Chart Scaling Factor `C.areaScale = C.radius ^ 2` (in the Numerator!)**:
   - Let $C := \mathrm{AdmitsWrinkledOrBrokenLefschetzFibration.fiberDiskChart}\,M : \mathrm{SymplecticDiskChart}\,A.\mathrm{Fiber}\,A.\mathrm{fiberVolume}.\Omega$.
   - By `C.mpullback_embed_eq` (`WrinkledGeneral4Manifold.lean` line 463):
     $$C.\mathrm{embed}^* \omega_F = C.\mathrm{areaScale} \cdot \mathrm{planeAreaForm}|_{\mathrm{UnitDisk2}}, \qquad C.\mathrm{areaScale} = C.\mathrm{radius}^2 > 0.$$
   - For an autonomous planar Hamiltonian $P = \mathrm{CompactlySupportedPlanarHamiltonian.ofAutonomous}\,hr_0\,h\,hh\,h_{\mathrm{supp}}$, its planar Hamiltonian vector field $X_h = P.\mathrm{vectorField}\,0$ satisfies
     $$\iota_{X_h}\,\mathrm{planeAreaForm} = dh.$$
   - Define the lifted fiber Hamiltonian $h_F : A.\mathrm{Fiber} \to \mathbb{R}$ (supported in $C.\mathrm{supportSet}\,hr_0 \subset C.\mathrm{sourceOpen}$) by:
     $$h_F(z) := \begin{cases} C.\mathrm{areaScale} \cdot h(C.\mathrm{radius}^{-1} \cdot C.\mathrm{rawChart}\,z) & \text{if } z \in C.\mathrm{sourceOpen}, \\ 0 & \text{if } z \notin C.\mathrm{sourceOpen}, \end{cases}$$
     so that $h_F(C.\mathrm{embed}\,y) = C.\mathrm{areaScale} \cdot h(y)$.
     Then on $C.\mathrm{sourceOpen}$, the pushed-forward vector field $Y_F(C.\mathrm{embed}\,y) := d(C.\mathrm{embed})_y(X_h(y))$ ($0$ outside $C.\mathrm{sourceOpen}$) satisfies:
     $$\iota_{Y_F} \omega_F = dh_F.$$

3. **Annihilation of $\nabla\rho(b)$ and Sign $+1$ in the 4D Jacobian–Poisson Equation**:
   - Define the global smooth 4-manifold Hamiltonian $\tilde{H}_P : M \to \mathbb{R}$ by:
     $$\tilde{H}_P(x) := \begin{cases} \rho(f(x)) \cdot h_F\big((\Phi(x)).2\big) & \text{if } x \in f^{-1}(\mathrm{baseRegion}), \\ 0 & \text{otherwise.} \end{cases}$$
     Equivalently, on $\Phi^{-1}(b, C.\mathrm{embed}\,y)$:
     $$\boxed{\tilde{H}_P\big(\Phi^{-1}(b, C.\mathrm{embed}\,y)\big) = \big(\rho(b) \cdot C.\mathrm{areaScale}\big) \cdot h(y)}$$
     with **sign $+1$** and constant factor **$C.\mathrm{areaScale} = C.\mathrm{radius}^2 > 0$ in the numerator**.
   - On $U_{\mathrm{in}} = \mathrm{innerPreimageOpen}\,M$ (which contains $\mathrm{tsupport}(\tilde{H}_P)$),
     $$d\tilde{H}_P = h_F(z)\,f^*(d\rho) + \rho(f(x))\,\Phi^*(p_F^* dh_F).$$
   - When wedged with $f^* \mu_B$:
     $$f^*(d\rho) \wedge f^* \mu_B = f^*(d\rho \wedge \mu_B) = 0$$
     identically on all of $M$ (including on the slope of $\rho$ where $d\rho \ne 0$!), because $d\rho \wedge \mu_B$ is a $3$-form on the $2$-dimensional manifold $\mathrm{Sphere2}$ (`ContinuousAlternatingMap.eq_zero_of_finrank_lt`, `JacobianPoisson.lean` line 734).
   - Consequently, for the purely vertical vector field $V(b, z) = (0, \rho(b) Y_F(z))$:
     $$\iota_{\Phi_*^{-1} V} \Omega = \Phi^*\!\left(\iota_V (p_F^* \omega_F \wedge p_B^* \mu_B)\right)
       = \Phi^*\!\left(\rho(b)\,p_F^*(\iota_{Y_F}\omega_F) \wedge p_B^* \mu_B\right)
       = \rho(f(x))\,\Phi^*(p_F^* dh_F) \wedge f^* \mu_B
       = d\tilde{H}_P \wedge f^* \mu_B.$$
   - By `interior_hamiltonianVectorField_jacobianSmoothBivector` (`JacobianPoisson.lean` line 636) and uniqueness of `vectorFieldOfSubTopForm` (`eq_vectorFieldOfSubTopForm_iff`, line 276):
     $$\boxed{X_{\tilde{H}_P}\big(\Phi^{-1}(b, C.\mathrm{embed}\,y)\big) = d(\Phi^{-1})_{(b, C.\mathrm{embed}\,y)}\!\left(0,\; +\rho(b) \cdot d(C.\mathrm{embed})_y\big(X_h(y)\big)\right)}$$
     and $X_{\tilde{H}_P}(x) = 0$ outside $\mathrm{tsupport}(\tilde{H}_P)$.

4. **Time-1 Flow Identity via Autonomous Time-Rescaling**:
   - Because $P$ is autonomous ($P.\mathrm{vectorField}\,u\,y = X_h(y)$ is independent of $u$), for each fixed base point $b$ and initial point $y_0 \in \mathrm{EuclideanPlane}$, the time-rescaled trajectory
     $$\gamma_b(u) := P.\mathrm{flow}(u \cdot \rho(b),\; y_0)$$
     satisfies $\gamma_b'(u) = \rho(b) \cdot X_h(\gamma_b(u))$.
   - Lifting via $z \mapsto \Phi^{-1}(b, C.\mathrm{embed}\,z)$ and applying `TauCeti.timeDependentFlowOf_eq_of_hasMFDerivAt` proves that the time-$1$ flow of the autonomous 4D Poisson–Hamiltonian vector field $X_{\tilde{H}_P}$ on $M$ is **identically equal** to `leafwiseBumpDiffeomorphOfIsotopy M P.toDiskIsotopy` across all of $M$!

### 4.2 Finalized Lean 4 Statements for Deliverable R5 (Milestone P: `S4TuringPoisson/Extension/PoissonHamiltonian.lean`)

```lean
/-- An autonomous compactly supported planar Hamiltonian `P` satisfies `P.H (t, y) = P.H (0, y)`
for all `(t, y)`. -/
def CompactlySupportedPlanarHamiltonian.IsAutonomous {r₀ : ℝ}
    (P : CompactlySupportedPlanarHamiltonian r₀) : Prop :=
  ∀ (t : ℝ) (y : EuclideanPlane), P.H (t, y) = P.H (0, y)

/-- Lift an autonomous `CompactlySupportedPlanarHamiltonian r₀` to a smooth global Hamiltonian
`H̃ : C^∞⟮𝓡 4, M; ℝ⟯` on any 4-manifold `M` with `[A : AdmitsWrinkledOrBrokenLefschetzFibration M]`,
defined on `Φ⁻¹(b, C.embed y)` by `(bumpProfile M b * C.areaScale) * P.H (0, y)` and extended
smoothly by `0` outside `f ⁻¹' baseRegion` and `C.sourceOpen`. -/
noncomputable def liftPlanarHamiltonianTo4Manifold
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [A : AdmitsWrinkledOrBrokenLefschetzFibration M]
    {r₀ : ℝ} (P : CompactlySupportedPlanarHamiltonian r₀) :
    C^∞⟮𝓡 4, M; ℝ⟯

/-- Completeness of the Poisson-Hamiltonian vector field `(adaptedJacobianPoisson M).hamiltonianVectorField H`
on a compact 4-manifold `M`. -/
theorem isComplete_hamiltonianVectorField_adaptedJacobianPoisson
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
    [A : AdmitsWrinkledOrBrokenLefschetzFibration M]
    (H : C^∞⟮𝓡 4, M; ℝ⟯) :
    TauCeti.IsCompleteVectorField
      (TauCeti.timeDependentSuspensionField fun _ : ℝ ↦
        (adaptedJacobianPoisson M).hamiltonianVectorField H)

/-- Time-`1` flow diffeomorphism `M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M` generated by the Poisson-Hamiltonian vector
field `(adaptedJacobianPoisson M).hamiltonianVectorField H` on a compact 4-manifold `M`. -/
noncomputable def poissonHamiltonianTimeOneDiffeomorph
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
    [A : AdmitsWrinkledOrBrokenLefschetzFibration M]
    (H : C^∞⟮𝓡 4, M; ℝ⟯) :
    M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M

/-- Right-fold composition of the time-`1` Poisson-Hamiltonian flow diffeomorphisms for a finite
list of smooth Hamiltonians `Hs : List C^∞⟮𝓡 4, M; ℝ⟯`. -/
noncomputable def composePoissonHamiltonianTimeOneFlows
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
    [A : AdmitsWrinkledOrBrokenLefschetzFibration M] :
    List C^∞⟮𝓡 4, M; ℝ⟯ → (M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M)
  | [] => Diffeomorph.refl (𝓡 4) M ∞
  | H :: Hs => (composePoissonHamiltonianTimeOneFlows M Hs).trans
      (poissonHamiltonianTimeOneDiffeomorph M H)

/-- **Fundamental Leafwise-to-Poisson-Hamiltonian Time-`1` Flow Theorem**:
For every autonomous `P : CompactlySupportedPlanarHamiltonian r₀`, the time-`1` flow diffeomorphism
of `(adaptedJacobianPoisson M).hamiltonianVectorField (liftPlanarHamiltonianTo4Manifold M P)` equals
`leafwiseBumpDiffeomorphOfIsotopy M P.toDiskIsotopy`. -/
theorem poissonHamiltonianTimeOneDiffeomorph_liftPlanarHamiltonian_eq
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
    [A : AdmitsWrinkledOrBrokenLefschetzFibration M]
    {r₀ : ℝ} (P : CompactlySupportedPlanarHamiltonian r₀) (hP : P.IsAutonomous) :
    poissonHamiltonianTimeOneDiffeomorph M (liftPlanarHamiltonianTo4Manifold M P) =
      leafwiseBumpDiffeomorphOfIsotopy M P.toDiskIsotopy

/-- **Deliverable R5 (Unconditional Poisson-Hamiltonian Realization on `Sphere4`)**:
There exist a finite list of smooth Hamiltonians `Hs : List C^∞⟮𝓡 4, Sphere4; ℝ⟯` and a smooth
diffeomorphism `d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4` equal to the composition of the time-`1`
flows of the Poisson-Hamiltonian vector fields `s4AdaptedPoisson.hamiltonianVectorField H` (`H ∈ Hs`)
such that `d_bar` preserves `s4Fibration`, `s4AlignedPositiveVolume.Ω`, `s4AlignedPositiveVolume.μ`,
and `s4AdaptedPoisson`, and `IsTuringComplete ⇑d_bar`. -/
theorem exists_poisson_hamiltonian_realization_S4 :
    ∃ (Hs : List C^∞⟮𝓡 4, Sphere4; ℝ⟯)
      (d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4),
      d_bar = composePoissonHamiltonianTimeOneFlows Sphere4 Hs ∧
      s4Fibration ∘ ⇑d_bar = s4Fibration ∧
      SmoothBivector.IsPoissonMap s4AdaptedPoisson.toSmoothBivector
        s4AdaptedPoisson.toSmoothBivector d_bar d_bar.contMDiff ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff s4AlignedPositiveVolume.Ω =
        s4AlignedPositiveVolume.Ω ∧
      MeasureTheory.MeasurePreserving ⇑d_bar
        s4AlignedPositiveVolume.μ s4AlignedPositiveVolume.μ ∧
      IsTuringComplete ⇑d_bar ∧
      (⇑d_bar : Sphere4 → Sphere4) ≠ id
```
