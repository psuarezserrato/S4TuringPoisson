# MISSION DIRECTIVE: Lean 4 Formalization of Hamiltonian & Turing Complete Poisson Diffeomorphisms on Smooth 4-Manifolds

## 1. Mission Objective & Formal Deliverables

Formalize in **Lean 4** (`leanprover/lean4:v4.36.0`, downstream of `TauCeti` `v4.36.0` and `Mathlib4`) the theorems and intrinsic Poisson-geometric constructions of Pablo Suárez-Serrato, *"Hamiltonian and Turing complete flows on smooth 4-manifolds"* (`S4TCdiffeo-Aug-2026.tex`):

1. **Theorem 1 (`S4TuringPoisson.Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_S4`)**:
   Construct on the standard smooth 4-sphere $S^4$ (`Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1`) a generically rank-2, unimodular Poisson structure $\pi_f$ adapted to a smooth singular fibration $f : S^4 \to S^2$ with positive invariant volume form $\Omega \in \Omega^4(S^4)$, together with a $C^\infty$ diffeomorphism $\bar{d} : S^4 \simeq^\infty S^4$ such that:
   - $\bar{d}$ preserves every symplectic leaf of $\pi_f$ ($f \circ \bar{d} = f$) and acts as an area-preserving symplectomorphism on regular $S^2$ leaves,
   - $\bar{d}$ preserves the global unimodular volume form ($\bar{d}^*\Omega = \Omega$) and satisfies `MeasureTheory.MeasurePreserving ⇑d̄ μ_Ω μ_Ω` for the induced positive finite Borel volume measure $\mu_\Omega$ on $S^4$, and
   - $\bar{d}$ is Turing complete (`IsTuringComplete ⇑d̄`), yielding algorithmic undecidability of forward-orbit reachability into constructible open sets on $S^4$.
   *(Also export the concise projection `exists_turingComplete_volumePreserving_diffeomorph_S4` matching Theorem 1's prose statement.)*

2. **Corollary 2 (`S4TuringPoisson.Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_fourManifold`)**:
   Prove that every closed, connected, oriented, $C^\infty$ 4-manifold $M$ admitting a broken Lefschetz or wrinkled fibration $f : M \to S^2$ (`[AdmitsWrinkledOrBrokenLefschetzFibration M]`) carries a compatible generically rank-2 unimodular Poisson structure $\pi_f$ and a smooth, leaf-preserving, volume-preserving, Turing complete diffeomorphism $\bar{d} : M \simeq^\infty M$.

3. **Kernel & Axiom Standard**:
   Zero `sorry`, zero `admit`, and zero custom `axiom` declarations across all files. Running `#print axioms` on every theorem in `S4TuringPoisson/Main.lean` must output only a subset of `{propext, Classical.choice, Quot.sound}`. External upstream literature inputs (`CMPP21` $C^\infty$ disk smoothing if Stretch Track `@cmpp-smoothing` has not yet closed, and `Gay–Kirby / Lekili` wrinkled fibration existence on general closed oriented 4-manifolds) must be expressed strictly as explicit Lean `class` hypotheses, never as global `axiom`s.

---

## 2. Antigravity Execution Modes, Worktrees & Model Pinning

- **If running under `/teamwork`**:
  - Select Execution Path: `Math / Proof (Large Team)` and **Integrity Mode: `development`** (so `TauCeti` and `Mathlib` dependencies are allowed while `Auditor` validates real build/axiom outputs and blocks facades).
  - `Sentinel` and rotating `Project Orchestrators` execute Milestones M0 through M5 sequentially/in-parallel, clearing `Critic`, `Challenger`, `Auditor`, and `Success Auditor` at every milestone boundary.

- **If running under `/swarm`**:
  - **Per-Worker Isolated Git Worktrees**: Assign every active worker its own isolated repository working copy / Git worktree so parallel edits and `lake build` invocations never collide.
  - **Model Assignments**:
    - Pin `@coordinator`, `@verifier-geom`, and `@verifier-comp` to **Gemini 4 Carbon**.
    - Pin `@poisson-core`, `@fibration-s4`, `@turing-shift`, `@leaf-extension`, and `@cmpp-smoothing` to **Gemini 4 Carbon** during core proof construction; hot-swap waiting workers to **Gemini 4 Argon** for routine lint, docstring, and import cleanup.
    - Keep `@monitor` asleep at zero token cost unless all active workers stall.

---

## 3. Phase 0 Read-Only Explorer Audit

Before freezing `S4TuringPoisson/Interfaces.lean`, run two read-only Explorer sweeps and post the exact API signatures to the Shared Board / Progress Artifact:

1. **`@explorer-upstream` (`TauCeti v4.36.0` & `Mathlib4` Signature Inventory)**:
   - Use `lean_local_search` and `rg` inside `.lake/packages/TauCeti` and `.lake/packages/mathlib` to record exact declaration names, namespaces, and universe levels for:
     - `Metric.sphere` smooth manifold instances and `stereographic'` (`Mathlib.Geometry.Manifold.Instances.Sphere`)
     - `Diffeomorph` and `IsLocalDiffeomorph.diffeomorphOfBijective` (`Mathlib.Geometry.Manifold.LocalDiffeomorph`)
     - `ContDiffBump` (`Mathlib.Analysis.Calculus.BumpFunction.Basic`) and `SmoothBumpCovering` (`Mathlib.Geometry.Manifold.PartitionOfUnity`)
     - `MeasureTheory.MeasurePreserving` (`Mathlib.Dynamics.Ergodic.MeasurePreserving`) and `lintegral_abs_det_fderiv_eq_addHaar_image` (`Mathlib.MeasureTheory.Function.Jacobian`)
     - `Turing.TM0.Machine`, `Turing.TM0.Cfg`, `Turing.Tape`, `Turing.TM0.step`, and `Turing.TM0.Reaches` (`Mathlib.Computability.TuringMachine.PostTuringMachine`)
     - `TauCeti.SmoothForm`, `TauCeti.mextDeriv`, wedge products, pullbacks, and Cartan's magic formula (`TauCeti/Geometry/Manifold/DifferentialForm/`)
     - `TauCeti.SmoothTwoForm`, `IsSymplectic`, `exists_darbouxChart`, `liouvilleMeasure`, and `measurePreserving_globalFlowDiffeomorph_liouvilleMeasure` (`TauCeti/Geometry/Symplectic/Manifold/`)
     - `TauCeti.Geometry.Manifold.Boundary.Charts` and collar gluing utilities.
   - Verify whether time-dependent compactly supported Hamiltonian isotopies on `ℝ²` / `S²` are directly constructible from `TauCeti`'s global flow API; if a time-dependent Seeley ODE flow lemma is needed, inspect a shallow clone of `https://github.com/qinz1yang/differential-geometry.git` (`rev = "v0.1.5"`, Apache-2.0) to vendor only the minimal self-contained flow file under `S4TuringPoisson/Vendor/DifferentialGeometry/` with full Apache-2.0 `NOTICE` attribution.

2. **`@explorer-local` (Local `gromov-genus0-compactness` & `poissongeometry` Audit)**:
   - Search sibling/home paths (`../gromov-genus0-compactness`, `~/gromov-genus0-compactness`, `../poissongeometry`) for the author's local repositories.
   - Record any reusable $S^2 \cong \mathbb{CP}^1$ stereographic chart helpers, disk-into-sphere smooth embeddings $D^2 \hookrightarrow S^2$, area-form conventions, and symbolic coordinate test cases for Equations (3)–(5). If not mounted in the workspace, note this on the board and proceed via `Mathlib.Geometry.Manifold.Instances.Sphere` and `TauCeti.SmoothTwoForm`.

---

## 4. Exclusive Directory Ownership Roster

| Agent Handle | Role & Model Tier | Exclusive Owned Paths | Prohibited Paths |
| :--- | :--- | :--- | :--- |
| `@coordinator` | Coordinator (Gemini 4 Carbon) | `S4TuringPoisson/Interfaces.lean`, `S4TuringPoisson.lean` | Worker proof subdirectories |
| `@poisson-core` | Worker 1 (Gemini 4 Carbon) | `S4TuringPoisson/Poisson/*.lean` | `Fibration/`, `Dynamics/`, `Extension/`, `Smoothing/` |
| `@fibration-s4` | Worker 2 (Gemini 4 Carbon) | `S4TuringPoisson/Fibration/*.lean` | `Poisson/`, `Dynamics/`, `Extension/`, `Smoothing/` |
| `@turing-shift` | Worker 3 (Gemini 4 Carbon) | `S4TuringPoisson/Dynamics/*.lean` | `Poisson/`, `Fibration/`, `Extension/`, `Smoothing/` |
| `@leaf-extension` | Worker 4 (Gemini 4 Carbon) | `S4TuringPoisson/Extension/*.lean`, `S4TuringPoisson/Main.lean` | Modifying `Interfaces.lean` without `@coordinator` |
| `@cmpp-smoothing` | Worker 5 — Stretch (Gemini 4 Carbon) | `S4TuringPoisson/Smoothing/*.lean` | Blocking M4/M5 main-branch merges |
| `@verifier-geom` | Verifier (Gemini 4 Carbon) | Read-only + `S4TuringPoisson/Checks/GeomChecks.lean` | Editing production modules |
| `@verifier-comp` | Verifier (Gemini 4 Carbon) | Read-only + `S4TuringPoisson/Checks/CompChecks.lean` | Editing production modules |

---

## 5. Milestone Blueprint & Mathematical Specifications

### Milestone M0: Shared Type Contracts (`S4TuringPoisson/Interfaces.lean`)
`@coordinator` writes `Interfaces.lean` (compiling cleanly with zero `sorry`) immediately after Phase 0:

1. **`PositiveVolumeForm I M` & Induced Measure $\mu_\Omega$**:
   - Bundles a smooth nowhere-vanishing top form $\Omega \in \Omega^n(M)$ on a closed oriented smooth manifold $M$ together with its positive finite Borel measure $\mu_\Omega : \text{Measure } M$ satisfying `IsFiniteMeasure μ_Ω`, `∀ U : Opens M, U.1.Nonempty → 0 < μ_Ω U.1`, and the bridge obligation: any smooth diffeomorphism $\Phi : M \simeq^\infty M$ with $\Phi^*\Omega = \Omega$ satisfies `MeasureTheory.MeasurePreserving ⇑Φ μ_Ω μ_Ω`.

2. **Decoupled Anti-Vacuity `IsTuringComplete` Predicate**:
   - Built on `Turing.TM0.Machine Γ Λ`, `Turing.Tape Γ`, and `Turing.TM0.step` for finite alphabets/states (`Fintype Γ`, `Fintype Λ`, `DecidableEq`, `Inhabited`).
   - Define `HaltsWithWindow M t k w` (`k : ℕ`, `w : Set.Icc (-k : ℤ) k → Γ`) asserting finite-step termination from `{ q := default, Tape := t }` at a configuration `c` (`Turing.TM0.step M c = none`) whose tape symbol at each offset `i ∈ [-k, k]` equals `w ⟨i, hi⟩`.
   - Define `IsTuringComplete {X : Type*} [TopologicalSpace X] (φ : X → X) : Prop` requiring:
     - `encodePoint : FinTM0 → FinSupportedTape → X` *(depending ONLY on machine and input tape, equipped with computable rational chart approximations)*, and
     - `encodeOpen : (M : FinTM0) → (k : ℕ) → Window M k → TopologicalSpace.Opens X` *(depending ONLY on machine and target output window, independent of `t`, with `(encodeOpen M k w).1.Nonempty`)*,
     such that for every `M`, `t`, `k`, `w`:
     $$(\exists n : \mathbb{N},\; \varphi^{[n]}(\text{encodePoint } M\; t) \in \text{encodeOpen } M\; k\; w) \iff \text{HaltsWithWindow } M\; t\; k\; w.$$

3. **Disk Isotopy Interface (`HasTuringCompleteAreaPreservingDiskIsotopy`)**:
   - Packages a smooth map $d : \mathbb{R} \times \mathbb{R}^2 \to \mathbb{R}^2$ and radius $r_0 \in (0, 1)$ such that:
     - for every $t \in \mathbb{R}$, $y \mapsto d(t, y)$ is a $C^\infty$ diffeomorphism of $\mathbb{R}^2$ equal to `id` outside `Metric.ball 0 r_0`,
     - $d(0, y) = y$ for all $y \in \mathbb{R}^2$,
     - $\det (\text{fderiv } \mathbb{R} (y \mapsto d(t, y)) y) = 1$ (equivalently $(d_t)^*(dy_1 \wedge dy_2) = dy_1 \wedge dy_2$) for all $(t, y)$, and
     - the restriction of $y \mapsto d(1, y)$ to `Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1` satisfies `IsTuringComplete`.

---

### Milestone M1 (Parallel Track 1 — `@poisson-core`): Unimodular Jacobian–Poisson Geometry (`S4TuringPoisson/Poisson/`)

1. **`BivectorAndModular.lean`**:
   - Formalize smooth Poisson brackets $\{ \cdot, \cdot \}_\pi : C^\infty(M) \times C^\infty(M) \to C^\infty(M)$ ($\mathbb{R}$-bilinear, skew-symmetric, Leibniz derivation in each argument, Jacobi identity), the anchor map $\#_\pi : T^*M \to TM$, Hamiltonian vector fields $X_h$, the Koszul 1-form bracket $[\alpha, \beta]_\pi$, Lichnerowicz 1-cocycles, Weinstein's modular vector field $Y^\Omega$ defined via $\mathcal{L}_{X_h}\Omega = (Y^\Omega h)\,\Omega$, invariance of $[Y^\Omega] \in H^1(M, \pi)$ under positive density rescaling $\Omega \mapsto a\,\Omega$, and `IsUnimodularPoisson M π`.

2. **`JacobianPoisson.lean`**:
   - Formalize `GSV15` Theorem 2.6 and unimodularity (`BV21`): for any smooth map $f : M^4 \to \Sigma^2$ between oriented smooth 4- and 2-manifolds with positive volume forms $\Omega \in \Omega^4(M^4)$ and $\mu_\Sigma \in \Omega^2(\Sigma^2)$, define $\{g, h\}_{\pi_f}$ globally by $\{g, h\}_{\pi_f}\,\Omega = dg \wedge dh \wedge f^*\mu_\Sigma$.
   - Prove skew-symmetry, Leibniz derivation, Jacobi identity, and global unimodularity ($\mathcal{L}_{X_h}\Omega = d(dh \wedge f^*\mu_\Sigma) = -dh \wedge f^*(d\mu_\Sigma) = 0$ since $\dim \Sigma^2 = 2$, so $Y^\Omega \equiv 0$) across all of $M^4$ including $\mathrm{Crit}(f)$.
   - Prove that on $M^4 \setminus \mathrm{Crit}(f)$, $\mathrm{rank}(\pi_f) = 2$ and $\mathrm{Im}(\#_{\pi_f}) = \ker(df)$.

3. **`SingularCircleNormalForm.lean`**:
   - Formalize Equations (3)–(5) of `S4TCdiffeo-Aug-2026.tex` (`GSV15` Propositions 3.2 & 3.3) on $S^1 \times B^3$:
     - Verify that $\pi = k(\theta, x_1, x_2, x_3)(x_1 \partial_{x_2}\wedge\partial_{x_3} + x_2 \partial_{x_1}\wedge\partial_{x_3} - x_3 \partial_{x_1}\wedge\partial_{x_2})$ arises as the Jacobian–Poisson bivector of $(\theta, -x_1^2 + x_2^2 + x_3^2)$ (hence satisfies Jacobi for every smooth non-vanishing $k$ and has Casimirs $\theta$ and $-x_1^2 + x_2^2 + x_3^2$).
     - Prove that the non-orientable normal-bundle involution $i(\theta, x_1, x_2, x_3) = (\theta + \pi, -x_1, -x_2, x_3)$ is a Poisson map whenever $k \circ i = k$.

---

### Milestone M2 (Parallel Track 2 — `@fibration-s4`): Singular Fibrations on $S^4$ and Wrinkled 4-Manifolds (`S4TuringPoisson/Fibration/`)

1. **`LocalSingularModels.lean`**:
   - Formalize the local normal forms for indefinite quadratic folds (Eq. 2: $(y_1, y_2, y_3, t) \mapsto (y_1^2 - \frac{1}{2}(y_2^2 + y_3^2), t)$, proving $\mathrm{Crit} = \{y_1 = y_2 = y_3 = 0\}$), Lefschetz points, and wrinkled cusps (`Lekili 2009`, `ST16`), and define `BrokenLefschetzFibration M Σ` and `WrinkledFibration M Σ`.

2. **`S4Fibration.lean`**:
   - Construct an explicit, `sorry`-free smooth singular fibration $f_{S^4} : S^4 \to S^2$ with an open regular disk $B \subset S^2 \setminus f_{S^4}(\mathrm{Crit}(f_{S^4}))$ and an explicit smooth trivialization $\Phi : f_{S^4}^{-1}(B) \simeq^\infty B \times S^2$ (for example via $(x_0, x_1, y) \in S^4 \subset \mathbb{R}^2 \times \mathbb{R}^3$ projecting $(x_0, x_1)$ through `stereographic'.symm` onto $S^2$ with explicit fiber normalization $y / \sqrt{1 - x_0^2 - x_1^2} \in S^2$ over $\|b\| < 1/2$, plus the local ADK equatorial cobordism model $W$ of Eq. 2 showing the $S^2$-to-$T^2$ fiber transition).

3. **`WrinkledGeneral4Manifold.lean`**:
   - Define typeclass `AdmitsWrinkledOrBrokenLefschetzFibration M` packaging the `Gay–Kirby (2007)` / `Lekili (2009)` existence of a `WrinkledFibration M S²` with nonempty closed oriented regular fiber $F$.
   - Prove using `TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart` that **every** nonempty closed oriented surface $(F, \omega_F)$ admits a smooth symplectic disk embedding $(B(0, 1) \subset \mathbb{R}^2, c\,\omega_{\mathrm{std}}) \hookrightarrow (F, \omega_F)$, supporting any fiber genus $g \ge 0$ without topological genus-reduction moves.

---

### Milestone M3 (Parallel Track 3 — `@turing-shift` & Stretch `@cmpp-smoothing`): Generalized Shifts, Undecidability & Disk Smoothing (`S4TuringPoisson/Dynamics/` & `Smoothing/`)

1. **`GeneralizedShift.lean` (`@turing-shift`)**:
   - Formalize Moore's generalized shifts (`Moore 1990`, `CMPP21` Section 4) on `ℤ → A`, prove **`CMPP21` Proposition 4.4** conjugating any `TM0` machine (and bijectively any reversible machine) to a generalized shift on $D_F = D_G = \{-1, 0, 1\}$, and construct the injective base-$(2|A|-1)$ square Cantor embedding $(ℤ \to A) \hookrightarrow D^2$ mapping cylinder blocks to pairwise disjoint open rectangles.

2. **`UndecidabilityAndTransfer.lean` (`@turing-shift`)**:
   - **Halting Undecidability Transfer**: Prove from Mathlib's computability library that for any `IsTuringComplete φ`, point-to-open-set orbit reachability is algorithmically undecidable.
   - **Fiber-to-4-Manifold Transfer Lemma**: Given an open embedding $\Psi : B \times U_{\text{disk}} \hookrightarrow M$, $c \in B_0 \subset B$ (`IsOpen B_0`), and $\bar{d}(\Psi(b, y)) = \Psi(b, d(y))$ on $B_0 \times U_{\text{disk}}$, prove $\bar{d}^{[n]}(\Psi(c, p)) = \Psi(c, d^{[n]}(p))$ for all $n \in \mathbb{N}$ and deduce `IsTuringComplete d → IsTuringComplete d̄` with $\bar{p} = \Psi(c, p)$ and $\overline{\mathcal{O}} = \Psi '' (B_0 \times \mathcal{O})$.

3. **`DiskSmoothing.lean` (Stretch Worker `@cmpp-smoothing`)**:
   - Construct an unconditional instance `instHasTuringCompleteAreaPreservingDiskIsotopy` by generating each finite Cantor-block rotation $\rho$, sector swap $\sigma$, and area-preserving circulation stretch (Figures 1 and 2 of `S4TCdiffeo-Aug-2026.tex`) as time-$t$ flows of compactly supported smooth Hamiltonians $H_i \in C_c^\infty(D^2)$ via `TauCeti`'s symplectic flow API. *(Non-blocking: if still in progress when M4 finishes, M5 exports both typeclass-parameterized and conditional specializations cleanly with zero `sorry`.)*

---

### Milestone M4 (Convergence Track — `@leaf-extension`): Aligned Volume & Leafwise Bump Isotopy Lift (`S4TuringPoisson/Extension/`)

1. **`AlignedUnimodularVolume.lean`**:
   - Construct the convex-combination global positive 4-form $\Omega = (1 - \chi \circ f)\,\Omega_0 + (\chi \circ f)\,\Phi^*(p_F^*\omega_F \wedge p_B^*\mu_B)$ on $M^4$ (`supp(ρ) ⊂ int(χ⁻¹(1))`, `supp(χ) ⊂ B`), proving $\Omega$ is globally positive, $\pi_f = \pi_{f, \Omega, \mu_{S^2}}$ is unimodular with invariant volume $\Omega$, and Equation (1) ($\Omega = \Phi^*(p_F^*\omega_F \wedge p_B^*\mu_B)$) holds over $\mathrm{supp}(\rho)$.

2. **`BumpIsotopyLift.lean`**:
   - Lift $d_t : D^2 \to D^2$ via Darboux/stereographic disk embedding to $d_t^F : F \to F$, choose $\rho : B \to [0,1]$ via `ContDiffBump` (`ρ ≡ 1` on $\overline{B_0}$), and define $\bar{d}(\Phi^{-1}(b, y)) = \Phi^{-1}(b, d_{\rho(b)}^F(y))$ on $f^{-1}(B)$ and `id` outside $f^{-1}(B)$.
   - Prove: (a) $\bar{d}$ and $\bar{d}^{-1}$ form a smooth global `Diffeomorph` of $M^4$; (b) $f \circ \bar{d} = f$, preserving every symplectic leaf of $\pi_f$ and leafwise area forms; and (c) $\bar{d}^*\Omega = \Omega$ via block-triangular wedge annihilation ($\det D\bar{d}(b,y) = \det D_y(d_{\rho(b)}^F)(y) = 1$), yielding `MeasureTheory.MeasurePreserving ⇑d̄ μ_Ω μ_Ω`.

---

### Milestone M5 (Synthesis — `@leaf-extension` + All Gates): `S4TuringPoisson/Main.lean`

Export `exists_turingComplete_volumePreserving_poissonDiffeomorph_S4`, `exists_turingComplete_volumePreserving_diffeomorph_S4`, `exists_turingComplete_volumePreserving_poissonDiffeomorph_fourManifold`, and `undecidable_orbit_reachability_S4`.

---

## 6. Adversarial Verification Rubric (`@verifier-geom`, `@verifier-comp` & Teamwork Gates)

Every milestone PR/branch is **blocked** unless all six checks pass with ground-truth command output:

1. **Clean Build & Linter Gate (`Auditor`)**: `lake build` succeeds with zero errors and zero `sorry` warnings.
2. **Transitive Axiom Gate (`Auditor`)**: `#print axioms` on every theorem in `Main.lean` lists **only** `{propext, Classical.choice, Quot.sound}`.
3. **Non-Zero Poisson Bracket Witness (`Challenger` — `GeomChecks.lean`)**: Instantiate `JacobianPoisson` on $(x_1, x_2, x_3, x_4) \mapsto (x_1, x_2)$ on $\mathbb{R}^4$ and prove `{x₃, x₄}_{π_f} = 1 ≠ 0`, ruling out junk-value zero-bivector bugs.
4. **Singular-to-Regular Witness (`Challenger` — `GeomChecks.lean`)**: Instantiate Eq. (2) and prove $(0,0,0,t) \in \mathrm{Crit}$ while $(1,0,0,t) \notin \mathrm{Crit}$ has rank-2 $\pi_f$.
5. **Nontrivial Volume Measure Witness (`Challenger` — `GeomChecks.lean`)**: Prove on $S^4$ that `0 < μ_Ω (Metric.ball p (1/2))` and `μ_Ω (Metric.ball p (1/2)) < μ_Ω Set.univ`, ruling out zero or Dirac measures.
6. **Halting Separation & Foliation Tangency Witness (`Challenger` — `CompChecks.lean`)**: Exhibit concrete 2-state `TM0` machines `M_halt` and `M_loop`, proving `∃ n, d̄^[n] p_halt ∈ U_halt`, `∀ n, d̄^[n] p_loop ∉ U_loop`, `f ∘ d̄ = f`, and `⇑d̄ ≠ id`.