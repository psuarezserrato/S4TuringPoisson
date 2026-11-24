# MISSION DIRECTIVE (LEKILI): Formalizing Wrinkled Fibrations & Discharging `[AdmitsWrinkledOrBrokenLefschetzFibration M]`

Repo: `/Users/pablosuarez/Desktop/S4TuringPoisson` (Lean `v4.36.0`, Mathlib + `TauCeti v4.36.0`, companion `../Turing-recursive`).
Origin: Independent audit (`cb2b631`, 23 November 2026) Finding **F1** and blueprint nodes `ext_fibration_existence` / `cor_paper_all` in [`blueprint/src/content.tex`](blueprint/src/content.tex).

---

## §0. Audit Origin & Mathematical Anatomy

In `S4TuringPoisson/Main.lean`, all headline theorems on $S^4$ (`exists_turingComplete_volumePreserving_poissonDiffeomorph_S4`, `exists_turingComplete_volumePreserving_diffeomorph_S4`, `undecidable_orbit_reachability_S4`, and `exists_poisson_hamiltonian_realization_S4`) are **unconditional** (`0` binders). Only **Corollary 2** retains a non-manifold geometric typeclass hypothesis:

```lean
theorem exists_turingComplete_volumePreserving_poissonDiffeomorph_fourManifold
    (M : Type*) ... [A : AdmitsWrinkledOrBrokenLefschetzFibration M] : ...
```

Currently, `AdmitsWrinkledOrBrokenLefschetzFibration` has a global instance **only** for `Sphere4` (`instAdmitsWrinkledOrBrokenLefschetzFibrationSphere4` in `S4TuringPoisson/Fibration/WrinkledGeneral4Manifold.lean`).

### Three Levels of Global Fibration Constraints

1. **Unconstrained `WrinkledFibration`** (`Fibration/LocalSingularModels.lean`, L1033):
   Packages a smooth map $f : M^4 \to N^2$, an open disk $B \subseteq N$ of regular values, and a smooth product trivialization $f^{-1}(B) \simeq_m B \times F$ with compact nonempty fiber $F$. It places **no** local normal-form constraint on critical points $p \in \mathrm{Crit}(f)$.
2. **`BrokenLefschetzFibration`** (`LocalSingularModels.lean`, L1180):
   Extends `WrinkledFibration` with:
   $$\forall p \in \mathrm{Crit}(f),\quad \mathrm{IsRealLefschetzAt}(f, p) \lor \mathrm{IsIndefiniteFoldAt}(f, p).$$
   No definite folds and no cusps occur; critical loci are isolated Lefschetz points and $1$-dimensional circles of indefinite folds.
3. **`PurelyWrinkledFibration`** (Lekili 2009, *Geom. Topol.* **13**, 277–318; Suárez-Serrato–Torres Orozco 2016):
   Extends `WrinkledFibration` with:
   $$\forall p \in \mathrm{Crit}(f),\quad \mathrm{IsIndefiniteFoldAt}(f, p) \lor \mathrm{IsWrinkledCuspAt}(f, p).$$
   Every singularity is modeled either on Eq. (2) indefinite quadratic folds `(y₁, y₂, y₃, t) ↦ (y₁² - (y₂² + y₃²)/2, t)` or wrinkled cusps `(t, x₁, x₂, x₃) ↦ (t, x₁³ - 3 t x₁ + x₂² - x₃²)`, with **zero** definite folds (`IsIndefiniteFoldAt` already defined in `LocalSingularModels.lean` L952; `IsWrinkledCuspAt` already defined alongside `wrinkledCuspMap`).

### Crucial Simplification Already Earned by `AlignedUnimodularVolume.lean`

By inspection of `AdmitsWrinkledOrBrokenLefschetzFibration` (`WrinkledGeneral4Manifold.lean` L177–235), discharging the typeclass for a closed oriented smooth 4-manifold `(M, Ω_M)` requires:
- a `WrinkledFibration (𝓡 4) M (𝓡 2) Sphere2 F` (regular disk $B \subset S^2$, compact fiber $F$),
- a positive area 2-form $\omega_F$ on the **single compact model fiber** $F$, and
- a positive co-orientation $c(u) > 0$ matching $\Phi^*(p_F^*\omega_F \wedge p_B^*\mu_{S^2}) = c \cdot \Omega_M$ over $f^{-1}(B)$.

Crucially, `S4TuringPoisson` **does not require a global closed 2-form on all of $M$** (since `AlignedUnimodularVolume` splices the product form into $\Omega_M$ via a radial cutoff inside $B$); hence Thurston's global homological Lefschetz trick is not needed on $M$.

---

## §1. Deliverables (`L-R1` – `L-R5`) & Two Complementary Tracks

### `L-R1`: Purely Wrinkled Interface (`S4TuringPoisson/Fibration/PurelyWrinkled.lean`)
- Define `PurelyWrinkledFibration` (`extends WrinkledFibration I_M M I_B Base Fiber` constraining `criticalPoints I_M I_B toFun` to `IsIndefiniteFoldAt` $\lor$ `IsWrinkledCuspAt`).
- Prove `AdmitsWrinkledOrBrokenLefschetzFibration.ofPurelyWrinkled`, mirroring `AdmitsWrinkledOrBrokenLefschetzFibration.ofBrokenLefschetz`.

### `L-R2`: Lekili (2009) §3–4 Explicit Planar Moves (`S4TuringPoisson/Fibration/LekiliMoves.lean`)
Formalize the explicit smooth polynomial homotopies $f_s : B^4 \to \mathbb{R}^2$ ($s \in [0, 1]$), boundary stability ($f_s = f_0$ near $\partial B^4$ via cutoff), exact `mfderiv` critical-locus classification, and cusp/fold normal forms for all four Lekili moves:
1. **Wrinkling a Lefschetz singularity** (Lekili 2009 Prop. 4 / §3.1):
   $(z_1, z_2) \mapsto z_1^2 + z_2^2 + s\,\overline{z}_1$ perturbs an isolated real Lefschetz point at $s=0$ into a regular $3$-cusp astroid circle of indefinite folds for $s > 0$.
2. **Birth / death of a $2$-cusp wrinkle** (Eliashberg–Mishachev embryo):
   $(t, x_1, x_2, x_3) \mapsto (t,\; x_1^3 + 3(t^2 - s)x_1 + x_2^2 - x_3^2)$ creates a compact $2$-cusp wrinkle inside $t^2 < s$.
3. **Cusp-merge move**: joins two opposite cusps across an indefinite-fold arc into two disjoint smooth indefinite-fold arcs.
4. **Flip / swallowtail move**: introduces a pair of cusps along an indefinite-fold arc via $(t, x_1, x_2, x_3) \mapsto (t,\; x_1^4 + t x_1^2 + \dots)$.
- Combine Move 1 with chart gluing over compactly many isolated Lefschetz points to prove the **Broken-to-Wrinkled Smoothing Theorem**: every `BrokenLefschetzFibration` on a compact 4-manifold deforms (preserving its regular region $B$ and fiber $F$) to a `PurelyWrinkledFibration`.

### `L-R3` (Track B — Fast Unconditional Closure of Current Corollary 2, ~1,200 LOC)
- Construct `AdmitsWrinkledOrBrokenLefschetzFibration.ofOrientedCompactFourManifold`: given any nonempty compact Hausdorff oriented smooth 4-manifold $M$ with `V_M : PositiveVolumeForm (𝓡 4) M`, extract an orientation-preserving coordinate ball chart $\varphi : B^4(0, 2) \hookrightarrow M$, compose a bumped local submersion inside $B^4(0, 1.5)$ agreeing with `s4Fibration` on $B^4(0, 1)$ and collapsing outside $B^4(0, 1.5)$ to `s2SouthPole ∉ s4BaseRegion`, and pull back a positive fiber form.
- Export `exists_turingComplete_volumePreserving_poissonDiffeomorph_closedOrientedFourManifold` requiring **only** `[CompactSpace M] [T2Space M] [Nonempty M] (V_M : PositiveVolumeForm (𝓡 4) M)` (orientation-compatible).
- **Honesty Label**: Explicitly documented as closing `cor_paper_all` for the unconstrained `WrinkledFibration` interface using a local definite-fold chart map; kept strictly separate from **Track A** (`L-R4`) so it never masquerades as Lekili's or Gay–Kirby's theorem.

### `L-R4` (Track A — Full Gay–Kirby / Saeki / Lekili Theorem + Explicit ADK $S^4$ Upgrade)
- **`L-R4a` (Explicit ADK $S^4$ Fibration, ~2,500 LOC)**:
  Construct `s4BrokenLefschetzFibration : BrokenLefschetzFibration (𝓡 4) Sphere4 (𝓡 2) Sphere2 Sphere2` realizing Auroux–Donaldson–Katzarkov (2005) via the round-handle decomposition $S^4 = (S^1 \times B^3) \cup (D^2 \times S^2)$ with non-trivial `SO(3)` framing twist, $T^2$ fibers over $D_-$, $S^2$ fibers over $D_+$, and single indefinite-fold equator $S^1$. Applying `L-R2` yields an explicit `PurelyWrinkledFibration` on `Sphere4` (resolving Finding **F2** too).
- **`L-R4b` (General Closed Oriented 4-Manifolds, ~6,000–9,000 LOC)**:
  Prove unconditional existence of a `PurelyWrinkledFibration` on every closed oriented connected smooth 4-manifold $M$:
  1. Smooth map $M \to S^2$ deformed via 2-jet parametric transversality (`Thom` / `Sard`) into a generic Morin map (definite folds, indefinite folds, cusps).
  2. **Saeki (2006) / Gay–Kirby (2007) definite-fold elimination**: flip/unsink definite fold components across regular arcs to eliminate all definite folds while preserving orientability of fibers.
  3. **Regular-disk selection & Ehresmann trivialization**: apply compact proper-submersion Ehresmann trivialization over a nonempty regular disk $B \subset S^2$ (note: fiber connectedness guarantees nonempty compact oriented surface $F$).
  4. Apply `L-R1` to discharge `Nonempty (PurelyWrinkledFibration ...)` and `AdmitsWrinkledOrBrokenLefschetzFibration M` unconditionally on every closed oriented smooth 4-manifold $M$.

### `L-R5` (Blueprint 100% Green Closure)
- Wire `L-R1`–`L-R4` into [`blueprint/src/content.tex`](blueprint/src/content.tex), discharging the two remaining unformalized nodes (`ext_fibration_existence` and `cor_paper_all`), and re-run `build_dep_graph.py --require-all-green` + `verify_blueprint.py audit` (`50/50` green, `0 sorryAx`).

---

## §2. Prerequisites in Mathlib & `TauCeti`

| Prerequisite | Current Availability | Required Extension |
|---|---|---|
| Ehresmann proper-submersion trivialization theorem | Partial flow/ODE engine in `TauCeti/Geometry/Manifold/Flow` | Horizontal lift of radial disk vector field via Riemannian/ambient metric splitting + flow integrability on compact fibers (`~700 LOC`) |
| Orientation-preserving atlas & connected-sum / handlebody charts on 4-manifolds | Smooth charts in Mathlib `ChartedSpace`, `IsManifold`; volume positivity in `Interfaces.lean` | Smooth radial isotopy / Palais disk-chart normalization (`~400 LOC`, shared by Track B and Track A) |
| Parametric Sard theorem & 2-jet transversality on compact manifolds | `ContMDiff`, `mfderiv`, Baire category in Mathlib; iterated jets in `TauCeti` | `2`-jet bundle section & finite-dimensional Sard + Thom transversality for maps $M^4 \to S^2$ (`~2,000 LOC`, Track A `L-R4b` only) |
| `IsIndefiniteFoldAt` & `IsWrinkledCuspAt` predicates | Already formalized in `Fibration/LocalSingularModels.lean` (M2.1) | Direct reuse (no new definitions needed) |

---

## §3. Milestone Wave Plan & Effort Estimates

| Wave | Milestone | Module Target | Deliverables | Est. LOC | Track |
|---|---|---|---|---:|---|
| **W1** | `LW1` | `Fibration/PurelyWrinkled.lean` | `L-R1` interface & `ofPurelyWrinkled` | ~300 | Shared |
| **W1** | `LW2` | `Fibration/ClosedManifoldLocal.lean` | `L-R3` (`ofOrientedCompactFourManifold` + `cor_paper_all` closure) | ~1,200 | **Track B** (fast path) |
| **W2** | `LW3` | `Fibration/LekiliMoves.lean` | `L-R2` explicit polynomial homotopies & Broken $\to$ Wrinkled theorem | ~2,200 | **Track A** |
| **W2** | `LW4` | `Fibration/ADKS4Fibration.lean` | `L-R4a` explicit ADK indefinite-fold fibration on `Sphere4` | ~2,500 | **Track A** (`F2` upgrade) |
| **W3** | `LW5` | `Fibration/Ehresmann.lean`, `Fibration/JetTransversality.lean` | Ehresmann trivialization + Morin 2-jet transversality | ~3,000 | **Track A** |
| **W4** | `LW6` | `Fibration/SaekiElimination.lean`, `Fibration/GeneralExistence.lean` | `L-R4b` definite-fold elimination + unconditional Corollary 2 | ~3,500 | **Track A** |
| **W5** | `LW7` | `blueprint/src/content.tex`, `report/`, `AUDIT.md` | `L-R5` (`50/50` green blueprint + kernel audit) | ~200 | Final |

---

## §4. Verification Gates (`G1`–`G8`) & Anti-Vacuity Criteria

All milestones follow `.agents/rules/lean-integrity.md` (`LEAN_NUM_THREADS=2 lake build --wfail`, max 1 active Lean worker, 24 GB RAM guardrails `< 10240M` swap, local `gemma4:12B` routing for `-- tier: T0`):
- **G1 Build & Lint**: `0` warnings/errors, `<= 100` cols, `100%` docstrings, `#lint` `0` errors.
- **G2 Kernel Axioms**: `0` forbidden tokens (`sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `native_decide`, `opaque`, `skipKernelTC`, `maxHeartbeats`), `leanchecker` replay pass, every declaration strictly `⊆ {propext, Classical.choice, Quot.sound}`.
- **G3 Statement Freeze**: Never weaken `BrokenLefschetzFibration`, `IsIndefiniteFoldAt`, `IsRealLefschetzAt`, `IsWrinkledCuspAt`, or `IsTuringComplete`.
- **G4 Transitive Wiring**: `#audit_wiring` confirms Track A uses `LekiliMoves` + `SaekiElimination` + `Ehresmann` (never bypassing via unconstrained definite folds!).
- **G5 Anti-Vacuity (CRITICAL for Lekili & ADK)**:
  1. **Definite-Fold Exclusion Witness**: Construct a definite fold (`s4Fibration` on `Sphere4`) and **prove** it does *not* satisfy `IsIndefiniteFoldAt` or `IsWrinkledCuspAt` (Hessian index / signed eigenvalue count obstruction), proving `PurelyWrinkledFibration` is strictly stronger than `WrinkledFibration`.
  2. **Astroid / Cusp Witness**: On the $s > 0$ wrinkled Lefschetz move (`LW3`), prove the existence of **three** distinct cusp points and an indefinite-fold point on the critical locus.
  3. **ADK Topology Witness (`LW4`)**: Prove that `s4BrokenLefschetzFibration` has disconnected $T^2$-region vs. $S^2$-region regular fibers across $\mathrm{Crit}(f)$ (specifically `0 < EulerChar` vs `= 0` or fundamental-group / connectedness distinction), ruling out definite folds.
- **G6–G8**: Zero regression on `Main.lean` / `GeomChecks` / `CompChecks`, honest labelling (`Track B` vs. `Track A`), `check_gemma_provenance.py` `0` violations, and `build_dep_graph.py --require-all-green`.

---

## References

- **ADK05**: D. Auroux, S. K. Donaldson, L. Katzarkov, *Singular Lefschetz pencils*, Geom. Topol. **9** (2005), 1043–1114.
- **GK07**: D. T. Gay, R. Kirby, *Constructing Lefschetz-type fibrations on four-manifolds*, Geom. Topol. **11** (2007), 2075–2115.
- **GSV15**: L. C. García-Naranjo, P. Suárez-Serrato, R. Vera, *Poisson structures on smooth 4-manifolds*, Lett. Math. Phys. **105**(11) (2015), 1533–1550.
- **Lek09**: Y. Lekili, *Wrinkled fibrations on near-symplectic manifolds*, Geom. Topol. **13** (2009), 277–318.
- **Sae06**: O. Saeki, *Elimination of definite fold*, Kyushu J. Math. **60** (2006), 363–382.
- **ST16**: P. Suárez-Serrato, J. Torres Orozco, *Poisson structures on wrinkled fibrations*, Bol. Soc. Mat. Mex. **22**(1) (2016), 263–280.

---

## License

Licensed under the **GNU Affero General Public License v3.0 (AGPLv3)** for non-commercial use — see [LICENSE.md](LICENSE.md) for details:

> This project is licensed under non-commercial use. If you wish to use this software in a commercial product, service, or enterprise environment, please contact the developer to purchase a commercial license or negotiate royalty terms.

Authored by Pablo Suárez-Serrato (November 2026).
