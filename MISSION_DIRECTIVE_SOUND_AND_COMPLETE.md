# MISSION DIRECTIVE (SOUND & COMPLETE): Closing Semantic Audit Findings `S1`–`S6` & Recommendations `(i)`–`(iv)`

Repo: `/Users/pablosuarez/Desktop/S4TuringPoisson` (`main` @ `8b87ac4`, Lean `v4.36.0`, Mathlib `fc4f59e5` + `TauCeti` `d91980bdc`, companion [`../Turing-recursive`](https://github.com/psuarezserrato/Turing-recursive) @ `4120346`).
Origin: Independent semantic re-audit (`bc772ad`, 23 November 2026) Table 2 Findings **`S1`–`S6`** and §3 **Recommendations `(i)`–`(iv)`** in [`report/final_executive_report.tex`](report/final_executive_report.tex).
Goal: Upgrade the independent audit verdict from **"kernel-sound"** to **"sound and complete"** with `0 sorryAx`, strictly standard axioms `{propext, Classical.choice, Quot.sound}`, `100%` green `leanblueprint`, and exact alignment between exported Lean theorem statements, docstrings, interfaces, and [`S4TCdiffeo-Aug-2026.tex`](S4TCdiffeo-Aug-2026.tex).

---

## §0. Audit Traceability Matrix (`S1`–`S6` & Recommendations `(i)`–`(iv)`)

Every semantic finding and recommendation from `report/final_executive_report.tex` maps to a dedicated deliverable and milestone below:

| Audit ID / Rec | Issue Identified in `bc772ad` | Resolution Deliverable & Exact Mathematical Fix | Milestone |
|---|---|---|---|
| **S1** + **Rec (i), (iv)** | `ofPositiveVolumeForm` builds `closedManifoldLocalMap` constant outside one coordinate ball, so `π_f ≡ 0` on a nonempty open set (`¬ Dense` rank-2 locus); docstring `Main.lean:496–503` overstated `"generically rank-2"`; no Corollary 2 theorem over `PurelyWrinkledFibration` exported density of the rank-2 locus; Gay–Kirby global existence was conflated with Track B. | **`SC-R2` & `SC-R3`**: (1) Fix `Main.lean:496–503` docstring and separate local coordinate-ball Poisson theorems from genuine wrinkled-fibration theorems. (2) Define `IsGenericallyRankTwo π := IsOpen {x \| π.rankAt x = 2} ∧ Dense {x \| π.rankAt x = 2}`, prove it unconditionally for every `PurelyWrinkledFibration` and `BrokenLefschetzFibration` (and both $S^4$ models), and export the full Corollary 2 + R5 + undecidability suite over positively co-oriented `PurelyWrinkledFibration` (`ofPurelyWrinkled`) and `BrokenLefschetzFibration`. (3) Prove **Moser's Volume Theorem** (`SC-R3`) so the paper's literal Corollary 2 holds on every `(M, V_M)` preserving **`V_M.Ω` and `V_M.μ` exactly**, while isolating Gay–Kirby (2007) global existence cleanly in `[AdmitsWrinkledOrBrokenLefschetzFibration M]`. | `SC3`, `SC4` |
| **S2** | `WrinkledFibration` (`LocalSingularModels.lean:1037`) imposes no critical-point normal forms; `AdmitsWrinkledOrBrokenLefschetzFibration` (`WrinkledGeneral4Manifold.lean:181`) is "wrinkled" in name only. | **`SC-R1`**: Introduce `RegularDiskFibration` and `AdmitsRegularDiskFibration M` as the honest names for smooth maps trivialized over one regular base disk (powering the leafwise lift engine, `s4Fibration`, and Track B `ClosedManifoldLocal`). Upgrade `AdmitsWrinkledOrBrokenLefschetzFibration M` (extending `AdmitsRegularDiskFibration M`) to require `∀ p ∈ criticalPoints (𝓡 4) (𝓡 2) fibration.toFun, IsIndefiniteFoldAt ... ∨ IsWrinkledCuspAt ... ∨ IsRealLefschetzAt ...`, set its `Sphere4` instance to `s4ADKAdmits`, and prove `closedManifoldLocalMap` cannot inhabit it (`¬ Dense` regular set on compact `M`). | `SC3` |
| **S3** + **Rec (ii)** | `TuringCompleteWitness` requires computable `coordPoint` approximations, but `encodeOpen` can be any nonempty open set; concrete witness is honest by inspection, yet no theorem certifies effectiveness (and periodic twist-map counterexamples are not ruled out at the interface level). | **`SC-R4`**: Add `RatBox2`, ambient open-tube chart `openChart : Param × UnitDisk2 → X` (`Topology.IsOpenEmbedding`, matching $\bar p = (c, p)$ and $\overline{\mathcal O} = B_0 \times \mathcal O$ in `S4TCdiffeo-Aug-2026.tex:549`), **`computable_encodeOpen`** (a `Computable` — proved `Primrec` — rational-box enumerator `enumBoxes` generating `encodeOpen M k w`), and **`orbit_encodePoint_injective`** (infinite non-repeating forward orbits, yielding `IsTuringComplete.iterate_ne_id : ∀ p > 0, φ^[p] ≠ id` and refuting all periodic/twist-rotation fake witnesses). Export explicit `Computable` `targetBoxes : ℕ → RatBox2` in all undecidability theorems. | `SC1` |
| **S4** + **Rec (i), (iii)** | `BrokenLefschetzFibration.exists_purelyWrinkledFibration` (`LekiliMoves.lean:5283`) exports only agreement over a half-radius disk, keeping compact-support locality and smooth homotopy internal; docstring `LekiliMoves.lean:5278–5281` cites `"Theorem 1.1"` without verification. | **`SC-R5`**: Export (1) a compact surgery support `K ⊆ M` disjoint from `B.toFun ⁻¹' closure P.baseRegion.1` and from all non-Lefschetz critical points of `B` with `∀ x ∉ K, P.toFun x = B.toFun x`, and (2) a jointly $C^\infty$ global homotopy `H : ℝ → M → Base` (`H 0 = B.toFun`, `H 1 = P.toFun`, stationary outside `K`). Update docstring to cite **Lekili (2009), §3.1 (Move 1) & §4 / Theorem 4**. | `SC2` |
| **S5** + **Rec (i)** | `LekiliMoves.lean:36–39` claims closed-form fold/cusp charts for Moves 2–4, but `lekiliMove4` only proves `criticalPoints_lekiliMove4`; `lekiliMove1`–`4` are local $\mathbb{R}^4 \to \mathbb{R}^2$ models and Moves 2–4 are unused outside `LekiliMoves.lean`. | **`SC-R6a`**: Prove closed-form `IsIndefiniteFoldAt` ($3x_1^2 + s \neq 0$) and `IsWrinkledCuspAt` ($s < 0, x_1 = \pm\sqrt{-s/3}$) for `lekiliMove4`, plus full critical-point classifications `singularities_lekiliMove4_pos` and `singularities_lekiliMove4_neg`. Correct `LekiliMoves.lean:36–39` header and add **Gate G5.4** in `Checks/GeomChecks.lean` exercising Moves 2–4 externally. | `SC2`, `SC-Final` |
| **S6** | (a) ADK fibers are `Homeomorph` (not `Diffeomorph`) and only the $S^2$ side is trivialized; (b) preserved volume `V` is positively proportional to `V_M` rather than `V_M` itself; (c) theorem statements do not pin `V.μ` to `V.Ω`; (d) `IsRealLefschetzAt` admits achiral charts without an explicit chiral companion. | **`SC-R3` & `SC-R6b–d`**: (a) Prove `s2SouthPole` is a regular value, equip regular fibers with `TauCeti.regularFiberChartedSpace`, upgrade both $S^2$ and $T^2 = S^1 \times S^1$ fibers to $C^\infty$ `Diffeomorph`s, and construct `s4ADKTorusBrokenLefschetzFibration` trivializing the $T^2$ hemisphere. (b) Prove global Moser volume conjugation (`Extension/MoserVolume.lean`) preserving `V_M.Ω` and `V_M.μ` **exactly** on `(M, V_M)` and `(Sphere4, S4PositiveVolumeForm)`. (c) Add `V.μ = TauCeti.RoughForm.measure V.Ω.1` (`rfl`) to all existential theorems. (d) Define `IsChiralRealLefschetzAt`, prove `IsChiralRealLefschetzAt → IsRealLefschetzAt`, and document why `BrokenLefschetzFibration` covers Gay–Kirby achiral Lefschetz points. | `SC2`, `SC3`, `SC4` |

---

## §1. Technical Specifications & Target Lean Signatures (`SC-R1` – `SC-R7`)

### `SC-R1`: Honest Fibration Hierarchy (`LocalSingularModels.lean`, `WrinkledGeneral4Manifold.lean`, `PurelyWrinkled.lean`)
1. Rename the unconstrained structure `WrinkledFibration` (`LocalSingularModels.lean:1037`) to **`RegularDiskFibration`** (smooth global map `toFun : M → Base` with one regular open disk `baseRegion` and smooth product trivialization `f ⁻¹' baseRegion ≃ₘ baseRegion × Fiber`, zero critical-locus restrictions), removing all unconstrained `*WrinkledFibration*` names (`WrinkledFibration` → `RegularDiskFibration`, `s4WrinkledFibration` → `s4RegularDiskFibration`, `s4ADKWrinkledFibration` → `s4ADKRegularDiskFibration`, `closedManifoldWrinkledFibration` → `closedManifoldRegularDiskFibration`, `wrinkledFibration_mem_closure_baseRegion` → `regularDiskFibration_mem_closure_baseRegion`; resolved user decision 1: zero misleading compatibility aliases). Keep `PurelyWrinkledFibration` (`IsIndefiniteFoldAt ∨ IsWrinkledCuspAt`) and `BrokenLefschetzFibration` (`IsRealLefschetzAt ∨ IsIndefiniteFoldAt`) extending `RegularDiskFibration`.
2. Split `AdmitsWrinkledOrBrokenLefschetzFibration` (`WrinkledGeneral4Manifold.lean:181`) into two classes:
   - **`class AdmitsRegularDiskFibration (M : Type*) ...`**: packages `ambientVolume`, `Fiber`, `fibration : RegularDiskFibration (𝓡 4) M (𝓡 2) Sphere2 Fiber`, `fiberVolume`, and `trivialization_pos_cooriented`. All leafwise volume/lift/Hamiltonian machinery in `AlignedUnimodularVolume.lean`, `BumpIsotopyLift.lean`, `PoissonHamiltonian.lean`, `s4Fibration`, and `ClosedManifoldLocal.lean` (`AdmitsRegularDiskFibration.ofPositiveVolumeForm`) generalizes cleanly to `[AdmitsRegularDiskFibration M]`.
   - **`class AdmitsWrinkledOrBrokenLefschetzFibration (M : Type*) ... extends AdmitsRegularDiskFibration M`**: adds the **genuine global singularity classification**:
     ```lean
     singularities_wrinkled_or_lefschetz :
       ∀ p ∈ criticalPoints (𝓡 4) (𝓡 2) fibration.toFun,
         IsIndefiniteFoldAt (𝓡 4) (𝓡 2) fibration.toFun p ∨
           IsWrinkledCuspAt (𝓡 4) (𝓡 2) fibration.toFun p ∨
           IsRealLefschetzAt (𝓡 4) (𝓡 2) fibration.toFun p
     ```
     Provide constructors `.ofPurelyWrinkled` and `.ofBrokenLefschetz`, register `instAdmitsWrinkledOrBrokenLefschetzFibrationSphere4` via `s4ADKAdmits` (`s4BrokenLefschetzFibration`), and update the module docstrings in `LocalSingularModels.lean:31` and `PurelyWrinkled.lean:21` from `Suárez-Serrato–Torres 2016` to `Suárez-Serrato–Torres Orozco 2016` (`Bol. Soc. Mat. Mex. 22(1) (2016), 263–280`).

### `SC-R2`: Generic Rank-2 Density & `PurelyWrinkledFibration` Corollary 2 (`PurelyWrinkled.lean`, `Main.lean`, `PoissonHamiltonian.lean`)
1. In `Poisson/BivectorAndModular.lean` (or `Poisson/JacobianPoisson.lean`), define:
   ```lean
   def PoissonStructure.IsGenericallyRankTwo
       {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
       {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
       (π : PoissonStructure I M) : Prop :=
     IsOpen {x : M | π.rankAt x = 2} ∧ Dense {x : M | π.rankAt x = 2}
   ```
2. Using `TauCeti.isOpen_setOf_isRegularPoint` (`LekiliMoves.lean:4976`) and local chart conjugacy `mem_criticalPoints_iff_of_partialDiffeomorph_conj` (`LekiliMoves.lean:4969`) around `(ε/2, 0, 0, 0)` (for `indefiniteFoldMap` and `realLefschetzMap`) and `(0, 0, ε/2, 0)` (for `wrinkledCuspMap`), prove:
   - `dense_regularPoints_of_wrinkled_or_lefschetz`: whenever every `p ∈ criticalPoints I_M I_B f` satisfies `IsIndefiniteFoldAt ∨ IsWrinkledCuspAt ∨ IsRealLefschetzAt`, `{x : M | x ∉ criticalPoints I_M I_B f}` is **open and dense** (`interior (criticalPoints I_M I_B f) = ∅`).
   - `isGenericallyRankTwo_adaptedJacobianPoisson` for **every** `[AdmitsWrinkledOrBrokenLefschetzFibration M]`, plus `isGenericallyRankTwo` for both $S^4$ models (`s4Fibration` and `s4BrokenLefschetzFibration`).
   - **Anti-Vacuity Separation Theorem (`ClosedManifoldLocal.lean`)**: on any compact 4-manifold `M`, `(criticalPoints (𝓡 4) (𝓡 2) (closedManifoldRegularDiskFibration V_M).toFun)` has **nonempty interior**, so its `π_f` satisfies `¬ π_f.IsGenericallyRankTwo` and `closedManifoldRegularDiskFibration V_M` cannot underlie any `AdmitsWrinkledOrBrokenLefschetzFibration M`.
3. **Recommendation (iv) Corollary 2 Suite (`Main.lean`, `PoissonHamiltonian.lean`)**:
   - Export `Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_of_purelyWrinkled` (taking `(V_M : PositiveVolumeForm (𝓡 4) M)`, `(P : PurelyWrinkledFibration (𝓡 4) M (𝓡 2) Sphere2 F)`, `(V_F : PositiveVolumeForm (𝓡 2) F)`, and positive co-orientation `hpos` via `ofPurelyWrinkled`) AND `..._of_brokenLefschetz` (deforming `B` to `P` via `BrokenLefschetzFibration.exists_purelyWrinkledFibration`!), exporting `π_f.IsGenericallyRankTwo` (`IsOpen` + `Dense` rank-2 locus), `V.μ = TauCeti.RoughForm.measure V.Ω.1`, R5 Hamiltonian realization, and undecidable reachability.
   - Keep `[AdmitsWrinkledOrBrokenLefschetzFibration M]` parametric Corollary 2 (`Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_fourManifold`) upgraded with `π_f.IsGenericallyRankTwo` and `V.μ = TauCeti.RoughForm.measure V.Ω.1`.
   - Fix `Main.lean:496–503` docstring on `..._closedFourManifold` (removing `"generically rank-2"` on the coordinate-ball map and stating explicitly that `f` is constant outside a coordinate ball while the diffeomorphism satisfies Corollary 2 unconditionally).

### `SC-R3`: Global Moser Volume Conjugation & Exact `V_M` Preservation (`Extension/MoserVolume.lean`, `Main.lean`, `PoissonHamiltonian.lean`)
1. Create `S4TuringPoisson/Extension/MoserVolume.lean` using `TauCeti`'s verified de Rham & Moser libraries:
   - `TauCeti.compactlySupportedDeRhamCohomology.bijective_integral` & `TauCeti.mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero` (`TauCeti/Geometry/Manifold/DeRham/Integration/Bijective.lean`),
   - `TauCeti.Geometry.Manifold.DifferentialForm.Integration.Positivity` (strict positivity of $\int_C \Omega$ on each connected component $C$),
   - `TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_eq` (`TauCeti/Geometry/Manifold/DifferentialForm/Flow/Family.lean`).
2. Prove **Moser's Volume Theorem on Compact Smooth 4-Manifolds**:
   - On a compact connected smooth boundaryless 4-manifold `M`, for any two positively co-oriented `PositiveVolumeForm`s `V₀, V₁` (`∀ x, ∃ a > 0, V₁.Ω.1 x = a • V₀.Ω.1 x`), there exist `c > 0` and a smooth diffeomorphism `ψ : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M` isotopic to `id` such that `SmoothForm.mpullback ψ ψ.contMDiff V₁.Ω = c • V₀.Ω`.
   - Decomposing any nonempty compact smooth 4-manifold `M` into its finitely many clopen connected components `C_i` (locally connected + compact), construct `ψ : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M` preserving each component `C_i` with `(ψ^* V.Ω)|_{C_i} = c_i • V_M.Ω|_{C_i}` (`c_i > 0`). For any diffeomorphism `d_bar` preserving each connected component (in particular every time-1 flow composition `leafwiseBumpDiffeomorph M`!), the conjugate `d_exact := ψ.symm.trans (d_bar.trans ψ)` satisfies **exact preservation of `V_M` itself** (requiring **zero** `[ConnectedSpace M]` assumption!):
     ```lean
     TauCeti.SmoothForm.mpullback d_exact d_exact.contMDiff V_M.Ω = V_M.Ω ∧
     MeasurePreserving ⇑d_exact V_M.μ V_M.μ
     ```
3. Export **Exact-Volume Literal Corollary 2 & Theorem 1 Companions**:
   - `Main.exists_turingComplete_exactVolumePreserving_diffeomorph_closedFourManifold` on any `(M, V_M)` (`d_exact^* V_M.Ω = V_M.Ω ∧ MeasurePreserving ⇑d_exact V_M.μ V_M.μ ∧ IsTuringComplete ⇑d_exact`, plus pushed-forward unimodular Jacobian–Poisson structure `ψ^* π_f` and R5 time-1 Hamiltonian flow realization `Hs.map (· ∘ ψ)`!).
   - `Main.exists_turingComplete_exactVolumePreserving_diffeomorph_S4` & `..._S4_ADK` preserving the **exact standard round volume form `S4PositiveVolumeForm`**!
   - Pin `V.μ = TauCeti.RoughForm.measure V.Ω.1` (`rfl`) as an explicit conjunct in all existential `PositiveVolumeForm` theorems across `Main.lean`, `ADKS4Fibration.lean`, and `PoissonHamiltonian.lean`.

### `SC-R4`: Effective Rational-Box `encodeOpen` & Non-Periodicity (`Interfaces.lean`, `Simulator.lean`, `DiskSmoothing.lean`, `UndecidabilityAndTransfer.lean`)
1. In `S4TuringPoisson/Interfaces.lean`, define open rational 2-boxes inside `UnitDisk2`:
   ```lean
   abbrev RatBox2 : Type := (RatFrac × RatFrac) × (RatFrac × RatFrac)

   def evalRatBox2 (b : RatBox2) : Opens UnitDisk2 :=
     ⟨{ y : UnitDisk2 |
         b.1.1.toReal < y.1 0 ∧ y.1 0 < b.1.2.toReal ∧
         b.2.1.toReal < y.1 1 ∧ y.1 1 < b.2.2.toReal }, ...⟩
   ```
   and canonical window encoding `encodeWindow {M : FinTM0} (encΓ : M.Γ ≃ Fin (Fintype.card M.Γ)) (k : ℕ) (w : Window M k) : List (Fin (Fintype.card M.Γ))`.
2. Strengthen `TuringCompleteWitness {X : Type*} [TopologicalSpace X] (φ : X → X)` (`Interfaces.lean:382`) with:
   - **Open-tube chart** matching $\bar p = (c, p)$ and $\overline{\mathcal O} = B_0 \times \mathcal O$ (`S4TCdiffeo-Aug-2026.tex:549`):
     ```lean
     Param : Type
     instTopologicalSpaceParam : TopologicalSpace Param
     param₀ : Param
     openChart : Param × UnitDisk2 → X
     openChart_isOpenEmbedding :
       @Topology.IsOpenEmbedding _ _ (@instTopologicalSpaceProd _ _ instTopologicalSpaceParam _) _
         openChart
     chart_eq_openChart : ∀ y : UnitDisk2, chart y = openChart (param₀, y)
     ```
   - **Computably enumerable rational-box target sets (`Recommendation (ii)`)**:
     ```lean
     computable_encodeOpen :
       ∀ M : FinTM0,
         ∃ (encΓ : M.Γ ≃ Fin (Fintype.card M.Γ))
           (enumBoxes : ℕ × List (Fin (Fintype.card M.Γ)) × ℕ → RatBox2),
           Computable enumBoxes ∧
           ∀ (k : ℕ) (w : Window M k),
             (∀ j : ℕ, (evalRatBox2 (enumBoxes (k, encodeWindow encΓ k w, j))).1.Nonempty) ∧
             (encodeOpen M k w).1 =
               openChart '' (Set.univ ×ˢ
                 ⋃ j : ℕ, (evalRatBox2 (enumBoxes (k, encodeWindow encΓ k w, j))).1)
     ```
   - **Infinite non-repeating orbits (`orbit_encodePoint_injective`)**:
     ```lean
     orbit_encodePoint_injective :
       ∀ (M : FinTM0) (t : FinSupportedTape M),
         Function.Injective (fun n : ℕ ↦ φ^[n] (encodePoint M t))
     ```
     Prove `IsTuringComplete.iterate_ne_id {p : ℕ} (hp : 0 < p) (hφ : IsTuringComplete φ) : φ^[p] ≠ id` (subsuming `IsTuringComplete.ne_id` at `p = 1` and refuting all periodic twist/rotation maps!).
3. Discharge `computable_encodeOpen` and `orbit_encodePoint_injective` in `Bennett.lean`, `Simulator.lean`, and `DiskSmoothing.lean`:
   - In `Bennett.lean`: prove `(bennettReversibleTM M).step^[m] (bennettInitCfg M t) ≠ bennettInitCfg M t` for all `m ≥ 1` (since step `0` has `(q = .exec _ _, posH = 0)` whereas every subsequent state either enters `.halted`/`.haltRun` forever or strictly advances history/phase), which by `Bijective.iterate` implies `Function.Injective (fun n ↦ R.step^[n] (bennettInitCfg M t))`.
   - In `GeneralizedShift.lean` & `Simulator.lean`: express `cantorOpenInterval` endpoints as exact `Primrec` `RatFrac` pairs and build a `Primrec` (hence `Computable`) box enumerator `(k, w_list, j) ↦ RatBox2` decoding `j` into `(c_extra, digits : List (Fin universalShiftCard))`, checking the finite-domain `PrimrecPred` for `IsAcceptingCylinderBlock`, and falling back to `canonicalAcceptBlock` otherwise.
   - Transport `openChart`, `computable_encodeOpen`, and `orbit_encodePoint_injective` across `TuringCompleteWitness.ofOpenEmbedding` (including diffeomorphism conjugation `ψ⁻¹`) and `TuringCompleteWitness.transfer`, and export `targetBoxes : ℕ → RatBox2` (`Computable targetBoxes`) in `TuringCompleteWitness.undecidable_orbit_reachability`, `IsTuringComplete.undecidable_orbit_reachability`, and all headline undecidability theorems in `Main.lean` and `ADKS4Fibration.lean`.

### `SC-R5`: Exported Surgery Locality & Smooth Homotopy (`LekiliMoves.lean`)
1. Upgrade `regularDiskFibration_mem_closure_baseRegion` and `BrokenLefschetzFibration.exists_purelyWrinkledFibration` (`LekiliMoves.lean:5283`) so the public theorem exports:
   - `P.baseDiskRadius = B.baseDiskRadius / 2 ∧ P.baseRegion.1 ⊆ B.baseRegion.1`,
   - **Compact surgery support `K : Set M`**: `IsCompact K`, `Disjoint K (B.toFun ⁻¹' closure (P.baseRegion : Set Base))`, `∀ p ∈ criticalPoints I_M I_B B.toFun, ¬ IsRealLefschetzAt I_M I_B B.toFun p → p ∉ K` (all regular points and all indefinite-fold loci of `B` lie outside `K`), and `∀ x ∉ K, P.toFun x = B.toFun x` (which immediately implies `∀ x ∈ P.toFun ⁻¹' P.baseRegion.1, P.toFun x = B.toFun x`),
   - **Smooth global homotopy `H : ℝ → M → Base`**: `ContMDiff (𝓘(ℝ, ℝ).prod I_M) I_B ∞ (Function.uncurry H)`, `∀ x, H 0 x = B.toFun x`, `∀ x, H 1 x = P.toFun x`, and `∀ (t : ℝ), ∀ x ∉ K, H t x = B.toFun x` (constructed via `compactLefschetzWrinkle (t * s₀)` on pairwise-disjoint isolating Lefschetz charts).
2. Fix `LekiliMoves.lean:5278–5281` docstring to cite **Lekili (2009), *Geom. Topol.* 13, §3.1 (Move 1 local wrinkling of a Lefschetz point) & §4 / Theorem 4 (replacing Lefschetz singularities by 3-cusped wrinkles)**.

### `SC-R6`: Move 4 Normal Forms, Smooth ADK Fibers/South Trivialization & Chiral Lefschetz (`LekiliMoves.lean`, `ADKS4Fibration.lean`, `LocalSingularModels.lean`, `GeomChecks.lean`)
1. **Move 4 Swallowtail/Flip Normal Forms (`LekiliMoves.lean:3890–4056`)**:
   - Prove `isIndefiniteFoldAt_lekiliMove4` at every critical point `lekiliMove4CritCurve s x` with `3 * x ^ 2 + s ≠ 0`.
   - Prove `isWrinkledCuspAt_lekiliMove4` at `x = ±Real.sqrt (-s / 3)` whenever `s < 0` (via the closed-form smooth coordinate shear factoring `c u³ + u⁴ / 4 = u³ (c + u / 4)` near `u = 0`).
   - Export full critical-locus classifications `singularities_lekiliMove4_pos` (`0 < s → ∀ p ∈ Crit, IsIndefiniteFoldAt`) and `singularities_lekiliMove4_neg` (`s < 0 → ∀ p ∈ Crit, IsIndefiniteFoldAt ∨ IsWrinkledCuspAt`), and update `LekiliMoves.lean:36–39` header to state accurately that `lekiliMove1`–`4` are explicit local $\mathbb{R}^4 \to \mathbb{R}^2$ 1-parameter normal-form families.
   - Add **Gate G5.4 (`Checks.gate54_lekili_moves_234_witness`)** in `Checks/GeomChecks.lean` externally verifying Moves 2, 3, and 4.
2. **ADK $S^4$ Smooth Diffeomorphisms & Two-Sided Trivialization (`ADKS4Fibration.lean`)**:
   - Prove `s2SouthPole_notMem_image_criticalPoints_s4ADKFibration` (`s2SouthPole` is a regular value).
   - Equip `{x : Sphere4 // s4ADKFibration x = s2NorthPole}` and `{x : Sphere4 // s4ADKFibration x = s2SouthPole}` with `TauCeti.regularFiberChartedSpace` (`TauCeti.isManifold_regularFiber` from `TauCeti/Geometry/Manifold/RegularValue/ManifoldLevel.lean`) and upgrade `s4ADKNorthFiberHomeomorph` and `s4ADKTorusFiberHomeomorph` to **$C^\infty$ `Diffeomorph`s** (`s4ADKNorthFiberDiffeomorph`, `s4ADKTorusFiberDiffeomorph`) via `ContMDiff.iff_comp_isImmersion`.
   - Construct the explicit south-hemisphere trivialization around `s2SouthPole` (`s4ADKTorusBrokenLefschetzFibration : BrokenLefschetzFibration (𝓡 4) Sphere4 (𝓡 2) Sphere2 Torus2`), trivializing **both** the $S^2$ and $T^2$ chambers of `s4ADKFibration`.
3. **Chiral vs. Achiral Lefschetz (`LocalSingularModels.lean`)**:
   - Define `IsChiralRealLefschetzAt` on oriented 4-manifolds `(M, V_M)` over oriented surfaces `(Base, V_B)` by requiring orientation-preserving chart diffeomorphisms `(φ, ψ)` (`TauCeti.Manifold.Orientation.IsOrientationPreservingAt`), prove `IsChiralRealLefschetzAt → IsRealLefschetzAt`, prove `realLefschetzMap` at `0` is chiral while `(z₁, z₂) ↦ z̄₁² + z₂²` is achiral yet satisfies `IsRealLefschetzAt`, and document why `BrokenLefschetzFibration` covers Gay–Kirby (2007) achiral broken Lefschetz fibrations.

### `SC-R7`: Blueprint, `AUDIT.md`, `README.md` & Executive Report Upgrade (`SC-Final`)
- Update `blueprint/src/content.tex` with nodes/links for `RegularDiskFibration`, `IsGenericallyRankTwo`, `MoserVolume`, `computable_encodeOpen` / `iterate_ne_id`, `lekiliMove4` normal forms, surgery locality/homotopy, and ADK smooth fiber diffeomorphisms (`100%` green via `build_dep_graph.py full --require-all-green`).
- Update `AUDIT.md`, `README.md` (preserving the verbatim AGPLv3 non-commercial footer), and `report/final_executive_report.tex` & `report/final_executive_report.pdf` (`<= 6` pages, `0 Overfull \hbox`), replacing open semantic caveats `S1`–`S6` with verified resolutions and upgrading the audit verdict to **"Sound and Complete"**.

---

## §2. Swarm Roster, Exclusive File Ownership & 24 GB RAM Schedule

### 2.1 Non-Negotiable Hardware & Concurrency Guardrails (`.agents/rules/lean-integrity.md`)
- **Build & Elaboration**: Always run `LEAN_NUM_THREADS=2 lake build --wfail` (Lake 5.0.0 has no `-j` flag).
- **Pre-Flight Gate Before Every `lake` / Lean Invocation**:
  ```bash
  python3 tools/workflow_control.py check-pause && sysctl vm.swapusage && (ollama ps || true)
  ```
  Halt immediately and notify `@coordinator` if `vm.swapusage used >= 10240M`.
- **Max 1–2 Active Lean Processes Total**: At most **1 active frontier Lean worker** + **1 `gemma4:12B` daemon check slot** (`tools/gemma_loop.py`, locked to `num_ctx=4096`, `max_prompt_chars=4000`, `keep_alive=0`, `OLLAMA_NUM_PARALLEL=1`, `temperature=1.0`, `top_p=0.95`, `top_k=64`, `think=false`). All other swarm workers MUST remain parked on `swarm_wait` until `@coordinator` assigns them the active Lean slot.
- **Worktree Isolation**: Spawn author workers with `workspace: "share"` (isolated working copies) and verifiers with `workspace: "inherit"`. Merge `--no-ff` onto `main` only after verifier sign-off.
- **Routing & 5-Retry Rule**: Tag routine discrete/algebraic helpers (`RatBox2` bounds, digit list indexing, `Fin` projections) as `-- tier: T0` and route through `tools/gemma_loop.py` first (Gate G8 enforced by `tools/check_gemma_provenance.py`). Keep `Interfaces.lean`, `MoserVolume.lean`, manifold charts, and verifiers on frontier models; escalate any subgoal failing `>5` tactic cycles immediately.

### 2.2 Swarm Roster & Exclusive Module Boundaries

| Roster Name | Role | Owned Files (Exclusive Per Wave) | Milestone(s) |
|---|---|---|---|
| `@coordinator` | Swarm Coordinator & Integrator | Merge commits on `main`, `S4TuringPoisson.lean`, final docs (`blueprint/`, `report/`, `AUDIT.md`, `README.md`) | Wave scheduling & `SC-Final` |
| `@worker-comp` | Computability & Witness Author (`workspace: "share"`) | `Interfaces.lean`, `Dynamics/GeneralizedShift.lean`, `Dynamics/Reversible/Bennett.lean`, `Dynamics/UndecidabilityAndTransfer.lean`, `Smoothing/DiskSmoothing.lean`, `Smoothing/CMPP/Simulator.lean`, `Checks/CompChecks.lean` | **`SC1`** (`SC-R4`: `S3` + Rec `(ii)`) |
| `@worker-lekili` | Singularity & Surgery Author (`workspace: "share"`) | `Fibration/LekiliMoves.lean`, chiral predicate section of `Fibration/LocalSingularModels.lean` | **`SC2`** (`SC-R5`, `SC-R6a,d`: `S4`, `S5`, `S6d`, Rec `(i, iii)`) |
| `@worker-fibration` | Global Fibration & ADK Author (`workspace: "share"`) | `Fibration/LocalSingularModels.lean`, `Fibration/PurelyWrinkled.lean`, `Fibration/WrinkledGeneral4Manifold.lean`, `Fibration/ClosedManifoldLocal.lean`, `Fibration/ADKS4Fibration.lean`, `Poisson/JacobianPoisson.lean`, `Extension/{AlignedUnimodularVolume,BumpIsotopyLift,PoissonHamiltonian}.lean` | **`SC3`** (`SC-R1`, `SC-R2`, `SC-R6b`: `S1`, `S2`, `S6a`, Rec `(iv)`) |
| `@worker-moser` | Moser Volume & Main Assembly Author (`workspace: "share"`) | `Extension/MoserVolume.lean` (new), `Main.lean`, `Checks/GeomChecks.lean` | **`SC4`** (`SC-R3`, `SC-R2` Cor 2, `G5.4`: `S1`, `S6b,c`, Rec `(i, iv)`) |
| `@verifier-comp` | Adversarial Computability Verifier (`workspace: "inherit"`) | Read-only + scratch refutation tests (attempts periodic/non-effective counterexamples against `TuringCompleteWitness`) | Audits `SC1`, `SC4` |
| `@verifier-geom` | Adversarial Geometry & Kernel Verifier (`workspace: "inherit"`) | Read-only + scratch refutation tests (`leanchecker`, `#audit_wiring`, definite-fold / local-constant exclusion, Moser exactness) | Audits `SC2`, `SC3`, `SC4`, `SC-Final` |

### 2.3 Sequential Wave Execution Plan (Zero Merge Conflicts, Single Active Lean Slot)

```
Wave 1 (SC1 — Computability & Effective encodeOpen, ~450 LOC)
  Active slot: @worker-comp (+ gemma4:12B on T0 RatBox2/digit lemmas)
  Gate: @verifier-comp verifies computable_encodeOpen, iterate_ne_id (refutes period-2 rotation),
        collect_axioms.sh, check_gemma_provenance.py -> Coordinator merges work/sc1 to main.
        │
        ▼
Wave 2 (SC2 — Lekili Move 4 Normal Forms, Surgery Locality/Homotopy & Chiral Lefschetz, ~650 LOC)
  Active slot: @worker-lekili
  Gate: @verifier-geom verifies Move 4 cusp/fold charts, compact support K, smooth homotopy H,
        Lekili 2009 §3.1/§4 citations -> Coordinator merges work/sc2 to main.
        │
        ▼
Wave 3 (SC3 — RegularDiskFibration Split, IsGenericallyRankTwo & Smooth ADK S^2/T^2 Fibers, ~800 LOC)
  Active slot: @worker-fibration (rebases on main with SC1 + SC2)
  Gate: @verifier-geom verifies AdmitsWrinkledOrBrokenLefschetzFibration singularity enforcement,
        Dense rank-2 locus, Track B ¬IsGenericallyRankTwo separation, ADK C^∞ fiber diffeomorphisms
        & south T^2 trivialization -> Coordinator merges work/sc3 to main.
        │
        ▼
Wave 4 (SC4 — Moser Exact Volume Theorem, PurelyWrinkled Corollary 2 & Gate G5.4, ~650 LOC)
  Active slot: @worker-moser (rebases on main with SC1–SC3)
  Gate: @verifier-geom + @verifier-comp verify d_exact^* V_M.Ω = V_M.Ω (zero ConnectedSpace assumption),
        V.μ = RoughForm.measure V.Ω.1, PurelyWrinkled Corollary 2, Gate G5.4 -> Merge work/sc4 to main.
        │
        ▼
Wave 5 (SC-Final — Blueprint 100% Green, Independent Kernel Replay & Executive Report, ~300 LOC)
  Active slot: @coordinator + independent read-only audit by @verifier-geom & @verifier-comp
  Gate: All Gates G1–G10 pass; report/final_executive_report.pdf <= 6 pages, 0 Overfull \hbox,
        verdict upgraded to "Sound and Complete".
```

**Estimated Total Addition**: `~2,500–2,900` LOC across 1 new file (`Extension/MoserVolume.lean`) and targeted upgrades to existing modules.

---

## §3. Verification Gates (`G1`–`G10`) & Adversarial Refutation Criteria

No milestone may merge onto `main` unless every applicable gate passes with zero failures:

1. **G1 Build & Hygiene**: `LEAN_NUM_THREADS=2 lake build --wfail` (`0` errors, `0` warnings), `<= 100` columns per `.lean` line, 9-line AGPLv3 non-commercial header on every `.lean` file, only `set_option linter.concreteInstances false` permitted.
2. **G2 Kernel Axioms & Replay**: `LEAN_NUM_THREADS=2 bash tools/collect_axioms.sh` (`0` forbidden tokens; every constant strictly `⊆ {propext, Classical.choice, Quot.sound}`), plus sequential leaf-module `lake env leanchecker` replay across **all** leaf modules (`0` failures).
3. **G3 Statement & Docstring Alignment (`Rec (i)`)**: Every exported docstring is audited line-by-line against its formal conclusion by `@verifier-geom` / `@verifier-comp` — zero unproved adjectives (`"generically rank-2"` allowed **only** where `IsGenericallyRankTwo` is an exported conjunct; `"deformation"` allowed **only** where smooth homotopy `H` is exported).
4. **G4 Pruned Proof-Term Wiring (`#audit_wiring`)**:
   - `Main.exists_turingComplete_exactVolumePreserving_diffeomorph_closedFourManifold` transitively uses `TauCeti.mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero` (or `bijective_integral`), `MoserVolume`, `instHasCMPPCantorCirculationHamiltonians`, and `TuringRecursive.U`.
   - `Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_of_purelyWrinkled` transitively uses `AdmitsWrinkledOrBrokenLefschetzFibration.ofPurelyWrinkled` and `isGenericallyRankTwo_adaptedJacobianPoisson`.
   - `BrokenLefschetzFibration.exists_purelyWrinkledFibration` transitively uses `lekiliMove1`, `singularities_lekiliMove1`, `exists_compactLefschetzWrinkle_collar`, and `WrinkledFibration.shrinkBaseHalf` (renamed `RegularDiskFibration.shrinkBaseHalf`).
5. **G5 Adversarial Anti-Vacuity & Refutation Witnesses (`CompChecks.lean`, `GeomChecks.lean`)**:
   - **G5-Comp (Twist-Rotation Refutation)**: Prove `Checks.periodic_rotation_not_isTuringComplete` — the period-2 disk rotation `(x, y) ↦ (-x, -y)` (which defeated the old `encodeOpen`-unconstrained interface!) satisfies `¬ IsTuringComplete`, and exhibit concrete rational boxes from `targetBoxes` on `Sphere4`.
   - **G5-Geom-1 (Local vs. Global Fibration Separation)**: Prove `Checks.closedManifoldLocal_not_genericallyRankTwo` on `Sphere4`, confirming Track B's coordinate-ball map has nonempty critical interior and cannot satisfy `AdmitsWrinkledOrBrokenLefschetzFibration`.
   - **G5-Geom-2 (Gate G5.4 Moves 2–4)**: Verify 2-cusp birth (`lekiliMove2 1`), cusp-merge (`lekiliMove3`), and swallowtail flip (`lekiliMove4 1` fold-only vs. `lekiliMove4 (-3)` 2-cusp + fold classification).
   - **G5-Geom-3 (ADK Smooth Diffeomorphisms & Exact Moser Volume)**: Verify `s4ADKNorthFiberDiffeomorph`, `s4ADKTorusFiberDiffeomorph`, `s4ADKTorusBrokenLefschetzFibration`, and `d_exact^* S4PositiveVolumeForm.Ω = S4PositiveVolumeForm.Ω`.
6. **G6 Regression & Tooling**: Existing Gates `G5.1`–`G5.3` and `G6` pass; `python3 -m unittest discover -s tests -v` passes (`100%`).
7. **G7 Architectural Honesty**: Track B (`AdmitsRegularDiskFibration.ofPositiveVolumeForm` + Moser exact `V_M` preservation) proves the paper's literal Corollary 2 unconditionally; Track A (`AdmitsWrinkledOrBrokenLefschetzFibration` / `PurelyWrinkledFibration`) proves the full generically rank-2 Poisson Corollary 2 modulo only Gay–Kirby's 4-manifold handlebody theorem.
8. **G8 Local-Model Provenance**: `python3 tools/check_gemma_provenance.py` reports `0` violations across all `-- tier: T0` declarations.
9. **G9 Blueprint `100%` Green**: `build_dep_graph.py full --pdf-out report/blueprint_dep_graph.pdf --require-all-green` and `verify_blueprint.py audit --require-all-green` pass (`0` open nodes, `0 sorryAx`, `0` `plasTeX` errors).
10. **G10 Executive Report & Semantic Sign-Off**: `report_tool.py compile-and-verify --tex-path report/final_executive_report.tex --max-total-pages 6` passes (`0 Overfull \hbox`, `0` errors), visual inspection of every PDF page is clean, and independent semantic review confirms **0 open findings** (`S1`–`S6` resolved).

---

## References

- **ADK05**: D. Auroux, S. K. Donaldson, L. Katzarkov, *Singular Lefschetz pencils*, Geom. Topol. **9** (2005), 1043–1114.
- **CMPP21**: R. Cardona, E. Miranda, D. Peralta-Salas, F. Presas, *Constructing Turing complete Euler flows in dimension 3*, PNAS **118** (2021), e2026818118.
- **GK07**: D. T. Gay, R. Kirby, *Constructing Lefschetz-type fibrations on four-manifolds*, Geom. Topol. **11** (2007), 2075–2115.
- **GSV15**: L. C. García-Naranjo, P. Suárez-Serrato, R. Vera, *Poisson structures on smooth 4-manifolds*, Lett. Math. Phys. **105**(11) (2015), 1533–1550.
- **Lek09**: Y. Lekili, *Wrinkled fibrations on near-symplectic manifolds*, Geom. Topol. **13** (2009), 277–318 (§3.1 Move 1, §3.2 Moves 2–4, §4 Theorem 4).
- **Mos65**: J. Moser, *On the volume elements on a manifold*, Trans. Amer. Math. Soc. **120** (1965), 286–294.
- **ST16**: P. Suárez-Serrato, J. Torres Orozco, *Poisson structures on wrinkled fibrations*, Bol. Soc. Mat. Mex. **22**(1) (2016), 263–280.

---

## License

Licensed under the **GNU Affero General Public License v3.0 (AGPLv3)** for non-commercial use — see [LICENSE.md](LICENSE.md) for details:

> This project is licensed under non-commercial use. If you wish to use this software in a commercial product, service, or enterprise environment, please contact the developer to purchase a commercial license or negotiate royalty terms.

Authored by Pablo Suárez-Serrato (November 2026).
