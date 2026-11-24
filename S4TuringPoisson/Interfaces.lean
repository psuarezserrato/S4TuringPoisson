/-
Copyright (c) 2026 Pablo Suárez-Serrato. All rights reserved.
Released under the GNU Affero General Public License v3.0 (AGPLv3) for non-commercial use;
see LICENSE.md for details.
This project is licensed under non-commercial use. If you wish to use this software in a
commercial product, service, or enterprise environment, please contact the developer to purchase
a commercial license or negotiate royalty terms.
Authored by Pablo Suárez-Serrato (November 2026).
-/
module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.Primrec.List
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Measure
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.Geometry.Manifold.Orientation.Sphere

/-!
# Shared Milestone M0 Type Contracts for `S4TuringPoisson`

This file freezes the foundational interfaces shared across Milestones M1–M5 and Verification
Gates 1–6 of the `S4TuringPoisson` formalization of Pablo Suárez-Serrato,
*"Hamiltonian and Turing complete flows on smooth 4-manifolds"*:

1. **Canonical Manifolds & Dimension Indexing**:
   - `EuclideanPlane`, `UnitDisk2`, `Sphere2`, and `Sphere4`, together with `HasFinrank` so
     top-degree differential forms on `Sphere4` (`𝓡 4`) and `Sphere2` (`𝓡 2`) unify definitionally
     with degrees `4` and `2` respectively.

2. **Volume Forms & Induced Borel Measures (`PositiveVolumeForm`, M0.1)**:
   - Bundles a smooth nowhere-vanishing top form `Ω` on a smooth manifold `M`, its finite Borel
     measure `μ` (`IsFiniteMeasure μ`, positive on nonempty opens), and the bridge theorem that
     every smooth diffeomorphism preserving `Ω` under pullback preserves `μ`.
   - `PositiveVolumeForm.ofSmoothTopForm` builds this package on any compact smooth manifold from
     `TauCeti.RoughForm.measure`, `isLocallyFiniteMeasure_measure`, `isOpenPosMeasure_measure`, and
     `Homeomorph.measurePreserving_measure_mpullback`.
   - `S4PositiveVolumeForm : PositiveVolumeForm (𝓡 4) Sphere4` and
     `S2PositiveVolumeForm : PositiveVolumeForm (𝓡 2) Sphere2` specialize this to $S^4$ and $S^2$.

3. **Decoupled Anti-Vacuity Turing Completeness (`IsTuringComplete`, M0.2)**:
   - Built on Mathlib's `Turing.TM0.Machine`, `Turing.Tape`, `Turing.TM0.Cfg`, and
     `Turing.TM0.step`.
   - `FinTM0`, `FinSupportedTape`, `Window`, and `HaltsWithWindow` specify finite-step halting with
     prescribed output window on `[-k, k]`.
   - `TuringCompleteWitness` and `IsTuringComplete` enforce strict decoupling between
     `encodePoint M t` (equipped with computable rational chart approximations in `UnitDisk2` and
     infinite non-repeating forward orbits `orbit_encodePoint_injective`) and `encodeOpen M k w`
     (nonempty, independent of `t`, disjoint from non-terminal initial configurations, and
     presented via a `Computable` `RatBox2` enumerator `computable_encodeOpen` inside an ambient
     open-tube chart `openChart`), ruling out `Classical.by_cases` vacuity and every periodic map
     (`IsTuringComplete.iterate_ne_id`, `φ ≠ id`).

4. **Area-Preserving Disk Isotopy Interface (`HasTuringCompleteAreaPreservingDiskIsotopy`, M0.3)**:
   - Packages a jointly $C^\infty$ compactly supported area-preserving disk isotopy
     `d : ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)` (`r₀ ∈ (0, 1)`) whose time-`1`
     restriction to `UnitDisk2` satisfies `IsTuringComplete`, together with equivalence between
     unit Jacobian determinant and pullback invariance of `planeAreaForm`.
-/

@[expose] public section

open MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff ENNReal Manifold Topology

namespace S4TuringPoisson

/-! ## 1. Canonical Euclidean / Sphere Abbreviations & Dimension Resolution -/

/-- The Euclidean plane `ℝ² = EuclideanSpace ℝ (Fin 2)`. -/
abbrev EuclideanPlane : Type := EuclideanSpace ℝ (Fin 2)

/-- The open unit disk `B(0, 1) ⊂ ℝ²`. -/
noncomputable abbrev UnitDisk2 : Set (EuclideanSpace ℝ (Fin 2)) :=
  Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1

/-- The standard smooth unit 2-sphere $S^2 \subset \mathbb{R}^3$. -/
abbrev Sphere2 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- The standard smooth unit 4-sphere $S^4 \subset \mathbb{R}^5$. -/
abbrev Sphere4 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1

/-- Typeclass resolving the real vector space dimension `n` as an `outParam` so that top-degree
forms on `𝓡 n` (`EuclideanSpace ℝ (Fin n)`) elaborate with literal degree `n` definitionally. -/
class HasFinrank (E : Type*) [AddCommGroup E] [Module ℝ E] (n : outParam ℕ) : Prop where
  /-- Proof that `Module.finrank ℝ E` equals `n`. -/
  finrank_eq : Module.finrank ℝ E = n

instance instHasFinrankEuclideanSpace (n : ℕ) : HasFinrank (EuclideanSpace ℝ (Fin n)) n :=
  ⟨finrank_euclideanSpace_fin⟩

instance instHasFinrankReal : HasFinrank ℝ 1 :=
  ⟨Module.finrank_self ℝ⟩

instance instHasFinrankProd {E₁ E₂ : Type*} [AddCommGroup E₁] [Module ℝ E₁]
    [AddCommGroup E₂] [Module ℝ E₂] [Module.Finite ℝ E₁] [Module.Finite ℝ E₂]
    {n₁ n₂ : ℕ} [h₁ : HasFinrank E₁ n₁] [h₂ : HasFinrank E₂ n₂] :
    HasFinrank (E₁ × E₂) (n₁ + n₂) :=
  ⟨(Module.finrank_prod (R := ℝ) (M := E₁) (M' := E₂)).trans (congrArg₂ (· + ·) h₁.1 h₂.1)⟩

instance (priority := 100) instHasFinrankOfFiniteDimensional (E : Type*)
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] :
    HasFinrank E (Module.finrank ℝ E) :=
  ⟨rfl⟩

/-! ## 2. Positive Volume Forms & Induced Borel Measures (M0.1) -/

/-- A smooth nowhere-vanishing top-degree volume form `Ω` on a smooth manifold `M` together with
its induced positive finite Borel volume measure `μ` (`μ_Ω`) and pullback-to-`MeasurePreserving`
bridge. -/
structure PositiveVolumeForm {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [MeasurableSpace M] [BorelSpace M] {n : ℕ} [HasFinrank E n] where
  /-- Smooth top-degree volume form `Ω ∈ Ωⁿ(M)`. -/
  Ω : TauCeti.SmoothForm I M ℝ n
  /-- Pointwise non-vanishing witness `Ω_x ≠ 0` at every `x : M`. -/
  Ω_ne_zero : ∀ x : M, Ω.1 x ≠ 0
  /-- Induced Borel volume measure `μ_Ω` on `M`. -/
  μ : Measure M
  /-- Finiteness of `μ_Ω` on `M`. -/
  isFiniteMeasure : IsFiniteMeasure μ
  /-- Strict positivity of `μ_Ω` on every nonempty open subset of `M`. -/
  measure_pos_of_nonempty : ∀ U : Opens M, U.1.Nonempty → 0 < μ U.1
  /-- Any smooth diffeomorphism `Φ : M ≃ₘ⟮I, I⟯ M` preserving `Ω` under pullback is
  measure-preserving with respect to `μ_Ω`. -/
  measurePreserving_of_mpullback_eq :
    ∀ Φ : M ≃ₘ⟮I, I⟯ M,
      TauCeti.SmoothForm.mpullback Φ Φ.contMDiff Ω = Ω →
        MeasurePreserving ⇑Φ μ μ

attribute [instance] PositiveVolumeForm.isFiniteMeasure

namespace PositiveVolumeForm

section General

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} [hdim : HasFinrank E n]

/-- Alias for the underlying smooth top form `V.Ω`. -/
abbrev form (V : PositiveVolumeForm I M) : TauCeti.SmoothForm I M ℝ n := V.Ω

/-- Alias for the induced finite Borel measure `V.μ`. -/
abbrev measure (V : PositiveVolumeForm I M) : Measure M := V.μ

/-- Strict positivity of `V.μ` on any nonempty open set `s : Set M`. -/
theorem measure_isOpen_pos (V : PositiveVolumeForm I M) {s : Set M} (hs : IsOpen s)
    (hne : s.Nonempty) : 0 < V.μ s :=
  V.measure_pos_of_nonempty ⟨s, hs⟩ hne

instance instIsOpenPosMeasure (V : PositiveVolumeForm I M) : V.μ.IsOpenPosMeasure :=
  ⟨fun _ hU hne ↦ (V.measure_isOpen_pos hU hne).ne'⟩

/-- On a nonempty manifold `M`, the total volume `V.μ Set.univ` is strictly positive. -/
theorem measure_univ_pos [Nonempty M] (V : PositiveVolumeForm I M) : 0 < V.μ Set.univ :=
  V.measure_isOpen_pos isOpen_univ Set.univ_nonempty

/-- Any set `s` disjoint from a nonempty open set `u` has measure strictly less than
`V.μ Set.univ` (ruling out Dirac or degenerate full-support measures in Gate 5). -/
theorem measure_lt_univ_of_disjoint_isOpen (V : PositiveVolumeForm I M) {s u : Set M}
    (hu : IsOpen u) (hne : u.Nonempty) (hdisj : Disjoint s u) :
    V.μ s < V.μ Set.univ := by
  have hu_pos : 0 < V.μ u := V.measure_isOpen_pos hu hne
  have hle : V.μ s + V.μ u ≤ V.μ Set.univ := by
    rw [← measure_union hdisj hu.measurableSet]
    exact measure_mono (subset_univ _)
  have hs_fin : V.μ s ≠ ⊤ := measure_ne_top V.μ s
  exact lt_of_lt_of_le (ENNReal.lt_add_right hs_fin hu_pos.ne') hle

/-- Rough-form pullback variant of `measurePreserving_of_mpullback_eq`. -/
theorem measurePreserving_of_rough_mpullback_eq (V : PositiveVolumeForm I M)
    (Φ : M ≃ₘ⟮I, I⟯ M) (hΦ : TauCeti.mpullback I I Φ V.Ω.1 = V.Ω.1) :
    MeasurePreserving ⇑Φ V.μ V.μ :=
  V.measurePreserving_of_mpullback_eq Φ
    (Subtype.ext ((TauCeti.SmoothForm.coe_mpullback Φ Φ.contMDiff V.Ω).trans hΦ))

/-- Construct a `PositiveVolumeForm I M` on a compact smooth manifold from any smooth
nowhere-vanishing top form `Ω : TauCeti.SmoothForm I M ℝ n`. -/
noncomputable def ofSmoothTopForm [FiniteDimensional ℝ E] [CompactSpace M]
    (Ω : TauCeti.SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0) :
    PositiveVolumeForm I M where
  Ω := Ω
  Ω_ne_zero := hΩ
  μ := TauCeti.RoughForm.measure (hk := ⟨hdim.finrank_eq⟩) Ω.1
  isFiniteMeasure := by
    let _ : Fact (Module.finrank ℝ E = n) := ⟨hdim.finrank_eq⟩
    have _ : IsLocallyFiniteMeasure (TauCeti.RoughForm.measure Ω.1) :=
      TauCeti.RoughForm.isLocallyFiniteMeasure_measure (Ω.isSmoothForm.of_le bot_le)
    exact ⟨isCompact_univ.measure_lt_top⟩
  measure_pos_of_nonempty U hne := by
    let _ : Fact (Module.finrank ℝ E = n) := ⟨hdim.finrank_eq⟩
    have _ : (TauCeti.RoughForm.measure Ω.1).IsOpenPosMeasure :=
      TauCeti.RoughForm.isOpenPosMeasure_measure (Ω.isSmoothForm.of_le bot_le) hΩ
    exact U.2.measure_pos (TauCeti.RoughForm.measure Ω.1) hne
  measurePreserving_of_mpullback_eq Φ hΦ := by
    let hk : Fact (Module.finrank ℝ E = n) := ⟨hdim.finrank_eq⟩
    have hrough : TauCeti.mpullback I I Φ Ω.1 = Ω.1 := by
      simpa only [TauCeti.SmoothForm.coe_mpullback] using congrArg Subtype.val hΦ
    have hmp := Φ.toHomeomorph.measurePreserving_measure_mpullback (hk := hk)
      (Φ.mdifferentiable (by simp)) Ω.1
    simpa only [Diffeomorph.coe_toHomeomorph, hrough] using hmp

@[simp]
theorem ofSmoothTopForm_Ω [FiniteDimensional ℝ E] [CompactSpace M]
    (Ω : TauCeti.SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0) :
    (ofSmoothTopForm Ω hΩ).Ω = Ω :=
  rfl

@[simp]
theorem ofSmoothTopForm_μ [FiniteDimensional ℝ E] [CompactSpace M]
    (Ω : TauCeti.SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0) :
    (ofSmoothTopForm Ω hΩ).μ = TauCeti.RoughForm.measure (hk := ⟨hdim.finrank_eq⟩) Ω.1 :=
  rfl

end General

end PositiveVolumeForm

section CanonicalSpheres

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

/-- The standard outward-normal smooth area 2-form on $S^2 \subset \mathbb{R}^3$ (definitionally
equal to `TauCeti.sphereAreaForm`). -/
noncomputable def S2VolumeForm : TauCeti.SmoothForm (𝓡 2) Sphere2 ℝ 2 :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereVolumeForm

/-- `S2VolumeForm` vanishes nowhere on $S^2$. -/
theorem S2VolumeForm_ne_zero (x : Sphere2) : S2VolumeForm.1 x ≠ 0 :=
  Orientation.sphereVolumeForm_apply_ne_zero _ x

/-- Canonical `PositiveVolumeForm` on $S^2$. -/
noncomputable def S2PositiveVolumeForm : PositiveVolumeForm (𝓡 2) Sphere2 :=
  PositiveVolumeForm.ofSmoothTopForm S2VolumeForm S2VolumeForm_ne_zero

/-- The standard outward-normal smooth volume 4-form $\Omega_{S^4}$ on
$S^4 \subset \mathbb{R}^5$. -/
noncomputable def S4VolumeForm : TauCeti.SmoothForm (𝓡 4) Sphere4 ℝ 4 :=
  (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis.orientation.sphereVolumeForm

/-- `S4VolumeForm` vanishes nowhere on $S^4$. -/
theorem S4VolumeForm_ne_zero (x : Sphere4) : S4VolumeForm.1 x ≠ 0 :=
  Orientation.sphereVolumeForm_apply_ne_zero _ x

/-- Canonical `PositiveVolumeForm` on $S^4$, shared across Milestones M1–M5 and Gate 5. -/
noncomputable def S4PositiveVolumeForm : PositiveVolumeForm (𝓡 4) Sphere4 :=
  PositiveVolumeForm.ofSmoothTopForm S4VolumeForm S4VolumeForm_ne_zero

end CanonicalSpheres

/-! ## 3. Decoupled Anti-Vacuity `IsTuringComplete` Predicate (M0.2) -/

/-- A finite Post-Turing machine (`Turing.TM0`) bundling a finite tape alphabet `Γ` (`default` is
the blank symbol), a finite state set `Λ` (`default` is the initial state), and transition function
`machine : Turing.TM0.Machine Γ Λ`. -/
structure FinTM0 : Type 1 where
  /-- Tape symbol alphabet (`default` is blank). -/
  Γ : Type
  /-- Internal machine state space (`default` is initial state). -/
  Λ : Type
  [instFintypeΓ : Fintype Γ]
  [instDecidableEqΓ : DecidableEq Γ]
  [instInhabitedΓ : Inhabited Γ]
  [instFintypeΛ : Fintype Λ]
  [instDecidableEqΛ : DecidableEq Λ]
  [instInhabitedΛ : Inhabited Λ]
  /-- Transition table `Λ → Γ → Option (Λ × Turing.TM0.Stmt Γ)`. -/
  machine : Turing.TM0.Machine Γ Λ

attribute [instance]
  FinTM0.instFintypeΓ FinTM0.instDecidableEqΓ FinTM0.instInhabitedΓ
  FinTM0.instFintypeΛ FinTM0.instDecidableEqΛ FinTM0.instInhabitedΛ

/-- Finitely supported bi-infinite tape for `M : FinTM0` (`Turing.Tape M.Γ` holds `default` outside
finitely many cells on the left and right). -/
abbrev FinSupportedTape (M : FinTM0) : Type := Turing.Tape M.Γ

/-- Target output window assigning a symbol of `M.Γ` to every integer offset in `[-k, k]`. -/
abbrev Window (M : FinTM0) (k : ℕ) : Type :=
  Set.Icc (-(k : ℤ)) (k : ℤ) → M.Γ

/-- Initial `TM0` configuration `{ q := default, Tape := t }` of `M` on tape `t`. -/
def FinTM0.initCfg (M : FinTM0) (t : FinSupportedTape M) : Turing.TM0.Cfg M.Γ M.Λ :=
  { q := default, Tape := t }

/-- Single-step bind on `Option (Cfg)` used to iterate `Turing.TM0.step` `n` times. -/
def FinTM0.stepOpt (M : FinTM0) (o : Option (Turing.TM0.Cfg M.Γ M.Λ)) :
    Option (Turing.TM0.Cfg M.Γ M.Λ) :=
  o.bind (Turing.TM0.step M.machine)

@[simp]
theorem FinTM0.stepOpt_none (M : FinTM0) : M.stepOpt none = none := rfl

@[simp]
theorem FinTM0.iterate_stepOpt_none (M : FinTM0) (n : ℕ) :
    M.stepOpt^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, M.stepOpt_none]

/-- `HaltsWithWindow M t k w` asserts that `M`, started from `{ q := default, Tape := t }`, reaches
in finitely many steps a terminal configuration `c` (`Turing.TM0.step M.machine c = none`) whose
tape symbol at each offset `i ∈ [-k, k]` equals `w i`. -/
def HaltsWithWindow (M : FinTM0) (t : FinSupportedTape M) (k : ℕ) (w : Window M k) : Prop :=
  ∃ c : Turing.TM0.Cfg M.Γ M.Λ,
    Turing.TM0.Reaches M.machine (M.initCfg t) c ∧
    Turing.TM0.step M.machine c = none ∧
    ∀ i : Set.Icc (-(k : ℤ)) (k : ℤ), c.Tape.nth i.1 = w i

/-- Equivalence between `Turing.TM0.Reaches` and explicit step-count iteration of `M.stepOpt`. -/
theorem FinTM0.reaches_iff_exists_iterate_stepOpt (M : FinTM0)
    (c₀ c : Turing.TM0.Cfg M.Γ M.Λ) :
    Turing.TM0.Reaches M.machine c₀ c ↔ ∃ n : ℕ, M.stepOpt^[n] (some c₀) = some c := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail _ hstep ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, by rw [Function.iterate_succ_apply', hn]; exact hstep⟩
  · rintro ⟨n, hn⟩
    induction n generalizing c₀ with
    | zero =>
      cases hn
      exact Relation.ReflTransGen.refl
    | succ n ih =>
      rw [Function.iterate_succ_apply] at hn
      change M.stepOpt^[n] (Turing.TM0.step M.machine c₀) = some c at hn
      rcases h1 : Turing.TM0.step M.machine c₀ with _ | c₁
      · rw [h1, M.iterate_stepOpt_none] at hn
        cases hn
      · rw [h1] at hn
        exact Relation.ReflTransGen.head h1 (ih c₁ hn)

/-- Explicit finite-step characterization of `HaltsWithWindow`. -/
theorem haltsWithWindow_iff_exists_steps (M : FinTM0) (t : FinSupportedTape M) (k : ℕ)
    (w : Window M k) :
    HaltsWithWindow M t k w ↔
      ∃ (n : ℕ) (c : Turing.TM0.Cfg M.Γ M.Λ),
        M.stepOpt^[n] (some (M.initCfg t)) = some c ∧
        Turing.TM0.step M.machine c = none ∧
        ∀ i : Set.Icc (-(k : ℤ)) (k : ℤ), c.Tape.nth i.1 = w i := by
  unfold HaltsWithWindow
  constructor
  · rintro ⟨c, hreach, hterm, hwin⟩
    obtain ⟨n, hn⟩ := (M.reaches_iff_exists_iterate_stepOpt _ _).mp hreach
    exact ⟨n, c, hn, hterm, hwin⟩
  · rintro ⟨n, c, hn, hterm, hwin⟩
    exact ⟨c, (M.reaches_iff_exists_iterate_stepOpt _ _).mpr ⟨n, hn⟩, hterm, hwin⟩

/-- Unreduced signed fraction `(neg, num, denPred)` representing `± num / (denPred + 1) : ℚ`.
Uses `Bool × ℕ × ℕ` so `Primcodable` and `Primrec` instances are automatic without GCD
normalization overhead. -/
abbrev RatFrac : Type := Bool × ℕ × ℕ

/-- Rational value `(± num) / (denPred + 1)` of a `RatFrac`. -/
def RatFrac.toRat (r : RatFrac) : ℚ :=
  if r.1 then -((r.2.1 : ℚ) / ((r.2.2 : ℚ) + 1)) else (r.2.1 : ℚ) / ((r.2.2 : ℚ) + 1)

/-- Real value of a `RatFrac`. -/
noncomputable def RatFrac.toReal (r : RatFrac) : ℝ :=
  (r.toRat : ℝ)

/-- Embed a pair of `RatFrac` rational coordinates into `ℝ² = EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def ratFracPairToEuclidean2 (p : RatFrac × RatFrac) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![p.1.toReal, p.2.toReal]

/-- Unreduced rational 2-box `((xMin, xMax), (yMin, yMax))` specifying an open rectangle inside
`UnitDisk2`. Automatically inherits `Primcodable` from `RatFrac = Bool × ℕ × ℕ`. -/
abbrev RatBox2 : Type := (RatFrac × RatFrac) × (RatFrac × RatFrac)

/-- Open axis-aligned rational rectangle `(xMin, xMax) × (yMin, yMax) ∩ UnitDisk2` inside
`UnitDisk2`. -/
noncomputable def evalRatBox2 (b : RatBox2) : Opens UnitDisk2 :=
  ⟨{ y : UnitDisk2 |
      b.1.1.toReal < y.1 0 ∧ y.1 0 < b.1.2.toReal ∧
      b.2.1.toReal < y.1 1 ∧ y.1 1 < b.2.2.toReal }, by
    have c0 : Continuous fun y : UnitDisk2 ↦ y.1 0 :=
      (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).comp continuous_subtype_val
    have c1 : Continuous fun y : UnitDisk2 ↦ y.1 1 :=
      (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1).comp continuous_subtype_val
    exact (isOpen_lt continuous_const c0).inter
      ((isOpen_lt c0 continuous_const).inter
        ((isOpen_lt continuous_const c1).inter (isOpen_lt c1 continuous_const)))⟩

/-- Pointwise membership characterization for `evalRatBox2`. -/
@[simp]
theorem mem_evalRatBox2_iff (b : RatBox2) (y : UnitDisk2) :
    y ∈ evalRatBox2 b ↔
      b.1.1.toReal < y.1 0 ∧ y.1 0 < b.1.2.toReal ∧
      b.2.1.toReal < y.1 1 ∧ y.1 1 < b.2.2.toReal :=
  Iff.rfl

/-- Canonical finite-list encoding `[encΓ (w (-k)), …, encΓ (w 0), …, encΓ (w k)]` of a target
output window `w : Window M k` under `encΓ : M.Γ ≃ Fin (Fintype.card M.Γ)`. -/
def encodeWindow {M : FinTM0} (encΓ : M.Γ ≃ Fin (Fintype.card M.Γ)) (k : ℕ)
    (w : Window M k) : List (Fin (Fintype.card M.Γ)) :=
  List.ofFn fun j : Fin (2 * k + 1) ↦
    encΓ (w ⟨(j.1 : ℤ) - (k : ℤ), ⟨by omega, by omega⟩⟩)

/-- `encodeWindow encΓ k w` has exact length `2 * k + 1`. -/
@[simp]
theorem length_encodeWindow {M : FinTM0} (encΓ : M.Γ ≃ Fin (Fintype.card M.Γ)) (k : ℕ)
    (w : Window M k) :
    (encodeWindow encΓ k w).length = 2 * k + 1 := by
  simp [encodeWindow]

/-- Witness structure for anti-vacuous, effective Turing completeness of a discrete dynamical
system `φ : X → X` (Moore 1990, CMPP21 Definition 2.1 / Theorem 5.2, `S4TCdiffeo-Aug-2026.tex`
p. 13).

* `encodePoint M t` depends **only** on the machine `M` and input tape `t` (never on `(k, w)`), is
  represented in a continuous injective disk slice `chart : UnitDisk2 → X` (`chart y = openChart
  (param₀, y)`) with computable dyadic-rate rational approximations `approx`, and generates an
  infinite non-repeating forward orbit (`orbit_encodePoint_injective`).
* `encodeOpen M k w` depends **only** on `(M, k, w)` (never on `t`), is nonempty, excludes
  non-terminal initial configurations (`step ≠ none`), and is generated inside the ambient open
  tube `openChart : Param × UnitDisk2 → X` (`IsOpenEmbedding`) by a `Computable` rational-box
  enumerator `enumBoxes` (`computable_encodeOpen`).
* Forward-orbit reachability into `encodeOpen M k w` from `encodePoint M t` is equivalent to
  `HaltsWithWindow M t k w`. -/
structure TuringCompleteWitness {X : Type*} [TopologicalSpace X] (φ : X → X) where
  /-- Point encoding depending strictly on `(M, t)`. -/
  encodePoint : (M : FinTM0) → FinSupportedTape M → X
  /-- Open target set encoding depending strictly on `(M, k, w)`. -/
  encodeOpen : (M : FinTM0) → (k : ℕ) → Window M k → Opens X
  /-- Non-vacuity of every target open set. -/
  encodeOpen_nonempty : ∀ (M : FinTM0) (k : ℕ) (w : Window M k), (encodeOpen M k w).1.Nonempty
  /-- Exact simulation equivalence between forward-orbit reachability and `HaltsWithWindow`. -/
  orbit_mem_encodeOpen_iff :
    ∀ (M : FinTM0) (t : FinSupportedTape M) (k : ℕ) (w : Window M k),
      (∃ n : ℕ, φ^[n] (encodePoint M t) ∈ encodeOpen M k w) ↔ HaltsWithWindow M t k w
  /-- Separation of non-terminal initial configurations from halting target windows at `n = 0`. -/
  notMem_encodeOpen_of_step_ne_none :
    ∀ (M : FinTM0) (t : FinSupportedTape M) (k : ℕ) (w : Window M k),
      Turing.TM0.step M.machine (M.initCfg t) ≠ none →
        encodePoint M t ∉ encodeOpen M k w
  /-- Transverse parameter space for the ambient open-tube chart `openChart` (`B₀ × D²` in
  `S4TCdiffeo-Aug-2026.tex`). -/
  Param : Type
  /-- Topological space structure on `Param`. -/
  instTopologicalSpaceParam : TopologicalSpace Param
  /-- Distinguished base parameter selecting the slice `chart : UnitDisk2 → X`. -/
  param₀ : Param
  /-- Ambient open-tube chart `Param × UnitDisk2 → X` carrying the open target sets. -/
  openChart : Param × UnitDisk2 → X
  /-- `openChart` is a topological open embedding for the product topology on
  `Param × UnitDisk2`. -/
  openChart_isOpenEmbedding :
    @Topology.IsOpenEmbedding _ _ (@instTopologicalSpaceProd _ _ instTopologicalSpaceParam _) _
      openChart
  /-- Constructible coordinate chart `UnitDisk2 → X` carrying the encoded points. -/
  chart : UnitDisk2 → X
  /-- Compatibility `chart y = openChart (param₀, y)` between `chart` and `openChart`. -/
  chart_eq_openChart : ∀ y : UnitDisk2, chart y = openChart (param₀, y)
  /-- Continuity of `chart`. -/
  chart_continuous : Continuous chart
  /-- Injectivity of `chart`. -/
  chart_injective : Function.Injective chart
  /-- Disk coordinates of `encodePoint M t`. -/
  coordPoint : (M : FinTM0) → FinSupportedTape M → UnitDisk2
  /-- Factorization `encodePoint M t = chart (coordPoint M t)`. -/
  encodePoint_eq_chart :
    ∀ (M : FinTM0) (t : FinSupportedTape M), encodePoint M t = chart (coordPoint M t)
  /-- Computable rational approximations of `coordPoint M (Tape.mk₂ L R)` at rate `2⁻ᵐ`. -/
  computable_approx :
    ∀ M : FinTM0,
      ∃ (encΓ : M.Γ ≃ Fin (Fintype.card M.Γ))
        (approx :
          List (Fin (Fintype.card M.Γ)) × List (Fin (Fintype.card M.Γ)) × ℕ →
            RatFrac × RatFrac),
        Computable approx ∧
        ∀ (L R : List M.Γ) (m : ℕ),
          ‖ratFracPairToEuclidean2 (approx (L.map encΓ, R.map encΓ, m)) -
              (coordPoint M (Turing.Tape.mk₂ L R)).1‖ ≤ (1 / 2 : ℝ) ^ m
  /-- Computably enumerable rational-box presentation of every target open set `encodeOpen M k w`
  inside the ambient open tube `openChart`. -/
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
  /-- Every encoded initial point generates an infinite non-repeating forward orbit. -/
  orbit_encodePoint_injective :
    ∀ (M : FinTM0) (t : FinSupportedTape M),
      Function.Injective (fun n : ℕ ↦ φ^[n] (encodePoint M t))

/-- A self-map `φ : X → X` on a topological space `X` is **Turing complete** if it admits a
`TuringCompleteWitness`. -/
def IsTuringComplete {X : Type*} [TopologicalSpace X] (φ : X → X) : Prop :=
  Nonempty (TuringCompleteWitness φ)

/-- No positive iterate `φ^[p]` (`0 < p`) of a Turing complete self-map can equal `id` (refuting
every periodic map, including period-`2` rotation by `π`). -/
theorem IsTuringComplete.iterate_ne_id {X : Type*} [TopologicalSpace X] {φ : X → X}
    {p : ℕ} (hp : 0 < p) (hφ : IsTuringComplete φ) : φ^[p] ≠ id := by
  intro hid
  obtain ⟨W⟩ := hφ
  let M₀ : FinTM0 := { Γ := PUnit, Λ := PUnit, machine := fun _ _ ↦ none }
  have heq : φ^[p] (W.encodePoint M₀ default) = φ^[0] (W.encodePoint M₀ default) := by
    simpa only [Function.iterate_zero, id_eq] using congrFun hid (W.encodePoint M₀ default)
  exact hp.ne' (W.orbit_encodePoint_injective M₀ default heq)

/-- No Turing complete self-map can equal `id` (anti-vacuity sanity theorem used in Gate 6). -/
theorem IsTuringComplete.ne_id {X : Type*} [TopologicalSpace X] {φ : X → X}
    (hφ : IsTuringComplete φ) : φ ≠ id := by
  simpa only [Function.iterate_one] using hφ.iterate_ne_id Nat.one_pos

/-! ## 4. Area-Preserving Disk Isotopy Interface (M0.3) -/

section DiskIsotopy

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

/-- Standard constant area 2-form `dy₀ ∧ dy₁` on `ℝ² = EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def planeAreaForm : TauCeti.SmoothForm (𝓡 2) (EuclideanSpace ℝ (Fin 2)) ℝ 2 :=
  ⟨fun _ ↦ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation.volumeFormL,
    (TauCeti.isSmoothForm_modelSpace_iff.2 contDiff_const).mem_smoothBundleForms⟩

/-- Evaluation of `planeAreaForm` at any point `y : ℝ²` is the standard oriented volume 2-form. -/
@[simp]
theorem planeAreaForm_apply (y : EuclideanSpace ℝ (Fin 2))
    (v : Fin 2 → TangentSpace (𝓡 2) y) :
    planeAreaForm.1 y v =
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation.volumeForm
        (fun i ↦ (v i : EuclideanSpace ℝ (Fin 2))) :=
  Orientation.volumeFormL_apply (E := EuclideanSpace ℝ (Fin 2)) (n := 2) _
    (fun i ↦ (v i : EuclideanSpace ℝ (Fin 2)))

/-- `planeAreaForm` evaluates to `1` on the standard orthonormal basis of `ℝ²`. -/
@[simp]
theorem planeAreaForm_apply_basisFun (y : EuclideanSpace ℝ (Fin 2)) :
    planeAreaForm.1 y (fun i ↦ (EuclideanSpace.basisFun (Fin 2) ℝ i : TangentSpace (𝓡 2) y)) = 1 :=
  Orientation.volumeFormL_apply_orthonormal _ (EuclideanSpace.basisFun (Fin 2) ℝ) rfl

/-- `planeAreaForm` vanishes nowhere on `ℝ²`. -/
theorem planeAreaForm_ne_zero (y : EuclideanSpace ℝ (Fin 2)) : planeAreaForm.1 y ≠ 0 := by
  intro h
  have h1 := DFunLike.congr_fun h
    (fun i ↦ (EuclideanSpace.basisFun (Fin 2) ℝ i : TangentSpace (𝓡 2) y))
  have h2 : planeAreaForm.1 y
      (fun i ↦ (EuclideanSpace.basisFun (Fin 2) ℝ i : TangentSpace (𝓡 2) y)) = 1 :=
    planeAreaForm_apply_basisFun y
  exact one_ne_zero ((h2.symm.trans h1).trans rfl)

/-- On `ℝ² = EuclideanSpace ℝ (Fin 2)`, pullback preservation of `planeAreaForm` along a $C^\infty$
self-map `g` is equivalent to `LinearMap.det (fderiv ℝ g y).toLinearMap = 1` everywhere. -/
theorem mpullback_planeAreaForm_eq_iff_det_fderiv_eq_one
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)} (hg : ContDiff ℝ ∞ g) :
    TauCeti.SmoothForm.mpullback g hg.contMDiff planeAreaForm = planeAreaForm ↔
      ∀ y : EuclideanSpace ℝ (Fin 2), LinearMap.det (fderiv ℝ g y).toLinearMap = 1 := by
  let b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  have hor : b.orientation = (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation := rfl
  let bT (y : EuclideanSpace ℝ (Fin 2)) : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) y) := b
  have hplane (y : EuclideanSpace ℝ (Fin 2)) : planeAreaForm.1 y ⇑(bT y) = 1 :=
    planeAreaForm_apply_basisFun y
  have hval (y : EuclideanSpace ℝ (Fin 2)) :
      (TauCeti.SmoothForm.mpullback g hg.contMDiff planeAreaForm).1 y ⇑(bT y) =
        LinearMap.det (fderiv ℝ g y).toLinearMap := by
    rw [TauCeti.SmoothForm.mpullback_apply, planeAreaForm_apply]
    have hmf (v : TangentSpace (𝓡 2) y) :
        (mfderiv (𝓡 2) (𝓡 2) g y v : EuclideanSpace ℝ (Fin 2)) = fderiv ℝ g y v := by
      rw [mfderiv_eq_fderiv]
      rfl
    simp_rw [hmf]
    change b.orientation.volumeForm (⇑(fderiv ℝ g y).toLinearMap ∘ ⇑b) = _
    rw [b.orientation.volumeForm_robust (EuclideanSpace.basisFun (Fin 2) ℝ) hor,
      b.det_comp, b.det_self, mul_one]
  constructor
  · intro h y
    have hy := DFunLike.congr_fun (congrFun (congrArg Subtype.val h) y) ⇑(bT y)
    rw [hval y, hplane y] at hy
    exact hy
  · intro h
    refine Subtype.ext (funext fun y ↦ ?_)
    ext v
    rw [ContinuousAlternatingMap.apply_eq_det_mul _ (bT y) v,
      ContinuousAlternatingMap.apply_eq_det_mul _ (bT y) v, hval y, h y, hplane y]

end DiskIsotopy

/-- An injective map fixing the complement of `Metric.ball 0 r₀` maps `Metric.ball 0 r₀` into
itself, and hence maps `UnitDisk2` (`Metric.ball 0 1`) into itself whenever `r₀ < 1`. -/
theorem mem_unitDisk2_of_leftInverse_of_eq_self
    {f g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)} {r₀ : ℝ}
    (hr₁ : r₀ < 1) (hinv : ∀ y, g (f y) = y)
    (hsupp : ∀ y, y ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r₀ → f y = y)
    {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ UnitDisk2) :
    f y ∈ UnitDisk2 := by
  by_cases hy0 : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r₀
  · have hfy0 : f y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r₀ := by
      by_contra hnot
      have hfix : f (f y) = f y := hsupp (f y) hnot
      have heq : f y = y := by
        calc
          f y = g (f (f y)) := (hinv (f y)).symm
          _ = g (f y) := by rw [hfix]
          _ = y := hinv y
      rw [heq] at hnot
      exact hnot hy0
    exact Metric.ball_subset_ball hr₁.le hfy0
  · rwa [hsupp y hy0]

/-- Typeclass packaging the existence of a smooth, compactly supported, area-preserving isotopy
`d : ℝ × ℝ² → ℝ²` of the open unit disk `UnitDisk2` whose time-`1` slice is Turing complete
(Moore 1990; Cardona–Miranda–Peralta-Salas–Presas 2021, Theorem 5.2; `S4TCdiffeo-Aug-2026.tex`).

Expressing this external input (discharged unconditionally in Stretch Track `DiskSmoothing.lean`)
as an explicit Lean `class` rather than a custom `axiom` ensures `#print axioms` stays strictly
within `{propext, Classical.choice, Quot.sound}`. -/
class HasTuringCompleteAreaPreservingDiskIsotopy : Type where
  /-- Time-dependent planar isotopy `(t, y) ↦ d(t, y)`. -/
  d : ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)
  /-- Time-dependent inverse family `(t, y) ↦ d_t⁻¹(y)`. -/
  dInv : ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)
  /-- Compact-support radius `r₀ ∈ (0, 1)` strictly inside `UnitDisk2`. -/
  r₀ : ℝ
  /-- `0 < r₀` and `r₀ < 1`. -/
  r₀_mem_Ioo : r₀ ∈ Set.Ioo (0 : ℝ) 1
  /-- Joint $C^\infty$ regularity of `d` on `ℝ × ℝ²`. -/
  contDiff_d : ContDiff ℝ ∞ d
  /-- Joint $C^\infty$ regularity of `dInv` on `ℝ × ℝ²`. -/
  contDiff_dInv : ContDiff ℝ ∞ dInv
  /-- `dInv (t, ·)` is a left inverse to `d (t, ·)` for every `t : ℝ`. -/
  left_inv : ∀ (t : ℝ) (y : EuclideanSpace ℝ (Fin 2)), dInv (t, d (t, y)) = y
  /-- `dInv (t, ·)` is a right inverse to `d (t, ·)` for every `t : ℝ`. -/
  right_inv : ∀ (t : ℝ) (y : EuclideanSpace ℝ (Fin 2)), d (t, dInv (t, y)) = y
  /-- Every slice `d (t, ·)` equals `id` outside `Metric.ball 0 r₀`. -/
  eq_self_of_notMem_ball :
    ∀ (t : ℝ) (y : EuclideanSpace ℝ (Fin 2)),
      y ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r₀ → d (t, y) = y
  /-- Isotopy starts at `id` at `t = 0`. -/
  time_zero : ∀ y : EuclideanSpace ℝ (Fin 2), d (0, y) = y
  /-- Area-preserving condition `det (D_y d_t(y)) = 1` for all `(t, y)`. -/
  det_fderiv_eq_one :
    ∀ (t : ℝ) (y : EuclideanSpace ℝ (Fin 2)),
      LinearMap.det (fderiv ℝ (fun z ↦ d (t, z)) y).toLinearMap = 1
  /-- Turing completeness of the time-`1` slice restricted to `UnitDisk2`. -/
  isTuringComplete_timeOne :
    IsTuringComplete fun y : UnitDisk2 ↦
      ⟨d (1, y.1),
        mem_unitDisk2_of_leftInverse_of_eq_self (f := fun z ↦ d (1, z))
          (g := fun z ↦ dInv (1, z)) r₀_mem_Ioo.2 (left_inv 1)
          (eq_self_of_notMem_ball 1) y.2⟩

namespace HasTuringCompleteAreaPreservingDiskIsotopy

section Helpers

set_option linter.concreteInstances false

variable [H : HasTuringCompleteAreaPreservingDiskIsotopy]

/-- `0 < r₀`. -/
theorem r₀_pos : 0 < r₀ := H.r₀_mem_Ioo.1

/-- `r₀ < 1`. -/
theorem r₀_lt_one : r₀ < 1 := H.r₀_mem_Ioo.2

/-- Smoothness of the time-`t` slice `y ↦ d (t, y)`. -/
theorem contDiff_slice (t : ℝ) : ContDiff ℝ ∞ (fun y ↦ d (t, y)) :=
  H.contDiff_d.comp (contDiff_const.prodMk contDiff_id)

/-- Smoothness of the inverse time-`t` slice `y ↦ dInv (t, y)`. -/
theorem contDiff_sliceInv (t : ℝ) : ContDiff ℝ ∞ (fun y ↦ dInv (t, y)) :=
  H.contDiff_dInv.comp (contDiff_const.prodMk contDiff_id)

/-- Each slice `y ↦ d (t, y)` packaged as a $C^\infty$ `Diffeomorph` of `ℝ²`. -/
noncomputable def sliceDiffeomorph (t : ℝ) :
    EuclideanSpace ℝ (Fin 2) ≃ₘ⟮𝓡 2, 𝓡 2⟯ EuclideanSpace ℝ (Fin 2) where
  toFun y := d (t, y)
  invFun y := dInv (t, y)
  left_inv := H.left_inv t
  right_inv := H.right_inv t
  contMDiff_toFun := (contDiff_slice t).contMDiff
  contMDiff_invFun := (contDiff_sliceInv t).contMDiff

@[simp]
theorem sliceDiffeomorph_apply (t : ℝ) (y : EuclideanSpace ℝ (Fin 2)) :
    sliceDiffeomorph t y = d (t, y) :=
  rfl

@[simp]
theorem sliceDiffeomorph_symm_apply (t : ℝ) (y : EuclideanSpace ℝ (Fin 2)) :
    (sliceDiffeomorph t).symm y = dInv (t, y) :=
  rfl

/-- `dInv (t, ·)` also equals `id` outside `Metric.ball 0 r₀`. -/
theorem dInv_eq_self_of_notMem_ball (t : ℝ) {y : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r₀) :
    dInv (t, y) = y := by
  calc
    dInv (t, y) = dInv (t, d (t, y)) := by rw [H.eq_self_of_notMem_ball t y hy]
    _ = y := H.left_inv t y

/-- `dInv (0, y) = y` for all `y`. -/
@[simp]
theorem dInv_time_zero (y : EuclideanSpace ℝ (Fin 2)) : dInv (0, y) = y := by
  calc
    dInv (0, y) = dInv (0, d (0, y)) := by rw [H.time_zero y]
    _ = y := H.left_inv 0 y

/-- Every slice `y ↦ d (t, y)` preserves `planeAreaForm` under smooth pullback. -/
theorem mpullback_planeAreaForm_eq (t : ℝ) :
    TauCeti.SmoothForm.mpullback (fun y ↦ d (t, y)) (contDiff_slice t).contMDiff
        planeAreaForm = planeAreaForm :=
  (mpullback_planeAreaForm_eq_iff_det_fderiv_eq_one (contDiff_slice t)).mpr (H.det_fderiv_eq_one t)

/-- Every slice `d (t, ·)` maps `UnitDisk2` into `UnitDisk2`. -/
theorem mem_unitDisk2 (t : ℝ) {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ UnitDisk2) :
    d (t, y) ∈ UnitDisk2 :=
  mem_unitDisk2_of_leftInverse_of_eq_self (f := fun z ↦ d (t, z)) (g := fun z ↦ dInv (t, z))
    r₀_lt_one (H.left_inv t) (H.eq_self_of_notMem_ball t) hy

/-- Restriction of the time-`1` slice `y ↦ d (1, y)` to the open unit disk `UnitDisk2`. -/
noncomputable def diskTimeOneMap (y : UnitDisk2) : UnitDisk2 :=
  ⟨d (1, y.1), mem_unitDisk2 1 y.2⟩

/-- `diskTimeOneMap` is Turing complete. -/
theorem isTuringComplete_diskTimeOneMap : IsTuringComplete diskTimeOneMap :=
  H.isTuringComplete_timeOne

end Helpers

end HasTuringCompleteAreaPreservingDiskIsotopy

end S4TuringPoisson
