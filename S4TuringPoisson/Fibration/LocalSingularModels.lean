/-
Copyright (c) 2026 Pablo Suárez-Serrato. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Suárez-Serrato
-/
module

public import S4TuringPoisson.Interfaces
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Sphere.Connected

/-!
# Local Singular Fibration Models & Global Wrinkled / Broken Lefschetz Structures (M2.1)

This file formalizes Milestone M2.1 of `S4TuringPoisson` (`S4TCdiffeo-Aug-2026.tex`,
Auroux–Donaldson–Katzarkov 2005, Lekili 2009, García-Naranjo–Suárez-Serrato–Vera 2015, and
Suárez-Serrato–Torres 2016):

1. **Critical Point Sets & Regularity (`criticalPoints`, `euclideanCriticalPoints`)**:
   - Manifold-level `criticalPoints I J f = {p | ¬ Function.Surjective (mfderiv I J f p)}` and
     normed-space `euclideanCriticalPoints f = {p | ¬ Function.Surjective (fderiv ℝ f p)}`, proved
     equal on `𝓡 m → 𝓡 n`.
2. **Indefinite Quadratic Fold Normal Form (Eq. 2 of `S4TCdiffeo-Aug-2026.tex`, Gate 4)**:
   - `indefiniteFoldMap (y₁, y₂, y₃, t) = (y₁² - (y₂² + y₃²) / 2, t)` on
     `EuclideanSpace ℝ (Fin 4) → EuclideanPlane` (and tuple variant `indefiniteFoldTuple`).
   - Exact `ContDiff ℝ ∞`, `HasFDerivAt`, `fderiv` / `mfderiv` formulas, critical locus
     `{p | p 0 = 0 ∧ p 1 = 0 ∧ p 2 = 0}`, Gate 4 witnesses `(0, 0, 0, t) ∈ Crit` and
     `(1, 0, 0, t) ∉ Crit`, and the ADK equatorial cobordism fiber topology transition
     (disconnected two-sheeted hyperboloid over `c > 0` vs. connected cylinder `Circle × ℝ` with
     vanishing cycle over `c < 0`).
3. **Real Lefschetz & Wrinkled Cusp Normal Forms (`Lekili 2009`, `ST16`)**:
   - `realLefschetzMap` (`(x₁, y₁, x₂, y₂) ↦ (x₁² - y₁² + x₂² - y₂², 2 x₁ y₁ + 2 x₂ y₂)`) with
     isolated critical point `{0}`.
   - `wrinkledCuspMap` (`(t, x₁, x₂, x₃) ↦ (t, x₁³ - 3 t x₁ + x₂² - x₃²)`) with parabolic critical
     curve `{p | p 0 = p 1 ^ 2 ∧ p 2 = 0 ∧ p 3 = 0}` projecting to the semi-cubical cusp
     `(s², -2 s³)`.
   - Local chart singularity predicates `IsLocallyModeledOn`, `IsIndefiniteFoldAt`,
     `IsRealLefschetzAt`, and `IsWrinkledCuspAt`.
4. **`WrinkledFibration` & `BrokenLefschetzFibration`**:
   - Global smooth singular fibration structures packaging a nonempty regular open disk
     `baseRegion ⊆ Base` disjoint from `f '' Crit(f)`, a compact nonempty smooth 2-manifold fiber
     `Fiber`, a Euclidean disk parametrization `baseDisk`, and an explicit smooth trivialization
     `f ⁻¹' baseRegion ≃ₘ baseRegion × Fiber` directly usable by Milestones M2.2, M2.3, and M4.
-/

@[expose] public section

open Function Metric Module Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace S4TuringPoisson

/-! ## 1. Critical Points and Regularity on Manifolds and Euclidean Spaces -/

section CriticalPoints

variable {E H E' H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]

/-- The set of critical points of a map `f : M → N` between charted spaces: points `p : M` at which
`mfderiv I J f p` is not surjective. -/
def criticalPoints (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H') (f : M → N) :
    Set M :=
  {p : M | ¬ Function.Surjective (mfderiv I J f p)}

/-- A point `p : M` is regular for `f : M → N` when `mfderiv I J f p` is surjective. -/
def IsRegularPointAt (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
    (f : M → N) (p : M) : Prop :=
  Function.Surjective (mfderiv I J f p)

@[simp]
theorem mem_criticalPoints_iff {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
    {f : M → N} {p : M} :
    p ∈ criticalPoints I J f ↔ ¬ Function.Surjective (mfderiv I J f p) :=
  Iff.rfl

theorem notMem_criticalPoints_iff {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
    {f : M → N} {p : M} :
    p ∉ criticalPoints I J f ↔ Function.Surjective (mfderiv I J f p) :=
  not_not

/-- Critical points of a map `f : E → E'` between real normed spaces via `fderiv ℝ`. -/
def euclideanCriticalPoints (f : E → E') : Set E :=
  {p : E | ¬ Function.Surjective (fderiv ℝ f p)}

@[simp]
theorem mem_euclideanCriticalPoints_iff {f : E → E'} {p : E} :
    p ∈ euclideanCriticalPoints f ↔ ¬ Function.Surjective (fderiv ℝ f p) :=
  Iff.rfl

theorem notMem_euclideanCriticalPoints_iff {f : E → E'} {p : E} :
    p ∉ euclideanCriticalPoints f ↔ Function.Surjective (fderiv ℝ f p) :=
  not_not

/-- On `EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)` equipped with `𝓡 m` and `𝓡 n`,
manifold `criticalPoints` and `euclideanCriticalPoints` coincide. -/
@[simp]
theorem criticalPoints_euclidean_eq (m n : ℕ)
    (f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)) :
    criticalPoints (𝓡 m) (𝓡 n) f = euclideanCriticalPoints f := by
  ext p
  simp only [mem_criticalPoints_iff, mem_euclideanCriticalPoints_iff]
  congr! 1
  constructor <;> intro h w <;> obtain ⟨v, hv⟩ := h w <;> refine ⟨v, ?_⟩
  · rwa [mfderiv_eq_fderiv] at hv
  · rwa [mfderiv_eq_fderiv]

/-- A subset `s ⊆ N` is disjoint from the critical-value set `f '' criticalPoints I J f` if and only
if every point in `f ⁻¹' s` has surjective `mfderiv`. -/
theorem disjoint_image_criticalPoints_iff {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ E' H'} {f : M → N} {s : Set N} :
    Disjoint s (f '' criticalPoints I J f) ↔
      ∀ p ∈ f ⁻¹' s, Function.Surjective (mfderiv I J f p) := by
  rw [Set.disjoint_iff]
  constructor
  · intro h p hp
    rw [← notMem_criticalPoints_iff]
    intro hcrit
    exact h ⟨hp, ⟨p, hcrit, rfl⟩⟩
  · rintro h y ⟨hys, p, hcrit, rfl⟩
    exact hcrit (h p hys)

end CriticalPoints

/-! ## 2. Euclidean Coordinate Constructors and Calculus Helpers -/

section EuclideanHelpers

/-- Continuous linear coordinate projection `p ↦ p i` on `EuclideanSpace ℝ (Fin n)`. -/
noncomputable abbrev euclidProj {n : ℕ} (i : Fin n) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  EuclideanSpace.proj (𝕜 := ℝ) i

/-- Explicit 2-vector `(x₀, x₁)` in `EuclideanPlane = EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def vec2 (x₀ x₁ : ℝ) : EuclideanPlane :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![x₀, x₁]

/-- Explicit 4-vector `(y₁, y₂, y₃, t)` in `EuclideanSpace ℝ (Fin 4)`. -/
noncomputable def vec4 (y₁ y₂ y₃ t : ℝ) : EuclideanSpace ℝ (Fin 4) :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm ![y₁, y₂, y₃, t]

@[simp]
theorem vec2_zero (x₀ x₁ : ℝ) : vec2 x₀ x₁ 0 = x₀ := rfl

@[simp]
theorem vec2_one (x₀ x₁ : ℝ) : vec2 x₀ x₁ 1 = x₁ := rfl

theorem vec2_eq_toLp (x₀ x₁ : ℝ) : vec2 x₀ x₁ = WithLp.toLp 2 ![x₀, x₁] := rfl

@[simp]
theorem vec4_zero (y₁ y₂ y₃ t : ℝ) : vec4 y₁ y₂ y₃ t 0 = y₁ := rfl

@[simp]
theorem vec4_one (y₁ y₂ y₃ t : ℝ) : vec4 y₁ y₂ y₃ t 1 = y₂ := rfl

@[simp]
theorem vec4_two (y₁ y₂ y₃ t : ℝ) : vec4 y₁ y₂ y₃ t 2 = y₃ := rfl

@[simp]
theorem vec4_three (y₁ y₂ y₃ t : ℝ) : vec4 y₁ y₂ y₃ t 3 = t := rfl

theorem vec4_eq_toLp (y₁ y₂ y₃ t : ℝ) :
    vec4 y₁ y₂ y₃ t = WithLp.toLp 2 ![y₁, y₂, y₃, t] := rfl

theorem ext_vec2 {u v : EuclideanPlane} (h0 : u 0 = v 0) (h1 : u 1 = v 1) : u = v := by
  refine PiLp.ext fun i ↦ ?_
  fin_cases i
  · exact h0
  · exact h1

theorem ext_vec4 {u v : EuclideanSpace ℝ (Fin 4)}
    (h0 : u 0 = v 0) (h1 : u 1 = v 1) (h2 : u 2 = v 2) (h3 : u 3 = v 3) : u = v := by
  refine PiLp.ext fun i ↦ ?_
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- Smoothness of a map into `EuclideanPlane` from smoothness of its two components. -/
theorem contDiff_vec2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞}
    {g₀ g₁ : E → ℝ} (hg₀ : ContDiff ℝ n g₀) (hg₁ : ContDiff ℝ n g₁) :
    ContDiff ℝ n (fun x ↦ vec2 (g₀ x) (g₁ x)) := by
  refine (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp (contDiff_pi.mpr fun i ↦ ?_)
  fin_cases i
  · exact hg₀
  · exact hg₁

/-- Smoothness of a map into `EuclideanSpace ℝ (Fin 4)` from smoothness of its four components. -/
theorem contDiff_vec4 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞}
    {g₀ g₁ g₂ g₃ : E → ℝ} (hg₀ : ContDiff ℝ n g₀) (hg₁ : ContDiff ℝ n g₁)
    (hg₂ : ContDiff ℝ n g₂) (hg₃ : ContDiff ℝ n g₃) :
    ContDiff ℝ n (fun x ↦ vec4 (g₀ x) (g₁ x) (g₂ x) (g₃ x)) := by
  refine (EuclideanSpace.equiv (Fin 4) ℝ).symm.contDiff.comp (contDiff_pi.mpr fun i ↦ ?_)
  fin_cases i
  · exact hg₀
  · exact hg₁
  · exact hg₂
  · exact hg₃

/-- Build a continuous linear map `E →L[ℝ] EuclideanPlane` from two scalar continuous linear
functionals. -/
noncomputable def clmVec2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L₀ L₁ : E →L[ℝ] ℝ) : E →L[ℝ] EuclideanPlane :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦ if i = 0 then L₀ else L₁)

@[simp]
theorem clmVec2_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L₀ L₁ : E →L[ℝ] ℝ) (v : E) :
    clmVec2 L₀ L₁ v = vec2 (L₀ v) (L₁ v) := by
  refine PiLp.ext fun i ↦ ?_
  fin_cases i <;> rfl

/-- Fréchet derivative of `x ↦ vec2 (g₀ x) (g₁ x)`. -/
theorem hasFDerivAt_vec2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g₀ g₁ : E → ℝ} {L₀ L₁ : E →L[ℝ] ℝ} {x : E}
    (h₀ : HasFDerivAt g₀ L₀ x) (h₁ : HasFDerivAt g₁ L₁ x) :
    HasFDerivAt (fun y ↦ vec2 (g₀ y) (g₁ y)) (clmVec2 L₀ L₁) x := by
  have hpi : HasFDerivAt (fun y : E ↦ (![g₀ y, g₁ y] : Fin 2 → ℝ))
      (ContinuousLinearMap.pi fun i : Fin 2 ↦ if i = 0 then L₀ else L₁) x := by
    refine hasFDerivAt_pi.mpr fun i ↦ ?_
    fin_cases i
    · simpa using h₀
    · simpa using h₁
  exact (EuclideanSpace.equiv (Fin 2) ℝ).symm.hasFDerivAt.comp x hpi

end EuclideanHelpers

/-! ## 3. Indefinite Quadratic Fold (Eq. 2 of `S4TCdiffeo-Aug-2026.tex`, ADK 2005) & Gate 4 -/

section IndefiniteFold

/-- Local normal form for an **indefinite quadratic fold** (Equation 2 of `S4TCdiffeo-Aug-2026.tex`,
Auroux–Donaldson–Katzarkov 2005):
`(y₁, y₂, y₃, t) ↦ (y₁² - (y₂² + y₃²) / 2, t)`. -/
noncomputable def indefiniteFoldMap (p : EuclideanSpace ℝ (Fin 4)) : EuclideanPlane :=
  vec2 (p 0 ^ 2 - (p 1 ^ 2 + p 2 ^ 2) / 2) (p 3)

/-- Tuple representation `(y₁, y₂, y₃, t) ↦ (y₁² - (y₂² + y₃²) / 2, t)` of Equation 2. -/
noncomputable def indefiniteFoldTuple (q : ℝ × ℝ × ℝ × ℝ) : ℝ × ℝ :=
  (q.1 ^ 2 - (q.2.1 ^ 2 + q.2.2.1 ^ 2) / 2, q.2.2.2)

@[simp]
theorem indefiniteFoldMap_apply_zero (p : EuclideanSpace ℝ (Fin 4)) :
    indefiniteFoldMap p 0 = p 0 ^ 2 - (p 1 ^ 2 + p 2 ^ 2) / 2 := rfl

@[simp]
theorem indefiniteFoldMap_apply_one (p : EuclideanSpace ℝ (Fin 4)) :
    indefiniteFoldMap p 1 = p 3 := rfl

@[simp]
theorem indefiniteFoldMap_vec4 (y₁ y₂ y₃ t : ℝ) :
    indefiniteFoldMap (vec4 y₁ y₂ y₃ t) = vec2 (y₁ ^ 2 - (y₂ ^ 2 + y₃ ^ 2) / 2) t := rfl

/-- `indefiniteFoldMap` is $C^\infty$ smooth (`ContDiff ℝ ∞`). -/
theorem contDiff_indefiniteFoldMap : ContDiff ℝ ∞ indefiniteFoldMap := by
  have hp (i : Fin 4) : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 4) ↦ p i) :=
    (euclidProj i).contDiff
  exact contDiff_vec2
    (((hp 0).pow 2).sub ((((hp 1).pow 2).add ((hp 2).pow 2)).div_const 2))
    (hp 3)

/-- `indefiniteFoldMap` is $C^\infty$ smooth as a manifold map `𝓡 4 → 𝓡 2`. -/
theorem contMDiff_indefiniteFoldMap : ContMDiff (𝓡 4) (𝓡 2) ∞ indefiniteFoldMap :=
  contDiff_indefiniteFoldMap.contMDiff

/-- Explicit continuous linear map representing `fderiv ℝ indefiniteFoldMap p`. -/
noncomputable def indefiniteFoldFDerivCLM (p : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanPlane :=
  clmVec2
    ((2 * p 0) • euclidProj (0 : Fin 4) -
      p 1 • euclidProj (1 : Fin 4) -
      p 2 • euclidProj (2 : Fin 4))
    (euclidProj (3 : Fin 4))

@[simp]
theorem indefiniteFoldFDerivCLM_apply (p v : EuclideanSpace ℝ (Fin 4)) :
    indefiniteFoldFDerivCLM p v =
      vec2 (2 * p 0 * v 0 - p 1 * v 1 - p 2 * v 2) (v 3) := by
  simp [indefiniteFoldFDerivCLM, euclidProj]

/-- Exact `HasFDerivAt` for `indefiniteFoldMap` at every `p : EuclideanSpace ℝ (Fin 4)`. -/
theorem hasFDerivAt_indefiniteFoldMap (p : EuclideanSpace ℝ (Fin 4)) :
    HasFDerivAt indefiniteFoldMap (indefiniteFoldFDerivCLM p) p := by
  have hp (i : Fin 4) : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ x i)
      (euclidProj i) p :=
    (euclidProj i).hasFDerivAt
  have hsq (i : Fin 4) : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ x i ^ 2)
      ((2 * p i) • euclidProj i) p := by
    convert (hp i).pow 2 using 1
    ext v
    simp only [smul_apply, euclidProj, EuclideanSpace.proj, nsmul_eq_mul, Nat.cast_ofNat,
      smul_eq_mul]
    ring
  have hhalf : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ (x 1 ^ 2 + x 2 ^ 2) / 2)
      ((1 / 2 : ℝ) • ((2 * p 1) • euclidProj (1 : Fin 4) +
        (2 * p 2) • euclidProj (2 : Fin 4))) p := by
    have heq : (fun x : EuclideanSpace ℝ (Fin 4) ↦ (x 1 ^ 2 + x 2 ^ 2) / 2) =
        fun x ↦ (1 / 2 : ℝ) • (x 1 ^ 2 + x 2 ^ 2) := by
      funext x
      simp [smul_eq_mul, div_eq_inv_mul]
    rw [heq]
    exact ((hsq 1).add (hsq 2)).const_smul (1 / 2 : ℝ)
  have h0 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ x 0 ^ 2 - (x 1 ^ 2 + x 2 ^ 2) / 2)
      ((2 * p 0) • euclidProj (0 : Fin 4) -
        p 1 • euclidProj (1 : Fin 4) -
        p 2 • euclidProj (2 : Fin 4)) p := by
    convert (hsq 0).sub hhalf using 1
    ext v
    simp only [sub_apply, smul_apply, add_apply, euclidProj, EuclideanSpace.proj, smul_eq_mul]
    ring
  exact hasFDerivAt_vec2 h0 (hp 3)

@[simp]
theorem fderiv_indefiniteFoldMap (p : EuclideanSpace ℝ (Fin 4)) :
    fderiv ℝ indefiniteFoldMap p = indefiniteFoldFDerivCLM p :=
  (hasFDerivAt_indefiniteFoldMap p).fderiv

theorem fderiv_indefiniteFoldMap_apply (p v : EuclideanSpace ℝ (Fin 4)) :
    fderiv ℝ indefiniteFoldMap p v =
      vec2 (2 * p 0 * v 0 - p 1 * v 1 - p 2 * v 2) (v 3) := by
  rw [fderiv_indefiniteFoldMap, indefiniteFoldFDerivCLM_apply]

theorem mfderiv_indefiniteFoldMap_apply (p : EuclideanSpace ℝ (Fin 4))
    (v : TangentSpace (𝓡 4) p) :
    let v' : EuclideanSpace ℝ (Fin 4) := v
    (mfderiv (𝓡 4) (𝓡 2) indefiniteFoldMap p v : EuclideanPlane) =
      vec2 (2 * p 0 * v' 0 - p 1 * v' 1 - p 2 * v' 2) (v' 3) := by
  rw [mfderiv_eq_fderiv]
  exact fderiv_indefiniteFoldMap_apply p v

/-- Exact characterization of regular points of `indefiniteFoldMap`: `fderiv ℝ indefiniteFoldMap p`
is surjective if and only if `(p 0, p 1, p 2) ≠ (0, 0, 0)`. -/
theorem surjective_fderiv_indefiniteFoldMap_iff (p : EuclideanSpace ℝ (Fin 4)) :
    Function.Surjective (fderiv ℝ indefiniteFoldMap p) ↔
      p 0 ≠ 0 ∨ p 1 ≠ 0 ∨ p 2 ≠ 0 := by
  rw [fderiv_indefiniteFoldMap]
  constructor
  · intro hsurj
    by_contra! hzero
    rcases hzero with ⟨h0, h1, h2⟩
    obtain ⟨v, hv⟩ := hsurj (vec2 1 0)
    have hv0 := congrArg (fun u : EuclideanPlane ↦ u 0) hv
    simp [h0, h1, h2] at hv0
  · intro h w
    rcases h with h0 | h1 | h2
    · refine ⟨vec4 (w 0 / (2 * p 0)) 0 0 (w 1), ext_vec2 ?_ rfl⟩
      simp only [indefiniteFoldFDerivCLM_apply, vec2_zero, vec4_zero, vec4_one, vec4_two]
      field_simp [h0]
      ring
    · refine ⟨vec4 0 (-w 0 / p 1) 0 (w 1), ext_vec2 ?_ rfl⟩
      simp only [indefiniteFoldFDerivCLM_apply, vec2_zero, vec4_zero, vec4_one, vec4_two]
      field_simp [h1]
      ring
    · refine ⟨vec4 0 0 (-w 0 / p 2) (w 1), ext_vec2 ?_ rfl⟩
      simp only [indefiniteFoldFDerivCLM_apply, vec2_zero, vec4_zero, vec4_one, vec4_two]
      field_simp [h2]
      ring

/-- Exact characterization of the critical locus of `indefiniteFoldMap`:
`Crit(indefiniteFoldMap) = {p | p 0 = 0 ∧ p 1 = 0 ∧ p 2 = 0}`. -/
theorem euclideanCriticalPoints_indefiniteFoldMap :
    euclideanCriticalPoints indefiniteFoldMap =
      {p : EuclideanSpace ℝ (Fin 4) | p 0 = 0 ∧ p 1 = 0 ∧ p 2 = 0} := by
  ext p
  rw [mem_euclideanCriticalPoints_iff, surjective_fderiv_indefiniteFoldMap_iff, Set.mem_ofPred_eq]
  tauto

/-- Manifold-level critical locus of `indefiniteFoldMap`:
`criticalPoints (𝓡 4) (𝓡 2) indefiniteFoldMap = {p | p 0 = 0 ∧ p 1 = 0 ∧ p 2 = 0}`. -/
theorem criticalPoints_indefiniteFoldMap :
    criticalPoints (𝓡 4) (𝓡 2) indefiniteFoldMap =
      {p : EuclideanSpace ℝ (Fin 4) | p 0 = 0 ∧ p 1 = 0 ∧ p 2 = 0} := by
  rw [criticalPoints_euclidean_eq, euclideanCriticalPoints_indefiniteFoldMap]

/-- **Gate 4 Singular Witness**: `(0, 0, 0, t)` lies in the critical locus of `indefiniteFoldMap`
for every `t : ℝ`. -/
theorem indefiniteFold_zero_mem_criticalPoints (t : ℝ) :
    vec4 0 0 0 t ∈ criticalPoints (𝓡 4) (𝓡 2) indefiniteFoldMap := by
  rw [criticalPoints_indefiniteFoldMap]
  simp

/-- **Gate 4 Regular Witness**: `(1, 0, 0, t)` lies outside the critical locus of
`indefiniteFoldMap` for every `t : ℝ`. -/
theorem indefiniteFold_one_notMem_criticalPoints (t : ℝ) :
    vec4 1 0 0 t ∉ criticalPoints (𝓡 4) (𝓡 2) indefiniteFoldMap := by
  rw [criticalPoints_indefiniteFoldMap]
  simp

/-- Surjectivity of `mfderiv (𝓡 4) (𝓡 2) indefiniteFoldMap` at `(1, 0, 0, t)` (Gate 4 regular
submersion witness). -/
theorem surjective_mfderiv_indefiniteFold_one (t : ℝ) :
    Function.Surjective (mfderiv (𝓡 4) (𝓡 2) indefiniteFoldMap (vec4 1 0 0 t)) :=
  notMem_criticalPoints_iff.mp (indefiniteFold_one_notMem_criticalPoints t)

/-! ### ADK Equatorial Cobordism Regular-Fiber Transition (`c > 0` vs `c < 0`) -/

/-- Fiber `indefiniteFoldMap ⁻¹' {(c, t)}` of the ADK cobordism model over `(c, t) ∈ ℝ²`. -/
noncomputable def indefiniteFoldFiber (c t : ℝ) : Set (EuclideanSpace ℝ (Fin 4)) :=
  indefiniteFoldMap ⁻¹' {vec2 c t}

@[simp]
theorem mem_indefiniteFoldFiber_iff {c t : ℝ} {p : EuclideanSpace ℝ (Fin 4)} :
    p ∈ indefiniteFoldFiber c t ↔
      p 0 ^ 2 - (p 1 ^ 2 + p 2 ^ 2) / 2 = c ∧ p 3 = t := by
  simp only [indefiniteFoldFiber, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    exact ⟨by simpa using congrArg (fun u : EuclideanPlane ↦ u 0) h,
      by simpa using congrArg (fun u : EuclideanPlane ↦ u 1) h⟩
  · rintro ⟨h0, h1⟩
    exact ext_vec2 h0 h1

/-- Every fiber `indefiniteFoldFiber c t` with `c ≠ 0` is disjoint from the critical circle
`{y₁ = y₂ = y₃ = 0}`. -/
theorem disjoint_indefiniteFoldFiber_criticalPoints {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    Disjoint (indefiniteFoldFiber c t) (criticalPoints (𝓡 4) (𝓡 2) indefiniteFoldMap) := by
  rw [criticalPoints_indefiniteFoldMap, Set.disjoint_iff]
  rintro p ⟨hp_fib, h0, h1, h2⟩
  rw [mem_indefiniteFoldFiber_iff] at hp_fib
  apply hc
  linarith [hp_fib.1, sq_eq_zero_iff.mpr h0, sq_eq_zero_iff.mpr h1, sq_eq_zero_iff.mpr h2]

/-- Upper hyperboloid sheet `(y₂, y₃) ↦ (+√(c + (y₂² + y₃²)/2), y₂, y₃, t)` over `c > 0`. -/
noncomputable def indefiniteFoldPosSheet (c t : ℝ) (u : EuclideanPlane) :
    EuclideanSpace ℝ (Fin 4) :=
  vec4 (Real.sqrt (c + (u 0 ^ 2 + u 1 ^ 2) / 2)) (u 0) (u 1) t

/-- Lower hyperboloid sheet `(y₂, y₃) ↦ (-√(c + (y₂² + y₃²)/2), y₂, y₃, t)` over `c > 0`. -/
noncomputable def indefiniteFoldNegSheet (c t : ℝ) (u : EuclideanPlane) :
    EuclideanSpace ℝ (Fin 4) :=
  vec4 (-Real.sqrt (c + (u 0 ^ 2 + u 1 ^ 2) / 2)) (u 0) (u 1) t

/-- Smoothness (`ContDiff ℝ ∞`) of `indefiniteFoldPosSheet c t` for `c > 0`. -/
theorem contDiff_indefiniteFoldPosSheet {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ContDiff ℝ ∞ (indefiniteFoldPosSheet c t) := by
  have hu (i : Fin 2) : ContDiff ℝ ∞ (fun u : EuclideanPlane ↦ u i) :=
    (euclidProj i).contDiff
  have hrad : ContDiff ℝ ∞ (fun u : EuclideanPlane ↦ c + (u 0 ^ 2 + u 1 ^ 2) / 2) :=
    contDiff_const.add ((((hu 0).pow 2).add ((hu 1).pow 2)).div_const 2)
  have hsqrt : ContDiff ℝ ∞ (fun u : EuclideanPlane ↦ Real.sqrt (c + (u 0 ^ 2 + u 1 ^ 2) / 2)) :=
    contDiff_iff_contDiffAt.mpr fun u ↦
      (Real.contDiffAt_sqrt (by positivity)).comp u hrad.contDiffAt
  exact contDiff_vec4 hsqrt (hu 0) (hu 1) contDiff_const

/-- Smoothness (`ContDiff ℝ ∞`) of `indefiniteFoldNegSheet c t` for `c > 0`. -/
theorem contDiff_indefiniteFoldNegSheet {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ContDiff ℝ ∞ (indefiniteFoldNegSheet c t) := by
  have hu (i : Fin 2) : ContDiff ℝ ∞ (fun u : EuclideanPlane ↦ u i) :=
    (euclidProj i).contDiff
  have hrad : ContDiff ℝ ∞ (fun u : EuclideanPlane ↦ c + (u 0 ^ 2 + u 1 ^ 2) / 2) :=
    contDiff_const.add ((((hu 0).pow 2).add ((hu 1).pow 2)).div_const 2)
  have hsqrt : ContDiff ℝ ∞ (fun u : EuclideanPlane ↦ Real.sqrt (c + (u 0 ^ 2 + u 1 ^ 2) / 2)) :=
    contDiff_iff_contDiffAt.mpr fun u ↦
      (Real.contDiffAt_sqrt (by positivity)).comp u hrad.contDiffAt
  exact contDiff_vec4 hsqrt.neg (hu 0) (hu 1) contDiff_const

/-- Decomposition of `indefiniteFoldFiber c t` for `c > 0` into two disjoint smooth sheets. -/
theorem indefiniteFoldFiber_eq_union_sheets {c : ℝ} (hc : 0 < c) (t : ℝ) :
    indefiniteFoldFiber c t =
      Set.range (indefiniteFoldPosSheet c t) ∪ Set.range (indefiniteFoldNegSheet c t) := by
  ext p
  simp only [mem_indefiniteFoldFiber_iff, Set.mem_union, Set.mem_range]
  constructor
  · rintro ⟨heq, rfl⟩
    have hpos : 0 ≤ c + (p 1 ^ 2 + p 2 ^ 2) / 2 := by positivity
    have hsq : p 0 ^ 2 = (Real.sqrt (c + (p 1 ^ 2 + p 2 ^ 2) / 2)) ^ 2 := by
      rw [Real.sq_sqrt hpos]
      linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hp0 | hp0
    · left
      exact ⟨vec2 (p 1) (p 2), ext_vec4 hp0.symm rfl rfl rfl⟩
    · right
      exact ⟨vec2 (p 1) (p 2), ext_vec4 hp0.symm rfl rfl rfl⟩
  · rintro (⟨u, rfl⟩ | ⟨u, rfl⟩)
    · refine ⟨?_, rfl⟩
      simp only [indefiniteFoldPosSheet, vec4_zero, vec4_one, vec4_two]
      rw [Real.sq_sqrt (by positivity)]
      ring
    · refine ⟨?_, rfl⟩
      simp only [indefiniteFoldNegSheet, vec4_zero, vec4_one, vec4_two, neg_sq]
      rw [Real.sq_sqrt (by positivity)]
      ring

/-- Over `c > 0`, the regular fiber `indefiniteFoldFiber c t` is disconnected (`y₁ > 0` vs
`y₁ < 0`). -/
theorem not_isPreconnected_indefiniteFoldFiber_of_pos {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ¬ IsPreconnected (indefiniteFoldFiber c t) := by
  intro hpre
  let Upos : Set (EuclideanSpace ℝ (Fin 4)) := {p | 0 < p 0}
  let Uneg : Set (EuclideanSpace ℝ (Fin 4)) := {p | p 0 < 0}
  have hopen_pos : IsOpen Upos := isOpen_lt continuous_const (euclidProj 0).continuous
  have hopen_neg : IsOpen Uneg := isOpen_lt (euclidProj 0).continuous continuous_const
  have hcov : indefiniteFoldFiber c t ⊆ Upos ∪ Uneg := by
    intro p hp
    rw [mem_indefiniteFoldFiber_iff] at hp
    have hsq : 0 < p 0 ^ 2 := by
      have hnn : 0 ≤ (p 1 ^ 2 + p 2 ^ 2) / 2 := by positivity
      linarith
    rcases ne_iff_lt_or_gt.mp (sq_pos_iff.mp hsq) with hlt | hgt
    · exact Or.inr hlt
    · exact Or.inl hgt
  have hne_pos : (indefiniteFoldFiber c t ∩ Upos).Nonempty := by
    refine ⟨indefiniteFoldPosSheet c t 0, ?_, ?_⟩
    · rw [indefiniteFoldFiber_eq_union_sheets hc t]
      exact Or.inl ⟨0, rfl⟩
    · change 0 < (indefiniteFoldPosSheet c t 0) 0
      simp only [indefiniteFoldPosSheet, vec4_zero]
      exact Real.sqrt_pos.mpr (by positivity)
  have hne_neg : (indefiniteFoldFiber c t ∩ Uneg).Nonempty := by
    refine ⟨indefiniteFoldNegSheet c t 0, ?_, ?_⟩
    · rw [indefiniteFoldFiber_eq_union_sheets hc t]
      exact Or.inr ⟨0, rfl⟩
    · change (indefiniteFoldNegSheet c t 0) 0 < 0
      simp only [indefiniteFoldNegSheet, vec4_zero, Left.neg_neg_iff]
      exact Real.sqrt_pos.mpr (by positivity)
  obtain ⟨p, -, hp_pos, hp_neg⟩ := hpre Upos Uneg hopen_pos hopen_neg hcov hne_pos hne_neg
  change 0 < p 0 at hp_pos
  change p 0 < 0 at hp_neg
  exact lt_asymm hp_pos hp_neg

/-- Cylindrical parametrization `Circle × ℝ → indefiniteFoldFiber c t` over `c < 0`
(one-sheeted hyperboloid carrying the vanishing cycle `Circle × {0}` of radius `√(-2c)`). -/
noncomputable def indefiniteFoldCylinderParam (c t : ℝ) (z : Circle × ℝ) :
    EuclideanSpace ℝ (Fin 4) :=
  vec4 z.2 (Real.sqrt (2 * (z.2 ^ 2 - c)) * (z.1 : ℂ).re)
    (Real.sqrt (2 * (z.2 ^ 2 - c)) * (z.1 : ℂ).im) t

/-- Smoothness of `indefiniteFoldCylinderParam c t` as a manifold map `(𝓡 1).prod 𝓘(ℝ, ℝ) → 𝓡 4`
for `c < 0`. -/
theorem contMDiff_indefiniteFoldCylinderParam {c : ℝ} (hc : c < 0) (t : ℝ) :
    ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 4) ∞ (indefiniteFoldCylinderParam c t) := by
  let _ : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
  have hz1 : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℂ) ∞ (fun z : Circle × ℝ ↦ (z.1 : ℂ)) :=
    contMDiff_coe_sphere.comp contMDiff_fst
  have hre : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun z : Circle × ℝ ↦ (z.1 : ℂ).re) :=
    Complex.reCLM.contDiff.contMDiff.comp hz1
  have him : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun z : Circle × ℝ ↦ (z.1 : ℂ).im) :=
    Complex.imCLM.contDiff.contMDiff.comp hz1
  have hs : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun z : Circle × ℝ ↦ z.2) :=
    contMDiff_snd
  have hrad_diff : ContDiff ℝ ∞ (fun s : ℝ ↦ 2 * (s ^ 2 - c)) :=
    contDiff_const.mul ((contDiff_id.pow 2).sub contDiff_const)
  have hsqrt_diff : ContDiff ℝ ∞ (fun s : ℝ ↦ Real.sqrt (2 * (s ^ 2 - c))) :=
    contDiff_iff_contDiffAt.mpr fun s ↦
      (Real.contDiffAt_sqrt (by nlinarith [sq_nonneg s])).comp s hrad_diff.contDiffAt
  have hsqrt : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : Circle × ℝ ↦ Real.sqrt (2 * (z.2 ^ 2 - c))) :=
    hsqrt_diff.contMDiff.comp hs
  have hmul : ContDiff ℝ ∞ (fun q : ℝ × ℝ ↦ q.1 * q.2) :=
    contDiff_fst.mul contDiff_snd
  have htuple : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Fin 4 → ℝ) ∞
      (fun z : Circle × ℝ ↦
        ![z.2, Real.sqrt (2 * (z.2 ^ 2 - c)) * (z.1 : ℂ).re,
          Real.sqrt (2 * (z.2 ^ 2 - c)) * (z.1 : ℂ).im, t]) := by
    refine contMDiff_pi_module_iff.mpr fun i ↦ ?_
    fin_cases i
    · exact hs
    · exact hmul.contMDiff.comp (hsqrt.prodMk_space hre)
    · exact hmul.contMDiff.comp (hsqrt.prodMk_space him)
    · exact contMDiff_const
  exact (EuclideanSpace.equiv (Fin 4) ℝ).symm.contDiff.contMDiff.comp htuple

/-- For `c < 0`, `indefiniteFoldCylinderParam c t` maps `Circle × ℝ` onto
`indefiniteFoldFiber c t`. -/
theorem range_indefiniteFoldCylinderParam {c : ℝ} (hc : c < 0) (t : ℝ) :
    Set.range (indefiniteFoldCylinderParam c t) = indefiniteFoldFiber c t := by
  ext p
  simp only [Set.mem_range, mem_indefiniteFoldFiber_iff]
  constructor
  · rintro ⟨⟨θ, s⟩, rfl⟩
    refine ⟨?_, rfl⟩
    simp only [indefiniteFoldCylinderParam, vec4_zero, vec4_one, vec4_two]
    have hpos : 0 ≤ 2 * (s ^ 2 - c) := by nlinarith [sq_nonneg s]
    have hcircle : (θ : ℂ).re ^ 2 + (θ : ℂ).im ^ 2 = 1 := by
      simpa [Complex.normSq_apply, sq] using Circle.normSq_coe θ
    calc
      s ^ 2 - ((Real.sqrt (2 * (s ^ 2 - c)) * (θ : ℂ).re) ^ 2 +
          (Real.sqrt (2 * (s ^ 2 - c)) * (θ : ℂ).im) ^ 2) / 2
        = s ^ 2 - (Real.sqrt (2 * (s ^ 2 - c)) ^ 2 * ((θ : ℂ).re ^ 2 + (θ : ℂ).im ^ 2)) / 2 := by
          ring
      _ = s ^ 2 - (2 * (s ^ 2 - c) * 1) / 2 := by rw [Real.sq_sqrt hpos, hcircle]
      _ = c := by ring
  · rintro ⟨heq, rfl⟩
    have hr2_eq : p 1 ^ 2 + p 2 ^ 2 = 2 * (p 0 ^ 2 - c) := by linarith
    have hr2_pos : 0 < 2 * (p 0 ^ 2 - c) := by nlinarith [sq_nonneg (p 0)]
    let R : ℝ := Real.sqrt (2 * (p 0 ^ 2 - c))
    have hR_pos : 0 < R := Real.sqrt_pos.mpr hr2_pos
    have hR_ne : R ≠ 0 := hR_pos.ne'
    let zc : ℂ := ⟨p 1 / R, p 2 / R⟩
    have hzc_mem : zc ∈ Metric.sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm]
      have hsq1 : ‖zc‖ ^ 2 = 1 := by
        rw [Complex.sq_norm, Complex.normSq_mk]
        have hR_sq : R ^ 2 = 2 * (p 0 ^ 2 - c) := Real.sq_sqrt hr2_pos.le
        calc
          p 1 / R * (p 1 / R) + p 2 / R * (p 2 / R)
            = (p 1 ^ 2 + p 2 ^ 2) / R ^ 2 := by ring
          _ = (2 * (p 0 ^ 2 - c)) / (2 * (p 0 ^ 2 - c)) := by rw [hr2_eq, hR_sq]
          _ = 1 := div_self hr2_pos.ne'
      nlinarith [norm_nonneg zc]
    refine ⟨(⟨zc, hzc_mem⟩, p 0), ext_vec4 rfl ?_ ?_ rfl⟩
    · simp only [indefiniteFoldCylinderParam, vec4_one, zc]
      exact mul_div_cancel₀ (p 1) hR_ne
    · simp only [indefiniteFoldCylinderParam, vec4_two, zc]
      exact mul_div_cancel₀ (p 2) hR_ne

theorem injective_indefiniteFoldCylinderParam {c : ℝ} (hc : c < 0) (t : ℝ) :
    Function.Injective (indefiniteFoldCylinderParam c t) := by
  rintro ⟨θ₁, s₁⟩ ⟨θ₂, s₂⟩ h
  have hs : s₁ = s₂ := congrArg (fun u : EuclideanSpace ℝ (Fin 4) ↦ u 0) h
  subst hs
  have hpos : 0 < Real.sqrt (2 * (s₁ ^ 2 - c)) :=
    Real.sqrt_pos.mpr (by nlinarith [sq_nonneg s₁])
  have h1 := congrArg (fun u : EuclideanSpace ℝ (Fin 4) ↦ u 1) h
  have h2 := congrArg (fun u : EuclideanSpace ℝ (Fin 4) ↦ u 2) h
  simp only [indefiniteFoldCylinderParam, vec4_one, vec4_two] at h1 h2
  have hre : (θ₁ : ℂ).re = (θ₂ : ℂ).re := mul_left_cancel₀ hpos.ne' h1
  have him : (θ₁ : ℂ).im = (θ₂ : ℂ).im := mul_left_cancel₀ hpos.ne' h2
  exact Prod.ext (Subtype.ext (Complex.ext hre him)) rfl

/-- Over `c < 0`, the regular fiber `indefiniteFoldFiber c t` is connected (contrasting with
`not_isPreconnected_indefiniteFoldFiber_of_pos` for `c > 0`). -/
theorem isConnected_indefiniteFoldFiber_of_neg {c : ℝ} (hc : c < 0) (t : ℝ) :
    IsConnected (indefiniteFoldFiber c t) := by
  let _ : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
  have _ : ConnectedSpace Circle := TauCeti.connectedSpace_sphere (E := ℂ) 1
  rw [← range_indefiniteFoldCylinderParam hc t]
  exact isConnected_range (contMDiff_indefiniteFoldCylinderParam hc t).continuous

end IndefiniteFold

/-! ## 4. Real Lefschetz Singularity and Wrinkled Cusp Normal Forms (`Lekili 2009`, `ST16`) -/

section LefschetzAndCusp

/-- Real normal form of an **achiral / oriented Lefschetz singularity** (`ℂ² → ℂ`,
`(z₁, z₂) ↦ z₁² + z₂²` in real coordinates `(x₁, y₁, x₂, y₂)`):
`(x₁, y₁, x₂, y₂) ↦ (x₁² - y₁² + x₂² - y₂², 2 x₁ y₁ + 2 x₂ y₂)`. -/
noncomputable def realLefschetzMap (p : EuclideanSpace ℝ (Fin 4)) : EuclideanPlane :=
  vec2 (p 0 ^ 2 - p 1 ^ 2 + p 2 ^ 2 - p 3 ^ 2) (2 * p 0 * p 1 + 2 * p 2 * p 3)

@[simp]
theorem realLefschetzMap_apply_zero (p : EuclideanSpace ℝ (Fin 4)) :
    realLefschetzMap p 0 = p 0 ^ 2 - p 1 ^ 2 + p 2 ^ 2 - p 3 ^ 2 := rfl

@[simp]
theorem realLefschetzMap_apply_one (p : EuclideanSpace ℝ (Fin 4)) :
    realLefschetzMap p 1 = 2 * p 0 * p 1 + 2 * p 2 * p 3 := rfl

/-- `realLefschetzMap` is $C^\infty$ smooth (`ContDiff ℝ ∞`). -/
theorem contDiff_realLefschetzMap : ContDiff ℝ ∞ realLefschetzMap := by
  have hp (i : Fin 4) : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 4) ↦ p i) :=
    (euclidProj i).contDiff
  exact contDiff_vec2
    (((((hp 0).pow 2).sub ((hp 1).pow 2)).add ((hp 2).pow 2)).sub ((hp 3).pow 2))
    (((contDiff_const.mul (hp 0)).mul (hp 1)).add ((contDiff_const.mul (hp 2)).mul (hp 3)))

/-- `realLefschetzMap` is $C^\infty$ smooth as a manifold map `𝓡 4 → 𝓡 2`. -/
theorem contMDiff_realLefschetzMap : ContMDiff (𝓡 4) (𝓡 2) ∞ realLefschetzMap :=
  contDiff_realLefschetzMap.contMDiff

/-- Continuous linear map representing `fderiv ℝ realLefschetzMap p`. -/
noncomputable def realLefschetzFDerivCLM (p : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanPlane :=
  clmVec2
    ((2 * p 0) • euclidProj (0 : Fin 4) -
      (2 * p 1) • euclidProj (1 : Fin 4) +
      (2 * p 2) • euclidProj (2 : Fin 4) -
      (2 * p 3) • euclidProj (3 : Fin 4))
    ((2 * p 1) • euclidProj (0 : Fin 4) +
      (2 * p 0) • euclidProj (1 : Fin 4) +
      (2 * p 3) • euclidProj (2 : Fin 4) +
      (2 * p 2) • euclidProj (3 : Fin 4))

@[simp]
theorem realLefschetzFDerivCLM_apply (p v : EuclideanSpace ℝ (Fin 4)) :
    realLefschetzFDerivCLM p v =
      vec2 (2 * p 0 * v 0 - 2 * p 1 * v 1 + 2 * p 2 * v 2 - 2 * p 3 * v 3)
        (2 * p 1 * v 0 + 2 * p 0 * v 1 + 2 * p 3 * v 2 + 2 * p 2 * v 3) := by
  simp [realLefschetzFDerivCLM, euclidProj]

theorem hasFDerivAt_realLefschetzMap (p : EuclideanSpace ℝ (Fin 4)) :
    HasFDerivAt realLefschetzMap (realLefschetzFDerivCLM p) p := by
  have hp (i : Fin 4) : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ x i)
      (euclidProj i) p :=
    (euclidProj i).hasFDerivAt
  have hsq (i : Fin 4) : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ x i ^ 2)
      ((2 * p i) • euclidProj i) p := by
    convert (hp i).pow 2 using 1
    ext v
    simp only [smul_apply, euclidProj, EuclideanSpace.proj, nsmul_eq_mul, Nat.cast_ofNat,
      smul_eq_mul]
    ring
  have h0 := (((hsq 0).sub (hsq 1)).add (hsq 2)).sub (hsq 3)
  have hprod (i j : Fin 4) :
      HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ 2 * x i * x j)
        ((2 * p j) • euclidProj i + (2 * p i) • euclidProj j) p := by
    have heq : (fun x : EuclideanSpace ℝ (Fin 4) ↦ 2 * x i * x j) =
        fun x ↦ ((2 : ℝ) • x i) * x j := by
      funext x
      simp [smul_eq_mul]
    rw [heq]
    convert (((hp i).const_smul (2 : ℝ)).mul (hp j)) using 1
    ext v
    simp only [add_apply, smul_apply, Pi.smul_apply, euclidProj, EuclideanSpace.proj, smul_eq_mul]
    ring
  have h1 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ 2 * x 0 * x 1 + 2 * x 2 * x 3)
      ((2 * p 1) • euclidProj (0 : Fin 4) +
        (2 * p 0) • euclidProj (1 : Fin 4) +
        (2 * p 3) • euclidProj (2 : Fin 4) +
        (2 * p 2) • euclidProj (3 : Fin 4)) p := by
    convert (hprod 0 1).add (hprod 2 3) using 1
    ext v
    simp only [add_apply]
    ring
  exact hasFDerivAt_vec2 h0 h1

@[simp]
theorem fderiv_realLefschetzMap (p : EuclideanSpace ℝ (Fin 4)) :
    fderiv ℝ realLefschetzMap p = realLefschetzFDerivCLM p :=
  (hasFDerivAt_realLefschetzMap p).fderiv

/-- `fderiv ℝ realLefschetzMap p` is surjective if and only if `p ≠ 0`. -/
theorem surjective_fderiv_realLefschetzMap_iff (p : EuclideanSpace ℝ (Fin 4)) :
    Function.Surjective (fderiv ℝ realLefschetzMap p) ↔ p ≠ 0 := by
  rw [fderiv_realLefschetzMap]
  constructor
  · rintro hsurj rfl
    obtain ⟨v, hv⟩ := hsurj (vec2 1 0)
    have hv0 := congrArg (fun u : EuclideanPlane ↦ u 0) hv
    simp at hv0
  · intro hp w
    by_cases h01 : p 0 ^ 2 + p 1 ^ 2 ≠ 0
    · let s := p 0 ^ 2 + p 1 ^ 2
      refine ⟨vec4 ((p 0 * w 0 + p 1 * w 1) / (2 * s))
        ((-p 1 * w 0 + p 0 * w 1) / (2 * s)) 0 0, ext_vec2 ?_ ?_⟩
      · simp only [realLefschetzFDerivCLM_apply, vec2_zero, vec4_zero, vec4_one, vec4_two,
          vec4_three, s]
        field_simp [h01]
        ring
      · simp only [realLefschetzFDerivCLM_apply, vec2_one, vec4_zero, vec4_one, vec4_two,
          vec4_three, s]
        field_simp [h01]
        ring
    · push Not at h01
      have hp0 : p 0 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
      have hp1 : p 1 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
      have h23 : p 2 ^ 2 + p 3 ^ 2 ≠ 0 := by
        intro h23_zero
        have hp2 : p 2 = 0 := by nlinarith [sq_nonneg (p 2), sq_nonneg (p 3)]
        have hp3 : p 3 = 0 := by nlinarith [sq_nonneg (p 2), sq_nonneg (p 3)]
        exact hp (ext_vec4 hp0 hp1 hp2 hp3)
      let s := p 2 ^ 2 + p 3 ^ 2
      refine ⟨vec4 0 0 ((p 2 * w 0 + p 3 * w 1) / (2 * s))
        ((-p 3 * w 0 + p 2 * w 1) / (2 * s)), ext_vec2 ?_ ?_⟩
      · simp only [realLefschetzFDerivCLM_apply, vec2_zero, vec4_zero, vec4_one, vec4_two,
          vec4_three, s]
        field_simp [h23]
        ring
      · simp only [realLefschetzFDerivCLM_apply, vec2_one, vec4_zero, vec4_one, vec4_two,
          vec4_three, s]
        field_simp [h23]
        ring

/-- Exact critical locus of `realLefschetzMap`: the isolated origin `{0}`. -/
theorem criticalPoints_realLefschetzMap :
    criticalPoints (𝓡 4) (𝓡 2) realLefschetzMap = {0} := by
  rw [criticalPoints_euclidean_eq]
  ext p
  rw [mem_euclideanCriticalPoints_iff, surjective_fderiv_realLefschetzMap_iff, not_not,
    Set.mem_singleton_iff]

/-- Local normal form of a **wrinkled cusp singularity** (`Lekili 2009`, `ST16`):
`(t, x₁, x₂, x₃) ↦ (t, x₁³ - 3 t x₁ + x₂² - x₃²)`. -/
noncomputable def wrinkledCuspMap (p : EuclideanSpace ℝ (Fin 4)) : EuclideanPlane :=
  vec2 (p 0) (p 1 ^ 3 - 3 * p 0 * p 1 + p 2 ^ 2 - p 3 ^ 2)

@[simp]
theorem wrinkledCuspMap_apply_zero (p : EuclideanSpace ℝ (Fin 4)) :
    wrinkledCuspMap p 0 = p 0 := rfl

@[simp]
theorem wrinkledCuspMap_apply_one (p : EuclideanSpace ℝ (Fin 4)) :
    wrinkledCuspMap p 1 = p 1 ^ 3 - 3 * p 0 * p 1 + p 2 ^ 2 - p 3 ^ 2 := rfl

/-- `wrinkledCuspMap` is $C^\infty$ smooth (`ContDiff ℝ ∞`). -/
theorem contDiff_wrinkledCuspMap : ContDiff ℝ ∞ wrinkledCuspMap := by
  have hp (i : Fin 4) : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 4) ↦ p i) :=
    (euclidProj i).contDiff
  exact contDiff_vec2 (hp 0)
    (((((hp 1).pow 3).sub ((contDiff_const.mul (hp 0)).mul (hp 1))).add ((hp 2).pow 2)).sub
      ((hp 3).pow 2))

/-- `wrinkledCuspMap` is $C^\infty$ smooth as a manifold map `𝓡 4 → 𝓡 2`. -/
theorem contMDiff_wrinkledCuspMap : ContMDiff (𝓡 4) (𝓡 2) ∞ wrinkledCuspMap :=
  contDiff_wrinkledCuspMap.contMDiff

/-- Continuous linear map representing `fderiv ℝ wrinkledCuspMap p`. -/
noncomputable def wrinkledCuspFDerivCLM (p : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanPlane :=
  clmVec2
    (euclidProj (0 : Fin 4))
    ((-3 * p 1) • euclidProj (0 : Fin 4) +
      (3 * p 1 ^ 2 - 3 * p 0) • euclidProj (1 : Fin 4) +
      (2 * p 2) • euclidProj (2 : Fin 4) -
      (2 * p 3) • euclidProj (3 : Fin 4))

@[simp]
theorem wrinkledCuspFDerivCLM_apply (p v : EuclideanSpace ℝ (Fin 4)) :
    wrinkledCuspFDerivCLM p v =
      vec2 (v 0) (-3 * p 1 * v 0 + (3 * p 1 ^ 2 - 3 * p 0) * v 1 + 2 * p 2 * v 2 -
        2 * p 3 * v 3) := by
  simp [wrinkledCuspFDerivCLM, euclidProj]

theorem hasFDerivAt_wrinkledCuspMap (p : EuclideanSpace ℝ (Fin 4)) :
    HasFDerivAt wrinkledCuspMap (wrinkledCuspFDerivCLM p) p := by
  have hp (i : Fin 4) : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ x i)
      (euclidProj i) p :=
    (euclidProj i).hasFDerivAt
  have hcube : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ x 1 ^ 3)
      ((3 * p 1 ^ 2) • euclidProj (1 : Fin 4)) p := by
    convert (hp 1).pow 3 using 1
    ext v
    simp [smul_apply, euclidProj, nsmul_eq_mul, smul_eq_mul]
  have hsq (i : Fin 4) : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ x i ^ 2)
      ((2 * p i) • euclidProj i) p := by
    convert (hp i).pow 2 using 1
    ext v
    simp only [smul_apply, euclidProj, EuclideanSpace.proj, nsmul_eq_mul, Nat.cast_ofNat,
      smul_eq_mul]
    ring
  have hmix : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ 3 * x 0 * x 1)
      ((3 * p 1) • euclidProj (0 : Fin 4) +
        (3 * p 0) • euclidProj (1 : Fin 4)) p := by
    have heq : (fun x : EuclideanSpace ℝ (Fin 4) ↦ 3 * x 0 * x 1) =
        fun x ↦ ((3 : ℝ) • x 0) * x 1 := by
      funext x
      simp [smul_eq_mul]
    rw [heq]
    convert (((hp 0).const_smul (3 : ℝ)).mul (hp 1)) using 1
    ext v
    simp only [add_apply, smul_apply, Pi.smul_apply, euclidProj, EuclideanSpace.proj, smul_eq_mul]
    ring
  have h1 : HasFDerivAt
      (fun x : EuclideanSpace ℝ (Fin 4) ↦ x 1 ^ 3 - 3 * x 0 * x 1 + x 2 ^ 2 - x 3 ^ 2)
      ((-3 * p 1) • euclidProj (0 : Fin 4) +
        (3 * p 1 ^ 2 - 3 * p 0) • euclidProj (1 : Fin 4) +
        (2 * p 2) • euclidProj (2 : Fin 4) -
        (2 * p 3) • euclidProj (3 : Fin 4)) p := by
    convert ((hcube.sub hmix).add (hsq 2)).sub (hsq 3) using 1
    ext v
    simp only [sub_apply, add_apply, smul_apply, euclidProj, EuclideanSpace.proj, smul_eq_mul]
    ring
  exact hasFDerivAt_vec2 (hp 0) h1

@[simp]
theorem fderiv_wrinkledCuspMap (p : EuclideanSpace ℝ (Fin 4)) :
    fderiv ℝ wrinkledCuspMap p = wrinkledCuspFDerivCLM p :=
  (hasFDerivAt_wrinkledCuspMap p).fderiv

/-- `fderiv ℝ wrinkledCuspMap p` is surjective iff `p 0 ≠ p 1 ^ 2 ∨ p 2 ≠ 0 ∨ p 3 ≠ 0`. -/
theorem surjective_fderiv_wrinkledCuspMap_iff (p : EuclideanSpace ℝ (Fin 4)) :
    Function.Surjective (fderiv ℝ wrinkledCuspMap p) ↔
      p 0 ≠ p 1 ^ 2 ∨ p 2 ≠ 0 ∨ p 3 ≠ 0 := by
  rw [fderiv_wrinkledCuspMap]
  constructor
  · intro hsurj
    by_contra! hcrit
    rcases hcrit with ⟨ht, h2, h3⟩
    obtain ⟨v, hv⟩ := hsurj (vec2 0 1)
    have hv0 : v 0 = 0 := by
      simpa using congrArg (fun u : EuclideanPlane ↦ u 0) hv
    have hv1 := congrArg (fun u : EuclideanPlane ↦ u 1) hv
    simp only [wrinkledCuspFDerivCLM_apply, vec2_one, hv0, ht, h2, h3, mul_zero, sub_self, zero_mul,
      add_zero] at hv1
    exact zero_ne_one hv1
  · intro h w
    let c := w 1 + 3 * p 1 * w 0
    rcases h with ht | h2 | h3
    · have hden : 3 * p 1 ^ 2 - 3 * p 0 ≠ 0 := fun h0 ↦ ht (by linarith)
      refine ⟨vec4 (w 0) (c / (3 * p 1 ^ 2 - 3 * p 0)) 0 0, ext_vec2 rfl ?_⟩
      simp only [wrinkledCuspFDerivCLM_apply, vec2_one, vec4_zero, vec4_one, vec4_two, vec4_three,
        c]
      field_simp [hden]
      ring
    · refine ⟨vec4 (w 0) 0 (c / (2 * p 2)) 0, ext_vec2 rfl ?_⟩
      simp only [wrinkledCuspFDerivCLM_apply, vec2_one, vec4_zero, vec4_one, vec4_two, vec4_three,
        c]
      field_simp [h2]
      ring
    · refine ⟨vec4 (w 0) 0 0 (-c / (2 * p 3)), ext_vec2 rfl ?_⟩
      simp only [wrinkledCuspFDerivCLM_apply, vec2_one, vec4_zero, vec4_one, vec4_two, vec4_three,
        c]
      field_simp [h3]
      ring

/-- Exact critical locus of `wrinkledCuspMap`: the smooth parabola
`{p | p 0 = p 1 ^ 2 ∧ p 2 = 0 ∧ p 3 = 0}`. -/
theorem criticalPoints_wrinkledCuspMap :
    criticalPoints (𝓡 4) (𝓡 2) wrinkledCuspMap =
      {p : EuclideanSpace ℝ (Fin 4) | p 0 = p 1 ^ 2 ∧ p 2 = 0 ∧ p 3 = 0} := by
  rw [criticalPoints_euclidean_eq]
  ext p
  rw [mem_euclideanCriticalPoints_iff, surjective_fderiv_wrinkledCuspMap_iff, Set.mem_ofPred_eq]
  tauto

/-- Parametrization `s ↦ (s², s, 0, 0)` of the critical curve of `wrinkledCuspMap`, projecting to
the semi-cubical cusp `s ↦ (s², -2 s³)` in `ℝ²`. -/
theorem wrinkledCuspMap_criticalCurve (s : ℝ) :
    vec4 (s ^ 2) s 0 0 ∈ criticalPoints (𝓡 4) (𝓡 2) wrinkledCuspMap ∧
      wrinkledCuspMap (vec4 (s ^ 2) s 0 0) = vec2 (s ^ 2) (-2 * s ^ 3) := by
  rw [criticalPoints_wrinkledCuspMap]
  refine ⟨by simp, ext_vec2 rfl ?_⟩
  simp only [wrinkledCuspMap_apply_one, vec2_one, vec4_zero, vec4_one, vec4_two, vec4_three]
  ring

/-! ### Local Coordinate-Chart Singularity Predicates -/

/-- A map `f : M → Base` is locally modeled on `model : EuclideanSpace ℝ (Fin 4) → EuclideanPlane`
around `p ∈ M` centered at `p₀ ∈ ℝ⁴` when there exist smooth partial diffeomorphisms around `p` and
`f p` intertwining `f` with `model`. -/
def IsLocallyModeledOn
    {E_M H_M E_B H_B M Base : Type*}
    [NormedAddCommGroup E_M] [NormedSpace ℝ E_M] [TopologicalSpace H_M]
    (I_M : ModelWithCorners ℝ E_M H_M)
    [NormedAddCommGroup E_B] [NormedSpace ℝ E_B] [TopologicalSpace H_B]
    (I_B : ModelWithCorners ℝ E_B H_B)
    [TopologicalSpace M] [ChartedSpace H_M M]
    [TopologicalSpace Base] [ChartedSpace H_B Base]
    (f : M → Base) (p : M) (model : EuclideanSpace ℝ (Fin 4) → EuclideanPlane)
    (p₀ : EuclideanSpace ℝ (Fin 4)) : Prop :=
  ∃ (φ : PartialDiffeomorph I_M (𝓡 4) M (EuclideanSpace ℝ (Fin 4)) ∞)
    (ψ : PartialDiffeomorph I_B (𝓡 2) Base EuclideanPlane ∞),
    p ∈ φ.source ∧ f p ∈ ψ.source ∧ φ p = p₀ ∧ ψ (f p) = model p₀ ∧
    ∀ q ∈ φ.source, f q ∈ ψ.source ∧ ψ (f q) = model (φ q)

/-- `f` has an **indefinite quadratic fold** at `p` (`ADK05` Eq. 2). -/
def IsIndefiniteFoldAt
    {E_M H_M E_B H_B M Base : Type*}
    [NormedAddCommGroup E_M] [NormedSpace ℝ E_M] [TopologicalSpace H_M]
    (I_M : ModelWithCorners ℝ E_M H_M)
    [NormedAddCommGroup E_B] [NormedSpace ℝ E_B] [TopologicalSpace H_B]
    (I_B : ModelWithCorners ℝ E_B H_B)
    [TopologicalSpace M] [ChartedSpace H_M M]
    [TopologicalSpace Base] [ChartedSpace H_B Base]
    (f : M → Base) (p : M) : Prop :=
  IsLocallyModeledOn I_M I_B f p indefiniteFoldMap 0

/-- `f` has a **real Lefschetz singularity** at `p` (`ADK05`, `ST16`). -/
def IsRealLefschetzAt
    {E_M H_M E_B H_B M Base : Type*}
    [NormedAddCommGroup E_M] [NormedSpace ℝ E_M] [TopologicalSpace H_M]
    (I_M : ModelWithCorners ℝ E_M H_M)
    [NormedAddCommGroup E_B] [NormedSpace ℝ E_B] [TopologicalSpace H_B]
    (I_B : ModelWithCorners ℝ E_B H_B)
    [TopologicalSpace M] [ChartedSpace H_M M]
    [TopologicalSpace Base] [ChartedSpace H_B Base]
    (f : M → Base) (p : M) : Prop :=
  IsLocallyModeledOn I_M I_B f p realLefschetzMap 0

/-- `f` has a **wrinkled cusp singularity** at `p` (`Lekili 2009`, `ST16`). -/
def IsWrinkledCuspAt
    {E_M H_M E_B H_B M Base : Type*}
    [NormedAddCommGroup E_M] [NormedSpace ℝ E_M] [TopologicalSpace H_M]
    (I_M : ModelWithCorners ℝ E_M H_M)
    [NormedAddCommGroup E_B] [NormedSpace ℝ E_B] [TopologicalSpace H_B]
    (I_B : ModelWithCorners ℝ E_B H_B)
    [TopologicalSpace M] [ChartedSpace H_M M]
    [TopologicalSpace Base] [ChartedSpace H_B Base]
    (f : M → Base) (p : M) : Prop :=
  IsLocallyModeledOn I_M I_B f p wrinkledCuspMap 0

/-- Identity `PartialDiffeomorph` on a charted space with `source = Set.univ`. -/
def reflPartialDiffeomorph {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] :
    PartialDiffeomorph I I M M ∞ where
  toPartialEquiv := PartialEquiv.refl M
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := contMDiffOn_id
  contMDiffOn_invFun := contMDiffOn_id

/-- Every model map is locally modeled on itself via `reflPartialDiffeomorph`. -/
theorem isLocallyModeledOn_self (model : EuclideanSpace ℝ (Fin 4) → EuclideanPlane)
    (p₀ : EuclideanSpace ℝ (Fin 4)) :
    IsLocallyModeledOn (𝓡 4) (𝓡 2) model p₀ model p₀ :=
  ⟨reflPartialDiffeomorph (𝓡 4) (EuclideanSpace ℝ (Fin 4)),
    reflPartialDiffeomorph (𝓡 2) EuclideanPlane,
    Set.mem_univ _, Set.mem_univ _, rfl, rfl, fun _ _ ↦ ⟨Set.mem_univ _, rfl⟩⟩

theorem isIndefiniteFoldAt_indefiniteFoldMap_zero :
    IsIndefiniteFoldAt (𝓡 4) (𝓡 2) indefiniteFoldMap 0 :=
  isLocallyModeledOn_self indefiniteFoldMap 0

theorem isRealLefschetzAt_realLefschetzMap_zero :
    IsRealLefschetzAt (𝓡 4) (𝓡 2) realLefschetzMap 0 :=
  isLocallyModeledOn_self realLefschetzMap 0

theorem isWrinkledCuspAt_wrinkledCuspMap_zero :
    IsWrinkledCuspAt (𝓡 4) (𝓡 2) wrinkledCuspMap 0 :=
  isLocallyModeledOn_self wrinkledCuspMap 0

end LefschetzAndCusp

/-! ## 5. Global `WrinkledFibration` and `BrokenLefschetzFibration` Structures -/

section GlobalFibrations

universe u v w

/-- A **wrinkled / smooth singular surface fibration** `f : M → Base` from a smooth 4-manifold `M`
to a smooth 2-manifold `Base` with regular fiber `Fiber` (`Lekili 2009`, `ST16`,
`S4TCdiffeo-Aug-2026.tex`), packaging:
- a nonempty compact Hausdorff smooth 2-manifold regular fiber `Fiber`,
- a nonempty open regular region `baseRegion ⊆ Base` disjoint from `f '' Crit(f)`,
- an explicit Euclidean disk chart `baseDisk : Metric.ball 0 r_B ≃ₘ baseRegion` (`r_B > 0`), and
- an explicit smooth trivialization `f ⁻¹' baseRegion ≃ₘ baseRegion × Fiber` compatible with `f`. -/
structure WrinkledFibration
    {E_M H_M : Type*} [NormedAddCommGroup E_M] [NormedSpace ℝ E_M] [TopologicalSpace H_M]
    (I_M : ModelWithCorners ℝ E_M H_M) (M : Type u)
    [TopologicalSpace M] [ChartedSpace H_M M] [IsManifold I_M ∞ M]
    {E_B H_B : Type*} [NormedAddCommGroup E_B] [NormedSpace ℝ E_B] [TopologicalSpace H_B]
    (I_B : ModelWithCorners ℝ E_B H_B) (Base : Type v)
    [TopologicalSpace Base] [ChartedSpace H_B Base] [IsManifold I_B ∞ Base]
    (Fiber : Type w) [TopologicalSpace Fiber] [ChartedSpace EuclideanPlane Fiber]
    [IsManifold (𝓡 2) ∞ Fiber] [T2Space Fiber] [CompactSpace Fiber] [Nonempty Fiber] :
    Type (max u v w) where
  /-- Underlying smooth map `f : M → Base`. -/
  toFun : M → Base
  /-- Global `C^∞` smoothness of `f`. -/
  contMDiff_toFun : ContMDiff I_M I_B ∞ toFun
  /-- Nonempty open regular base region `B ⊆ Base` over which `f` trivializes. -/
  baseRegion : Opens Base
  /-- Non-emptiness of `B`. -/
  baseRegion_nonempty : baseRegion.1.Nonempty
  /-- Every point in `f ⁻¹' B` is regular (`mfderiv` is surjective). -/
  regular_on_preimage :
    ∀ p ∈ toFun ⁻¹' baseRegion.1, Function.Surjective (mfderiv I_M I_B toFun p)
  /-- Radius `r_B > 0` of the Euclidean open disk parameterizing `B`. -/
  baseDiskRadius : ℝ
  /-- Positivity `0 < r_B`. -/
  baseDiskRadius_pos : 0 < baseDiskRadius
  /-- Smooth diffeomorphism from the Euclidean ball `Metric.ball 0 r_B` onto `B`. -/
  baseDisk :
    (⟨Metric.ball (0 : EuclideanPlane) baseDiskRadius, Metric.isOpen_ball⟩ :
        Opens EuclideanPlane) ≃ₘ⟮𝓡 2, I_B⟯ baseRegion
  /-- Smooth trivialization `f ⁻¹' B ≃ₘ B × Fiber`. -/
  trivialization :
    (⟨toFun ⁻¹' baseRegion.1, baseRegion.2.preimage contMDiff_toFun.continuous⟩ : Opens M)
      ≃ₘ⟮I_M, I_B.prod (𝓡 2)⟯ (baseRegion × Fiber)
  /-- First projection of `trivialization` recovers `f`. -/
  trivialization_fst :
    ∀ p : (⟨toFun ⁻¹' baseRegion.1, baseRegion.2.preimage contMDiff_toFun.continuous⟩ : Opens M),
      (trivialization p).1 = ⟨toFun p.1, p.2⟩

instance instCoeFunWrinkledFibration
    {E_M H_M : Type*} [NormedAddCommGroup E_M] [NormedSpace ℝ E_M] [TopologicalSpace H_M]
    {I_M : ModelWithCorners ℝ E_M H_M} {M : Type u}
    [TopologicalSpace M] [ChartedSpace H_M M] [IsManifold I_M ∞ M]
    {E_B H_B : Type*} [NormedAddCommGroup E_B] [NormedSpace ℝ E_B] [TopologicalSpace H_B]
    {I_B : ModelWithCorners ℝ E_B H_B} {Base : Type v}
    [TopologicalSpace Base] [ChartedSpace H_B Base] [IsManifold I_B ∞ Base]
    {Fiber : Type w} [TopologicalSpace Fiber] [ChartedSpace EuclideanPlane Fiber]
    [IsManifold (𝓡 2) ∞ Fiber] [T2Space Fiber] [CompactSpace Fiber] [Nonempty Fiber] :
    CoeFun (WrinkledFibration I_M M I_B Base Fiber) (fun _ ↦ M → Base) :=
  ⟨WrinkledFibration.toFun⟩

namespace WrinkledFibration

variable {E_M H_M : Type*} [NormedAddCommGroup E_M] [NormedSpace ℝ E_M] [TopologicalSpace H_M]
  {I_M : ModelWithCorners ℝ E_M H_M} {M : Type u}
  [TopologicalSpace M] [ChartedSpace H_M M] [IsManifold I_M ∞ M]
  {E_B H_B : Type*} [NormedAddCommGroup E_B] [NormedSpace ℝ E_B] [TopologicalSpace H_B]
  {I_B : ModelWithCorners ℝ E_B H_B} {Base : Type v}
  [TopologicalSpace Base] [ChartedSpace H_B Base] [IsManifold I_B ∞ Base]
  {F : Type w} [TopologicalSpace F] [ChartedSpace EuclideanPlane F]
  [IsManifold (𝓡 2) ∞ F] [T2Space F] [CompactSpace F] [Nonempty F]
  (W : WrinkledFibration I_M M I_B Base F)

/-- Convenient dot-notation alias for the regular fiber type `F`. -/
abbrev Fiber (_ : WrinkledFibration I_M M I_B Base F) : Type w := F

/-- Open preimage `f ⁻¹' B` in `M` as an element of `Opens M`. -/
abbrev preimageOpen : Opens M :=
  ⟨W.toFun ⁻¹' W.baseRegion.1, W.baseRegion.2.preimage W.contMDiff_toFun.continuous⟩

/-- Euclidean open ball `Metric.ball 0 W.baseDiskRadius` as an element of `Opens EuclideanPlane`. -/
noncomputable abbrev baseDiskOpen : Opens EuclideanPlane :=
  ⟨Metric.ball (0 : EuclideanPlane) W.baseDiskRadius, Metric.isOpen_ball⟩

/-- `W.baseRegion` is disjoint from the critical-value set `W '' criticalPoints I_M I_B W`. -/
theorem disjoint_baseRegion_criticalPoints :
    Disjoint W.baseRegion.1 (W.toFun '' criticalPoints I_M I_B W.toFun) :=
  disjoint_image_criticalPoints_iff.mpr W.regular_on_preimage

/-- Smooth product open embedding `Ψ : baseRegion × F → M` inverse to `W.trivialization`. -/
noncomputable def embed (bz : W.baseRegion × F) : M :=
  (W.trivialization.symm bz).1

theorem contMDiff_embed : ContMDiff (I_B.prod (𝓡 2)) I_M ∞ W.embed :=
  contMDiff_subtype_val.comp W.trivialization.symm.contMDiff

theorem isLocalDiffeomorph_embed : IsLocalDiffeomorph (I_B.prod (𝓡 2)) I_M ∞ W.embed :=
  fun bz ↦ (W.trivialization.symm.isLocalDiffeomorph bz).comp
    (hg := TauCeti.isLocalDiffeomorph_subtype_val (W.trivialization.symm bz))

theorem isOpenEmbedding_embed : Topology.IsOpenEmbedding W.embed :=
  W.preimageOpen.2.isOpenEmbedding_subtypeVal.comp
    W.trivialization.symm.toHomeomorph.isOpenEmbedding

theorem range_embed : Set.range W.embed = W.toFun ⁻¹' W.baseRegion.1 := by
  ext x
  simp only [embed, Set.mem_range, Set.mem_preimage]
  constructor
  · rintro ⟨bz, rfl⟩
    exact (W.trivialization.symm bz).2
  · intro hx
    exact ⟨W.trivialization ⟨x, hx⟩, congrArg Subtype.val (W.trivialization.symm_apply_apply _)⟩

@[simp]
theorem apply_embed (b : W.baseRegion) (z : F) : W (W.embed (b, z)) = b.1 := by
  have h := W.trivialization_fst (W.trivialization.symm (b, z))
  rw [W.trivialization.apply_symm_apply] at h
  exact (congrArg Subtype.val h).symm

/-- Non-emptiness of `W.toFun ⁻¹' W.baseRegion.1`. -/
theorem preimage_baseRegion_nonempty : (W.toFun ⁻¹' W.baseRegion.1).Nonempty := by
  obtain ⟨b, hb⟩ := W.baseRegion_nonempty
  obtain ⟨z⟩ := (inferInstance : Nonempty F)
  exact ⟨W.embed (⟨b, hb⟩, z), by simpa [Set.mem_preimage] using hb⟩

/-- Smooth product open embedding `Ψ_disk : baseDiskOpen × F → M` over Euclidean disk
coordinates `Metric.ball 0 r_B`. -/
noncomputable def embedDisk (wz : W.baseDiskOpen × F) : M :=
  W.embed (W.baseDisk wz.1, wz.2)

theorem contMDiff_embedDisk : ContMDiff ((𝓡 2).prod (𝓡 2)) I_M ∞ W.embedDisk :=
  W.contMDiff_embed.comp ((W.baseDisk.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)

theorem isOpenEmbedding_embedDisk : Topology.IsOpenEmbedding W.embedDisk :=
  W.isOpenEmbedding_embed.comp
    (W.baseDisk.toHomeomorph.isOpenEmbedding.prodMap (Homeomorph.refl F).isOpenEmbedding)

theorem isLocalDiffeomorph_embedDisk : IsLocalDiffeomorph ((𝓡 2).prod (𝓡 2)) I_M ∞ W.embedDisk := by
  have hprod :
      IsLocalDiffeomorph ((𝓡 2).prod (𝓡 2)) (I_B.prod (𝓡 2)) ∞
        (fun wz : W.baseDiskOpen × F ↦ (W.baseDisk wz.1, wz.2)) :=
    (W.baseDisk.prodCongr (Diffeomorph.refl (𝓡 2) F ∞)).isLocalDiffeomorph
  exact fun wz ↦ (hprod wz).comp (hg := W.isLocalDiffeomorph_embed (W.baseDisk wz.1, wz.2))

@[simp]
theorem apply_embedDisk (w : W.baseDiskOpen) (z : F) :
    W (W.embedDisk (w, z)) = (W.baseDisk w).1 :=
  W.apply_embed (W.baseDisk w) z

/-- Center basepoint `W.baseDisk ⟨0, ...⟩ ∈ W.baseRegion`. -/
noncomputable def baseCenter : W.baseRegion :=
  W.baseDisk ⟨0, Metric.mem_ball_self W.baseDiskRadius_pos⟩

end WrinkledFibration

/-- A **broken Lefschetz fibration** (`ADK05`, `GSV15`, `BV21`) is a `WrinkledFibration` whose
critical points are all locally modeled on isolated real Lefschetz points (`IsRealLefschetzAt`) or
1-dimensional circles of indefinite quadratic folds (`IsIndefiniteFoldAt`). -/
structure BrokenLefschetzFibration
    {E_M H_M : Type*} [NormedAddCommGroup E_M] [NormedSpace ℝ E_M] [TopologicalSpace H_M]
    (I_M : ModelWithCorners ℝ E_M H_M) (M : Type u)
    [TopologicalSpace M] [ChartedSpace H_M M] [IsManifold I_M ∞ M]
    {E_B H_B : Type*} [NormedAddCommGroup E_B] [NormedSpace ℝ E_B] [TopologicalSpace H_B]
    (I_B : ModelWithCorners ℝ E_B H_B) (Base : Type v)
    [TopologicalSpace Base] [ChartedSpace H_B Base] [IsManifold I_B ∞ Base]
    (Fiber : Type w) [TopologicalSpace Fiber] [ChartedSpace EuclideanPlane Fiber]
    [IsManifold (𝓡 2) ∞ Fiber] [T2Space Fiber] [CompactSpace Fiber] [Nonempty Fiber] :
    Type (max u v w)
    extends WrinkledFibration I_M M I_B Base Fiber where
  /-- Every critical point is either a real Lefschetz point or an indefinite quadratic fold. -/
  singularities_broken_lefschetz :
    ∀ p ∈ criticalPoints I_M I_B toFun,
      IsRealLefschetzAt I_M I_B toFun p ∨ IsIndefiniteFoldAt I_M I_B toFun p

end GlobalFibrations

end S4TuringPoisson
