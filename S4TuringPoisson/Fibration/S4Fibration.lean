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

public import S4TuringPoisson.Fibration.LocalSingularModels
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic

/-!
# Explicit Co-Oriented Smooth Singular Fibration on $S^4$ (M2.2)

This file constructs Milestone M2.2 of `S4TuringPoisson`: an explicit, `sorry`-free smooth singular
surface fibration `s4Fibration : Sphere4 → Sphere2` whose smooth trivialization over an open regular
disk `s4BaseRegion ⊂ Sphere2` is **strictly positively co-oriented** with `S4PositiveVolumeForm` and
`S2PositiveVolumeForm` (`S4TCdiffeo-Aug-2026.tex`, Theorem 1 & Equation 1):

1. **Orientation-Preserving South-Pole Stereographic Parameterization (`southPoleStereoInv`)**:
   - Maps `w = (w₀, w₁) ∈ ℝ²` to `(4 w₀, 4 w₁, 4 - ‖w‖²) / (‖w‖² + 4) ∈ S² \ {s2SouthPole}` with
     rational inverse `(z₀, z₁, z₂) ↦ (2 z₀ / (1 + z₂), 2 z₁ / (1 + z₂))`.
   - Avoids `Classical.choose` in `OrthonormalBasis.fromOrthogonalSpanSingleton` and pulls
     `S2VolumeForm` back to `+(16 / (w₀² + w₁² + 4)²) • planeAreaForm` (`> 0` everywhere).
2. **Smooth Singular Fibration `s4Fibration : Sphere4 → Sphere2`**:
   - Defined globally by `s4Fibration (x₀, x₁, x₂, x₃, x₄) = southPoleStereoInv (x₀, x₁)`.
   - Exact critical circle characterization `Crit(s4Fibration) = {x ∈ S⁴ | (x₂, x₃, x₄) = 0}`
     (`criticalPoints_s4Fibration_nonempty`), regular everywhere on `{x ∈ S⁴ | ‖(x₀, x₁)‖ < 1}`.
3. **Regular Disk `s4BaseRegion` & Smooth Trivialization `s4Trivialization`**:
   - Over `s4BaseRegion = southPoleStereoInv '' Metric.ball 0 (1 / 2)`, `s4Fibration ⁻¹' B` equals
     `{x ∈ S⁴ | ‖(x₀, x₁)‖ < 1 / 2}` and trivializes smoothly onto `s4BaseRegion × Sphere2` via
     fiber normalization `(x₂, x₃, x₄) / √(1 - x₀² - x₁²) ∈ Sphere2`, packaged as
     `s4RegularDiskFibration : RegularDiskFibration (𝓡 4) Sphere4 (𝓡 2) Sphere2 Sphere2`.
4. **Strict Positive Co-Orientation (`s4Trivialization_pos_cooriented`)**:
   - Proves `s4PlaneEmbed^* S4VolumeForm = √(1 - ‖w‖²) • (p_F^* S2VolumeForm ∧ p_B^* planeAreaForm)`
     and deduces that `s4Trivialization^* (p_F^* S2VolumeForm ∧ p_B^* S2VolumeForm|_B)` equals a
     strictly positive scalar multiple of `S4VolumeForm` at every point of `s4Fibration ⁻¹' B`.
-/

@[expose] public section

open Filter Function Metric Module Set TopologicalSpace
open scoped ContDiff InnerProductSpace Manifold Topology

namespace S4TuringPoisson

/-! ## 1. Ambient Coordinate Helpers on $\mathbb{R}^3$ and $\mathbb{R}^5$ -/

section AmbientCoordinates

@[simp]
theorem euclidProj_apply {n : ℕ} (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    euclidProj i x = x i := rfl

/-- Explicit 3-vector `(x₀, x₁, x₂)` in `EuclideanSpace ℝ (Fin 3)`. -/
noncomputable def vec3 (x₀ x₁ x₂ : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![x₀, x₁, x₂]

/-- Explicit 5-vector `(x₀, x₁, x₂, x₃, x₄)` in `EuclideanSpace ℝ (Fin 5)`. -/
noncomputable def vec5 (x₀ x₁ x₂ x₃ x₄ : ℝ) : EuclideanSpace ℝ (Fin 5) :=
  (EuclideanSpace.equiv (Fin 5) ℝ).symm ![x₀, x₁, x₂, x₃, x₄]

@[simp] theorem vec3_zero (x₀ x₁ x₂ : ℝ) : vec3 x₀ x₁ x₂ 0 = x₀ := rfl
@[simp] theorem vec3_one (x₀ x₁ x₂ : ℝ) : vec3 x₀ x₁ x₂ 1 = x₁ := rfl
@[simp] theorem vec3_two (x₀ x₁ x₂ : ℝ) : vec3 x₀ x₁ x₂ 2 = x₂ := rfl

@[simp] theorem vec5_zero (x₀ x₁ x₂ x₃ x₄ : ℝ) : vec5 x₀ x₁ x₂ x₃ x₄ 0 = x₀ := rfl
@[simp] theorem vec5_one (x₀ x₁ x₂ x₃ x₄ : ℝ) : vec5 x₀ x₁ x₂ x₃ x₄ 1 = x₁ := rfl
@[simp] theorem vec5_two (x₀ x₁ x₂ x₃ x₄ : ℝ) : vec5 x₀ x₁ x₂ x₃ x₄ 2 = x₂ := rfl
@[simp] theorem vec5_three (x₀ x₁ x₂ x₃ x₄ : ℝ) : vec5 x₀ x₁ x₂ x₃ x₄ 3 = x₃ := rfl
@[simp] theorem vec5_four (x₀ x₁ x₂ x₃ x₄ : ℝ) : vec5 x₀ x₁ x₂ x₃ x₄ 4 = x₄ := rfl

theorem ext_vec3 {u v : EuclideanSpace ℝ (Fin 3)}
    (h0 : u 0 = v 0) (h1 : u 1 = v 1) (h2 : u 2 = v 2) : u = v := by
  refine PiLp.ext fun i ↦ ?_
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem ext_vec5 {u v : EuclideanSpace ℝ (Fin 5)}
    (h0 : u 0 = v 0) (h1 : u 1 = v 1) (h2 : u 2 = v 2) (h3 : u 3 = v 3) (h4 : u 4 = v 4) :
    u = v := by
  refine PiLp.ext fun i ↦ ?_
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem contDiff_vec3 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞}
    {g₀ g₁ g₂ : E → ℝ} (hg₀ : ContDiff ℝ n g₀) (hg₁ : ContDiff ℝ n g₁) (hg₂ : ContDiff ℝ n g₂) :
    ContDiff ℝ n (fun x ↦ vec3 (g₀ x) (g₁ x) (g₂ x)) := by
  refine (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp (contDiff_pi.mpr fun i ↦ ?_)
  fin_cases i
  · exact hg₀
  · exact hg₁
  · exact hg₂

theorem contDiff_vec5 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞}
    {g₀ g₁ g₂ g₃ g₄ : E → ℝ} (hg₀ : ContDiff ℝ n g₀) (hg₁ : ContDiff ℝ n g₁)
    (hg₂ : ContDiff ℝ n g₂) (hg₃ : ContDiff ℝ n g₃) (hg₄ : ContDiff ℝ n g₄) :
    ContDiff ℝ n (fun x ↦ vec5 (g₀ x) (g₁ x) (g₂ x) (g₃ x) (g₄ x)) := by
  refine (EuclideanSpace.equiv (Fin 5) ℝ).symm.contDiff.comp (contDiff_pi.mpr fun i ↦ ?_)
  fin_cases i
  · exact hg₀
  · exact hg₁
  · exact hg₂
  · exact hg₃
  · exact hg₄

/-- Continuous linear map `E →L[ℝ] EuclideanSpace ℝ (Fin 3)` from three scalar functionals. -/
noncomputable def clmVec3 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L₀ L₁ L₂ : E →L[ℝ] ℝ) : E →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦ match i with | 0 => L₀ | 1 => L₁ | 2 => L₂)

@[simp]
theorem clmVec3_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L₀ L₁ L₂ : E →L[ℝ] ℝ) (v : E) :
    clmVec3 L₀ L₁ L₂ v = vec3 (L₀ v) (L₁ v) (L₂ v) := by
  refine PiLp.ext fun i ↦ ?_
  fin_cases i <;> rfl

theorem hasFDerivAt_vec3 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g₀ g₁ g₂ : E → ℝ} {L₀ L₁ L₂ : E →L[ℝ] ℝ} {x : E}
    (h₀ : HasFDerivAt g₀ L₀ x) (h₁ : HasFDerivAt g₁ L₁ x) (h₂ : HasFDerivAt g₂ L₂ x) :
    HasFDerivAt (fun y ↦ vec3 (g₀ y) (g₁ y) (g₂ y)) (clmVec3 L₀ L₁ L₂) x := by
  have hpi : HasFDerivAt (fun y : E ↦ (![g₀ y, g₁ y, g₂ y] : Fin 3 → ℝ))
      (ContinuousLinearMap.pi fun i : Fin 3 ↦ match i with | 0 => L₀ | 1 => L₁ | 2 => L₂) x := by
    refine hasFDerivAt_pi.mpr fun i ↦ ?_
    fin_cases i
    · simpa using h₀
    · simpa using h₁
    · simpa using h₂
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.hasFDerivAt.comp x hpi

/-- Continuous linear map `E →L[ℝ] EuclideanSpace ℝ (Fin 5)` from five scalar functionals. -/
noncomputable def clmVec5 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L₀ L₁ L₂ L₃ L₄ : E →L[ℝ] ℝ) : E →L[ℝ] EuclideanSpace ℝ (Fin 5) :=
  (EuclideanSpace.equiv (Fin 5) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦ match i with
      | 0 => L₀ | 1 => L₁ | 2 => L₂ | 3 => L₃ | 4 => L₄)

@[simp]
theorem clmVec5_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L₀ L₁ L₂ L₃ L₄ : E →L[ℝ] ℝ) (v : E) :
    clmVec5 L₀ L₁ L₂ L₃ L₄ v = vec5 (L₀ v) (L₁ v) (L₂ v) (L₃ v) (L₄ v) := by
  refine PiLp.ext fun i ↦ ?_
  fin_cases i <;> rfl

theorem hasFDerivAt_vec5 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g₀ g₁ g₂ g₃ g₄ : E → ℝ} {L₀ L₁ L₂ L₃ L₄ : E →L[ℝ] ℝ} {x : E}
    (h₀ : HasFDerivAt g₀ L₀ x) (h₁ : HasFDerivAt g₁ L₁ x) (h₂ : HasFDerivAt g₂ L₂ x)
    (h₃ : HasFDerivAt g₃ L₃ x) (h₄ : HasFDerivAt g₄ L₄ x) :
    HasFDerivAt (fun y ↦ vec5 (g₀ y) (g₁ y) (g₂ y) (g₃ y) (g₄ y))
      (clmVec5 L₀ L₁ L₂ L₃ L₄) x := by
  have hpi : HasFDerivAt (fun y : E ↦ (![g₀ y, g₁ y, g₂ y, g₃ y, g₄ y] : Fin 5 → ℝ))
      (ContinuousLinearMap.pi fun i : Fin 5 ↦ match i with
        | 0 => L₀ | 1 => L₁ | 2 => L₂ | 3 => L₃ | 4 => L₄) x := by
    refine hasFDerivAt_pi.mpr fun i ↦ ?_
    fin_cases i
    · simpa using h₀
    · simpa using h₁
    · simpa using h₂
    · simpa using h₃
    · simpa using h₄
  exact (EuclideanSpace.equiv (Fin 5) ℝ).symm.hasFDerivAt.comp x hpi

/-- Norm-squared expansion on `EuclideanPlane`. -/
theorem norm_sq_plane (w : EuclideanPlane) : ‖w‖ ^ 2 = w 0 ^ 2 + w 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs]

/-- Norm-squared expansion on `EuclideanSpace ℝ (Fin 3)`. -/
theorem norm_sq_vec3 (z : EuclideanSpace ℝ (Fin 3)) :
    ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]

/-- Norm-squared expansion on `EuclideanSpace ℝ (Fin 5)`. -/
theorem norm_sq_vec5 (x : EuclideanSpace ℝ (Fin 5)) :
    ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_five]
  simp [Real.norm_eq_abs, sq_abs]

/-- Continuous linear projection `ℝ⁵ →L[ℝ] ℝ²` onto the first two coordinates `(x₀, x₁)`. -/
noncomputable def s4ProjPlane : EuclideanSpace ℝ (Fin 5) →L[ℝ] EuclideanPlane :=
  clmVec2 (euclidProj (0 : Fin 5)) (euclidProj (1 : Fin 5))

/-- Continuous linear projection `ℝ⁵ →L[ℝ] ℝ³` onto the last three coordinates `(x₂, x₃, x₄)`. -/
noncomputable def s4ProjFiber : EuclideanSpace ℝ (Fin 5) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  clmVec3 (euclidProj (2 : Fin 5)) (euclidProj (3 : Fin 5)) (euclidProj (4 : Fin 5))

@[simp]
theorem s4ProjPlane_apply (x : EuclideanSpace ℝ (Fin 5)) :
    s4ProjPlane x = vec2 (x 0) (x 1) := by
  simp [s4ProjPlane, euclidProj]

@[simp]
theorem s4ProjFiber_apply (x : EuclideanSpace ℝ (Fin 5)) :
    s4ProjFiber x = vec3 (x 2) (x 3) (x 4) := by
  simp [s4ProjFiber, euclidProj]

/-- For every `x : Sphere4`, `‖s4ProjPlane x.1‖² + ‖s4ProjFiber x.1‖² = 1`. -/
theorem norm_sq_s4_split (x : Sphere4) :
    ‖s4ProjPlane x.1‖ ^ 2 + ‖s4ProjFiber x.1‖ ^ 2 = 1 := by
  have hx : ‖x.1‖ ^ 2 = 1 := by
    rw [mem_sphere_zero_iff_norm.mp x.2]
    norm_num
  rw [norm_sq_plane, norm_sq_vec3]
  simp only [s4ProjPlane_apply, s4ProjFiber_apply, vec2_zero, vec2_one, vec3_zero, vec3_one,
    vec3_two]
  rw [norm_sq_vec5] at hx
  linarith

/-- Matrix determinant formula for the standard oriented volume form on `EuclideanSpace ℝ (Fin n)`.
-/
theorem volumeForm_basisFun_eq_det {n : ℕ}
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n)]
    (v : Fin n → EuclideanSpace ℝ (Fin n)) :
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.orientation.volumeForm v =
      (Matrix.of fun i j : Fin n ↦ (v j) i).det := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  rw [b.toBasis.orientation.volumeForm_robust b rfl, Module.Basis.det_apply]
  congr 1

theorem basisFun2_zero_eq_vec2 :
    ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 0 : EuclideanPlane) = vec2 1 0 := by
  rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  refine ext_vec2 ?_ ?_ <;> simp

theorem basisFun2_one_eq_vec2 :
    ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 1 : EuclideanPlane) = vec2 0 1 := by
  rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  refine ext_vec2 ?_ ?_ <;> simp

end AmbientCoordinates

/-! ## 2. Orientation-Preserving South-Pole Stereographic Parameterization of $S^2$ -/

section SouthPoleStereographic

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

/-- North pole `(0, 0, 1) ∈ S²`. -/
noncomputable def s2NorthPole : Sphere2 :=
  ⟨vec3 0 0 1, by
    rw [mem_sphere_zero_iff_norm]
    have hsq : ‖vec3 0 0 1‖ ^ 2 = 1 := by rw [norm_sq_vec3]; norm_num
    nlinarith [norm_nonneg (vec3 0 0 1)]⟩

instance instNonemptySphere2 : Nonempty Sphere2 :=
  ⟨s2NorthPole⟩

/-- South pole `(0, 0, -1) ∈ S²`. -/
noncomputable def s2SouthPole : Sphere2 :=
  ⟨vec3 0 0 (-1), by
    rw [mem_sphere_zero_iff_norm]
    have hsq : ‖vec3 0 0 (-1)‖ ^ 2 = 1 := by rw [norm_sq_vec3]; norm_num
    nlinarith [norm_nonneg (vec3 0 0 (-1))]⟩

/-- Open punctured 2-sphere `S² \ {s2SouthPole}` as an element of `Opens Sphere2`. -/
noncomputable abbrev s2PuncturedSouth : Opens Sphere2 :=
  ⟨{s2SouthPole}ᶜ, isOpen_compl_singleton⟩

/-- Ambient formula `(4 w₀, 4 w₁, 4 - (w₀² + w₁²)) / (w₀² + w₁² + 4)` for the orientation-preserving
south-pole inverse stereographic parameterization `ℝ² → ℝ³`. -/
noncomputable def southPoleStereoRaw (w : EuclideanPlane) : EuclideanSpace ℝ (Fin 3) :=
  vec3 (4 * w 0 / (w 0 ^ 2 + w 1 ^ 2 + 4))
    (4 * w 1 / (w 0 ^ 2 + w 1 ^ 2 + 4))
    ((4 - (w 0 ^ 2 + w 1 ^ 2)) / (w 0 ^ 2 + w 1 ^ 2 + 4))

theorem southPoleStereoRaw_mem_sphere (w : EuclideanPlane) :
    southPoleStereoRaw w ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have hden : w 0 ^ 2 + w 1 ^ 2 + 4 ≠ 0 := by positivity
  have hsq : ‖southPoleStereoRaw w‖ ^ 2 = 1 := by
    rw [norm_sq_vec3]
    simp only [southPoleStereoRaw, vec3_zero, vec3_one, vec3_two]
    field_simp [hden]
    ring
  nlinarith [norm_nonneg (southPoleStereoRaw w)]

/-- Smoothness (`ContDiff ℝ ∞`) of `southPoleStereoRaw : ℝ² → ℝ³`. -/
theorem contDiff_southPoleStereoRaw : ContDiff ℝ ∞ southPoleStereoRaw := by
  have hw (i : Fin 2) : ContDiff ℝ ∞ (fun w : EuclideanPlane ↦ w i) :=
    (euclidProj i).contDiff
  have hden : ContDiff ℝ ∞ (fun w : EuclideanPlane ↦ w 0 ^ 2 + w 1 ^ 2 + 4) :=
    (((hw 0).pow 2).add ((hw 1).pow 2)).add contDiff_const
  have hne : ∀ w : EuclideanPlane, w 0 ^ 2 + w 1 ^ 2 + 4 ≠ 0 := fun w ↦ by positivity
  exact contDiff_vec3
    ((contDiff_const.mul (hw 0)).div hden hne)
    ((contDiff_const.mul (hw 1)).div hden hne)
    ((contDiff_const.sub (((hw 0).pow 2).add ((hw 1).pow 2))).div hden hne)

/-- Orientation-preserving south-pole inverse stereographic map `σ_S : ℝ² → S²`. -/
noncomputable def southPoleStereoInv (w : EuclideanPlane) : Sphere2 :=
  Set.codRestrict southPoleStereoRaw (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    southPoleStereoRaw_mem_sphere w

@[simp]
theorem coe_southPoleStereoInv (w : EuclideanPlane) :
    (southPoleStereoInv w : EuclideanSpace ℝ (Fin 3)) = southPoleStereoRaw w :=
  rfl

/-- `southPoleStereoInv : ℝ² → S²` is globally $C^\infty$ smooth. -/
theorem contMDiff_southPoleStereoInv : ContMDiff (𝓡 2) (𝓡 2) ∞ southPoleStereoInv :=
  contDiff_southPoleStereoRaw.contMDiff.codRestrict_sphere southPoleStereoRaw_mem_sphere

@[simp]
theorem southPoleStereoInv_zero : southPoleStereoInv 0 = s2NorthPole := by
  apply Subtype.ext
  refine ext_vec3 ?_ ?_ ?_ <;> simp [southPoleStereoRaw, s2NorthPole]

theorem southPoleStereoInv_ne_southPole (w : EuclideanPlane) :
    southPoleStereoInv w ≠ s2SouthPole := by
  intro h
  have h2 := congrArg (fun z : Sphere2 ↦ z.1 2) h
  simp only [coe_southPoleStereoInv, southPoleStereoRaw, vec3_two, s2SouthPole] at h2
  have hden : 0 < w 0 ^ 2 + w 1 ^ 2 + 4 := by positivity
  rw [div_eq_iff hden.ne'] at h2
  linarith

/-- A point `z : Sphere2` differs from `s2SouthPole` if and only if `1 + z.1 2 ≠ 0` (and in fact
`0 < 1 + z.1 2`). -/
theorem one_add_coord2_pos_of_ne_southPole {z : Sphere2} (hz : z ≠ s2SouthPole) :
    0 < 1 + z.1 2 := by
  have hnorm : z.1 0 ^ 2 + z.1 1 ^ 2 + z.1 2 ^ 2 = 1 := by
    rw [← norm_sq_vec3, mem_sphere_zero_iff_norm.mp z.2]
    norm_num
  have hge : 0 ≤ 1 + z.1 2 := by
    nlinarith [sq_nonneg (z.1 0), sq_nonneg (z.1 1), sq_nonneg (z.1 2 + 1)]
  refine lt_of_le_of_ne hge fun hzero ↦ hz ?_
  have hz2 : z.1 2 = -1 := by linarith
  have hz0 : z.1 0 = 0 := by nlinarith [sq_nonneg (z.1 0), sq_nonneg (z.1 1)]
  have hz1 : z.1 1 = 0 := by nlinarith [sq_nonneg (z.1 0), sq_nonneg (z.1 1)]
  exact Subtype.ext (ext_vec3 hz0 hz1 hz2)

/-- Forward south-pole stereographic coordinate map `z ↦ (2 z₀ / (1 + z₂), 2 z₁ / (1 + z₂))` on
`Sphere2`. -/
noncomputable def southPoleStereoChart (z : Sphere2) : EuclideanPlane :=
  vec2 (2 * z.1 0 / (1 + z.1 2)) (2 * z.1 1 / (1 + z.1 2))

@[simp]
theorem southPoleStereoChart_inv (w : EuclideanPlane) :
    southPoleStereoChart (southPoleStereoInv w) = w := by
  have hden : w 0 ^ 2 + w 1 ^ 2 + 4 ≠ 0 := by positivity
  refine ext_vec2 ?_ ?_
  · simp only [southPoleStereoChart, coe_southPoleStereoInv, southPoleStereoRaw, vec2_zero,
      vec3_zero, vec3_two]
    field_simp [hden]
    ring
  · simp only [southPoleStereoChart, coe_southPoleStereoInv, southPoleStereoRaw, vec2_one,
      vec3_one, vec3_two]
    field_simp [hden]
    ring

theorem injective_southPoleStereoInv : Function.Injective southPoleStereoInv :=
  Function.LeftInverse.injective southPoleStereoChart_inv

theorem southPoleStereoInv_chart {z : Sphere2} (hz : z ≠ s2SouthPole) :
    southPoleStereoInv (southPoleStereoChart z) = z := by
  have h1z : 1 + z.1 2 ≠ 0 := (one_add_coord2_pos_of_ne_southPole hz).ne'
  have hnorm : z.1 0 ^ 2 + z.1 1 ^ 2 + z.1 2 ^ 2 = 1 := by
    rw [← norm_sq_vec3, mem_sphere_zero_iff_norm.mp z.2]
    norm_num
  let u := southPoleStereoChart z
  have hu_den : u 0 ^ 2 + u 1 ^ 2 + 4 = 8 / (1 + z.1 2) := by
    simp only [u, southPoleStereoChart, vec2_zero, vec2_one]
    field_simp [h1z]
    linear_combination 4 * hnorm
  have hden_ne : u 0 ^ 2 + u 1 ^ 2 + 4 ≠ 0 := by positivity
  apply Subtype.ext
  refine ext_vec3 ?_ ?_ ?_
  · change 4 * u 0 / (u 0 ^ 2 + u 1 ^ 2 + 4) = z.1 0
    rw [hu_den]
    simp only [u, southPoleStereoChart, vec2_zero]
    field_simp [h1z]
    ring
  · change 4 * u 1 / (u 0 ^ 2 + u 1 ^ 2 + 4) = z.1 1
    rw [hu_den]
    simp only [u, southPoleStereoChart, vec2_one]
    field_simp [h1z]
    ring
  · change (4 - (u 0 ^ 2 + u 1 ^ 2)) / (u 0 ^ 2 + u 1 ^ 2 + 4) = z.1 2
    rw [hu_den]
    have h4 : 4 - (u 0 ^ 2 + u 1 ^ 2) = 8 * z.1 2 / (1 + z.1 2) := by
      have hsub : u 0 ^ 2 + u 1 ^ 2 = 8 / (1 + z.1 2) - 4 := by linarith [hu_den]
      rw [hsub]
      field_simp [h1z]
      ring
    rw [h4]
    field_simp [h1z]

/-- Smooth diffeomorphism `EuclideanPlane ≃ₘ⟮𝓡 2, 𝓡 2⟯ (S² \ {s2SouthPole})` given by
`southPoleStereoInv` and `southPoleStereoChart`. -/
noncomputable def southPoleStereoDiffeomorph :
    EuclideanPlane ≃ₘ⟮𝓡 2, 𝓡 2⟯ s2PuncturedSouth where
  toFun w := ⟨southPoleStereoInv w, southPoleStereoInv_ne_southPole w⟩
  invFun z := southPoleStereoChart z.1
  left_inv w := southPoleStereoChart_inv w
  right_inv z := Subtype.ext (southPoleStereoInv_chart z.2)
  contMDiff_toFun :=
    (TauCeti.ContMDiff.subtypeVal_comp_iff s2PuncturedSouth _).mp contMDiff_southPoleStereoInv
  contMDiff_invFun := by
    have hcoe : ContMDiff (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
        (fun z : s2PuncturedSouth ↦ (z.1 : EuclideanSpace ℝ (Fin 3))) :=
      contMDiff_coe_sphere.comp contMDiff_subtype_val
    have hc (i : Fin 3) : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun z : s2PuncturedSouth ↦ z.1.1 i) :=
      (euclidProj i).contDiff.contMDiff.comp hcoe
    have hinv_diff : ∀ z : s2PuncturedSouth,
        ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun y : s2PuncturedSouth ↦ (1 + y.1.1 2)⁻¹) z := by
      intro z
      have h1z : 1 + z.1.1 2 ≠ 0 := (one_add_coord2_pos_of_ne_southPole z.2).ne'
      have hadd : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun y : s2PuncturedSouth ↦ 1 + y.1.1 2) z :=
        (contDiff_const.add contDiff_id).contMDiff.contMDiffAt.comp z (hc 2).contMDiffAt
      exact (contDiffAt_inv ℝ h1z).contMDiffAt.comp z hadd
    have hinv : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun z : s2PuncturedSouth ↦ (1 + z.1.1 2)⁻¹) :=
      fun z ↦ hinv_diff z
    have hmul2 : ContDiff ℝ ∞ (fun q : ℝ × ℝ ↦ (2 * q.1) * q.2) :=
      (contDiff_const.mul contDiff_fst).mul contDiff_snd
    have heq0 : (fun z : s2PuncturedSouth ↦ 2 * z.1.1 0 / (1 + z.1.1 2)) =
        (fun q : ℝ × ℝ ↦ (2 * q.1) * q.2) ∘
          fun z : s2PuncturedSouth ↦ (z.1.1 0, (1 + z.1.1 2)⁻¹) := by
      funext z; simp [div_eq_mul_inv]
    have heq1 : (fun z : s2PuncturedSouth ↦ 2 * z.1.1 1 / (1 + z.1.1 2)) =
        (fun q : ℝ × ℝ ↦ (2 * q.1) * q.2) ∘
          fun z : s2PuncturedSouth ↦ (z.1.1 1, (1 + z.1.1 2)⁻¹) := by
      funext z; simp [div_eq_mul_inv]
    have hpi : ContMDiff (𝓡 2) 𝓘(ℝ, Fin 2 → ℝ) ∞
        (fun z : s2PuncturedSouth ↦
          ![2 * z.1.1 0 / (1 + z.1.1 2), 2 * z.1.1 1 / (1 + z.1.1 2)]) := by
      refine contMDiff_pi_module_iff.mpr fun i ↦ ?_
      fin_cases i
      · change ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
            (fun z : s2PuncturedSouth ↦ 2 * z.1.1 0 / (1 + z.1.1 2))
        rw [heq0]
        exact hmul2.contMDiff.comp ((hc 0).prodMk_space hinv)
      · change ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
            (fun z : s2PuncturedSouth ↦ 2 * z.1.1 1 / (1 + z.1.1 2))
        rw [heq1]
        exact hmul2.contMDiff.comp ((hc 1).prodMk_space hinv)
    exact (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.contMDiff.comp hpi

theorem isLocalDiffeomorph_southPoleStereoInv :
    IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ southPoleStereoInv :=
  fun w ↦ (southPoleStereoDiffeomorph.isLocalDiffeomorph w).comp
    (hg := TauCeti.isLocalDiffeomorph_subtype_val (southPoleStereoDiffeomorph w))

theorem isOpenEmbedding_southPoleStereoInv :
    Topology.IsOpenEmbedding southPoleStereoInv :=
  s2PuncturedSouth.2.isOpenEmbedding_subtypeVal.comp
    southPoleStereoDiffeomorph.toHomeomorph.isOpenEmbedding

/-- Exact Fréchet derivative of `southPoleStereoRaw` at `w : EuclideanPlane`. -/
theorem fderiv_southPoleStereoRaw_apply (w v : EuclideanPlane) :
    fderiv ℝ southPoleStereoRaw w v =
      vec3
        ((4 * v 0 * (w 0 ^ 2 + w 1 ^ 2 + 4) - 4 * w 0 * (2 * w 0 * v 0 + 2 * w 1 * v 1)) /
          (w 0 ^ 2 + w 1 ^ 2 + 4) ^ 2)
        ((4 * v 1 * (w 0 ^ 2 + w 1 ^ 2 + 4) - 4 * w 1 * (2 * w 0 * v 0 + 2 * w 1 * v 1)) /
          (w 0 ^ 2 + w 1 ^ 2 + 4) ^ 2)
        ((-(2 * w 0 * v 0 + 2 * w 1 * v 1) * (w 0 ^ 2 + w 1 ^ 2 + 4) -
            (4 - (w 0 ^ 2 + w 1 ^ 2)) * (2 * w 0 * v 0 + 2 * w 1 * v 1)) /
          (w 0 ^ 2 + w 1 ^ 2 + 4) ^ 2) := by
  let s : ℝ := w 0 ^ 2 + w 1 ^ 2 + 4
  have hs_ne : s ≠ 0 := by positivity
  have hden_ne : w 0 ^ 2 + w 1 ^ 2 + 4 ≠ 0 := hs_ne
  have hw (i : Fin 2) : HasFDerivAt (fun u : EuclideanPlane ↦ u i) (euclidProj i) w :=
    (euclidProj i).hasFDerivAt
  have hsq (i : Fin 2) : HasFDerivAt (fun u : EuclideanPlane ↦ u i ^ 2)
      ((2 * w i) • euclidProj i) w := by
    convert (hw i).pow 2 using 1
    ext u
    simp only [smul_apply, euclidProj, EuclideanSpace.proj, nsmul_eq_mul, Nat.cast_ofNat,
      smul_eq_mul]
    ring
  let ds : EuclideanPlane →L[ℝ] ℝ := (2 * w 0) • euclidProj 0 + (2 * w 1) • euclidProj 1
  have hden : HasFDerivAt (fun u : EuclideanPlane ↦ u 0 ^ 2 + u 1 ^ 2 + 4) ds w := by
    simpa [ds] using ((hsq 0).add (hsq 1)).add_const (4 : ℝ)
  have hinv : HasFDerivAt (fun u : EuclideanPlane ↦ (u 0 ^ 2 + u 1 ^ 2 + 4)⁻¹)
      (-(s ^ 2)⁻¹ • ds) w := by
    convert (hasDerivAt_inv hs_ne).comp_hasFDerivAt w hden using 1
    ext u
    simp
  have hquot (g : EuclideanPlane → ℝ) (dg : EuclideanPlane →L[ℝ] ℝ)
      (hg : HasFDerivAt g dg w) :
      HasFDerivAt (fun u ↦ g u / (u 0 ^ 2 + u 1 ^ 2 + 4))
        (s⁻¹ • dg + g w • (-(s ^ 2)⁻¹ • ds)) w := by
    have heq : (fun u ↦ g u / (u 0 ^ 2 + u 1 ^ 2 + 4)) =
        fun u ↦ g u * (u 0 ^ 2 + u 1 ^ 2 + 4)⁻¹ := by
      funext u
      exact div_eq_mul_inv _ _
    rw [heq]
    convert hg.mul hinv using 1
    ext u
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hn0 : HasFDerivAt (fun u : EuclideanPlane ↦ 4 * u 0) ((4 : ℝ) • euclidProj 0) w := by
    have heq : (fun u : EuclideanPlane ↦ 4 * u 0) = fun u ↦ (4 : ℝ) • u 0 := by
      funext u; simp [smul_eq_mul]
    rw [heq]
    exact (hw 0).const_smul (4 : ℝ)
  have hn1 : HasFDerivAt (fun u : EuclideanPlane ↦ 4 * u 1) ((4 : ℝ) • euclidProj 1) w := by
    have heq : (fun u : EuclideanPlane ↦ 4 * u 1) = fun u ↦ (4 : ℝ) • u 1 := by
      funext u; simp [smul_eq_mul]
    rw [heq]
    exact (hw 1).const_smul (4 : ℝ)
  have hn2 : HasFDerivAt (fun u : EuclideanPlane ↦ 4 - (u 0 ^ 2 + u 1 ^ 2)) (-ds) w := by
    convert (hasFDerivAt_const (4 : ℝ) w).sub ((hsq 0).add (hsq 1)) using 1
    ext u
    simp [ds]
  have hraw : HasFDerivAt southPoleStereoRaw _ w :=
    hasFDerivAt_vec3 (hquot _ _ hn0) (hquot _ _ hn1) (hquot _ _ hn2)
  rw [hraw.fderiv, clmVec3_apply]
  refine ext_vec3 ?_ ?_ ?_ <;>
  · simp only [vec3_zero, vec3_one, vec3_two, add_apply, smul_apply, neg_apply, ds,
      euclidProj_apply, smul_eq_mul, s]
    field_simp [hden_ne]
    ring

/-- **South-Pole Stereographic Orientation Theorem**: `southPoleStereoInv` pulls `S2VolumeForm`
back to `+(16 / (w₀² + w₁² + 4)²) • planeAreaForm` at every `w : EuclideanPlane`. -/
theorem mpullback_southPoleStereoInv_s2VolumeForm (w : EuclideanPlane) :
    (TauCeti.SmoothForm.mpullback southPoleStereoInv contMDiff_southPoleStereoInv
        S2VolumeForm).1 w =
      (16 / (w 0 ^ 2 + w 1 ^ 2 + 4) ^ 2) • planeAreaForm.1 w := by
  let b : Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) w) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  have hd (u : TangentSpace (𝓡 2) w) :
      mvfderiv (𝓡 2) (Subtype.val : Sphere2 → EuclideanSpace ℝ (Fin 3)) (southPoleStereoInv w)
          (mfderiv (𝓡 2) (𝓡 2) southPoleStereoInv w u) =
        fderiv ℝ southPoleStereoRaw w u := by
    have hcoe : MDifferentiableAt (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
        (Subtype.val : Sphere2 → EuclideanSpace ℝ (Fin 3)) (southPoleStereoInv w) :=
      (contMDiff_coe_sphere (m := ∞) (southPoleStereoInv w)).mdifferentiableAt (by simp)
    have hst : MDifferentiableAt (𝓡 2) (𝓡 2) southPoleStereoInv w :=
      (contMDiff_southPoleStereoInv w).mdifferentiableAt (by simp)
    rw [← mvfderiv_comp_apply w hcoe hst]
    exact TauCeti.mvfderiv_eq_fderiv_apply southPoleStereoRaw w u
  have hbasis_val :
      (TauCeti.SmoothForm.mpullback southPoleStereoInv contMDiff_southPoleStereoInv
          S2VolumeForm).1 w ⇑b =
        16 / (w 0 ^ 2 + w 1 ^ 2 + 4) ^ 2 := by
    rw [TauCeti.SmoothForm.mpullback_apply, S2VolumeForm, Orientation.sphereVolumeForm_apply]
    simp_rw [hd]
    have hb0 : (b 0 : EuclideanPlane) = vec2 1 0 := basisFun2_zero_eq_vec2
    have hb1 : (b 1 : EuclideanPlane) = vec2 0 1 := basisFun2_one_eq_vec2
    let c₀ : EuclideanSpace ℝ (Fin 3) := southPoleStereoRaw w
    let c₁ : EuclideanSpace ℝ (Fin 3) := fderiv ℝ southPoleStereoRaw w (vec2 1 0)
    let c₂ : EuclideanSpace ℝ (Fin 3) := fderiv ℝ southPoleStereoRaw w (vec2 0 1)
    have hcols :
        (Fin.cons (southPoleStereoInv w : EuclideanSpace ℝ (Fin 3))
          fun i : Fin 2 ↦ fderiv ℝ southPoleStereoRaw w (b i)) = ![c₀, c₁, c₂] := by
      funext i
      fin_cases i
      · rfl
      · change fderiv ℝ southPoleStereoRaw w (b 0) = c₁
        rw [hb0]
      · change fderiv ℝ southPoleStereoRaw w (b 1) = c₂
        rw [hb1]
    rw [hcols, volumeForm_basisFun_eq_det, Matrix.det_fin_three]
    dsimp only [Matrix.of_apply]
    have hj0 : (![c₀, c₁, c₂] : Fin 3 → _) 0 = c₀ := rfl
    have hj1 : (![c₀, c₁, c₂] : Fin 3 → _) 1 = c₁ := rfl
    have hj2 : (![c₀, c₁, c₂] : Fin 3 → _) 2 = c₂ := rfl
    rw [hj0, hj1, hj2]
    simp only [c₀, c₁, c₂, fderiv_southPoleStereoRaw_apply, southPoleStereoRaw,
      vec2_zero, vec2_one, vec3_zero, vec3_one, vec3_two]
    have hden : w 0 ^ 2 + w 1 ^ 2 + 4 ≠ 0 := by positivity
    field_simp [hden]
    ring
  have hplane_val : planeAreaForm.1 w ⇑b = 1 := planeAreaForm_apply_basisFun w
  ext v
  rw [ContinuousAlternatingMap.apply_eq_det_mul _ b v, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.apply_eq_det_mul _ b v, hbasis_val, hplane_val, smul_eq_mul]
  ring

end SouthPoleStereographic

/-! ## 3. Explicit Smooth Singular Fibration `s4Fibration : Sphere4 → Sphere2` -/

section S4SingularFibration

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

/-- Smooth singular surface fibration `f_{S⁴} : S⁴ → S²` sending `(x₀, x₁, x₂, x₃, x₄) ∈ S⁴` to
`southPoleStereoInv (x₀, x₁) ∈ S²`. -/
noncomputable def s4Fibration (x : Sphere4) : Sphere2 :=
  southPoleStereoInv (s4ProjPlane x.1)

/-- `s4Fibration` is globally $C^\infty$ smooth (`ContMDiff (𝓡 4) (𝓡 2) ∞`). -/
theorem contMDiff_s4Fibration : ContMDiff (𝓡 4) (𝓡 2) ∞ s4Fibration :=
  contMDiff_southPoleStereoInv.comp (s4ProjPlane.contDiff.contMDiff.comp contMDiff_coe_sphere)

/-- Surjectivity of `mfderiv (𝓡 4) (𝓡 2) s4Fibration x` equals surjectivity of the planar
projection `mfderiv (𝓡 4) (𝓡 2) (s4ProjPlane ∘ Subtype.val) x`. -/
theorem surjective_mfderiv_s4Fibration_iff (x : Sphere4) :
    Function.Surjective (mfderiv (𝓡 4) (𝓡 2) s4Fibration x) ↔
      Function.Surjective (mfderiv (𝓡 4) (𝓡 2) (s4ProjPlane ∘ Subtype.val) x) := by
  have hproj : MDifferentiableAt (𝓡 4) (𝓡 2) (s4ProjPlane ∘ Subtype.val) x :=
    (s4ProjPlane.contDiff.contMDiff.comp (contMDiff_coe_sphere (m := ∞)) x).mdifferentiableAt
      (by simp)
  have hinv := (isLocalDiffeomorph_southPoleStereoInv (s4ProjPlane x.1)).isInvertible_mfderiv
    (by simp)
  have hst : MDifferentiableAt (𝓡 2) (𝓡 2) southPoleStereoInv (s4ProjPlane x.1) :=
    (contMDiff_southPoleStereoInv (s4ProjPlane x.1)).mdifferentiableAt (by simp)
  have hcomp : mfderiv (𝓡 4) (𝓡 2) s4Fibration x =
      (mfderiv (𝓡 2) (𝓡 2) southPoleStereoInv (s4ProjPlane x.1)).comp
        (mfderiv (𝓡 4) (𝓡 2) (s4ProjPlane ∘ Subtype.val) x) :=
    mfderiv_comp x hst hproj
  rw [hcomp]
  refine ⟨fun h y ↦ ?_, fun h ↦ hinv.surjective.comp h⟩
  obtain ⟨v, hv⟩ := h (mfderiv (𝓡 2) (𝓡 2) southPoleStereoInv (s4ProjPlane x.1) y)
  exact ⟨v, hinv.injective hv⟩

/-- Exact characterization of regular points of `s4Fibration`: `mfderiv` is surjective at `x` if
and only if `s4ProjFiber x.1 ≠ 0` (`(x₂, x₃, x₄) ≠ (0, 0, 0)`). -/
theorem surjective_mfderiv_s4Fibration_iff_fiber_ne_zero (x : Sphere4) :
    Function.Surjective (mfderiv (𝓡 4) (𝓡 2) s4Fibration x) ↔ s4ProjFiber x.1 ≠ 0 := by
  rw [surjective_mfderiv_s4Fibration_iff]
  have hcoe : MDifferentiableAt (𝓡 4) 𝓘(ℝ, EuclideanSpace ℝ (Fin 5))
      (Subtype.val : Sphere4 → EuclideanSpace ℝ (Fin 5)) x :=
    (contMDiff_coe_sphere (m := ∞) x).mdifferentiableAt (by simp)
  have hval (v : TangentSpace (𝓡 4) x) :
      (mfderiv (𝓡 4) (𝓡 2) (s4ProjPlane ∘ Subtype.val) x v : EuclideanPlane) =
        s4ProjPlane (mvfderiv (𝓡 4) (Subtype.val : Sphere4 → EuclideanSpace ℝ (Fin 5)) x v) := by
    rw [← mvfderiv_apply_eq_mfderiv_apply, s4ProjPlane.mvfderiv_comp_apply hcoe v]
  constructor
  · intro hsurj hzero
    have hsplit := norm_sq_s4_split x
    rw [hzero, norm_zero, zero_pow two_ne_zero, add_zero, norm_sq_plane] at hsplit
    simp only [s4ProjPlane_apply, vec2_zero, vec2_one] at hsplit
    obtain ⟨v, hv⟩ := hsurj (vec2 (x.1 0) (x.1 1))
    let V : EuclideanSpace ℝ (Fin 5) :=
      mvfderiv (𝓡 4) (Subtype.val : Sphere4 → EuclideanSpace ℝ (Fin 5)) x v
    have hv' : s4ProjPlane V = vec2 (x.1 0) (x.1 1) :=
      (hval v).symm.trans hv
    have hV_mem : V ∈ (ℝ ∙ (x : EuclideanSpace ℝ (Fin 5)))ᗮ := by
      rw [← range_mvfderiv_subtypeVal (n := 4) x]
      exact LinearMap.mem_range_self _ v
    have hinner : ⟪(x : EuclideanSpace ℝ (Fin 5)), V⟫_ℝ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp hV_mem
    rw [PiLp.inner_apply, Fin.sum_univ_five] at hinner
    have hx2 : x.1 2 = 0 := by simpa using congrArg (fun u : EuclideanSpace ℝ (Fin 3) ↦ u 0) hzero
    have hx3 : x.1 3 = 0 := by simpa using congrArg (fun u : EuclideanSpace ℝ (Fin 3) ↦ u 1) hzero
    have hx4 : x.1 4 = 0 := by simpa using congrArg (fun u : EuclideanSpace ℝ (Fin 3) ↦ u 2) hzero
    have hV0 : V 0 = x.1 0 := by
      simpa only [s4ProjPlane_apply, vec2_zero] using congrArg (fun u : EuclideanPlane ↦ u 0) hv'
    have hV1 : V 1 = x.1 1 := by
      simpa only [s4ProjPlane_apply, vec2_one] using congrArg (fun u : EuclideanPlane ↦ u 1) hv'
    simp only [RCLike.inner_apply, conj_trivial, hx2, hx3, hx4, hV0, hV1, mul_zero, add_zero]
      at hinner
    linarith
  · intro hy u
    let u' : EuclideanPlane := u
    let y := s4ProjFiber x.1
    have hy_sq : ‖y‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hy)
    let c : ℝ := -(x.1 0 * u' 0 + x.1 1 * u' 1) / ‖y‖ ^ 2
    let V : EuclideanSpace ℝ (Fin 5) := vec5 (u' 0) (u' 1) (c * y 0) (c * y 1) (c * y 2)
    have hV_orth : V ∈ (ℝ ∙ (x : EuclideanSpace ℝ (Fin 5)))ᗮ := by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right, PiLp.inner_apply, Fin.sum_univ_five]
      have hy_expand : y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 = ‖y‖ ^ 2 := (norm_sq_vec3 y).symm
      have hy_sum_ne : y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 ≠ 0 := by rw [hy_expand]; exact hy_sq
      have hy0 : x.1 2 = y 0 := rfl
      have hy1 : x.1 3 = y 1 := rfl
      have hy2 : x.1 4 = y 2 := rfl
      simp only [RCLike.inner_apply, conj_trivial, V, vec5_zero, vec5_one, vec5_two, vec5_three,
        vec5_four, hy0, hy1, hy2, c, ← hy_expand]
      field_simp [hy_sum_ne]
      ring
    rw [← range_mvfderiv_subtypeVal (n := 4) x] at hV_orth
    obtain ⟨v, hv⟩ := hV_orth
    rw [ContinuousLinearMap.coe_coe] at hv
    refine ⟨v, ?_⟩
    change (mfderiv (𝓡 4) (𝓡 2) (s4ProjPlane ∘ Subtype.val) x v : EuclideanPlane) = u'
    rw [hval v, hv]
    exact ext_vec2 rfl rfl

/-- Exact critical locus of `s4Fibration`: the equatorial circle `{x ∈ S⁴ | s4ProjFiber x.1 = 0}`.
-/
theorem criticalPoints_s4Fibration :
    criticalPoints (𝓡 4) (𝓡 2) s4Fibration = {x : Sphere4 | s4ProjFiber x.1 = 0} := by
  ext x
  rw [mem_criticalPoints_iff, surjective_mfderiv_s4Fibration_iff_fiber_ne_zero, not_not,
    Set.mem_ofPred_eq]

/-- Concrete singular witness `(1, 0, 0, 0, 0) ∈ Sphere4`. -/
noncomputable def s4CriticalPoint : Sphere4 :=
  ⟨vec5 1 0 0 0 0, by
    rw [mem_sphere_zero_iff_norm]
    have hsq : ‖vec5 1 0 0 0 0‖ ^ 2 = 1 := by rw [norm_sq_vec5]; norm_num
    nlinarith [norm_nonneg (vec5 1 0 0 0 0)]⟩

theorem s4CriticalPoint_mem_criticalPoints :
    s4CriticalPoint ∈ criticalPoints (𝓡 4) (𝓡 2) s4Fibration := by
  rw [criticalPoints_s4Fibration, Set.mem_ofPred_eq]
  exact ext_vec3 rfl rfl rfl

/-- Non-emptiness of `criticalPoints (𝓡 4) (𝓡 2) s4Fibration`. -/
theorem criticalPoints_s4Fibration_nonempty :
    (criticalPoints (𝓡 4) (𝓡 2) s4Fibration).Nonempty :=
  ⟨s4CriticalPoint, s4CriticalPoint_mem_criticalPoints⟩

/-- Density of the regular locus `{x : Sphere4 | x ∉ criticalPoints (𝓡 4) (𝓡 2) s4Fibration}` in
`Sphere4` (its equatorial critical circle `{x₂ = x₃ = x₄ = 0}` has empty interior). -/
-- tier: T2
theorem dense_regularPoints_s4Fibration :
    Dense {x : Sphere4 | x ∉ criticalPoints (𝓡 4) (𝓡 2) s4Fibration} := by
  refine dense_iff_inter_open.mpr fun U hU hne ↦ ?_
  obtain ⟨p, hpU⟩ := hne
  by_cases hp : p ∈ criticalPoints (𝓡 4) (𝓡 2) s4Fibration
  · rw [criticalPoints_s4Fibration, Set.mem_ofPred_eq] at hp
    have hp2 : p.1 2 = 0 := by simpa using congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 0) hp
    have hp3 : p.1 3 = 0 := by simpa using congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 1) hp
    have hp4 : p.1 4 = 0 := by simpa using congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 2) hp
    have hp_plane : p.1 0 ^ 2 + p.1 1 ^ 2 = 1 := by
      have hsplit := norm_sq_s4_split p
      rw [hp, norm_zero, zero_pow two_ne_zero, add_zero, norm_sq_plane] at hsplit
      simpa only [s4ProjPlane_apply, vec2_zero, vec2_one] using hsplit
    let γ_raw : ℝ → EuclideanSpace ℝ (Fin 5) := fun t ↦
      vec5 (p.1 0 * (1 - t ^ 2) / (1 + t ^ 2)) (p.1 1 * (1 - t ^ 2) / (1 + t ^ 2))
        (2 * t / (1 + t ^ 2)) 0 0
    have hγ_mem (t : ℝ) : γ_raw t ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1 := by
      rw [mem_sphere_zero_iff_norm]
      have hden : 1 + t ^ 2 ≠ 0 := by positivity
      have hsq : ‖γ_raw t‖ ^ 2 = 1 := by
        rw [norm_sq_vec5]
        simp only [γ_raw, vec5_zero, vec5_one, vec5_two, vec5_three, vec5_four]
        field_simp [hden]
        linear_combination (1 - t ^ 2) ^ 2 * hp_plane
      nlinarith [norm_nonneg (γ_raw t)]
    let γ : ℝ → Sphere4 := fun t ↦ ⟨γ_raw t, hγ_mem t⟩
    have hγ_cont : Continuous γ := by
      refine Continuous.subtype_mk ?_ _
      have hden_cont : Continuous (fun t : ℝ ↦ 1 + t ^ 2) :=
        continuous_const.add (continuous_pow 2)
      have hden_ne : ∀ t : ℝ, 1 + t ^ 2 ≠ 0 := fun t ↦ by positivity
      have hc0 : Continuous (fun t : ℝ ↦ p.1 0 * (1 - t ^ 2) / (1 + t ^ 2)) :=
        (continuous_const.mul (continuous_const.sub (continuous_pow 2))).div hden_cont hden_ne
      have hc1 : Continuous (fun t : ℝ ↦ p.1 1 * (1 - t ^ 2) / (1 + t ^ 2)) :=
        (continuous_const.mul (continuous_const.sub (continuous_pow 2))).div hden_cont hden_ne
      have hc2 : Continuous (fun t : ℝ ↦ 2 * t / (1 + t ^ 2)) :=
        (continuous_const.mul continuous_id).div hden_cont hden_ne
      have hpi : Continuous (fun t : ℝ ↦
          ![p.1 0 * (1 - t ^ 2) / (1 + t ^ 2), p.1 1 * (1 - t ^ 2) / (1 + t ^ 2),
            2 * t / (1 + t ^ 2), 0, 0]) := by
        refine continuous_pi fun i ↦ ?_
        fin_cases i
        · exact hc0
        · exact hc1
        · exact hc2
        · exact continuous_const
        · exact continuous_const
      exact (EuclideanSpace.equiv (Fin 5) ℝ).symm.continuous.comp hpi
    have hγ0 : γ 0 = p := by
      apply Subtype.ext
      change γ_raw 0 = p.1
      refine ext_vec5 ?_ ?_ ?_ hp3.symm hp4.symm <;> simp [γ_raw, hp2]
    have hev : ∀ᶠ t : ℝ in 𝓝 0, γ t ∈ U :=
      hγ_cont.continuousAt.eventually (hγ0 ▸ hU.mem_nhds hpU)
    obtain ⟨ε, hε_pos, hε⟩ := Metric.eventually_nhds_iff.mp hev
    have ht_dist : dist (ε / 2) 0 < ε := by
      rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε_pos)]
      linarith
    refine ⟨γ (ε / 2), hε ht_dist, ?_⟩
    rw [Set.mem_ofPred_eq, criticalPoints_s4Fibration, Set.mem_ofPred_eq]
    intro h0
    have hc : (s4ProjFiber (γ (ε / 2)).1) 0 = 0 :=
      by simpa using congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 0) h0
    have hpos : 0 < 2 * (ε / 2) / (1 + (ε / 2) ^ 2) := by positivity
    exact hpos.ne' (by simpa [γ, γ_raw, s4ProjFiber_apply] using hc)
  · exact ⟨p, hpU, hp⟩

/-- The equatorial critical locus of `s4Fibration` has empty interior in `Sphere4`. -/
-- tier: T1
theorem interior_criticalPoints_s4Fibration_eq_empty :
    interior (criticalPoints (𝓡 4) (𝓡 2) s4Fibration) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦ ?_
  obtain ⟨y, hy_int, hy_reg⟩ :=
    dense_regularPoints_s4Fibration.inter_open_nonempty _ isOpen_interior ⟨x, hx⟩
  exact hy_reg (interior_subset hy_int)

end S4SingularFibration

/-! ## 4. Open Regular Base Region `s4BaseRegion` and Smooth Trivialization `s4Trivialization` -/

section S4Trivialization

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

/-- Radius `1 / 2` of the planar coordinate disk `s4PlaneDisk ⊂ ℝ²`. -/
noncomputable abbrev s4BaseDiskRadius : ℝ := 1 / 2

theorem s4BaseDiskRadius_pos : 0 < s4BaseDiskRadius := by norm_num

/-- Planar open disk `Metric.ball 0 (1 / 2)` as an element of `Opens EuclideanPlane`. -/
noncomputable abbrev s4PlaneDisk : Opens EuclideanPlane :=
  ⟨Metric.ball (0 : EuclideanPlane) s4BaseDiskRadius, Metric.isOpen_ball⟩

theorem norm_lt_half_of_mem_s4PlaneDisk (w : s4PlaneDisk) : ‖w.1‖ < 1 / 2 := by
  simpa only [s4PlaneDisk, s4BaseDiskRadius, Opens.mem_mk, Metric.mem_ball,
    dist_zero_right] using w.2

theorem mem_s4PlaneDisk_of_norm_lt_half {w : EuclideanPlane} (hw : ‖w‖ < 1 / 2) :
    w ∈ s4PlaneDisk := by
  simpa only [s4PlaneDisk, s4BaseDiskRadius, Opens.mem_mk, Metric.mem_ball,
    dist_zero_right] using hw

/-- Open regular disk `southPoleStereoInv '' Metric.ball 0 (1 / 2) ⊂ Sphere2`. -/
noncomputable def s4BaseRegion : Opens Sphere2 :=
  ⟨southPoleStereoInv '' Metric.ball (0 : EuclideanPlane) s4BaseDiskRadius,
    isOpenEmbedding_southPoleStereoInv.isOpenMap _ Metric.isOpen_ball⟩

theorem s2NorthPole_mem_s4BaseRegion : s2NorthPole ∈ s4BaseRegion.1 :=
  ⟨0, Metric.mem_ball_self s4BaseDiskRadius_pos, southPoleStereoInv_zero⟩

theorem s4BaseRegion_nonempty : s4BaseRegion.1.Nonempty :=
  ⟨s2NorthPole, s2NorthPole_mem_s4BaseRegion⟩

/-- A point `x ∈ Sphere4` lies over `s4BaseRegion` if and only if `‖s4ProjPlane x.1‖ < 1 / 2`. -/
theorem mem_preimage_s4BaseRegion_iff (x : Sphere4) :
    x ∈ s4Fibration ⁻¹' s4BaseRegion.1 ↔ ‖s4ProjPlane x.1‖ < 1 / 2 := by
  change southPoleStereoInv (s4ProjPlane x.1) ∈
      southPoleStereoInv '' Metric.ball (0 : EuclideanPlane) (1 / 2) ↔ _
  rw [injective_southPoleStereoInv.mem_set_image, Metric.mem_ball, dist_zero_right]

/-- Every point in `s4Fibration ⁻¹' s4BaseRegion` is a regular point of `s4Fibration`. -/
theorem regular_on_s4BaseRegion :
    ∀ x ∈ s4Fibration ⁻¹' s4BaseRegion.1,
      Function.Surjective (mfderiv (𝓡 4) (𝓡 2) s4Fibration x) := by
  intro x hx
  rw [mem_preimage_s4BaseRegion_iff] at hx
  rw [surjective_mfderiv_s4Fibration_iff_fiber_ne_zero]
  intro hzero
  have hsplit := norm_sq_s4_split x
  rw [hzero, norm_zero, zero_pow two_ne_zero, add_zero] at hsplit
  nlinarith [norm_nonneg (s4ProjPlane x.1)]

/-- `s4BaseRegion` is disjoint from the critical-value circle `s4Fibration '' Crit(s4Fibration)`. -/
theorem disjoint_s4BaseRegion_criticalPoints :
    Disjoint s4BaseRegion.1 (s4Fibration '' criticalPoints (𝓡 4) (𝓡 2) s4Fibration) :=
  disjoint_image_criticalPoints_iff.mpr regular_on_s4BaseRegion

/-- Smooth diffeomorphism `s4PlaneDisk ≃ₘ⟮𝓡 2, 𝓡 2⟯ s4BaseRegion` restricting `southPoleStereoInv`.
-/
noncomputable def s4BaseDiskDiffeomorph : s4PlaneDisk ≃ₘ⟮𝓡 2, 𝓡 2⟯ s4BaseRegion where
  toFun w := ⟨southPoleStereoInv w.1, ⟨w.1, w.2, rfl⟩⟩
  invFun b := ⟨southPoleStereoChart b.1, by
    obtain ⟨w, hw, hw_eq⟩ := b.2
    rw [← hw_eq, southPoleStereoChart_inv]
    exact hw⟩
  left_inv w := Subtype.ext (southPoleStereoChart_inv w.1)
  right_inv b := by
    obtain ⟨w, -, hw_eq⟩ := b.2
    apply Subtype.ext
    dsimp only
    rw [← hw_eq, southPoleStereoChart_inv]
  contMDiff_toFun :=
    (TauCeti.ContMDiff.subtypeVal_comp_iff s4BaseRegion _).mp
      (contMDiff_southPoleStereoInv.comp contMDiff_subtype_val)
  contMDiff_invFun := by
    have hsub : s4BaseRegion.1 ⊆ s2PuncturedSouth.1 := by
      rintro _ ⟨w, -, rfl⟩
      exact southPoleStereoInv_ne_southPole w
    have hincl : ContMDiff (𝓡 2) (𝓡 2) ∞
        (fun b : s4BaseRegion ↦ (⟨b.1, hsub b.2⟩ : s2PuncturedSouth)) :=
      (TauCeti.ContMDiff.subtypeVal_comp_iff s2PuncturedSouth _).mp contMDiff_subtype_val
    exact (TauCeti.ContMDiff.subtypeVal_comp_iff s4PlaneDisk _).mp
      (southPoleStereoDiffeomorph.symm.contMDiff.comp hincl)

@[simp]
theorem coe_s4BaseDiskDiffeomorph (w : s4PlaneDisk) :
    (s4BaseDiskDiffeomorph w).1 = southPoleStereoInv w.1 :=
  rfl

/-- Open preimage `s4Fibration ⁻¹' s4BaseRegion.1` in `Sphere4`. -/
noncomputable abbrev s4PreimageOpen : Opens Sphere4 :=
  ⟨s4Fibration ⁻¹' s4BaseRegion.1, s4BaseRegion.2.preimage contMDiff_s4Fibration.continuous⟩

theorem one_sub_norm_sq_pos_of_mem_s4PlaneDisk (w : s4PlaneDisk) :
    0 < 1 - (w.1 0 ^ 2 + w.1 1 ^ 2) := by
  have hw : ‖w.1‖ < 1 / 2 := norm_lt_half_of_mem_s4PlaneDisk w
  have hsq : w.1 0 ^ 2 + w.1 1 ^ 2 = ‖w.1‖ ^ 2 := (norm_sq_plane w.1).symm
  nlinarith [norm_nonneg w.1]

/-- Ambient formula for the planar product embedding `s4PlaneDisk × Sphere2 → ℝ⁵`:
`((w₀, w₁), z) ↦ (w₀, w₁, √(1 - w₀² - w₁²) • z)`. -/
noncomputable def s4PlaneEmbedRaw (w : EuclideanPlane) (z : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 5) :=
  let ρ := Real.sqrt (1 - (w 0 ^ 2 + w 1 ^ 2))
  vec5 (w 0) (w 1) (ρ * z 0) (ρ * z 1) (ρ * z 2)

theorem s4PlaneEmbedRaw_mem_sphere (w : s4PlaneDisk) (z : Sphere2) :
    s4PlaneEmbedRaw w.1 z.1 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have hpos := (one_sub_norm_sq_pos_of_mem_s4PlaneDisk w).le
  have hz : z.1 0 ^ 2 + z.1 1 ^ 2 + z.1 2 ^ 2 = 1 := by
    rw [← norm_sq_vec3, mem_sphere_zero_iff_norm.mp z.2]
    norm_num
  have hsq : ‖s4PlaneEmbedRaw w.1 z.1‖ ^ 2 = 1 := by
    rw [norm_sq_vec5]
    simp only [s4PlaneEmbedRaw, vec5_zero, vec5_one, vec5_two, vec5_three, vec5_four]
    calc
      w.1 0 ^ 2 + w.1 1 ^ 2 + (Real.sqrt (1 - (w.1 0 ^ 2 + w.1 1 ^ 2)) * z.1 0) ^ 2 +
          (Real.sqrt (1 - (w.1 0 ^ 2 + w.1 1 ^ 2)) * z.1 1) ^ 2 +
          (Real.sqrt (1 - (w.1 0 ^ 2 + w.1 1 ^ 2)) * z.1 2) ^ 2
        = w.1 0 ^ 2 + w.1 1 ^ 2 +
            Real.sqrt (1 - (w.1 0 ^ 2 + w.1 1 ^ 2)) ^ 2 *
              (z.1 0 ^ 2 + z.1 1 ^ 2 + z.1 2 ^ 2) := by ring
      _ = w.1 0 ^ 2 + w.1 1 ^ 2 + (1 - (w.1 0 ^ 2 + w.1 1 ^ 2)) * 1 := by
        rw [Real.sq_sqrt hpos, hz]
      _ = 1 := by ring
  nlinarith [norm_nonneg (s4PlaneEmbedRaw w.1 z.1)]

/-- Smooth product open embedding `s4PlaneDisk × Sphere2 → Sphere4` over `Metric.ball 0 (1 / 2)`. -/
noncomputable def s4PlaneEmbed (wz : s4PlaneDisk × Sphere2) : Sphere4 :=
  ⟨s4PlaneEmbedRaw wz.1.1 wz.2.1, s4PlaneEmbedRaw_mem_sphere wz.1 wz.2⟩

@[simp]
theorem coe_s4PlaneEmbed (wz : s4PlaneDisk × Sphere2) :
    (s4PlaneEmbed wz : EuclideanSpace ℝ (Fin 5)) = s4PlaneEmbedRaw wz.1.1 wz.2.1 :=
  rfl

theorem contMDiff_s4PlaneEmbed : ContMDiff ((𝓡 2).prod (𝓡 2)) (𝓡 4) ∞ s4PlaneEmbed := by
  have hw_val : ContMDiff ((𝓡 2).prod (𝓡 2)) 𝓘(ℝ, EuclideanPlane) ∞
      (fun wz : s4PlaneDisk × Sphere2 ↦ wz.1.1) :=
    contMDiff_subtype_val.comp contMDiff_fst
  have hz_val : ContMDiff ((𝓡 2).prod (𝓡 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (fun wz : s4PlaneDisk × Sphere2 ↦ wz.2.1) :=
    contMDiff_coe_sphere.comp contMDiff_snd
  have hw (i : Fin 2) : ContMDiff ((𝓡 2).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (fun wz : s4PlaneDisk × Sphere2 ↦ wz.1.1 i) :=
    (euclidProj i).contDiff.contMDiff.comp hw_val
  have hz (j : Fin 3) : ContMDiff ((𝓡 2).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (fun wz : s4PlaneDisk × Sphere2 ↦ wz.2.1 j) :=
    (euclidProj j).contDiff.contMDiff.comp hz_val
  have hrad_diff : ContDiff ℝ ∞ (fun w : EuclideanPlane ↦ 1 - (w 0 ^ 2 + w 1 ^ 2)) :=
    contDiff_const.sub ((((euclidProj (0 : Fin 2)).contDiff.pow 2).add
      ((euclidProj (1 : Fin 2)).contDiff.pow 2)))
  have hrad_m : ContMDiff ((𝓡 2).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (fun wz : s4PlaneDisk × Sphere2 ↦ 1 - (wz.1.1 0 ^ 2 + wz.1.1 1 ^ 2)) :=
    hrad_diff.contMDiff.comp hw_val
  have hρ : ContMDiff ((𝓡 2).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (fun wz : s4PlaneDisk × Sphere2 ↦ Real.sqrt (1 - (wz.1.1 0 ^ 2 + wz.1.1 1 ^ 2))) := by
    intro wz
    have hpos := one_sub_norm_sq_pos_of_mem_s4PlaneDisk wz.1
    exact (Real.contDiffAt_sqrt hpos.ne').contMDiffAt.comp wz (hrad_m wz)
  have hmul : ContDiff ℝ ∞ (fun q : ℝ × ℝ ↦ q.1 * q.2) := contDiff_fst.mul contDiff_snd
  have hraw : ContMDiff ((𝓡 2).prod (𝓡 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 5)) ∞
      (fun wz : s4PlaneDisk × Sphere2 ↦ s4PlaneEmbedRaw wz.1.1 wz.2.1) := by
    have hpi : ContMDiff ((𝓡 2).prod (𝓡 2)) 𝓘(ℝ, Fin 5 → ℝ) ∞
        (fun wz : s4PlaneDisk × Sphere2 ↦
          ![wz.1.1 0, wz.1.1 1,
            Real.sqrt (1 - (wz.1.1 0 ^ 2 + wz.1.1 1 ^ 2)) * wz.2.1 0,
            Real.sqrt (1 - (wz.1.1 0 ^ 2 + wz.1.1 1 ^ 2)) * wz.2.1 1,
            Real.sqrt (1 - (wz.1.1 0 ^ 2 + wz.1.1 1 ^ 2)) * wz.2.1 2]) := by
      refine contMDiff_pi_module_iff.mpr fun i ↦ ?_
      fin_cases i
      · exact hw 0
      · exact hw 1
      · exact hmul.contMDiff.comp (hρ.prodMk_space (hz 0))
      · exact hmul.contMDiff.comp (hρ.prodMk_space (hz 1))
      · exact hmul.contMDiff.comp (hρ.prodMk_space (hz 2))
    exact (EuclideanSpace.equiv (Fin 5) ℝ).symm.contDiff.contMDiff.comp hpi
  exact hraw.codRestrict_sphere fun wz ↦ s4PlaneEmbedRaw_mem_sphere wz.1 wz.2

theorem s4PlaneEmbed_mem_preimage (wz : s4PlaneDisk × Sphere2) :
    s4PlaneEmbed wz ∈ s4Fibration ⁻¹' s4BaseRegion.1 := by
  rw [mem_preimage_s4BaseRegion_iff]
  have heq : s4ProjPlane (s4PlaneEmbed wz).1 = wz.1.1 := ext_vec2 rfl rfl
  rw [heq]
  exact norm_lt_half_of_mem_s4PlaneDisk wz.1

/-- Normalized fiber projection `x ↦ (1 / √(1 - x₀² - x₁²)) • (x₂, x₃, x₄) ∈ Sphere2` on
`s4PreimageOpen`. -/
noncomputable def s4FiberNormalize (u : s4PreimageOpen) : Sphere2 :=
  let w : s4PlaneDisk := ⟨s4ProjPlane u.1.1,
    mem_s4PlaneDisk_of_norm_lt_half ((mem_preimage_s4BaseRegion_iff u.1).mp u.2)⟩
  let ρ := Real.sqrt (1 - (w.1 0 ^ 2 + w.1 1 ^ 2))
  ⟨ρ⁻¹ • s4ProjFiber u.1.1, by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs]
    have hρ_pos : 0 < ρ := Real.sqrt_pos.mpr (one_sub_norm_sq_pos_of_mem_s4PlaneDisk w)
    have hsplit := norm_sq_s4_split u.1
    have hw_sq : ‖s4ProjPlane u.1.1‖ ^ 2 = w.1 0 ^ 2 + w.1 1 ^ 2 := norm_sq_plane w.1
    have hfib_sq : ‖s4ProjFiber u.1.1‖ ^ 2 = ρ ^ 2 := by
      rw [Real.sq_sqrt (one_sub_norm_sq_pos_of_mem_s4PlaneDisk w).le]
      linarith
    have hfib_norm : ‖s4ProjFiber u.1.1‖ = ρ := by
      nlinarith [norm_nonneg (s4ProjFiber u.1.1), hρ_pos]
    rw [abs_of_pos (inv_pos.mpr hρ_pos), hfib_norm, inv_mul_cancel₀ hρ_pos.ne']⟩

/-- Smooth planar trivialization `s4PreimageOpen ≃ₘ⟮𝓡 4, (𝓡 2).prod (𝓡 2)⟯ (s4PlaneDisk × Sphere2)`.
-/
noncomputable def s4PlaneTrivialization :
    s4PreimageOpen ≃ₘ⟮𝓡 4, (𝓡 2).prod (𝓡 2)⟯ (s4PlaneDisk × Sphere2) where
  toFun u :=
    (⟨s4ProjPlane u.1.1,
        mem_s4PlaneDisk_of_norm_lt_half ((mem_preimage_s4BaseRegion_iff u.1).mp u.2)⟩,
      s4FiberNormalize u)
  invFun wz := ⟨s4PlaneEmbed wz, s4PlaneEmbed_mem_preimage wz⟩
  left_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    let w : s4PlaneDisk := ⟨s4ProjPlane u.1.1,
      mem_s4PlaneDisk_of_norm_lt_half ((mem_preimage_s4BaseRegion_iff u.1).mp u.2)⟩
    have hρ_ne : Real.sqrt (1 - (w.1 0 ^ 2 + w.1 1 ^ 2)) ≠ 0 :=
      (Real.sqrt_pos.mpr (one_sub_norm_sq_pos_of_mem_s4PlaneDisk w)).ne'
    refine ext_vec5 rfl rfl ?_ ?_ ?_ <;>
    · simp only [coe_s4PlaneEmbed, s4PlaneEmbedRaw, s4FiberNormalize, s4ProjPlane_apply,
        s4ProjFiber_apply, vec2_zero, vec2_one, vec3_zero, vec3_one, vec3_two, vec5_two,
        vec5_three, vec5_four, PiLp.smul_apply, smul_eq_mul]
      exact mul_inv_cancel_left₀ hρ_ne _
  right_inv wz := by
    have hw_eq : (⟨s4ProjPlane (s4PlaneEmbed wz).1,
        mem_s4PlaneDisk_of_norm_lt_half
          ((mem_preimage_s4BaseRegion_iff (s4PlaneEmbed wz)).mp
            (s4PlaneEmbed_mem_preimage wz))⟩ :
          s4PlaneDisk) = wz.1 :=
      Subtype.ext (ext_vec2 rfl rfl)
    refine Prod.ext hw_eq (Subtype.ext ?_)
    have hρ_ne : Real.sqrt (1 - (wz.1.1 0 ^ 2 + wz.1.1 1 ^ 2)) ≠ 0 :=
      (Real.sqrt_pos.mpr (one_sub_norm_sq_pos_of_mem_s4PlaneDisk wz.1)).ne'
    refine ext_vec3 ?_ ?_ ?_ <;>
    · simp only [s4FiberNormalize, coe_s4PlaneEmbed, s4PlaneEmbedRaw, s4ProjPlane_apply,
        s4ProjFiber_apply, vec2_zero, vec2_one, vec3_zero, vec3_one, vec3_two, vec5_zero,
        vec5_one, vec5_two, vec5_three, vec5_four, PiLp.smul_apply, smul_eq_mul]
      exact inv_mul_cancel_left₀ hρ_ne _
  contMDiff_toFun := by
    have hcoe : ContMDiff (𝓡 4) 𝓘(ℝ, EuclideanSpace ℝ (Fin 5)) ∞
        (fun u : s4PreimageOpen ↦ u.1.1) :=
      contMDiff_coe_sphere.comp contMDiff_subtype_val
    have hw_val : ContMDiff (𝓡 4) (𝓡 2) ∞ (fun u : s4PreimageOpen ↦ s4ProjPlane u.1.1) :=
      s4ProjPlane.contDiff.contMDiff.comp hcoe
    have hw_disk : ContMDiff (𝓡 4) (𝓡 2) ∞
        (fun u : s4PreimageOpen ↦ (⟨s4ProjPlane u.1.1,
          mem_s4PlaneDisk_of_norm_lt_half ((mem_preimage_s4BaseRegion_iff u.1).mp u.2)⟩ :
            s4PlaneDisk)) :=
      (TauCeti.ContMDiff.subtypeVal_comp_iff s4PlaneDisk _).mp hw_val
    have hfib_val : ContMDiff (𝓡 4) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
        (fun u : s4PreimageOpen ↦ s4ProjFiber u.1.1) :=
      s4ProjFiber.contDiff.contMDiff.comp hcoe
    have hrad_diff : ContDiff ℝ ∞ (fun w : EuclideanPlane ↦ 1 - (w 0 ^ 2 + w 1 ^ 2)) :=
      contDiff_const.sub ((((euclidProj (0 : Fin 2)).contDiff.pow 2).add
        ((euclidProj (1 : Fin 2)).contDiff.pow 2)))
    have hrad_m : ContMDiff (𝓡 4) 𝓘(ℝ, ℝ) ∞
        (fun u : s4PreimageOpen ↦ 1 - ((s4ProjPlane u.1.1) 0 ^ 2 + (s4ProjPlane u.1.1) 1 ^ 2)) :=
      hrad_diff.contMDiff.comp hw_val
    have hρ_m : ContMDiff (𝓡 4) 𝓘(ℝ, ℝ) ∞
        (fun u : s4PreimageOpen ↦
          Real.sqrt (1 - ((s4ProjPlane u.1.1) 0 ^ 2 + (s4ProjPlane u.1.1) 1 ^ 2))) := by
      intro u
      let w : s4PlaneDisk := ⟨s4ProjPlane u.1.1,
        mem_s4PlaneDisk_of_norm_lt_half ((mem_preimage_s4BaseRegion_iff u.1).mp u.2)⟩
      have hpos := one_sub_norm_sq_pos_of_mem_s4PlaneDisk w
      exact (Real.contDiffAt_sqrt hpos.ne').contMDiffAt.comp u (hrad_m u)
    have hρ_inv : ContMDiff (𝓡 4) 𝓘(ℝ, ℝ) ∞
        (fun u : s4PreimageOpen ↦
          (Real.sqrt (1 - ((s4ProjPlane u.1.1) 0 ^ 2 + (s4ProjPlane u.1.1) 1 ^ 2)))⁻¹) := by
      intro u
      let w : s4PlaneDisk := ⟨s4ProjPlane u.1.1,
        mem_s4PlaneDisk_of_norm_lt_half ((mem_preimage_s4BaseRegion_iff u.1).mp u.2)⟩
      have hpos := one_sub_norm_sq_pos_of_mem_s4PlaneDisk w
      have hρ_ne : Real.sqrt (1 - (w.1 0 ^ 2 + w.1 1 ^ 2)) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
      exact (contDiffAt_inv ℝ hρ_ne).contMDiffAt.comp u (hρ_m u)
    have hsmul : ContDiff ℝ ∞
        (fun q : ℝ × EuclideanSpace ℝ (Fin 3) ↦ q.1 • q.2) :=
      contDiff_fst.smul contDiff_snd
    have hnorm_raw : ContMDiff (𝓡 4) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
        (fun u : s4PreimageOpen ↦ (s4FiberNormalize u : EuclideanSpace ℝ (Fin 3))) :=
      hsmul.contMDiff.comp (hρ_inv.prodMk_space hfib_val)
    have hnorm_s2 : ContMDiff (𝓡 4) (𝓡 2) ∞ s4FiberNormalize :=
      hnorm_raw.codRestrict_sphere fun u ↦ (s4FiberNormalize u).2
    exact hw_disk.prodMk hnorm_s2
  contMDiff_invFun :=
    (TauCeti.ContMDiff.subtypeVal_comp_iff s4PreimageOpen _).mp contMDiff_s4PlaneEmbed

/-- Smooth trivialization `s4Fibration ⁻¹' s4BaseRegion ≃ₘ s4BaseRegion × Sphere2`. -/
noncomputable def s4Trivialization :
    s4PreimageOpen ≃ₘ⟮𝓡 4, (𝓡 2).prod (𝓡 2)⟯ (s4BaseRegion × Sphere2) :=
  s4PlaneTrivialization.trans (s4BaseDiskDiffeomorph.prodCongr (Diffeomorph.refl (𝓡 2) Sphere2 ∞))

@[simp]
theorem s4Trivialization_fst (u : s4PreimageOpen) :
    (s4Trivialization u).1 = ⟨s4Fibration u.1, u.2⟩ := by
  apply Subtype.ext
  rfl

@[simp]
theorem coe_s4Trivialization_symm_plane (wz : s4PlaneDisk × Sphere2) :
    (s4Trivialization.symm (s4BaseDiskDiffeomorph wz.1, wz.2)).1 = s4PlaneEmbed wz := by
  have hsymm :
      (s4BaseDiskDiffeomorph.prodCongr (Diffeomorph.refl (𝓡 2) Sphere2 ∞)).symm
        (s4BaseDiskDiffeomorph wz.1, wz.2) = wz :=
    Prod.ext (s4BaseDiskDiffeomorph.symm_apply_apply wz.1) rfl
  change (s4PlaneTrivialization.symm
      ((s4BaseDiskDiffeomorph.prodCongr (Diffeomorph.refl (𝓡 2) Sphere2 ∞)).symm
        (s4BaseDiskDiffeomorph wz.1, wz.2))).1 = s4PlaneEmbed wz
  rw [hsymm]
  rfl

/-- `s4Fibration` packaged as a global `RegularDiskFibration (𝓡 4) Sphere4 (𝓡 2) Sphere2 Sphere2`
with regular `Sphere2` fiber. -/
noncomputable def s4RegularDiskFibration :
    RegularDiskFibration (𝓡 4) Sphere4 (𝓡 2) Sphere2 Sphere2 where
  toFun := s4Fibration
  contMDiff_toFun := contMDiff_s4Fibration
  baseRegion := s4BaseRegion
  baseRegion_nonempty := s4BaseRegion_nonempty
  regular_on_preimage := regular_on_s4BaseRegion
  baseDiskRadius := s4BaseDiskRadius
  baseDiskRadius_pos := s4BaseDiskRadius_pos
  baseDisk := s4BaseDiskDiffeomorph
  trivialization := s4Trivialization
  trivialization_fst := s4Trivialization_fst

end S4Trivialization

/-! ## 5. Strict Positive Co-Orientation of `s4Trivialization` with $\Omega_{S^4}$ & $\sigma_{S^2}$
-/

section S4CoOrientation

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

/-- Block evaluation of the wedge of two 2-forms pulled back from the two factors of a product
manifold `M₁ × M₂` on `![(a₀, 0), (a₁, 0), (0, b₀), (0, b₁)]`. -/
theorem wedge_mpullback_fst_snd_two_two
    {E₁ H₁ M₁ E₂ H₂ M₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [IsManifold I₁ 1 M₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    [IsManifold I₂ 1 M₂]
    (α : TauCeti.SmoothForm I₁ M₁ ℝ 2) (β : TauCeti.SmoothForm I₂ M₂ ℝ 2)
    (p : M₁ × M₂) (a₀ a₁ : TangentSpace I₁ p.1) (b₀ b₁ : TangentSpace I₂ p.2) :
    let e := TauCeti.Manifold.tangentSpaceProdEquiv (I := I₁) (J := I₂) p
    (TauCeti.SmoothForm.wedge
        (TauCeti.SmoothForm.mpullback Prod.fst contMDiff_fst α)
        (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd β)).1 p
      ![e.symm (a₀, 0), e.symm (a₁, 0), e.symm (0, b₀), e.symm (0, b₁)] =
      α.1 p.1 ![a₀, a₁] * β.1 p.2 ![b₀, b₁] := by
  intro e
  let V : Fin (2 + 2) → TangentSpace (I₁.prod I₂) p :=
    ![e.symm (a₀, 0), e.symm (a₁, 0), e.symm (0, b₀), e.symm (0, b₁)]
  let f₁ : Fin (2 + 2) → TangentSpace I₁ p.1 := ![a₀, a₁, 0, 0]
  let f₂ : Fin (2 + 2) → TangentSpace I₂ p.2 := ![0, 0, b₀, b₁]
  have hf₁ (k : Fin (2 + 2)) : (e (V k)).1 = f₁ k := by
    fin_cases k <;> simp [V, f₁]
  have hf₂ (k : Fin (2 + 2)) : (e (V k)).2 = f₂ k := by
    fin_cases k <;> simp [V, f₂]
  change (TauCeti.SmoothForm.wedge
      (TauCeti.SmoothForm.mpullback Prod.fst contMDiff_fst α)
      (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd β)).1 p V = _
  rw [TauCeti.SmoothForm.wedge_apply]
  simp_rw [TauCeti.SmoothForm.mpullback_fst_apply, TauCeti.SmoothForm.mpullback_snd_apply,
    show ∀ k, (TauCeti.Manifold.tangentSpaceProdEquiv p (V k)).1 = f₁ k from hf₁,
    show ∀ k, (TauCeti.Manifold.tangentSpaceProdEquiv p (V k)).2 = f₂ k from hf₂]
  let blockPerm (τ : Equiv.Perm (Fin 2) × Equiv.Perm (Fin 2)) : Equiv.Perm (Fin (2 + 2)) :=
    finSumFinEquiv.permCongr (Equiv.Perm.sumCongr τ.1 τ.2)
  have hblock_inj : Function.Injective blockPerm := by
    rintro ⟨τ₁, τ₂⟩ ⟨τ₁', τ₂'⟩ h
    have h' := finSumFinEquiv.permCongr.injective h
    exact Prod.ext
      (Equiv.ext fun i ↦ Sum.inl.inj (congrArg (fun σ ↦ σ (Sum.inl i)) h'))
      (Equiv.ext fun j ↦ Sum.inr.inj (congrArg (fun σ ↦ σ (Sum.inr j)) h'))
  let S : Finset (Equiv.Perm (Fin (2 + 2))) := Finset.univ.image blockPerm
  have hzero_outside : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin (2 + 2)))), σ ∉ S →
      Equiv.Perm.sign σ •
        (α.1 p.1 (fun i ↦ f₁ (σ (Fin.castAdd 2 i))) *
          β.1 p.2 (fun j ↦ f₂ (σ (Fin.natAdd 2 j)))) = 0 := by
    intro σ _ hnotS
    by_cases h01 : (σ 0).1 < 2 ∧ (σ 1).1 < 2
    · exfalso
      apply hnotS
      rw [Finset.mem_image]
      have hne01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
      have h2_ge : 2 ≤ (σ 2).1 := by
        by_contra! hlt2
        have hne02 : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
        have hne12 : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
        omega
      have h3_ge : 2 ≤ (σ 3).1 := by
        by_contra! hlt2
        have hne03 : σ 0 ≠ σ 3 := σ.injective.ne (by decide)
        have hne13 : σ 1 ≠ σ 3 := σ.injective.ne (by decide)
        omega
      let τ₁ : Equiv.Perm (Fin 2) := if (σ 0).1 = 0 then 1 else Equiv.swap 0 1
      let τ₂ : Equiv.Perm (Fin 2) := if (σ 2).1 = 2 then 1 else Equiv.swap 0 1
      refine ⟨(τ₁, τ₂), Finset.mem_univ _, Equiv.ext fun k ↦ ?_⟩
      have hne23 : σ 2 ≠ σ 3 := σ.injective.ne (by decide)
      have h0_lt : (σ 0).1 < 2 := h01.1
      have h1_lt : (σ 1).1 < 2 := h01.2
      have h2_lt : (σ 2).1 < 4 := (σ 2).2
      have h3_lt : (σ 3).1 < 4 := (σ 3).2
      have hne01_val : (σ 0).1 ≠ (σ 1).1 := Fin.val_ne_of_ne hne01
      have hne23_val : (σ 2).1 ≠ (σ 3).1 := Fin.val_ne_of_ne hne23
      fin_cases k
      · change finSumFinEquiv (Equiv.Perm.sumCongr τ₁ τ₂ (finSumFinEquiv.symm 0)) = σ 0
        have hs0 : finSumFinEquiv.symm (0 : Fin (2 + 2)) = Sum.inl 0 :=
          finSumFinEquiv.symm_apply_eq.mpr rfl
        rw [hs0, Equiv.Perm.sumCongr_apply, Sum.map_inl, finSumFinEquiv_apply_left]
        dsimp only [τ₁]
        split_ifs with h0
        · exact Fin.ext h0.symm
        · rw [Equiv.swap_apply_left]
          refine Fin.ext ?_
          change 1 = (σ 0).1
          omega
      · change finSumFinEquiv (Equiv.Perm.sumCongr τ₁ τ₂ (finSumFinEquiv.symm 1)) = σ 1
        have hs1 : finSumFinEquiv.symm (1 : Fin (2 + 2)) = Sum.inl 1 :=
          finSumFinEquiv.symm_apply_eq.mpr rfl
        rw [hs1, Equiv.Perm.sumCongr_apply, Sum.map_inl, finSumFinEquiv_apply_left]
        dsimp only [τ₁]
        split_ifs with h0
        · refine Fin.ext ?_
          change 1 = (σ 1).1
          omega
        · rw [Equiv.swap_apply_right]
          refine Fin.ext ?_
          change 0 = (σ 1).1
          omega
      · change finSumFinEquiv (Equiv.Perm.sumCongr τ₁ τ₂ (finSumFinEquiv.symm 2)) = σ 2
        have hs2 : finSumFinEquiv.symm (2 : Fin (2 + 2)) = Sum.inr 0 :=
          finSumFinEquiv.symm_apply_eq.mpr rfl
        rw [hs2, Equiv.Perm.sumCongr_apply, Sum.map_inr, finSumFinEquiv_apply_right]
        dsimp only [τ₂]
        split_ifs with h2
        · exact Fin.ext h2.symm
        · rw [Equiv.swap_apply_left]
          refine Fin.ext ?_
          change 3 = (σ 2).1
          omega
      · change finSumFinEquiv (Equiv.Perm.sumCongr τ₁ τ₂ (finSumFinEquiv.symm 3)) = σ 3
        have hs3 : finSumFinEquiv.symm (3 : Fin (2 + 2)) = Sum.inr 1 :=
          finSumFinEquiv.symm_apply_eq.mpr rfl
        rw [hs3, Equiv.Perm.sumCongr_apply, Sum.map_inr, finSumFinEquiv_apply_right]
        dsimp only [τ₂]
        split_ifs with h2
        · refine Fin.ext ?_
          change 3 = (σ 3).1
          omega
        · rw [Equiv.swap_apply_right]
          refine Fin.ext ?_
          change 2 = (σ 3).1
          omega
    · have hα_zero : α.1 p.1 (fun i ↦ f₁ (σ (Fin.castAdd 2 i))) = 0 := by
        by_cases h0 : (σ 0).1 < 2
        · have h1 : 2 ≤ (σ 1).1 := not_lt.mp fun h1 ↦ h01 ⟨h0, h1⟩
          have hf1_zero : f₁ (σ (Fin.castAdd 2 1)) = 0 := by
            change f₁ (σ 1) = 0
            rcases hσ1 : σ 1 with ⟨val, hlt⟩
            rw [hσ1] at h1
            interval_cases val <;> rfl
          exact (α.1 p.1).map_coord_zero 1 hf1_zero
        · have h0' : 2 ≤ (σ 0).1 := not_lt.mp h0
          have hf0_zero : f₁ (σ (Fin.castAdd 2 0)) = 0 := by
            change f₁ (σ 0) = 0
            rcases hσ0 : σ 0 with ⟨val, hlt⟩
            rw [hσ0] at h0'
            interval_cases val <;> rfl
          exact (α.1 p.1).map_coord_zero 0 hf0_zero
      rw [hα_zero, zero_mul, smul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ S) hzero_outside,
    Finset.sum_image fun _ _ _ _ h ↦ hblock_inj h]
  have hterm (τ : Equiv.Perm (Fin 2) × Equiv.Perm (Fin 2)) :
      Equiv.Perm.sign (blockPerm τ) •
        (α.1 p.1 (fun i ↦ f₁ (blockPerm τ (Fin.castAdd 2 i))) *
          β.1 p.2 (fun j ↦ f₂ (blockPerm τ (Fin.natAdd 2 j)))) =
        α.1 p.1 ![a₀, a₁] * β.1 p.2 ![b₀, b₁] := by
    have hsign : Equiv.Perm.sign (blockPerm τ) = Equiv.Perm.sign τ.1 * Equiv.Perm.sign τ.2 := by
      simp [blockPerm, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr]
    have hleft : (fun i ↦ f₁ (blockPerm τ (Fin.castAdd 2 i))) = (![a₀, a₁] : Fin 2 → _) ∘ ⇑τ.1 := by
      funext i
      have hc : blockPerm τ (Fin.castAdd 2 i) = Fin.castAdd 2 (τ.1 i) := by
        dsimp only [blockPerm, Equiv.permCongr_apply]
        rw [← finSumFinEquiv_apply_left, Equiv.symm_apply_apply, Equiv.Perm.sumCongr_apply,
          Sum.map_inl, finSumFinEquiv_apply_left]
      rw [hc]
      dsimp only [Function.comp_apply]
      rcases hv : τ.1 i with ⟨val, hlt⟩
      interval_cases val <;> rfl
    have hright : (fun j ↦ f₂ (blockPerm τ (Fin.natAdd 2 j))) = (![b₀, b₁] : Fin 2 → _) ∘ ⇑τ.2 := by
      funext j
      have hc : blockPerm τ (Fin.natAdd 2 j) = Fin.natAdd 2 (τ.2 j) := by
        dsimp only [blockPerm, Equiv.permCongr_apply]
        rw [← finSumFinEquiv_apply_right, Equiv.symm_apply_apply, Equiv.Perm.sumCongr_apply,
          Sum.map_inr, finSumFinEquiv_apply_right]
      rw [hc]
      dsimp only [Function.comp_apply]
      rcases hv : τ.2 j with ⟨val, hlt⟩
      interval_cases val <;> rfl
    have hp1 : α.1 p.1 ((![a₀, a₁] : Fin 2 → _) ∘ ⇑τ.1) =
        Equiv.Perm.sign τ.1 • α.1 p.1 ![a₀, a₁] :=
      (α.1 p.1).toAlternatingMap.map_perm ![a₀, a₁] τ.1
    have hp2 : β.1 p.2 ((![b₀, b₁] : Fin 2 → _) ∘ ⇑τ.2) =
        Equiv.Perm.sign τ.2 • β.1 p.2 ![b₀, b₁] :=
      (β.1 p.2).toAlternatingMap.map_perm ![b₀, b₁] τ.2
    rw [hleft, hright, hp1, hp2, hsign]
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ.1) with hs1 | hs1 <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ.2) with hs2 | hs2 <;>
    simp [hs1, hs2]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]
  simp only [Nat.factorial, Nat.mul_one, nsmul_eq_mul, smul_eq_mul]
  ring

/-- `5 × 5` alternating volume identity reducing `S4VolumeForm` along `s4PlaneEmbed` to
`ρ * S2VolumeForm` via column elimination. -/
theorem volumeForm5_s4PlaneEmbed_identity
    (w₀ w₁ ρ : ℝ) (hρ_ne : ρ ≠ 0) (hρ_sq : ρ ^ 2 = 1 - (w₀ ^ 2 + w₁ ^ 2))
    (z u₀ u₁ : EuclideanSpace ℝ (Fin 3)) :
    (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis.orientation.volumeForm
      ![vec5 w₀ w₁ (ρ * z 0) (ρ * z 1) (ρ * z 2),
        vec5 1 0 (-(w₀ / ρ) * z 0) (-(w₀ / ρ) * z 1) (-(w₀ / ρ) * z 2),
        vec5 0 1 (-(w₁ / ρ) * z 0) (-(w₁ / ρ) * z 1) (-(w₁ / ρ) * z 2),
        vec5 0 0 (ρ * u₀ 0) (ρ * u₀ 1) (ρ * u₀ 2),
        vec5 0 0 (ρ * u₁ 0) (ρ * u₁ 1) (ρ * u₁ 2)] =
      ρ * (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.volumeForm ![z, u₀, u₁] := by
  let ω₅ := (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis.orientation.volumeForm
  let V₁ := vec5 1 0 (-(w₀ / ρ) * z 0) (-(w₀ / ρ) * z 1) (-(w₀ / ρ) * z 2)
  let V₂ := vec5 0 1 (-(w₁ / ρ) * z 0) (-(w₁ / ρ) * z 1) (-(w₁ / ρ) * z 2)
  let V₃ := vec5 0 0 (ρ * u₀ 0) (ρ * u₀ 1) (ρ * u₀ 2)
  let V₄ := vec5 0 0 (ρ * u₁ 0) (ρ * u₁ 1) (ρ * u₁ 2)
  let Z₅ := vec5 0 0 (z 0) (z 1) (z 2)
  let U₀₅ := vec5 0 0 (u₀ 0) (u₀ 1) (u₀ 2)
  let U₁₅ := vec5 0 0 (u₁ 0) (u₁ 1) (u₁ 2)
  let W₀ := ρ⁻¹ • Z₅
  let e₀ := vec5 1 0 0 0 0
  let e₁ := vec5 0 1 0 0 0
  have hV0_decomp :
      vec5 w₀ w₁ (ρ * z 0) (ρ * z 1) (ρ * z 2) = W₀ + w₀ • V₁ + w₁ • V₂ := by
    refine ext_vec5 ?_ ?_ ?_ ?_ ?_
    · simp [W₀, Z₅, V₁, V₂]
    · simp [W₀, Z₅, V₁, V₂]
    · simp only [W₀, Z₅, V₁, V₂, vec5_two, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp [hρ_ne]
      linear_combination (z 0) * hρ_sq
    · simp only [W₀, Z₅, V₁, V₂, vec5_three, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp [hρ_ne]
      linear_combination (z 1) * hρ_sq
    · simp only [W₀, Z₅, V₁, V₂, vec5_four, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp [hρ_ne]
      linear_combination (z 2) * hρ_sq
  have hV1_decomp : V₁ = e₀ - w₀ • W₀ := by
    refine ext_vec5 ?_ ?_ ?_ ?_ ?_ <;>
    · simp [V₁, e₀, W₀, Z₅, div_eq_mul_inv, mul_assoc]
  have hV2_decomp : V₂ = e₁ - w₁ • W₀ := by
    refine ext_vec5 ?_ ?_ ?_ ?_ ?_ <;>
    · simp [V₂, e₁, W₀, Z₅, div_eq_mul_inv, mul_assoc]
  -- Step 1: eliminate `w₀ • V₁ + w₁ • V₂` from slot 0
  have hstep1 : ω₅ ![vec5 w₀ w₁ (ρ * z 0) (ρ * z 1) (ρ * z 2), V₁, V₂, V₃, V₄] =
      ω₅ ![W₀, V₁, V₂, V₃, V₄] := by
    let F0 : Fin 5 → EuclideanSpace ℝ (Fin 5) := ![W₀, V₁, V₂, V₃, V₄]
    have hrew : (![vec5 w₀ w₁ (ρ * z 0) (ρ * z 1) (ρ * z 2), V₁, V₂, V₃, V₄] : Fin 5 → _) =
        Function.update F0 0 ((W₀ + w₀ • V₁) + w₁ • V₂) := by
      ext i; fin_cases i <;> simp [F0, hV0_decomp]
    rw [hrew, ω₅.map_update_add F0 0 (W₀ + w₀ • V₁) (w₁ • V₂),
      ω₅.map_update_smul F0 0 w₁ V₂,
      ω₅.map_eq_zero_of_eq _ (by simp [F0] : Function.update F0 0 V₂ 0 = Function.update F0 0 V₂ 2)
        (by decide),
      smul_zero, add_zero, ω₅.map_update_add F0 0 W₀ (w₀ • V₁),
      ω₅.map_update_smul F0 0 w₀ V₁,
      ω₅.map_eq_zero_of_eq _ (by simp [F0] : Function.update F0 0 V₁ 0 = Function.update F0 0 V₁ 1)
        (by decide),
      smul_zero, add_zero]
    congr 1; ext i; fin_cases i <;> rfl
  -- Step 2: eliminate `- w₀ • W₀` from slot 1 and `- w₁ • W₀` from slot 2
  have hstep2 : ω₅ ![W₀, V₁, V₂, V₃, V₄] = ω₅ ![W₀, e₀, e₁, V₃, V₄] := by
    let F1 : Fin 5 → EuclideanSpace ℝ (Fin 5) := ![W₀, e₀, V₂, V₃, V₄]
    have hrew1 : (![W₀, V₁, V₂, V₃, V₄] : Fin 5 → _) = Function.update F1 1 (e₀ - w₀ • W₀) := by
      ext i; fin_cases i <;> simp [F1, hV1_decomp]
    rw [hrew1, ω₅.map_update_sub, ω₅.map_update_smul,
      ω₅.map_eq_zero_of_eq _ (by simp [F1] : Function.update F1 1 W₀ 0 = Function.update F1 1 W₀ 1)
        (by decide),
      smul_zero, sub_zero]
    let F2 : Fin 5 → EuclideanSpace ℝ (Fin 5) := ![W₀, e₀, e₁, V₃, V₄]
    have hrew2 : Function.update F1 1 e₀ = Function.update F2 2 (e₁ - w₁ • W₀) := by
      ext i; fin_cases i <;> simp [F1, F2, hV2_decomp]
    rw [hrew2, ω₅.map_update_sub, ω₅.map_update_smul,
      ω₅.map_eq_zero_of_eq _ (by simp [F2] : Function.update F2 2 W₀ 0 = Function.update F2 2 W₀ 2)
        (by decide),
      smul_zero, sub_zero]
    congr 1; ext i; fin_cases i <;> rfl
  -- Step 3: two swaps move `W₀` from slot 0 to slot 2 with sign `(-1)^2 = +1`
  have hstep3 : ω₅ ![W₀, e₀, e₁, V₃, V₄] = ω₅ ![e₀, e₁, W₀, V₃, V₄] := by
    have hs01 := ω₅.map_swap ![e₀, W₀, e₁, V₃, V₄] (by decide : (0 : Fin 5) ≠ 1)
    have hs12 := ω₅.map_swap ![e₀, e₁, W₀, V₃, V₄] (by decide : (1 : Fin 5) ≠ 2)
    have heq01 : (![e₀, W₀, e₁, V₃, V₄] : Fin 5 → _) ∘ Equiv.swap (0 : Fin 5) 1 =
        ![W₀, e₀, e₁, V₃, V₄] := by
      ext i; fin_cases i <;> rfl
    have heq12 : (![e₀, e₁, W₀, V₃, V₄] : Fin 5 → _) ∘ Equiv.swap (1 : Fin 5) 2 =
        ![e₀, W₀, e₁, V₃, V₄] := by
      ext i; fin_cases i <;> rfl
    rw [heq01] at hs01
    rw [heq12] at hs12
    rw [hs01, hs12, neg_neg]
  -- Step 4: factor `ρ⁻¹`, `ρ`, `ρ` from slots 2, 3, 4
  have hstep4 : ω₅ ![e₀, e₁, W₀, V₃, V₄] = ρ * ω₅ ![e₀, e₁, Z₅, U₀₅, U₁₅] := by
    have hV3 : V₃ = ρ • U₀₅ := by refine ext_vec5 ?_ ?_ ?_ ?_ ?_ <;> simp [V₃, U₀₅]
    have hV4 : V₄ = ρ • U₁₅ := by refine ext_vec5 ?_ ?_ ?_ ?_ ?_ <;> simp [V₄, U₁₅]
    let G2 : Fin 5 → EuclideanSpace ℝ (Fin 5) := ![e₀, e₁, Z₅, ρ • U₀₅, ρ • U₁₅]
    let G3 : Fin 5 → EuclideanSpace ℝ (Fin 5) := ![e₀, e₁, Z₅, U₀₅, ρ • U₁₅]
    let G4 : Fin 5 → EuclideanSpace ℝ (Fin 5) := ![e₀, e₁, Z₅, U₀₅, U₁₅]
    have hr2 : (![e₀, e₁, W₀, V₃, V₄] : Fin 5 → _) = Function.update G2 2 (ρ⁻¹ • Z₅) := by
      ext i; fin_cases i <;> simp [G2, W₀, hV3, hV4]
    have hr3 : Function.update G2 2 Z₅ = Function.update G3 3 (ρ • U₀₅) := by
      ext i; fin_cases i <;> rfl
    have hr4 : Function.update G3 3 U₀₅ = Function.update G4 4 (ρ • U₁₅) := by
      ext i; fin_cases i <;> rfl
    have hr5 : Function.update G4 4 U₁₅ = G4 := by
      ext i; fin_cases i <;> rfl
    rw [hr2, ω₅.map_update_smul, hr3, ω₅.map_update_smul, hr4, ω₅.map_update_smul, hr5]
    simp only [G4, smul_eq_mul]
    field_simp [hρ_ne]
  -- Step 5: block-diagonal `5 × 5` determinant equals `3 × 3` determinant
  have hstep5 : ω₅ ![e₀, e₁, Z₅, U₀₅, U₁₅] =
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.volumeForm ![z, u₀, u₁] := by
    change (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis.orientation.volumeForm
        ![e₀, e₁, Z₅, U₀₅, U₁₅] = _
    rw [volumeForm_basisFun_eq_det, volumeForm_basisFun_eq_det]
    let M₅ : Matrix (Fin 5) (Fin 5) ℝ :=
      Matrix.of fun i j : Fin 5 ↦ (![e₀, e₁, Z₅, U₀₅, U₁₅] j) i
    let M₄ : Matrix (Fin 4) (Fin 4) ℝ := M₅.submatrix Fin.succ Fin.succ
    let M₃ : Matrix (Fin 3) (Fin 3) ℝ :=
      Matrix.of fun i j : Fin 3 ↦ (![z, u₀, u₁] j) i
    change M₅.det = M₃.det
    have hm5 : M₅.det = M₄.det := by
      rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
      have h0 : M₅ 0 0 = 1 := rfl
      have htail : ∀ k : Fin 4,
          (-1 : ℝ) ^ (k.succ : ℕ) * M₅ 0 k.succ *
            (M₅.submatrix Fin.succ k.succ.succAbove).det = 0 := by
        intro k
        have hk : M₅ 0 k.succ = 0 := by fin_cases k <;> rfl
        rw [hk, mul_zero, zero_mul]
      rw [Finset.sum_eq_zero fun k _ ↦ htail k, add_zero, Fin.val_zero, pow_zero, h0,
        one_mul, one_mul, Fin.succAbove_zero]
    have hm4 : M₄.det = (M₄.submatrix Fin.succ Fin.succ).det := by
      rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
      have h0 : M₄ 0 0 = 1 := rfl
      have htail : ∀ k : Fin 3,
          (-1 : ℝ) ^ (k.succ : ℕ) * M₄ 0 k.succ *
            (M₄.submatrix Fin.succ k.succ.succAbove).det = 0 := by
        intro k
        have hk : M₄ 0 k.succ = 0 := by fin_cases k <;> rfl
        rw [hk, mul_zero, zero_mul]
      rw [Finset.sum_eq_zero fun k _ ↦ htail k, add_zero, Fin.val_zero, pow_zero, h0,
        one_mul, one_mul, Fin.succAbove_zero]
    have hm3 : M₄.submatrix Fin.succ Fin.succ = M₃ := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [hm5, hm4, hm3]
  exact hstep1.trans (hstep2.trans (hstep3.trans (hstep4.trans (congrArg (ρ * ·) hstep5))))

/-- Partial Fréchet derivative of `y ↦ s4PlaneEmbedRaw y z.1` at `w.1` for `w : s4PlaneDisk`. -/
theorem differentiableAt_and_fderiv_s4PlaneEmbedRaw_fst (w : s4PlaneDisk) (z : Sphere2)
    (u : EuclideanPlane) :
    let ρ := Real.sqrt (1 - (w.1 0 ^ 2 + w.1 1 ^ 2))
    DifferentiableAt ℝ (fun y : EuclideanPlane ↦ s4PlaneEmbedRaw y z.1) w.1 ∧
      fderiv ℝ (fun y : EuclideanPlane ↦ s4PlaneEmbedRaw y z.1) w.1 u =
        vec5 (u 0) (u 1)
          (-((w.1 0 * u 0 + w.1 1 * u 1) / ρ) * z.1 0)
          (-((w.1 0 * u 0 + w.1 1 * u 1) / ρ) * z.1 1)
          (-((w.1 0 * u 0 + w.1 1 * u 1) / ρ) * z.1 2) := by
  intro ρ
  have hpos := one_sub_norm_sq_pos_of_mem_s4PlaneDisk w
  have hρ_ne : ρ ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hy (i : Fin 2) : HasFDerivAt (fun y : EuclideanPlane ↦ y i) (euclidProj i) w.1 :=
    (euclidProj i).hasFDerivAt
  have hsq (i : Fin 2) : HasFDerivAt (fun y : EuclideanPlane ↦ y i ^ 2)
      ((2 * w.1 i) • euclidProj i) w.1 := by
    convert (hy i).pow 2 using 1
    ext a
    simp only [smul_apply, euclidProj, EuclideanSpace.proj, nsmul_eq_mul, Nat.cast_ofNat,
      smul_eq_mul]
    ring
  have eq_fderiv {f : EuclideanPlane → ℝ} {L₁ L₂ : EuclideanPlane →L[ℝ] ℝ}
      (hf : HasFDerivAt f L₁ w.1) (hL : ∀ a, L₁ a = L₂ a) : HasFDerivAt f L₂ w.1 :=
    ContinuousLinearMap.ext hL ▸ hf
  have hrad : HasFDerivAt (fun y : EuclideanPlane ↦ 1 - (y 0 ^ 2 + y 1 ^ 2))
      (-((2 * w.1 0) • euclidProj 0 + (2 * w.1 1) • euclidProj 1)) w.1 :=
    eq_fderiv ((hasFDerivAt_const (1 : ℝ) w.1).sub ((hsq 0).add (hsq 1))) fun a ↦ by simp
  have hsqrt : HasFDerivAt (fun y : EuclideanPlane ↦ Real.sqrt (1 - (y 0 ^ 2 + y 1 ^ 2)))
      ((2 * ρ)⁻¹ • (-((2 * w.1 0) • euclidProj 0 + (2 * w.1 1) • euclidProj 1))) w.1 :=
    eq_fderiv ((Real.hasDerivAt_sqrt hpos.ne').comp_hasFDerivAt w.1 hrad) fun a ↦ by
      simp only [smul_apply, neg_apply, add_apply, smul_eq_mul, ρ]
      ring
  let dρ := (2 * ρ)⁻¹ • (-((2 * w.1 0) • euclidProj (0 : Fin 2) +
    (2 * w.1 1) • euclidProj (1 : Fin 2)))
  have hzk (k : Fin 3) :
      HasFDerivAt (fun y : EuclideanPlane ↦ Real.sqrt (1 - (y 0 ^ 2 + y 1 ^ 2)) * z.1 k)
        (z.1 k • dρ) w.1 :=
    eq_fderiv (hsqrt.mul_const (z.1 k)) fun a ↦ by
      simp only [dρ, smul_apply, neg_apply, add_apply, smul_eq_mul]
  have hall : HasFDerivAt (fun y : EuclideanPlane ↦ s4PlaneEmbedRaw y z.1) _ w.1 :=
    hasFDerivAt_vec5 (hy 0) (hy 1) (hzk 0) (hzk 1) (hzk 2)
  refine ⟨hall.differentiableAt, ?_⟩
  rw [hall.fderiv, clmVec5_apply]
  refine ext_vec5 ?_ ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · simp only [dρ, smul_apply, neg_apply, add_apply, euclidProj_apply, smul_eq_mul, vec5_two]
    field_simp [hρ_ne]
  · simp only [dρ, smul_apply, neg_apply, add_apply, euclidProj_apply, smul_eq_mul, vec5_three]
    field_simp [hρ_ne]
  · simp only [dρ, smul_apply, neg_apply, add_apply, euclidProj_apply, smul_eq_mul, vec5_four]
    field_simp [hρ_ne]

/-- Partial manifold derivative of `q ↦ s4PlaneEmbedRaw w.1 q.1` with respect to `q : Sphere2`. -/
theorem mvfderiv_s4PlaneEmbedRaw_snd (w : s4PlaneDisk) (z : Sphere2) (v : TangentSpace (𝓡 2) z) :
    let ρ := Real.sqrt (1 - (w.1 0 ^ 2 + w.1 1 ^ 2))
    mvfderiv (𝓡 2) (fun q : Sphere2 ↦ s4PlaneEmbedRaw w.1 q.1) z v =
      vec5 0 0
        (ρ * (mvfderiv (𝓡 2) (Subtype.val : Sphere2 → EuclideanSpace ℝ (Fin 3)) z v) 0)
        (ρ * (mvfderiv (𝓡 2) (Subtype.val : Sphere2 → EuclideanSpace ℝ (Fin 3)) z v) 1)
        (ρ * (mvfderiv (𝓡 2) (Subtype.val : Sphere2 → EuclideanSpace ℝ (Fin 3)) z v) 2) := by
  intro ρ
  let Lz : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 5) :=
    clmVec5 0 0 (ρ • euclidProj 0) (ρ • euclidProj 1) (ρ • euclidProj 2)
  have hLz_apply (a : EuclideanSpace ℝ (Fin 3)) :
      Lz a = vec5 0 0 (ρ * a 0) (ρ * a 1) (ρ * a 2) := by
    dsimp only [Lz]
    rw [clmVec5_apply]
    refine ext_vec5 ?_ ?_ ?_ ?_ ?_ <;>
      simp only [zero_apply, smul_apply, euclidProj_apply, smul_eq_mul,
        vec5_zero, vec5_one, vec5_two, vec5_three, vec5_four]
  have hlin : (fun q : Sphere2 ↦ s4PlaneEmbedRaw w.1 q.1) =
      fun q : Sphere2 ↦
        (⇑Lz ∘ (Subtype.val : Sphere2 → EuclideanSpace ℝ (Fin 3))) q +
          vec5 (w.1 0) (w.1 1) 0 0 0 := by
    funext q
    dsimp only [Function.comp_apply]
    rw [hLz_apply]
    dsimp only [s4PlaneEmbedRaw, ρ]
    refine ext_vec5 ?_ ?_ ?_ ?_ ?_ <;>
      simp only [PiLp.add_apply, vec5_zero, vec5_one, vec5_two, vec5_three, vec5_four,
        add_zero, zero_add]
  rw [hlin, TauCeti.mvfderiv_add_const
      (⇑Lz ∘ (Subtype.val : Sphere2 → EuclideanSpace ℝ (Fin 3)))
      (vec5 (w.1 0) (w.1 1) 0 0 0) z,
    Lz.mvfderiv_comp_apply ((contMDiff_coe_sphere (m := ∞) z).mdifferentiableAt (by simp)) v,
    hLz_apply]

private theorem fin_cons_five_eq {α : Type*} (x₀ x₁ x₂ x₃ x₄ : α) (f : Fin 4 → α)
    (h0 : f 0 = x₁) (h1 : f 1 = x₂) (h2 : f 2 = x₃) (h3 : f 3 = x₄) :
    Fin.cons x₀ f = ![x₀, x₁, x₂, x₃, x₄] := by
  funext i
  fin_cases i
  · rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

private theorem fin_cons_three_eq {α : Type*} (x₀ x₁ x₂ : α) (f : Fin 2 → α)
    (h0 : f 0 = x₁) (h1 : f 1 = x₂) :
    ![x₀, x₁, x₂] = Fin.cons x₀ f := by
  funext i
  fin_cases i
  · rfl
  · exact h0.symm
  · exact h1.symm

private noncomputable def s4PlaneProdBasis (w : s4PlaneDisk) (z : Sphere2) :
    Module.Basis (Fin 4) ℝ (TangentSpace ((𝓡 2).prod (𝓡 2)) (w, z)) :=
  let bW : Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) w) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  let bZ : Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  let eProd := TauCeti.Manifold.tangentSpaceProdEquiv (I := 𝓡 2) (J := 𝓡 2) (w, z)
  ((bW.prod bZ).reindex finSumFinEquiv).map eProd.symm.toLinearEquiv

private theorem s4PlaneProdBasis_eq (w : s4PlaneDisk) (z : Sphere2) :
    let bW : Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) w) :=
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    let bZ : Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z) :=
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    let eProd := TauCeti.Manifold.tangentSpaceProdEquiv (I := 𝓡 2) (J := 𝓡 2) (w, z)
    (⇑(s4PlaneProdBasis w z) : Fin 4 → _) =
      ![eProd.symm (bW 0, 0), eProd.symm (bW 1, 0),
        eProd.symm (0, bZ 0), eProd.symm (0, bZ 1)] ∧
      s4PlaneProdBasis w z 0 = eProd.symm (bW 0, 0) ∧
      s4PlaneProdBasis w z 1 = eProd.symm (bW 1, 0) ∧
      s4PlaneProdBasis w z 2 = eProd.symm (0, bZ 0) ∧
      s4PlaneProdBasis w z 3 = eProd.symm (0, bZ 1) := by
  intro bW bZ eProd
  have hbProd_apply (i : Fin 4) :
      s4PlaneProdBasis w z i = eProd.symm ((bW.prod bZ) (finSumFinEquiv.symm i)) := by
    simp [s4PlaneProdBasis, bW, bZ, eProd, Module.Basis.map_apply, Module.Basis.reindex_apply]
  have hb0 : s4PlaneProdBasis w z 0 = eProd.symm (bW 0, 0) := by
    have hs : finSumFinEquiv.symm (0 : Fin (2 + 2)) = Sum.inl 0 :=
      finSumFinEquiv.symm_apply_eq.mpr rfl
    rw [hbProd_apply 0, hs]
    exact congrArg eProd.symm
      (Prod.ext (Module.Basis.prod_apply_inl_fst bW bZ 0)
        (Module.Basis.prod_apply_inl_snd bW bZ 0))
  have hb1 : s4PlaneProdBasis w z 1 = eProd.symm (bW 1, 0) := by
    have hs : finSumFinEquiv.symm (1 : Fin (2 + 2)) = Sum.inl 1 :=
      finSumFinEquiv.symm_apply_eq.mpr rfl
    rw [hbProd_apply 1, hs]
    exact congrArg eProd.symm
      (Prod.ext (Module.Basis.prod_apply_inl_fst bW bZ 1)
        (Module.Basis.prod_apply_inl_snd bW bZ 1))
  have hb2 : s4PlaneProdBasis w z 2 = eProd.symm (0, bZ 0) := by
    have hs : finSumFinEquiv.symm (2 : Fin (2 + 2)) = Sum.inr 0 :=
      finSumFinEquiv.symm_apply_eq.mpr rfl
    rw [hbProd_apply 2, hs]
    exact congrArg eProd.symm
      (Prod.ext (Module.Basis.prod_apply_inr_fst bW bZ 0)
        (Module.Basis.prod_apply_inr_snd bW bZ 0))
  have hb3 : s4PlaneProdBasis w z 3 = eProd.symm (0, bZ 1) := by
    have hs : finSumFinEquiv.symm (3 : Fin (2 + 2)) = Sum.inr 1 :=
      finSumFinEquiv.symm_apply_eq.mpr rfl
    rw [hbProd_apply 3, hs]
    exact congrArg eProd.symm
      (Prod.ext (Module.Basis.prod_apply_inr_fst bW bZ 1)
        (Module.Basis.prod_apply_inr_snd bW bZ 1))
  refine ⟨?_, hb0, hb1, hb2, hb3⟩
  funext i
  fin_cases i
  · exact hb0
  · exact hb1
  · exact hb2
  · exact hb3

/-- Pullback of `S2VolumeForm` along `Prod.snd : s4PlaneDisk × Sphere2 → Sphere2`. -/
noncomputable def s4PlaneFiberForm :
    TauCeti.SmoothForm ((𝓡 2).prod (𝓡 2)) (s4PlaneDisk × Sphere2) ℝ 2 :=
  TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd S2VolumeForm

/-- Pullback of `planeAreaForm` along `Subtype.val ∘ Prod.fst : s4PlaneDisk × Sphere2 → ℝ²`. -/
noncomputable def s4PlaneAreaBaseForm :
    TauCeti.SmoothForm ((𝓡 2).prod (𝓡 2)) (s4PlaneDisk × Sphere2) ℝ 2 :=
  TauCeti.SmoothForm.mpullback (Subtype.val ∘ Prod.fst)
    (contMDiff_subtype_val.comp contMDiff_fst) planeAreaForm

/-- Pullback of `S2VolumeForm` along `southPoleStereoInv ∘ Subtype.val ∘ Prod.fst`. -/
noncomputable def s4PlaneStereoBaseForm :
    TauCeti.SmoothForm ((𝓡 2).prod (𝓡 2)) (s4PlaneDisk × Sphere2) ℝ 2 :=
  TauCeti.SmoothForm.mpullback (southPoleStereoInv ∘ Subtype.val ∘ Prod.fst)
    (contMDiff_southPoleStereoInv.comp (contMDiff_subtype_val.comp contMDiff_fst))
    S2VolumeForm

/-- Product 4-form `p_F^* S2VolumeForm ∧ p_B^* S2VolumeForm|_B` on `s4BaseRegion × Sphere2`. -/
noncomputable def s4TrivTargetForm :
    TauCeti.SmoothForm ((𝓡 2).prod (𝓡 2)) (s4BaseRegion × Sphere2) ℝ (2 + 2) :=
  TauCeti.SmoothForm.wedge
    (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd S2VolumeForm)
    (TauCeti.SmoothForm.mpullback (Subtype.val ∘ Prod.fst)
      (contMDiff_subtype_val.comp contMDiff_fst) S2VolumeForm)

/-- Restriction of `S4VolumeForm` to `s4PreimageOpen`. -/
noncomputable def s4PreimageVolumeForm :
    TauCeti.SmoothForm (𝓡 4) s4PreimageOpen ℝ 4 :=
  TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val S4VolumeForm

private theorem s4PlaneWedge_basis_eval (w : s4PlaneDisk) (z : Sphere2) :
    let bZ : Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z) :=
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    (TauCeti.SmoothForm.wedge s4PlaneFiberForm s4PlaneAreaBaseForm).1 (w, z)
        ⇑(s4PlaneProdBasis w z) =
      S2VolumeForm.1 z ![bZ 0, bZ 1] := by
  intro bZ
  let bW : Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) w) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  rw [s4PlaneFiberForm, s4PlaneAreaBaseForm,
    TauCeti.SmoothForm.wedge_comm_of_even (by decide : Even 2),
    ← TauCeti.SmoothForm.mpullback_mpullback Prod.fst Subtype.val contMDiff_fst
      contMDiff_subtype_val planeAreaForm,
    (s4PlaneProdBasis_eq w z).1]
  have hblock := wedge_mpullback_fst_snd_two_two
    (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val planeAreaForm)
    S2VolumeForm (w, z) (bW 0) (bW 1) (bZ 0) (bZ 1)
  rw [hblock, TauCeti.SmoothForm.coe_mpullback_subtype_val_apply]
  dsimp only
  have hplane_arg : (![bW 0, bW 1] : Fin 2 → TangentSpace (𝓡 2) w.1) =
      fun i ↦ (EuclideanSpace.basisFun (Fin 2) ℝ i : TangentSpace (𝓡 2) w.1) := by
    funext i; fin_cases i <;> rfl
  have hplane : planeAreaForm.1 w.1 (![bW 0, bW 1] : Fin 2 → TangentSpace (𝓡 2) w.1) = 1 :=
    (congrArg (planeAreaForm.1 w.1) hplane_arg).trans (planeAreaForm_apply_basisFun w.1)
  exact (congrArg (· * S2VolumeForm.1 z ![bZ 0, bZ 1]) hplane).trans (one_mul _)

private theorem s4PlaneEmbed_basis_eval (w : s4PlaneDisk) (z : Sphere2) :
    let bZ : Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z) :=
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    (TauCeti.SmoothForm.mpullback s4PlaneEmbed contMDiff_s4PlaneEmbed S4VolumeForm).1 (w, z)
        ⇑(s4PlaneProdBasis w z) =
      Real.sqrt (1 - (w.1 0 ^ 2 + w.1 1 ^ 2)) * S2VolumeForm.1 z ![bZ 0, bZ 1] := by
  intro bZ
  let ρ := Real.sqrt (1 - (w.1 0 ^ 2 + w.1 1 ^ 2))
  have hpos := one_sub_norm_sq_pos_of_mem_s4PlaneDisk w
  have hρ_ne : ρ ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hρ_sq : ρ ^ 2 = 1 - (w.1 0 ^ 2 + w.1 1 ^ 2) := Real.sq_sqrt hpos.le
  let bW : Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) w) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  let eProd := TauCeti.Manifold.tangentSpaceProdEquiv (I := 𝓡 2) (J := 𝓡 2) (w, z)
  obtain ⟨-, hbProd0, hbProd1, hbProd2, hbProd3⟩ := s4PlaneProdBasis_eq w z
  let F : s4PlaneDisk × Sphere2 → EuclideanSpace ℝ (Fin 5) :=
    fun pq ↦ s4PlaneEmbedRaw pq.1.1 pq.2.1
  have hF_smooth : ContMDiff ((𝓡 2).prod (𝓡 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 5)) ∞ F :=
    contMDiff_coe_sphere.comp contMDiff_s4PlaneEmbed
  have hd_embed (v : TangentSpace ((𝓡 2).prod (𝓡 2)) (w, z)) :
      mvfderiv (𝓡 4) (Subtype.val : Sphere4 → EuclideanSpace ℝ (Fin 5))
          (s4PlaneEmbed (w, z)) (mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 4) s4PlaneEmbed (w, z) v) =
        mvfderiv ((𝓡 2).prod (𝓡 2)) F (w, z) v := by
    rw [← mvfderiv_comp_apply (w, z)
      ((contMDiff_coe_sphere (m := ∞) _).mdifferentiableAt (by simp))
      ((contMDiff_s4PlaneEmbed (w, z)).mdifferentiableAt (by simp))]
    rfl
  have hd_pair (a : TangentSpace (𝓡 2) w) (b : TangentSpace (𝓡 2) z) :
      mvfderiv ((𝓡 2).prod (𝓡 2)) F (w, z) (eProd.symm (a, b)) =
        mvfderiv (𝓡 2) (fun y : s4PlaneDisk ↦ F (y, z)) w a +
          mvfderiv (𝓡 2) (fun q : Sphere2 ↦ F (w, q)) z b := by
    have h := ((hF_smooth (w, z)).mdifferentiableAt (by simp)).mvfderiv_prod_eq_add_apply
      (eProd.symm (a, b))
    have h1 : (eProd.symm (a, b)).1 = a :=
      congrArg Prod.fst (TauCeti.Manifold.tangentSpaceProdEquiv_symm_apply (w, z) (a, b))
    have h2 : (eProd.symm (a, b)).2 = b :=
      congrArg Prod.snd (TauCeti.Manifold.tangentSpaceProdEquiv_symm_apply (w, z) (a, b))
    exact h.trans (congrArg₂ (· + ·) (congrArg _ h1) (congrArg _ h2))
  have hd_w_eval (u : TangentSpace (𝓡 2) w) (uE : EuclideanPlane)
      (hu : (u : EuclideanPlane) = uE) :
      mvfderiv (𝓡 2) (fun y : s4PlaneDisk ↦ F (y, z)) w u =
        vec5 (uE 0) (uE 1)
          (-((w.1 0 * uE 0 + w.1 1 * uE 1) / ρ) * z.1 0)
          (-((w.1 0 * uE 0 + w.1 1 * uE 1) / ρ) * z.1 1)
          (-((w.1 0 * uE 0 + w.1 1 * uE 1) / ρ) * z.1 2) := by
    have hcomp : (fun y : s4PlaneDisk ↦ F (y, z)) =
        (fun y : EuclideanPlane ↦ s4PlaneEmbedRaw y z.1) ∘ (Subtype.val : s4PlaneDisk → _) := rfl
    have hsub : mvfderiv (𝓡 2) (Subtype.val : s4PlaneDisk → EuclideanPlane) w u = uE :=
      (TauCeti.Manifold.mvfderiv_subtype_val_apply w u).trans hu
    exact (congrFun (congrArg (fun g ↦ ⇑(mvfderiv (𝓡 2) g w)) hcomp) u).trans
      ((TauCeti.mvfderiv_comp_apply_of_differentiableAt
          (differentiableAt_and_fderiv_s4PlaneEmbedRaw_fst w z uE).1
          ((contMDiff_subtype_val (n := ∞) w).mdifferentiableAt (by simp)) u).trans
        ((congrArg (fderiv ℝ (fun y : EuclideanPlane ↦ s4PlaneEmbedRaw y z.1) w.1) hsub).trans
          (differentiableAt_and_fderiv_s4PlaneEmbedRaw_fst w z uE).2))
  let u₀ := mvfderiv (𝓡 2) (Subtype.val : Sphere2 → EuclideanSpace ℝ (Fin 3)) z (bZ 0)
  let u₁ := mvfderiv (𝓡 2) (Subtype.val : Sphere2 → EuclideanSpace ℝ (Fin 3)) z (bZ 1)
  rw [TauCeti.SmoothForm.mpullback_apply, S4VolumeForm, Orientation.sphereVolumeForm_apply]
  simp_rw [hd_embed]
  have hE0 : mvfderiv ((𝓡 2).prod (𝓡 2)) F (w, z) (s4PlaneProdBasis w z 0) =
      vec5 1 0 (-(w.1 0 / ρ) * z.1 0) (-(w.1 0 / ρ) * z.1 1) (-(w.1 0 / ρ) * z.1 2) := by
    rw [hbProd0, hd_pair (bW 0) 0, ContinuousLinearMap.map_zero, add_zero,
      hd_w_eval (bW 0) (vec2 1 0) basisFun2_zero_eq_vec2]
    refine ext_vec5 rfl rfl ?_ ?_ ?_ <;>
      simp only [vec2_zero, vec2_one, vec5_two, vec5_three, vec5_four, mul_one, mul_zero,
        add_zero]
  have hE1 : mvfderiv ((𝓡 2).prod (𝓡 2)) F (w, z) (s4PlaneProdBasis w z 1) =
      vec5 0 1 (-(w.1 1 / ρ) * z.1 0) (-(w.1 1 / ρ) * z.1 1) (-(w.1 1 / ρ) * z.1 2) := by
    rw [hbProd1, hd_pair (bW 1) 0, ContinuousLinearMap.map_zero, add_zero,
      hd_w_eval (bW 1) (vec2 0 1) basisFun2_one_eq_vec2]
    refine ext_vec5 rfl rfl ?_ ?_ ?_ <;>
      simp only [vec2_zero, vec2_one, vec5_two, vec5_three, vec5_four, mul_one, mul_zero,
        zero_add]
  have hV0 : mvfderiv ((𝓡 2).prod (𝓡 2)) F (w, z) (s4PlaneProdBasis w z 2) =
      vec5 0 0 (ρ * u₀ 0) (ρ * u₀ 1) (ρ * u₀ 2) := by
    rw [hbProd2, hd_pair 0 (bZ 0), ContinuousLinearMap.map_zero, zero_add]
    exact mvfderiv_s4PlaneEmbedRaw_snd w z (bZ 0)
  have hV1 : mvfderiv ((𝓡 2).prod (𝓡 2)) F (w, z) (s4PlaneProdBasis w z 3) =
      vec5 0 0 (ρ * u₁ 0) (ρ * u₁ 1) (ρ * u₁ 2) := by
    rw [hbProd3, hd_pair 0 (bZ 1), ContinuousLinearMap.map_zero, zero_add]
    exact mvfderiv_s4PlaneEmbedRaw_snd w z (bZ 1)
  have hcons := fin_cons_five_eq
    (vec5 (w.1 0) (w.1 1) (ρ * z.1 0) (ρ * z.1 1) (ρ * z.1 2))
    (vec5 1 0 (-(w.1 0 / ρ) * z.1 0) (-(w.1 0 / ρ) * z.1 1) (-(w.1 0 / ρ) * z.1 2))
    (vec5 0 1 (-(w.1 1 / ρ) * z.1 0) (-(w.1 1 / ρ) * z.1 1) (-(w.1 1 / ρ) * z.1 2))
    (vec5 0 0 (ρ * u₀ 0) (ρ * u₀ 1) (ρ * u₀ 2))
    (vec5 0 0 (ρ * u₁ 0) (ρ * u₁ 1) (ρ * u₁ 2))
    (fun i ↦ mvfderiv ((𝓡 2).prod (𝓡 2)) F (w, z) (s4PlaneProdBasis w z i))
    hE0 hE1 hV0 hV1
  have harg3 := fin_cons_three_eq z.1 u₀ u₁
    (fun i ↦ mvfderiv (𝓡 2) (Subtype.val : Sphere2 → _) z (![bZ 0, bZ 1] i)) rfl rfl
  change (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis.orientation.volumeForm
      (Fin.cons (vec5 (w.1 0) (w.1 1) (ρ * z.1 0) (ρ * z.1 1) (ρ * z.1 2))
        (fun i ↦ mvfderiv ((𝓡 2).prod (𝓡 2)) F (w, z) (s4PlaneProdBasis w z i))) = _
  rw [hcons, volumeForm5_s4PlaneEmbed_identity (w.1 0) (w.1 1) ρ hρ_ne hρ_sq z.1 u₀ u₁,
    S2VolumeForm, Orientation.sphereVolumeForm_apply, harg3]

/-- Exact pullback of `S4VolumeForm` along `s4PlaneEmbed : s4PlaneDisk × Sphere2 → Sphere4`:
`s4PlaneEmbed^* Ω_{S⁴} = √(1 - w₀² - w₁²) • (p_F^* σ_{S²} ∧ p_B^* planeAreaForm)`. -/
theorem mpullback_s4PlaneEmbed_s4VolumeForm (wz : s4PlaneDisk × Sphere2) :
    (TauCeti.SmoothForm.mpullback s4PlaneEmbed contMDiff_s4PlaneEmbed S4VolumeForm).1 wz =
      Real.sqrt (1 - (wz.1.1 0 ^ 2 + wz.1.1 1 ^ 2)) •
        (TauCeti.SmoothForm.wedge s4PlaneFiberForm s4PlaneAreaBaseForm).1 wz := by
  rcases wz with ⟨w, z⟩
  ext v
  rw [ContinuousAlternatingMap.apply_eq_det_mul _ (s4PlaneProdBasis w z) v,
    ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.apply_eq_det_mul _ (s4PlaneProdBasis w z) v,
    s4PlaneEmbed_basis_eval w z, s4PlaneWedge_basis_eval w z, smul_eq_mul, mul_left_comm]

private theorem wedge_apply_smul_right
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {k l : ℕ} (α : TauCeti.SmoothForm I M ℝ k) (β γ : TauCeti.SmoothForm I M ℝ l)
    (x : M) (c : ℝ) (hβ : β.1 x = c • γ.1 x) :
    (TauCeti.SmoothForm.wedge α β).1 x = c • (TauCeti.SmoothForm.wedge α γ).1 x := by
  ext v
  rw [TauCeti.SmoothForm.wedge_apply, ContinuousAlternatingMap.smul_apply,
    TauCeti.SmoothForm.wedge_apply, hβ]
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  let a : ℝ := ((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹
  change a * ∑ σ : Equiv.Perm (Fin (k + l)), _ = c * (a * ∑ σ : Equiv.Perm (Fin (k + l)), _)
  rw [← mul_assoc c a, mul_comm c a, mul_assoc a c, Finset.mul_sum (a := c)]
  congr 1
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [mul_smul_comm, mul_left_comm]

private theorem mpullback_congr_fun {E H M E' H' M' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
    [IsManifold I' 1 M'] {k : ℕ} {f g : M → M'}
    (hf : ContMDiff I I' ∞ f) (hg : ContMDiff I I' ∞ g) (hfg : f = g)
    (η : TauCeti.SmoothForm I' M' ℝ k) :
    TauCeti.SmoothForm.mpullback f hf η = TauCeti.SmoothForm.mpullback g hg η := by
  subst hfg
  rfl

private theorem mpullback_s4PlaneTrivialization_symm_s4VolumeForm :
    TauCeti.SmoothForm.mpullback s4PlaneTrivialization.symm
        s4PlaneTrivialization.symm.contMDiff s4PreimageVolumeForm =
      TauCeti.SmoothForm.mpullback s4PlaneEmbed contMDiff_s4PlaneEmbed S4VolumeForm := by
  unfold s4PreimageVolumeForm
  rw [TauCeti.SmoothForm.mpullback_mpullback]
  exact mpullback_congr_fun _ _ (funext fun ⟨_, _⟩ ↦ rfl) S4VolumeForm

private noncomputable def s4BaseProdDiffeomorph :
    (s4PlaneDisk × Sphere2) ≃ₘ⟮(𝓡 2).prod (𝓡 2), (𝓡 2).prod (𝓡 2)⟯ (s4BaseRegion × Sphere2) :=
  s4BaseDiskDiffeomorph.prodCongr (Diffeomorph.refl (𝓡 2) Sphere2 ∞)

private theorem mpullback_s4BaseProdDiffeomorph_fiber :
    TauCeti.SmoothForm.mpullback s4BaseProdDiffeomorph s4BaseProdDiffeomorph.contMDiff
        (TauCeti.SmoothForm.mpullback
          (Prod.snd : s4BaseRegion × Sphere2 → Sphere2)
          (contMDiff_snd (I := 𝓡 2) (J := 𝓡 2)) S2VolumeForm) =
      s4PlaneFiberForm := by
  rw [TauCeti.SmoothForm.mpullback_mpullback]
  exact mpullback_congr_fun _ _ (funext fun ⟨_, _⟩ ↦ rfl) S2VolumeForm

private theorem mpullback_s4BaseProdDiffeomorph_base :
    TauCeti.SmoothForm.mpullback s4BaseProdDiffeomorph s4BaseProdDiffeomorph.contMDiff
        (TauCeti.SmoothForm.mpullback
          (Subtype.val ∘ (Prod.fst : s4BaseRegion × Sphere2 → s4BaseRegion))
          (contMDiff_subtype_val.comp (contMDiff_fst (I := 𝓡 2) (J := 𝓡 2))) S2VolumeForm) =
      s4PlaneStereoBaseForm := by
  rw [TauCeti.SmoothForm.mpullback_mpullback]
  exact mpullback_congr_fun _ _ (funext fun ⟨_, _⟩ ↦ rfl) S2VolumeForm

private theorem mpullback_s4BaseProdDiffeomorph_target :
    TauCeti.SmoothForm.mpullback s4BaseProdDiffeomorph s4BaseProdDiffeomorph.contMDiff
        s4TrivTargetForm =
      TauCeti.SmoothForm.wedge s4PlaneFiberForm s4PlaneStereoBaseForm :=
  (TauCeti.SmoothForm.mpullback_wedge s4BaseProdDiffeomorph s4BaseProdDiffeomorph.contMDiff
      (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd S2VolumeForm)
      (TauCeti.SmoothForm.mpullback (Subtype.val ∘ Prod.fst)
        (contMDiff_subtype_val.comp contMDiff_fst) S2VolumeForm)).trans
    (congrArg₂
      (fun α β : TauCeti.SmoothForm ((𝓡 2).prod (𝓡 2)) (s4PlaneDisk × Sphere2) ℝ 2 ↦
        TauCeti.SmoothForm.wedge α β)
      mpullback_s4BaseProdDiffeomorph_fiber mpullback_s4BaseProdDiffeomorph_base)

private theorem mpullback_s4PlaneTrivialization_symm_wedge :
    TauCeti.SmoothForm.mpullback s4PlaneTrivialization.symm
        s4PlaneTrivialization.symm.contMDiff
        (TauCeti.SmoothForm.mpullback s4Trivialization s4Trivialization.contMDiff
          s4TrivTargetForm) =
      TauCeti.SmoothForm.wedge s4PlaneFiberForm s4PlaneStereoBaseForm := by
  have htriv_coe :
      (⇑s4Trivialization : s4PreimageOpen → _) =
        ⇑(s4PlaneTrivialization.trans s4BaseProdDiffeomorph) :=
    funext fun _ ↦ rfl
  exact (congrArg
      (TauCeti.SmoothForm.mpullback s4PlaneTrivialization.symm
        s4PlaneTrivialization.symm.contMDiff)
      ((mpullback_congr_fun s4Trivialization.contMDiff
          (s4PlaneTrivialization.trans s4BaseProdDiffeomorph).contMDiff htriv_coe
          s4TrivTargetForm).trans
        (TauCeti.SmoothForm.mpullback_trans s4PlaneTrivialization s4BaseProdDiffeomorph
          s4TrivTargetForm))).trans
    ((TauCeti.SmoothForm.mpullback_symm_mpullback s4PlaneTrivialization _).trans
      mpullback_s4BaseProdDiffeomorph_target)

private theorem s4PlaneStereoBaseForm_apply (w : s4PlaneDisk) (z : Sphere2) :
    s4PlaneStereoBaseForm.1 (w, z) =
      (16 / (w.1 0 ^ 2 + w.1 1 ^ 2 + 4) ^ 2) • s4PlaneAreaBaseForm.1 (w, z) := by
  unfold s4PlaneStereoBaseForm s4PlaneAreaBaseForm
  rw [← TauCeti.SmoothForm.mpullback_mpullback
    (Subtype.val ∘ (Prod.fst : s4PlaneDisk × Sphere2 → s4PlaneDisk)) southPoleStereoInv
    (contMDiff_subtype_val.comp (contMDiff_fst (I := 𝓡 2) (J := 𝓡 2)))
    contMDiff_southPoleStereoInv S2VolumeForm]
  have hw_eq :
      (Subtype.val ∘ (Prod.fst : s4PlaneDisk × Sphere2 → s4PlaneDisk)) (w, z) = w.1 := rfl
  ext v
  rw [TauCeti.SmoothForm.mpullback_apply, hw_eq, mpullback_southPoleStereoInv_s2VolumeForm w.1,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.smul_apply,
    TauCeti.SmoothForm.mpullback_apply, hw_eq]

private theorem s4Trivialization_pos_cooriented_symm (w : s4PlaneDisk) (z : Sphere2) :
    ∃ c : ℝ, 0 < c ∧
      (TauCeti.SmoothForm.mpullback s4Trivialization s4Trivialization.contMDiff
          s4TrivTargetForm).1 (s4PlaneTrivialization.symm (w, z)) =
        c • s4PreimageVolumeForm.1 (s4PlaneTrivialization.symm (w, z)) := by
  let ρ := Real.sqrt (1 - (w.1 0 ^ 2 + w.1 1 ^ 2))
  have hρ_pos : 0 < ρ := Real.sqrt_pos.mpr (one_sub_norm_sq_pos_of_mem_s4PlaneDisk w)
  let κ := 16 / (w.1 0 ^ 2 + w.1 1 ^ 2 + 4) ^ 2
  have hκ_pos : 0 < κ := by positivity
  refine ⟨κ / ρ, div_pos hκ_pos hρ_pos, ?_⟩
  refine (TauCeti.SmoothForm.mpullback_apply_eq_smul_iff s4PlaneTrivialization.symm
    (TauCeti.SmoothForm.mpullback s4Trivialization s4Trivialization.contMDiff s4TrivTargetForm)
    s4PreimageVolumeForm (κ / ρ) (w, z)).mp ?_
  rw [mpullback_s4PlaneTrivialization_symm_s4VolumeForm,
    mpullback_s4PlaneTrivialization_symm_wedge,
    mpullback_s4PlaneEmbed_s4VolumeForm (w, z), smul_smul, div_mul_cancel₀ _ hρ_pos.ne']
  exact wedge_apply_smul_right s4PlaneFiberForm s4PlaneStereoBaseForm s4PlaneAreaBaseForm
    (w, z) κ (s4PlaneStereoBaseForm_apply w z)

private theorem s4Trivialization_pos_cooriented_aux (u : s4PreimageOpen) :
    ∃ c : ℝ, 0 < c ∧
      (TauCeti.SmoothForm.mpullback s4Trivialization s4Trivialization.contMDiff
          s4TrivTargetForm).1 u =
        c • s4PreimageVolumeForm.1 u := by
  let wz := s4PlaneTrivialization u
  have hu : s4PlaneTrivialization.symm (wz.1, wz.2) = u :=
    s4PlaneTrivialization.symm_apply_apply u
  exact hu ▸ s4Trivialization_pos_cooriented_symm wz.1 wz.2

/-- **Strict Positive Co-Orientation of `s4Trivialization`**:
At every point `u : s4PreimageOpen` (`s4Fibration ⁻¹' s4BaseRegion`), the pullback along
`s4Trivialization` of the product 4-form `p_F^* S2VolumeForm ∧ p_B^* S2VolumeForm|_B` equals a
**strictly positive** scalar multiple `c • S4VolumeForm|_U` (`c > 0`). -/
theorem s4Trivialization_pos_cooriented (u : s4PreimageOpen) :
    ∃ c : ℝ, 0 < c ∧
      (TauCeti.SmoothForm.mpullback s4Trivialization s4Trivialization.contMDiff
          (TauCeti.SmoothForm.wedge
            (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd S2VolumeForm)
            (TauCeti.SmoothForm.mpullback (Subtype.val ∘ Prod.fst)
              (contMDiff_subtype_val.comp contMDiff_fst) S2VolumeForm))).1 u =
        c • (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val S4VolumeForm).1 u :=
  s4Trivialization_pos_cooriented_aux u

end S4CoOrientation

end S4TuringPoisson
