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

public import S4TuringPoisson.Fibration.PurelyWrinkled
public import S4TuringPoisson.Main
public import S4TuringPoisson.Extension.PoissonHamiltonian
public import TauCeti.Geometry.Manifold.RegularValue.ManifoldLevel
public import TauCeti.Geometry.Manifold.ModelTransport.Boundaryless
public import TauCeti.Geometry.Manifold.ModelTransport.Diffeomorph
public import TauCeti.Geometry.Manifold.PullbackGroupoid
import Mathlib.Geometry.Manifold.Immersion
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic

/-!
# Explicit Global Auroux–Donaldson–Katzarkov Broken Lefschetz Fibration on $S^4$ (Option A)

This file formalizes Option A (`LW4`) by constructing the explicit polynomial
Auroux–Donaldson–Katzarkov (ADK) broken Lefschetz fibration `s4ADKFibration : Sphere4 → Sphere2`
directly on the unit 4-sphere `Sphere4 ⊂ ℝ⁵` (with coordinates `(x₀, x₁, x₂, x₃, x₄)`):

1. **Global Map & $S^2$ vs. $T^2$ Fiber Witnesses (`Section 1` & `Section 2`)**:
   - Defines `s4ADKRaw x = (Z₀, Z₁, H)` where `Z = (x₀ + i x₁) * ((x₂² + x₃² - 1 / 2) + i x₄)`
     and `H = 1 / 4 - (x₀² + x₁²)`, proves `s4ADKRaw x.1 ≠ 0` on `Sphere4`, and normalizes to
     `s4ADKFibration : Sphere4 → Sphere2`.
   - Exhibits explicit smooth ($C^\infty$) regular-fiber diffeomorphisms
     `s4ADKNorthFiberDiffeomorph` from `Sphere2` onto
     `{x : Sphere4 // s4ADKFibration x = s2NorthPole}` and `s4ADKTorusFiberDiffeomorph` from
     `Torus2` onto the Clifford torus fiber `{x : Sphere4 // s4ADKFibration x = s2SouthPole}`.
   - Proves `SO(2)_{01}` rotational equivariance (`s4Rot01`, `s2Rot01`).

2. **Exact Equatorial Critical Circle (`Section 2`)**:
   - Proves `criticalPoints (𝓡 4) (𝓡 2) s4ADKFibration = {x : Sphere4 | x₂ = 0 ∧ x₃ = 0 ∧ x₄ = 0}`
     via explicit tangent-pair `3 × 3` determinant lower bounds across all cases.

3. **Indefinite Fold Local Normal Form (`Section 3`)** & **ADK Headline Theorems (`Section 4`)**:
   - Formalizes `IsIndefiniteFoldAt`, `s4BrokenLefschetzFibration` ($S^2$ chamber),
     `s4ADKTorusBrokenLefschetzFibration` ($T^2$ chamber), `s4PurelyWrinkledFibration`,
     and exports `exists_turingComplete_volumePreserving_poissonDiffeomorph_S4_ADK` and
     `exists_poisson_hamiltonian_realization_S4_ADK`.
-/

@[expose] public section

open Function MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff InnerProductSpace Manifold Topology

namespace S4TuringPoisson

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

/-! ## 1. Explicit Global ADK Map on $S^4 \subset \mathbb{R}^5$ & Fiber Witnesses -/

section GlobalADKMap

/-- Unnormalized polynomial ADK map `ℝ⁵ → ℝ³`:
`(x₀, x₁, x₂, x₃, x₄) ↦ (Z₀, Z₁, H)` with
`Z₀ + i Z₁ = (x₀ + i x₁)((x₂² + x₃² - 1/2) + i x₄)` and `H = 1/4 - (x₀² + x₁²)`. -/
noncomputable def s4ADKRaw (x : EuclideanSpace ℝ (Fin 5)) : EuclideanSpace ℝ (Fin 3) :=
  vec3
    (x 0 * (x 2 ^ 2 + x 3 ^ 2 - 1 / 2) - x 1 * x 4)
    (x 0 * x 4 + x 1 * (x 2 ^ 2 + x 3 ^ 2 - 1 / 2))
    (1 / 4 - (x 0 ^ 2 + x 1 ^ 2))

/-- Coordinate `0` of `s4ADKRaw x`. -/
@[simp]
theorem s4ADKRaw_zero (x : EuclideanSpace ℝ (Fin 5)) :
    s4ADKRaw x 0 = x 0 * (x 2 ^ 2 + x 3 ^ 2 - 1 / 2) - x 1 * x 4 := rfl

/-- Coordinate `1` of `s4ADKRaw x`. -/
@[simp]
theorem s4ADKRaw_one (x : EuclideanSpace ℝ (Fin 5)) :
    s4ADKRaw x 1 = x 0 * x 4 + x 1 * (x 2 ^ 2 + x 3 ^ 2 - 1 / 2) := rfl

/-- Coordinate `2` of `s4ADKRaw x`. -/
@[simp]
theorem s4ADKRaw_two (x : EuclideanSpace ℝ (Fin 5)) :
    s4ADKRaw x 2 = 1 / 4 - (x 0 ^ 2 + x 1 ^ 2) := rfl

/-- Squared Euclidean norm identity for `s4ADKRaw x`. -/
theorem norm_sq_s4ADKRaw (x : EuclideanSpace ℝ (Fin 5)) :
    ‖s4ADKRaw x‖ ^ 2 =
      (x 0 ^ 2 + x 1 ^ 2) * ((x 2 ^ 2 + x 3 ^ 2 - 1 / 2) ^ 2 + x 4 ^ 2) +
        (1 / 4 - (x 0 ^ 2 + x 1 ^ 2)) ^ 2 := by
  rw [norm_sq_vec3, s4ADKRaw_zero, s4ADKRaw_one, s4ADKRaw_two]
  ring

/-- Smoothness of the ambient ADK map `s4ADKRaw : ℝ⁵ → ℝ³`. -/
-- tier: T2
theorem contDiff_s4ADKRaw : ContDiff ℝ ∞ s4ADKRaw := by
  have hx (i : Fin 5) : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 5) ↦ x i) :=
    (euclidProj i).contDiff
  have hrho : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 5) ↦ x 2 ^ 2 + x 3 ^ 2 - 1 / 2) :=
    (((hx 2).pow 2).add ((hx 3).pow 2)).sub contDiff_const
  refine contDiff_vec3 ?_ ?_ ?_
  · exact ((hx 0).mul hrho).sub ((hx 1).mul (hx 4))
  · exact ((hx 0).mul (hx 4)).add ((hx 1).mul hrho)
  · exact contDiff_const.sub (((hx 0).pow 2).add ((hx 1).pow 2))

/-- On the unit sphere `Sphere4 ⊂ ℝ⁵`, `s4ADKRaw x.1` vanishes nowhere. -/
-- tier: T2
theorem s4ADKRaw_ne_zero_of_mem_sphere4 (x : Sphere4) : s4ADKRaw x.1 ≠ 0 := by
  intro h0
  have hx : x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2 + x.1 3 ^ 2 + x.1 4 ^ 2 = 1 := by
    rw [← norm_sq_vec5, mem_sphere_zero_iff_norm.mp x.2, one_pow]
  have hn : ‖s4ADKRaw x.1‖ ^ 2 = 0 := by simp [h0]
  rw [norm_sq_s4ADKRaw] at hn
  have h1 : 0 ≤ (x.1 0 ^ 2 + x.1 1 ^ 2) * ((x.1 2 ^ 2 + x.1 3 ^ 2 - 1 / 2) ^ 2 + x.1 4 ^ 2) := by
    positivity
  have h2 : 0 ≤ (1 / 4 - (x.1 0 ^ 2 + x.1 1 ^ 2)) ^ 2 := by positivity
  have hH : 1 / 4 - (x.1 0 ^ 2 + x.1 1 ^ 2) = 0 :=
    sq_eq_zero_iff.mp (le_antisymm (by linarith) h2)
  have hZ : (x.1 0 ^ 2 + x.1 1 ^ 2) * ((x.1 2 ^ 2 + x.1 3 ^ 2 - 1 / 2) ^ 2 + x.1 4 ^ 2) = 0 := by
    linarith
  have hr : x.1 0 ^ 2 + x.1 1 ^ 2 = 1 / 4 := by linarith
  rw [hr] at hZ
  have hZ0 : (x.1 2 ^ 2 + x.1 3 ^ 2 - 1 / 2) ^ 2 + x.1 4 ^ 2 = 0 := by linarith
  have hu : x.1 2 ^ 2 + x.1 3 ^ 2 = 1 / 2 := by nlinarith [sq_nonneg (x.1 4)]
  have hv : x.1 4 ^ 2 = 0 := by nlinarith [sq_nonneg (x.1 2 ^ 2 + x.1 3 ^ 2 - 1 / 2)]
  linarith

/-- Nonvanishing of `‖s4ADKRaw x.1‖` on `Sphere4`. -/
theorem norm_s4ADKRaw_pos (x : Sphere4) : 0 < ‖s4ADKRaw x.1‖ :=
  norm_pos_iff.mpr (s4ADKRaw_ne_zero_of_mem_sphere4 x)

/-- Explicit global Auroux–Donaldson–Katzarkov broken Lefschetz fibration `Sphere4 → Sphere2`
constructed by normalizing `s4ADKRaw`. -/
noncomputable def s4ADKFibration (x : Sphere4) : Sphere2 :=
  ⟨‖s4ADKRaw x.1‖⁻¹ • s4ADKRaw x.1, mem_sphere_zero_iff_norm.mpr (by
    rw [norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_s4ADKRaw_pos x).ne'])⟩

/-- Coordinate normalization formula for `s4ADKFibration x`. -/
theorem coe_s4ADKFibration (x : Sphere4) :
    (s4ADKFibration x : EuclideanSpace ℝ (Fin 3)) = ‖s4ADKRaw x.1‖⁻¹ • s4ADKRaw x.1 :=
  rfl

/-- Smoothness (`ContMDiff (𝓡 4) (𝓡 2) ∞`) of the global ADK map `s4ADKFibration`. -/
-- tier: T2
theorem contMDiff_s4ADKFibration : ContMDiff (𝓡 4) (𝓡 2) ∞ s4ADKFibration := by
  have hg :
      ContMDiff (𝓡 4) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
        (fun x : Sphere4 ↦ ‖s4ADKRaw x.1‖⁻¹ • s4ADKRaw x.1) := by
    intro x
    have hne : s4ADKRaw x.1 ≠ 0 := s4ADKRaw_ne_zero_of_mem_sphere4 x
    have hnormAt : ContDiffAt ℝ ∞ (fun w : EuclideanSpace ℝ (Fin 3) ↦ ‖w‖) (s4ADKRaw x.1) :=
      contDiffAt_norm (𝕜 := ℝ) hne
    have hinvAt :
        ContDiffAt ℝ ∞ (fun w : EuclideanSpace ℝ (Fin 3) ↦ ‖w‖⁻¹ • w) (s4ADKRaw x.1) :=
      (hnormAt.inv (norm_ne_zero_iff.mpr hne)).smul contDiffAt_id
    exact (hinvAt.comp x.1 contDiff_s4ADKRaw.contDiffAt).contMDiffAt.comp x
      (contMDiff_coe_sphere (m := ∞) x)
  exact hg.codRestrict_sphere _

/-! ### $S^2$ Fiber (North Pole), Clifford Torus $T^2$ Fiber (South Pole) & $SO(2)_{01}$ Action -/

/-- The preimage fiber of `s2NorthPole` under `s4ADKFibration` is
`{x : Sphere4 | x₀ = 0 ∧ x₁ = 0}`. -/
-- tier: T2
theorem s4ADKFibration_eq_northPole_iff (x : Sphere4) :
    s4ADKFibration x = s2NorthPole ↔ x.1 0 = 0 ∧ x.1 1 = 0 := by
  have hx : x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2 + x.1 3 ^ 2 + x.1 4 ^ 2 = 1 := by
    rw [← norm_sq_vec5, mem_sphere_zero_iff_norm.mp x.2, one_pow]
  have hnorm_pos : 0 < ‖s4ADKRaw x.1‖ := norm_s4ADKRaw_pos x
  constructor
  · intro h
    have h2 : ‖s4ADKRaw x.1‖⁻¹ * s4ADKRaw x.1 2 = 1 := by
      have hc := congrArg (fun z : Sphere2 ↦ z.1 2) h
      simpa [coe_s4ADKFibration, s2NorthPole] using hc
    have hraw2 : s4ADKRaw x.1 2 = ‖s4ADKRaw x.1‖ := by
      have hm := congrArg (‖s4ADKRaw x.1‖ * ·) h2
      simpa [mul_inv_cancel_left₀ hnorm_pos.ne'] using hm
    have hH_nn : 0 ≤ 1 / 4 - (x.1 0 ^ 2 + x.1 1 ^ 2) := by
      linarith [hnorm_pos, hraw2, s4ADKRaw_two x.1]
    have hsq : ‖s4ADKRaw x.1‖ ^ 2 = (1 / 4 - (x.1 0 ^ 2 + x.1 1 ^ 2)) ^ 2 := by
      rw [← hraw2, s4ADKRaw_two]
    rw [norm_sq_s4ADKRaw] at hsq
    have hZ : (x.1 0 ^ 2 + x.1 1 ^ 2) * ((x.1 2 ^ 2 + x.1 3 ^ 2 - 1 / 2) ^ 2 + x.1 4 ^ 2) = 0 := by
      linarith
    rcases mul_eq_zero.mp hZ with hr0 | hZ0
    · exact ⟨by nlinarith [sq_nonneg (x.1 0), sq_nonneg (x.1 1)],
        by nlinarith [sq_nonneg (x.1 0), sq_nonneg (x.1 1)]⟩
    · exfalso
      have hu : x.1 2 ^ 2 + x.1 3 ^ 2 = 1 / 2 := by nlinarith [sq_nonneg (x.1 4)]
      have hv : x.1 4 ^ 2 = 0 := by nlinarith [sq_nonneg (x.1 2 ^ 2 + x.1 3 ^ 2 - 1 / 2)]
      linarith
  · rintro ⟨hx0, hx1⟩
    apply Subtype.ext
    have hraw : s4ADKRaw x.1 = vec3 0 0 (1 / 4) := by
      refine ext_vec3 ?_ ?_ ?_ <;> simp [s4ADKRaw, hx0, hx1]
    have hnorm : ‖s4ADKRaw x.1‖ = 1 / 4 := by
      have hsq : ‖s4ADKRaw x.1‖ ^ 2 = (1 / 4) ^ 2 := by
        rw [hraw, norm_sq_vec3]; norm_num
      nlinarith [norm_nonneg (s4ADKRaw x.1)]
    refine ext_vec3 ?_ ?_ ?_ <;>
      simp [coe_s4ADKFibration, hraw, s2NorthPole]
    rw [show (vec3 0 0 4⁻¹ : EuclideanSpace ℝ (Fin 3)) = s4ADKRaw x.1 from by
      simpa using hraw.symm, hnorm]
    norm_num

/-- Explicit homeomorphism from `Sphere2` onto the regular fiber
`{x : Sphere4 // s4ADKFibration x = s2NorthPole}` (`S²` fiber witness for Gate 5.3). -/
-- tier: T2
noncomputable def s4ADKNorthFiberHomeomorph :
    Sphere2 ≃ₜ {x : Sphere4 // s4ADKFibration x = s2NorthPole} where
  toFun y := ⟨⟨vec5 0 0 (y.1 0) (y.1 1) (y.1 2), mem_sphere_zero_iff_norm.mpr (by
    have hy : y.1 0 ^ 2 + y.1 1 ^ 2 + y.1 2 ^ 2 = 1 := by
      rw [← norm_sq_vec3, mem_sphere_zero_iff_norm.mp y.2, one_pow]
    have hsq : ‖vec5 0 0 (y.1 0) (y.1 1) (y.1 2)‖ ^ 2 = 1 := by
      rw [norm_sq_vec5]
      simp only [vec5_zero, vec5_one, vec5_two, vec5_three, vec5_four]
      linarith
    nlinarith [norm_nonneg (vec5 0 0 (y.1 0) (y.1 1) (y.1 2))])⟩,
    (s4ADKFibration_eq_northPole_iff _).mpr ⟨rfl, rfl⟩⟩
  invFun x := ⟨vec3 (x.1.1 2) (x.1.1 3) (x.1.1 4), mem_sphere_zero_iff_norm.mpr (by
    obtain ⟨hx0, hx1⟩ := (s4ADKFibration_eq_northPole_iff x.1).mp x.2
    have hsq : ‖vec3 (x.1.1 2) (x.1.1 3) (x.1.1 4)‖ ^ 2 = 1 := by
      rw [norm_sq_vec3]
      have hx := mem_sphere_zero_iff_norm.mp x.1.2
      have hxsq : ‖x.1.1‖ ^ 2 = 1 := by rw [hx]; norm_num
      rw [norm_sq_vec5] at hxsq
      simp only [vec3_zero, vec3_one, vec3_two]
      nlinarith [hx0, hx1]
    nlinarith [norm_nonneg (vec3 (x.1.1 2) (x.1.1 3) (x.1.1 4))])⟩
  left_inv y := by
    apply Subtype.ext
    refine ext_vec3 rfl rfl rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    obtain ⟨hx0, hx1⟩ := (s4ADKFibration_eq_northPole_iff x.1).mp x.2
    refine ext_vec5 hx0.symm hx1.symm rfl rfl rfl
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact (contDiff_vec5 (n := ∞) (E := EuclideanSpace ℝ (Fin 3)) contDiff_const contDiff_const
      (euclidProj 0).contDiff (euclidProj 1).contDiff
      (euclidProj 2).contDiff).continuous.comp continuous_subtype_val
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact (contDiff_vec3 (n := ∞) (E := EuclideanSpace ℝ (Fin 5))
      (euclidProj 2).contDiff (euclidProj 3).contDiff
      (euclidProj 4).contDiff).continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)

/-- The preimage fiber of `s2SouthPole` under `s4ADKFibration` is the Clifford torus
`{x : Sphere4 | x₀² + x₁² = 1/2 ∧ x₂² + x₃² = 1/2 ∧ x₄ = 0}`. -/
-- tier: T2
theorem s4ADKFibration_eq_southPole_iff (x : Sphere4) :
    s4ADKFibration x = s2SouthPole ↔
      x.1 0 ^ 2 + x.1 1 ^ 2 = 1 / 2 ∧
        x.1 2 ^ 2 + x.1 3 ^ 2 = 1 / 2 ∧
        x.1 4 = 0 := by
  have hx : x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2 + x.1 3 ^ 2 + x.1 4 ^ 2 = 1 := by
    rw [← norm_sq_vec5, mem_sphere_zero_iff_norm.mp x.2, one_pow]
  have hnorm_pos : 0 < ‖s4ADKRaw x.1‖ := norm_s4ADKRaw_pos x
  constructor
  · intro h
    have h2 : ‖s4ADKRaw x.1‖⁻¹ * s4ADKRaw x.1 2 = -1 := by
      have hc := congrArg (fun z : Sphere2 ↦ z.1 2) h
      simpa [coe_s4ADKFibration, s2SouthPole] using hc
    have hraw2 : s4ADKRaw x.1 2 = -‖s4ADKRaw x.1‖ := by
      have hm := congrArg (‖s4ADKRaw x.1‖ * ·) h2
      simpa [mul_inv_cancel_left₀ hnorm_pos.ne'] using hm
    have hH_le : 1 / 4 - (x.1 0 ^ 2 + x.1 1 ^ 2) ≤ 0 := by
      have := hnorm_pos.le
      rw [← s4ADKRaw_two, hraw2]
      linarith
    have hsq : ‖s4ADKRaw x.1‖ ^ 2 = (1 / 4 - (x.1 0 ^ 2 + x.1 1 ^ 2)) ^ 2 := by
      rw [← neg_sq ‖s4ADKRaw x.1‖, ← hraw2, s4ADKRaw_two]
    rw [norm_sq_s4ADKRaw] at hsq
    have hZ : (x.1 0 ^ 2 + x.1 1 ^ 2) * ((x.1 2 ^ 2 + x.1 3 ^ 2 - 1 / 2) ^ 2 + x.1 4 ^ 2) = 0 := by
      linarith
    have hr_pos : 0 < x.1 0 ^ 2 + x.1 1 ^ 2 := by linarith
    have hZ0 : (x.1 2 ^ 2 + x.1 3 ^ 2 - 1 / 2) ^ 2 + x.1 4 ^ 2 = 0 :=
      (mul_eq_zero.mp hZ).resolve_left hr_pos.ne'
    have hu : x.1 2 ^ 2 + x.1 3 ^ 2 = 1 / 2 := by nlinarith [sq_nonneg (x.1 4)]
    have hv : x.1 4 = 0 := by
      have hv2 : x.1 4 ^ 2 = 0 := by nlinarith [sq_nonneg (x.1 2 ^ 2 + x.1 3 ^ 2 - 1 / 2)]
      exact sq_eq_zero_iff.mp hv2
    refine ⟨?_, hu, hv⟩
    linarith [sq_eq_zero_iff.mpr hv]
  · rintro ⟨hr, hu, hv⟩
    apply Subtype.ext
    have hraw : s4ADKRaw x.1 = vec3 0 0 (-1 / 4) := by
      refine ext_vec3 ?_ ?_ ?_ <;> simp only [s4ADKRaw_zero, s4ADKRaw_one, s4ADKRaw_two,
        vec3_zero, vec3_one, vec3_two]
      · rw [hu, hv]; ring
      · rw [hu, hv]; ring
      · rw [hr]; ring
    have hnorm : ‖s4ADKRaw x.1‖ = 1 / 4 := by
      have hsq : ‖s4ADKRaw x.1‖ ^ 2 = (1 / 4) ^ 2 := by
        rw [hraw, norm_sq_vec3]; norm_num
      nlinarith [norm_nonneg (s4ADKRaw x.1)]
    refine ext_vec3 ?_ ?_ ?_ <;>
      simp [coe_s4ADKFibration, hraw, s2SouthPole]
    rw [← hraw, hnorm]; norm_num

/-- Explicit homeomorphism from the 2-torus `S¹ × S¹` (`Metric.sphere 0 1 × Metric.sphere 0 1`)
onto the Clifford torus regular fiber `{x : Sphere4 // s4ADKFibration x = s2SouthPole}`
(`T²` fiber witness for Gate 5.3). -/
-- tier: T2
noncomputable def s4ADKTorusFiberHomeomorph :
    (Metric.sphere (0 : EuclideanPlane) 1 × Metric.sphere (0 : EuclideanPlane) 1) ≃ₜ
      {x : Sphere4 // s4ADKFibration x = s2SouthPole} where
  toFun uv :=
    let s : ℝ := (Real.sqrt 2)⁻¹
    let v5 := vec5 (s * uv.1.1 0) (s * uv.1.1 1) (s * uv.2.1 0) (s * uv.2.1 1) 0
    have hs2 : s ^ 2 = 1 / 2 := by
      dsimp [s]; rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
    have hu1 : uv.1.1 0 ^ 2 + uv.1.1 1 ^ 2 = 1 := by
      rw [← norm_sq_plane, mem_sphere_zero_iff_norm.mp uv.1.2, one_pow]
    have hu2 : uv.2.1 0 ^ 2 + uv.2.1 1 ^ 2 = 1 := by
      rw [← norm_sq_plane, mem_sphere_zero_iff_norm.mp uv.2.2, one_pow]
    ⟨⟨v5, mem_sphere_zero_iff_norm.mpr (by
      have hsq : ‖v5‖ ^ 2 = 1 := by
        rw [norm_sq_vec5]
        simp only [v5, vec5_zero, vec5_one, vec5_two, vec5_three, vec5_four]
        calc
          (s * uv.1.1 0) ^ 2 + (s * uv.1.1 1) ^ 2 +
              (s * uv.2.1 0) ^ 2 + (s * uv.2.1 1) ^ 2 + 0 ^ 2
            = s ^ 2 * (uv.1.1 0 ^ 2 + uv.1.1 1 ^ 2) +
                s ^ 2 * (uv.2.1 0 ^ 2 + uv.2.1 1 ^ 2) := by ring
          _ = 1 := by rw [hs2, hu1, hu2]; ring
      nlinarith [norm_nonneg v5])⟩,
      (s4ADKFibration_eq_southPole_iff _).mpr ⟨by
        simp only [v5, vec5_zero, vec5_one]
        calc
          (s * uv.1.1 0) ^ 2 + (s * uv.1.1 1) ^ 2 = s ^ 2 * (uv.1.1 0 ^ 2 + uv.1.1 1 ^ 2) := by
            ring
          _ = 1 / 2 := by rw [hs2, hu1]; ring, by
        simp only [v5, vec5_two, vec5_three]
        calc
          (s * uv.2.1 0) ^ 2 + (s * uv.2.1 1) ^ 2 = s ^ 2 * (uv.2.1 0 ^ 2 + uv.2.1 1 ^ 2) := by
            ring
          _ = 1 / 2 := by rw [hs2, hu2]; ring, rfl⟩⟩
  invFun x :=
    let r2 : ℝ := Real.sqrt 2
    have hr2 : r2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hfib := (s4ADKFibration_eq_southPole_iff x.1).mp x.2
    (⟨vec2 (r2 * x.1.1 0) (r2 * x.1.1 1), mem_sphere_zero_iff_norm.mpr (by
      have hsq : ‖vec2 (r2 * x.1.1 0) (r2 * x.1.1 1)‖ ^ 2 = 1 := by
        rw [norm_sq_plane]
        simp only [vec2_zero, vec2_one]
        calc
          (r2 * x.1.1 0) ^ 2 + (r2 * x.1.1 1) ^ 2 = r2 ^ 2 * (x.1.1 0 ^ 2 + x.1.1 1 ^ 2) := by
            ring
          _ = 1 := by rw [hr2, hfib.1]; norm_num
      nlinarith [norm_nonneg (vec2 (r2 * x.1.1 0) (r2 * x.1.1 1))])⟩,
    ⟨vec2 (r2 * x.1.1 2) (r2 * x.1.1 3), mem_sphere_zero_iff_norm.mpr (by
      have hsq : ‖vec2 (r2 * x.1.1 2) (r2 * x.1.1 3)‖ ^ 2 = 1 := by
        rw [norm_sq_plane]
        simp only [vec2_zero, vec2_one]
        calc
          (r2 * x.1.1 2) ^ 2 + (r2 * x.1.1 3) ^ 2 = r2 ^ 2 * (x.1.1 2 ^ 2 + x.1.1 3 ^ 2) := by
            ring
          _ = 1 := by rw [hr2, hfib.2.1]; norm_num
      nlinarith [norm_nonneg (vec2 (r2 * x.1.1 2) (r2 * x.1.1 3))])⟩)
  left_inv uv := by
    have hne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    apply Prod.ext <;> apply Subtype.ext <;> refine ext_vec2 ?_ ?_ <;>
      simp
  right_inv x := by
    have hne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    have hfib := (s4ADKFibration_eq_southPole_iff x.1).mp x.2
    apply Subtype.ext
    apply Subtype.ext
    refine ext_vec5 ?_ ?_ ?_ ?_ hfib.2.2.symm <;>
      simp
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    have h10 : Continuous (fun uv :
        Metric.sphere (0 : EuclideanPlane) 1 × Metric.sphere (0 : EuclideanPlane) 1 ↦
        (Real.sqrt 2)⁻¹ * uv.1.1 0) :=
      continuous_const.mul ((euclidProj 0).continuous.comp
        (continuous_subtype_val.comp continuous_fst))
    have h11 : Continuous (fun uv :
        Metric.sphere (0 : EuclideanPlane) 1 × Metric.sphere (0 : EuclideanPlane) 1 ↦
        (Real.sqrt 2)⁻¹ * uv.1.1 1) :=
      continuous_const.mul ((euclidProj 1).continuous.comp
        (continuous_subtype_val.comp continuous_fst))
    have h20 : Continuous (fun uv :
        Metric.sphere (0 : EuclideanPlane) 1 × Metric.sphere (0 : EuclideanPlane) 1 ↦
        (Real.sqrt 2)⁻¹ * uv.2.1 0) :=
      continuous_const.mul ((euclidProj 0).continuous.comp
        (continuous_subtype_val.comp continuous_snd))
    have h21 : Continuous (fun uv :
        Metric.sphere (0 : EuclideanPlane) 1 × Metric.sphere (0 : EuclideanPlane) 1 ↦
        (Real.sqrt 2)⁻¹ * uv.2.1 1) :=
      continuous_const.mul ((euclidProj 1).continuous.comp
        (continuous_subtype_val.comp continuous_snd))
    refine (EuclideanSpace.equiv (Fin 5) ℝ).symm.continuous.comp ?_
    refine continuous_pi fun i ↦ ?_
    fin_cases i
    · exact h10
    · exact h11
    · exact h20
    · exact h21
    · exact continuous_const
  continuous_invFun := by
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) (Continuous.subtype_mk ?_ _)
    · refine (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp (continuous_pi fun i ↦ ?_)
      have hx (k : Fin 5) : Continuous (fun x : {x : Sphere4 // s4ADKFibration x = s2SouthPole} ↦
          Real.sqrt 2 * x.1.1 k) :=
        continuous_const.mul ((euclidProj k).continuous.comp
          (continuous_subtype_val.comp continuous_subtype_val))
      fin_cases i <;> [exact hx 0; exact hx 1]
    · refine (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp (continuous_pi fun i ↦ ?_)
      have hx (k : Fin 5) : Continuous (fun x : {x : Sphere4 // s4ADKFibration x = s2SouthPole} ↦
          Real.sqrt 2 * x.1.1 k) :=
        continuous_const.mul ((euclidProj k).continuous.comp
          (continuous_subtype_val.comp continuous_subtype_val))
      fin_cases i <;> [exact hx 2; exact hx 3]

/-! ### `SO(2)_{01}` Rotational Equivariance -/

/-- Smooth diffeomorphism `Sphere4 ≃ₘ Sphere4` rotating `(x₀, x₁)` by `(c, s)` (`c² + s² = 1`). -/
noncomputable def s4Rot01 (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4 where
  toFun x :=
    ⟨vec5 (c * x.1 0 - s * x.1 1) (s * x.1 0 + c * x.1 1) (x.1 2) (x.1 3) (x.1 4),
      mem_sphere_zero_iff_norm.mpr (by
        have hsq : ‖vec5 (c * x.1 0 - s * x.1 1) (s * x.1 0 + c * x.1 1)
            (x.1 2) (x.1 3) (x.1 4)‖ ^ 2 = 1 := by
          rw [norm_sq_vec5]
          have hx : x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2 + x.1 3 ^ 2 + x.1 4 ^ 2 = 1 := by
            rw [← norm_sq_vec5, mem_sphere_zero_iff_norm.mp x.2, one_pow]
          simp only [vec5_zero, vec5_one, vec5_two, vec5_three, vec5_four]
          calc
            (c * x.1 0 - s * x.1 1) ^ 2 + (s * x.1 0 + c * x.1 1) ^ 2 +
                x.1 2 ^ 2 + x.1 3 ^ 2 + x.1 4 ^ 2
              = (c ^ 2 + s ^ 2) * (x.1 0 ^ 2 + x.1 1 ^ 2) +
                  x.1 2 ^ 2 + x.1 3 ^ 2 + x.1 4 ^ 2 := by ring
            _ = 1 := by rw [hcs, one_mul, hx]
        nlinarith [norm_nonneg (vec5 (c * x.1 0 - s * x.1 1) (s * x.1 0 + c * x.1 1)
          (x.1 2) (x.1 3) (x.1 4))])⟩
  invFun x :=
    ⟨vec5 (c * x.1 0 + s * x.1 1) (-s * x.1 0 + c * x.1 1) (x.1 2) (x.1 3) (x.1 4),
      mem_sphere_zero_iff_norm.mpr (by
        have hsq : ‖vec5 (c * x.1 0 + s * x.1 1) (-s * x.1 0 + c * x.1 1)
            (x.1 2) (x.1 3) (x.1 4)‖ ^ 2 = 1 := by
          rw [norm_sq_vec5]
          have hx : x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2 + x.1 3 ^ 2 + x.1 4 ^ 2 = 1 := by
            rw [← norm_sq_vec5, mem_sphere_zero_iff_norm.mp x.2, one_pow]
          simp only [vec5_zero, vec5_one, vec5_two, vec5_three, vec5_four]
          calc
            (c * x.1 0 + s * x.1 1) ^ 2 + (-s * x.1 0 + c * x.1 1) ^ 2 +
                x.1 2 ^ 2 + x.1 3 ^ 2 + x.1 4 ^ 2
              = (c ^ 2 + s ^ 2) * (x.1 0 ^ 2 + x.1 1 ^ 2) +
                  x.1 2 ^ 2 + x.1 3 ^ 2 + x.1 4 ^ 2 := by ring
            _ = 1 := by rw [hcs, one_mul, hx]
        nlinarith [norm_nonneg (vec5 (c * x.1 0 + s * x.1 1) (-s * x.1 0 + c * x.1 1)
          (x.1 2) (x.1 3) (x.1 4))])⟩
  left_inv x := by
    apply Subtype.ext
    refine ext_vec5 ?_ ?_ rfl rfl rfl
    · simp only [vec5_zero, vec5_one]; linear_combination x.1 0 * hcs
    · simp only [vec5_zero, vec5_one]; linear_combination x.1 1 * hcs
  right_inv x := by
    apply Subtype.ext
    refine ext_vec5 ?_ ?_ rfl rfl rfl
    · simp only [vec5_zero, vec5_one]; linear_combination x.1 0 * hcs
    · simp only [vec5_zero, vec5_one]; linear_combination x.1 1 * hcs
  contMDiff_toFun := by
    have hc : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 5) ↦
        vec5 (c * x 0 - s * x 1) (s * x 0 + c * x 1) (x 2) (x 3) (x 4)) := by
      have hx (i : Fin 5) : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 5) ↦ x i) :=
        (euclidProj i).contDiff
      exact contDiff_vec5 ((contDiff_const.mul (hx 0)).sub (contDiff_const.mul (hx 1)))
        ((contDiff_const.mul (hx 0)).add (contDiff_const.mul (hx 1))) (hx 2) (hx 3) (hx 4)
    exact (hc.contMDiff.comp contMDiff_coe_sphere).codRestrict_sphere _
  contMDiff_invFun := by
    have hc : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 5) ↦
        vec5 (c * x 0 + s * x 1) (-s * x 0 + c * x 1) (x 2) (x 3) (x 4)) := by
      have hx (i : Fin 5) : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 5) ↦ x i) :=
        (euclidProj i).contDiff
      exact contDiff_vec5 ((contDiff_const.mul (hx 0)).add (contDiff_const.mul (hx 1)))
        (((contDiff_const (c := -s)).mul (hx 0)).add (contDiff_const.mul (hx 1)))
        (hx 2) (hx 3) (hx 4)
    exact (hc.contMDiff.comp contMDiff_coe_sphere).codRestrict_sphere _

/-- Coordinate formula for `s4Rot01 c s hcs x` in `ℝ⁵`. -/
@[simp]
theorem coe_s4Rot01 (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (x : Sphere4) :
    (s4Rot01 c s hcs x : EuclideanSpace ℝ (Fin 5)) =
      vec5 (c * x.1 0 - s * x.1 1) (s * x.1 0 + c * x.1 1) (x.1 2) (x.1 3) (x.1 4) :=
  rfl

/-- Smooth diffeomorphism `Sphere2 ≃ₘ Sphere2` rotating `(y₀, y₁)` by `(c, s)` (`c² + s² = 1`). -/
noncomputable def s2Rot01 (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    Sphere2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere2 where
  toFun y :=
    ⟨vec3 (c * y.1 0 - s * y.1 1) (s * y.1 0 + c * y.1 1) (y.1 2),
      mem_sphere_zero_iff_norm.mpr (by
        have hsq : ‖vec3 (c * y.1 0 - s * y.1 1) (s * y.1 0 + c * y.1 1) (y.1 2)‖ ^ 2 = 1 := by
          rw [norm_sq_vec3]
          have hy : y.1 0 ^ 2 + y.1 1 ^ 2 + y.1 2 ^ 2 = 1 := by
            rw [← norm_sq_vec3, mem_sphere_zero_iff_norm.mp y.2, one_pow]
          simp only [vec3_zero, vec3_one, vec3_two]
          calc
            (c * y.1 0 - s * y.1 1) ^ 2 + (s * y.1 0 + c * y.1 1) ^ 2 + y.1 2 ^ 2
              = (c ^ 2 + s ^ 2) * (y.1 0 ^ 2 + y.1 1 ^ 2) + y.1 2 ^ 2 := by ring
            _ = 1 := by rw [hcs, one_mul, hy]
        nlinarith [norm_nonneg (vec3 (c * y.1 0 - s * y.1 1)
          (s * y.1 0 + c * y.1 1) (y.1 2))])⟩
  invFun y :=
    ⟨vec3 (c * y.1 0 + s * y.1 1) (-s * y.1 0 + c * y.1 1) (y.1 2),
      mem_sphere_zero_iff_norm.mpr (by
        have hsq : ‖vec3 (c * y.1 0 + s * y.1 1) (-s * y.1 0 + c * y.1 1) (y.1 2)‖ ^ 2 = 1 := by
          rw [norm_sq_vec3]
          have hy : y.1 0 ^ 2 + y.1 1 ^ 2 + y.1 2 ^ 2 = 1 := by
            rw [← norm_sq_vec3, mem_sphere_zero_iff_norm.mp y.2, one_pow]
          simp only [vec3_zero, vec3_one, vec3_two]
          calc
            (c * y.1 0 + s * y.1 1) ^ 2 + (-s * y.1 0 + c * y.1 1) ^ 2 + y.1 2 ^ 2
              = (c ^ 2 + s ^ 2) * (y.1 0 ^ 2 + y.1 1 ^ 2) + y.1 2 ^ 2 := by ring
            _ = 1 := by rw [hcs, one_mul, hy]
        nlinarith [norm_nonneg (vec3 (c * y.1 0 + s * y.1 1)
          (-s * y.1 0 + c * y.1 1) (y.1 2))])⟩
  left_inv y := by
    apply Subtype.ext
    refine ext_vec3 ?_ ?_ rfl
    · simp only [vec3_zero, vec3_one]; linear_combination y.1 0 * hcs
    · simp only [vec3_zero, vec3_one]; linear_combination y.1 1 * hcs
  right_inv y := by
    apply Subtype.ext
    refine ext_vec3 ?_ ?_ rfl
    · simp only [vec3_zero, vec3_one]; linear_combination y.1 0 * hcs
    · simp only [vec3_zero, vec3_one]; linear_combination y.1 1 * hcs
  contMDiff_toFun := by
    have hc : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin 3) ↦
        vec3 (c * y 0 - s * y 1) (s * y 0 + c * y 1) (y 2)) := by
      have hy (i : Fin 3) : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin 3) ↦ y i) :=
        (euclidProj i).contDiff
      exact contDiff_vec3 ((contDiff_const.mul (hy 0)).sub (contDiff_const.mul (hy 1)))
        ((contDiff_const.mul (hy 0)).add (contDiff_const.mul (hy 1))) (hy 2)
    exact (hc.contMDiff.comp contMDiff_coe_sphere).codRestrict_sphere _
  contMDiff_invFun := by
    have hc : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin 3) ↦
        vec3 (c * y 0 + s * y 1) (-s * y 0 + c * y 1) (y 2)) := by
      have hy (i : Fin 3) : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin 3) ↦ y i) :=
        (euclidProj i).contDiff
      exact contDiff_vec3 ((contDiff_const.mul (hy 0)).add (contDiff_const.mul (hy 1)))
        (((contDiff_const (c := -s)).mul (hy 0)).add (contDiff_const.mul (hy 1))) (hy 2)
    exact (hc.contMDiff.comp contMDiff_coe_sphere).codRestrict_sphere _

/-- Coordinate formula for `s2Rot01 c s hcs y` in `ℝ³`. -/
@[simp]
theorem coe_s2Rot01 (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (y : Sphere2) :
    (s2Rot01 c s hcs y : EuclideanSpace ℝ (Fin 3)) =
      vec3 (c * y.1 0 - s * y.1 1) (s * y.1 0 + c * y.1 1) (y.1 2) :=
  rfl

/-- `SO(2)_{01}` equivariance of `s4ADKRaw`. -/
theorem s4ADKRaw_s4Rot01 (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (x : Sphere4) :
    s4ADKRaw (s4Rot01 c s hcs x).1 =
      vec3 (c * s4ADKRaw x.1 0 - s * s4ADKRaw x.1 1)
        (s * s4ADKRaw x.1 0 + c * s4ADKRaw x.1 1) (s4ADKRaw x.1 2) := by
  refine ext_vec3 ?_ ?_ ?_ <;>
    simp only [coe_s4Rot01, s4ADKRaw_zero, s4ADKRaw_one, s4ADKRaw_two,
      vec5_zero, vec5_one, vec5_two, vec5_three, vec5_four, vec3_zero, vec3_one, vec3_two]
  · ring
  · ring
  · linear_combination -(x.1 0 ^ 2 + x.1 1 ^ 2) * hcs

/-- Rotational `SO(2)_{01}` equivariance of `s4ADKFibration`. -/
-- tier: T2
theorem s4ADKFibration_s4Rot01 (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (x : Sphere4) :
    s4ADKFibration (s4Rot01 c s hcs x) = s2Rot01 c s hcs (s4ADKFibration x) := by
  have hnorm : ‖s4ADKRaw (s4Rot01 c s hcs x).1‖ = ‖s4ADKRaw x.1‖ := by
    have hsq : ‖s4ADKRaw (s4Rot01 c s hcs x).1‖ ^ 2 = ‖s4ADKRaw x.1‖ ^ 2 := by
      rw [s4ADKRaw_s4Rot01, norm_sq_vec3, norm_sq_vec3]
      simp only [vec3_zero, vec3_one, vec3_two]
      calc
        (c * s4ADKRaw x.1 0 - s * s4ADKRaw x.1 1) ^ 2 +
            (s * s4ADKRaw x.1 0 + c * s4ADKRaw x.1 1) ^ 2 + s4ADKRaw x.1 2 ^ 2
          = (c ^ 2 + s ^ 2) * (s4ADKRaw x.1 0 ^ 2 + s4ADKRaw x.1 1 ^ 2) + s4ADKRaw x.1 2 ^ 2 := by
            ring
        _ = s4ADKRaw x.1 0 ^ 2 + s4ADKRaw x.1 1 ^ 2 + s4ADKRaw x.1 2 ^ 2 := by rw [hcs, one_mul]
    nlinarith [norm_nonneg (s4ADKRaw (s4Rot01 c s hcs x).1), norm_nonneg (s4ADKRaw x.1)]
  apply Subtype.ext
  rw [coe_s4ADKFibration, hnorm, s4ADKRaw_s4Rot01]
  refine ext_vec3 ?_ ?_ ?_ <;>
    simp only [coe_s4ADKFibration, coe_s2Rot01, PiLp.smul_apply, smul_eq_mul,
      vec3_zero, vec3_one, vec3_two] <;> ring

end GlobalADKMap

/-! ## 2. Exact Equatorial Critical Circle of `s4ADKFibration` -/

section CriticalPoints

/-- Explicit `3 × 3` determinant `det [a, b, c]` in `EuclideanSpace ℝ (Fin 3)`. -/
def det3 (a b c : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  a 0 * (b 1 * c 2 - b 2 * c 1) - a 1 * (b 0 * c 2 - b 2 * c 0) + a 2 * (b 0 * c 1 - b 1 * c 0)

/-- Scaling the third column of `det3`. -/
@[simp]
theorem det3_smul_right (a b c : EuclideanSpace ℝ (Fin 3)) (k : ℝ) :
    det3 a b (k • c) = k * det3 a b c := by
  simp only [det3, PiLp.smul_apply, smul_eq_mul]
  ring

/-- Scaling the second column of `det3`. -/
@[simp]
theorem det3_smul_mid (a b c : EuclideanSpace ℝ (Fin 3)) (k : ℝ) :
    det3 a (k • b) c = k * det3 a b c := by
  simp only [det3, PiLp.smul_apply, smul_eq_mul]
  ring

/-- Vanishing of `det3` when the first and third arguments agree. -/
@[simp]
theorem det3_self_right (a b : EuclideanSpace ℝ (Fin 3)) : det3 a b a = 0 := by
  simp only [det3]
  ring

/-- Vanishing of `det3` when the first and second arguments agree. -/
@[simp]
theorem det3_self_mid (a c : EuclideanSpace ℝ (Fin 3)) : det3 a a c = 0 := by
  simp only [det3]
  ring

/-- Vanishing of `det3` when the second and third arguments agree. -/
@[simp]
theorem det3_mid_self (a b : EuclideanSpace ℝ (Fin 3)) : det3 a b b = 0 := by
  simp only [det3]
  ring

/-- Additivity in the middle argument of `det3`. -/
theorem det3_add_mid (a b₁ b₂ c : EuclideanSpace ℝ (Fin 3)) :
    det3 a (b₁ + b₂) c = det3 a b₁ c + det3 a b₂ c := by
  simp only [det3, PiLp.add_apply]
  ring

/-- Additivity in the third argument of `det3`. -/
theorem det3_add_right (a b c₁ c₂ : EuclideanSpace ℝ (Fin 3)) :
    det3 a b (c₁ + c₂) = det3 a b c₁ + det3 a b c₂ := by
  simp only [det3, PiLp.add_apply]
  ring

/-- Subtractivity in the middle argument of `det3`. -/
theorem det3_sub_mid (a b₁ b₂ c : EuclideanSpace ℝ (Fin 3)) :
    det3 a (b₁ - b₂) c = det3 a b₁ c - det3 a b₂ c := by
  simp only [det3, PiLp.sub_apply]
  ring

/-- Subtractivity in the third argument of `det3`. -/
theorem det3_sub_right (a b c₁ c₂ : EuclideanSpace ℝ (Fin 3)) :
    det3 a b (c₁ - c₂) = det3 a b c₁ - det3 a b c₂ := by
  simp only [det3, PiLp.sub_apply]
  ring

/-- Nonzero `det3 w b₁ b₂` implies linear independence of `![b₁, b₂]`. -/
theorem linearIndependent_of_det3_ne_zero {w b₁ b₂ : EuclideanSpace ℝ (Fin 3)}
    (h : det3 w b₁ b₂ ≠ 0) :
    LinearIndependent ℝ ![b₁, b₂] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h1 : g 0 • b₁ + g 1 • b₂ = 0 := by
    simpa [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using hg
  have hd0 : det3 w (g 0 • b₁ + g 1 • b₂) b₂ = 0 := by
    simp only [h1, det3, PiLp.zero_apply, zero_mul, mul_zero, sub_self, add_zero]
  rw [det3_add_mid, det3_smul_mid, det3_smul_mid, det3_mid_self, mul_zero, add_zero] at hd0
  have hd1 : det3 w b₁ (g 0 • b₁ + g 1 • b₂) = 0 := by
    simp only [h1, det3, PiLp.zero_apply, mul_zero, sub_self, add_zero]
  rw [det3_add_right, det3_smul_right, det3_smul_right, det3_mid_self, mul_zero, zero_add] at hd1
  intro i
  fin_cases i
  · exact (mul_eq_zero.mp hd0).resolve_right h
  · exact (mul_eq_zero.mp hd1).resolve_right h

private noncomputable def s4ADKRawDerivCLM (x : EuclideanSpace ℝ (Fin 5)) :
    EuclideanSpace ℝ (Fin 5) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  let px (i : Fin 5) : EuclideanSpace ℝ (Fin 5) →L[ℝ] ℝ := euclidProj i
  let rho : ℝ := x 2 ^ 2 + x 3 ^ 2 - 1 / 2
  let drho : EuclideanSpace ℝ (Fin 5) →L[ℝ] ℝ := (2 * x 2) • px 2 + (2 * x 3) • px 3
  clmVec3
    (rho • px 0 + x 0 • drho - x 4 • px 1 - x 1 • px 4)
    (x 4 • px 0 + x 0 • px 4 + rho • px 1 + x 1 • drho)
    ((-2 * x 0) • px 0 + (-2 * x 1) • px 1)

private theorem s4ADKRawDerivCLM_apply (x v : EuclideanSpace ℝ (Fin 5)) :
    s4ADKRawDerivCLM x v =
      vec3
        ((x 2 ^ 2 + x 3 ^ 2 - 1 / 2) * v 0 - x 4 * v 1 +
          2 * x 0 * x 2 * v 2 + 2 * x 0 * x 3 * v 3 - x 1 * v 4)
        (x 4 * v 0 + (x 2 ^ 2 + x 3 ^ 2 - 1 / 2) * v 1 +
          2 * x 1 * x 2 * v 2 + 2 * x 1 * x 3 * v 3 + x 0 * v 4)
        (-2 * x 0 * v 0 - 2 * x 1 * v 1) := by
  simp only [s4ADKRawDerivCLM, clmVec3_apply, add_apply, sub_apply, smul_apply, smul_eq_mul,
    euclidProj_apply]
  refine ext_vec3 ?_ ?_ ?_ <;> ring_nf

private theorem hasFDerivAt_s4ADKRaw (x : EuclideanSpace ℝ (Fin 5)) :
    HasFDerivAt s4ADKRaw (s4ADKRawDerivCLM x) x := by
  have hx (i : Fin 5) :
      HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 5) ↦ y i) (euclidProj i) x :=
    (euclidProj i).hasFDerivAt
  have hsq (i : Fin 5) :
      HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 5) ↦ y i ^ 2)
        ((2 * x i) • euclidProj i) x := by
    refine ((hasDerivAt_pow 2 (x i)).comp_hasFDerivAt x (hx i)).congr_fderiv ?_
    ext v; simp [smul_eq_mul]
  have hrho :
      HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 5) ↦ y 2 ^ 2 + y 3 ^ 2 - 1 / 2)
        ((2 * x 2) • euclidProj 2 + (2 * x 3) • euclidProj 3) x := by
    refine (((hsq 2).add (hsq 3)).sub (hasFDerivAt_const _ x)).congr_fderiv ?_
    simp
  have h0 : HasFDerivAt (fun y ↦ s4ADKRaw y 0)
      ((x 2 ^ 2 + x 3 ^ 2 - 1 / 2) • euclidProj 0 +
        x 0 • ((2 * x 2) • euclidProj 2 + (2 * x 3) • euclidProj 3) -
        (x 4 • euclidProj 1 + x 1 • euclidProj 4)) x := by
    refine (((hx 0).mul hrho).sub ((hx 1).mul (hx 4))).congr_fderiv ?_
    ext v; simp [smul_eq_mul]; ring
  have h1 : HasFDerivAt (fun y ↦ s4ADKRaw y 1)
      ((x 4 • euclidProj 0 + x 0 • euclidProj 4) +
        ((x 2 ^ 2 + x 3 ^ 2 - 1 / 2) • euclidProj 1 +
          x 1 • ((2 * x 2) • euclidProj 2 + (2 * x 3) • euclidProj 3))) x := by
    refine (((hx 0).mul (hx 4)).add ((hx 1).mul hrho)).congr_fderiv ?_
    ext v; simp [smul_eq_mul]; ring
  have h2 : HasFDerivAt (fun y ↦ s4ADKRaw y 2)
      ((-2 * x 0) • euclidProj 0 + (-2 * x 1) • euclidProj 1) x := by
    refine ((hasFDerivAt_const (1 / 4 : ℝ) x).sub ((hsq 0).add (hsq 1))).congr_fderiv ?_
    ext v; simp [smul_eq_mul]; ring
  refine (hasFDerivAt_vec3 h0 h1 h2).congr_fderiv ?_
  ext v i
  simp only [s4ADKRawDerivCLM, clmVec3_apply]
  fin_cases i <;> simp [smul_eq_mul] <;> ring

private theorem fderiv_s4ADKRaw_apply (x v : EuclideanSpace ℝ (Fin 5)) :
    fderiv ℝ s4ADKRaw x v =
      vec3
        ((x 2 ^ 2 + x 3 ^ 2 - 1 / 2) * v 0 - x 4 * v 1 +
          2 * x 0 * x 2 * v 2 + 2 * x 0 * x 3 * v 3 - x 1 * v 4)
        (x 4 * v 0 + (x 2 ^ 2 + x 3 ^ 2 - 1 / 2) * v 1 +
          2 * x 1 * x 2 * v 2 + 2 * x 1 * x 3 * v 3 + x 0 * v 4)
        (-2 * x 0 * v 0 - 2 * x 1 * v 1) := by
  rw [(hasFDerivAt_s4ADKRaw x).fderiv]
  exact s4ADKRawDerivCLM_apply x v

private theorem hasFDerivAt_normalizeVec3 {w : EuclideanSpace ℝ (Fin 3)} (hw : w ≠ 0) :
    ∃ L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ,
      HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 3) ↦ ‖z‖⁻¹ • z)
        (‖w‖⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) + L.smulRight w) w := by
  have hsq : w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 ≠ 0 := by
    have hp : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw)
    rw [norm_sq_vec3] at hp
    exact hp.ne'
  have hcoord (i : Fin 3) :
      HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 3) ↦ z i ^ 2)
        ((2 * w i) • euclidProj i) w := by
    refine ((hasDerivAt_pow 2 (w i)).comp_hasFDerivAt w (euclidProj i).hasFDerivAt).congr_fderiv ?_
    ext u; simp [smul_eq_mul]
  have hnorm_sq :
      HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 3) ↦ z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2)
        ((2 * w 0) • euclidProj 0 + (2 * w 1) • euclidProj 1 +
          (2 * w 2) • euclidProj 2) w :=
    ((hcoord 0).add (hcoord 1)).add (hcoord 2)
  have hsqrt := (Real.hasDerivAt_sqrt hsq).comp_hasFDerivAt w hnorm_sq
  have hsqrt_eq : (fun z : EuclideanSpace ℝ (Fin 3) ↦ ‖z‖⁻¹ • z) =
      (((fun y : ℝ ↦ y⁻¹) ∘ (fun s : ℝ ↦ Real.sqrt s) ∘
        fun z : EuclideanSpace ℝ (Fin 3) ↦ z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2) • id) := by
    funext z
    dsimp only [Pi.smul_apply, Function.comp_apply, id_eq]
    rw [show ‖z‖ = Real.sqrt (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2) from by
      rw [← norm_sq_vec3, Real.sqrt_sq (norm_nonneg z)]]
    rfl
  have hsqrt_ne : Real.sqrt (w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (norm_sq_vec3 w ▸ sq_pos_of_pos (norm_pos_iff.mpr hw))
  have hinv := (hasDerivAt_inv hsqrt_ne).comp_hasFDerivAt w hsqrt
  have hnorm_val : Real.sqrt (w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2) = ‖w‖ := by
    rw [← norm_sq_vec3, Real.sqrt_sq (norm_nonneg w)]
  have hsmul1 := (hinv.smul (hasFDerivAt_id w)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (congrFun hsqrt_eq))
  dsimp only [Function.comp_apply, id_eq] at hsmul1
  rw [hnorm_val] at hsmul1
  exact ⟨_, hsmul1⟩

private theorem regular_of_det3_ne_zero (x : Sphere4)
    {v₁ v₂ : EuclideanSpace ℝ (Fin 5)}
    (hv₁_orth : ⟪x.1, v₁⟫_ℝ = 0) (hv₂_orth : ⟪x.1, v₂⟫_ℝ = 0)
    (hdet : det3 (s4ADKRaw x.1) (fderiv ℝ s4ADKRaw x.1 v₁) (fderiv ℝ s4ADKRaw x.1 v₂) ≠ 0) :
    Function.Surjective (mfderiv (𝓡 4) (𝓡 2) s4ADKFibration x) := by
  have hv₁_range : v₁ ∈ (mvfderiv (𝓡 4) (Subtype.val : Sphere4 → _) x).range := by
    rw [range_mvfderiv_subtypeVal (n := 4) x, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact hv₁_orth
  have hv₂_range : v₂ ∈ (mvfderiv (𝓡 4) (Subtype.val : Sphere4 → _) x).range := by
    rw [range_mvfderiv_subtypeVal (n := 4) x, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact hv₂_orth
  obtain ⟨u₁, hu₁⟩ := hv₁_range
  obtain ⟨u₂, hu₂⟩ := hv₂_range
  set w := s4ADKRaw x.1
  obtain ⟨L, hnorm_fderiv⟩ := hasFDerivAt_normalizeVec3 (s4ADKRaw_ne_zero_of_mem_sphere4 x)
  let N : EuclideanSpace ℝ (Fin 5) → EuclideanSpace ℝ (Fin 3) :=
    fun y ↦ ‖s4ADKRaw y‖⁻¹ • s4ADKRaw y
  have hN : HasFDerivAt N
      ((‖w‖⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) +
        L.smulRight w).comp (s4ADKRawDerivCLM x.1)) x.1 :=
    hnorm_fderiv.comp x.1 (hasFDerivAt_s4ADKRaw x.1)
  have hcomp_val : (Subtype.val : Sphere2 → EuclideanSpace ℝ (Fin 3)) ∘ s4ADKFibration =
      N ∘ (Subtype.val : Sphere4 → EuclideanSpace ℝ (Fin 5)) := by
    funext z; rfl
  let J : TangentSpace (𝓡 2) (s4ADKFibration x) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    mvfderiv (𝓡 2) (Subtype.val : Sphere2 → EuclideanSpace ℝ (Fin 3)) (s4ADKFibration x)
  let D : TangentSpace (𝓡 4) x →L[ℝ] TangentSpace (𝓡 2) (s4ADKFibration x) :=
    mfderiv (𝓡 4) (𝓡 2) s4ADKFibration x
  have hJ_eval (u : TangentSpace (𝓡 4) x) :
      J (D u) =
        (‖w‖⁻¹ • fderiv ℝ s4ADKRaw x.1 (mvfderiv (𝓡 4) Subtype.val x u) +
          (L (fderiv ℝ s4ADKRaw x.1 (mvfderiv (𝓡 4) Subtype.val x u))) • w) := by
    have hf : MDifferentiableAt (𝓡 4) (𝓡 2) s4ADKFibration x :=
      (contMDiff_s4ADKFibration x).mdifferentiableAt (by simp)
    have hj : MDifferentiableAt (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
        (Subtype.val : Sphere2 → EuclideanSpace ℝ (Fin 3)) (s4ADKFibration x) :=
      (contMDiff_coe_sphere (m := ∞) _).mdifferentiableAt (by simp)
    have hcomp1 : mvfderiv (𝓡 4) ((Subtype.val : Sphere2 → _) ∘ s4ADKFibration) x u = J (D u) :=
      mvfderiv_comp_apply x hj hf u
    have hcomp2 : mvfderiv (𝓡 4) (N ∘ (Subtype.val : Sphere4 → _)) x u =
        (‖w‖⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) + L.smulRight w)
          (s4ADKRawDerivCLM x.1 (mvfderiv (𝓡 4) Subtype.val x u)) := by
      rw [TauCeti.mvfderiv_comp_apply_of_differentiableAt hN.differentiableAt
        ((contMDiff_coe_sphere (m := ∞) x).mdifferentiableAt (by simp)) u, hN.fderiv]
      rfl
    have heq := congrArg (fun g ↦ mvfderiv (𝓡 4) g x u) hcomp_val
    rw [hcomp1, hcomp2] at heq
    rw [heq, ← (hasFDerivAt_s4ADKRaw x.1).fderiv]
    simp [add_apply, smul_apply]
  set b₁ := fderiv ℝ s4ADKRaw x.1 v₁
  set b₂ := fderiv ℝ s4ADKRaw x.1 v₂
  have hw_pos : 0 < ‖w‖ := norm_s4ADKRaw_pos x
  have hdet_J : det3 w (J (D u₁)) (J (D u₂)) = ‖w‖⁻¹ ^ 2 * det3 w b₁ b₂ := by
    change mvfderiv (𝓡 4) Subtype.val x u₁ = v₁ at hu₁
    change mvfderiv (𝓡 4) Subtype.val x u₂ = v₂ at hu₂
    rw [hJ_eval u₁, hJ_eval u₂, hu₁, hu₂]
    change det3 w (‖w‖⁻¹ • b₁ + L b₁ • w) (‖w‖⁻¹ • b₂ + L b₂ • w) = _
    rw [det3_add_mid, det3_add_right, det3_add_right]
    simp only [det3_smul_mid, det3_smul_right, det3_self_mid, det3_self_right]
    ring
  have hdet_J_ne : det3 w (J (D u₁)) (J (D u₂)) ≠ 0 := by
    rw [hdet_J]
    exact mul_ne_zero (pow_ne_zero 2 (inv_ne_zero hw_pos.ne')) hdet
  have hli_img : LinearIndependent ℝ ![J (D u₁), J (D u₂)] :=
    linearIndependent_of_det3_ne_zero hdet_J_ne
  have hli : LinearIndependent ℝ ![D u₁, D u₂] := by
    refine LinearIndependent.of_comp J.toLinearMap ?_
    convert hli_img using 1
    ext i; fin_cases i <;> rfl
  have htop : Submodule.span ℝ (Set.range ![D u₁, D u₂]) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [finrank_span_eq_card hli, Fintype.card_fin]
    exact finrank_euclideanSpace_fin.symm
  intro z
  have hz : z ∈ Submodule.span ℝ (Set.range ![D u₁, D u₂]) := htop ▸ Submodule.mem_top
  rw [Submodule.mem_span_range_iff_exists_fun] at hz
  obtain ⟨c, hc⟩ := hz
  refine ⟨c 0 • u₁ + c 1 • u₂, ?_⟩
  simpa only [map_add, map_smul, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one] using hc

private theorem inner_vec5 (a b : EuclideanSpace ℝ (Fin 5)) :
    ⟪a, b⟫_ℝ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 + a 3 * b 3 + a 4 * b 4 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_five]
  simp only [star_trivial, mul_comm]

/-- Canonical critical basepoint `p₀ = (1, 0, 0, 0, 0) ∈ Sphere4`. -/
noncomputable def s4ADKCritBase : Sphere4 :=
  ⟨vec5 1 0 0 0 0, mem_sphere_zero_iff_norm.mpr (by
    have hsq : ‖vec5 1 0 0 0 0‖ ^ 2 = 1 := by rw [norm_sq_vec5]; norm_num
    nlinarith [norm_nonneg (vec5 1 0 0 0 0)])⟩

private theorem s4ADKCritBase_mem_criticalPoints :
    s4ADKCritBase ∈ criticalPoints (𝓡 4) (𝓡 2) s4ADKFibration := by
  intro hsurj
  set w := s4ADKRaw s4ADKCritBase.1
  obtain ⟨L, hnorm_fderiv⟩ :=
    hasFDerivAt_normalizeVec3 (s4ADKRaw_ne_zero_of_mem_sphere4 s4ADKCritBase)
  let N : EuclideanSpace ℝ (Fin 5) → EuclideanSpace ℝ (Fin 3) :=
    fun y ↦ ‖s4ADKRaw y‖⁻¹ • s4ADKRaw y
  have hN : HasFDerivAt N
      ((‖w‖⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) + L.smulRight w).comp
        (s4ADKRawDerivCLM s4ADKCritBase.1)) s4ADKCritBase.1 :=
    hnorm_fderiv.comp s4ADKCritBase.1 (hasFDerivAt_s4ADKRaw s4ADKCritBase.1)
  have hcomp_val : (Subtype.val : Sphere2 → EuclideanSpace ℝ (Fin 3)) ∘ s4ADKFibration =
      N ∘ (Subtype.val : Sphere4 → EuclideanSpace ℝ (Fin 5)) := by
    funext z; rfl
  let J : TangentSpace (𝓡 2) (s4ADKFibration s4ADKCritBase) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    mvfderiv (𝓡 2) (Subtype.val : Sphere2 → EuclideanSpace ℝ (Fin 3))
      (s4ADKFibration s4ADKCritBase)
  let D : TangentSpace (𝓡 4) s4ADKCritBase →L[ℝ]
      TangentSpace (𝓡 2) (s4ADKFibration s4ADKCritBase) :=
    mfderiv (𝓡 4) (𝓡 2) s4ADKFibration s4ADKCritBase
  have hJ_span (u : TangentSpace (𝓡 4) s4ADKCritBase) :
      J (D u) ∈ Submodule.span ℝ ({vec3 0 1 0} : Set (EuclideanSpace ℝ (Fin 3))) := by
    have hf : MDifferentiableAt (𝓡 4) (𝓡 2) s4ADKFibration s4ADKCritBase :=
      (contMDiff_s4ADKFibration s4ADKCritBase).mdifferentiableAt (by simp)
    have hj : MDifferentiableAt (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
        (Subtype.val : Sphere2 → EuclideanSpace ℝ (Fin 3)) (s4ADKFibration s4ADKCritBase) :=
      (contMDiff_coe_sphere (m := ∞) _).mdifferentiableAt (by simp)
    have hcomp1 :
        mvfderiv (𝓡 4) ((Subtype.val : Sphere2 → _) ∘ s4ADKFibration) s4ADKCritBase u =
          J (D u) :=
      mvfderiv_comp_apply s4ADKCritBase hj hf u
    have hcomp2 :
        mvfderiv (𝓡 4) (N ∘ (Subtype.val : Sphere4 → _)) s4ADKCritBase u =
          (‖w‖⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) + L.smulRight w)
            (s4ADKRawDerivCLM s4ADKCritBase.1
              (mvfderiv (𝓡 4) Subtype.val s4ADKCritBase u)) := by
      rw [TauCeti.mvfderiv_comp_apply_of_differentiableAt hN.differentiableAt
        ((contMDiff_coe_sphere (m := ∞) s4ADKCritBase).mdifferentiableAt (by simp)) u,
        hN.fderiv]
      rfl
    have heq := congrArg (fun g ↦ mvfderiv (𝓡 4) g s4ADKCritBase u) hcomp_val
    rw [hcomp1, hcomp2] at heq
    set v := mvfderiv (𝓡 4) (Subtype.val : Sphere4 → EuclideanSpace ℝ (Fin 5)) s4ADKCritBase u
    have hv_orth : v ∈ (ℝ ∙ s4ADKCritBase.1)ᗮ := by
      rw [← range_mvfderiv_subtypeVal (n := 4) s4ADKCritBase]
      exact LinearMap.mem_range_self _ u
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_vec5] at hv_orth
    have hv0 : v 0 = 0 := by
      simpa [s4ADKCritBase] using hv_orth
    have hraw_v : s4ADKRawDerivCLM s4ADKCritBase.1 v = (-1 / 2 * v 1 + v 4) • vec3 0 1 0 := by
      rw [s4ADKRawDerivCLM_apply]
      refine ext_vec3 ?_ ?_ ?_ <;>
        simp [s4ADKCritBase, hv0, PiLp.smul_apply, smul_eq_mul]
      ring
    have hw_orth : ⟪J (D u), (s4ADKFibration s4ADKCritBase : EuclideanSpace ℝ (Fin 3))⟫_ℝ = 0 := by
      have hm : J (D u) ∈ (ℝ ∙ (s4ADKFibration s4ADKCritBase : EuclideanSpace ℝ (Fin 3)))ᗮ := by
        rw [← range_mvfderiv_subtypeVal (n := 2) (s4ADKFibration s4ADKCritBase)]
        exact LinearMap.mem_range_self _ (D u)
      exact (Submodule.mem_orthogonal_singleton_iff_inner_left).mp hm
    have horth_w : ⟪J (D u), w⟫_ℝ = 0 := by
      have hm := hw_orth
      rw [coe_s4ADKFibration, inner_smul_right] at hm
      exact (mul_eq_zero.mp hm).resolve_left (inv_ne_zero (norm_s4ADKRaw_pos _).ne')
    have hw_val : w = vec3 (-1 / 2) 0 (-3 / 4) := by
      refine ext_vec3 ?_ ?_ ?_ <;> simp [w, s4ADKRaw, s4ADKCritBase] <;> norm_num
    have he1_w : ⟪vec3 0 1 0, w⟫_ℝ = 0 := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
      simp [hw_val]
    have hJ_val : J (D u) =
        ‖w‖⁻¹ • s4ADKRawDerivCLM s4ADKCritBase.1 v +
          L (s4ADKRawDerivCLM s4ADKCritBase.1 v) • w := by
      rw [heq]
      simp [add_apply, smul_apply]
    have hL_coef : L (s4ADKRawDerivCLM s4ADKCritBase.1 v) = 0 := by
      rw [hJ_val, hraw_v, inner_add_left, inner_smul_left, inner_smul_left, inner_smul_left,
        he1_w] at horth_w
      simp only [RCLike.conj_to_real, mul_zero, zero_add] at horth_w
      have hw_sq : ⟪w, w⟫_ℝ ≠ 0 := by
        rw [real_inner_self_eq_norm_sq]
        exact pow_ne_zero 2 (norm_s4ADKRaw_pos s4ADKCritBase).ne'
      have hL0 := (mul_eq_zero.mp horth_w).resolve_right hw_sq
      rwa [← hraw_v] at hL0
    have hJu : J (D u) =
        (‖w‖⁻¹ * (-1 / 2 * v 1 + v 4)) • vec3 0 1 0 := by
      rw [hJ_val, hL_coef, zero_smul, add_zero, hraw_v, smul_smul]
    rw [hJu]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  have hle : (LinearMap.comp J.toLinearMap D.toLinearMap).range ≤
      Submodule.span ℝ ({vec3 0 1 0} : Set (EuclideanSpace ℝ (Fin 3))) := by
    rintro _ ⟨u, rfl⟩
    exact hJ_span u
  have htop_J : J.toLinearMap.range ≤
      Submodule.span ℝ ({vec3 0 1 0} : Set (EuclideanSpace ℝ (Fin 3))) := by
    rintro z ⟨y, rfl⟩
    obtain ⟨u, rfl⟩ := hsurj y
    exact hle ⟨u, rfl⟩
  have hfin_range : Module.finrank ℝ J.toLinearMap.range ≤ 1 :=
    (Submodule.finrank_mono htop_J).trans (le_of_eq (finrank_span_singleton (K := ℝ)
      (v := vec3 0 1 0) (by
        intro h0
        have h1 := congrArg (fun a : EuclideanSpace ℝ (Fin 3) ↦ a 1) h0
        simp at h1)))
  have hfin_dom :
      Module.finrank ℝ (TangentSpace (𝓡 2) (s4ADKFibration s4ADKCritBase)) = 2 :=
    finrank_euclideanSpace_fin
  have hfin_inj :
      Module.finrank ℝ J.toLinearMap.range =
        Module.finrank ℝ (TangentSpace (𝓡 2) (s4ADKFibration s4ADKCritBase)) :=
    LinearEquiv.finrank_eq
      (LinearEquiv.ofInjective J.toLinearMap (injective_mvfderiv_subtypeVal_sphere _)).symm
  omega

private theorem surjective_mfderiv_of_s4Rot01_conj {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1)
    {x : Sphere4}
    (hsurj : Function.Surjective (mfderiv (𝓡 4) (𝓡 2) s4ADKFibration x)) :
    Function.Surjective (mfderiv (𝓡 4) (𝓡 2) s4ADKFibration (s4Rot01 c s hcs x)) := by
  have hcomm : s4ADKFibration =
      (s2Rot01 c s hcs).symm ∘ s4ADKFibration ∘ s4Rot01 c s hcs := by
    funext y
    change _ = (s2Rot01 c s hcs).symm (s4ADKFibration (s4Rot01 c s hcs y))
    rw [s4ADKFibration_s4Rot01 c s hcs y, (s2Rot01 c s hcs).symm_apply_apply]
  have hf_at : MDifferentiableAt (𝓡 4) (𝓡 2) s4ADKFibration x :=
    (contMDiff_s4ADKFibration x).mdifferentiableAt (by simp)
  have hrot4_diff : MDifferentiableAt (𝓡 4) (𝓡 4) (s4Rot01 c s hcs) x :=
    ((s4Rot01 c s hcs).contMDiff x).mdifferentiableAt (by simp)
  have hrot2_diff : MDifferentiableAt (𝓡 2) (𝓡 2) (s2Rot01 c s hcs).symm
      (s4ADKFibration (s4Rot01 c s hcs x)) :=
    ((s2Rot01 c s hcs).symm.contMDiff _).mdifferentiableAt (by simp)
  have h1 : Function.Surjective
      (mfderiv (𝓡 4) (𝓡 2) ((s2Rot01 c s hcs).symm ∘ s4ADKFibration ∘ s4Rot01 c s hcs) x) := by
    rw [← hcomm]
    exact hsurj
  have hcomp_deriv :
      mfderiv (𝓡 4) (𝓡 2) ((s2Rot01 c s hcs).symm ∘ s4ADKFibration ∘ s4Rot01 c s hcs) x =
        (mfderiv (𝓡 2) (𝓡 2) (s2Rot01 c s hcs).symm (s4ADKFibration (s4Rot01 c s hcs x))).comp
          ((mfderiv (𝓡 4) (𝓡 2) s4ADKFibration (s4Rot01 c s hcs x)).comp
            (mfderiv (𝓡 4) (𝓡 4) (s4Rot01 c s hcs) x)) := by
    have hfa : MDifferentiableAt (𝓡 4) (𝓡 2) (s4ADKFibration ∘ s4Rot01 c s hcs) x :=
      ((contMDiff_s4ADKFibration.comp (s4Rot01 c s hcs).contMDiff) x).mdifferentiableAt (by simp)
    have hfb : MDifferentiableAt (𝓡 4) (𝓡 2) s4ADKFibration (s4Rot01 c s hcs x) :=
      (contMDiff_s4ADKFibration _).mdifferentiableAt (by simp)
    rw [mfderiv_comp x hrot2_diff hfa, mfderiv_comp x hfb hrot4_diff]
    rfl
  rw [hcomp_deriv] at h1
  have hrot2_inj :
      Function.Injective
        (mfderiv (𝓡 2) (𝓡 2) (s2Rot01 c s hcs).symm (s4ADKFibration (s4Rot01 c s hcs x))) :=
    ((s2Rot01 c s hcs).symm.isLocalDiffeomorph _).isInvertible_mfderiv (by simp) |>.injective
  have hmid :
      Function.Surjective
        ((mfderiv (𝓡 4) (𝓡 2) s4ADKFibration (s4Rot01 c s hcs x)).comp
          (mfderiv (𝓡 4) (𝓡 4) (s4Rot01 c s hcs) x)) := by
    intro w
    obtain ⟨v, hv⟩ := h1 (mfderiv (𝓡 2) (𝓡 2) (s2Rot01 c s hcs).symm
      (s4ADKFibration (s4Rot01 c s hcs x)) w)
    exact ⟨v, hrot2_inj hv⟩
  exact Function.Surjective.of_comp hmid

private theorem detA_identity {x0 x1 x2 x3 : ℝ}
    (h : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 = 1) :
    let R := x0 ^ 2 + x1 ^ 2
    let U := x2 ^ 2 + x3 ^ 2
    let v0 := -x1
    let v1 := x0
    let w0 := -U * x0
    let w1 := -U * x1
    let w2 := R * x2
    let w3 := R * x3
    let a0 := x0 * (U - 1 / 2)
    let a1 := x1 * (U - 1 / 2)
    let a2 := 1 / 4 - R
    let b0 := (U - 1 / 2) * v0
    let b1 := (U - 1 / 2) * v1
    let b2 := -2 * x0 * v0 - 2 * x1 * v1
    let c0 := (U - 1 / 2) * w0 + 2 * x0 * x2 * w2 + 2 * x0 * x3 * w3
    let c1 := (U - 1 / 2) * w1 + 2 * x1 * x2 * w2 + 2 * x1 * x3 * w3
    let c2 := -2 * x0 * w0 - 2 * x1 * w1
    a0 * (b1 * c2 - b2 * c1) - a1 * (b0 * c2 - b2 * c0) + a2 * (b0 * c1 - b1 * c0) =
      R * U * (-(2 * R - 1) * (8 * R ^ 2 - 2 * R + 1)) / 16 := by
  dsimp only
  linear_combination
    ((x0 ^ 2 + x1 ^ 2) * (x2 ^ 2 + x3 ^ 2) *
      (4 * (x0 ^ 2 + x1 ^ 2) ^ 2 + 4 * (x0 ^ 2 + x1 ^ 2) * (x2 ^ 2 + x3 ^ 2) -
        3 * (x0 ^ 2 + x1 ^ 2) + (x2 ^ 2 + x3 ^ 2)) / 4) * h

private theorem detB_identity {x0 x1 x2 x3 t : ℝ}
    (h : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + t ^ 2 = 1) :
    let R := x0 ^ 2 + x1 ^ 2
    let U := x2 ^ 2 + x3 ^ 2
    let a0 := x0 * (U - 1 / 2) - x1 * t
    let a1 := x0 * t + x1 * (U - 1 / 2)
    let a2 := 1 / 4 - R
    let b0 := (U - 1 / 2) * (-x1) - t * x0
    let b1 := t * (-x1) + (U - 1 / 2) * x0
    let b2 := -2 * x0 * (-x1) - 2 * x1 * x0
    let c0 := (U - 1 / 2) * (-t * x0) - t * (-t * x1) - x1 * R
    let c1 := t * (-t * x0) + (U - 1 / 2) * (-t * x1) + x0 * R
    let c2 := -2 * x0 * (-t * x0) - 2 * x1 * (-t * x1)
    a0 * (b1 * c2 - b2 * c1) - a1 * (b0 * c2 - b2 * c0) + a2 * (b0 * c1 - b1 * c0) =
      t * R * (4 * (4 * R + 1) * (1 - U) ^ 2 - 4 * R + 1) / 16 := by
  dsimp only
  linear_combination ((x0 ^ 2 + x1 ^ 2) * t * (4 * (x0 ^ 2 + x1 ^ 2) + 1) / 4) * h

private theorem not_mem_criticalPoints_of_ne_zero (x : Sphere4)
    (hne : x.1 2 ≠ 0 ∨ x.1 3 ≠ 0 ∨ x.1 4 ≠ 0) :
    x ∉ criticalPoints (𝓡 4) (𝓡 2) s4ADKFibration := by
  intro hcrit
  apply hcrit
  have hx : x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2 + x.1 3 ^ 2 + x.1 4 ^ 2 = 1 := by
    rw [← norm_sq_vec5, mem_sphere_zero_iff_norm.mp x.2, one_pow]
  set R : ℝ := x.1 0 ^ 2 + x.1 1 ^ 2
  set U : ℝ := x.1 2 ^ 2 + x.1 3 ^ 2
  set t : ℝ := x.1 4
  have hR_nn : 0 ≤ R := by positivity
  have hU_nn : 0 ≤ U := by positivity
  by_cases hR0 : R = 0
  · have hx0 : x.1 0 = 0 := by nlinarith [sq_nonneg (x.1 1)]
    have hx1 : x.1 1 = 0 := by nlinarith [sq_nonneg (x.1 0)]
    let v₁ : EuclideanSpace ℝ (Fin 5) := vec5 1 0 0 0 0
    let v₂ : EuclideanSpace ℝ (Fin 5) := vec5 0 1 0 0 0
    refine regular_of_det3_ne_zero x (v₁ := v₁) (v₂ := v₂) ?_ ?_ ?_
    · rw [inner_vec5]; simp [v₁, hx0]
    · rw [inner_vec5]; simp [v₂, hx1]
    · rw [fderiv_s4ADKRaw_apply, fderiv_s4ADKRaw_apply]
      have hUt : U + t ^ 2 = 1 := by linarith [sq_eq_zero_iff.mpr hx0, sq_eq_zero_iff.mpr hx1]
      have hdet_eq :
          det3 (s4ADKRaw x.1)
              (vec3 (U - 1 / 2) t 0) (vec3 (-t) (U - 1 / 2) 0) =
            (1 / 4) * ((U - 1 / 2) ^ 2 + t ^ 2) := by
        simp only [det3, s4ADKRaw_zero, s4ADKRaw_one, s4ADKRaw_two, hx0, hx1,
          vec3_zero, vec3_one, vec3_two]
        ring
      have harg1 :
          vec3 ((x.1 2 ^ 2 + x.1 3 ^ 2 - 1 / 2) * v₁ 0 - x.1 4 * v₁ 1 +
              2 * x.1 0 * x.1 2 * v₁ 2 + 2 * x.1 0 * x.1 3 * v₁ 3 - x.1 1 * v₁ 4)
            (x.1 4 * v₁ 0 + (x.1 2 ^ 2 + x.1 3 ^ 2 - 1 / 2) * v₁ 1 +
              2 * x.1 1 * x.1 2 * v₁ 2 + 2 * x.1 1 * x.1 3 * v₁ 3 + x.1 0 * v₁ 4)
            (-2 * x.1 0 * v₁ 0 - 2 * x.1 1 * v₁ 1) = vec3 (U - 1 / 2) t 0 := by
        refine ext_vec3 ?_ ?_ ?_ <;> simp [v₁, U, t, hx0, hx1]
      have harg2 :
          vec3 ((x.1 2 ^ 2 + x.1 3 ^ 2 - 1 / 2) * v₂ 0 - x.1 4 * v₂ 1 +
              2 * x.1 0 * x.1 2 * v₂ 2 + 2 * x.1 0 * x.1 3 * v₂ 3 - x.1 1 * v₂ 4)
            (x.1 4 * v₂ 0 + (x.1 2 ^ 2 + x.1 3 ^ 2 - 1 / 2) * v₂ 1 +
              2 * x.1 1 * x.1 2 * v₂ 2 + 2 * x.1 1 * x.1 3 * v₂ 3 + x.1 0 * v₂ 4)
            (-2 * x.1 0 * v₂ 0 - 2 * x.1 1 * v₂ 1) = vec3 (-t) (U - 1 / 2) 0 := by
        refine ext_vec3 ?_ ?_ ?_ <;> simp [v₂, U, t, hx0, hx1]
      rw [harg1, harg2, hdet_eq]
      have hpos : 0 < (1 / 4 : ℝ) * ((U - 1 / 2) ^ 2 + t ^ 2) := by
        have hid : (U - 1 / 2) ^ 2 + t ^ 2 = (1 / 2 - t ^ 2) ^ 2 + t ^ 2 := by
          rw [show U = 1 - t ^ 2 from by linarith]
          ring
        have hpos2 : 0 < (1 / 2 - t ^ 2) ^ 2 + t ^ 2 := by
          nlinarith [sq_nonneg (t ^ 2 - 1 / 2), sq_nonneg (t ^ 2)]
        linarith
      exact hpos.ne'
  · have hR_pos : 0 < R := lt_of_le_of_ne' hR_nn hR0
    by_cases ht0 : t = 0
    · by_cases hRhalf : R = 1 / 2
      · have hUhalf : U = 1 / 2 := by
          have : t ^ 2 = 0 := by rw [ht0]; norm_num
          linarith
        dsimp only [R, U, t] at hx ht0 hRhalf hUhalf
        let v₁ : EuclideanSpace ℝ (Fin 5) := vec5 0 0 0 0 1
        let v₂ : EuclideanSpace ℝ (Fin 5) := vec5 (x.1 0) (x.1 1) (-x.1 2) (-x.1 3) 0
        refine regular_of_det3_ne_zero x (v₁ := v₁) (v₂ := v₂) ?_ ?_ ?_
        · rw [inner_vec5]; simp [v₁, ht0]
        · rw [inner_vec5]
          simp only [v₂, vec5_zero, vec5_one, vec5_two, vec5_three, vec5_four]
          linear_combination hRhalf - hUhalf
        · rw [fderiv_s4ADKRaw_apply, fderiv_s4ADKRaw_apply]
          have hdet_val :
              det3 (s4ADKRaw x.1)
                  (vec3 (-x.1 1) (x.1 0) 0) (vec3 (-x.1 0) (-x.1 1) (-1)) = -1 / 8 := by
            have hraw : s4ADKRaw x.1 = vec3 0 0 (-1 / 4) := by
              refine ext_vec3 ?_ ?_ ?_ <;>
                simp only [s4ADKRaw_zero, s4ADKRaw_one, s4ADKRaw_two, vec3_zero, vec3_one,
                  vec3_two]
              · rw [hUhalf, ht0]; ring
              · rw [hUhalf, ht0]; ring
              · rw [hRhalf]; ring
            rw [hraw]
            simp only [det3, vec3_zero, vec3_one, vec3_two]
            linear_combination -(1 / 4) * hRhalf
          have hv₁_eq :
              vec3 ((x.1 2 ^ 2 + x.1 3 ^ 2 - 1 / 2) * v₁ 0 - x.1 4 * v₁ 1 +
                  2 * x.1 0 * x.1 2 * v₁ 2 + 2 * x.1 0 * x.1 3 * v₁ 3 - x.1 1 * v₁ 4)
                (x.1 4 * v₁ 0 + (x.1 2 ^ 2 + x.1 3 ^ 2 - 1 / 2) * v₁ 1 +
                  2 * x.1 1 * x.1 2 * v₁ 2 + 2 * x.1 1 * x.1 3 * v₁ 3 + x.1 0 * v₁ 4)
                (-2 * x.1 0 * v₁ 0 - 2 * x.1 1 * v₁ 1) = vec3 (-x.1 1) (x.1 0) 0 := by
            refine ext_vec3 ?_ ?_ ?_ <;> simp [v₁]
          have hv₂_eq :
              vec3 ((x.1 2 ^ 2 + x.1 3 ^ 2 - 1 / 2) * v₂ 0 - x.1 4 * v₂ 1 +
                  2 * x.1 0 * x.1 2 * v₂ 2 + 2 * x.1 0 * x.1 3 * v₂ 3 - x.1 1 * v₂ 4)
                (x.1 4 * v₂ 0 + (x.1 2 ^ 2 + x.1 3 ^ 2 - 1 / 2) * v₂ 1 +
                  2 * x.1 1 * x.1 2 * v₂ 2 + 2 * x.1 1 * x.1 3 * v₂ 3 + x.1 0 * v₂ 4)
                (-2 * x.1 0 * v₂ 0 - 2 * x.1 1 * v₂ 1) = vec3 (-x.1 0) (-x.1 1) (-1) := by
            refine ext_vec3 ?_ ?_ ?_ <;> simp only [v₂, vec5_zero, vec5_one, vec5_two, vec5_three,
              vec5_four, vec3_zero, vec3_one, vec3_two]
            · rw [ht0]; linear_combination -x.1 0 * hUhalf
            · rw [ht0]; linear_combination -x.1 1 * hUhalf
            · linear_combination -2 * hRhalf
          rw [hv₁_eq, hv₂_eq, hdet_val]
          norm_num
      · have hU_pos : 0 < U := by
          rcases hne with h2 | h3 | h4
          · positivity
          · positivity
          · exact absurd ht0 h4
        dsimp only [t] at ht0
        have hRU : x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2 + x.1 3 ^ 2 = 1 := by
          have : x.1 4 ^ 2 = 0 := by rw [ht0]; norm_num
          dsimp only [R, U] at hx ⊢
          linarith
        let v_rot : EuclideanSpace ℝ (Fin 5) := vec5 (-x.1 1) (x.1 0) 0 0 0
        let v_A : EuclideanSpace ℝ (Fin 5) :=
          vec5 (-U * x.1 0) (-U * x.1 1) (R * x.1 2) (R * x.1 3) 0
        refine regular_of_det3_ne_zero x (v₁ := v_rot) (v₂ := v_A) ?_ ?_ ?_
        · rw [inner_vec5]; simp [v_rot]; ring
        · rw [inner_vec5]
          simp only [v_A, vec5_zero, vec5_one, vec5_two, vec5_three, vec5_four]
          ring
        · rw [fderiv_s4ADKRaw_apply, fderiv_s4ADKRaw_apply]
          have hdetA :
              det3 (s4ADKRaw x.1)
                  (vec3 ((x.1 2 ^ 2 + x.1 3 ^ 2 - 1 / 2) * v_rot 0 - x.1 4 * v_rot 1 +
                      2 * x.1 0 * x.1 2 * v_rot 2 + 2 * x.1 0 * x.1 3 * v_rot 3 -
                      x.1 1 * v_rot 4)
                    (x.1 4 * v_rot 0 + (x.1 2 ^ 2 + x.1 3 ^ 2 - 1 / 2) * v_rot 1 +
                      2 * x.1 1 * x.1 2 * v_rot 2 + 2 * x.1 1 * x.1 3 * v_rot 3 +
                      x.1 0 * v_rot 4)
                    (-2 * x.1 0 * v_rot 0 - 2 * x.1 1 * v_rot 1))
                  (vec3 ((x.1 2 ^ 2 + x.1 3 ^ 2 - 1 / 2) * v_A 0 - x.1 4 * v_A 1 +
                      2 * x.1 0 * x.1 2 * v_A 2 + 2 * x.1 0 * x.1 3 * v_A 3 - x.1 1 * v_A 4)
                    (x.1 4 * v_A 0 + (x.1 2 ^ 2 + x.1 3 ^ 2 - 1 / 2) * v_A 1 +
                      2 * x.1 1 * x.1 2 * v_A 2 + 2 * x.1 1 * x.1 3 * v_A 3 + x.1 0 * v_A 4)
                    (-2 * x.1 0 * v_A 0 - 2 * x.1 1 * v_A 1)) =
                R * U * (-(2 * R - 1) * (8 * R ^ 2 - 2 * R + 1)) / 16 := by
            simp only [det3, s4ADKRaw_zero, s4ADKRaw_one, s4ADKRaw_two, v_rot, v_A,
              vec5_zero, vec5_one, vec5_two, vec5_three, vec5_four,
              vec3_zero, vec3_one, vec3_two]
            rw [ht0]
            dsimp only [R, U]
            simpa only [mul_zero, sub_zero, zero_mul, add_zero, zero_add] using detA_identity hRU
          rw [hdetA]
          have hq : 0 < 8 * R ^ 2 - 2 * R + 1 := by
            nlinarith [sq_nonneg (2 * R - 1 / 2)]
          have hm1 : 2 * R - 1 ≠ 0 := by intro he; apply hRhalf; linarith
          exact div_ne_zero
            (mul_ne_zero (mul_ne_zero hR_pos.ne' hU_pos.ne')
              (mul_ne_zero (neg_ne_zero.mpr hm1) hq.ne')) (by norm_num)
    · let v_rot : EuclideanSpace ℝ (Fin 5) := vec5 (-x.1 1) (x.1 0) 0 0 0
      let v_B : EuclideanSpace ℝ (Fin 5) := vec5 (-t * x.1 0) (-t * x.1 1) 0 0 R
      refine regular_of_det3_ne_zero x (v₁ := v_rot) (v₂ := v_B) ?_ ?_ ?_
      · rw [inner_vec5]; simp [v_rot]; ring
      · rw [inner_vec5]
        simp only [v_B, vec5_zero, vec5_one, vec5_two, vec5_three, vec5_four]
        ring
      · rw [fderiv_s4ADKRaw_apply, fderiv_s4ADKRaw_apply]
        have hdetB :
            det3 (s4ADKRaw x.1)
                (vec3 ((x.1 2 ^ 2 + x.1 3 ^ 2 - 1 / 2) * v_rot 0 - x.1 4 * v_rot 1 +
                    2 * x.1 0 * x.1 2 * v_rot 2 + 2 * x.1 0 * x.1 3 * v_rot 3 -
                    x.1 1 * v_rot 4)
                  (x.1 4 * v_rot 0 + (x.1 2 ^ 2 + x.1 3 ^ 2 - 1 / 2) * v_rot 1 +
                    2 * x.1 1 * x.1 2 * v_rot 2 + 2 * x.1 1 * x.1 3 * v_rot 3 +
                    x.1 0 * v_rot 4)
                  (-2 * x.1 0 * v_rot 0 - 2 * x.1 1 * v_rot 1))
                (vec3 ((x.1 2 ^ 2 + x.1 3 ^ 2 - 1 / 2) * v_B 0 - x.1 4 * v_B 1 +
                    2 * x.1 0 * x.1 2 * v_B 2 + 2 * x.1 0 * x.1 3 * v_B 3 - x.1 1 * v_B 4)
                  (x.1 4 * v_B 0 + (x.1 2 ^ 2 + x.1 3 ^ 2 - 1 / 2) * v_B 1 +
                    2 * x.1 1 * x.1 2 * v_B 2 + 2 * x.1 1 * x.1 3 * v_B 3 + x.1 0 * v_B 4)
                  (-2 * x.1 0 * v_B 0 - 2 * x.1 1 * v_B 1)) =
              t * R * (4 * (4 * R + 1) * (1 - U) ^ 2 - 4 * R + 1) / 16 := by
          simp only [det3, s4ADKRaw_zero, s4ADKRaw_one, s4ADKRaw_two, v_rot, v_B,
            vec5_zero, vec5_one, vec5_two, vec5_three, vec5_four,
            vec3_zero, vec3_one, vec3_two]
          dsimp only [R, U, t]
          simpa only [mul_zero, sub_zero, zero_mul, add_zero, zero_add] using detB_identity hx
        rw [hdetB]
        have h1U : R ≤ 1 - U := by linarith [sq_nonneg t]
        have hfac : 0 < 4 * (4 * R + 1) * (1 - U) ^ 2 - 4 * R + 1 := by
          have hsq : R ^ 2 ≤ (1 - U) ^ 2 := by nlinarith
          have hlin : 0 < 16 * R ^ 3 + (2 * R - 1) ^ 2 := by
            have h3 : 0 < R ^ 3 := pow_pos hR_pos 3
            nlinarith [sq_nonneg (2 * R - 1)]
          nlinarith
        exact div_ne_zero
          (mul_ne_zero (mul_ne_zero ht0 hR_pos.ne') hfac.ne') (by norm_num)

/-- Exact characterization of the critical locus of `s4ADKFibration`:
`criticalPoints (𝓡 4) (𝓡 2) s4ADKFibration = {x : Sphere4 | x₂ = 0 ∧ x₃ = 0 ∧ x₄ = 0}`
(a single equatorial circle `S¹ ⊂ S⁴`). -/
-- tier: T2
theorem criticalPoints_s4ADKFibration :
    criticalPoints (𝓡 4) (𝓡 2) s4ADKFibration =
      {x : Sphere4 | x.1 2 = 0 ∧ x.1 3 = 0 ∧ x.1 4 = 0} := by
  ext x
  constructor
  · intro hx
    by_contra hnot
    change ¬ (x.1 2 = 0 ∧ x.1 3 = 0 ∧ x.1 4 = 0) at hnot
    exact not_mem_criticalPoints_of_ne_zero x (by tauto) hx
  · rintro ⟨hx2, hx3, hx4⟩ hsurj
    have hcirc : x.1 0 ^ 2 + x.1 1 ^ 2 = 1 := by
      have hx := mem_sphere_zero_iff_norm.mp x.2
      have hsq : ‖x.1‖ ^ 2 = 1 := by rw [hx]; norm_num
      rw [norm_sq_vec5, hx2, hx3, hx4] at hsq
      linarith
    have hrot : s4Rot01 (x.1 0) (-x.1 1) (by nlinarith) x = s4ADKCritBase := by
      apply Subtype.ext
      refine ext_vec5 ?_ ?_ hx2 hx3 hx4
      · simp only [coe_s4Rot01, vec5_zero, s4ADKCritBase]
        linear_combination hcirc
      · simp only [coe_s4Rot01, vec5_one, s4ADKCritBase]
        ring
    have hsurj0 : Function.Surjective (mfderiv (𝓡 4) (𝓡 2) s4ADKFibration s4ADKCritBase) := by
      rw [← hrot]
      exact surjective_mfderiv_of_s4Rot01_conj (by nlinarith) hsurj
    exact s4ADKCritBase_mem_criticalPoints hsurj0

/-- `s2NorthPole` is not in the critical-value image of `s4ADKFibration`. -/
theorem s2NorthPole_notMem_image_criticalPoints_s4ADKFibration :
    s2NorthPole ∉ s4ADKFibration '' criticalPoints (𝓡 4) (𝓡 2) s4ADKFibration := by
  rintro ⟨x, hx_crit, hfx⟩
  rw [criticalPoints_s4ADKFibration] at hx_crit
  rcases hx_crit with ⟨hx2, hx3, hx4⟩
  obtain ⟨hx0, hx1⟩ := (s4ADKFibration_eq_northPole_iff x).mp hfx
  have hx := mem_sphere_zero_iff_norm.mp x.2
  have hsq : ‖x.1‖ ^ 2 = 1 := by rw [hx]; norm_num
  rw [norm_sq_vec5, hx0, hx1, hx2, hx3, hx4] at hsq
  norm_num at hsq

/-- `s2NorthPole` is a regular value of `s4ADKFibration`. -/
theorem isRegularValue_s4ADKFibration_northPole :
    TauCeti.IsRegularValue (𝓡 4) (𝓡 2) s4ADKFibration s2NorthPole := by
  rw [TauCeti.isRegularValue_iff_notMem_image]
  simp_rw [TauCeti.isRegularPoint_iff]
  exact s2NorthPole_notMem_image_criticalPoints_s4ADKFibration

/-- `s2SouthPole` is not in the critical-value image of `s4ADKFibration`. -/
theorem s2SouthPole_notMem_image_criticalPoints_s4ADKFibration :
    s2SouthPole ∉ s4ADKFibration '' criticalPoints (𝓡 4) (𝓡 2) s4ADKFibration := by
  rintro ⟨x, hx_crit, hfx⟩
  rw [criticalPoints_s4ADKFibration] at hx_crit
  rcases hx_crit with ⟨hx2, hx3, -⟩
  obtain ⟨-, hu, -⟩ := (s4ADKFibration_eq_southPole_iff x).mp hfx
  rw [hx2, hx3] at hu
  norm_num at hu

/-- `s2SouthPole` is a regular value of `s4ADKFibration`. -/
theorem isRegularValue_s4ADKFibration_southPole :
    TauCeti.IsRegularValue (𝓡 4) (𝓡 2) s4ADKFibration s2SouthPole := by
  rw [TauCeti.isRegularValue_iff_notMem_image]
  simp_rw [TauCeti.isRegularPoint_iff]
  exact s2SouthPole_notMem_image_criticalPoints_s4ADKFibration

/-- Model space `Fin (finrank ℝ ℝ⁴ - finrank ℝ ℝ²) → ℝ` for `TauCeti.regularFiberChartedSpace`
of `s4ADKFibration : Sphere4 → Sphere2`. -/
noncomputable abbrev ADKRegularFiberSpace : Type :=
  Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) - Module.finrank ℝ EuclideanPlane) → ℝ

/-- Boundaryless model with corners on `ADKRegularFiberSpace`. -/
noncomputable abbrev ADKRegularFiberModel :
    ModelWithCorners ℝ ADKRegularFiberSpace ADKRegularFiberSpace :=
  𝓘(ℝ, ADKRegularFiberSpace)

/-- Embedded regular-fiber `ChartedSpace` instance on `{x : Sphere4 // s4ADKFibration x =
s2NorthPole}` via `TauCeti.regularFiberChartedSpace`. -/
noncomputable instance instChartedSpaceS4ADKNorthFiber :
    ChartedSpace ADKRegularFiberSpace {x : Sphere4 // s4ADKFibration x = s2NorthPole} :=
  TauCeti.regularFiberChartedSpace (by simp : (1 : ℕ∞ω) ≤ ∞) contMDiff_s4ADKFibration
    BoundarylessManifold.isInteriorPoint isRegularValue_s4ADKFibration_northPole

/-- Smooth manifold instance on `{x : Sphere4 // s4ADKFibration x = s2NorthPole}` via
`TauCeti.isManifold_regularFiber`. -/
instance instIsManifoldS4ADKNorthFiber :
    IsManifold ADKRegularFiberModel ∞ {x : Sphere4 // s4ADKFibration x = s2NorthPole} :=
  TauCeti.isManifold_regularFiber (by simp : (1 : ℕ∞ω) ≤ ∞) contMDiff_s4ADKFibration
    BoundarylessManifold.isInteriorPoint isRegularValue_s4ADKFibration_northPole

/-- Embedded regular-fiber `ChartedSpace` instance on `{x : Sphere4 // s4ADKFibration x =
s2SouthPole}` via `TauCeti.regularFiberChartedSpace`. -/
noncomputable instance instChartedSpaceS4ADKTorusFiber :
    ChartedSpace ADKRegularFiberSpace {x : Sphere4 // s4ADKFibration x = s2SouthPole} :=
  TauCeti.regularFiberChartedSpace (by simp : (1 : ℕ∞ω) ≤ ∞) contMDiff_s4ADKFibration
    BoundarylessManifold.isInteriorPoint isRegularValue_s4ADKFibration_southPole

/-- Smooth manifold instance on `{x : Sphere4 // s4ADKFibration x = s2SouthPole}` via
`TauCeti.isManifold_regularFiber`. -/
instance instIsManifoldS4ADKTorusFiber :
    IsManifold ADKRegularFiberModel ∞ {x : Sphere4 // s4ADKFibration x = s2SouthPole} :=
  TauCeti.isManifold_regularFiber (by simp : (1 : ℕ∞ω) ≤ ∞) contMDiff_s4ADKFibration
    BoundarylessManifold.isInteriorPoint isRegularValue_s4ADKFibration_southPole

/-- Explicit $C^\infty$ diffeomorphism from `Sphere2` onto the embedded regular fiber
`{x : Sphere4 // s4ADKFibration x = s2NorthPole}` (`SC-R6b` smooth $S^2$ fiber witness). -/
-- tier: T2
noncomputable def s4ADKNorthFiberDiffeomorph :
    Sphere2 ≃ₘ⟮𝓡 2, ADKRegularFiberModel⟯ {x : Sphere4 // s4ADKFibration x = s2NorthPole} where
  toEquiv := s4ADKNorthFiberHomeomorph.toEquiv
  contMDiff_toFun := by
    have himm :=
      (TauCeti.isSmoothEmbedding_coe_regularFiber (by simp : (1 : ℕ∞ω) ≤ ∞)
        contMDiff_s4ADKFibration BoundarylessManifold.isInteriorPoint
        isRegularValue_s4ADKFibration_northPole).isImmersion
    rw [ContMDiff.iff_comp_isImmersion himm]
    refine ⟨s4ADKNorthFiberHomeomorph.continuous_toFun, ?_⟩
    have hraw : ContMDiff (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 5)) ∞
        (fun y : Sphere2 ↦ vec5 0 0 (y.1 0) (y.1 1) (y.1 2)) :=
      (contDiff_vec5 contDiff_const contDiff_const (euclidProj 0).contDiff
        (euclidProj 1).contDiff (euclidProj 2).contDiff).contMDiff.comp contMDiff_coe_sphere
    exact hraw.codRestrict_sphere _
  contMDiff_invFun := by
    have hcoe : ContMDiff ADKRegularFiberModel 𝓘(ℝ, EuclideanSpace ℝ (Fin 5)) ∞
        (fun x : {x : Sphere4 // s4ADKFibration x = s2NorthPole} ↦ x.1.1) :=
      contMDiff_coe_sphere.comp
        (TauCeti.isSmoothEmbedding_coe_regularFiber (by simp : (1 : ℕ∞ω) ≤ ∞)
          contMDiff_s4ADKFibration BoundarylessManifold.isInteriorPoint
          isRegularValue_s4ADKFibration_northPole).contMDiff
    have hraw : ContMDiff ADKRegularFiberModel 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
        (fun x : {x : Sphere4 // s4ADKFibration x = s2NorthPole} ↦
          vec3 (x.1.1 2) (x.1.1 3) (x.1.1 4)) :=
      (contDiff_vec3 (euclidProj 2).contDiff (euclidProj 3).contDiff
        (euclidProj 4).contDiff).contMDiff.comp hcoe
    exact hraw.codRestrict_sphere _

/-- Explicit $C^\infty$ diffeomorphism from `S¹ × S¹` (`Metric.sphere 0 1 × Metric.sphere 0 1`)
onto the embedded Clifford torus regular fiber `{x : Sphere4 // s4ADKFibration x = s2SouthPole}`.
-/
-- tier: T2
noncomputable def s4ADKTorusProdFiberDiffeomorph :
    (Metric.sphere (0 : EuclideanPlane) 1 × Metric.sphere (0 : EuclideanPlane) 1)
      ≃ₘ⟮(𝓡 1).prod (𝓡 1), ADKRegularFiberModel⟯
      {x : Sphere4 // s4ADKFibration x = s2SouthPole} where
  toEquiv := s4ADKTorusFiberHomeomorph.toEquiv
  contMDiff_toFun := by
    have himm :=
      (TauCeti.isSmoothEmbedding_coe_regularFiber (by simp : (1 : ℕ∞ω) ≤ ∞)
        contMDiff_s4ADKFibration BoundarylessManifold.isInteriorPoint
        isRegularValue_s4ADKFibration_southPole).isImmersion
    rw [ContMDiff.iff_comp_isImmersion himm]
    refine ⟨s4ADKTorusFiberHomeomorph.continuous_toFun, ?_⟩
    have hc1 : ContMDiff ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, EuclideanPlane) ∞
        (fun uv : Metric.sphere (0 : EuclideanPlane) 1 × Metric.sphere (0 : EuclideanPlane) 1 ↦
          uv.1.1) :=
      contMDiff_coe_sphere.comp contMDiff_fst
    have hc2 : ContMDiff ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, EuclideanPlane) ∞
        (fun uv : Metric.sphere (0 : EuclideanPlane) 1 × Metric.sphere (0 : EuclideanPlane) 1 ↦
          uv.2.1) :=
      contMDiff_coe_sphere.comp contMDiff_snd
    have hp1 (k : Fin 2) : ContMDiff ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞
        (fun uv : Metric.sphere (0 : EuclideanPlane) 1 × Metric.sphere (0 : EuclideanPlane) 1 ↦
          (Real.sqrt 2)⁻¹ * uv.1.1 k) :=
      (contDiff_const.mul (euclidProj k).contDiff).contMDiff.comp hc1
    have hp2 (k : Fin 2) : ContMDiff ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞
        (fun uv : Metric.sphere (0 : EuclideanPlane) 1 × Metric.sphere (0 : EuclideanPlane) 1 ↦
          (Real.sqrt 2)⁻¹ * uv.2.1 k) :=
      (contDiff_const.mul (euclidProj k).contDiff).contMDiff.comp hc2
    have hpi : ContMDiff ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, Fin 5 → ℝ) ∞
        (fun uv : Metric.sphere (0 : EuclideanPlane) 1 × Metric.sphere (0 : EuclideanPlane) 1 ↦
          ![(Real.sqrt 2)⁻¹ * uv.1.1 0, (Real.sqrt 2)⁻¹ * uv.1.1 1,
            (Real.sqrt 2)⁻¹ * uv.2.1 0, (Real.sqrt 2)⁻¹ * uv.2.1 1, 0]) := by
      refine contMDiff_pi_module_iff.mpr fun i ↦ ?_
      fin_cases i
      · exact hp1 0
      · exact hp1 1
      · exact hp2 0
      · exact hp2 1
      · exact contMDiff_const
    have hraw : ContMDiff ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 5)) ∞
        (fun uv : Metric.sphere (0 : EuclideanPlane) 1 × Metric.sphere (0 : EuclideanPlane) 1 ↦
          vec5 ((Real.sqrt 2)⁻¹ * uv.1.1 0) ((Real.sqrt 2)⁻¹ * uv.1.1 1)
            ((Real.sqrt 2)⁻¹ * uv.2.1 0) ((Real.sqrt 2)⁻¹ * uv.2.1 1) 0) :=
      (EuclideanSpace.equiv (Fin 5) ℝ).symm.contDiff.contMDiff.comp hpi
    exact hraw.codRestrict_sphere _
  contMDiff_invFun := by
    have hcoe : ContMDiff ADKRegularFiberModel 𝓘(ℝ, EuclideanSpace ℝ (Fin 5)) ∞
        (fun x : {x : Sphere4 // s4ADKFibration x = s2SouthPole} ↦ x.1.1) :=
      contMDiff_coe_sphere.comp
        (TauCeti.isSmoothEmbedding_coe_regularFiber (by simp : (1 : ℕ∞ω) ≤ ∞)
          contMDiff_s4ADKFibration BoundarylessManifold.isInteriorPoint
          isRegularValue_s4ADKFibration_southPole).contMDiff
    have hx (k : Fin 5) : ContMDiff ADKRegularFiberModel 𝓘(ℝ, ℝ) ∞
        (fun x : {x : Sphere4 // s4ADKFibration x = s2SouthPole} ↦ Real.sqrt 2 * x.1.1 k) :=
      (contDiff_const.mul (euclidProj k).contDiff).contMDiff.comp hcoe
    have h1_pi : ContMDiff ADKRegularFiberModel 𝓘(ℝ, Fin 2 → ℝ) ∞
        (fun x : {x : Sphere4 // s4ADKFibration x = s2SouthPole} ↦
          ![Real.sqrt 2 * x.1.1 0, Real.sqrt 2 * x.1.1 1]) := by
      refine contMDiff_pi_module_iff.mpr fun i ↦ ?_
      fin_cases i <;> [exact hx 0; exact hx 1]
    have h2_pi : ContMDiff ADKRegularFiberModel 𝓘(ℝ, Fin 2 → ℝ) ∞
        (fun x : {x : Sphere4 // s4ADKFibration x = s2SouthPole} ↦
          ![Real.sqrt 2 * x.1.1 2, Real.sqrt 2 * x.1.1 3]) := by
      refine contMDiff_pi_module_iff.mpr fun i ↦ ?_
      fin_cases i <;> [exact hx 2; exact hx 3]
    have h1_raw : ContMDiff ADKRegularFiberModel 𝓘(ℝ, EuclideanPlane) ∞
        (fun x : {x : Sphere4 // s4ADKFibration x = s2SouthPole} ↦
          vec2 (Real.sqrt 2 * x.1.1 0) (Real.sqrt 2 * x.1.1 1)) :=
      (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.contMDiff.comp h1_pi
    have h2_raw : ContMDiff ADKRegularFiberModel 𝓘(ℝ, EuclideanPlane) ∞
        (fun x : {x : Sphere4 // s4ADKFibration x = s2SouthPole} ↦
          vec2 (Real.sqrt 2 * x.1.1 2) (Real.sqrt 2 * x.1.1 3)) :=
      (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.contMDiff.comp h2_pi
    exact (h1_raw.codRestrict_sphere _).prodMk (h2_raw.codRestrict_sphere _)

/-- Smooth 2-torus `S¹ × S¹` (`Metric.sphere 0 1 × Metric.sphere 0 1`) equipped with a
`ChartedSpace EuclideanPlane` and `IsManifold (𝓡 2) ∞` structure so it can serve directly as the
`Fiber` manifold of `BrokenLefschetzFibration`. -/
@[ext]
structure Torus2 where
  /-- First unit circle factor `S¹ ⊂ ℝ²`. -/
  fst : Metric.sphere (0 : EuclideanPlane) 1
  /-- Second unit circle factor `S¹ ⊂ ℝ²`. -/
  snd : Metric.sphere (0 : EuclideanPlane) 1

/-- Canonical bijection `Torus2 ≃ S¹ × S¹`. -/
def Torus2.toProdEquiv :
    Torus2 ≃ (Metric.sphere (0 : EuclideanPlane) 1 × Metric.sphere (0 : EuclideanPlane) 1) where
  toFun t := (t.fst, t.snd)
  invFun uv := ⟨uv.1, uv.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instTopologicalSpaceTorus2 : TopologicalSpace Torus2 :=
  TopologicalSpace.induced Torus2.toProdEquiv inferInstance

/-- Canonical homeomorphism `Torus2 ≃ₜ S¹ × S¹`. -/
def Torus2.toProdHomeomorph :
    Torus2 ≃ₜ (Metric.sphere (0 : EuclideanPlane) 1 × Metric.sphere (0 : EuclideanPlane) 1) where
  toEquiv := Torus2.toProdEquiv
  continuous_toFun := continuous_induced_dom
  continuous_invFun :=
    continuous_induced_rng.mpr
      (continuous_id :
        Continuous (@id (Metric.sphere (0 : EuclideanPlane) 1 ×
          Metric.sphere (0 : EuclideanPlane) 1)))

instance instT2SpaceTorus2 : T2Space Torus2 :=
  Torus2.toProdHomeomorph.isEmbedding.t2Space

instance instCompactSpaceTorus2 : CompactSpace Torus2 :=
  Torus2.toProdHomeomorph.symm.compactSpace

instance instNonemptyTorus2 : Nonempty Torus2 :=
  have hc : vec2 1 0 ∈ Metric.sphere (0 : EuclideanPlane) 1 := by
    rw [mem_sphere_zero_iff_norm]
    have hsq : ‖vec2 1 0‖ ^ 2 = 1 := by rw [norm_sq_plane]; norm_num
    nlinarith [norm_nonneg (vec2 1 0)]
  ⟨⟨⟨vec2 1 0, hc⟩, ⟨vec2 1 0, hc⟩⟩⟩

/-- Product circle type `S¹ × S¹` underlying `Torus2`. -/
abbrev Torus1Prod : Type :=
  Metric.sphere (0 : EuclideanPlane) 1 × Metric.sphere (0 : EuclideanPlane) 1

/-- Vector-space model `ℝ¹ × ℝ¹` of `(𝓡 1).prod (𝓡 1)`. -/
abbrev Torus1ModelVec : Type :=
  EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)

/-- Vector-space-charted copy of `S¹ × S¹` via `TauCeti.BoundarylessModel`. -/
abbrev Torus1Boundaryless : Type :=
  TauCeti.BoundarylessModel ((𝓡 1).prod (𝓡 1)) Torus1Prod

/-- Smoothness of `(pq : ℝ¹ × ℝ¹) ↦ vec2 (pq.1 0) (pq.2 0)`. -/
theorem contDiff_torusModelVecToPlane :
    ContDiff ℝ ∞ (fun pq : Torus1ModelVec ↦ vec2 (pq.1 0) (pq.2 0)) :=
  contDiff_vec2
    ((euclidProj (0 : Fin 1)).contDiff.comp contDiff_fst)
    ((euclidProj (0 : Fin 1)).contDiff.comp contDiff_snd)

/-- Smoothness of the inverse linear map `ℝ² → ℝ¹ × ℝ¹`. -/
theorem contDiff_planeToTorusModelVec :
    ContDiff ℝ ∞ (fun w : EuclideanPlane ↦
      (((EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ w 0),
        (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ w 1)) : Torus1ModelVec)) :=
  ((EuclideanSpace.equiv (Fin 1) ℝ).symm.contDiff.comp
      (contDiff_pi.mpr fun _ ↦ (euclidProj (0 : Fin 2)).contDiff)).prodMk
    ((EuclideanSpace.equiv (Fin 1) ℝ).symm.contDiff.comp
      (contDiff_pi.mpr fun _ ↦ (euclidProj (1 : Fin 2)).contDiff))

/-- Smooth linear model diffeomorphism `ℝ¹ × ℝ¹ ≃ₘ ℝ²` for recharting `Torus2`. -/
noncomputable def torusModelVecDiffeomorph :
    Torus1ModelVec ≃ₘ⟮𝓘(ℝ, Torus1ModelVec), 𝓡 2⟯ EuclideanPlane where
  toFun pq := vec2 (pq.1 0) (pq.2 0)
  invFun w :=
    ((EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ w 0),
      (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ w 1))
  left_inv pq :=
    Prod.ext (PiLp.ext fun i ↦ by fin_cases i; rfl) (PiLp.ext fun i ↦ by fin_cases i; rfl)
  right_inv w := ext_vec2 rfl rfl
  contMDiff_toFun := contDiff_torusModelVecToPlane.contMDiff
  contMDiff_invFun := contDiff_planeToTorusModelVec.contMDiff

/-- Canonical homeomorphism `Torus2 ≃ₜ Torus1Boundaryless`. -/
noncomputable def Torus2.toBoundarylessHomeomorph : Torus2 ≃ₜ Torus1Boundaryless :=
  Torus2.toProdHomeomorph.trans
    (TauCeti.BoundarylessModel.homeomorph ((𝓡 1).prod (𝓡 1)) Torus1Prod)

/-- Auxiliary `EuclideanPlane`-valued `ChartedSpace` on `Torus1Boundaryless`. -/
@[instance_reducible]
noncomputable def torus1BoundarylessPlaneChartedSpace :
    ChartedSpace EuclideanPlane Torus1Boundaryless :=
  letI : ChartedSpace EuclideanPlane Torus1ModelVec :=
    torusModelVecDiffeomorph.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  ChartedSpace.comp EuclideanPlane Torus1ModelVec Torus1Boundaryless

noncomputable instance instChartedSpaceTorus2 : ChartedSpace EuclideanPlane Torus2 :=
  letI := torus1BoundarylessPlaneChartedSpace
  Torus2.toBoundarylessHomeomorph.pullbackChartedSpace

instance instIsManifoldTorus2 : IsManifold (𝓡 2) ∞ Torus2 := by
  let _ : ChartedSpace EuclideanPlane Torus1Boundaryless := torus1BoundarylessPlaneChartedSpace
  have _ : IsManifold (𝓡 2) ∞ Torus1Boundaryless :=
    torusModelVecDiffeomorph.isManifold_chartedSpaceComp Torus1Boundaryless
  exact Torus2.toBoundarylessHomeomorph.pullback_isManifold (𝓡 2) ∞

private theorem chartAt_torus2 (t : Torus2) :
    chartAt EuclideanPlane t =
      Torus2.toBoundarylessHomeomorph.transOpenPartialHomeomorph
        (chartAt Torus1ModelVec (Torus2.toBoundarylessHomeomorph t) ≫ₕ
          torusModelVecDiffeomorph.toHomeomorph.toOpenPartialHomeomorph) := by
  let c₀ : OpenPartialHomeomorph Torus1Boundaryless Torus1ModelVec :=
    chartAt Torus1ModelVec (Torus2.toBoundarylessHomeomorph t)
  let eL := torusModelVecDiffeomorph.toHomeomorph.toOpenPartialHomeomorph
  let _ : ChartedSpace EuclideanPlane Torus1ModelVec := eL.singletonChartedSpace (by simp [eL])
  let _ : ChartedSpace EuclideanPlane Torus1Boundaryless :=
    ChartedSpace.comp EuclideanPlane Torus1ModelVec Torus1Boundaryless
  change Torus2.toBoundarylessHomeomorph.transOpenPartialHomeomorph
      (chartAt EuclideanPlane (Torus2.toBoundarylessHomeomorph t)) =
    Torus2.toBoundarylessHomeomorph.transOpenPartialHomeomorph (c₀ ≫ₕ eL)
  congr 1

/-- Smooth diffeomorphism `Torus2 ≃ₘ Torus1Boundaryless`. -/
noncomputable def torus2ToBoundarylessDiffeomorph :
    Torus2 ≃ₘ⟮𝓡 2, 𝓘(ℝ, Torus1ModelVec)⟯ Torus1Boundaryless where
  toEquiv := Torus2.toBoundarylessHomeomorph.toEquiv
  contMDiff_toFun t := by
    rw [contMDiffAt_iff]
    refine ⟨Torus2.toBoundarylessHomeomorph.continuous.continuousAt, ?_⟩
    let b : Torus1Boundaryless := Torus2.toBoundarylessHomeomorph t
    let c : OpenPartialHomeomorph Torus1Boundaryless Torus1ModelVec :=
      chartAt Torus1ModelVec b
    have heq : ∀ w ∈ (extChartAt (𝓡 2) t).target,
        (extChartAt 𝓘(ℝ, Torus1ModelVec) b ∘ Torus2.toBoundarylessHomeomorph ∘
            (extChartAt (𝓡 2) t).symm) w =
          torusModelVecDiffeomorph.symm w := by
      intro w hw
      have hw' : torusModelVecDiffeomorph.symm w ∈ c.target := by
        simp only [extChartAt, OpenPartialHomeomorph.extend, chartAt_torus2,
          modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl,
          Homeomorph.transOpenPartialHomeomorph_target, OpenPartialHomeomorph.trans_target,
          Homeomorph.toOpenPartialHomeomorph_target, univ_inter, mem_preimage,
          Homeomorph.toOpenPartialHomeomorph_symm_apply] at hw
        exact hw
      simp only [Function.comp_apply, extChartAt, OpenPartialHomeomorph.extend, chartAt_torus2,
        modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl,
        OpenPartialHomeomorph.coe_toPartialEquiv, OpenPartialHomeomorph.coe_toPartialEquiv_symm,
        Homeomorph.transOpenPartialHomeomorph_symm_apply, Homeomorph.apply_symm_apply,
        OpenPartialHomeomorph.coe_trans_symm, Homeomorph.toOpenPartialHomeomorph_symm_apply]
      exact c.right_inv hw'
    exact (contDiff_planeToTorusModelVec.contDiffAt.congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (extChartAt_target_mem_nhds t) heq)).contDiffWithinAt
  contMDiff_invFun b := by
    rw [contMDiffAt_iff]
    refine ⟨Torus2.toBoundarylessHomeomorph.symm.continuous.continuousAt, ?_⟩
    let t : Torus2 := Torus2.toBoundarylessHomeomorph.symm b
    have htb : Torus2.toBoundarylessHomeomorph t = b :=
      Torus2.toBoundarylessHomeomorph.apply_symm_apply b
    let c : OpenPartialHomeomorph Torus1Boundaryless Torus1ModelVec :=
      chartAt Torus1ModelVec b
    have heq : ∀ pq ∈ (extChartAt 𝓘(ℝ, Torus1ModelVec) b).target,
        (extChartAt (𝓡 2) t ∘ Torus2.toBoundarylessHomeomorph.symm ∘
            (extChartAt 𝓘(ℝ, Torus1ModelVec) b).symm) pq =
          torusModelVecDiffeomorph pq := by
      intro pq hpq
      have hpq' : pq ∈ c.target := by
        simpa only [extChartAt, OpenPartialHomeomorph.extend,
          modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl] using hpq
      have hchart_t :
          chartAt EuclideanPlane t =
            Torus2.toBoundarylessHomeomorph.transOpenPartialHomeomorph
              (c ≫ₕ torusModelVecDiffeomorph.toHomeomorph.toOpenPartialHomeomorph) := by
        simpa only [c, htb] using chartAt_torus2 t
      simp only [Function.comp_apply, extChartAt, OpenPartialHomeomorph.extend, hchart_t,
        modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl,
        OpenPartialHomeomorph.coe_toPartialEquiv, OpenPartialHomeomorph.coe_toPartialEquiv_symm,
        Homeomorph.transOpenPartialHomeomorph_apply, Homeomorph.apply_symm_apply,
        OpenPartialHomeomorph.coe_trans, Homeomorph.toOpenPartialHomeomorph_apply]
      exact congrArg torusModelVecDiffeomorph (c.right_inv hpq')
    exact (contDiff_torusModelVecToPlane.contDiffAt.congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (extChartAt_target_mem_nhds b) heq)).contDiffWithinAt

@[simp]
private theorem coe_torus2ToBoundarylessDiffeomorph (t : Torus2) :
    torus2ToBoundarylessDiffeomorph t = Torus2.toBoundarylessHomeomorph t := rfl

@[simp]
private theorem coe_torus2ToBoundarylessDiffeomorph_symm (b : Torus1Boundaryless) :
    torus2ToBoundarylessDiffeomorph.symm b = Torus2.toBoundarylessHomeomorph.symm b := rfl

/-- Canonical $C^\infty$ diffeomorphism `Torus2 ≃ₘ S¹ × S¹` between `Torus2` (modeled on `𝓡 2`)
and the product of unit circles (modeled on `(𝓡 1).prod (𝓡 1)`). -/
-- tier: T2
noncomputable def Torus2.toProdDiffeomorph :
    Torus2 ≃ₘ⟮𝓡 2, (𝓡 1).prod (𝓡 1)⟯ Torus1Prod :=
  torus2ToBoundarylessDiffeomorph.trans
    (TauCeti.BoundarylessModel.diffeomorph ((𝓡 1).prod (𝓡 1)) (M := Torus1Prod) ∞).symm

@[simp]
private theorem coe_torus2_toProdDiffeomorph (t : Torus2) :
    Torus2.toProdDiffeomorph t = (t.fst, t.snd) := by
  change (TauCeti.BoundarylessModel.diffeomorph ((𝓡 1).prod (𝓡 1)) (M := Torus1Prod) ∞).symm
      (torus2ToBoundarylessDiffeomorph t) =
    (t.fst, t.snd)
  rw [TauCeti.BoundarylessModel.coe_diffeomorph_symm, coe_torus2ToBoundarylessDiffeomorph]
  change (TauCeti.BoundarylessModel.homeomorph ((𝓡 1).prod (𝓡 1)) Torus1Prod).symm
      ((TauCeti.BoundarylessModel.homeomorph ((𝓡 1).prod (𝓡 1)) Torus1Prod)
        (Torus2.toProdHomeomorph t)) =
    (t.fst, t.snd)
  rw [Homeomorph.symm_apply_apply]
  rfl

@[simp]
private theorem coe_torus2_toProdDiffeomorph_symm (uv : Torus1Prod) :
    Torus2.toProdDiffeomorph.symm uv = ⟨uv.1, uv.2⟩ := by
  change torus2ToBoundarylessDiffeomorph.symm
      (TauCeti.BoundarylessModel.diffeomorph ((𝓡 1).prod (𝓡 1)) (M := Torus1Prod) ∞ uv) =
    ⟨uv.1, uv.2⟩
  rw [TauCeti.BoundarylessModel.coe_diffeomorph, coe_torus2ToBoundarylessDiffeomorph_symm]
  change Torus2.toProdHomeomorph.symm
      ((TauCeti.BoundarylessModel.homeomorph ((𝓡 1).prod (𝓡 1)) Torus1Prod).symm
        ((TauCeti.BoundarylessModel.homeomorph ((𝓡 1).prod (𝓡 1)) Torus1Prod) uv)) =
    ⟨uv.1, uv.2⟩
  rw [Homeomorph.symm_apply_apply]
  rfl

/-- Smoothness of `(t : Torus2) ↦ (t.fst : EuclideanPlane)`. -/
theorem Torus2.contMDiff_coe_fst :
    ContMDiff (𝓡 2) 𝓘(ℝ, EuclideanPlane) ∞ (fun t : Torus2 ↦ (t.fst : EuclideanPlane)) := by
  have h := (contMDiff_coe_sphere.comp contMDiff_fst).comp Torus2.toProdDiffeomorph.contMDiff
  exact h.congr fun t ↦ by simp

/-- Smoothness of `(t : Torus2) ↦ (t.snd : EuclideanPlane)`. -/
theorem Torus2.contMDiff_coe_snd :
    ContMDiff (𝓡 2) 𝓘(ℝ, EuclideanPlane) ∞ (fun t : Torus2 ↦ (t.snd : EuclideanPlane)) := by
  have h := (contMDiff_coe_sphere.comp contMDiff_snd).comp Torus2.toProdDiffeomorph.contMDiff
  exact h.congr fun t ↦ by simp

/-- Explicit $C^\infty$ diffeomorphism from `Torus2` (`S¹ × S¹` modeled on `𝓡 2`) onto the embedded
Clifford torus regular fiber `{x : Sphere4 // s4ADKFibration x = s2SouthPole}` (`SC-R6b` smooth
$T^2$ fiber witness). -/
-- tier: T2
noncomputable def s4ADKTorusFiberDiffeomorph :
    Torus2 ≃ₘ⟮𝓡 2, ADKRegularFiberModel⟯ {x : Sphere4 // s4ADKFibration x = s2SouthPole} :=
  Torus2.toProdDiffeomorph.trans s4ADKTorusProdFiberDiffeomorph

end CriticalPoints

/-! ## 3. Indefinite Quadratic Fold Local Normal Form Along the Critical Circle -/

section IndefiniteFoldLocalNormalForm

/-- Transport `IsLocallyModeledOn` backwards along equivariant smooth diffeomorphisms
`Φ : M' ≃ₘ M` and `Ψ : Base' ≃ₘ Base`. -/
private theorem isLocallyModeledOn_of_diffeomorph_conj
    {E_M H_M E_B H_B M Base E_M' H_M' E_B' H_B' M' Base' : Type*}
    [NormedAddCommGroup E_M] [NormedSpace ℝ E_M] [TopologicalSpace H_M]
    {I_M : ModelWithCorners ℝ E_M H_M}
    [NormedAddCommGroup E_B] [NormedSpace ℝ E_B] [TopologicalSpace H_B]
    {I_B : ModelWithCorners ℝ E_B H_B}
    [TopologicalSpace M] [ChartedSpace H_M M]
    [TopologicalSpace Base] [ChartedSpace H_B Base]
    [NormedAddCommGroup E_M'] [NormedSpace ℝ E_M'] [TopologicalSpace H_M']
    {I_M' : ModelWithCorners ℝ E_M' H_M'}
    [NormedAddCommGroup E_B'] [NormedSpace ℝ E_B'] [TopologicalSpace H_B']
    {I_B' : ModelWithCorners ℝ E_B' H_B'}
    [TopologicalSpace M'] [ChartedSpace H_M' M']
    [TopologicalSpace Base'] [ChartedSpace H_B' Base']
    (Φ : M' ≃ₘ⟮I_M', I_M⟯ M) (Ψ : Base' ≃ₘ⟮I_B', I_B⟯ Base)
    {f' : M' → Base'} {f : M → Base} (hcomm : ∀ x : M', Ψ (f' x) = f (Φ x))
    {p' : M'} {model : EuclideanSpace ℝ (Fin 4) → EuclideanPlane}
    {q₀ : EuclideanSpace ℝ (Fin 4)}
    (hmodel : IsLocallyModeledOn I_M I_B f (Φ p') model q₀) :
    IsLocallyModeledOn I_M' I_B' f' p' model q₀ := by
  rcases hmodel with ⟨φ, ψ, hpφ, hfpψ, hφ0, hψ0, hmatch⟩
  let φ' : PartialDiffeomorph I_M' (𝓡 4) M' (EuclideanSpace ℝ (Fin 4)) ∞ :=
    Φ.toPartialDiffeomorph.trans φ
  let ψ' : PartialDiffeomorph I_B' (𝓡 2) Base' EuclideanPlane ∞ :=
    Ψ.toPartialDiffeomorph.trans ψ
  refine ⟨φ', ψ', ?_, ?_, ?_, ?_, ?_⟩
  · simpa [φ', PartialDiffeomorph.trans_source, Diffeomorph.toPartialDiffeomorph_toPartialEquiv]
      using hpφ
  · simpa [ψ', PartialDiffeomorph.trans_source, Diffeomorph.toPartialDiffeomorph_toPartialEquiv,
      hcomm] using hfpψ
  · simpa [φ', PartialDiffeomorph.coe_trans] using hφ0
  · simpa [ψ', PartialDiffeomorph.coe_trans, hcomm] using hψ0
  · intro q hq
    simp only [φ', PartialDiffeomorph.trans_source,
      Diffeomorph.toPartialDiffeomorph_toPartialEquiv, Set.mem_inter_iff,
      Set.mem_preimage] at hq
    obtain ⟨hmem, heq⟩ := hmatch (Φ q) hq.2
    refine ⟨?_, ?_⟩
    · simpa [ψ', PartialDiffeomorph.trans_source,
        Diffeomorph.toPartialDiffeomorph_toPartialEquiv, hcomm] using hmem
    · simpa [φ', ψ', PartialDiffeomorph.coe_trans, hcomm] using heq

private noncomputable def s4EastHemisphereOpen : Opens Sphere4 :=
  ⟨{x : Sphere4 | 0 < x.1 0},
    isOpen_lt continuous_const ((euclidProj (0 : Fin 5)).continuous.comp continuous_subtype_val)⟩

private theorem s4ADKCritBase_mem_east : s4ADKCritBase ∈ s4EastHemisphereOpen.1 := by
  change (0 : ℝ) < (s4ADKCritBase.1 0)
  simp [s4ADKCritBase]

private noncomputable def r4UnitBallOpen : Opens (EuclideanSpace ℝ (Fin 4)) :=
  ⟨Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) 1, Metric.isOpen_ball⟩

private theorem zero_mem_r4UnitBallOpen : (0 : EuclideanSpace ℝ (Fin 4)) ∈ r4UnitBallOpen.1 := by
  simp [r4UnitBallOpen]

private noncomputable def s4EastHemisphereDiffeomorph :
    s4EastHemisphereOpen ≃ₘ⟮𝓡 4, 𝓡 4⟯ r4UnitBallOpen where
  toFun x := ⟨vec4 (x.1.1 1) (x.1.1 2) (x.1.1 3) (x.1.1 4), by
    change dist (vec4 (x.1.1 1) (x.1.1 2) (x.1.1 3) (x.1.1 4)) 0 < 1
    rw [dist_zero_right]
    have hx : x.1.1 0 ^ 2 + x.1.1 1 ^ 2 + x.1.1 2 ^ 2 + x.1.1 3 ^ 2 + x.1.1 4 ^ 2 = 1 := by
      rw [← norm_sq_vec5, mem_sphere_zero_iff_norm.mp x.1.2, one_pow]
    have hx0 : 0 < x.1.1 0 := x.2
    have hsq : ‖vec4 (x.1.1 1) (x.1.1 2) (x.1.1 3) (x.1.1 4)‖ ^ 2 < 1 := by
      rw [norm_sq_vec4]
      simp only [vec4_zero, vec4_one, vec4_two, vec4_three]
      nlinarith [sq_pos_of_pos hx0]
    nlinarith [norm_nonneg (vec4 (x.1.1 1) (x.1.1 2) (x.1.1 3) (x.1.1 4))]⟩
  invFun y :=
    ⟨⟨vec5 (Real.sqrt (1 - (y.1 0 ^ 2 + y.1 1 ^ 2 + y.1 2 ^ 2 + y.1 3 ^ 2)))
        (y.1 0) (y.1 1) (y.1 2) (y.1 3), mem_sphere_zero_iff_norm.mpr (by
      have hy : y.1 0 ^ 2 + y.1 1 ^ 2 + y.1 2 ^ 2 + y.1 3 ^ 2 < 1 := by
        have h : ‖y.1‖ < 1 := by simpa [r4UnitBallOpen, dist_zero_right] using y.2
        have hsq : ‖y.1‖ ^ 2 < 1 := by nlinarith [norm_nonneg y.1]
        rwa [norm_sq_vec4] at hsq
      have hpos : 0 < 1 - (y.1 0 ^ 2 + y.1 1 ^ 2 + y.1 2 ^ 2 + y.1 3 ^ 2) := by linarith
      have hsq : ‖vec5 (Real.sqrt (1 - (y.1 0 ^ 2 + y.1 1 ^ 2 + y.1 2 ^ 2 + y.1 3 ^ 2)))
          (y.1 0) (y.1 1) (y.1 2) (y.1 3)‖ ^ 2 = 1 := by
        rw [norm_sq_vec5]
        simp only [vec5_zero, vec5_one, vec5_two, vec5_three, vec5_four]
        rw [Real.sq_sqrt hpos.le]
        ring
      nlinarith [norm_nonneg (vec5
        (Real.sqrt (1 - (y.1 0 ^ 2 + y.1 1 ^ 2 + y.1 2 ^ 2 + y.1 3 ^ 2)))
        (y.1 0) (y.1 1) (y.1 2) (y.1 3))])⟩, by
      change 0 < Real.sqrt (1 - (y.1 0 ^ 2 + y.1 1 ^ 2 + y.1 2 ^ 2 + y.1 3 ^ 2))
      have hy : ‖y.1‖ ^ 2 < 1 := by
        have h : ‖y.1‖ < 1 := by simpa [r4UnitBallOpen, dist_zero_right] using y.2
        nlinarith [norm_nonneg y.1]
      rw [norm_sq_vec4] at hy
      exact Real.sqrt_pos.mpr (by linarith)⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    have hx : x.1.1 0 ^ 2 + x.1.1 1 ^ 2 + x.1.1 2 ^ 2 + x.1.1 3 ^ 2 + x.1.1 4 ^ 2 = 1 := by
      rw [← norm_sq_vec5, mem_sphere_zero_iff_norm.mp x.1.2, one_pow]
    have hx0 : 0 < x.1.1 0 := x.2
    refine ext_vec5 ?_ rfl rfl rfl rfl
    simp only [vec5_zero, vec4_zero, vec4_one, vec4_two, vec4_three]
    rw [show 1 - (x.1.1 1 ^ 2 + x.1.1 2 ^ 2 + x.1.1 3 ^ 2 + x.1.1 4 ^ 2) = x.1.1 0 ^ 2 from by
      linarith, Real.sqrt_sq hx0.le]
  right_inv y := by
    apply Subtype.ext
    refine ext_vec4 rfl rfl rfl rfl
  contMDiff_toFun := by
    rw [← TauCeti.ContMDiff.subtypeVal_comp_iff r4UnitBallOpen]
    have hcoe : ContMDiff (𝓡 4) 𝓘(ℝ, EuclideanSpace ℝ (Fin 5)) ∞
        (fun x : s4EastHemisphereOpen ↦ (x.1 : EuclideanSpace ℝ (Fin 5))) :=
      contMDiff_coe_sphere.comp contMDiff_subtype_val
    have hcoord (i : Fin 5) :
        ContMDiff (𝓡 4) 𝓘(ℝ, ℝ) ∞ (fun x : s4EastHemisphereOpen ↦ x.1.1 i) :=
      (euclidProj i).contDiff.contMDiff.comp hcoe
    refine (EuclideanSpace.equiv (Fin 4) ℝ).symm.contDiff.contMDiff.comp ?_
    refine contMDiff_pi_module_iff.mpr fun i ↦ ?_
    fin_cases i
    · exact hcoord 1
    · exact hcoord 2
    · exact hcoord 3
    · exact hcoord 4
  contMDiff_invFun := by
    rw [← TauCeti.ContMDiff.subtypeVal_comp_iff s4EastHemisphereOpen]
    have hy_val : ContMDiff (𝓡 4) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) ∞
        (fun y : r4UnitBallOpen ↦ y.1) :=
      contMDiff_subtype_val
    have hy (i : Fin 4) : ContMDiff (𝓡 4) 𝓘(ℝ, ℝ) ∞ (fun y : r4UnitBallOpen ↦ y.1 i) :=
      (euclidProj i).contDiff.contMDiff.comp hy_val
    have hrad : ContMDiff (𝓡 4) 𝓘(ℝ, ℝ) ∞
        (fun y : r4UnitBallOpen ↦ 1 - (y.1 0 ^ 2 + y.1 1 ^ 2 + y.1 2 ^ 2 + y.1 3 ^ 2)) :=
      contMDiff_const.sub ((((hy 0).pow 2).add ((hy 1).pow 2)).add ((hy 2).pow 2) |>.add
        ((hy 3).pow 2))
    have hsqrt : ContMDiff (𝓡 4) 𝓘(ℝ, ℝ) ∞
        (fun y : r4UnitBallOpen ↦
          Real.sqrt (1 - (y.1 0 ^ 2 + y.1 1 ^ 2 + y.1 2 ^ 2 + y.1 3 ^ 2))) := by
      intro y
      have hpos : 0 < 1 - (y.1 0 ^ 2 + y.1 1 ^ 2 + y.1 2 ^ 2 + y.1 3 ^ 2) := by
        have h : ‖y.1‖ ^ 2 < 1 := by
          have hb : ‖y.1‖ < 1 := by simpa [r4UnitBallOpen, dist_zero_right] using y.2
          nlinarith [norm_nonneg y.1]
        rw [norm_sq_vec4] at h
        linarith
      exact (Real.contDiffAt_sqrt hpos.ne').contMDiffAt.comp y (hrad y)
    have hpi : ContMDiff (𝓡 4) 𝓘(ℝ, Fin 5 → ℝ) ∞
        (fun y : r4UnitBallOpen ↦
          ![Real.sqrt (1 - (y.1 0 ^ 2 + y.1 1 ^ 2 + y.1 2 ^ 2 + y.1 3 ^ 2)),
            y.1 0, y.1 1, y.1 2, y.1 3]) := by
      refine contMDiff_pi_module_iff.mpr fun i ↦ ?_
      fin_cases i
      · exact hsqrt
      · exact hy 0
      · exact hy 1
      · exact hy 2
      · exact hy 3
    have hraw : ContMDiff (𝓡 4) 𝓘(ℝ, EuclideanSpace ℝ (Fin 5)) ∞
        (fun y : r4UnitBallOpen ↦
          vec5 (Real.sqrt (1 - (y.1 0 ^ 2 + y.1 1 ^ 2 + y.1 2 ^ 2 + y.1 3 ^ 2)))
            (y.1 0) (y.1 1) (y.1 2) (y.1 3)) :=
      (EuclideanSpace.equiv (Fin 5) ℝ).symm.contDiff.contMDiff.comp hpi
    exact hraw.codRestrict_sphere _

private noncomputable def s4EastHemisphereSlice :
    PartialDiffeomorph (𝓡 4) (𝓡 4) Sphere4 (EuclideanSpace ℝ (Fin 4)) ∞ :=
  s4EastHemisphereDiffeomorph.toPartialDiffeomorph.liftOpens
    ⟨⟨s4ADKCritBase, s4ADKCritBase_mem_east⟩⟩ ⟨⟨0, zero_mem_r4UnitBallOpen⟩⟩

private theorem s4EastHemisphereSlice_source :
    s4EastHemisphereSlice.source = s4EastHemisphereOpen.1 := by
  unfold s4EastHemisphereSlice
  rw [PartialDiffeomorph.liftOpens_source]
  ext x
  simp [SetLike.mem_coe]

private theorem s4EastHemisphereSlice_apply (x : s4EastHemisphereOpen) :
    s4EastHemisphereSlice x.1 = (s4EastHemisphereDiffeomorph x).1 := by
  unfold s4EastHemisphereSlice
  rw [PartialDiffeomorph.liftOpens_apply_coe, Diffeomorph.toPartialDiffeomorph_toPartialEquiv]
  rfl

private theorem s4EastHemisphereSlice_symm_apply (y : r4UnitBallOpen) :
    s4EastHemisphereSlice.symm y.1 = (s4EastHemisphereDiffeomorph.symm y).1 := by
  change s4EastHemisphereSlice.toPartialEquiv.symm y.1 = (s4EastHemisphereDiffeomorph.symm y).1
  unfold s4EastHemisphereSlice
  rw [PartialDiffeomorph.liftOpens_symm_apply_coe, Diffeomorph.toPartialDiffeomorph_toPartialEquiv]
  rfl

private noncomputable def s2WestHemisphereOpen : Opens Sphere2 :=
  ⟨{z : Sphere2 | z.1 0 < 0},
    isOpen_lt ((euclidProj (0 : Fin 3)).continuous.comp continuous_subtype_val) continuous_const⟩

private theorem s4ADKCritBase_image_mem_west :
    s4ADKFibration s4ADKCritBase ∈ s2WestHemisphereOpen.1 := by
  change (s4ADKFibration s4ADKCritBase).1 0 < 0
  have hraw0 : s4ADKRaw s4ADKCritBase.1 0 = -1 / 2 := by
    simp only [s4ADKRaw_zero, s4ADKCritBase, vec5_zero, vec5_one, vec5_two, vec5_three, vec5_four]
    norm_num
  rw [coe_s4ADKFibration, PiLp.smul_apply, smul_eq_mul, hraw0]
  have hpos : 0 < ‖s4ADKRaw s4ADKCritBase.1‖⁻¹ := inv_pos.mpr (norm_s4ADKRaw_pos s4ADKCritBase)
  linarith

private noncomputable def r2UnitBallOpen : Opens EuclideanPlane :=
  ⟨Metric.ball (0 : EuclideanPlane) 1, Metric.isOpen_ball⟩

private theorem zero_mem_r2UnitBallOpen : (0 : EuclideanPlane) ∈ r2UnitBallOpen.1 := by
  simp [r2UnitBallOpen]

private noncomputable def s2WestHemisphereDiffeomorph :
    s2WestHemisphereOpen ≃ₘ⟮𝓡 2, 𝓡 2⟯ r2UnitBallOpen where
  toFun z := ⟨vec2 (z.1.1 1) (z.1.1 2), by
    change dist (vec2 (z.1.1 1) (z.1.1 2)) 0 < 1
    rw [dist_zero_right]
    have hz : z.1.1 0 ^ 2 + z.1.1 1 ^ 2 + z.1.1 2 ^ 2 = 1 := by
      rw [← norm_sq_vec3, mem_sphere_zero_iff_norm.mp z.1.2, one_pow]
    have hz0 : z.1.1 0 < 0 := z.2
    have hsq : ‖vec2 (z.1.1 1) (z.1.1 2)‖ ^ 2 < 1 := by
      rw [norm_sq_plane]
      simp only [vec2_zero, vec2_one]
      nlinarith [sq_pos_of_neg hz0]
    nlinarith [norm_nonneg (vec2 (z.1.1 1) (z.1.1 2))]⟩
  invFun q :=
    ⟨⟨vec3 (-Real.sqrt (1 - (q.1 0 ^ 2 + q.1 1 ^ 2))) (q.1 0) (q.1 1),
      mem_sphere_zero_iff_norm.mpr (by
        have hq : q.1 0 ^ 2 + q.1 1 ^ 2 < 1 := by
          have h : ‖q.1‖ < 1 := by simpa [r2UnitBallOpen, dist_zero_right] using q.2
          have hsq : ‖q.1‖ ^ 2 < 1 := by nlinarith [norm_nonneg q.1]
          rwa [norm_sq_plane] at hsq
        have hpos : 0 < 1 - (q.1 0 ^ 2 + q.1 1 ^ 2) := by linarith
        have hsq : ‖vec3 (-Real.sqrt (1 - (q.1 0 ^ 2 + q.1 1 ^ 2))) (q.1 0) (q.1 1)‖ ^ 2 = 1 := by
          rw [norm_sq_vec3]
          simp only [vec3_zero, vec3_one, vec3_two]
          rw [neg_sq, Real.sq_sqrt hpos.le]
          ring
        nlinarith [norm_nonneg
          (vec3 (-Real.sqrt (1 - (q.1 0 ^ 2 + q.1 1 ^ 2))) (q.1 0) (q.1 1))])⟩, by
      change -Real.sqrt (1 - (q.1 0 ^ 2 + q.1 1 ^ 2)) < 0
      have hq : ‖q.1‖ ^ 2 < 1 := by
        have h : ‖q.1‖ < 1 := by simpa [r2UnitBallOpen, dist_zero_right] using q.2
        nlinarith [norm_nonneg q.1]
      rw [norm_sq_plane] at hq
      exact neg_lt_zero.mpr (Real.sqrt_pos.mpr (by linarith))⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    have hz : z.1.1 0 ^ 2 + z.1.1 1 ^ 2 + z.1.1 2 ^ 2 = 1 := by
      rw [← norm_sq_vec3, mem_sphere_zero_iff_norm.mp z.1.2, one_pow]
    have hz0 : z.1.1 0 < 0 := z.2
    refine ext_vec3 ?_ rfl rfl
    simp only [vec3_zero, vec2_zero, vec2_one]
    rw [show 1 - (z.1.1 1 ^ 2 + z.1.1 2 ^ 2) = (-z.1.1 0) ^ 2 from by linear_combination -hz,
      Real.sqrt_sq (by linarith)]
    ring
  right_inv q := by
    apply Subtype.ext
    refine ext_vec2 rfl rfl
  contMDiff_toFun := by
    rw [← TauCeti.ContMDiff.subtypeVal_comp_iff r2UnitBallOpen]
    have hcoe : ContMDiff (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
        (fun z : s2WestHemisphereOpen ↦ (z.1 : EuclideanSpace ℝ (Fin 3))) :=
      contMDiff_coe_sphere.comp contMDiff_subtype_val
    have hcoord (i : Fin 3) :
        ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun z : s2WestHemisphereOpen ↦ z.1.1 i) :=
      (euclidProj i).contDiff.contMDiff.comp hcoe
    refine (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.contMDiff.comp ?_
    refine contMDiff_pi_module_iff.mpr fun i ↦ ?_
    fin_cases i
    · exact hcoord 1
    · exact hcoord 2
  contMDiff_invFun := by
    rw [← TauCeti.ContMDiff.subtypeVal_comp_iff s2WestHemisphereOpen]
    have hq_val : ContMDiff (𝓡 2) 𝓘(ℝ, EuclideanPlane) ∞ (fun q : r2UnitBallOpen ↦ q.1) :=
      contMDiff_subtype_val
    have hq (i : Fin 2) : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun q : r2UnitBallOpen ↦ q.1 i) :=
      (euclidProj i).contDiff.contMDiff.comp hq_val
    have hrad : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
        (fun q : r2UnitBallOpen ↦ 1 - (q.1 0 ^ 2 + q.1 1 ^ 2)) :=
      (contDiff_const.sub (((euclidProj (0 : Fin 2)).contDiff.pow 2).add
        ((euclidProj (1 : Fin 2)).contDiff.pow 2))).contMDiff.comp hq_val
    have hsqrt : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
        (fun q : r2UnitBallOpen ↦ Real.sqrt (1 - (q.1 0 ^ 2 + q.1 1 ^ 2))) := by
      intro q
      have hpos : 0 < 1 - (q.1 0 ^ 2 + q.1 1 ^ 2) := by
        have hb : ‖q.1‖ < 1 := by simpa [r2UnitBallOpen, dist_zero_right] using q.2
        have h : ‖q.1‖ ^ 2 < 1 := by nlinarith [norm_nonneg q.1]
        rw [norm_sq_plane] at h
        linarith
      exact (Real.contDiffAt_sqrt hpos.ne').contMDiffAt.comp q (hrad q)
    have hpi : ContMDiff (𝓡 2) 𝓘(ℝ, Fin 3 → ℝ) ∞
        (fun q : r2UnitBallOpen ↦
          ![-Real.sqrt (1 - (q.1 0 ^ 2 + q.1 1 ^ 2)), q.1 0, q.1 1]) := by
      refine contMDiff_pi_module_iff.mpr fun i ↦ ?_
      fin_cases i
      · exact hsqrt.neg
      · exact hq 0
      · exact hq 1
    have hraw : ContMDiff (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
        (fun q : r2UnitBallOpen ↦
          vec3 (-Real.sqrt (1 - (q.1 0 ^ 2 + q.1 1 ^ 2))) (q.1 0) (q.1 1)) :=
      (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.contMDiff.comp hpi
    exact hraw.codRestrict_sphere _

private noncomputable def s2WestHemisphereSlice :
    PartialDiffeomorph (𝓡 2) (𝓡 2) Sphere2 EuclideanPlane ∞ :=
  s2WestHemisphereDiffeomorph.toPartialDiffeomorph.liftOpens
    ⟨⟨s4ADKFibration s4ADKCritBase, s4ADKCritBase_image_mem_west⟩⟩
    ⟨⟨0, zero_mem_r2UnitBallOpen⟩⟩

private theorem s2WestHemisphereSlice_source :
    s2WestHemisphereSlice.source = s2WestHemisphereOpen.1 := by
  unfold s2WestHemisphereSlice
  rw [PartialDiffeomorph.liftOpens_source]
  ext z
  simp [SetLike.mem_coe]

private theorem s2WestHemisphereSlice_apply (z : s2WestHemisphereOpen) :
    s2WestHemisphereSlice z.1 = (s2WestHemisphereDiffeomorph z).1 := by
  unfold s2WestHemisphereSlice
  rw [PartialDiffeomorph.liftOpens_apply_coe, Diffeomorph.toPartialDiffeomorph_toPartialEquiv]
  rfl

private theorem norm_s4ADKCritBase_raw :
    ‖s4ADKRaw s4ADKCritBase.1‖ = Real.sqrt 13 / 4 := by
  have hsq : ‖s4ADKRaw s4ADKCritBase.1‖ ^ 2 = (Real.sqrt 13 / 4) ^ 2 := by
    rw [norm_sq_s4ADKRaw]
    simp only [s4ADKCritBase, vec5_zero, vec5_one, vec5_two, vec5_three, vec5_four]
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  nlinarith [norm_nonneg (s4ADKRaw s4ADKCritBase.1), Real.sqrt_nonneg 13]

private noncomputable def adkTgtBase : EuclideanPlane :=
  vec2 0 (-3 / Real.sqrt 13)

private theorem s2WestHemisphereSlice_critBase :
    s2WestHemisphereSlice (s4ADKFibration s4ADKCritBase) = adkTgtBase := by
  have hmem := s4ADKCritBase_image_mem_west
  change s2WestHemisphereSlice
      (⟨s4ADKFibration s4ADKCritBase, hmem⟩ : s2WestHemisphereOpen).1 = adkTgtBase
  rw [s2WestHemisphereSlice_apply]
  refine ext_vec2 ?_ ?_
  · have h0 : (s2WestHemisphereDiffeomorph ⟨s4ADKFibration s4ADKCritBase, hmem⟩).1 0 =
        (s4ADKFibration s4ADKCritBase).1 1 := rfl
    rw [h0, coe_s4ADKFibration, PiLp.smul_apply, smul_eq_mul, s4ADKRaw_one]
    simp [s4ADKCritBase, adkTgtBase]
  · have h1 : (s2WestHemisphereDiffeomorph ⟨s4ADKFibration s4ADKCritBase, hmem⟩).1 1 =
        (s4ADKFibration s4ADKCritBase).1 2 := rfl
    rw [h1, coe_s4ADKFibration, PiLp.smul_apply, smul_eq_mul, s4ADKRaw_two,
      norm_s4ADKCritBase_raw]
    have htwo : 1 / 4 - (s4ADKCritBase.1 0 ^ 2 + s4ADKCritBase.1 1 ^ 2) = -3 / 4 := by
      simp only [s4ADKCritBase, vec5_zero, vec5_one]; norm_num
    rw [htwo]
    simp only [adkTgtBase, vec2_one]
    have hs13 : Real.sqrt 13 ≠ 0 := by positivity
    field_simp [hs13]

private theorem adkTgtBase_mem_ball : adkTgtBase ∈ Metric.ball (0 : EuclideanPlane) 1 := by
  rw [Metric.mem_ball, dist_zero_right]
  have hs13 : Real.sqrt 13 ≠ 0 := by positivity
  have hsq : ‖adkTgtBase‖ ^ 2 < 1 := by
    rw [norm_sq_plane]
    simp only [adkTgtBase, vec2_zero, vec2_one, zero_pow two_ne_zero, zero_add]
    rw [div_pow, neg_sq, Real.sq_sqrt (by norm_num)]
    norm_num
  nlinarith [norm_nonneg adkTgtBase]

private noncomputable def adkTgtMap (q : EuclideanPlane) : EuclideanPlane :=
  vec2
    (q 1 / Real.sqrt (1 - q 1 ^ 2) + 3 / 2)
    (Real.arctan (q 0 / (-Real.sqrt (1 - q 0 ^ 2 - q 1 ^ 2))))

private theorem adkTgtMap_critBase : adkTgtMap adkTgtBase = 0 := by
  have hs13 : Real.sqrt 13 ≠ 0 := by positivity
  have hsq13 : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  have hden : 1 - adkTgtBase 1 ^ 2 = (2 / Real.sqrt 13) ^ 2 := by
    simp only [adkTgtBase, vec2_one]
    field_simp [hs13]
    rw [hsq13]
    norm_num
  have hsqrt : Real.sqrt (1 - adkTgtBase 1 ^ 2) = 2 / Real.sqrt 13 := by
    rw [hden, Real.sqrt_sq (by positivity)]
  refine ext_vec2 ?_ ?_
  · simp only [adkTgtMap, vec2_zero, hsqrt, PiLp.zero_apply]
    simp only [adkTgtBase, vec2_one]
    field_simp [hs13]
    ring
  · simp [adkTgtMap, adkTgtBase]

private theorem contDiffOn_adkTgtMap :
    ContDiffOn ℝ ∞ adkTgtMap (Metric.ball (0 : EuclideanPlane) 1) := by
  intro q hq
  have hq_sq : q 0 ^ 2 + q 1 ^ 2 < 1 := by
    rw [Metric.mem_ball, dist_zero_right] at hq
    have hs : ‖q‖ ^ 2 < 1 := by nlinarith [norm_nonneg q]
    rwa [norm_sq_plane] at hs
  have h1_pos : 0 < 1 - q 1 ^ 2 := by nlinarith [sq_nonneg (q 0)]
  have h2_pos : 0 < 1 - q 0 ^ 2 - q 1 ^ 2 := by linarith
  have hcoord (i : Fin 2) : ContDiffAt ℝ ∞ (fun z : EuclideanPlane ↦ z i) q :=
    (euclidProj i).contDiff.contDiffAt
  have hrad1 : ContDiffAt ℝ ∞ (fun z : EuclideanPlane ↦ 1 - z 1 ^ 2) q :=
    contDiffAt_const.sub ((hcoord 1).pow 2)
  have hsqrt1 : ContDiffAt ℝ ∞ (fun z : EuclideanPlane ↦ Real.sqrt (1 - z 1 ^ 2)) q :=
    (Real.contDiffAt_sqrt h1_pos.ne').comp q hrad1
  have hcomp0 : ContDiffAt ℝ ∞ (fun z : EuclideanPlane ↦ adkTgtMap z 0) q :=
    ((hcoord 1).div hsqrt1 (Real.sqrt_pos.mpr h1_pos).ne').add contDiffAt_const
  have hrad2 : ContDiffAt ℝ ∞ (fun z : EuclideanPlane ↦ 1 - z 0 ^ 2 - z 1 ^ 2) q :=
    (contDiffAt_const.sub ((hcoord 0).pow 2)).sub ((hcoord 1).pow 2)
  have hsqrt2 :
      ContDiffAt ℝ ∞ (fun z : EuclideanPlane ↦ -Real.sqrt (1 - z 0 ^ 2 - z 1 ^ 2)) q :=
    ((Real.contDiffAt_sqrt h2_pos.ne').comp q hrad2).neg
  have hcomp1 : ContDiffAt ℝ ∞ (fun z : EuclideanPlane ↦ adkTgtMap z 1) q :=
    ((hcoord 0).div hsqrt2 (neg_ne_zero.mpr (Real.sqrt_pos.mpr h2_pos).ne')).arctan
  have hvec : ContDiffAt ℝ ∞ adkTgtMap q := by
    have hpi : ContDiffAt ℝ ∞ (fun z : EuclideanPlane ↦ ![adkTgtMap z 0, adkTgtMap z 1]) q := by
      refine contDiffAt_pi.mpr fun i ↦ ?_
      fin_cases i <;> assumption
    exact ((EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.contDiffAt).comp q hpi
  exact hvec.contDiffWithinAt

private theorem exists_fderiv_adkTgtMap :
    ∃ e : EuclideanPlane ≃L[ℝ] EuclideanPlane,
      (e : EuclideanPlane →L[ℝ] EuclideanPlane) = fderiv ℝ adkTgtMap adkTgtBase := by
  have hs13 : Real.sqrt 13 ≠ 0 := by positivity
  have hsq13 : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  set t₀ : ℝ := adkTgtBase 1
  have h1_pos : 0 < 1 - t₀ ^ 2 := by
    simp only [t₀, adkTgtBase, vec2_one]
    field_simp [hs13]
    rw [hsq13]
    norm_num
  set s := Real.sqrt (1 - t₀ ^ 2)
  have hs_pos : 0 < s := Real.sqrt_pos.mpr h1_pos
  have hrad : HasDerivAt (fun t : ℝ ↦ 1 - t ^ 2) (-2 * t₀) t₀ := by
    refine ((hasDerivAt_const t₀ (1 : ℝ)).sub (hasDerivAt_pow 2 t₀)).congr_deriv ?_
    ring
  have hsqrt_t : HasDerivAt (fun t : ℝ ↦ Real.sqrt (1 - t ^ 2))
      ((-2 * t₀) / (2 * s)) t₀ := by
    refine ((Real.hasDerivAt_sqrt h1_pos.ne').comp t₀ hrad).congr_deriv ?_
    dsimp only [s]
    ring
  have hquot : HasDerivAt (fun t : ℝ ↦ t / Real.sqrt (1 - t ^ 2) + 3 / 2)
      ((1 * s - t₀ * ((-2 * t₀) / (2 * s))) / s ^ 2) t₀ := by
    refine (((hasDerivAt_id t₀).div hsqrt_t hs_pos.ne').add
      (hasDerivAt_const t₀ (3 / 2 : ℝ))).congr_deriv ?_
    dsimp only [s]
    simp
  set c₁ : ℝ := (1 * s - t₀ * ((-2 * t₀) / (2 * s))) / s ^ 2
  have hc₁_ne : c₁ ≠ 0 := by
    have hs_sq : s ^ 2 = 1 - t₀ ^ 2 := Real.sq_sqrt h1_pos.le
    have hc₁_pos : 0 < c₁ := by
      have hid : c₁ = 1 / s ^ 3 := by
        dsimp only [c₁]
        field_simp [hs_pos.ne']
        nlinarith [hs_sq]
      rw [hid]
      positivity
    exact hc₁_pos.ne'
  have hcomp0 : HasFDerivAt (fun z : EuclideanPlane ↦ adkTgtMap z 0)
      (c₁ • euclidProj (1 : Fin 2)) adkTgtBase := by
    refine (hquot.comp_hasFDerivAt adkTgtBase
      (euclidProj (1 : Fin 2)).hasFDerivAt).congr_fderiv ?_
    ext v
    simp
  have h2_pos : 0 < 1 - adkTgtBase 0 ^ 2 - adkTgtBase 1 ^ 2 := by
    dsimp only [t₀] at h1_pos
    simpa [adkTgtBase] using h1_pos
  have hden_cont : DifferentiableAt ℝ
      (fun z : EuclideanPlane ↦ (-Real.sqrt (1 - z 0 ^ 2 - z 1 ^ 2))⁻¹) adkTgtBase := by
    have hcoord (i : Fin 2) : DifferentiableAt ℝ (fun z : EuclideanPlane ↦ z i) adkTgtBase :=
      (euclidProj i).differentiableAt
    have hr : DifferentiableAt ℝ (fun z : EuclideanPlane ↦ 1 - z 0 ^ 2 - z 1 ^ 2) adkTgtBase :=
      ((differentiableAt_const _).sub ((hcoord 0).pow 2)).sub ((hcoord 1).pow 2)
    have hsr : DifferentiableAt ℝ
        (fun z : EuclideanPlane ↦ Real.sqrt (1 - z 0 ^ 2 - z 1 ^ 2)) adkTgtBase :=
      hr.sqrt h2_pos.ne'
    exact hsr.neg.inv (neg_ne_zero.mpr (Real.sqrt_pos.mpr h2_pos).ne')
  set c₀ : ℝ := (-Real.sqrt (1 - adkTgtBase 0 ^ 2 - adkTgtBase 1 ^ 2))⁻¹
  have hc₀_ne : c₀ ≠ 0 :=
    inv_ne_zero (neg_ne_zero.mpr (Real.sqrt_pos.mpr h2_pos).ne')
  have hdiv_at : HasFDerivAt (fun z : EuclideanPlane ↦ z 0 / (-Real.sqrt (1 - z 0 ^ 2 - z 1 ^ 2)))
      (c₀ • euclidProj (0 : Fin 2)) adkTgtBase := by
    have hm := (euclidProj (0 : Fin 2)).hasFDerivAt.mul hden_cont.hasFDerivAt
    have hz0 : adkTgtBase 0 = 0 := rfl
    refine hm.congr_fderiv ?_
    ext v
    simp [hz0, c₀, smul_apply, smul_eq_mul]
  have harc_val : adkTgtBase 0 / (-Real.sqrt (1 - adkTgtBase 0 ^ 2 - adkTgtBase 1 ^ 2)) = 0 := by
    simp [adkTgtBase]
  have hcomp1 : HasFDerivAt (fun z : EuclideanPlane ↦ adkTgtMap z 1)
      (c₀ • euclidProj (0 : Fin 2)) adkTgtBase := by
    have ha := (Real.hasDerivAt_arctan _).comp_hasFDerivAt adkTgtBase hdiv_at
    rw [harc_val] at ha
    refine ha.congr_fderiv ?_
    ext v
    simp [smul_apply, smul_eq_mul]
  have hmap : HasFDerivAt adkTgtMap (clmVec2 (c₁ • euclidProj 1) (c₀ • euclidProj 0))
      adkTgtBase :=
    hasFDerivAt_vec2 hcomp0 hcomp1
  let e_lin : EuclideanPlane ≃ₗ[ℝ] EuclideanPlane :=
    { toFun := fun v ↦ vec2 (c₁ * v 1) (c₀ * v 0)
      map_add' := fun u v ↦ by
        refine ext_vec2 ?_ ?_ <;> simp <;> ring
      map_smul' := fun r v ↦ by
        refine ext_vec2 ?_ ?_ <;> simp <;> ring
      invFun := fun w ↦ vec2 (w 1 / c₀) (w 0 / c₁)
      left_inv := fun v ↦ by
        refine ext_vec2 ?_ ?_ <;> simp [mul_div_cancel_left₀, hc₀_ne, hc₁_ne]
      right_inv := fun w ↦ by
        refine ext_vec2 ?_ ?_ <;> simp [mul_div_cancel₀, hc₀_ne, hc₁_ne] }
  let e : EuclideanPlane ≃L[ℝ] EuclideanPlane :=
    { toLinearEquiv := e_lin
      continuous_toFun := e_lin.toLinearMap.continuous_of_finiteDimensional
      continuous_invFun := e_lin.symm.toLinearMap.continuous_of_finiteDimensional }
  refine ⟨e, ?_⟩
  rw [hmap.fderiv]
  ext v i
  fin_cases i <;> simp [e, e_lin, clmVec2_apply, smul_apply, smul_eq_mul]

private theorem tan_arctan_sub_arctan (a b : ℝ) :
    Real.tan (Real.arctan a - Real.arctan b) = (a - b) / (1 + a * b) := by
  have hne (r : ℝ) : ∀ k : ℤ, Real.arctan r ≠ (2 * (k : ℝ) + 1) * Real.pi / 2 := by
    intro k hk
    have hlo : -(Real.pi / 2) < Real.arctan r := Real.neg_pi_div_two_lt_arctan r
    have hhi : Real.arctan r < Real.pi / 2 := Real.arctan_lt_pi_div_two r
    rw [hk] at hlo hhi
    have hlt : (-1 : ℤ) < k := by
      exact_mod_cast (by nlinarith [Real.pi_pos] : (-1 : ℝ) < k)
    have hgt : k < 0 := by
      exact_mod_cast (by nlinarith [Real.pi_pos] : (k : ℝ) < 0)
    omega
  rw [Real.tan_sub' ⟨hne a, hne b⟩, Real.tan_arctan, Real.tan_arctan]

private noncomputable def adkU (y : EuclideanSpace ℝ (Fin 4)) : ℝ := y 1 ^ 2 + y 2 ^ 2
private noncomputable def adkV (y : EuclideanSpace ℝ (Fin 4)) : ℝ := y 3 ^ 2
private noncomputable def adkQ (u v : ℝ) : ℝ := (1 - u - v) * ((1 / 2 - u) ^ 2 + v)
private noncomputable def adkP2 (u v : ℝ) : ℝ :=
  21 / 4 - 14 * u + 8 * v + 9 * u * v + 9 * u ^ 2
private noncomputable def adkD (u v : ℝ) : ℝ :=
  2 * Real.sqrt (adkQ u v) * (3 * Real.sqrt (adkQ u v) - 2 * (u + v - 3 / 4))

private theorem adk_single_denom_identity (u v : ℝ) :
    9 * adkQ u v - 4 * (u + v - 3 / 4) ^ 2 = v * (51 / 4 - 13 * v) - u * adkP2 u v := by
  unfold adkQ adkP2
  ring

private theorem norm_sq_lt_one_sixteenth {y : EuclideanSpace ℝ (Fin 4)}
    (hy : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) (1 / 4)) :
    y 0 ^ 2 + adkU y + adkV y < 1 / 16 := by
  rw [Metric.mem_ball, dist_zero_right] at hy
  have hsq : ‖y‖ ^ 2 < (1 / 4) ^ 2 := by nlinarith [norm_nonneg y]
  rw [norm_sq_vec4] at hsq
  unfold adkU adkV
  linarith

private theorem adkU_nonneg (y : EuclideanSpace ℝ (Fin 4)) : 0 ≤ adkU y := by
  unfold adkU; positivity

private theorem adkV_nonneg (y : EuclideanSpace ℝ (Fin 4)) : 0 ≤ adkV y := by
  unfold adkV; positivity

private theorem adkQ_pos {y : EuclideanSpace ℝ (Fin 4)}
    (hy : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) (1 / 4)) :
    0 < adkQ (adkU y) (adkV y) := by
  have hsum := norm_sq_lt_one_sixteenth hy
  have hu := adkU_nonneg y
  have hv := adkV_nonneg y
  have hx0 : 0 ≤ y 0 ^ 2 := sq_nonneg _
  have h1 : 0 < 1 - adkU y - adkV y := by linarith
  have h2 : 0 < (1 / 2 - adkU y) ^ 2 + adkV y := by
    have hlt : 7 / 16 < 1 / 2 - adkU y := by linarith
    nlinarith [sq_nonneg (1 / 2 - adkU y)]
  exact mul_pos h1 h2

private theorem adkD_factor_pos {y : EuclideanSpace ℝ (Fin 4)}
    (hy : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) (1 / 4)) :
    0 < 3 * Real.sqrt (adkQ (adkU y) (adkV y)) - 2 * (adkU y + adkV y - 3 / 4) := by
  have hsum := norm_sq_lt_one_sixteenth hy
  have hq : 0 < Real.sqrt (adkQ (adkU y) (adkV y)) := Real.sqrt_pos.mpr (adkQ_pos hy)
  have hneg : adkU y + adkV y - 3 / 4 < 0 := by
    have : 0 ≤ y 0 ^ 2 := sq_nonneg _
    linarith
  linarith

private theorem adkD_pos {y : EuclideanSpace ℝ (Fin 4)}
    (hy : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) (1 / 4)) :
    0 < adkD (adkU y) (adkV y) := by
  unfold adkD
  exact mul_pos (mul_pos two_pos (Real.sqrt_pos.mpr (adkQ_pos hy))) (adkD_factor_pos hy)

private theorem adkP2_pos {y : EuclideanSpace ℝ (Fin 4)}
    (hy : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) (1 / 4)) :
    0 < adkP2 (adkU y) (adkV y) := by
  have hsum := norm_sq_lt_one_sixteenth hy
  have hu := adkU_nonneg y
  have hv := adkV_nonneg y
  have hx0 : 0 ≤ y 0 ^ 2 := sq_nonneg _
  unfold adkP2
  nlinarith

private theorem adkC1_pos {y : EuclideanSpace ℝ (Fin 4)}
    (hy : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) (1 / 4)) :
    0 < 51 / 4 - 13 * adkV y := by
  have hsum := norm_sq_lt_one_sixteenth hy
  have hu := adkU_nonneg y
  have hx0 : 0 ≤ y 0 ^ 2 := sq_nonneg _
  linarith

private noncomputable def adkSrcMap (y : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 4) :=
  vec4
    (y 3 * Real.sqrt ((51 / 4 - 13 * adkV y) / adkD (adkU y) (adkV y)))
    (y 1 * Real.sqrt (2 * adkP2 (adkU y) (adkV y) / adkD (adkU y) (adkV y)))
    (y 2 * Real.sqrt (2 * adkP2 (adkU y) (adkV y) / adkD (adkU y) (adkV y)))
    (Real.arctan (y 0 / Real.sqrt (1 - (y 0 ^ 2 + adkU y + adkV y))) -
      Real.arctan (y 3 / (1 / 2 - adkU y)))

private theorem adkQ_zero : adkQ 0 0 = 1 / 4 := by
  unfold adkQ; norm_num

private theorem adkD_zero : adkD 0 0 = 3 := by
  unfold adkD
  rw [adkQ_zero]
  have hsqrt : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hsqrt]
  norm_num

private theorem adkSrcMap_zero : adkSrcMap 0 = 0 := by
  refine ext_vec4 ?_ ?_ ?_ ?_ <;> simp [adkSrcMap]

private theorem contDiffAt_adkU (y : EuclideanSpace ℝ (Fin 4)) :
    ContDiffAt ℝ ∞ adkU y :=
  (((euclidProj (1 : Fin 4)).contDiff.pow 2).add
    ((euclidProj (2 : Fin 4)).contDiff.pow 2)).contDiffAt

private theorem contDiffAt_adkV (y : EuclideanSpace ℝ (Fin 4)) :
    ContDiffAt ℝ ∞ adkV y :=
  ((euclidProj (3 : Fin 4)).contDiff.pow 2).contDiffAt

private theorem contDiffAt_adkD {y : EuclideanSpace ℝ (Fin 4)}
    (hy : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) (1 / 4)) :
    ContDiffAt ℝ ∞ (fun z ↦ adkD (adkU z) (adkV z)) y := by
  have hu := contDiffAt_adkU y
  have hv := contDiffAt_adkV y
  have hq : ContDiffAt ℝ ∞ (fun z ↦ adkQ (adkU z) (adkV z)) y :=
    ((contDiffAt_const.sub hu).sub hv).mul (((contDiffAt_const.sub hu).pow 2).add hv)
  have hsqrtq : ContDiffAt ℝ ∞ (fun z ↦ Real.sqrt (adkQ (adkU z) (adkV z))) y :=
    (Real.contDiffAt_sqrt (adkQ_pos hy).ne').comp y hq
  have hfac : ContDiffAt ℝ ∞
      (fun z ↦ 3 * Real.sqrt (adkQ (adkU z) (adkV z)) - 2 * (adkU z + adkV z - 3 / 4)) y :=
    (contDiffAt_const.mul hsqrtq).sub
      (contDiffAt_const.mul ((hu.add hv).sub contDiffAt_const))
  exact (contDiffAt_const.mul hsqrtq).mul hfac

private theorem contDiffAt_adkFactor0 {y : EuclideanSpace ℝ (Fin 4)}
    (hy : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) (1 / 4)) :
    ContDiffAt ℝ ∞ (fun z ↦ Real.sqrt ((51 / 4 - 13 * adkV z) / adkD (adkU z) (adkV z))) y := by
  have hv := contDiffAt_adkV y
  have hnum : ContDiffAt ℝ ∞ (fun z ↦ 51 / 4 - 13 * adkV z) y :=
    contDiffAt_const.sub (contDiffAt_const.mul hv)
  have hden := contDiffAt_adkD hy
  have hquot : ContDiffAt ℝ ∞ (fun z ↦ (51 / 4 - 13 * adkV z) / adkD (adkU z) (adkV z)) y :=
    hnum.div hden (adkD_pos hy).ne'
  have hpos : 0 < (51 / 4 - 13 * adkV y) / adkD (adkU y) (adkV y) :=
    div_pos (adkC1_pos hy) (adkD_pos hy)
  exact (Real.contDiffAt_sqrt hpos.ne').comp y hquot

private theorem contDiffAt_adkFactor12 {y : EuclideanSpace ℝ (Fin 4)}
    (hy : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) (1 / 4)) :
    ContDiffAt ℝ ∞
      (fun z ↦ Real.sqrt (2 * adkP2 (adkU z) (adkV z) / adkD (adkU z) (adkV z))) y := by
  have hu := contDiffAt_adkU y
  have hv := contDiffAt_adkV y
  have hp2 : ContDiffAt ℝ ∞ (fun z ↦ 2 * adkP2 (adkU z) (adkV z)) y := by
    have hp : ContDiffAt ℝ ∞ (fun z ↦ adkP2 (adkU z) (adkV z)) y := by
      unfold adkP2
      exact ((((contDiffAt_const.sub (contDiffAt_const.mul hu)).add (contDiffAt_const.mul hv)).add
        ((contDiffAt_const.mul hu).mul hv)).add (contDiffAt_const.mul (hu.pow 2)))
    exact contDiffAt_const.mul hp
  have hquot := hp2.div (contDiffAt_adkD hy) (adkD_pos hy).ne'
  have hpos : 0 < 2 * adkP2 (adkU y) (adkV y) / adkD (adkU y) (adkV y) :=
    div_pos (mul_pos two_pos (adkP2_pos hy)) (adkD_pos hy)
  exact (Real.contDiffAt_sqrt hpos.ne').comp y hquot

private theorem contDiffOn_adkSrcMap :
    ContDiffOn ℝ ∞ adkSrcMap (Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) (1 / 4)) := by
  intro y hy
  have hsum := norm_sq_lt_one_sixteenth hy
  have hrad_pos : 0 < 1 - (y 0 ^ 2 + adkU y + adkV y) := by linarith
  have hhalf_pos : 0 < 1 / 2 - adkU y := by
    have : 0 ≤ y 0 ^ 2 := sq_nonneg _
    have : 0 ≤ adkV y := adkV_nonneg y
    linarith
  have hcoord (i : Fin 4) : ContDiffAt ℝ ∞ (fun z : EuclideanSpace ℝ (Fin 4) ↦ z i) y :=
    (euclidProj i).contDiff.contDiffAt
  have h0 : ContDiffAt ℝ ∞ (fun z ↦ adkSrcMap z 0) y :=
    (hcoord 3).mul (contDiffAt_adkFactor0 hy)
  have h1 : ContDiffAt ℝ ∞ (fun z ↦ adkSrcMap z 1) y :=
    (hcoord 1).mul (contDiffAt_adkFactor12 hy)
  have h2 : ContDiffAt ℝ ∞ (fun z ↦ adkSrcMap z 2) y :=
    (hcoord 2).mul (contDiffAt_adkFactor12 hy)
  have hrad : ContDiffAt ℝ ∞ (fun z ↦ 1 - (z 0 ^ 2 + adkU z + adkV z)) y :=
    contDiffAt_const.sub ((((hcoord 0).pow 2).add (contDiffAt_adkU y)).add (contDiffAt_adkV y))
  have hsqrt_rad : ContDiffAt ℝ ∞ (fun z ↦ Real.sqrt (1 - (z 0 ^ 2 + adkU z + adkV z))) y :=
    (Real.contDiffAt_sqrt hrad_pos.ne').comp y hrad
  have htermA : ContDiffAt ℝ ∞
      (fun z ↦ Real.arctan (z 0 / Real.sqrt (1 - (z 0 ^ 2 + adkU z + adkV z)))) y :=
    ((hcoord 0).div hsqrt_rad (Real.sqrt_pos.mpr hrad_pos).ne').arctan
  have htermB : ContDiffAt ℝ ∞ (fun z ↦ Real.arctan (z 3 / (1 / 2 - adkU z))) y :=
    ((hcoord 3).div (contDiffAt_const.sub (contDiffAt_adkU y)) hhalf_pos.ne').arctan
  have h3 : ContDiffAt ℝ ∞ (fun z ↦ adkSrcMap z 3) y := htermA.sub htermB
  have hpi : ContDiffAt ℝ ∞
      (fun z ↦ ![adkSrcMap z 0, adkSrcMap z 1, adkSrcMap z 2, adkSrcMap z 3]) y := by
    refine contDiffAt_pi.mpr fun i ↦ ?_
    fin_cases i <;> assumption
  have hvec : ContDiffAt ℝ ∞ adkSrcMap y :=
    ((EuclideanSpace.equiv (Fin 4) ℝ).symm.contDiff.contDiffAt).comp y hpi
  exact hvec.contDiffWithinAt

private noncomputable def adkClmVec4 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L₀ L₁ L₂ L₃ : E →L[ℝ] ℝ) : E →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![L₀, L₁, L₂, L₃])

@[simp]
private theorem adkClmVec4_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L₀ L₁ L₂ L₃ : E →L[ℝ] ℝ) (v : E) :
    adkClmVec4 L₀ L₁ L₂ L₃ v = vec4 (L₀ v) (L₁ v) (L₂ v) (L₃ v) := by
  refine PiLp.ext fun i ↦ ?_
  fin_cases i <;> rfl

private theorem hasFDerivAt_vec4 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g₀ g₁ g₂ g₃ : E → ℝ} {L₀ L₁ L₂ L₃ : E →L[ℝ] ℝ} {x : E}
    (h₀ : HasFDerivAt g₀ L₀ x) (h₁ : HasFDerivAt g₁ L₁ x)
    (h₂ : HasFDerivAt g₂ L₂ x) (h₃ : HasFDerivAt g₃ L₃ x) :
    HasFDerivAt (fun y ↦ vec4 (g₀ y) (g₁ y) (g₂ y) (g₃ y)) (adkClmVec4 L₀ L₁ L₂ L₃) x := by
  have hpi : HasFDerivAt (fun y : E ↦ (![g₀ y, g₁ y, g₂ y, g₃ y] : Fin 4 → ℝ))
      (ContinuousLinearMap.pi ![L₀, L₁, L₂, L₃]) x := by
    refine hasFDerivAt_pi.mpr fun i ↦ ?_
    fin_cases i
    · simpa using h₀
    · simpa using h₁
    · simpa using h₂
    · simpa using h₃
  exact (EuclideanSpace.equiv (Fin 4) ℝ).symm.hasFDerivAt.comp x hpi

private theorem exists_fderiv_adkSrcMap :
    ∃ e : EuclideanSpace ℝ (Fin 4) ≃L[ℝ] EuclideanSpace ℝ (Fin 4),
      (e : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) = fderiv ℝ adkSrcMap 0 := by
  have h0_mem : (0 : EuclideanSpace ℝ (Fin 4)) ∈
      Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) (1 / 4) := by
    simp
  have hfac0_at := (contDiffAt_adkFactor0 h0_mem).differentiableAt (by simp)
  have hfac12_at := (contDiffAt_adkFactor12 h0_mem).differentiableAt (by simp)
  set a₀ : ℝ := Real.sqrt (17 / 4)
  set a₁ : ℝ := Real.sqrt (7 / 2)
  have ha₀_pos : 0 < a₀ := Real.sqrt_pos.mpr (by norm_num)
  have ha₁_pos : 0 < a₁ := Real.sqrt_pos.mpr (by norm_num)
  have ha₀_val : Real.sqrt ((51 / 4 - 13 * adkV 0) / adkD (adkU 0) (adkV 0)) = a₀ := by
    have hu0 : adkU 0 = 0 := by simp [adkU]
    have hv0 : adkV 0 = 0 := by simp [adkV]
    rw [hu0, hv0, adkD_zero]
    norm_num [a₀]
  have ha₁_val : Real.sqrt (2 * adkP2 (adkU 0) (adkV 0) / adkD (adkU 0) (adkV 0)) = a₁ := by
    have hu0 : adkU 0 = 0 := by simp [adkU]
    have hv0 : adkV 0 = 0 := by simp [adkV]
    rw [hu0, hv0, adkD_zero]
    unfold adkP2
    norm_num [a₁]
  have h0 : HasFDerivAt (fun z ↦ adkSrcMap z 0) (a₀ • euclidProj (3 : Fin 4)) 0 := by
    have hm := (euclidProj (3 : Fin 4)).hasFDerivAt.mul hfac0_at.hasFDerivAt
    refine hm.congr_fderiv ?_
    ext v
    simp [ha₀_val, smul_apply, smul_eq_mul]
  have h1 : HasFDerivAt (fun z ↦ adkSrcMap z 1) (a₁ • euclidProj (1 : Fin 4)) 0 := by
    have hm := (euclidProj (1 : Fin 4)).hasFDerivAt.mul hfac12_at.hasFDerivAt
    refine hm.congr_fderiv ?_
    ext v
    simp [ha₁_val, smul_apply, smul_eq_mul]
  have h2 : HasFDerivAt (fun z ↦ adkSrcMap z 2) (a₁ • euclidProj (2 : Fin 4)) 0 := by
    have hm := (euclidProj (2 : Fin 4)).hasFDerivAt.mul hfac12_at.hasFDerivAt
    refine hm.congr_fderiv ?_
    ext v
    simp [ha₁_val, smul_apply, smul_eq_mul]
  have hdenA_diff : DifferentiableAt ℝ
      (fun z ↦ (Real.sqrt (1 - (z 0 ^ 2 + adkU z + adkV z)))⁻¹) 0 := by
    have hcoord (i : Fin 4) : DifferentiableAt ℝ (fun z : EuclideanSpace ℝ (Fin 4) ↦ z i) 0 :=
      (euclidProj i).differentiableAt
    have hu : DifferentiableAt ℝ adkU 0 := (contDiffAt_adkU 0).differentiableAt (by simp)
    have hv : DifferentiableAt ℝ adkV 0 := (contDiffAt_adkV 0).differentiableAt (by simp)
    have hr : DifferentiableAt ℝ (fun z ↦ 1 - (z 0 ^ 2 + adkU z + adkV z)) 0 :=
      (differentiableAt_const _).sub ((((hcoord 0).pow 2).add hu).add hv)
    exact (hr.sqrt (by simp [adkU, adkV])).inv (by simp [adkU, adkV])
  have hdivA : HasFDerivAt (fun z ↦ z 0 / Real.sqrt (1 - (z 0 ^ 2 + adkU z + adkV z)))
      (euclidProj (0 : Fin 4)) 0 := by
    have hm := (euclidProj (0 : Fin 4)).hasFDerivAt.mul hdenA_diff.hasFDerivAt
    refine hm.congr_fderiv ?_
    ext v
    simp [adkU, adkV]
  have htermA : HasFDerivAt
      (fun z ↦ Real.arctan (z 0 / Real.sqrt (1 - (z 0 ^ 2 + adkU z + adkV z))))
      (euclidProj (0 : Fin 4)) 0 := by
    refine ((Real.hasDerivAt_arctan _).comp_hasFDerivAt 0 hdivA).congr_fderiv ?_
    ext v
    simp [adkU, adkV]
  have hdenB_diff : DifferentiableAt ℝ (fun z ↦ (1 / 2 - adkU z)⁻¹) 0 :=
    ((differentiableAt_const _).sub ((contDiffAt_adkU 0).differentiableAt (by simp))).inv
      (by simp [adkU])
  have hdivB : HasFDerivAt (fun z ↦ z 3 / (1 / 2 - adkU z))
      ((2 : ℝ) • euclidProj (3 : Fin 4)) 0 := by
    have hm := (euclidProj (3 : Fin 4)).hasFDerivAt.mul hdenB_diff.hasFDerivAt
    refine hm.congr_fderiv ?_
    ext v
    simp [adkU, smul_apply, smul_eq_mul, div_eq_mul_inv]
  have htermB : HasFDerivAt (fun z ↦ Real.arctan (z 3 / (1 / 2 - adkU z)))
      ((2 : ℝ) • euclidProj (3 : Fin 4)) 0 := by
    refine ((Real.hasDerivAt_arctan _).comp_hasFDerivAt 0 hdivB).congr_fderiv ?_
    ext v
    simp [adkU, smul_apply, smul_eq_mul]
  have h3 : HasFDerivAt (fun z ↦ adkSrcMap z 3)
      (euclidProj (0 : Fin 4) - (2 : ℝ) • euclidProj (3 : Fin 4)) 0 :=
    htermA.sub htermB
  have hmap : HasFDerivAt adkSrcMap
      (adkClmVec4 (a₀ • euclidProj 3) (a₁ • euclidProj 1) (a₁ • euclidProj 2)
        (euclidProj 0 - (2 : ℝ) • euclidProj 3)) 0 :=
    hasFDerivAt_vec4 h0 h1 h2 h3
  let e_lin : EuclideanSpace ℝ (Fin 4) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 4) :=
    { toFun := fun v ↦ vec4 (a₀ * v 3) (a₁ * v 1) (a₁ * v 2) (v 0 - 2 * v 3)
      map_add' := fun u v ↦ by refine ext_vec4 ?_ ?_ ?_ ?_ <;> simp <;> ring
      map_smul' := fun r v ↦ by refine ext_vec4 ?_ ?_ ?_ ?_ <;> simp <;> ring
      invFun := fun w ↦ vec4 (w 3 + 2 * (w 0 / a₀)) (w 1 / a₁) (w 2 / a₁) (w 0 / a₀)
      left_inv := fun v ↦ by
        refine ext_vec4 ?_ ?_ ?_ ?_
        · simp [mul_div_cancel_left₀, ha₀_pos.ne']
        · simp [mul_div_cancel_left₀, ha₁_pos.ne']
        · simp [mul_div_cancel_left₀, ha₁_pos.ne']
        · simp [mul_div_cancel_left₀, ha₀_pos.ne']
      right_inv := fun w ↦ by
        refine ext_vec4 ?_ ?_ ?_ ?_
        · simp [mul_div_cancel₀, ha₀_pos.ne']
        · simp [mul_div_cancel₀, ha₁_pos.ne']
        · simp [mul_div_cancel₀, ha₁_pos.ne']
        · simp }
  let e : EuclideanSpace ℝ (Fin 4) ≃L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    { toLinearEquiv := e_lin
      continuous_toFun := e_lin.toLinearMap.continuous_of_finiteDimensional
      continuous_invFun := e_lin.symm.toLinearMap.continuous_of_finiteDimensional }
  refine ⟨e, ?_⟩
  rw [hmap.fderiv]
  ext v i
  fin_cases i <;>
    simp [e, e_lin, adkClmVec4_apply, sub_apply, smul_apply, smul_eq_mul]

private theorem adk_single_denom_rat {Q H u v P₂ C₁ D : ℝ}
    (hq_pos : 0 < Q) (hfac_pos : 0 < 3 * Real.sqrt Q - 2 * H)
    (hD : D = 2 * Real.sqrt Q * (3 * Real.sqrt Q - 2 * H))
    (hid : 9 * Q - 4 * H ^ 2 = v * C₁ - u * P₂) :
    H / Real.sqrt Q + 3 / 2 = (v * C₁ - u * P₂) / D := by
  have hsqrtQ_pos : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hq_pos
  have hq_sq : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hq_pos.le
  have hden1 : Real.sqrt Q ≠ 0 := hsqrtQ_pos.ne'
  have h2q : 2 * Real.sqrt Q ≠ 0 := mul_ne_zero two_pos.ne' hden1
  have hden2 : 2 * Real.sqrt Q * (3 * Real.sqrt Q - 2 * H) ≠ 0 :=
    mul_ne_zero h2q hfac_pos.ne'
  rw [← hid, hD]
  calc
    H / Real.sqrt Q + 3 / 2
      = (2 * H + 3 * Real.sqrt Q) / (2 * Real.sqrt Q) := by field_simp [hden1]
    _ = (9 * Q - 4 * H ^ 2) / (2 * Real.sqrt Q * (3 * Real.sqrt Q - 2 * H)) := by
        rw [div_eq_div_iff h2q hden2]
        linear_combination 18 * Real.sqrt Q * hq_sq

private theorem adk_arctan_ratio_alg {x0 u y0 y3 : ℝ}
    (hx0 : x0 ≠ 0) (hu : 1 / 2 - u ≠ 0) (hz0 : x0 * (u - 1 / 2) - y0 * y3 ≠ 0) :
    (y0 / x0 - y3 / (1 / 2 - u)) / (1 + (y0 / x0) * (y3 / (1 / 2 - u))) =
      (x0 * y3 + y0 * (u - 1 / 2)) / (x0 * (u - 1 / 2) - y0 * y3) := by
  have hnum : x0 * (1 / 2 - u) * (y0 / x0 - y3 / (1 / 2 - u)) =
      -(x0 * y3 + y0 * (u - 1 / 2)) := by
    calc
      x0 * (1 / 2 - u) * (y0 / x0 - y3 / (1 / 2 - u))
        = (1 / 2 - u) * (x0 * (y0 / x0)) - x0 * ((1 / 2 - u) * (y3 / (1 / 2 - u))) := by ring
      _ = (1 / 2 - u) * y0 - x0 * y3 := by rw [mul_div_cancel₀ _ hx0, mul_div_cancel₀ _ hu]
      _ = -(x0 * y3 + y0 * (u - 1 / 2)) := by ring
  have hden : x0 * (1 / 2 - u) * (1 + (y0 / x0) * (y3 / (1 / 2 - u))) =
      -(x0 * (u - 1 / 2) - y0 * y3) := by
    calc
      x0 * (1 / 2 - u) * (1 + (y0 / x0) * (y3 / (1 / 2 - u)))
        = x0 * (1 / 2 - u) + (x0 * (y0 / x0)) * ((1 / 2 - u) * (y3 / (1 / 2 - u))) := by ring
      _ = x0 * (1 / 2 - u) + y0 * y3 := by rw [mul_div_cancel₀ _ hx0, mul_div_cancel₀ _ hu]
      _ = -(x0 * (u - 1 / 2) - y0 * y3) := by ring
  have h1ab : 1 + (y0 / x0) * (y3 / (1 / 2 - u)) ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hden
    exact hz0 (by linarith)
  rw [div_eq_div_iff h1ab hz0]
  apply mul_left_cancel₀ (mul_ne_zero hx0 hu)
  calc
    x0 * (1 / 2 - u) * ((y0 / x0 - y3 / (1 / 2 - u)) * (x0 * (u - 1 / 2) - y0 * y3))
      = (x0 * (1 / 2 - u) * (y0 / x0 - y3 / (1 / 2 - u))) * (x0 * (u - 1 / 2) - y0 * y3) := by
        ring
    _ = -(x0 * y3 + y0 * (u - 1 / 2)) * (x0 * (u - 1 / 2) - y0 * y3) := by rw [hnum]
    _ = (x0 * y3 + y0 * (u - 1 / 2)) * -(x0 * (u - 1 / 2) - y0 * y3) := by ring
    _ = (x0 * y3 + y0 * (u - 1 / 2)) *
          (x0 * (1 / 2 - u) * (1 + (y0 / x0) * (y3 / (1 / 2 - u)))) := by rw [← hden]
    _ = x0 * (1 / 2 - u) *
          ((x0 * y3 + y0 * (u - 1 / 2)) * (1 + (y0 / x0) * (y3 / (1 / 2 - u)))) := by ring

private theorem adkTgtMap_comp_eq_indefiniteFoldMap
    {y : EuclideanSpace ℝ (Fin 4)}
    (hy : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) (1 / 4)) :
    let x := s4EastHemisphereSlice.symm y
    s4ADKFibration x ∈ s2WestHemisphereOpen.1 ∧
      adkTgtMap (s2WestHemisphereSlice (s4ADKFibration x)) = indefiniteFoldMap (adkSrcMap y) := by
  have hy1 : y ∈ r4UnitBallOpen.1 := by
    rw [Metric.mem_ball, dist_zero_right] at hy
    change dist y 0 < 1
    rw [dist_zero_right]
    linarith
  have hsum := norm_sq_lt_one_sixteenth hy
  set u := adkU y
  set v := adkV y
  have hu_nn : 0 ≤ u := adkU_nonneg y
  have hv_nn : 0 ≤ v := adkV_nonneg y
  have hrad_pos : 0 < 1 - (y 0 ^ 2 + u + v) := by linarith
  set x0 := Real.sqrt (1 - (y 0 ^ 2 + u + v))
  have hx0_pos : 0 < x0 := Real.sqrt_pos.mpr hrad_pos
  have hx0_sq : x0 ^ 2 = 1 - (y 0 ^ 2 + u + v) := Real.sq_sqrt hrad_pos.le
  have hx0_gt : 3 / 4 < x0 := by
    have hgt : (3 / 4 : ℝ) ^ 2 < x0 ^ 2 := by linarith
    nlinarith [Real.sqrt_nonneg (1 - (y 0 ^ 2 + u + v))]
  let x : Sphere4 := s4EastHemisphereSlice.symm y
  have hx_coe : (x : EuclideanSpace ℝ (Fin 5)) = vec5 x0 (y 0) (y 1) (y 2) (y 3) := by
    have hy' := s4EastHemisphereSlice_symm_apply ⟨y, hy1⟩
    change ((s4EastHemisphereSlice.symm y) : EuclideanSpace ℝ (Fin 5)) = _
    rw [hy']
    refine ext_vec5 ?_ rfl rfl rfl rfl
    change Real.sqrt (1 - (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2)) = x0
    congr 1
    dsimp only [x0, u, v, adkU, adkV]
    ring
  have hx0_raw : x.1 0 = x0 := by rw [hx_coe]; rfl
  have hx1_raw : x.1 1 = y 0 := by rw [hx_coe]; rfl
  have hx2_raw : x.1 2 = y 1 := by rw [hx_coe]; rfl
  have hx3_raw : x.1 3 = y 2 := by rw [hx_coe]; rfl
  have hx4_raw : x.1 4 = y 3 := by rw [hx_coe]; rfl
  have hx01_sq : x.1 0 ^ 2 + x.1 1 ^ 2 = 1 - u - v := by
    rw [hx0_raw, hx1_raw, hx0_sq]; ring
  have hZ0 : s4ADKRaw x.1 0 = x0 * (u - 1 / 2) - y 0 * y 3 := by
    rw [s4ADKRaw_zero, hx0_raw, hx1_raw, hx2_raw, hx3_raw, hx4_raw]
    unfold u adkU; ring
  have hZ1 : s4ADKRaw x.1 1 = x0 * y 3 + y 0 * (u - 1 / 2) := by
    rw [s4ADKRaw_one, hx0_raw, hx1_raw, hx2_raw, hx3_raw, hx4_raw]
    unfold u adkU; ring
  have hH : s4ADKRaw x.1 2 = u + v - 3 / 4 := by
    rw [s4ADKRaw_two, hx01_sq]; ring
  have hZ0_neg : s4ADKRaw x.1 0 < 0 := by
    have hprod_le : |y 0 * y 3| ≤ (y 0 ^ 2 + v) / 2 := by
      unfold v adkV
      rw [abs_mul]
      nlinarith [sq_nonneg (|y 0| - |y 3|), sq_abs (y 0), sq_abs (y 3)]
    have hy03_gt : -(1 / 32) < y 0 * y 3 := by
      have h1 : -(y 0 * y 3) ≤ |y 0 * y 3| := neg_le_abs _
      linarith
    have hu_mid : u - 1 / 2 < -7 / 16 := by linarith [sq_nonneg (y 0)]
    have hfst : x0 * (u - 1 / 2) < (3 / 4) * (-7 / 16) := by nlinarith
    rw [hZ0]
    linarith
  have hnorm_pos : 0 < ‖s4ADKRaw x.1‖ := norm_s4ADKRaw_pos x
  have hmem_west : s4ADKFibration x ∈ s2WestHemisphereOpen.1 := by
    change (s4ADKFibration x).1 0 < 0
    rw [coe_s4ADKFibration, PiLp.smul_apply, smul_eq_mul]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr hnorm_pos) hZ0_neg
  refine ⟨hmem_west, ?_⟩
  have hZsq : s4ADKRaw x.1 0 ^ 2 + s4ADKRaw x.1 1 ^ 2 = adkQ u v := by
    rw [hZ0, hZ1]
    unfold adkQ
    calc
      (x0 * (u - 1 / 2) - y 0 * y 3) ^ 2 + (x0 * y 3 + y 0 * (u - 1 / 2)) ^ 2
        = (x0 ^ 2 + y 0 ^ 2) * ((1 / 2 - u) ^ 2 + y 3 ^ 2) := by ring
      _ = (1 - u - v) * ((1 / 2 - u) ^ 2 + v) := by
        rw [hx0_sq]; unfold v adkV; ring
  have hnorm_sq : ‖s4ADKRaw x.1‖ ^ 2 = adkQ u v + (u + v - 3 / 4) ^ 2 := by
    rw [norm_sq_vec3, hZsq, hH]
  set q := s2WestHemisphereSlice (s4ADKFibration x)
  have hq_val : q = vec2 (‖s4ADKRaw x.1‖⁻¹ * s4ADKRaw x.1 1)
      (‖s4ADKRaw x.1‖⁻¹ * s4ADKRaw x.1 2) := by
    change s2WestHemisphereSlice (⟨s4ADKFibration x, hmem_west⟩ : s2WestHemisphereOpen).1 = _
    rw [s2WestHemisphereSlice_apply]
    refine ext_vec2 rfl rfl
  have hq0 : q 0 = ‖s4ADKRaw x.1‖⁻¹ * s4ADKRaw x.1 1 := by rw [hq_val]; rfl
  have hq1 : q 1 = ‖s4ADKRaw x.1‖⁻¹ * s4ADKRaw x.1 2 := by rw [hq_val]; rfl
  have h1q1 : 1 - q 1 ^ 2 = adkQ u v / ‖s4ADKRaw x.1‖ ^ 2 := by
    rw [hq1, hH]
    field_simp [hnorm_pos.ne']
    linarith [hnorm_sq]
  have hsqrt_q1 : Real.sqrt (1 - q 1 ^ 2) = Real.sqrt (adkQ u v) / ‖s4ADKRaw x.1‖ := by
    rw [h1q1, Real.sqrt_div (adkQ_pos hy).le, Real.sqrt_sq hnorm_pos.le]
  have hcomp0 : adkTgtMap q 0 = indefiniteFoldMap (adkSrcMap y) 0 := by
    have hq_pos : 0 < adkQ u v := adkQ_pos hy
    have hsqrtQ_pos : 0 < Real.sqrt (adkQ u v) := Real.sqrt_pos.mpr hq_pos
    have hfac_pos : 0 < 3 * Real.sqrt (adkQ u v) - 2 * (u + v - 3 / 4) := adkD_factor_pos hy
    have hd_pos : 0 < adkD u v := adkD_pos hy
    have hc1_pos : 0 < 51 / 4 - 13 * v := adkC1_pos hy
    have hp2_pos : 0 < adkP2 u v := adkP2_pos hy
    have hsq_src0 : adkSrcMap y 0 ^ 2 = v * (51 / 4 - 13 * v) / adkD u v := by
      simp only [adkSrcMap, vec4_zero]
      rw [mul_pow, Real.sq_sqrt (div_pos hc1_pos hd_pos).le]
      unfold v adkV
      ring
    have hsq_src1 : adkSrcMap y 1 ^ 2 = y 1 ^ 2 * (2 * adkP2 u v / adkD u v) := by
      simp only [adkSrcMap, vec4_one]
      rw [mul_pow, Real.sq_sqrt (div_pos (mul_pos two_pos hp2_pos) hd_pos).le]
    have hsq_src2 : adkSrcMap y 2 ^ 2 = y 2 ^ 2 * (2 * adkP2 u v / adkD u v) := by
      simp only [adkSrcMap, vec4_two]
      rw [mul_pow, Real.sq_sqrt (div_pos (mul_pos two_pos hp2_pos) hd_pos).le]
    have hlhs : adkTgtMap q 0 = (u + v - 3 / 4) / Real.sqrt (adkQ u v) + 3 / 2 := by
      have h00 : adkTgtMap q 0 = q 1 / Real.sqrt (1 - q 1 ^ 2) + 3 / 2 := rfl
      rw [h00, hsqrt_q1, hq1, hH]
      field_simp [hnorm_pos.ne', hsqrtQ_pos.ne']
    have hrhs : indefiniteFoldMap (adkSrcMap y) 0 =
        (v * (51 / 4 - 13 * v) - u * adkP2 u v) / adkD u v := by
      rw [indefiniteFoldMap_apply_zero, hsq_src0, hsq_src1, hsq_src2]
      have hu_def : y 1 ^ 2 + y 2 ^ 2 = u := rfl
      calc
        v * (51 / 4 - 13 * v) / adkD u v -
            (y 1 ^ 2 * (2 * adkP2 u v / adkD u v) + y 2 ^ 2 * (2 * adkP2 u v / adkD u v)) / 2
          = v * (51 / 4 - 13 * v) / adkD u v -
              (y 1 ^ 2 + y 2 ^ 2) * adkP2 u v / adkD u v := by ring
        _ = (v * (51 / 4 - 13 * v) - u * adkP2 u v) / adkD u v := by rw [hu_def]; ring
    rw [hlhs, hrhs]
    exact adk_single_denom_rat hq_pos hfac_pos rfl (adk_single_denom_identity u v)
  have hcomp1 : adkTgtMap q 1 = indefiniteFoldMap (adkSrcMap y) 1 := by
    have h1q01 : 1 - q 0 ^ 2 - q 1 ^ 2 = (s4ADKRaw x.1 0) ^ 2 / ‖s4ADKRaw x.1‖ ^ 2 := by
      rw [hq0, hq1]
      field_simp [hnorm_pos.ne']
      have h3 := norm_sq_vec3 (s4ADKRaw x.1)
      linarith
    have hsqrt_q01 : -Real.sqrt (1 - q 0 ^ 2 - q 1 ^ 2) =
        ‖s4ADKRaw x.1‖⁻¹ * s4ADKRaw x.1 0 := by
      rw [h1q01, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hnorm_pos.le]
      have hneg0 : Real.sqrt (s4ADKRaw x.1 0 ^ 2) = -s4ADKRaw x.1 0 := by
        rw [show s4ADKRaw x.1 0 ^ 2 = (-s4ADKRaw x.1 0) ^ 2 by ring,
          Real.sqrt_sq (by linarith)]
      rw [hneg0]
      field_simp [hnorm_pos.ne']
    have hhalf_pos : 0 < 1 / 2 - u := by
      have : 0 ≤ y 0 ^ 2 := sq_nonneg _
      linarith
    set a := y 0 / x0
    set b := y 3 / (1 / 2 - u)
    have ha_abs : |a| < 1 := by
      have hy0_le : |y 0| ≤ ‖y‖ := by simpa using (PiLp.norm_apply_le y (0 : Fin 4))
      have hy0_lt : |y 0| < 1 / 4 := lt_of_le_of_lt hy0_le (by
        rw [Metric.mem_ball, dist_zero_right] at hy; exact hy)
      rw [show a = y 0 / x0 from rfl, abs_div, abs_of_pos hx0_pos, div_lt_one hx0_pos]
      linarith
    have hb_abs : |b| < 1 := by
      have hy3_le : |y 3| ≤ ‖y‖ := by simpa using (PiLp.norm_apply_le y (3 : Fin 4))
      have hy3_lt : |y 3| < 1 / 4 := lt_of_le_of_lt hy3_le (by
        rw [Metric.mem_ball, dist_zero_right] at hy; exact hy)
      have hgt7 : 7 / 16 < 1 / 2 - u := by
        have : 0 ≤ y 0 ^ 2 := sq_nonneg _
        linarith
      rw [show b = y 3 / (1 / 2 - u) from rfl, abs_div, abs_of_pos hhalf_pos, div_lt_one hhalf_pos]
      linarith
    have harctan_a : -(Real.pi / 4) < Real.arctan a ∧ Real.arctan a < Real.pi / 4 := by
      rcases abs_lt.mp ha_abs with ⟨hlo, hhi⟩
      rw [← Real.arctan_one]
      refine ⟨?_, Real.arctan_strictMono hhi⟩
      rw [← Real.arctan_neg]
      exact Real.arctan_strictMono hlo
    have harctan_b : -(Real.pi / 4) < Real.arctan b ∧ Real.arctan b < Real.pi / 4 := by
      rcases abs_lt.mp hb_abs with ⟨hlo, hhi⟩
      rw [← Real.arctan_one]
      refine ⟨?_, Real.arctan_strictMono hhi⟩
      rw [← Real.arctan_neg]
      exact Real.arctan_strictMono hlo
    have hx0u_ne : x0 * (u - 1 / 2) - y 0 * y 3 ≠ 0 := by rw [← hZ0]; exact hZ0_neg.ne
    have htan_eq : (a - b) / (1 + a * b) = s4ADKRaw x.1 1 / s4ADKRaw x.1 0 := by
      rw [hZ0, hZ1]
      dsimp only [a, b]
      exact adk_arctan_ratio_alg hx0_pos.ne' hhalf_pos.ne' hx0u_ne
    have harg_eq : q 0 / (-Real.sqrt (1 - q 0 ^ 2 - q 1 ^ 2)) =
        s4ADKRaw x.1 1 / s4ADKRaw x.1 0 := by
      rw [hsqrt_q01, hq0]
      field_simp [hnorm_pos.ne', hZ0_neg.ne]
    simp only [adkTgtMap, vec2_one, indefiniteFoldMap_apply_one, adkSrcMap, vec4_three]
    rw [harg_eq, ← htan_eq, ← tan_arctan_sub_arctan a b,
      Real.arctan_tan (by linarith) (by linarith)]
  exact ext_vec2 hcomp0 hcomp1

private theorem isIndefiniteFoldAt_s4ADKFibration_critBase :
    IsIndefiniteFoldAt (𝓡 4) (𝓡 2) s4ADKFibration s4ADKCritBase := by
  obtain ⟨e_tgt, he_tgt⟩ := exists_fderiv_adkTgtMap
  obtain ⟨Θ_tgt, hΘ_tgt_coe, hΘ_tgt_mem, hΘ_tgt_sub, hΘ_tgt_symm⟩ :=
    TauCeti.ContDiffOn.exists_openPartialHomeomorph contDiffOn_adkTgtMap Metric.isOpen_ball
      adkTgtBase_mem_ball (by simp) he_tgt
  let ψ₀ : PartialDiffeomorph (𝓡 2) (𝓡 2) EuclideanPlane EuclideanPlane ∞ :=
    TauCeti.PartialDiffeomorph.ofOpenPartialHomeomorph Θ_tgt
      (hΘ_tgt_coe ▸ contDiffOn_adkTgtMap.mono hΘ_tgt_sub) hΘ_tgt_symm
  have hψ₀_pe : ψ₀.toPartialEquiv = Θ_tgt.toPartialEquiv :=
    TauCeti.PartialDiffeomorph.ofOpenPartialHomeomorph_toPartialEquiv Θ_tgt _ hΘ_tgt_symm
  have hψ₀_src : ψ₀.source = Θ_tgt.source := by
    rw [hψ₀_pe]
  have hψ₀_coe : ⇑ψ₀ = ⇑Θ_tgt := by
    change ⇑ψ₀.toPartialEquiv = ⇑Θ_tgt.toPartialEquiv
    rw [hψ₀_pe]
  let ψ : PartialDiffeomorph (𝓡 2) (𝓡 2) Sphere2 EuclideanPlane ∞ :=
    s2WestHemisphereSlice.trans ψ₀
  have h0_mem : (0 : EuclideanSpace ℝ (Fin 4)) ∈
      Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) (1 / 4) := by
    simp
  obtain ⟨e_src, he_src⟩ := exists_fderiv_adkSrcMap
  obtain ⟨Θ_src, hΘ_src_coe, hΘ_src_mem, hΘ_src_sub, hΘ_src_symm⟩ :=
    TauCeti.ContDiffOn.exists_openPartialHomeomorph contDiffOn_adkSrcMap Metric.isOpen_ball
      h0_mem (by simp) he_src
  let φ₀ : PartialDiffeomorph (𝓡 4) (𝓡 4)
      (EuclideanSpace ℝ (Fin 4)) (EuclideanSpace ℝ (Fin 4)) ∞ :=
    TauCeti.PartialDiffeomorph.ofOpenPartialHomeomorph Θ_src
      (hΘ_src_coe ▸ contDiffOn_adkSrcMap.mono hΘ_src_sub) hΘ_src_symm
  have hφ₀_pe : φ₀.toPartialEquiv = Θ_src.toPartialEquiv :=
    TauCeti.PartialDiffeomorph.ofOpenPartialHomeomorph_toPartialEquiv Θ_src _ hΘ_src_symm
  have hφ₀_src : φ₀.source = Θ_src.source := by
    rw [hφ₀_pe]
  have hφ₀_coe : ⇑φ₀ = ⇑Θ_src := by
    change ⇑φ₀.toPartialEquiv = ⇑Θ_src.toPartialEquiv
    rw [hφ₀_pe]
  let φ₁ : PartialDiffeomorph (𝓡 4) (𝓡 4) Sphere4 (EuclideanSpace ℝ (Fin 4)) ∞ :=
    s4EastHemisphereSlice.trans φ₀
  let φ : PartialDiffeomorph (𝓡 4) (𝓡 4) Sphere4 (EuclideanSpace ℝ (Fin 4)) ∞ :=
    φ₁.restrOpen (s4ADKFibration ⁻¹' ψ.source)
      (ψ.open_source.preimage contMDiff_s4ADKFibration.continuous)
  have hval0 : s4EastHemisphereSlice s4ADKCritBase = 0 := by
    change s4EastHemisphereSlice (⟨s4ADKCritBase, s4ADKCritBase_mem_east⟩ :
      s4EastHemisphereOpen).1 = 0
    rw [s4EastHemisphereSlice_apply]
    refine ext_vec4 rfl rfl rfl rfl
  have hp_φ₁ : s4ADKCritBase ∈ φ₁.source := by
    rw [PartialDiffeomorph.trans_source, s4EastHemisphereSlice_source]
    refine ⟨s4ADKCritBase_mem_east, ?_⟩
    show s4EastHemisphereSlice s4ADKCritBase ∈ φ₀.source
    rw [hφ₀_src, hval0]
    exact hΘ_src_mem
  have hfp_ψ : s4ADKFibration s4ADKCritBase ∈ ψ.source := by
    rw [PartialDiffeomorph.trans_source, s2WestHemisphereSlice_source]
    refine ⟨s4ADKCritBase_image_mem_west, ?_⟩
    show s2WestHemisphereSlice (s4ADKFibration s4ADKCritBase) ∈ ψ₀.source
    rw [hψ₀_src, s2WestHemisphereSlice_critBase]
    exact hΘ_tgt_mem
  have hp_φ : s4ADKCritBase ∈ φ.source := by
    rw [PartialDiffeomorph.restrOpen_source]
    exact ⟨hp_φ₁, hfp_ψ⟩
  refine ⟨φ, ψ, hp_φ, hfp_ψ, ?_, ?_, ?_⟩
  · simp only [φ, PartialDiffeomorph.coe_restrOpen, φ₁, PartialDiffeomorph.coe_trans,
      Function.comp_apply]
    rw [hφ₀_coe, hval0, hΘ_src_coe]
    exact adkSrcMap_zero
  · simp only [ψ, PartialDiffeomorph.coe_trans, Function.comp_apply]
    rw [hψ₀_coe, s2WestHemisphereSlice_critBase, hΘ_tgt_coe, adkTgtMap_critBase]
    refine ext_vec2 (by simp [indefiniteFoldMap]) (by simp [indefiniteFoldMap])
  · intro x hx
    rw [PartialDiffeomorph.restrOpen_source] at hx
    refine ⟨hx.2, ?_⟩
    have hx_φ₁ := hx.1
    rw [PartialDiffeomorph.trans_source, s4EastHemisphereSlice_source] at hx_φ₁
    rcases hx_φ₁ with ⟨hx_east, hy_src⟩
    set y : EuclideanSpace ℝ (Fin 4) := s4EastHemisphereSlice x
    have hy_src' : y ∈ Θ_src.source := by rwa [← hφ₀_src]
    have hy_mem : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) (1 / 4) :=
      hΘ_src_sub hy_src'
    have hx_left : s4EastHemisphereSlice.symm y = x := by
      change s4EastHemisphereSlice.toPartialEquiv.symm (s4EastHemisphereSlice x) = x
      exact s4EastHemisphereSlice.left_inv (s4EastHemisphereSlice_source ▸ hx_east)
    have hmain := (adkTgtMap_comp_eq_indefiniteFoldMap hy_mem).2
    rw [hx_left] at hmain
    have hφx : φ x = adkSrcMap y := by
      simp only [φ, PartialDiffeomorph.coe_restrOpen, φ₁, PartialDiffeomorph.coe_trans,
        Function.comp_apply]
      rw [hφ₀_coe, hΘ_src_coe]
    have hψfx : ψ (s4ADKFibration x) =
        adkTgtMap (s2WestHemisphereSlice (s4ADKFibration x)) := by
      simp only [ψ, PartialDiffeomorph.coe_trans, Function.comp_apply]
      rw [hψ₀_coe, hΘ_tgt_coe]
    rw [hφx, hψfx, hmain]

/-- Every critical point of `s4ADKFibration` is an **indefinite quadratic fold**
(`IsIndefiniteFoldAt`, Eq. (2) of ADK05). -/
-- tier: T2
theorem isIndefiniteFoldAt_s4ADKFibration {x : Sphere4}
    (hx : x ∈ criticalPoints (𝓡 4) (𝓡 2) s4ADKFibration) :
    IsIndefiniteFoldAt (𝓡 4) (𝓡 2) s4ADKFibration x := by
  rw [criticalPoints_s4ADKFibration] at hx
  rcases hx with ⟨hx2, hx3, hx4⟩
  have hcirc : x.1 0 ^ 2 + x.1 1 ^ 2 = 1 := by
    have hsph := mem_sphere_zero_iff_norm.mp x.2
    have hsq : ‖x.1‖ ^ 2 = 1 := by rw [hsph]; norm_num
    rw [norm_sq_vec5, hx2, hx3, hx4] at hsq
    linarith
  have hcs : x.1 0 ^ 2 + (-x.1 1) ^ 2 = 1 := by nlinarith
  have hrot : s4Rot01 (x.1 0) (-x.1 1) hcs x = s4ADKCritBase := by
    apply Subtype.ext
    refine ext_vec5 ?_ ?_ hx2 hx3 hx4
    · simp only [coe_s4Rot01, vec5_zero, s4ADKCritBase]
      linear_combination hcirc
    · simp only [coe_s4Rot01, vec5_one, s4ADKCritBase]
      ring
  refine isLocallyModeledOn_of_diffeomorph_conj (s4Rot01 (x.1 0) (-x.1 1) hcs)
    (s2Rot01 (x.1 0) (-x.1 1) hcs) (f := s4ADKFibration) ?_ ?_
  · intro z
    exact (s4ADKFibration_s4Rot01 (x.1 0) (-x.1 1) hcs z).symm
  · rw [hrot]
    exact isIndefiniteFoldAt_s4ADKFibration_critBase

end IndefiniteFoldLocalNormalForm

/-! ## 4. Regular Disk Trivialization, Co-Orientation & ADK Headline Theorems (`LW4`) -/

section ADKTrivializationAndTheorems

/-- Origin `(0 : ℝ²)` as a point of `s4PlaneDisk`. -/
noncomputable def s4PlaneDiskZero : s4PlaneDisk :=
  ⟨0, Metric.mem_ball_self s4BaseDiskRadius_pos⟩

/-- Coercion of `s4PlaneDiskZero` to `EuclideanPlane` is `0`. -/
@[simp]
theorem coe_s4PlaneDiskZero : (s4PlaneDiskZero : EuclideanPlane) = 0 :=
  rfl

/-- Strict positivity of the vertical ADK component over `s4PlaneDisk × Sphere2`. -/
theorem s4ADKRaw_s4PlaneEmbed_coord2_pos (wz : s4PlaneDisk × Sphere2) :
    0 < s4ADKRaw (s4PlaneEmbed wz).1 2 := by
  have hw : wz.1.1 0 ^ 2 + wz.1.1 1 ^ 2 < 1 / 4 := by
    have hn : ‖wz.1.1‖ < 1 / 2 := norm_lt_half_of_mem_s4PlaneDisk wz.1
    have hsq : ‖wz.1.1‖ ^ 2 < (1 / 2) ^ 2 := by nlinarith [norm_nonneg wz.1.1]
    rw [norm_sq_plane] at hsq
    linarith
  have h2 : s4ADKRaw (s4PlaneEmbed wz).1 2 = 1 / 4 - (wz.1.1 0 ^ 2 + wz.1.1 1 ^ 2) := by
    simp [s4ADKRaw, s4PlaneEmbed, s4PlaneEmbedRaw]
  linarith

/-- Image of `s4PlaneEmbed` under `s4ADKFibration` avoids `s2SouthPole`. -/
theorem s4ADKFibration_s4PlaneEmbed_ne_southPole (wz : s4PlaneDisk × Sphere2) :
    s4ADKFibration (s4PlaneEmbed wz) ≠ s2SouthPole := by
  intro h
  have hc := congrArg (fun z : Sphere2 ↦ z.1 2) h
  rw [coe_s4ADKFibration, PiLp.smul_apply, smul_eq_mul] at hc
  have hpos :
      0 < ‖s4ADKRaw (s4PlaneEmbed wz).1‖⁻¹ * s4ADKRaw (s4PlaneEmbed wz).1 2 :=
    mul_pos (inv_pos.mpr (norm_s4ADKRaw_pos _)) (s4ADKRaw_s4PlaneEmbed_coord2_pos wz)
  have hsp : s2SouthPole.1 2 = -1 := rfl
  linarith

/-- Base stereographic coordinate map
`g_adk (w, z) = southPoleStereoChart (s4ADKFibration (s4PlaneEmbed (w, z)))`. -/
-- tier: T2
noncomputable def g_adk (wz : s4PlaneDisk × Sphere2) : EuclideanPlane :=
  southPoleStereoChart (s4ADKFibration (s4PlaneEmbed wz))

/-- Smoothness of `g_adk : s4PlaneDisk × Sphere2 → EuclideanPlane`. -/
-- tier: T2
theorem contMDiff_g_adk : ContMDiff ((𝓡 2).prod (𝓡 2)) (𝓡 2) ∞ g_adk := by
  let hpunct : s4PlaneDisk × Sphere2 → s2PuncturedSouth := fun wz ↦
    ⟨s4ADKFibration (s4PlaneEmbed wz), s4ADKFibration_s4PlaneEmbed_ne_southPole wz⟩
  have hhpunct : ContMDiff ((𝓡 2).prod (𝓡 2)) (𝓡 2) ∞ hpunct :=
    (TauCeti.ContMDiff.subtypeVal_comp_iff s2PuncturedSouth _).mp
      (contMDiff_s4ADKFibration.comp contMDiff_s4PlaneEmbed)
  have heq : g_adk = ⇑southPoleStereoDiffeomorph.symm ∘ hpunct := rfl
  rw [heq]
  exact southPoleStereoDiffeomorph.symm.contMDiff.comp hhpunct

/-- Recovery of `s4ADKFibration ∘ s4PlaneEmbed` from `southPoleStereoInv ∘ g_adk`. -/
theorem southPoleStereoInv_g_adk (wz : s4PlaneDisk × Sphere2) :
    southPoleStereoInv (g_adk wz) = s4ADKFibration (s4PlaneEmbed wz) :=
  southPoleStereoInv_chart (s4ADKFibration_s4PlaneEmbed_ne_southPole wz)

/-- `g_adk` maps the central fiber `{0} × Sphere2` to `0`. -/
@[simp]
theorem g_adk_zero_left (z : Sphere2) : g_adk (s4PlaneDiskZero, z) = 0 := by
  have hnp : s4ADKFibration (s4PlaneEmbed (s4PlaneDiskZero, z)) = s2NorthPole := by
    rw [s4ADKFibration_eq_northPole_iff]
    exact ⟨rfl, rfl⟩
  simp only [g_adk, hnp, ← southPoleStereoInv_zero, southPoleStereoChart_inv]

/-- Product local trivialization candidate `Ψ_adk (w, z) = (g_adk (w, z), z)`. -/
-- tier: T2
noncomputable def Ψ_adk (wz : s4PlaneDisk × Sphere2) : EuclideanPlane × Sphere2 :=
  (g_adk wz, wz.2)

/-- Smoothness of `Ψ_adk`. -/
-- tier: T2
theorem contMDiff_Ψ_adk :
    ContMDiff ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) ∞ Ψ_adk :=
  contMDiff_g_adk.prodMk contMDiff_snd

/-- Injectivity of `Ψ_adk` along `{0} × Sphere2`. -/
theorem injOn_Ψ_adk_zeroSlice :
    Set.InjOn Ψ_adk (({s4PlaneDiskZero} : Set s4PlaneDisk) ×ˢ (Set.univ : Set Sphere2)) := by
  rintro ⟨w₁, z₁⟩ ⟨hw₁, -⟩ ⟨w₂, z₂⟩ ⟨hw₂, -⟩ hEq
  rw [Set.mem_singleton_iff] at hw₁ hw₂
  have hz : z₁ = z₂ := congrArg Prod.snd hEq
  exact Prod.ext (hw₁.trans hw₂.symm) hz

private noncomputable def adkGRaw (z : Sphere2) (u : EuclideanPlane) : EuclideanPlane :=
  let ρ := Real.sqrt (1 - (u 0 ^ 2 + u 1 ^ 2))
  let W := s4ADKRaw (vec5 (u 0) (u 1) (ρ * z.1 0) (ρ * z.1 1) (ρ * z.1 2))
  vec2 (2 * W 0 / (‖W‖ + W 2)) (2 * W 1 / (‖W‖ + W 2))

private theorem g_adk_eq_adkGRaw (w : s4PlaneDisk) (z : Sphere2) :
    g_adk (w, z) = adkGRaw z w.1 := by
  let x := s4PlaneEmbed (w, z)
  let W := s4ADKRaw x.1
  have hW_pos : 0 < ‖W‖ := norm_s4ADKRaw_pos x
  have hW2_pos : 0 < W 2 := s4ADKRaw_s4PlaneEmbed_coord2_pos (w, z)
  have hden1 : 1 + ‖W‖⁻¹ * W 2 ≠ 0 := by positivity
  have hden2 : ‖W‖ + W 2 ≠ 0 := by positivity
  have hcomp (c : ℝ) :
      2 * (‖W‖⁻¹ * c) / (1 + ‖W‖⁻¹ * W 2) = 2 * c / (‖W‖ + W 2) := by
    rw [div_eq_div_iff hden1 hden2]
    field_simp [hW_pos.ne']
  have hW_eq :
      s4ADKRaw (vec5 (w.1 0) (w.1 1)
        (Real.sqrt (1 - (w.1 0 ^ 2 + w.1 1 ^ 2)) * z.1 0)
        (Real.sqrt (1 - (w.1 0 ^ 2 + w.1 1 ^ 2)) * z.1 1)
        (Real.sqrt (1 - (w.1 0 ^ 2 + w.1 1 ^ 2)) * z.1 2)) = W :=
    rfl
  refine ext_vec2 ?_ ?_
  · change 2 * (‖W‖⁻¹ * W 0) / (1 + ‖W‖⁻¹ * W 2) = _
    dsimp only [adkGRaw]
    rw [hW_eq]
    exact hcomp (W 0)
  · change 2 * (‖W‖⁻¹ * W 1) / (1 + ‖W‖⁻¹ * W 2) = _
    dsimp only [adkGRaw]
    rw [hW_eq]
    exact hcomp (W 1)

private noncomputable def adkCoeffA (z : Sphere2) : ℝ := z.1 0 ^ 2 + z.1 1 ^ 2 - 1 / 2

private noncomputable def adkCoeffB (z : Sphere2) : ℝ := z.1 2

private theorem adkCoeff_sq_sum_pos (z : Sphere2) :
    0 < adkCoeffA z ^ 2 + adkCoeffB z ^ 2 := by
  have hz : z.1 0 ^ 2 + z.1 1 ^ 2 + z.1 2 ^ 2 = 1 := by
    rw [← norm_sq_vec3, mem_sphere_zero_iff_norm.mp z.2, one_pow]
  have hid : adkCoeffA z ^ 2 + adkCoeffB z ^ 2 = 1 / 4 + z.1 2 ^ 4 := by
    unfold adkCoeffA adkCoeffB
    rw [show z.1 0 ^ 2 + z.1 1 ^ 2 - 1 / 2 = 1 / 2 - z.1 2 ^ 2 from by linarith]
    ring
  rw [hid]
  positivity

private theorem hasFDerivAt_adkGRaw_zero (z : Sphere2) :
    HasFDerivAt (adkGRaw z)
      (clmVec2
        ((4 * adkCoeffA z) • euclidProj 0 - (4 * adkCoeffB z) • euclidProj 1)
        ((4 * adkCoeffB z) • euclidProj 0 + (4 * adkCoeffA z) • euclidProj 1)) 0 := by
  let ρ : EuclideanPlane → ℝ := fun u ↦ Real.sqrt (1 - (u 0 ^ 2 + u 1 ^ 2))
  let W : EuclideanPlane → EuclideanSpace ℝ (Fin 3) := fun u ↦
    s4ADKRaw (vec5 (u 0) (u 1) (ρ u * z.1 0) (ρ u * z.1 1) (ρ u * z.1 2))
  have hu (i : Fin 2) : DifferentiableAt ℝ (fun u : EuclideanPlane ↦ u i) 0 :=
    (euclidProj i).differentiableAt
  have hrad_diff : DifferentiableAt ℝ (fun u : EuclideanPlane ↦ 1 - (u 0 ^ 2 + u 1 ^ 2)) 0 :=
    (differentiableAt_const _).sub (((hu 0).pow 2).add ((hu 1).pow 2))
  have hρ_diff : DifferentiableAt ℝ ρ 0 := hrad_diff.sqrt (by norm_num)
  have hρ_0 : ρ 0 = 1 := by simp [ρ]
  let A : EuclideanPlane → ℝ := fun u ↦ (ρ u * z.1 0) ^ 2 + (ρ u * z.1 1) ^ 2 - 1 / 2
  let B : EuclideanPlane → ℝ := fun u ↦ ρ u * z.1 2
  have hA_diff : DifferentiableAt ℝ A 0 :=
    (((hρ_diff.mul_const (z.1 0)).pow 2).add ((hρ_diff.mul_const (z.1 1)).pow 2)).sub
      (differentiableAt_const _)
  have hB_diff : DifferentiableAt ℝ B 0 := hρ_diff.mul_const (z.1 2)
  have hA_0 : A 0 = adkCoeffA z := by simp [A, hρ_0, adkCoeffA]
  have hB_0 : B 0 = adkCoeffB z := by simp [B, hρ_0, adkCoeffB]
  have hW0_eq : (fun u ↦ W u 0) = fun u ↦ u 0 * A u - u 1 * B u := by
    funext u; simp [W, A, B, s4ADKRaw_zero]
  have hW1_eq : (fun u ↦ W u 1) = fun u ↦ u 0 * B u + u 1 * A u := by
    funext u; simp [W, A, B, s4ADKRaw_one]
  have hW2_diff : DifferentiableAt ℝ (fun u ↦ W u 2) 0 := by
    have heq : (fun u ↦ W u 2) = fun u ↦ 1 / 4 - (u 0 ^ 2 + u 1 ^ 2) := by
      funext u; simp [W, s4ADKRaw_two]
    rw [heq]
    exact (differentiableAt_const _).sub (((hu 0).pow 2).add ((hu 1).pow 2))
  have hW0 : HasFDerivAt (fun u ↦ W u 0)
      (adkCoeffA z • euclidProj 0 - adkCoeffB z • euclidProj 1) 0 := by
    rw [hW0_eq]
    refine (((euclidProj 0).hasFDerivAt.mul hA_diff.hasFDerivAt).sub
      ((euclidProj 1).hasFDerivAt.mul hB_diff.hasFDerivAt)).congr_fderiv ?_
    ext v
    simp [hA_0, hB_0, sub_apply, smul_apply, smul_eq_mul]
  have hW1 : HasFDerivAt (fun u ↦ W u 1)
      (adkCoeffB z • euclidProj 0 + adkCoeffA z • euclidProj 1) 0 := by
    rw [hW1_eq]
    refine (((euclidProj 0).hasFDerivAt.mul hB_diff.hasFDerivAt).add
      ((euclidProj 1).hasFDerivAt.mul hA_diff.hasFDerivAt)).congr_fderiv ?_
    ext v
    simp [hA_0, hB_0, add_apply, smul_apply, smul_eq_mul]
  have hW_0_val : W 0 = vec3 0 0 (1 / 4) := by
    refine ext_vec3 ?_ ?_ ?_ <;> simp [W, ρ, s4ADKRaw]
  have hW0_norm : ‖W 0‖ = 1 / 4 := by
    have hsq : ‖W 0‖ ^ 2 = (1 / 4) ^ 2 := by
      rw [hW_0_val, norm_sq_vec3]; norm_num
    nlinarith [norm_nonneg (W 0)]
  have hW_diff : DifferentiableAt ℝ W 0 := by
    have hvec : DifferentiableAt ℝ
        (fun u : EuclideanPlane ↦
          vec5 (u 0) (u 1) (ρ u * z.1 0) (ρ u * z.1 1) (ρ u * z.1 2)) 0 := by
      have hpi : DifferentiableAt ℝ
          (fun u : EuclideanPlane ↦ ![u 0, u 1, ρ u * z.1 0, ρ u * z.1 1, ρ u * z.1 2]) 0 := by
        refine differentiableAt_pi.mpr fun i ↦ ?_
        fin_cases i
        · exact hu 0
        · exact hu 1
        · exact hρ_diff.mul_const _
        · exact hρ_diff.mul_const _
        · exact hρ_diff.mul_const _
      exact ((EuclideanSpace.equiv (Fin 5) ℝ).symm.differentiableAt).comp 0 hpi
    exact (contDiff_s4ADKRaw.contDiffAt.differentiableAt (by simp)).comp 0 hvec
  have hW0_ne : W 0 ≠ 0 := by
    rw [hW_0_val]
    intro h
    have hc := congrArg (fun q : EuclideanSpace ℝ (Fin 3) ↦ q 2) h
    simp at hc
  have hW_norm_diff : DifferentiableAt ℝ (fun u ↦ ‖W u‖) 0 :=
    DifferentiableAt.norm ℝ hW_diff hW0_ne
  have hden_0 : ‖W 0‖ + W 0 2 = 1 / 2 := by
    rw [hW0_norm, hW_0_val, vec3_two]; norm_num
  have hden_inv_diff : DifferentiableAt ℝ (fun u ↦ (‖W u‖ + W u 2)⁻¹) 0 :=
    (hW_norm_diff.add hW2_diff).inv (by change ‖W 0‖ + W 0 2 ≠ 0; rw [hden_0]; norm_num)
  have hg0_eq :
      (fun u ↦ adkGRaw z u 0) = fun u ↦ (2 * W u 0) * (‖W u‖ + W u 2)⁻¹ :=
    funext fun u ↦ div_eq_mul_inv _ _
  have hg1_eq :
      (fun u ↦ adkGRaw z u 1) = fun u ↦ (2 * W u 1) * (‖W u‖ + W u 2)⁻¹ :=
    funext fun u ↦ div_eq_mul_inv _ _
  have hg0 : HasFDerivAt (fun u ↦ adkGRaw z u 0)
      ((4 * adkCoeffA z) • euclidProj 0 - (4 * adkCoeffB z) • euclidProj 1) 0 := by
    rw [hg0_eq]
    have h2W0 : W 0 0 = 0 := by rw [hW_0_val]; rfl
    refine ((hW0.const_mul 2).mul hden_inv_diff.hasFDerivAt).congr_fderiv ?_
    ext v
    simp only [h2W0, mul_zero, zero_smul, hden_0, smul_apply, sub_apply, smul_eq_mul]
    norm_num
    ring
  have hg1 : HasFDerivAt (fun u ↦ adkGRaw z u 1)
      ((4 * adkCoeffB z) • euclidProj 0 + (4 * adkCoeffA z) • euclidProj 1) 0 := by
    rw [hg1_eq]
    have h2W1 : W 0 1 = 0 := by rw [hW_0_val]; rfl
    refine ((hW1.const_mul 2).mul hden_inv_diff.hasFDerivAt).congr_fderiv ?_
    ext v
    simp only [h2W1, mul_zero, zero_smul, hden_0, smul_apply, add_apply, smul_eq_mul]
    norm_num
    ring
  exact hasFDerivAt_vec2 hg0 hg1

private theorem mfderiv_g_adk_zero_left_slice (z : Sphere2)
    (u : TangentSpace (𝓡 2) s4PlaneDiskZero) :
    let uE : EuclideanPlane := u
    mfderiv (𝓡 2) (𝓡 2) (fun w : s4PlaneDisk ↦ g_adk (w, z)) s4PlaneDiskZero u =
      vec2 (4 * adkCoeffA z * uE 0 - 4 * adkCoeffB z * uE 1)
        (4 * adkCoeffB z * uE 0 + 4 * adkCoeffA z * uE 1) := by
  intro uE
  have hcomp : (fun w : s4PlaneDisk ↦ g_adk (w, z)) =
      adkGRaw z ∘ (Subtype.val : s4PlaneDisk → EuclideanPlane) :=
    funext fun w ↦ g_adk_eq_adkGRaw w z
  have hdf := hasFDerivAt_adkGRaw_zero z
  have hdf0 : DifferentiableAt ℝ (adkGRaw z) s4PlaneDiskZero.1 := by
    simpa only [coe_s4PlaneDiskZero] using hdf.differentiableAt
  have hsub_at : MDifferentiableAt (𝓡 2) 𝓘(ℝ, EuclideanPlane)
      (Subtype.val : s4PlaneDisk → EuclideanPlane) s4PlaneDiskZero :=
    (contMDiff_subtype_val (n := ∞) s4PlaneDiskZero).mdifferentiableAt (by simp)
  have h1 :
      mvfderiv (𝓡 2) (adkGRaw z ∘ (Subtype.val : s4PlaneDisk → EuclideanPlane))
          s4PlaneDiskZero u =
        fderiv ℝ (adkGRaw z) s4PlaneDiskZero.1
          (mvfderiv (𝓡 2) (Subtype.val : s4PlaneDisk → EuclideanPlane) s4PlaneDiskZero u) :=
    TauCeti.mvfderiv_comp_apply_of_differentiableAt hdf0 hsub_at u
  have hsub_u :
      mvfderiv (𝓡 2) (Subtype.val : s4PlaneDisk → EuclideanPlane) s4PlaneDiskZero u = uE :=
    TauCeti.Manifold.mvfderiv_subtype_val_apply s4PlaneDiskZero u
  have heq :
      mfderiv (𝓡 2) (𝓡 2) (fun w : s4PlaneDisk ↦ g_adk (w, z)) s4PlaneDiskZero u =
        mvfderiv (𝓡 2) (adkGRaw z ∘ (Subtype.val : s4PlaneDisk → EuclideanPlane))
          s4PlaneDiskZero u := by
    rw [hcomp]
    rfl
  rw [heq, h1, hsub_u, coe_s4PlaneDiskZero, hdf.fderiv, clmVec2_apply]
  refine ext_vec2 ?_ ?_ <;>
    simp [sub_apply, add_apply, smul_apply, smul_eq_mul]

private theorem mfderiv_g_adk_zero_left (z : Sphere2)
    (v : TangentSpace ((𝓡 2).prod (𝓡 2)) (s4PlaneDiskZero, z)) :
    let v1 : EuclideanPlane := v.1
    mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 2) g_adk (s4PlaneDiskZero, z) v =
      vec2 (4 * adkCoeffA z * v1 0 - 4 * adkCoeffB z * v1 1)
        (4 * adkCoeffB z * v1 0 + 4 * adkCoeffA z * v1 1) := by
  have hg_diff : MDifferentiableAt ((𝓡 2).prod (𝓡 2)) (𝓡 2) g_adk (s4PlaneDiskZero, z) :=
    (contMDiff_g_adk (s4PlaneDiskZero, z)).mdifferentiableAt (by simp)
  have hsplit :
      mvfderiv ((𝓡 2).prod (𝓡 2)) g_adk (s4PlaneDiskZero, z) v =
        mvfderiv (𝓡 2) (fun w : s4PlaneDisk ↦ g_adk (w, z)) s4PlaneDiskZero v.1 +
          mvfderiv (𝓡 2) (fun q : Sphere2 ↦ g_adk (s4PlaneDiskZero, q)) z v.2 :=
    hg_diff.mvfderiv_prod_eq_add_apply v
  have hconst_zero :
      mvfderiv (𝓡 2) (fun q : Sphere2 ↦ g_adk (s4PlaneDiskZero, q)) z v.2 = 0 := by
    have hfun : (fun q : Sphere2 ↦ g_adk (s4PlaneDiskZero, q)) = fun _ ↦ (0 : EuclideanPlane) :=
      funext fun q ↦ g_adk_zero_left q
    change mfderiv (𝓡 2) (𝓡 2) (fun q : Sphere2 ↦ g_adk (s4PlaneDiskZero, q)) z v.2 = 0
    rw [hfun, mfderiv_const]
    rfl
  change mvfderiv ((𝓡 2).prod (𝓡 2)) g_adk (s4PlaneDiskZero, z) v = _
  rw [hsplit, hconst_zero, add_zero]
  exact mfderiv_g_adk_zero_left_slice z v.1

private theorem isLocalDiffeomorphAt_Ψ_adk_zero_left (z : Sphere2) :
    IsLocalDiffeomorphAt ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) ∞
      Ψ_adk (s4PlaneDiskZero, z) := by
  have hΨ_diff :
      MDifferentiableAt ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) Ψ_adk (s4PlaneDiskZero, z) :=
    (contMDiff_Ψ_adk (s4PlaneDiskZero, z)).mdifferentiableAt (by simp)
  have hinj :
      Function.Injective
        (mfderiv ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) Ψ_adk (s4PlaneDiskZero, z)) := by
    intro v₁ v₂ hEq
    suffices v₁ - v₂ = 0 from sub_eq_zero.mp this
    set v := v₁ - v₂
    have hv :
        mfderiv ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) Ψ_adk (s4PlaneDiskZero, z) v = 0 := by
      simp only [v, map_sub, hEq, sub_self]
    have hv_snd :
        mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 2) (Prod.snd ∘ Ψ_adk) (s4PlaneDiskZero, z) v = 0 := by
      rw [mfderiv_comp _ mdifferentiableAt_snd hΨ_diff, ContinuousLinearMap.comp_apply, hv,
        map_zero]
    have hv2 : v.2 = 0 := by
      have h1 : mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 2) Prod.snd (s4PlaneDiskZero, z) v = 0 := hv_snd
      rw [mfderiv_snd] at h1
      exact h1
    have hv_fst :
        mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 2) (Prod.fst ∘ Ψ_adk) (s4PlaneDiskZero, z) v = 0 := by
      rw [mfderiv_comp _ mdifferentiableAt_fst hΨ_diff, ContinuousLinearMap.comp_apply, hv,
        map_zero]
    have hg0 : mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 2) g_adk (s4PlaneDiskZero, z) v = 0 :=
      hv_fst
    rw [mfderiv_g_adk_zero_left z v] at hg0
    let v1 : EuclideanPlane := v.1
    have h0 : 4 * adkCoeffA z * v1 0 - 4 * adkCoeffB z * v1 1 = 0 :=
      congrArg (fun w : EuclideanPlane ↦ w 0) hg0
    have h1 : 4 * adkCoeffB z * v1 0 + 4 * adkCoeffA z * v1 1 = 0 :=
      congrArg (fun w : EuclideanPlane ↦ w 1) hg0
    have hsum := adkCoeff_sq_sum_pos z
    have hx0_mul : 4 * (adkCoeffA z ^ 2 + adkCoeffB z ^ 2) * v1 0 = 0 := by
      linear_combination adkCoeffA z * h0 + adkCoeffB z * h1
    have hx1_mul : 4 * (adkCoeffA z ^ 2 + adkCoeffB z ^ 2) * v1 1 = 0 := by
      linear_combination -adkCoeffB z * h0 + adkCoeffA z * h1
    have h4_ne : 4 * (adkCoeffA z ^ 2 + adkCoeffB z ^ 2) ≠ 0 := by positivity
    have hx0 : v1 0 = 0 := (mul_eq_zero.mp hx0_mul).resolve_left h4_ne
    have hx1 : v1 1 = 0 := (mul_eq_zero.mp hx1_mul).resolve_left h4_ne
    have hv1 : v.1 = 0 := ext_vec2 hx0 hx1
    exact Prod.ext hv1 hv2
  exact TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv contMDiff_Ψ_adk.contMDiffOn
    isOpen_univ (Set.mem_univ _) BoundarylessManifold.isInteriorPoint (by simp) hinj rfl

private noncomputable def adkProdBasis (w : s4PlaneDisk) (z : Sphere2) :
    Module.Basis (Fin 4) ℝ (TangentSpace ((𝓡 2).prod (𝓡 2)) (w, z)) :=
  let bW : Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) w) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  let bZ : Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  let eProd := TauCeti.Manifold.tangentSpaceProdEquiv (I := 𝓡 2) (J := 𝓡 2) (w, z)
  ((bW.prod bZ).reindex finSumFinEquiv).map eProd.symm.toLinearEquiv

private theorem adkProdBasis_eq (w : s4PlaneDisk) (z : Sphere2) :
    let bW : Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) w) :=
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    let bZ : Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z) :=
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    let eProd := TauCeti.Manifold.tangentSpaceProdEquiv (I := 𝓡 2) (J := 𝓡 2) (w, z)
    (⇑(adkProdBasis w z) : Fin 4 → _) =
      ![eProd.symm (bW 0, 0), eProd.symm (bW 1, 0),
        eProd.symm (0, bZ 0), eProd.symm (0, bZ 1)] := by
  intro bW bZ eProd
  have hbProd_apply (i : Fin 4) :
      adkProdBasis w z i = eProd.symm ((bW.prod bZ) (finSumFinEquiv.symm i)) := by
    simp [adkProdBasis, bW, bZ, eProd, Module.Basis.map_apply, Module.Basis.reindex_apply]
  have hb0 : adkProdBasis w z 0 = eProd.symm (bW 0, 0) := by
    have hs : finSumFinEquiv.symm (0 : Fin (2 + 2)) = Sum.inl 0 :=
      finSumFinEquiv.symm_apply_eq.mpr rfl
    rw [hbProd_apply 0, hs]
    exact congrArg eProd.symm
      (Prod.ext (Module.Basis.prod_apply_inl_fst bW bZ 0)
        (Module.Basis.prod_apply_inl_snd bW bZ 0))
  have hb1 : adkProdBasis w z 1 = eProd.symm (bW 1, 0) := by
    have hs : finSumFinEquiv.symm (1 : Fin (2 + 2)) = Sum.inl 1 :=
      finSumFinEquiv.symm_apply_eq.mpr rfl
    rw [hbProd_apply 1, hs]
    exact congrArg eProd.symm
      (Prod.ext (Module.Basis.prod_apply_inl_fst bW bZ 1)
        (Module.Basis.prod_apply_inl_snd bW bZ 1))
  have hb2 : adkProdBasis w z 2 = eProd.symm (0, bZ 0) := by
    have hs : finSumFinEquiv.symm (2 : Fin (2 + 2)) = Sum.inr 0 :=
      finSumFinEquiv.symm_apply_eq.mpr rfl
    rw [hbProd_apply 2, hs]
    exact congrArg eProd.symm
      (Prod.ext (Module.Basis.prod_apply_inr_fst bW bZ 0)
        (Module.Basis.prod_apply_inr_snd bW bZ 0))
  have hb3 : adkProdBasis w z 3 = eProd.symm (0, bZ 1) := by
    have hs : finSumFinEquiv.symm (3 : Fin (2 + 2)) = Sum.inr 1 :=
      finSumFinEquiv.symm_apply_eq.mpr rfl
    rw [hbProd_apply 3, hs]
    exact congrArg eProd.symm
      (Prod.ext (Module.Basis.prod_apply_inr_fst bW bZ 1)
        (Module.Basis.prod_apply_inr_snd bW bZ 1))
  funext i
  fin_cases i
  · exact hb0
  · exact hb1
  · exact hb2
  · exact hb3

/-- Pullback of `S4VolumeForm` along `s4PlaneEmbed : s4PlaneDisk × Sphere2 → Sphere4`. -/
noncomputable def adkSourceForm :
    TauCeti.SmoothForm ((𝓡 2).prod (𝓡 2)) (s4PlaneDisk × Sphere2) ℝ 4 :=
  TauCeti.SmoothForm.mpullback s4PlaneEmbed contMDiff_s4PlaneEmbed S4VolumeForm

/-- Pullback of `S2VolumeForm` along `s4ADKFibration ∘ s4PlaneEmbed`. -/
noncomputable def adkTargetBaseForm :
    TauCeti.SmoothForm ((𝓡 2).prod (𝓡 2)) (s4PlaneDisk × Sphere2) ℝ 2 :=
  TauCeti.SmoothForm.mpullback (s4ADKFibration ∘ s4PlaneEmbed)
    (contMDiff_s4ADKFibration.comp contMDiff_s4PlaneEmbed) S2VolumeForm

/-- Wedge product `p_F^* S2VolumeForm ∧ (s4ADKFibration ∘ s4PlaneEmbed)^* S2VolumeForm`. -/
noncomputable def adkTargetPullForm :
    TauCeti.SmoothForm ((𝓡 2).prod (𝓡 2)) (s4PlaneDisk × Sphere2) ℝ 4 :=
  TauCeti.SmoothForm.wedge s4PlaneFiberForm adkTargetBaseForm

private noncomputable def adkGSlice (z : Sphere2) (w : s4PlaneDisk) : EuclideanPlane :=
  g_adk (w, z)

private theorem contMDiff_adkGSlice (z : Sphere2) :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (adkGSlice z) :=
  contMDiff_g_adk.comp (contMDiff_id.prodMk contMDiff_const)

private noncomputable def adkBaseSliceForm (z : Sphere2) :
    TauCeti.SmoothForm (𝓡 2) s4PlaneDisk ℝ 2 :=
  TauCeti.SmoothForm.mpullback (adkGSlice z) (contMDiff_adkGSlice z) planeAreaForm

private noncomputable def adkTargetPullBaseForm (z : Sphere2) :
    TauCeti.SmoothForm ((𝓡 2).prod (𝓡 2)) (s4PlaneDisk × Sphere2) ℝ 2 :=
  TauCeti.SmoothForm.mpullback Prod.fst contMDiff_fst (adkBaseSliceForm z)

private theorem adkSourceForm_basis_eval (w : s4PlaneDisk) (z : Sphere2) :
    let bZ : Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z) :=
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    adkSourceForm.1 (w, z) ⇑(adkProdBasis w z) =
      Real.sqrt (1 - (w.1 0 ^ 2 + w.1 1 ^ 2)) * S2VolumeForm.1 z ![bZ 0, bZ 1] := by
  intro bZ
  let bW : Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) w) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  have hpull := mpullback_s4PlaneEmbed_s4VolumeForm (w, z)
  change (TauCeti.SmoothForm.mpullback s4PlaneEmbed contMDiff_s4PlaneEmbed S4VolumeForm).1
      (w, z) ⇑(adkProdBasis w z) = _
  rw [hpull, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  congr 1
  rw [s4PlaneFiberForm, s4PlaneAreaBaseForm,
    TauCeti.SmoothForm.wedge_comm_of_even (by decide : Even 2),
    ← TauCeti.SmoothForm.mpullback_mpullback Prod.fst Subtype.val contMDiff_fst
      contMDiff_subtype_val planeAreaForm,
    adkProdBasis_eq w z]
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

private theorem adkSourceForm_ne_zero (wz : s4PlaneDisk × Sphere2) : adkSourceForm.1 wz ≠ 0 := by
  rcases wz with ⟨w, z⟩
  let bZ : Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  have hpos := one_sub_norm_sq_pos_of_mem_s4PlaneDisk w
  have hsqrt_ne : Real.sqrt (1 - (w.1 0 ^ 2 + w.1 1 ^ 2)) ≠ 0 :=
    (Real.sqrt_pos.mpr hpos).ne'
  have hs2_ne : S2VolumeForm.1 z ![bZ 0, bZ 1] ≠ 0 := by
    have harg : ![bZ 0, bZ 1] = ⇑bZ := by
      funext i; fin_cases i <;> rfl
    rw [harg]
    exact ((S2VolumeForm.1 z).map_basis_ne_zero_iff bZ).mpr (S2PositiveVolumeForm.Ω_ne_zero z)
  have heval_ne : adkSourceForm.1 (w, z) ⇑(adkProdBasis w z) ≠ 0 := by
    rw [adkSourceForm_basis_eval w z]
    exact mul_ne_zero hsqrt_ne hs2_ne
  exact ((adkSourceForm.1 (w, z)).map_basis_ne_zero_iff (adkProdBasis w z)).mp heval_ne

private theorem adkTargetBaseForm_zero_left_eq (z : Sphere2) :
    adkTargetBaseForm.1 (s4PlaneDiskZero, z) =
      (adkTargetPullBaseForm z).1 (s4PlaneDiskZero, z) := by
  have hcomp_fib : s4ADKFibration ∘ s4PlaneEmbed = southPoleStereoInv ∘ g_adk :=
    funext fun wz ↦ (southPoleStereoInv_g_adk wz).symm
  have h1 :
      adkTargetBaseForm =
        TauCeti.SmoothForm.mpullback g_adk contMDiff_g_adk
          (TauCeti.SmoothForm.mpullback southPoleStereoInv contMDiff_southPoleStereoInv
            S2VolumeForm) := by
    unfold adkTargetBaseForm
    rw [TauCeti.SmoothForm.mpullback_mpullback]
    exact Subtype.ext (funext fun wz ↦ by
      rw [TauCeti.SmoothForm.coe_mpullback, TauCeti.SmoothForm.coe_mpullback, hcomp_fib])
  ext v
  rw [h1, TauCeti.SmoothForm.mpullback_apply, mpullback_southPoleStereoInv_s2VolumeForm,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul, planeAreaForm_apply, g_adk_zero_left z]
  have h16 : (16 / ((0 : EuclideanPlane) 0 ^ 2 + (0 : EuclideanPlane) 1 ^ 2 + 4) ^ 2 : ℝ) =
      1 := by
    norm_num
  rw [h16, one_mul]
  rw [adkTargetPullBaseForm, TauCeti.SmoothForm.mpullback_apply, adkBaseSliceForm,
    TauCeti.SmoothForm.mpullback_apply, planeAreaForm_apply, mfderiv_fst]
  congr 1
  funext i
  exact (mfderiv_g_adk_zero_left z (v i)).trans (mfderiv_g_adk_zero_left_slice z (v i).1).symm

private theorem adkTargetPullForm_eq_smul_zero_left (z : Sphere2) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      adkTargetPullForm.1 (s4PlaneDiskZero, z) = c₀ • adkSourceForm.1 (s4PlaneDiskZero, z) := by
  let c₀ : ℝ := 16 * (adkCoeffA z ^ 2 + adkCoeffB z ^ 2)
  have hc₀_pos : 0 < c₀ := mul_pos (by norm_num) (adkCoeff_sq_sum_pos z)
  refine ⟨c₀, hc₀_pos, ?_⟩
  let bW : Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) s4PlaneDiskZero) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  let bZ : Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  have hbase_eq := adkTargetBaseForm_zero_left_eq z
  have hwedge_eq :
      adkTargetPullForm.1 (s4PlaneDiskZero, z) =
        (TauCeti.SmoothForm.wedge (adkTargetPullBaseForm z) s4PlaneFiberForm).1
          (s4PlaneDiskZero, z) := by
    unfold adkTargetPullForm
    rw [TauCeti.SmoothForm.wedge_comm_of_even (by decide : Even 2)]
    ext v
    rw [TauCeti.SmoothForm.wedge_apply, TauCeti.SmoothForm.wedge_apply, hbase_eq]
  have hslice_eval :
      (adkBaseSliceForm z).1 s4PlaneDiskZero ![bW 0, bW 1] = c₀ := by
    rw [adkBaseSliceForm, TauCeti.SmoothForm.mpullback_apply, planeAreaForm_apply]
    have hvec0 :
        mfderiv (𝓡 2) (𝓡 2) (adkGSlice z) s4PlaneDiskZero (bW 0) =
          vec2 (4 * adkCoeffA z) (4 * adkCoeffB z) := by
      change mfderiv (𝓡 2) (𝓡 2) (fun w : s4PlaneDisk ↦ g_adk (w, z)) s4PlaneDiskZero (bW 0) = _
      rw [mfderiv_g_adk_zero_left_slice z (bW 0)]
      have hb0 : ((bW 0 : TangentSpace (𝓡 2) s4PlaneDiskZero) : EuclideanPlane) = vec2 1 0 :=
        basisFun2_zero_eq_vec2
      rw [hb0]
      refine ext_vec2 ?_ ?_ <;> simp
    have hvec1 :
        mfderiv (𝓡 2) (𝓡 2) (adkGSlice z) s4PlaneDiskZero (bW 1) =
          vec2 (-4 * adkCoeffB z) (4 * adkCoeffA z) := by
      change mfderiv (𝓡 2) (𝓡 2) (fun w : s4PlaneDisk ↦ g_adk (w, z)) s4PlaneDiskZero (bW 1) = _
      rw [mfderiv_g_adk_zero_left_slice z (bW 1)]
      have hb1 : ((bW 1 : TangentSpace (𝓡 2) s4PlaneDiskZero) : EuclideanPlane) = vec2 0 1 :=
        basisFun2_one_eq_vec2
      rw [hb1]
      refine ext_vec2 ?_ ?_ <;> simp
    let f : Fin 2 → EuclideanPlane :=
      fun i ↦ mfderiv (𝓡 2) (𝓡 2) (adkGSlice z) s4PlaneDiskZero (![bW 0, bW 1] i)
    change (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation.volumeForm f = c₀
    rw [volumeForm_basisFun_eq_det (n := 2), Matrix.det_fin_two]
    have hf00 : f 0 0 = 4 * adkCoeffA z := congrArg (fun v : EuclideanPlane ↦ v 0) hvec0
    have hf01 : f 0 1 = 4 * adkCoeffB z := congrArg (fun v : EuclideanPlane ↦ v 1) hvec0
    have hf10 : f 1 0 = -4 * adkCoeffB z := congrArg (fun v : EuclideanPlane ↦ v 0) hvec1
    have hf11 : f 1 1 = 4 * adkCoeffA z := congrArg (fun v : EuclideanPlane ↦ v 1) hvec1
    simp only [Matrix.of_apply, hf00, hf01, hf10, hf11, c₀]
    ring
  have htgt_eval :
      adkTargetPullForm.1 (s4PlaneDiskZero, z) ⇑(adkProdBasis s4PlaneDiskZero z) =
        c₀ * S2VolumeForm.1 z ![bZ 0, bZ 1] := by
    rw [hwedge_eq, adkProdBasis_eq s4PlaneDiskZero z]
    have hblock := wedge_mpullback_fst_snd_two_two (adkBaseSliceForm z) S2VolumeForm
      (s4PlaneDiskZero, z) (bW 0) (bW 1) (bZ 0) (bZ 1)
    exact hblock.trans (congrArg (· * S2VolumeForm.1 z ![bZ 0, bZ 1]) hslice_eval)
  have hsrc_eval :
      adkSourceForm.1 (s4PlaneDiskZero, z) ⇑(adkProdBasis s4PlaneDiskZero z) =
        S2VolumeForm.1 z ![bZ 0, bZ 1] := by
    have h := adkSourceForm_basis_eval s4PlaneDiskZero z
    simpa only [coe_s4PlaneDiskZero, PiLp.zero_apply, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, add_zero, sub_zero, Real.sqrt_one, one_mul] using h
  ext v
  rw [ContinuousAlternatingMap.apply_eq_det_mul _ (adkProdBasis s4PlaneDiskZero z) v,
    ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.apply_eq_det_mul _ (adkProdBasis s4PlaneDiskZero z) v,
    htgt_eval, hsrc_eval, smul_eq_mul, mul_left_comm]

private theorem eventually_exists_pos_smul_of_eq_smul_finrank
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] {k : ℕ}
    (hk : Module.finrank ℝ E = k)
    {α β : TauCeti.SmoothForm I M ℝ k}
    (hβ : ∀ x : M, β.1 x ≠ 0) {x₀ : M} {c₀ : ℝ}
    (hc₀ : 0 < c₀) (heq : α.1 x₀ = c₀ • β.1 x₀) :
    ∀ᶠ x in 𝓝 x₀, ∃ c : ℝ, 0 < c ∧ α.1 x = c • β.1 x := by
  let e := trivializationAt E (TangentSpace I) x₀
  let bE : Module.Basis (Fin k) ℝ E := Module.finBasisOfFinrankEq ℝ E hk
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  let num : M → ℝ := fun y ↦ α.1 y (e.symmL ℝ y ∘ bE)
  let den : M → ℝ := fun y ↦ β.1 y (e.symmL ℝ y ∘ bE)
  have hnum_cont : ContinuousAt num x₀ :=
    ((TauCeti.isSmoothForm_iff_forall_contMDiffAt_trivializationAt_apply.mp
      α.isSmoothForm) x₀ bE).continuousAt
  have hden_cont : ContinuousAt den x₀ :=
    ((TauCeti.isSmoothForm_iff_forall_contMDiffAt_trivializationAt_apply.mp
      β.isSmoothForm) x₀ bE).continuousAt
  have hb_eq (y : M) (hy : y ∈ e.baseSet) : ⇑(e.basisAt bE hy) = e.symmL ℝ y ∘ bE := by
    funext i
    rw [Function.comp_apply, Bundle.Trivialization.basisAt, Module.Basis.map_apply,
      Bundle.Trivialization.linearEquivAt_symm_apply]
    exact (e.symmL_apply hy _).symm
  have hden₀ : den x₀ ≠ 0 := by
    change β.1 x₀ (e.symmL ℝ x₀ ∘ bE) ≠ 0
    rw [← hb_eq x₀ hx₀]
    exact ((β.1 x₀).map_basis_ne_zero_iff (e.basisAt bE hx₀)).mpr (hβ x₀)
  have hval₀ : num x₀ / den x₀ = c₀ := by
    have hnum₀ : num x₀ = c₀ * den x₀ := by
      change α.1 x₀ (e.symmL ℝ x₀ ∘ bE) = c₀ * β.1 x₀ (e.symmL ℝ x₀ ∘ bE)
      rw [heq, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    rw [hnum₀, mul_div_cancel_right₀ _ hden₀]
  have hdiv_cont : ContinuousAt (fun y ↦ num y / den y) x₀ := hnum_cont.div hden_cont hden₀
  have hpos_q : ∀ᶠ y in 𝓝 x₀, 0 < num y / den y :=
    hdiv_cont.eventually (lt_mem_nhds (by dsimp only; rwa [hval₀]))
  filter_upwards [hpos_q, e.open_baseSet.mem_nhds hx₀] with y hqy hy
  have hden_y : den y ≠ 0 := by
    intro h0
    simp [h0] at hqy
  refine ⟨num y / den y, hqy, ?_⟩
  ext v
  rw [ContinuousAlternatingMap.apply_eq_det_mul _ (e.basisAt bE hy) v,
    ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.apply_eq_det_mul _ (e.basisAt bE hy) v,
    hb_eq y hy, smul_eq_mul]
  change (e.basisAt bE hy).det v * num y = (num y / den y) * ((e.basisAt bE hy).det v * den y)
  field_simp [hden_y]

private theorem eventually_adkTargetPullForm_pos_smul (z : Sphere2) :
    ∀ᶠ wz in 𝓝 (s4PlaneDiskZero, z),
      ∃ c : ℝ, 0 < c ∧ adkTargetPullForm.1 wz = c • adkSourceForm.1 wz := by
  obtain ⟨c₀, hc₀_pos, hc₀_eq⟩ := adkTargetPullForm_eq_smul_zero_left z
  have hfin : Module.finrank ℝ (EuclideanPlane × EuclideanPlane) = 4 := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin]
  exact eventually_exists_pos_smul_of_eq_smul_finrank hfin adkSourceForm_ne_zero
    hc₀_pos hc₀_eq

/-- Open neighborhood & base-radius data for the regular ADK trivialization. -/
structure ADKTrivData where
  /-- Open neighborhood of `{0} × Sphere2` in `s4PlaneDisk × Sphere2`. -/
  U : Set (s4PlaneDisk × Sphere2)
  /-- Openness of `U`. -/
  hU_open : IsOpen U
  /-- Inclusion of `{0} × Sphere2` into `U`. -/
  hK_sub : ({s4PlaneDiskZero} : Set s4PlaneDisk) ×ˢ (Set.univ : Set Sphere2) ⊆ U
  /-- Injectivity of `Ψ_adk` on `U`. -/
  hU_inj : Set.InjOn Ψ_adk U
  /-- Local diffeomorphism property of `Ψ_adk` on `U`. -/
  hU_loc : IsLocalDiffeomorphOn ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) ∞ Ψ_adk U
  /-- Pointwise positive co-orientation ratio on `U`. -/
  hU_pos : ∀ wz ∈ U, ∃ c : ℝ, 0 < c ∧ adkTargetPullForm.1 wz = c • adkSourceForm.1 wz
  /-- Shrunk positive stereographic base radius `r > 0`. -/
  r : ℝ
  /-- Positivity `0 < r`. -/
  hr_pos : 0 < r
  /-- Image containment `ball 0 r × Sphere2 ⊆ Ψ_adk '' U`. -/
  hr_sub_target : Metric.ball (0 : EuclideanPlane) r ×ˢ (Set.univ : Set Sphere2) ⊆ Ψ_adk '' U
  /-- Preimage containment over `southPoleStereoInv '' ball 0 r`. -/
  hr_preimage_sub :
    ∀ x : Sphere4,
      s4ADKFibration x ∈ southPoleStereoInv '' Metric.ball (0 : EuclideanPlane) r →
        x ∈ s4PlaneEmbed '' U

/-- Existence of an open trivialization neighborhood and shrunk regular base radius for
`s4ADKFibration`. -/
-- tier: T2
theorem exists_adkTrivData : Nonempty ADKTrivData := by
  let K : Set (s4PlaneDisk × Sphere2) :=
    ({s4PlaneDiskZero} : Set s4PlaneDisk) ×ˢ (Set.univ : Set Sphere2)
  have hK_compact : IsCompact K := isCompact_singleton.prod isCompact_univ
  have hK_loc :
      ∀ wz ∈ K, IsLocalDiffeomorphAt ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) ∞ Ψ_adk wz := by
    rintro ⟨w, z⟩ ⟨hw, -⟩
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact isLocalDiffeomorphAt_Ψ_adk_zero_left z
  obtain ⟨U₀, hU₀_open, hK_U₀, hU₀_inj, hU₀_loc⟩ :=
    injOn_Ψ_adk_zeroSlice.exists_isOpen_superset_isLocalDiffeomorphOn hK_compact hK_loc
  let S_pos : Set (s4PlaneDisk × Sphere2) :=
    {wz | ∃ c : ℝ, 0 < c ∧ adkTargetPullForm.1 wz = c • adkSourceForm.1 wz}
  have hK_S_pos : S_pos ∈ 𝓝ˢ K := by
    change ∀ᶠ wz in 𝓝ˢ K, wz ∈ S_pos
    rw [eventually_nhdsSet_iff_forall]
    rintro ⟨w, z⟩ ⟨hw, -⟩
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact eventually_adkTargetPullForm_pos_smul z
  obtain ⟨U_pos, hU_pos_open, hK_U_pos, hU_pos_sub⟩ := mem_nhdsSet_iff_exists.mp hK_S_pos
  let U := U₀ ∩ U_pos
  have hU_open : IsOpen U := hU₀_open.inter hU_pos_open
  have hK_U : K ⊆ U := Set.subset_inter hK_U₀ hK_U_pos
  have hU_inj : Set.InjOn Ψ_adk U := hU₀_inj.mono Set.inter_subset_left
  have hU_loc : IsLocalDiffeomorphOn ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) ∞ Ψ_adk U :=
    fun wz ↦ hU₀_loc ⟨wz.1, wz.2.1⟩
  have hU_img_open : IsOpen (Ψ_adk '' U) :=
    (hU_loc.isLocalHomeomorphOn).isOpen_image hU_open
  have h0_sub_img :
      ({0} : Set EuclideanPlane) ×ˢ (Set.univ : Set Sphere2) ⊆ Ψ_adk '' U := by
    rintro ⟨w, z⟩ ⟨hw, -⟩
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact ⟨(s4PlaneDiskZero, z), hK_U ⟨rfl, trivial⟩, Prod.ext (g_adk_zero_left z) rfl⟩
  obtain ⟨V, W, hV_open, _, h0_V, huniv_W, hVW_sub⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ hU_img_open h0_sub_img
  have h0_mem_V : (0 : EuclideanPlane) ∈ V := h0_V rfl
  obtain ⟨r₁, hr₁_pos, hr₁_ball⟩ := Metric.isOpen_iff.mp hV_open 0 h0_mem_V
  have hr₁_sub :
      Metric.ball (0 : EuclideanPlane) r₁ ×ˢ (Set.univ : Set Sphere2) ⊆ Ψ_adk '' U := by
    rintro ⟨w, z⟩ ⟨hw, -⟩
    exact hVW_sub ⟨hr₁_ball hw, huniv_W trivial⟩
  have hU_s4_open : IsOpen (s4PlaneEmbed '' U) := by
    have heq : s4PlaneEmbed '' U =
        (Subtype.val : s4PreimageOpen → Sphere4) '' (s4PlaneTrivialization.symm '' U) := by
      ext x
      simp only [Set.mem_image]
      constructor
      · rintro ⟨wz, hwz, rfl⟩
        exact ⟨s4PlaneTrivialization.symm wz, ⟨wz, hwz, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨wz, hwz, rfl⟩, rfl⟩
        exact ⟨wz, hwz, rfl⟩
    rw [heq]
    exact s4PreimageOpen.2.isOpenEmbedding_subtypeVal.isOpenMap _
      (s4PlaneTrivialization.symm.toHomeomorph.isOpenMap _ hU_open)
  let C : Set Sphere4 := (s4PlaneEmbed '' U)ᶜ
  have hC_compact : IsCompact C := hU_s4_open.isClosed_compl.isCompact
  have hfC_closed : IsClosed (s4ADKFibration '' C) :=
    (hC_compact.image contMDiff_s4ADKFibration.continuous).isClosed
  have hnp_mem : s2NorthPole ∈ (s4ADKFibration '' C)ᶜ := by
    rintro ⟨x, hxC, hfx⟩
    rw [s4ADKFibration_eq_northPole_iff] at hfx
    let z : Sphere2 := ⟨vec3 (x.1 2) (x.1 3) (x.1 4), mem_sphere_zero_iff_norm.mpr (by
      have hxsq := mem_sphere_zero_iff_norm.mp x.2
      have hx1 : ‖x.1‖ ^ 2 = 1 := by rw [hxsq]; norm_num
      rw [norm_sq_vec5, hfx.1, hfx.2] at hx1
      have hsq : ‖vec3 (x.1 2) (x.1 3) (x.1 4)‖ ^ 2 = 1 := by
        rw [norm_sq_vec3]; simp only [vec3_zero, vec3_one, vec3_two]; linarith
      nlinarith [norm_nonneg (vec3 (x.1 2) (x.1 3) (x.1 4))])⟩
    have hx_eq : s4PlaneEmbed (s4PlaneDiskZero, z) = x := by
      apply Subtype.ext
      refine ext_vec5 hfx.1.symm hfx.2.symm ?_ ?_ ?_ <;>
        simp [s4PlaneEmbed, s4PlaneEmbedRaw, z]
    exact hxC ⟨(s4PlaneDiskZero, z), hK_U ⟨rfl, trivial⟩, hx_eq⟩
  have hpre_open : IsOpen (southPoleStereoInv ⁻¹' (s4ADKFibration '' C)ᶜ) :=
    hfC_closed.isOpen_compl.preimage contMDiff_southPoleStereoInv.continuous
  have h0_mem_pre :
      (0 : EuclideanPlane) ∈ southPoleStereoInv ⁻¹' (s4ADKFibration '' C)ᶜ := by
    simpa [southPoleStereoInv_zero] using hnp_mem
  obtain ⟨r₂, hr₂_pos, hr₂_ball⟩ := Metric.isOpen_iff.mp hpre_open 0 h0_mem_pre
  let r := min r₁ r₂
  have hr_pos : 0 < r := lt_min hr₁_pos hr₂_pos
  refine ⟨⟨U, hU_open, hK_U, hU_inj, hU_loc, fun wz hwz ↦ hU_pos_sub hwz.2,
    r, hr_pos, fun p hp ↦ hr₁_sub ⟨Metric.ball_subset_ball (min_le_left _ _) hp.1, hp.2⟩,
    ?_⟩⟩
  rintro x ⟨w, hw, hfx⟩
  by_contra hnot
  have hw2 : w ∈ Metric.ball (0 : EuclideanPlane) r₂ :=
    Metric.ball_subset_ball (min_le_right _ _) hw
  exact hr₂_ball hw2 ⟨x, hnot, hfx.symm⟩

/-- Chosen `ADKTrivData` witness. -/
noncomputable def adkTrivData : ADKTrivData :=
  Classical.choice exists_adkTrivData

/-- Positive Euclidean disk radius of `s4ADKBaseRegion ⊂ Sphere2`. -/
noncomputable def s4ADKBaseDiskRadius : ℝ :=
  adkTrivData.r

/-- Positivity `0 < s4ADKBaseDiskRadius`. -/
theorem s4ADKBaseDiskRadius_pos : 0 < s4ADKBaseDiskRadius :=
  adkTrivData.hr_pos

/-- Planar open coordinate disk `Metric.ball 0 s4ADKBaseDiskRadius` for `s4ADKBaseRegion`. -/
noncomputable abbrev s4ADKBaseDiskOpen : Opens EuclideanPlane :=
  ⟨Metric.ball (0 : EuclideanPlane) s4ADKBaseDiskRadius, Metric.isOpen_ball⟩

/-- Nonempty open regular base disk `s4ADKBaseRegion ⊂ Sphere2` for `s4ADKFibration`, containing
`s2NorthPole`. -/
noncomputable def s4ADKBaseRegion : Opens Sphere2 :=
  ⟨southPoleStereoInv '' Metric.ball (0 : EuclideanPlane) s4ADKBaseDiskRadius,
    isOpenEmbedding_southPoleStereoInv.isOpenMap _ Metric.isOpen_ball⟩

/-- `s2NorthPole` lies in `s4ADKBaseRegion`. -/
theorem s2NorthPole_mem_s4ADKBaseRegion : s2NorthPole ∈ s4ADKBaseRegion.1 :=
  ⟨0, Metric.mem_ball_self s4ADKBaseDiskRadius_pos, southPoleStereoInv_zero⟩

/-- `s4ADKBaseRegion` is nonempty. -/
theorem s4ADKBaseRegion_nonempty : s4ADKBaseRegion.1.Nonempty :=
  ⟨s2NorthPole, s2NorthPole_mem_s4ADKBaseRegion⟩

/-- Smooth diffeomorphism `Metric.ball 0 s4ADKBaseDiskRadius ≃ₘ s4ADKBaseRegion`. -/
-- tier: T2
noncomputable def s4ADKBaseDiskDiffeomorph :
    s4ADKBaseDiskOpen ≃ₘ⟮𝓡 2, 𝓡 2⟯ s4ADKBaseRegion where
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
    (TauCeti.ContMDiff.subtypeVal_comp_iff s4ADKBaseRegion _).mp
      (contMDiff_southPoleStereoInv.comp contMDiff_subtype_val)
  contMDiff_invFun := by
    have hsub : s4ADKBaseRegion.1 ⊆ s2PuncturedSouth.1 := by
      rintro _ ⟨w, -, rfl⟩
      exact southPoleStereoInv_ne_southPole w
    have hincl : ContMDiff (𝓡 2) (𝓡 2) ∞
        (fun b : s4ADKBaseRegion ↦ (⟨b.1, hsub b.2⟩ : s2PuncturedSouth)) :=
      (TauCeti.ContMDiff.subtypeVal_comp_iff s2PuncturedSouth _).mp contMDiff_subtype_val
    exact (TauCeti.ContMDiff.subtypeVal_comp_iff s4ADKBaseDiskOpen _).mp
      (southPoleStereoDiffeomorph.symm.contMDiff.comp hincl)

/-- Stereographic coordinate formula for `s4ADKBaseDiskDiffeomorph.symm`. -/
@[simp]
theorem coe_s4ADKBaseDiskDiffeomorph_symm (b : s4ADKBaseRegion) :
    ((s4ADKBaseDiskDiffeomorph.symm b : s4ADKBaseDiskOpen) : EuclideanPlane) =
      southPoleStereoChart b.1 :=
  rfl

/-- Open preimage `s4ADKFibration ⁻¹' s4ADKBaseRegion` in `Sphere4`. -/
noncomputable abbrev s4ADKPreimageOpen : Opens Sphere4 :=
  ⟨s4ADKFibration ⁻¹' s4ADKBaseRegion.1,
    s4ADKBaseRegion.2.preimage contMDiff_s4ADKFibration.continuous⟩

/-- Containment `s4ADKPreimageOpen ⊆ s4PreimageOpen`. -/
theorem s4ADKPreimageOpen_mem_s4PreimageOpen {x : Sphere4}
    (hx : x ∈ s4ADKPreimageOpen.1) : x ∈ s4PreimageOpen.1 := by
  obtain ⟨wz, -, rfl⟩ := adkTrivData.hr_preimage_sub x hx
  exact s4PlaneEmbed_mem_preimage wz

/-- Canonical inclusion of `s4ADKPreimageOpen` into `s4PlaneDisk × Sphere2`. -/
noncomputable def s4ADKIncl (u : s4ADKPreimageOpen) : s4PlaneDisk × Sphere2 :=
  s4PlaneTrivialization ⟨u.1, s4ADKPreimageOpen_mem_s4PreimageOpen u.2⟩

/-- Left-inverse property `s4PlaneEmbed (s4ADKIncl u) = u.1`. -/
theorem s4PlaneEmbed_s4ADKIncl (u : s4ADKPreimageOpen) :
    s4PlaneEmbed (s4ADKIncl u) = u.1 := by
  change (s4PlaneTrivialization.symm (s4PlaneTrivialization
    ⟨u.1, s4ADKPreimageOpen_mem_s4PreimageOpen u.2⟩)).1 = u.1
  rw [s4PlaneTrivialization.symm_apply_apply]

/-- Range containment `s4ADKIncl u ∈ adkTrivData.U`. -/
theorem s4ADKIncl_mem_U (u : s4ADKPreimageOpen) : s4ADKIncl u ∈ adkTrivData.U := by
  obtain ⟨wz, hwz, hEq⟩ := adkTrivData.hr_preimage_sub u.1 u.2
  have hwz_triv : s4ADKIncl u = wz := by
    have h1 : (⟨u.1, s4ADKPreimageOpen_mem_s4PreimageOpen u.2⟩ : s4PreimageOpen) =
        s4PlaneTrivialization.symm wz :=
      Subtype.ext hEq.symm
    change s4PlaneTrivialization ⟨u.1, s4ADKPreimageOpen_mem_s4PreimageOpen u.2⟩ = wz
    rw [h1, s4PlaneTrivialization.apply_symm_apply]
  rwa [hwz_triv]

/-- Smoothness of `s4ADKIncl`. -/
-- tier: T2
theorem contMDiff_s4ADKIncl :
    ContMDiff (𝓡 4) ((𝓡 2).prod (𝓡 2)) ∞ s4ADKIncl := by
  have hmap :
      ContMDiff (𝓡 4) (𝓡 4) ∞
        (fun u : s4ADKPreimageOpen ↦
          (⟨u.1, s4ADKPreimageOpen_mem_s4PreimageOpen u.2⟩ : s4PreimageOpen)) :=
    (TauCeti.ContMDiff.subtypeVal_comp_iff s4PreimageOpen _).mp contMDiff_subtype_val
  exact s4PlaneTrivialization.contMDiff.comp hmap

/-- Local diffeomorphism property of `s4ADKIncl`. -/
-- tier: T2
theorem isLocalDiffeomorph_s4ADKIncl :
    IsLocalDiffeomorph (𝓡 4) ((𝓡 2).prod (𝓡 2)) ∞ s4ADKIncl := by
  intro u
  let subMap : s4ADKPreimageOpen → s4PreimageOpen :=
    fun v ↦ ⟨v.1, s4ADKPreimageOpen_mem_s4PreimageOpen v.2⟩
  have hsub_loc : IsLocalDiffeomorphAt (𝓡 4) (𝓡 4) ∞ subMap u := by
    have hcomp : ((Subtype.val : s4PreimageOpen → Sphere4) ∘ subMap) =
        (Subtype.val : s4ADKPreimageOpen → Sphere4) := rfl
    have hval1 : IsLocalDiffeomorphAt (𝓡 4) (𝓡 4) ∞
        (Subtype.val : s4ADKPreimageOpen → Sphere4) u :=
      TauCeti.isLocalDiffeomorph_subtype_val u
    have hval2 : IsLocalDiffeomorphAt (𝓡 4) (𝓡 4) ∞
        (Subtype.val : s4PreimageOpen → Sphere4) (subMap u) :=
      TauCeti.isLocalDiffeomorph_subtype_val (subMap u)
    have hsub_cont : ContinuousAt subMap u :=
      (continuous_subtype_val.subtype_mk _).continuousAt
    rw [← hcomp] at hval1
    exact hval1.of_comp_left hval2 hsub_cont
  exact hsub_loc.comp (hg := s4PlaneTrivialization.isLocalDiffeomorph (subMap u))

/-- Forward trivialization map `s4ADKPreimageOpen → s4ADKBaseRegion × Sphere2`. -/
noncomputable def s4ADKTrivFun (u : s4ADKPreimageOpen) :
    s4ADKBaseRegion × Sphere2 :=
  (⟨s4ADKFibration u.1, u.2⟩, (s4ADKIncl u).2)

/-- Smoothness of `s4ADKTrivFun`. -/
-- tier: T2
theorem contMDiff_s4ADKTrivFun :
    ContMDiff (𝓡 4) ((𝓡 2).prod (𝓡 2)) ∞ s4ADKTrivFun := by
  have h1 : ContMDiff (𝓡 4) (𝓡 2) ∞
      (fun u : s4ADKPreimageOpen ↦ (⟨s4ADKFibration u.1, u.2⟩ : s4ADKBaseRegion)) :=
    (TauCeti.ContMDiff.subtypeVal_comp_iff s4ADKBaseRegion _).mp
      (contMDiff_s4ADKFibration.comp contMDiff_subtype_val)
  have h2 : ContMDiff (𝓡 4) (𝓡 2) ∞ (fun u : s4ADKPreimageOpen ↦ (s4ADKIncl u).2) :=
    contMDiff_snd.comp contMDiff_s4ADKIncl
  exact h1.prodMk h2

/-- Bijectivity of `s4ADKTrivFun`. -/
theorem bijective_s4ADKTrivFun : Function.Bijective s4ADKTrivFun := by
  constructor
  · intro u₁ u₂ hEq
    have hf : s4ADKFibration u₁.1 = s4ADKFibration u₂.1 :=
      congrArg (fun p : s4ADKBaseRegion × Sphere2 ↦ p.1.1) hEq
    have hz : (s4ADKIncl u₁).2 = (s4ADKIncl u₂).2 :=
      congrArg (Prod.snd : s4ADKBaseRegion × Sphere2 → Sphere2) hEq
    have hg : g_adk (s4ADKIncl u₁) = g_adk (s4ADKIncl u₂) := by
      apply injective_southPoleStereoInv
      rw [southPoleStereoInv_g_adk, southPoleStereoInv_g_adk,
        s4PlaneEmbed_s4ADKIncl, s4PlaneEmbed_s4ADKIncl, hf]
    have hΨ : Ψ_adk (s4ADKIncl u₁) = Ψ_adk (s4ADKIncl u₂) := Prod.ext hg hz
    have hincl : s4ADKIncl u₁ = s4ADKIncl u₂ :=
      adkTrivData.hU_inj (s4ADKIncl_mem_U u₁) (s4ADKIncl_mem_U u₂) hΨ
    have hsub : u₁.1 = u₂.1 := by
      calc
        u₁.1 = s4PlaneEmbed (s4ADKIncl u₁) := (s4PlaneEmbed_s4ADKIncl u₁).symm
        _ = s4PlaneEmbed (s4ADKIncl u₂) := congrArg s4PlaneEmbed hincl
        _ = u₂.1 := s4PlaneEmbed_s4ADKIncl u₂
    exact Subtype.ext hsub
  · rintro ⟨⟨b, hb⟩, z⟩
    obtain ⟨w₀, hw₀, rfl⟩ := hb
    have hw₀' : w₀ ∈ Metric.ball (0 : EuclideanPlane) adkTrivData.r := hw₀
    obtain ⟨wz, hwzU, hΨ⟩ :=
      adkTrivData.hr_sub_target (Set.mk_mem_prod hw₀' (Set.mem_univ z))
    have hg : g_adk wz = w₀ := congrArg Prod.fst hΨ
    have hz : wz.2 = z := congrArg Prod.snd hΨ
    let x := s4PlaneEmbed wz
    have hx_pre : x ∈ s4ADKPreimageOpen.1 := by
      change s4ADKFibration (s4PlaneEmbed wz) ∈ s4ADKBaseRegion.1
      rw [← southPoleStereoInv_g_adk wz, hg]
      exact ⟨w₀, hw₀, rfl⟩
    let u : s4ADKPreimageOpen := ⟨x, hx_pre⟩
    have hu_incl : s4ADKIncl u = wz := by
      have h1 : (⟨u.1, s4ADKPreimageOpen_mem_s4PreimageOpen u.2⟩ : s4PreimageOpen) =
          s4PlaneTrivialization.symm wz := rfl
      change s4PlaneTrivialization ⟨u.1, s4ADKPreimageOpen_mem_s4PreimageOpen u.2⟩ = wz
      rw [h1, s4PlaneTrivialization.apply_symm_apply]
    refine ⟨u, Prod.ext (Subtype.ext ?_) ?_⟩
    · change s4ADKFibration (s4PlaneEmbed wz) = southPoleStereoInv w₀
      rw [← southPoleStereoInv_g_adk wz, hg]
    · dsimp only [s4ADKTrivFun]
      rw [hu_incl, hz]

/-- Local diffeomorphism property of `s4ADKTrivFun`. -/
-- tier: T2
theorem isLocalDiffeomorph_s4ADKTrivFun :
    IsLocalDiffeomorph (𝓡 4) ((𝓡 2).prod (𝓡 2)) ∞ s4ADKTrivFun := by
  let Φ₀ : s4ADKBaseRegion × Sphere2 → EuclideanPlane × Sphere2 :=
    fun bz ↦ ((s4ADKBaseDiskDiffeomorph.symm bz.1).1, bz.2)
  have hΦ₀_comp : Φ₀ ∘ s4ADKTrivFun = Ψ_adk ∘ s4ADKIncl := by
    funext u
    dsimp only [Function.comp_apply, Φ₀, s4ADKTrivFun, Ψ_adk]
    refine Prod.ext ?_ rfl
    rw [coe_s4ADKBaseDiskDiffeomorph_symm]
    change southPoleStereoChart (s4ADKFibration u.1) = g_adk (s4ADKIncl u)
    rw [← s4PlaneEmbed_s4ADKIncl u]
    rfl
  have hΦ₀_loc :
      ∀ bz : s4ADKBaseRegion × Sphere2,
        IsLocalDiffeomorphAt ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) ∞ Φ₀ bz := by
    intro bz
    let d := s4ADKBaseDiskDiffeomorph.symm.prodCongr (Diffeomorph.refl (𝓡 2) Sphere2 ∞)
    let j : s4ADKBaseDiskOpen × Sphere2 → EuclideanPlane × Sphere2 :=
      fun q ↦ (q.1.1, q.2)
    have hΦ₀_eq : Φ₀ = j ∘ ⇑d := rfl
    have hj_loc :
        IsLocalDiffeomorphAt ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) ∞ j (d bz) :=
      (TauCeti.isLocalDiffeomorph_subtype_val (I := 𝓡 2) (n := ∞) (d bz).1).prodMap
        ((Diffeomorph.refl (𝓡 2) Sphere2 ∞).isLocalDiffeomorph (d bz).2)
    rw [hΦ₀_eq]
    exact (d.isLocalDiffeomorph bz).comp (hg := hj_loc)
  intro u
  have hΨu :
      IsLocalDiffeomorphAt ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) ∞ Ψ_adk (s4ADKIncl u) :=
    adkTrivData.hU_loc ⟨s4ADKIncl u, s4ADKIncl_mem_U u⟩
  have hcomp_loc : IsLocalDiffeomorphAt (𝓡 4) ((𝓡 2).prod (𝓡 2)) ∞
      (Φ₀ ∘ s4ADKTrivFun) u := by
    rw [hΦ₀_comp]
    exact (isLocalDiffeomorph_s4ADKIncl u).comp (hg := hΨu)
  exact hcomp_loc.of_comp_left (hΦ₀_loc (s4ADKTrivFun u))
    ((contMDiff_s4ADKTrivFun u).continuousAt)

/-- Explicit smooth trivialization
`s4ADKFibration ⁻¹' s4ADKBaseRegion ≃ₘ s4ADKBaseRegion × Sphere2`. -/
-- tier: T2
noncomputable def s4ADKTrivialization :
    s4ADKPreimageOpen ≃ₘ⟮𝓡 4, (𝓡 2).prod (𝓡 2)⟯ (s4ADKBaseRegion × Sphere2) :=
  isLocalDiffeomorph_s4ADKTrivFun.diffeomorphOfBijective bijective_s4ADKTrivFun

/-- First-factor projection law `(s4ADKTrivialization u).1 = ⟨s4ADKFibration u.1, u.2⟩`. -/
@[simp]
theorem s4ADKTrivialization_fst (u : s4ADKPreimageOpen) :
    (s4ADKTrivialization u).1 = ⟨s4ADKFibration u.1, u.2⟩ := by
  rw [s4ADKTrivialization, IsLocalDiffeomorph.coe_diffeomorphOfBijective]
  rfl

/-- Every point of `s4ADKFibration ⁻¹' s4ADKBaseRegion` is a regular point of `s4ADKFibration`.
-/
-- tier: T2
theorem regular_on_s4ADKBaseRegion :
    ∀ x ∈ s4ADKFibration ⁻¹' s4ADKBaseRegion.1,
      Function.Surjective (mfderiv (𝓡 4) (𝓡 2) s4ADKFibration x) := by
  intro x hx
  let p' : s4ADKPreimageOpen := ⟨x, hx⟩
  have hcomp_eq :
      s4ADKFibration ∘ (Subtype.val : s4ADKPreimageOpen → Sphere4) =
        (Subtype.val : s4ADKBaseRegion → Sphere2) ∘
          (Prod.fst ∘ ⇑s4ADKTrivialization) := by
    funext q
    exact (congrArg Subtype.val (s4ADKTrivialization_fst q)).symm
  have hf_at : MDifferentiableAt (𝓡 4) (𝓡 2) s4ADKFibration x :=
    (contMDiff_s4ADKFibration x).mdifferentiableAt (by simp)
  have hsub_in : MDifferentiableAt (𝓡 4) (𝓡 4)
      (Subtype.val : s4ADKPreimageOpen → Sphere4) p' :=
    (TauCeti.isLocalDiffeomorph_subtype_val (I := 𝓡 4) (n := ∞)
      p').contMDiffAt.mdifferentiableAt (by simp)
  have htriv_at : MDifferentiableAt (𝓡 4) ((𝓡 2).prod (𝓡 2))
      (⇑s4ADKTrivialization) p' :=
    (s4ADKTrivialization.contMDiff p').mdifferentiableAt (by simp)
  have hfst_at : MDifferentiableAt ((𝓡 2).prod (𝓡 2)) (𝓡 2)
      (Prod.fst : s4ADKBaseRegion × Sphere2 → s4ADKBaseRegion) (s4ADKTrivialization p') :=
    ((contMDiff_fst (n := ∞)) (s4ADKTrivialization p')).mdifferentiableAt (by simp)
  have hsub_out : MDifferentiableAt (𝓡 2) (𝓡 2)
      (Subtype.val : s4ADKBaseRegion → Sphere2) (s4ADKTrivialization p').1 :=
    (TauCeti.isLocalDiffeomorph_subtype_val (I := 𝓡 2) (n := ∞)
      (s4ADKTrivialization p').1).contMDiffAt.mdifferentiableAt (by simp)
  have hlhs_comp :
      mfderiv (𝓡 4) (𝓡 2)
          (s4ADKFibration ∘ (Subtype.val : s4ADKPreimageOpen → Sphere4)) p' =
        (mfderiv (𝓡 4) (𝓡 2) s4ADKFibration x).comp
          (mfderiv (𝓡 4) (𝓡 4) (Subtype.val : s4ADKPreimageOpen → Sphere4) p') :=
    mfderiv_comp p' hf_at hsub_in
  have hrhs_comp :
      mfderiv (𝓡 4) (𝓡 2)
          ((Subtype.val : s4ADKBaseRegion → Sphere2) ∘
            (Prod.fst ∘ ⇑s4ADKTrivialization)) p' =
        (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : s4ADKBaseRegion → Sphere2)
            (s4ADKTrivialization p').1).comp
          ((mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 2)
              (Prod.fst : s4ADKBaseRegion × Sphere2 → s4ADKBaseRegion)
              (s4ADKTrivialization p')).comp
            (mfderiv (𝓡 4) ((𝓡 2).prod (𝓡 2)) (⇑s4ADKTrivialization) p')) := by
    rw [mfderiv_comp p' hsub_out (hfst_at.comp p' htriv_at),
      mfderiv_comp p' hfst_at htriv_at]
    rfl
  have hsurj_triv : Function.Surjective
      (mfderiv (𝓡 4) ((𝓡 2).prod (𝓡 2)) (⇑s4ADKTrivialization) p') :=
    (s4ADKTrivialization.isLocalDiffeomorph p').isInvertible_mfderiv (by simp) |>.surjective
  have hsurj_fst : Function.Surjective
      (mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 2)
        (Prod.fst : s4ADKBaseRegion × Sphere2 → s4ADKBaseRegion)
        (s4ADKTrivialization p')) := by
    intro v
    rw [mfderiv_fst]
    exact ⟨(v, 0), rfl⟩
  have hsurj_sub_out : Function.Surjective
      (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : s4ADKBaseRegion → Sphere2)
        (s4ADKTrivialization p').1) :=
    (TauCeti.isLocalDiffeomorph_subtype_val (I := 𝓡 2) (n := ∞)
      (s4ADKTrivialization p').1).isInvertible_mfderiv (by simp) |>.surjective
  have hsurj_rhs : Function.Surjective
      (mfderiv (𝓡 4) (𝓡 2)
        ((Subtype.val : s4ADKBaseRegion → Sphere2) ∘
          (Prod.fst ∘ ⇑s4ADKTrivialization)) p') := by
    rw [hrhs_comp]
    exact hsurj_sub_out.comp (hsurj_fst.comp hsurj_triv)
  rw [← hcomp_eq, hlhs_comp] at hsurj_rhs
  exact Function.Surjective.of_comp hsurj_rhs

private theorem mpullback_congr_fun_adk
    {E₁ H₁ M₁ E₂ H₂ M₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [IsManifold I₁ 1 M₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    [IsManifold I₂ 1 M₂] {f g : M₁ → M₂}
    (hf : ContMDiff I₁ I₂ ∞ f) (hg : ContMDiff I₁ I₂ ∞ g) (hfg : f = g)
    {k : ℕ} (α : TauCeti.SmoothForm I₂ M₂ ℝ k) :
    TauCeti.SmoothForm.mpullback f hf α = TauCeti.SmoothForm.mpullback g hg α := by
  subst hfg
  rfl

private theorem mpullback_s4ADKIncl_adkSourceForm :
    TauCeti.SmoothForm.mpullback s4ADKIncl contMDiff_s4ADKIncl adkSourceForm =
      TauCeti.SmoothForm.mpullback (Subtype.val : s4ADKPreimageOpen → Sphere4)
        contMDiff_subtype_val S4VolumeForm := by
  unfold adkSourceForm
  rw [TauCeti.SmoothForm.mpullback_mpullback]
  exact mpullback_congr_fun_adk _ _ (funext s4PlaneEmbed_s4ADKIncl) S4VolumeForm

private theorem mpullback_s4ADKIncl_adkTargetPullForm :
    TauCeti.SmoothForm.mpullback s4ADKTrivialization s4ADKTrivialization.contMDiff
        (TauCeti.SmoothForm.wedge
          (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd S2VolumeForm)
          (TauCeti.SmoothForm.mpullback (Subtype.val ∘ Prod.fst)
            (contMDiff_subtype_val.comp contMDiff_fst) S2VolumeForm)) =
      TauCeti.SmoothForm.mpullback s4ADKIncl contMDiff_s4ADKIncl adkTargetPullForm := by
  have hfib_fun : Prod.snd ∘ ⇑s4ADKTrivialization = Prod.snd ∘ s4ADKIncl := by
    funext u
    change (s4ADKTrivialization u).2 = (s4ADKIncl u).2
    rw [s4ADKTrivialization, IsLocalDiffeomorph.coe_diffeomorphOfBijective]
    rfl
  have hbase_fun :
      (Subtype.val ∘ (Prod.fst : s4ADKBaseRegion × Sphere2 → _)) ∘ ⇑s4ADKTrivialization =
        (s4ADKFibration ∘ s4PlaneEmbed) ∘ s4ADKIncl := by
    funext u
    change (s4ADKTrivialization u).1.1 = s4ADKFibration (s4PlaneEmbed (s4ADKIncl u))
    rw [s4ADKTrivialization_fst, s4PlaneEmbed_s4ADKIncl]
  have hfib :
      TauCeti.SmoothForm.mpullback s4ADKTrivialization s4ADKTrivialization.contMDiff
          (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd S2VolumeForm) =
        TauCeti.SmoothForm.mpullback s4ADKIncl contMDiff_s4ADKIncl s4PlaneFiberForm := by
    rw [TauCeti.SmoothForm.mpullback_mpullback]
    unfold s4PlaneFiberForm
    rw [TauCeti.SmoothForm.mpullback_mpullback]
    exact mpullback_congr_fun_adk _ _ hfib_fun S2VolumeForm
  have hbase :
      TauCeti.SmoothForm.mpullback s4ADKTrivialization s4ADKTrivialization.contMDiff
          (TauCeti.SmoothForm.mpullback (Subtype.val ∘ Prod.fst)
            (contMDiff_subtype_val.comp contMDiff_fst) S2VolumeForm) =
        TauCeti.SmoothForm.mpullback s4ADKIncl contMDiff_s4ADKIncl adkTargetBaseForm := by
    rw [TauCeti.SmoothForm.mpullback_mpullback]
    unfold adkTargetBaseForm
    rw [TauCeti.SmoothForm.mpullback_mpullback]
    exact mpullback_congr_fun_adk _ _ hbase_fun S2VolumeForm
  have hw1 :=
    TauCeti.SmoothForm.mpullback_wedge (k := 2) (l := 2) s4ADKTrivialization
      s4ADKTrivialization.contMDiff
      (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd S2VolumeForm)
      (TauCeti.SmoothForm.mpullback (Subtype.val ∘ Prod.fst)
        (contMDiff_subtype_val.comp contMDiff_fst) S2VolumeForm)
  have hw2 :=
    TauCeti.SmoothForm.mpullback_wedge (k := 2) (l := 2) s4ADKIncl
      contMDiff_s4ADKIncl s4PlaneFiberForm adkTargetBaseForm
  have hwedge :
      TauCeti.SmoothForm.wedge
          (TauCeti.SmoothForm.mpullback s4ADKTrivialization s4ADKTrivialization.contMDiff
            (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd S2VolumeForm))
          (TauCeti.SmoothForm.mpullback s4ADKTrivialization s4ADKTrivialization.contMDiff
            (TauCeti.SmoothForm.mpullback (Subtype.val ∘ Prod.fst)
              (contMDiff_subtype_val.comp contMDiff_fst) S2VolumeForm)) =
        TauCeti.SmoothForm.wedge
          (TauCeti.SmoothForm.mpullback s4ADKIncl contMDiff_s4ADKIncl s4PlaneFiberForm)
          (TauCeti.SmoothForm.mpullback s4ADKIncl contMDiff_s4ADKIncl adkTargetBaseForm) :=
    congrArg₂ (fun (a b : TauCeti.SmoothForm (𝓡 4) s4ADKPreimageOpen ℝ 2) ↦
      TauCeti.SmoothForm.wedge a b) hfib hbase
  exact hw1.trans (hwedge.trans hw2.symm)

/-- **Strict Positive Co-Orientation of `s4ADKTrivialization`**:
At every point `u : s4ADKPreimageOpen` (`s4ADKFibration ⁻¹' s4ADKBaseRegion`), the pullback
along `s4ADKTrivialization` of `p_F^* S2VolumeForm ∧ p_B^* S2VolumeForm|_B` equals a strictly
positive scalar multiple `c • S4VolumeForm|_U` (`0 < c`). -/
-- tier: T2
theorem s4ADKTrivialization_pos_cooriented (u : s4ADKPreimageOpen) :
    ∃ c : ℝ, 0 < c ∧
      (TauCeti.SmoothForm.mpullback s4ADKTrivialization s4ADKTrivialization.contMDiff
          (TauCeti.SmoothForm.wedge
            (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd S2VolumeForm)
            (TauCeti.SmoothForm.mpullback (Subtype.val ∘ Prod.fst)
              (contMDiff_subtype_val.comp contMDiff_fst) S2VolumeForm))).1 u =
        c • (TauCeti.SmoothForm.mpullback Subtype.val
          contMDiff_subtype_val S4VolumeForm).1 u := by
  obtain ⟨c, hc_pos, hc_eq⟩ := adkTrivData.hU_pos (s4ADKIncl u) (s4ADKIncl_mem_U u)
  refine ⟨c, hc_pos, ?_⟩
  rw [mpullback_s4ADKIncl_adkTargetPullForm, ← mpullback_s4ADKIncl_adkSourceForm]
  ext v
  rw [TauCeti.SmoothForm.mpullback_apply, ContinuousAlternatingMap.smul_apply,
    TauCeti.SmoothForm.mpullback_apply, hc_eq, ContinuousAlternatingMap.smul_apply]

/-- Global ADK fibration `s4ADKFibration` packaged as a `RegularDiskFibration` with regular
`Sphere2` fiber over `s4ADKBaseRegion`. -/
noncomputable def s4ADKRegularDiskFibration :
    RegularDiskFibration (𝓡 4) Sphere4 (𝓡 2) Sphere2 Sphere2 where
  toFun := s4ADKFibration
  contMDiff_toFun := contMDiff_s4ADKFibration
  baseRegion := s4ADKBaseRegion
  baseRegion_nonempty := s4ADKBaseRegion_nonempty
  regular_on_preimage := regular_on_s4ADKBaseRegion
  baseDiskRadius := s4ADKBaseDiskRadius
  baseDiskRadius_pos := s4ADKBaseDiskRadius_pos
  baseDisk := s4ADKBaseDiskDiffeomorph
  trivialization := s4ADKTrivialization
  trivialization_fst := s4ADKTrivialization_fst

/-- **Global ADK Broken Lefschetz Fibration on $S^4$ ($S^2$ Chamber)**: every critical point of
`s4ADKFibration` is an indefinite quadratic fold (`IsIndefiniteFoldAt`), with zero real Lefschetz
points, trivialized over the north-hemisphere $S^2$ chamber `s4ADKBaseRegion`. -/
-- tier: T2
noncomputable def s4BrokenLefschetzFibration :
    BrokenLefschetzFibration (𝓡 4) Sphere4 (𝓡 2) Sphere2 Sphere2 where
  toRegularDiskFibration := s4ADKRegularDiskFibration
  singularities_broken_lefschetz _ hp := Or.inr (isIndefiniteFoldAt_s4ADKFibration hp)

/-- **Purely Wrinkled ADK Fibration on $S^4$**: every critical point of `s4ADKFibration` is an
indefinite quadratic fold (via `toPurelyWrinkledOfIndefiniteFolds`). -/
-- tier: T2
noncomputable def s4PurelyWrinkledFibration :
    PurelyWrinkledFibration (𝓡 4) Sphere4 (𝓡 2) Sphere2 Sphere2 :=
  s4BrokenLefschetzFibration.toPurelyWrinkledOfIndefiniteFolds
    fun _ hp ↦ isIndefiniteFoldAt_s4ADKFibration hp

/-! ### South-Hemisphere $T^2$ Chamber Trivialization (`SC-R6b`) -/

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

/-- Smooth antipodal involution `z ↦ -z` on `Sphere2`. -/
noncomputable def s2Antipodal : Sphere2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere2 where
  toFun z := ⟨-z.1, by
    rw [mem_sphere_zero_iff_norm, norm_neg]; exact mem_sphere_zero_iff_norm.mp z.2⟩
  invFun z := ⟨-z.1, by
    rw [mem_sphere_zero_iff_norm, norm_neg]; exact mem_sphere_zero_iff_norm.mp z.2⟩
  left_inv z := Subtype.ext (neg_neg z.1)
  right_inv z := Subtype.ext (neg_neg z.1)
  contMDiff_toFun :=
    (contDiff_neg.contMDiff.comp contMDiff_coe_sphere).codRestrict_sphere fun z ↦ by
      dsimp only [Function.comp_apply]
      rw [mem_sphere_zero_iff_norm, norm_neg]; exact mem_sphere_zero_iff_norm.mp z.2
  contMDiff_invFun :=
    (contDiff_neg.contMDiff.comp contMDiff_coe_sphere).codRestrict_sphere fun z ↦ by
      dsimp only [Function.comp_apply]
      rw [mem_sphere_zero_iff_norm, norm_neg]; exact mem_sphere_zero_iff_norm.mp z.2

@[simp]
private theorem coe_s2Antipodal (z : Sphere2) :
    (s2Antipodal z : EuclideanSpace ℝ (Fin 3)) = -z.1 := rfl

@[simp]
private theorem s2Antipodal_involutive (z : Sphere2) :
    s2Antipodal (s2Antipodal z) = z :=
  Subtype.ext (neg_neg z.1)

@[simp]
private theorem s2Antipodal_northPole : s2Antipodal s2NorthPole = s2SouthPole := by
  apply Subtype.ext
  refine ext_vec3 ?_ ?_ ?_ <;> simp [s2NorthPole, s2SouthPole]

@[simp]
private theorem s2Antipodal_southPole : s2Antipodal s2SouthPole = s2NorthPole := by
  apply Subtype.ext
  refine ext_vec3 ?_ ?_ ?_ <;> simp [s2NorthPole, s2SouthPole]

/-- If `z ≠ s2NorthPole`, its antipode `s2Antipodal z` differs from `s2SouthPole`. -/
theorem s2Antipodal_ne_southPole_of_ne_northPole {z : Sphere2} (hz : z ≠ s2NorthPole) :
    s2Antipodal z ≠ s2SouthPole := by
  intro h
  apply hz
  have h2 := congrArg s2Antipodal h
  simpa using h2

/-- North-pole inverse stereographic parameterization `ℝ² → Sphere2` centered at `s2SouthPole`. -/
noncomputable def northPoleStereoInv (w : EuclideanPlane) : Sphere2 :=
  s2Antipodal (southPoleStereoInv w)

/-- Smoothness of `northPoleStereoInv`. -/
theorem contMDiff_northPoleStereoInv : ContMDiff (𝓡 2) (𝓡 2) ∞ northPoleStereoInv :=
  s2Antipodal.contMDiff.comp contMDiff_southPoleStereoInv

/-- `northPoleStereoInv 0 = s2SouthPole`. -/
@[simp]
theorem northPoleStereoInv_zero : northPoleStereoInv 0 = s2SouthPole := by
  simp [northPoleStereoInv]

/-- `northPoleStereoInv` never hits `s2NorthPole`. -/
theorem northPoleStereoInv_ne_northPole (w : EuclideanPlane) :
    northPoleStereoInv w ≠ s2NorthPole := by
  intro h
  have h2 := congrArg s2Antipodal h
  simp only [northPoleStereoInv, s2Antipodal_involutive, s2Antipodal_northPole] at h2
  exact southPoleStereoInv_ne_southPole w h2

/-- Injectivity of `northPoleStereoInv`. -/
theorem injective_northPoleStereoInv : Function.Injective northPoleStereoInv :=
  s2Antipodal.injective.comp injective_southPoleStereoInv

/-- Open embedding property of `northPoleStereoInv`. -/
theorem isOpenEmbedding_northPoleStereoInv : Topology.IsOpenEmbedding northPoleStereoInv :=
  s2Antipodal.toHomeomorph.isOpenEmbedding.comp isOpenEmbedding_southPoleStereoInv

/-- Forward north-pole stereographic coordinate chart centered at `s2SouthPole`. -/
noncomputable def northPoleStereoChart (z : Sphere2) : EuclideanPlane :=
  southPoleStereoChart (s2Antipodal z)

/-- Left-inverse identity `northPoleStereoChart (northPoleStereoInv w) = w`. -/
@[simp]
theorem northPoleStereoChart_inv (w : EuclideanPlane) :
    northPoleStereoChart (northPoleStereoInv w) = w := by
  simp [northPoleStereoChart, northPoleStereoInv]

/-- Right-inverse identity `northPoleStereoInv (northPoleStereoChart z) = z` off `s2NorthPole`. -/
theorem northPoleStereoInv_chart {z : Sphere2} (hz : z ≠ s2NorthPole) :
    northPoleStereoInv (northPoleStereoChart z) = z := by
  simp only [northPoleStereoInv, northPoleStereoChart]
  rw [southPoleStereoInv_chart (s2Antipodal_ne_southPole_of_ne_northPole hz),
    s2Antipodal_involutive]

/-- Radius `1 / 6` for the normal coordinate disk of the Clifford torus tubular neighborhood. -/
noncomputable def s4TorusDiskRadius : ℝ := 1 / 6

/-- Positivity `0 < s4TorusDiskRadius`. -/
theorem s4TorusDiskRadius_pos : 0 < s4TorusDiskRadius := by
  norm_num [s4TorusDiskRadius]

/-- Open planar normal disk `Metric.ball 0 (1 / 6)` for the Clifford torus neighborhood. -/
noncomputable abbrev s4TorusDisk : Opens EuclideanPlane :=
  ⟨Metric.ball (0 : EuclideanPlane) s4TorusDiskRadius, Metric.isOpen_ball⟩

/-- Origin `(0 : ℝ²)` in `s4TorusDisk`. -/
noncomputable def s4TorusDiskZero : s4TorusDisk :=
  ⟨0, Metric.mem_ball_self s4TorusDiskRadius_pos⟩

@[simp]
private theorem coe_s4TorusDiskZero : (s4TorusDiskZero : EuclideanPlane) = 0 := rfl

private theorem s4TorusDisk_bounds {w : EuclideanPlane} (hw : w ∈ s4TorusDisk.1) :
    -1 / 6 < w 0 ∧ w 0 < 1 / 6 ∧ w 1 ^ 2 < 1 / 36 := by
  have hn : ‖w‖ < 1 / 6 := by simpa [s4TorusDisk, s4TorusDiskRadius, dist_zero_right] using hw
  have hsq : ‖w‖ ^ 2 < (1 / 6) ^ 2 := by nlinarith [norm_nonneg w]
  rw [norm_sq_plane] at hsq
  have hw0_sq : w 0 ^ 2 < (1 / 6) ^ 2 := by nlinarith [sq_nonneg (w 1)]
  have hw0_abs : |w 0| < 1 / 6 := by
    simpa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 6)] using sq_lt_sq.mp hw0_sq
  rw [abs_lt] at hw0_abs
  refine ⟨by linarith, hw0_abs.2, ?_⟩
  nlinarith [sq_nonneg (w 0)]

private theorem torusRad1Sq_pos {w : EuclideanPlane} (hw : w ∈ s4TorusDisk.1) :
    0 < 1 / 2 - w 0 - w 1 ^ 2 := by
  obtain ⟨-, hw0_hi, hw1_sq⟩ := s4TorusDisk_bounds hw
  linarith

private theorem torusRad2Sq_pos {w : EuclideanPlane} (hw : w ∈ s4TorusDisk.1) :
    0 < 1 / 2 + w 0 := by
  obtain ⟨hw0_lo, -, -⟩ := s4TorusDisk_bounds hw
  linarith

/-- Ambient Euclidean formula for the Clifford torus tubular embedding `ℝ² × Torus2 → ℝ⁵`. -/
noncomputable def s4TorusEmbedRaw (w : EuclideanPlane) (t : Torus2) :
    EuclideanSpace ℝ (Fin 5) :=
  let r₁ := Real.sqrt (1 / 2 - w 0 - w 1 ^ 2)
  let r₂ := Real.sqrt (1 / 2 + w 0)
  vec5 (r₁ * t.fst.1 0) (r₁ * t.fst.1 1) (r₂ * t.snd.1 0) (r₂ * t.snd.1 1) (w 1)

/-- `s4TorusEmbedRaw` maps `s4TorusDisk × Torus2` into the unit 4-sphere. -/
theorem s4TorusEmbedRaw_mem_sphere (wt : s4TorusDisk × Torus2) :
    s4TorusEmbedRaw wt.1.1 wt.2 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have hr1 := torusRad1Sq_pos wt.1.2
  have hr2 := torusRad2Sq_pos wt.1.2
  have hu1 : wt.2.fst.1 0 ^ 2 + wt.2.fst.1 1 ^ 2 = 1 := by
    rw [← norm_sq_plane, mem_sphere_zero_iff_norm.mp wt.2.fst.2, one_pow]
  have hu2 : wt.2.snd.1 0 ^ 2 + wt.2.snd.1 1 ^ 2 = 1 := by
    rw [← norm_sq_plane, mem_sphere_zero_iff_norm.mp wt.2.snd.2, one_pow]
  have hsq : ‖s4TorusEmbedRaw wt.1.1 wt.2‖ ^ 2 = 1 := by
    rw [norm_sq_vec5]
    dsimp only [s4TorusEmbedRaw]
    simp only [vec5_zero, vec5_one, vec5_two, vec5_three, vec5_four]
    calc
      (Real.sqrt (1 / 2 - wt.1.1 0 - wt.1.1 1 ^ 2) * wt.2.fst.1 0) ^ 2 +
          (Real.sqrt (1 / 2 - wt.1.1 0 - wt.1.1 1 ^ 2) * wt.2.fst.1 1) ^ 2 +
          (Real.sqrt (1 / 2 + wt.1.1 0) * wt.2.snd.1 0) ^ 2 +
          (Real.sqrt (1 / 2 + wt.1.1 0) * wt.2.snd.1 1) ^ 2 + wt.1.1 1 ^ 2
        = Real.sqrt (1 / 2 - wt.1.1 0 - wt.1.1 1 ^ 2) ^ 2 *
            (wt.2.fst.1 0 ^ 2 + wt.2.fst.1 1 ^ 2) +
          Real.sqrt (1 / 2 + wt.1.1 0) ^ 2 *
            (wt.2.snd.1 0 ^ 2 + wt.2.snd.1 1 ^ 2) + wt.1.1 1 ^ 2 := by ring
      _ = 1 := by rw [Real.sq_sqrt hr1.le, Real.sq_sqrt hr2.le, hu1, hu2]; ring
  nlinarith [norm_nonneg (s4TorusEmbedRaw wt.1.1 wt.2)]

/-- Smooth tubular embedding `s4TorusDisk × Torus2 → Sphere4` around the Clifford torus. -/
noncomputable def s4TorusEmbed (wt : s4TorusDisk × Torus2) : Sphere4 :=
  ⟨s4TorusEmbedRaw wt.1.1 wt.2, s4TorusEmbedRaw_mem_sphere wt⟩

/-- Smoothness of `s4TorusEmbed`. -/
-- tier: T2
theorem contMDiff_s4TorusEmbed :
    ContMDiff ((𝓡 2).prod (𝓡 2)) (𝓡 4) ∞ s4TorusEmbed := by
  have hw_val : ContMDiff ((𝓡 2).prod (𝓡 2)) 𝓘(ℝ, EuclideanPlane) ∞
      (fun wt : s4TorusDisk × Torus2 ↦ wt.1.1) :=
    contMDiff_subtype_val.comp contMDiff_fst
  have hw (i : Fin 2) : ContMDiff ((𝓡 2).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (fun wt : s4TorusDisk × Torus2 ↦ wt.1.1 i) :=
    (euclidProj i).contDiff.contMDiff.comp hw_val
  have hrad1 : ContMDiff ((𝓡 2).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (fun wt : s4TorusDisk × Torus2 ↦ 1 / 2 - wt.1.1 0 - wt.1.1 1 ^ 2) :=
    ((contDiff_const.sub (euclidProj (0 : Fin 2)).contDiff).sub
      ((euclidProj (1 : Fin 2)).contDiff.pow 2)).contMDiff.comp hw_val
  have hrad2 : ContMDiff ((𝓡 2).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (fun wt : s4TorusDisk × Torus2 ↦ 1 / 2 + wt.1.1 0) :=
    (contDiff_const.add (euclidProj (0 : Fin 2)).contDiff).contMDiff.comp hw_val
  have hr1 : ContMDiff ((𝓡 2).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (fun wt : s4TorusDisk × Torus2 ↦ Real.sqrt (1 / 2 - wt.1.1 0 - wt.1.1 1 ^ 2)) :=
    fun wt ↦ (Real.contDiffAt_sqrt (torusRad1Sq_pos wt.1.2).ne').contMDiffAt.comp wt (hrad1 wt)
  have hr2 : ContMDiff ((𝓡 2).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (fun wt : s4TorusDisk × Torus2 ↦ Real.sqrt (1 / 2 + wt.1.1 0)) :=
    fun wt ↦ (Real.contDiffAt_sqrt (torusRad2Sq_pos wt.1.2).ne').contMDiffAt.comp wt (hrad2 wt)
  have hc1 (k : Fin 2) : ContMDiff ((𝓡 2).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (fun wt : s4TorusDisk × Torus2 ↦ wt.2.fst.1 k) :=
    (euclidProj k).contDiff.contMDiff.comp (Torus2.contMDiff_coe_fst.comp contMDiff_snd)
  have hc2 (k : Fin 2) : ContMDiff ((𝓡 2).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (fun wt : s4TorusDisk × Torus2 ↦ wt.2.snd.1 k) :=
    (euclidProj k).contDiff.contMDiff.comp (Torus2.contMDiff_coe_snd.comp contMDiff_snd)
  have hmul : ContDiff ℝ ∞ (fun q : ℝ × ℝ ↦ q.1 * q.2) := contDiff_fst.mul contDiff_snd
  have hpi : ContMDiff ((𝓡 2).prod (𝓡 2)) 𝓘(ℝ, Fin 5 → ℝ) ∞
      (fun wt : s4TorusDisk × Torus2 ↦
        ![Real.sqrt (1 / 2 - wt.1.1 0 - wt.1.1 1 ^ 2) * wt.2.fst.1 0,
          Real.sqrt (1 / 2 - wt.1.1 0 - wt.1.1 1 ^ 2) * wt.2.fst.1 1,
          Real.sqrt (1 / 2 + wt.1.1 0) * wt.2.snd.1 0,
          Real.sqrt (1 / 2 + wt.1.1 0) * wt.2.snd.1 1,
          wt.1.1 1]) := by
    refine contMDiff_pi_module_iff.mpr fun i ↦ ?_
    fin_cases i
    · exact hmul.contMDiff.comp (hr1.prodMk_space (hc1 0))
    · exact hmul.contMDiff.comp (hr1.prodMk_space (hc1 1))
    · exact hmul.contMDiff.comp (hr2.prodMk_space (hc2 0))
    · exact hmul.contMDiff.comp (hr2.prodMk_space (hc2 1))
    · exact hw 1
  have hraw : ContMDiff ((𝓡 2).prod (𝓡 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 5)) ∞
      (fun wt : s4TorusDisk × Torus2 ↦ s4TorusEmbedRaw wt.1.1 wt.2) :=
    (EuclideanSpace.equiv (Fin 5) ℝ).symm.contDiff.contMDiff.comp hpi
  exact hraw.codRestrict_sphere _

/-- Normal coordinate map `x ↦ (x₂² + x₃² - 1 / 2, x₄)` for the Clifford torus neighborhood. -/
noncomputable def torusNormalCoord (x : Sphere4) : EuclideanPlane :=
  vec2 (x.1 2 ^ 2 + x.1 3 ^ 2 - 1 / 2) (x.1 4)

/-- Smoothness of `torusNormalCoord`. -/
theorem contMDiff_torusNormalCoord :
    ContMDiff (𝓡 4) 𝓘(ℝ, EuclideanPlane) ∞ torusNormalCoord :=
  (contDiff_vec2
    ((((euclidProj (2 : Fin 5)).contDiff.pow 2).add
      ((euclidProj (3 : Fin 5)).contDiff.pow 2)).sub contDiff_const)
    (euclidProj (4 : Fin 5)).contDiff).contMDiff.comp contMDiff_coe_sphere

private theorem torusNormalCoord_s4TorusEmbed (wt : s4TorusDisk × Torus2) :
    torusNormalCoord (s4TorusEmbed wt) = wt.1.1 := by
  have hr2 := torusRad2Sq_pos wt.1.2
  have hu2 : wt.2.snd.1 0 ^ 2 + wt.2.snd.1 1 ^ 2 = 1 := by
    rw [← norm_sq_plane, mem_sphere_zero_iff_norm.mp wt.2.snd.2, one_pow]
  refine ext_vec2 ?_ ?_
  · simp only [torusNormalCoord, s4TorusEmbed, s4TorusEmbedRaw, vec2_zero, vec5_two, vec5_three]
    calc
      (Real.sqrt (1 / 2 + wt.1.1 0) * wt.2.snd.1 0) ^ 2 +
          (Real.sqrt (1 / 2 + wt.1.1 0) * wt.2.snd.1 1) ^ 2 - 1 / 2
        = Real.sqrt (1 / 2 + wt.1.1 0) ^ 2 * (wt.2.snd.1 0 ^ 2 + wt.2.snd.1 1 ^ 2) - 1 / 2 := by
          ring
      _ = wt.1.1 0 := by rw [Real.sq_sqrt hr2.le, hu2]; ring
  · simp [torusNormalCoord, s4TorusEmbed, s4TorusEmbedRaw]

/-- Open tubular neighborhood of the Clifford torus in `Sphere4`. -/
noncomputable abbrev s4TorusTubularOpen : Opens Sphere4 :=
  ⟨{x : Sphere4 | torusNormalCoord x ∈ s4TorusDisk.1},
    s4TorusDisk.2.preimage contMDiff_torusNormalCoord.continuous⟩

/-- Image containment `s4TorusEmbed wt ∈ s4TorusTubularOpen`. -/
theorem s4TorusEmbed_mem_tubularOpen (wt : s4TorusDisk × Torus2) :
    s4TorusEmbed wt ∈ s4TorusTubularOpen.1 := by
  show torusNormalCoord (s4TorusEmbed wt) ∈ s4TorusDisk.1
  rw [torusNormalCoord_s4TorusEmbed]
  exact wt.1.2

private theorem s4TorusTubular_pair01_pos (u : s4TorusTubularOpen) :
    0 < u.1.1 0 ^ 2 + u.1.1 1 ^ 2 := by
  have hx : u.1.1 0 ^ 2 + u.1.1 1 ^ 2 + u.1.1 2 ^ 2 + u.1.1 3 ^ 2 + u.1.1 4 ^ 2 = 1 := by
    rw [← norm_sq_vec5, mem_sphere_zero_iff_norm.mp u.1.2, one_pow]
  have h1 := torusRad1Sq_pos u.2
  have hc0 : (torusNormalCoord u.1) 0 = u.1.1 2 ^ 2 + u.1.1 3 ^ 2 - 1 / 2 := vec2_zero _ _
  have hc1 : (torusNormalCoord u.1) 1 = u.1.1 4 := vec2_one _ _
  rw [hc0, hc1] at h1
  linarith

private theorem s4TorusTubular_pair23_pos (u : s4TorusTubularOpen) :
    0 < u.1.1 2 ^ 2 + u.1.1 3 ^ 2 := by
  have h2 := torusRad2Sq_pos u.2
  have hc0 : (torusNormalCoord u.1) 0 = u.1.1 2 ^ 2 + u.1.1 3 ^ 2 - 1 / 2 := vec2_zero _ _
  rw [hc0] at h2
  linarith

/-- First unit-circle factor projection on `s4TorusTubularOpen`. -/
noncomputable def torusTubularCircle1Raw (u : s4TorusTubularOpen) : EuclideanPlane :=
  let r₁ := Real.sqrt (u.1.1 0 ^ 2 + u.1.1 1 ^ 2)
  vec2 (r₁⁻¹ * u.1.1 0) (r₁⁻¹ * u.1.1 1)

/-- `torusTubularCircle1Raw u` lies on the unit circle `S¹ ⊂ ℝ²`. -/
theorem torusTubularCircle1Raw_mem_sphere (u : s4TorusTubularOpen) :
    torusTubularCircle1Raw u ∈ Metric.sphere (0 : EuclideanPlane) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have hp := s4TorusTubular_pair01_pos u
  have hsq : ‖torusTubularCircle1Raw u‖ ^ 2 = 1 := by
    rw [norm_sq_plane]
    dsimp only [torusTubularCircle1Raw]
    simp only [vec2_zero, vec2_one]
    calc
      ((Real.sqrt (u.1.1 0 ^ 2 + u.1.1 1 ^ 2))⁻¹ * u.1.1 0) ^ 2 +
          ((Real.sqrt (u.1.1 0 ^ 2 + u.1.1 1 ^ 2))⁻¹ * u.1.1 1) ^ 2
        = (Real.sqrt (u.1.1 0 ^ 2 + u.1.1 1 ^ 2) ^ 2)⁻¹ * (u.1.1 0 ^ 2 + u.1.1 1 ^ 2) := by ring
      _ = 1 := by rw [Real.sq_sqrt hp.le, inv_mul_cancel₀ hp.ne']
  nlinarith [norm_nonneg (torusTubularCircle1Raw u)]

/-- Second unit-circle factor projection on `s4TorusTubularOpen`. -/
noncomputable def torusTubularCircle2Raw (u : s4TorusTubularOpen) : EuclideanPlane :=
  let r₂ := Real.sqrt (u.1.1 2 ^ 2 + u.1.1 3 ^ 2)
  vec2 (r₂⁻¹ * u.1.1 2) (r₂⁻¹ * u.1.1 3)

/-- `torusTubularCircle2Raw u` lies on the unit circle `S¹ ⊂ ℝ²`. -/
theorem torusTubularCircle2Raw_mem_sphere (u : s4TorusTubularOpen) :
    torusTubularCircle2Raw u ∈ Metric.sphere (0 : EuclideanPlane) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have hp := s4TorusTubular_pair23_pos u
  have hsq : ‖torusTubularCircle2Raw u‖ ^ 2 = 1 := by
    rw [norm_sq_plane]
    dsimp only [torusTubularCircle2Raw]
    simp only [vec2_zero, vec2_one]
    calc
      ((Real.sqrt (u.1.1 2 ^ 2 + u.1.1 3 ^ 2))⁻¹ * u.1.1 2) ^ 2 +
          ((Real.sqrt (u.1.1 2 ^ 2 + u.1.1 3 ^ 2))⁻¹ * u.1.1 3) ^ 2
        = (Real.sqrt (u.1.1 2 ^ 2 + u.1.1 3 ^ 2) ^ 2)⁻¹ * (u.1.1 2 ^ 2 + u.1.1 3 ^ 2) := by ring
      _ = 1 := by rw [Real.sq_sqrt hp.le, inv_mul_cancel₀ hp.ne']
  nlinarith [norm_nonneg (torusTubularCircle2Raw u)]

/-- Smooth diffeomorphism `s4TorusTubularOpen ≃ₘ s4TorusDisk × Torus2`. -/
-- tier: T2
noncomputable def s4TorusTubularTrivialization :
    s4TorusTubularOpen ≃ₘ⟮𝓡 4, (𝓡 2).prod (𝓡 2)⟯ (s4TorusDisk × Torus2) where
  toFun u :=
    (⟨torusNormalCoord u.1, u.2⟩,
      Torus2.toProdDiffeomorph.symm
        (Set.codRestrict torusTubularCircle1Raw _ torusTubularCircle1Raw_mem_sphere u,
          Set.codRestrict torusTubularCircle2Raw _ torusTubularCircle2Raw_mem_sphere u))
  invFun wt := ⟨s4TorusEmbed wt, s4TorusEmbed_mem_tubularOpen wt⟩
  left_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    have hx : u.1.1 0 ^ 2 + u.1.1 1 ^ 2 + u.1.1 2 ^ 2 + u.1.1 3 ^ 2 + u.1.1 4 ^ 2 = 1 := by
      rw [← norm_sq_vec5, mem_sphere_zero_iff_norm.mp u.1.2, one_pow]
    have hp1 := s4TorusTubular_pair01_pos u
    have hp2 := s4TorusTubular_pair23_pos u
    have hr1_ne : Real.sqrt (u.1.1 0 ^ 2 + u.1.1 1 ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hp1).ne'
    have hr2_ne : Real.sqrt (u.1.1 2 ^ 2 + u.1.1 3 ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hp2).ne'
    have hrad1_eq : 1 / 2 - (torusNormalCoord u.1) 0 - (torusNormalCoord u.1) 1 ^ 2 =
        u.1.1 0 ^ 2 + u.1.1 1 ^ 2 := by
      simp only [torusNormalCoord, vec2_zero, vec2_one]
      linarith
    have hrad2_eq : 1 / 2 + (torusNormalCoord u.1) 0 = u.1.1 2 ^ 2 + u.1.1 3 ^ 2 := by
      simp only [torusNormalCoord, vec2_zero]
      ring
    refine ext_vec5 ?_ ?_ ?_ ?_ ?_
    · dsimp only [s4TorusEmbed, s4TorusEmbedRaw]
      simp only [coe_torus2_toProdDiffeomorph_symm, vec5_zero, hrad1_eq]
      dsimp only [Set.codRestrict, torusTubularCircle1Raw]
      simp only [vec2_zero]
      exact mul_inv_cancel_left₀ hr1_ne _
    · dsimp only [s4TorusEmbed, s4TorusEmbedRaw]
      simp only [coe_torus2_toProdDiffeomorph_symm, vec5_one, hrad1_eq]
      dsimp only [Set.codRestrict, torusTubularCircle1Raw]
      simp only [vec2_one]
      exact mul_inv_cancel_left₀ hr1_ne _
    · dsimp only [s4TorusEmbed, s4TorusEmbedRaw]
      simp only [coe_torus2_toProdDiffeomorph_symm, vec5_two, hrad2_eq]
      dsimp only [Set.codRestrict, torusTubularCircle2Raw]
      simp only [vec2_zero]
      exact mul_inv_cancel_left₀ hr2_ne _
    · dsimp only [s4TorusEmbed, s4TorusEmbedRaw]
      simp only [coe_torus2_toProdDiffeomorph_symm, vec5_three, hrad2_eq]
      dsimp only [Set.codRestrict, torusTubularCircle2Raw]
      simp only [vec2_one]
      exact mul_inv_cancel_left₀ hr2_ne _
    · simp [s4TorusEmbed, s4TorusEmbedRaw, torusNormalCoord]
  right_inv := by
    rintro ⟨w, t⟩
    have hw_eq := torusNormalCoord_s4TorusEmbed (w, t)
    have hr1_pos : 0 < Real.sqrt (1 / 2 - w.1 0 - w.1 1 ^ 2) :=
      Real.sqrt_pos.mpr (torusRad1Sq_pos w.2)
    have hr2_pos : 0 < Real.sqrt (1 / 2 + w.1 0) :=
      Real.sqrt_pos.mpr (torusRad2Sq_pos w.2)
    have hu1 : t.fst.1 0 ^ 2 + t.fst.1 1 ^ 2 = 1 := by
      rw [← norm_sq_plane, mem_sphere_zero_iff_norm.mp t.fst.2, one_pow]
    have hu2 : t.snd.1 0 ^ 2 + t.snd.1 1 ^ 2 = 1 := by
      rw [← norm_sq_plane, mem_sphere_zero_iff_norm.mp t.snd.2, one_pow]
    have hsq1 : (s4TorusEmbed (w, t)).1 0 ^ 2 + (s4TorusEmbed (w, t)).1 1 ^ 2 =
        Real.sqrt (1 / 2 - w.1 0 - w.1 1 ^ 2) ^ 2 := by
      dsimp only [s4TorusEmbed, s4TorusEmbedRaw]
      simp only [vec5_zero, vec5_one]
      calc
        (Real.sqrt (1 / 2 - w.1 0 - w.1 1 ^ 2) * t.fst.1 0) ^ 2 +
            (Real.sqrt (1 / 2 - w.1 0 - w.1 1 ^ 2) * t.fst.1 1) ^ 2
          = Real.sqrt (1 / 2 - w.1 0 - w.1 1 ^ 2) ^ 2 * (t.fst.1 0 ^ 2 + t.fst.1 1 ^ 2) := by ring
        _ = Real.sqrt (1 / 2 - w.1 0 - w.1 1 ^ 2) ^ 2 := by rw [hu1, mul_one]
    have hsq2 : (s4TorusEmbed (w, t)).1 2 ^ 2 + (s4TorusEmbed (w, t)).1 3 ^ 2 =
        Real.sqrt (1 / 2 + w.1 0) ^ 2 := by
      dsimp only [s4TorusEmbed, s4TorusEmbedRaw]
      simp only [vec5_two, vec5_three]
      calc
        (Real.sqrt (1 / 2 + w.1 0) * t.snd.1 0) ^ 2 +
            (Real.sqrt (1 / 2 + w.1 0) * t.snd.1 1) ^ 2
          = Real.sqrt (1 / 2 + w.1 0) ^ 2 * (t.snd.1 0 ^ 2 + t.snd.1 1 ^ 2) := by ring
        _ = Real.sqrt (1 / 2 + w.1 0) ^ 2 := by rw [hu2, mul_one]
    refine Prod.ext (Subtype.ext hw_eq) ?_
    ext1
    · apply Subtype.ext
      refine ext_vec2 ?_ ?_
      · simp only [coe_torus2_toProdDiffeomorph_symm]
        dsimp only [Set.codRestrict, torusTubularCircle1Raw]
        rw [hsq1, Real.sqrt_sq hr1_pos.le]
        dsimp only [s4TorusEmbed, s4TorusEmbedRaw]
        simp only [vec2_zero, vec5_zero]
        exact inv_mul_cancel_left₀ hr1_pos.ne' _
      · simp only [coe_torus2_toProdDiffeomorph_symm]
        dsimp only [Set.codRestrict, torusTubularCircle1Raw]
        rw [hsq1, Real.sqrt_sq hr1_pos.le]
        dsimp only [s4TorusEmbed, s4TorusEmbedRaw]
        simp only [vec2_one, vec5_one]
        exact inv_mul_cancel_left₀ hr1_pos.ne' _
    · apply Subtype.ext
      refine ext_vec2 ?_ ?_
      · simp only [coe_torus2_toProdDiffeomorph_symm]
        dsimp only [Set.codRestrict, torusTubularCircle2Raw]
        rw [hsq2, Real.sqrt_sq hr2_pos.le]
        dsimp only [s4TorusEmbed, s4TorusEmbedRaw]
        simp only [vec2_zero, vec5_two]
        exact inv_mul_cancel_left₀ hr2_pos.ne' _
      · simp only [coe_torus2_toProdDiffeomorph_symm]
        dsimp only [Set.codRestrict, torusTubularCircle2Raw]
        rw [hsq2, Real.sqrt_sq hr2_pos.le]
        dsimp only [s4TorusEmbed, s4TorusEmbedRaw]
        simp only [vec2_one, vec5_three]
        exact inv_mul_cancel_left₀ hr2_pos.ne' _
  contMDiff_toFun := by
    have hfst : ContMDiff (𝓡 4) (𝓡 2) ∞
        (fun u : s4TorusTubularOpen ↦ (⟨torusNormalCoord u.1, u.2⟩ : s4TorusDisk)) :=
      (TauCeti.ContMDiff.subtypeVal_comp_iff s4TorusDisk _).mp
        (contMDiff_torusNormalCoord.comp contMDiff_subtype_val)
    have hcoe : ContMDiff (𝓡 4) 𝓘(ℝ, EuclideanSpace ℝ (Fin 5)) ∞
        (fun u : s4TorusTubularOpen ↦ u.1.1) :=
      contMDiff_coe_sphere.comp contMDiff_subtype_val
    have hx (k : Fin 5) : ContMDiff (𝓡 4) 𝓘(ℝ, ℝ) ∞ (fun u : s4TorusTubularOpen ↦ u.1.1 k) :=
      (euclidProj k).contDiff.contMDiff.comp hcoe
    have hsum1 : ContMDiff (𝓡 4) 𝓘(ℝ, ℝ) ∞
        (fun u : s4TorusTubularOpen ↦ u.1.1 0 ^ 2 + u.1.1 1 ^ 2) :=
      (((euclidProj (0 : Fin 5)).contDiff.pow 2).add
        ((euclidProj (1 : Fin 5)).contDiff.pow 2)).contMDiff.comp hcoe
    have hsum2 : ContMDiff (𝓡 4) 𝓘(ℝ, ℝ) ∞
        (fun u : s4TorusTubularOpen ↦ u.1.1 2 ^ 2 + u.1.1 3 ^ 2) :=
      (((euclidProj (2 : Fin 5)).contDiff.pow 2).add
        ((euclidProj (3 : Fin 5)).contDiff.pow 2)).contMDiff.comp hcoe
    have hinv1 : ContMDiff (𝓡 4) 𝓘(ℝ, ℝ) ∞
        (fun u : s4TorusTubularOpen ↦ (Real.sqrt (u.1.1 0 ^ 2 + u.1.1 1 ^ 2))⁻¹) := fun u ↦ by
      have hp := s4TorusTubular_pair01_pos u
      exact (contDiffAt_inv ℝ (Real.sqrt_pos.mpr hp).ne').contMDiffAt.comp u
        ((Real.contDiffAt_sqrt hp.ne').contMDiffAt.comp u (hsum1 u))
    have hinv2 : ContMDiff (𝓡 4) 𝓘(ℝ, ℝ) ∞
        (fun u : s4TorusTubularOpen ↦ (Real.sqrt (u.1.1 2 ^ 2 + u.1.1 3 ^ 2))⁻¹) := fun u ↦ by
      have hp := s4TorusTubular_pair23_pos u
      exact (contDiffAt_inv ℝ (Real.sqrt_pos.mpr hp).ne').contMDiffAt.comp u
        ((Real.contDiffAt_sqrt hp.ne').contMDiffAt.comp u (hsum2 u))
    have hmul : ContDiff ℝ ∞ (fun q : ℝ × ℝ ↦ q.1 * q.2) := contDiff_fst.mul contDiff_snd
    have hpi1 : ContMDiff (𝓡 4) 𝓘(ℝ, Fin 2 → ℝ) ∞
        (fun u : s4TorusTubularOpen ↦
          ![(Real.sqrt (u.1.1 0 ^ 2 + u.1.1 1 ^ 2))⁻¹ * u.1.1 0,
            (Real.sqrt (u.1.1 0 ^ 2 + u.1.1 1 ^ 2))⁻¹ * u.1.1 1]) := by
      refine contMDiff_pi_module_iff.mpr fun i ↦ ?_
      fin_cases i
      · exact hmul.contMDiff.comp (hinv1.prodMk_space (hx 0))
      · exact hmul.contMDiff.comp (hinv1.prodMk_space (hx 1))
    have hpi2 : ContMDiff (𝓡 4) 𝓘(ℝ, Fin 2 → ℝ) ∞
        (fun u : s4TorusTubularOpen ↦
          ![(Real.sqrt (u.1.1 2 ^ 2 + u.1.1 3 ^ 2))⁻¹ * u.1.1 2,
            (Real.sqrt (u.1.1 2 ^ 2 + u.1.1 3 ^ 2))⁻¹ * u.1.1 3]) := by
      refine contMDiff_pi_module_iff.mpr fun i ↦ ?_
      fin_cases i
      · exact hmul.contMDiff.comp (hinv2.prodMk_space (hx 2))
      · exact hmul.contMDiff.comp (hinv2.prodMk_space (hx 3))
    have hraw1 : ContMDiff (𝓡 4) 𝓘(ℝ, EuclideanPlane) ∞ torusTubularCircle1Raw :=
      (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.contMDiff.comp hpi1
    have hraw2 : ContMDiff (𝓡 4) 𝓘(ℝ, EuclideanPlane) ∞ torusTubularCircle2Raw :=
      (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.contMDiff.comp hpi2
    have hc1 : ContMDiff (𝓡 4) (𝓡 1) ∞
        (Set.codRestrict torusTubularCircle1Raw _ torusTubularCircle1Raw_mem_sphere) :=
      hraw1.codRestrict_sphere torusTubularCircle1Raw_mem_sphere
    have hc2 : ContMDiff (𝓡 4) (𝓡 1) ∞
        (Set.codRestrict torusTubularCircle2Raw _ torusTubularCircle2Raw_mem_sphere) :=
      hraw2.codRestrict_sphere torusTubularCircle2Raw_mem_sphere
    exact hfst.prodMk (Torus2.toProdDiffeomorph.symm.contMDiff.comp (hc1.prodMk hc2))
  contMDiff_invFun :=
    (TauCeti.ContMDiff.subtypeVal_comp_iff s4TorusTubularOpen _).mp contMDiff_s4TorusEmbed

private theorem s4ADKRaw_s4TorusEmbed_coord2_neg (wt : s4TorusDisk × Torus2) :
    s4ADKRaw (s4TorusEmbed wt).1 2 < 0 := by
  have hr1 := torusRad1Sq_pos wt.1.2
  have hu1 : wt.2.fst.1 0 ^ 2 + wt.2.fst.1 1 ^ 2 = 1 := by
    rw [← norm_sq_plane, mem_sphere_zero_iff_norm.mp wt.2.fst.2, one_pow]
  obtain ⟨-, hw0_hi, hw1_sq⟩ := s4TorusDisk_bounds wt.1.2
  have h2 : s4ADKRaw (s4TorusEmbed wt).1 2 = -1 / 4 + wt.1.1 0 + wt.1.1 1 ^ 2 := by
    dsimp only [s4TorusEmbed, s4TorusEmbedRaw]
    simp only [s4ADKRaw_two, vec5_zero, vec5_one]
    calc
      1 / 4 - ((Real.sqrt (1 / 2 - wt.1.1 0 - wt.1.1 1 ^ 2) * wt.2.fst.1 0) ^ 2 +
          (Real.sqrt (1 / 2 - wt.1.1 0 - wt.1.1 1 ^ 2) * wt.2.fst.1 1) ^ 2)
        = 1 / 4 - Real.sqrt (1 / 2 - wt.1.1 0 - wt.1.1 1 ^ 2) ^ 2 *
            (wt.2.fst.1 0 ^ 2 + wt.2.fst.1 1 ^ 2) := by ring
      _ = -1 / 4 + wt.1.1 0 + wt.1.1 1 ^ 2 := by rw [Real.sq_sqrt hr1.le, hu1]; ring
  linarith

private theorem s4ADKFibration_s4TorusEmbed_ne_northPole (wt : s4TorusDisk × Torus2) :
    s4ADKFibration (s4TorusEmbed wt) ≠ s2NorthPole := by
  intro h
  have hc := congrArg (fun z : Sphere2 ↦ z.1 2) h
  rw [coe_s4ADKFibration, PiLp.smul_apply, smul_eq_mul] at hc
  have hneg :
      ‖s4ADKRaw (s4TorusEmbed wt).1‖⁻¹ * s4ADKRaw (s4TorusEmbed wt).1 2 < 0 :=
    mul_neg_of_pos_of_neg (inv_pos.mpr (norm_s4ADKRaw_pos _))
      (s4ADKRaw_s4TorusEmbed_coord2_neg wt)
  have hnp : s2NorthPole.1 2 = 1 := rfl
  linarith

/-- South-hemisphere stereographic base coordinate map for `s4ADKFibration`. -/
noncomputable def g_adk_south (wt : s4TorusDisk × Torus2) : EuclideanPlane :=
  northPoleStereoChart (s4ADKFibration (s4TorusEmbed wt))

private theorem contMDiff_g_adk_south :
    ContMDiff ((𝓡 2).prod (𝓡 2)) (𝓡 2) ∞ g_adk_south := by
  let hpunct : s4TorusDisk × Torus2 → s2PuncturedSouth := fun wt ↦
    ⟨s2Antipodal (s4ADKFibration (s4TorusEmbed wt)),
      s2Antipodal_ne_southPole_of_ne_northPole (s4ADKFibration_s4TorusEmbed_ne_northPole wt)⟩
  have hhpunct : ContMDiff ((𝓡 2).prod (𝓡 2)) (𝓡 2) ∞ hpunct :=
    (TauCeti.ContMDiff.subtypeVal_comp_iff s2PuncturedSouth _).mp
      (s2Antipodal.contMDiff.comp (contMDiff_s4ADKFibration.comp contMDiff_s4TorusEmbed))
  have heq : g_adk_south = ⇑southPoleStereoDiffeomorph.symm ∘ hpunct := rfl
  rw [heq]
  exact southPoleStereoDiffeomorph.symm.contMDiff.comp hhpunct

private theorem northPoleStereoInv_g_adk_south (wt : s4TorusDisk × Torus2) :
    northPoleStereoInv (g_adk_south wt) = s4ADKFibration (s4TorusEmbed wt) :=
  northPoleStereoInv_chart (s4ADKFibration_s4TorusEmbed_ne_northPole wt)

@[simp]
private theorem g_adk_south_zero_left (t : Torus2) :
    g_adk_south (s4TorusDiskZero, t) = 0 := by
  have hsp : s4ADKFibration (s4TorusEmbed (s4TorusDiskZero, t)) = s2SouthPole := by
    rw [s4ADKFibration_eq_southPole_iff]
    have hu1 : t.fst.1 0 ^ 2 + t.fst.1 1 ^ 2 = 1 := by
      rw [← norm_sq_plane, mem_sphere_zero_iff_norm.mp t.fst.2, one_pow]
    have hu2 : t.snd.1 0 ^ 2 + t.snd.1 1 ^ 2 = 1 := by
      rw [← norm_sq_plane, mem_sphere_zero_iff_norm.mp t.snd.2, one_pow]
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [s4TorusEmbed, s4TorusEmbedRaw]
      simp only [coe_s4TorusDiskZero, PiLp.zero_apply, vec5_zero, vec5_one, sub_zero,
        zero_pow (by decide : 2 ≠ 0)]
      calc
        (Real.sqrt (1 / 2) * t.fst.1 0) ^ 2 + (Real.sqrt (1 / 2) * t.fst.1 1) ^ 2
          = Real.sqrt (1 / 2) ^ 2 * (t.fst.1 0 ^ 2 + t.fst.1 1 ^ 2) := by ring
        _ = 1 / 2 := by rw [Real.sq_sqrt (by norm_num), hu1, mul_one]
    · dsimp only [s4TorusEmbed, s4TorusEmbedRaw]
      simp only [coe_s4TorusDiskZero, PiLp.zero_apply, vec5_two, vec5_three, add_zero]
      calc
        (Real.sqrt (1 / 2) * t.snd.1 0) ^ 2 + (Real.sqrt (1 / 2) * t.snd.1 1) ^ 2
          = Real.sqrt (1 / 2) ^ 2 * (t.snd.1 0 ^ 2 + t.snd.1 1 ^ 2) := by ring
        _ = 1 / 2 := by rw [Real.sq_sqrt (by norm_num), hu2, mul_one]
    · simp [s4TorusEmbed, s4TorusEmbedRaw]
  simp only [g_adk_south, hsp, ← northPoleStereoInv_zero, northPoleStereoChart_inv]

/-- Product local trivialization candidate `Ψ_adk_south (w, t) = (g_adk_south (w, t), t)`. -/
noncomputable def Ψ_adk_south (wt : s4TorusDisk × Torus2) :
    EuclideanPlane × Torus2 :=
  (g_adk_south wt, wt.2)

private theorem contMDiff_Ψ_adk_south :
    ContMDiff ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) ∞ Ψ_adk_south :=
  contMDiff_g_adk_south.prodMk contMDiff_snd

private theorem injOn_Ψ_adk_south_zeroSlice :
    Set.InjOn Ψ_adk_south (({s4TorusDiskZero} : Set s4TorusDisk) ×ˢ (Set.univ : Set Torus2)) := by
  rintro ⟨w₁, t₁⟩ ⟨hw₁, -⟩ ⟨w₂, t₂⟩ ⟨hw₂, -⟩ hEq
  rw [Set.mem_singleton_iff] at hw₁ hw₂
  have ht : t₁ = t₂ := congrArg Prod.snd hEq
  exact Prod.ext (hw₁.trans hw₂.symm) ht

private noncomputable def adkSouthGRaw (t : Torus2) (u : EuclideanPlane) : EuclideanPlane :=
  let r₁ := Real.sqrt (1 / 2 - u 0 - u 1 ^ 2)
  let r₂ := Real.sqrt (1 / 2 + u 0)
  let W :=
    s4ADKRaw (vec5 (r₁ * t.fst.1 0) (r₁ * t.fst.1 1) (r₂ * t.snd.1 0) (r₂ * t.snd.1 1) (u 1))
  vec2 (-2 * W 0 / (‖W‖ - W 2)) (-2 * W 1 / (‖W‖ - W 2))

private theorem g_adk_south_eq_adkSouthGRaw (w : s4TorusDisk) (t : Torus2) :
    g_adk_south (w, t) = adkSouthGRaw t w.1 := by
  let x := s4TorusEmbed (w, t)
  let W := s4ADKRaw x.1
  have hW_pos : 0 < ‖W‖ := norm_s4ADKRaw_pos x
  have hW2_neg : W 2 < 0 := s4ADKRaw_s4TorusEmbed_coord2_neg (w, t)
  have hden1 : 1 + -(‖W‖⁻¹ * W 2) ≠ 0 := by
    have : 0 < 1 - ‖W‖⁻¹ * W 2 := by
      have : ‖W‖⁻¹ * W 2 < 0 := mul_neg_of_pos_of_neg (inv_pos.mpr hW_pos) hW2_neg
      linarith
    linarith
  have hden2 : ‖W‖ - W 2 ≠ 0 := by linarith
  have hcomp (c : ℝ) :
      2 * -(‖W‖⁻¹ * c) / (1 + -(‖W‖⁻¹ * W 2)) = -2 * c / (‖W‖ - W 2) := by
    rw [div_eq_div_iff hden1 hden2]
    field_simp [hW_pos.ne']
    ring
  have hW_eq :
      s4ADKRaw
        (vec5 (Real.sqrt (1 / 2 - w.1 0 - w.1 1 ^ 2) * t.fst.1 0)
          (Real.sqrt (1 / 2 - w.1 0 - w.1 1 ^ 2) * t.fst.1 1)
          (Real.sqrt (1 / 2 + w.1 0) * t.snd.1 0)
          (Real.sqrt (1 / 2 + w.1 0) * t.snd.1 1) (w.1 1)) = W :=
    rfl
  refine ext_vec2 ?_ ?_
  · simp only [g_adk_south, northPoleStereoChart, southPoleStereoChart, coe_s2Antipodal,
      coe_s4ADKFibration, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul, vec2_zero, adkSouthGRaw]
    rw [hW_eq]
    exact hcomp (W 0)
  · simp only [g_adk_south, northPoleStereoChart, southPoleStereoChart, coe_s2Antipodal,
      coe_s4ADKFibration, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul, vec2_one, adkSouthGRaw]
    rw [hW_eq]
    exact hcomp (W 1)

private theorem hasFDerivAt_adkSouthGRaw_zero (t : Torus2) :
    let s₀ : ℝ := -4 * Real.sqrt (1 / 2)
    HasFDerivAt (adkSouthGRaw t)
      (clmVec2
        ((s₀ * t.fst.1 0) • euclidProj 0 - (s₀ * t.fst.1 1) • euclidProj 1)
        ((s₀ * t.fst.1 1) • euclidProj 0 + (s₀ * t.fst.1 0) • euclidProj 1)) 0 := by
  intro s₀
  let r₁ : EuclideanPlane → ℝ := fun u ↦ Real.sqrt (1 / 2 - u 0 - u 1 ^ 2)
  let r₂ : EuclideanPlane → ℝ := fun u ↦ Real.sqrt (1 / 2 + u 0)
  let W : EuclideanPlane → EuclideanSpace ℝ (Fin 3) := fun u ↦
    s4ADKRaw (vec5 (r₁ u * t.fst.1 0) (r₁ u * t.fst.1 1) (r₂ u * t.snd.1 0) (r₂ u * t.snd.1 1)
      (u 1))
  have hu (i : Fin 2) : DifferentiableAt ℝ (fun u : EuclideanPlane ↦ u i) 0 :=
    (euclidProj i).differentiableAt
  have hr1_diff : DifferentiableAt ℝ r₁ 0 :=
    (((differentiableAt_const _).sub (hu 0)).sub ((hu 1).pow 2)).sqrt (by norm_num)
  have hr2_diff : DifferentiableAt ℝ r₂ 0 :=
    ((differentiableAt_const _).add (hu 0)).sqrt (by norm_num)
  have hr1_0 : r₁ 0 = Real.sqrt (1 / 2) := by simp [r₁]
  have hu1 : t.fst.1 0 ^ 2 + t.fst.1 1 ^ 2 = 1 := by
    rw [← norm_sq_plane, mem_sphere_zero_iff_norm.mp t.fst.2, one_pow]
  have hu2 : t.snd.1 0 ^ 2 + t.snd.1 1 ^ 2 = 1 := by
    rw [← norm_sq_plane, mem_sphere_zero_iff_norm.mp t.snd.2, one_pow]
  have hball_nhds : s4TorusDisk.1 ∈ 𝓝 (0 : EuclideanPlane) :=
    Metric.ball_mem_nhds 0 s4TorusDiskRadius_pos
  have hW0_ev : (fun u ↦ W u 0) =ᶠ[𝓝 0]
      fun u ↦ r₁ u * (t.fst.1 0 * u 0 - t.fst.1 1 * u 1) := by
    filter_upwards [hball_nhds] with u hu_mem
    have hr2_pos := torusRad2Sq_pos hu_mem
    simp only [W, s4ADKRaw_zero, vec5_zero, vec5_one, vec5_two, vec5_three, vec5_four]
    have hA : (r₂ u * t.snd.1 0) ^ 2 + (r₂ u * t.snd.1 1) ^ 2 - 1 / 2 = u 0 := by
      calc
        (r₂ u * t.snd.1 0) ^ 2 + (r₂ u * t.snd.1 1) ^ 2 - 1 / 2
          = r₂ u ^ 2 * (t.snd.1 0 ^ 2 + t.snd.1 1 ^ 2) - 1 / 2 := by ring
        _ = u 0 := by dsimp [r₂]; rw [Real.sq_sqrt hr2_pos.le, hu2]; ring
    rw [hA]
    ring
  have hW1_ev : (fun u ↦ W u 1) =ᶠ[𝓝 0]
      fun u ↦ r₁ u * (t.fst.1 1 * u 0 + t.fst.1 0 * u 1) := by
    filter_upwards [hball_nhds] with u hu_mem
    have hr2_pos := torusRad2Sq_pos hu_mem
    simp only [W, s4ADKRaw_one, vec5_zero, vec5_one, vec5_two, vec5_three, vec5_four]
    have hA : (r₂ u * t.snd.1 0) ^ 2 + (r₂ u * t.snd.1 1) ^ 2 - 1 / 2 = u 0 := by
      calc
        (r₂ u * t.snd.1 0) ^ 2 + (r₂ u * t.snd.1 1) ^ 2 - 1 / 2
          = r₂ u ^ 2 * (t.snd.1 0 ^ 2 + t.snd.1 1 ^ 2) - 1 / 2 := by ring
        _ = u 0 := by dsimp [r₂]; rw [Real.sq_sqrt hr2_pos.le, hu2]; ring
    rw [hA]
    ring
  have hL0 : HasFDerivAt (fun u : EuclideanPlane ↦ t.fst.1 0 * u 0 - t.fst.1 1 * u 1)
      (t.fst.1 0 • euclidProj 0 - t.fst.1 1 • euclidProj 1) 0 :=
    ((euclidProj 0).hasFDerivAt.const_mul (t.fst.1 0)).sub
      ((euclidProj 1).hasFDerivAt.const_mul (t.fst.1 1))
  have hL1 : HasFDerivAt (fun u : EuclideanPlane ↦ t.fst.1 1 * u 0 + t.fst.1 0 * u 1)
      (t.fst.1 1 • euclidProj 0 + t.fst.1 0 • euclidProj 1) 0 :=
    ((euclidProj 0).hasFDerivAt.const_mul (t.fst.1 1)).add
      ((euclidProj 1).hasFDerivAt.const_mul (t.fst.1 0))
  have hW0 : HasFDerivAt (fun u ↦ W u 0)
      ((Real.sqrt (1 / 2) * t.fst.1 0) • euclidProj 0 -
        (Real.sqrt (1 / 2) * t.fst.1 1) • euclidProj 1) 0 := by
    refine ((hr1_diff.hasFDerivAt.mul hL0).congr_fderiv ?_).congr_of_eventuallyEq hW0_ev
    ext v
    simp only [hr1_0, PiLp.zero_apply, mul_zero, sub_self, zero_smul, add_zero,
      smul_apply, sub_apply, smul_eq_mul]
    ring
  have hW1 : HasFDerivAt (fun u ↦ W u 1)
      ((Real.sqrt (1 / 2) * t.fst.1 1) • euclidProj 0 +
        (Real.sqrt (1 / 2) * t.fst.1 0) • euclidProj 1) 0 := by
    refine ((hr1_diff.hasFDerivAt.mul hL1).congr_fderiv ?_).congr_of_eventuallyEq hW1_ev
    ext v
    simp only [hr1_0, PiLp.zero_apply, mul_zero, add_zero, zero_smul,
      smul_apply, add_apply, smul_eq_mul]
    ring
  have hW_0_val : W 0 = vec3 0 0 (-1 / 4) := by
    refine ext_vec3 ?_ ?_ ?_
    · simp only [W, r₂, s4ADKRaw_zero, PiLp.zero_apply, add_zero, vec5_zero, vec5_one, vec5_two,
        vec5_three, vec5_four]
      have hA0 : (Real.sqrt (1 / 2) * t.snd.1 0) ^ 2 +
          (Real.sqrt (1 / 2) * t.snd.1 1) ^ 2 - 1 / 2 = 0 := by
        calc
          (Real.sqrt (1 / 2) * t.snd.1 0) ^ 2 + (Real.sqrt (1 / 2) * t.snd.1 1) ^ 2 - 1 / 2
            = Real.sqrt (1 / 2) ^ 2 * (t.snd.1 0 ^ 2 + t.snd.1 1 ^ 2) - 1 / 2 := by ring
          _ = 0 := by rw [Real.sq_sqrt (by norm_num), hu2]; ring
      rw [hA0]; simp
    · simp only [W, r₂, s4ADKRaw_one, PiLp.zero_apply, add_zero, vec5_zero, vec5_one, vec5_two,
        vec5_three, vec5_four]
      have hA0 : (Real.sqrt (1 / 2) * t.snd.1 0) ^ 2 +
          (Real.sqrt (1 / 2) * t.snd.1 1) ^ 2 - 1 / 2 = 0 := by
        calc
          (Real.sqrt (1 / 2) * t.snd.1 0) ^ 2 + (Real.sqrt (1 / 2) * t.snd.1 1) ^ 2 - 1 / 2
            = Real.sqrt (1 / 2) ^ 2 * (t.snd.1 0 ^ 2 + t.snd.1 1 ^ 2) - 1 / 2 := by ring
          _ = 0 := by rw [Real.sq_sqrt (by norm_num), hu2]; ring
      rw [hA0]; simp
    · simp only [W, r₁, s4ADKRaw_two, PiLp.zero_apply, sub_zero, zero_pow (by decide : 2 ≠ 0),
        vec5_zero, vec5_one, vec3_two]
      calc
        1 / 4 - ((Real.sqrt (1 / 2) * t.fst.1 0) ^ 2 + (Real.sqrt (1 / 2) * t.fst.1 1) ^ 2)
          = 1 / 4 - Real.sqrt (1 / 2) ^ 2 * (t.fst.1 0 ^ 2 + t.fst.1 1 ^ 2) := by ring
        _ = -1 / 4 := by rw [Real.sq_sqrt (by norm_num), hu1]; ring
  have hW0_norm : ‖W 0‖ = 1 / 4 := by
    have hsq : ‖W 0‖ ^ 2 = (1 / 4) ^ 2 := by rw [hW_0_val, norm_sq_vec3]; norm_num
    nlinarith [norm_nonneg (W 0)]
  have hW_diff : DifferentiableAt ℝ W 0 := by
    have hpi : DifferentiableAt ℝ
        (fun u : EuclideanPlane ↦
          ![r₁ u * t.fst.1 0, r₁ u * t.fst.1 1, r₂ u * t.snd.1 0, r₂ u * t.snd.1 1, u 1]) 0 := by
      refine differentiableAt_pi.mpr fun i ↦ ?_
      fin_cases i
      · exact hr1_diff.mul_const _
      · exact hr1_diff.mul_const _
      · exact hr2_diff.mul_const _
      · exact hr2_diff.mul_const _
      · exact hu 1
    exact (contDiff_s4ADKRaw.contDiffAt.differentiableAt (by simp)).comp 0
      (((EuclideanSpace.equiv (Fin 5) ℝ).symm.differentiableAt).comp 0 hpi)
  have hW2_diff : DifferentiableAt ℝ (fun u ↦ W u 2) 0 :=
    ((euclidProj (2 : Fin 3)).differentiableAt).comp 0 hW_diff
  have hW0_ne : W 0 ≠ 0 := by
    rw [hW_0_val]
    intro h
    have hc := congrArg (fun q : EuclideanSpace ℝ (Fin 3) ↦ q 2) h
    simp at hc
  have hden_0 : ‖W 0‖ - W 0 2 = 1 / 2 := by
    rw [hW0_norm, hW_0_val, vec3_two]; norm_num
  have hden_inv_diff : DifferentiableAt ℝ (fun u ↦ (‖W u‖ - W u 2)⁻¹) 0 :=
    ((DifferentiableAt.norm ℝ hW_diff hW0_ne).sub hW2_diff).inv
      (by change ‖W 0‖ - W 0 2 ≠ 0; rw [hden_0]; norm_num)
  have hg0_eq :
      (fun u ↦ adkSouthGRaw t u 0) = fun u ↦ (-2 * W u 0) * (‖W u‖ - W u 2)⁻¹ :=
    funext fun u ↦ div_eq_mul_inv _ _
  have hg1_eq :
      (fun u ↦ adkSouthGRaw t u 1) = fun u ↦ (-2 * W u 1) * (‖W u‖ - W u 2)⁻¹ :=
    funext fun u ↦ div_eq_mul_inv _ _
  have hg0 : HasFDerivAt (fun u ↦ adkSouthGRaw t u 0)
      ((s₀ * t.fst.1 0) • euclidProj 0 - (s₀ * t.fst.1 1) • euclidProj 1) 0 := by
    rw [hg0_eq]
    have h00 : W 0 0 = 0 := by rw [hW_0_val]; rfl
    refine ((hW0.const_mul (-2)).mul hden_inv_diff.hasFDerivAt).congr_fderiv ?_
    ext v
    simp only [h00, mul_zero, zero_smul, hden_0, s₀, smul_apply, sub_apply, smul_eq_mul]
    norm_num
    ring
  have hg1 : HasFDerivAt (fun u ↦ adkSouthGRaw t u 1)
      ((s₀ * t.fst.1 1) • euclidProj 0 + (s₀ * t.fst.1 0) • euclidProj 1) 0 := by
    rw [hg1_eq]
    have h01 : W 0 1 = 0 := by rw [hW_0_val]; rfl
    refine ((hW1.const_mul (-2)).mul hden_inv_diff.hasFDerivAt).congr_fderiv ?_
    ext v
    simp only [h01, mul_zero, zero_smul, hden_0, s₀, smul_apply, add_apply, smul_eq_mul]
    norm_num
    ring
  exact hasFDerivAt_vec2 hg0 hg1

private theorem mfderiv_g_adk_south_zero_left_slice (t : Torus2)
    (u : TangentSpace (𝓡 2) s4TorusDiskZero) :
    let uE : EuclideanPlane := u
    let s₀ : ℝ := -4 * Real.sqrt (1 / 2)
    mfderiv (𝓡 2) (𝓡 2) (fun w : s4TorusDisk ↦ g_adk_south (w, t)) s4TorusDiskZero u =
      vec2 (s₀ * t.fst.1 0 * uE 0 - s₀ * t.fst.1 1 * uE 1)
        (s₀ * t.fst.1 1 * uE 0 + s₀ * t.fst.1 0 * uE 1) := by
  intro uE s₀
  have hcomp : (fun w : s4TorusDisk ↦ g_adk_south (w, t)) =
      adkSouthGRaw t ∘ (Subtype.val : s4TorusDisk → EuclideanPlane) :=
    funext fun w ↦ g_adk_south_eq_adkSouthGRaw w t
  have hdf := hasFDerivAt_adkSouthGRaw_zero t
  have hdf0 : DifferentiableAt ℝ (adkSouthGRaw t) s4TorusDiskZero.1 := by
    simpa only [coe_s4TorusDiskZero] using hdf.differentiableAt
  have hsub_at : MDifferentiableAt (𝓡 2) 𝓘(ℝ, EuclideanPlane)
      (Subtype.val : s4TorusDisk → EuclideanPlane) s4TorusDiskZero :=
    (contMDiff_subtype_val (n := ∞) s4TorusDiskZero).mdifferentiableAt (by simp)
  have h1 :
      mvfderiv (𝓡 2) (adkSouthGRaw t ∘ (Subtype.val : s4TorusDisk → EuclideanPlane))
          s4TorusDiskZero u =
        fderiv ℝ (adkSouthGRaw t) s4TorusDiskZero.1
          (mvfderiv (𝓡 2) (Subtype.val : s4TorusDisk → EuclideanPlane) s4TorusDiskZero u) :=
    TauCeti.mvfderiv_comp_apply_of_differentiableAt hdf0 hsub_at u
  have hsub_u :
      mvfderiv (𝓡 2) (Subtype.val : s4TorusDisk → EuclideanPlane) s4TorusDiskZero u = uE :=
    TauCeti.Manifold.mvfderiv_subtype_val_apply s4TorusDiskZero u
  have heq :
      mfderiv (𝓡 2) (𝓡 2) (fun w : s4TorusDisk ↦ g_adk_south (w, t)) s4TorusDiskZero u =
        mvfderiv (𝓡 2) (adkSouthGRaw t ∘ (Subtype.val : s4TorusDisk → EuclideanPlane))
          s4TorusDiskZero u := by
    rw [hcomp]; rfl
  rw [heq, h1, hsub_u, coe_s4TorusDiskZero, hdf.fderiv, clmVec2_apply]
  refine ext_vec2 ?_ ?_ <;> simp [s₀, sub_apply, add_apply, smul_apply, smul_eq_mul]

private theorem mfderiv_g_adk_south_zero_left (t : Torus2)
    (v : TangentSpace ((𝓡 2).prod (𝓡 2)) (s4TorusDiskZero, t)) :
    let v1 : EuclideanPlane := v.1
    let s₀ : ℝ := -4 * Real.sqrt (1 / 2)
    mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 2) g_adk_south (s4TorusDiskZero, t) v =
      vec2 (s₀ * t.fst.1 0 * v1 0 - s₀ * t.fst.1 1 * v1 1)
        (s₀ * t.fst.1 1 * v1 0 + s₀ * t.fst.1 0 * v1 1) := by
  have hg_diff : MDifferentiableAt ((𝓡 2).prod (𝓡 2)) (𝓡 2) g_adk_south (s4TorusDiskZero, t) :=
    (contMDiff_g_adk_south (s4TorusDiskZero, t)).mdifferentiableAt (by simp)
  have hsplit :
      mvfderiv ((𝓡 2).prod (𝓡 2)) g_adk_south (s4TorusDiskZero, t) v =
        mvfderiv (𝓡 2) (fun w : s4TorusDisk ↦ g_adk_south (w, t)) s4TorusDiskZero v.1 +
          mvfderiv (𝓡 2) (fun q : Torus2 ↦ g_adk_south (s4TorusDiskZero, q)) t v.2 :=
    hg_diff.mvfderiv_prod_eq_add_apply v
  have hconst_zero :
      mvfderiv (𝓡 2) (fun q : Torus2 ↦ g_adk_south (s4TorusDiskZero, q)) t v.2 = 0 := by
    have hfun : (fun q : Torus2 ↦ g_adk_south (s4TorusDiskZero, q)) =
        fun _ ↦ (0 : EuclideanPlane) :=
      funext fun q ↦ g_adk_south_zero_left q
    change mfderiv (𝓡 2) (𝓡 2) (fun q : Torus2 ↦ g_adk_south (s4TorusDiskZero, q)) t v.2 = 0
    rw [hfun, mfderiv_const]
    rfl
  change mvfderiv ((𝓡 2).prod (𝓡 2)) g_adk_south (s4TorusDiskZero, t) v = _
  rw [hsplit, hconst_zero, add_zero]
  exact mfderiv_g_adk_south_zero_left_slice t v.1

private theorem isLocalDiffeomorphAt_Ψ_adk_south_zero_left (t : Torus2) :
    IsLocalDiffeomorphAt ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) ∞
      Ψ_adk_south (s4TorusDiskZero, t) := by
  have hΨ_diff :
      MDifferentiableAt ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) Ψ_adk_south
        (s4TorusDiskZero, t) :=
    (contMDiff_Ψ_adk_south (s4TorusDiskZero, t)).mdifferentiableAt (by simp)
  have hinj :
      Function.Injective
        (mfderiv ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) Ψ_adk_south (s4TorusDiskZero, t)) := by
    intro v₁ v₂ hEq
    suffices v₁ - v₂ = 0 from sub_eq_zero.mp this
    set v := v₁ - v₂
    have hv :
        mfderiv ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) Ψ_adk_south (s4TorusDiskZero, t) v = 0 := by
      simp only [v, map_sub, hEq, sub_self]
    have hv_snd :
        mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 2) (Prod.snd ∘ Ψ_adk_south)
          (s4TorusDiskZero, t) v = 0 := by
      rw [mfderiv_comp _ mdifferentiableAt_snd hΨ_diff, ContinuousLinearMap.comp_apply, hv,
        map_zero]
    have hv2 : v.2 = 0 := by
      have h1 : mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 2) Prod.snd (s4TorusDiskZero, t) v = 0 := hv_snd
      rwa [mfderiv_snd] at h1
    have hv_fst :
        mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 2) (Prod.fst ∘ Ψ_adk_south)
          (s4TorusDiskZero, t) v = 0 := by
      rw [mfderiv_comp _ mdifferentiableAt_fst hΨ_diff, ContinuousLinearMap.comp_apply, hv,
        map_zero]
    have hg0 : mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 2) g_adk_south (s4TorusDiskZero, t) v = 0 :=
      hv_fst
    rw [mfderiv_g_adk_south_zero_left t v] at hg0
    let v1 : EuclideanPlane := v.1
    let s₀ : ℝ := -4 * Real.sqrt (1 / 2)
    have h0 : s₀ * t.fst.1 0 * v1 0 - s₀ * t.fst.1 1 * v1 1 = 0 :=
      congrArg (fun w : EuclideanPlane ↦ w 0) hg0
    have h1 : s₀ * t.fst.1 1 * v1 0 + s₀ * t.fst.1 0 * v1 1 = 0 :=
      congrArg (fun w : EuclideanPlane ↦ w 1) hg0
    have hu1 : t.fst.1 0 ^ 2 + t.fst.1 1 ^ 2 = 1 := by
      rw [← norm_sq_plane, mem_sphere_zero_iff_norm.mp t.fst.2, one_pow]
    have hs₀_ne : s₀ ≠ 0 :=
      mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr (by norm_num)).ne'
    have hs₀_sq_ne : s₀ ^ 2 ≠ 0 := pow_ne_zero 2 hs₀_ne
    have hx0_mul : s₀ ^ 2 * v1 0 = 0 := by
      have hlin : s₀ ^ 2 * (t.fst.1 0 ^ 2 + t.fst.1 1 ^ 2) * v1 0 = 0 := by
        linear_combination (s₀ * t.fst.1 0) * h0 + (s₀ * t.fst.1 1) * h1
      rwa [hu1, mul_one] at hlin
    have hx1_mul : s₀ ^ 2 * v1 1 = 0 := by
      have hlin : s₀ ^ 2 * (t.fst.1 0 ^ 2 + t.fst.1 1 ^ 2) * v1 1 = 0 := by
        linear_combination -(s₀ * t.fst.1 1) * h0 + (s₀ * t.fst.1 0) * h1
      rwa [hu1, mul_one] at hlin
    have hv1 : v.1 = 0 :=
      ext_vec2 ((mul_eq_zero.mp hx0_mul).resolve_left hs₀_sq_ne)
        ((mul_eq_zero.mp hx1_mul).resolve_left hs₀_sq_ne)
    exact Prod.ext hv1 hv2
  exact TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv contMDiff_Ψ_adk_south.contMDiffOn
    isOpen_univ (Set.mem_univ _) BoundarylessManifold.isInteriorPoint (by simp) hinj rfl

/-- Open neighborhood & base-radius data for the south-hemisphere $T^2$ ADK trivialization. -/
structure ADKTorusTrivData where
  /-- Open neighborhood of `{0} × Torus2` in `s4TorusDisk × Torus2`. -/
  U : Set (s4TorusDisk × Torus2)
  /-- Openness of `U`. -/
  hU_open : IsOpen U
  /-- Inclusion of `{0} × Torus2` into `U`. -/
  hK_sub : ({s4TorusDiskZero} : Set s4TorusDisk) ×ˢ (Set.univ : Set Torus2) ⊆ U
  /-- Injectivity of `Ψ_adk_south` on `U`. -/
  hU_inj : Set.InjOn Ψ_adk_south U
  /-- Local diffeomorphism property of `Ψ_adk_south` on `U`. -/
  hU_loc : IsLocalDiffeomorphOn ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) ∞ Ψ_adk_south U
  /-- Shrunk positive stereographic base radius `r > 0` around `s2SouthPole`. -/
  r : ℝ
  /-- Positivity `0 < r`. -/
  hr_pos : 0 < r
  /-- Image containment `ball 0 r × Torus2 ⊆ Ψ_adk_south '' U`. -/
  hr_sub_target :
    Metric.ball (0 : EuclideanPlane) r ×ˢ (Set.univ : Set Torus2) ⊆ Ψ_adk_south '' U
  /-- Preimage containment over `northPoleStereoInv '' ball 0 r`. -/
  hr_preimage_sub :
    ∀ x : Sphere4,
      s4ADKFibration x ∈ northPoleStereoInv '' Metric.ball (0 : EuclideanPlane) r →
        x ∈ s4TorusEmbed '' U

/-- Existence of an open trivialization neighborhood and shrunk regular base radius around
`s2SouthPole` for `s4ADKFibration`. -/
-- tier: T2
theorem exists_adkTorusTrivData : Nonempty ADKTorusTrivData := by
  let K : Set (s4TorusDisk × Torus2) :=
    ({s4TorusDiskZero} : Set s4TorusDisk) ×ˢ (Set.univ : Set Torus2)
  have hK_compact : IsCompact K := isCompact_singleton.prod isCompact_univ
  have hK_loc :
      ∀ wt ∈ K, IsLocalDiffeomorphAt ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) ∞ Ψ_adk_south wt := by
    rintro ⟨w, t⟩ ⟨hw, -⟩
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact isLocalDiffeomorphAt_Ψ_adk_south_zero_left t
  obtain ⟨U, hU_open, hK_U, hU_inj, hU_loc⟩ :=
    injOn_Ψ_adk_south_zeroSlice.exists_isOpen_superset_isLocalDiffeomorphOn hK_compact hK_loc
  have hU_img_open : IsOpen (Ψ_adk_south '' U) :=
    (hU_loc.isLocalHomeomorphOn).isOpen_image hU_open
  have h0_sub_img :
      ({0} : Set EuclideanPlane) ×ˢ (Set.univ : Set Torus2) ⊆ Ψ_adk_south '' U := by
    rintro ⟨w, t⟩ ⟨hw, -⟩
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact ⟨(s4TorusDiskZero, t), hK_U ⟨rfl, trivial⟩, Prod.ext (g_adk_south_zero_left t) rfl⟩
  obtain ⟨V, W, hV_open, _, h0_V, huniv_W, hVW_sub⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ hU_img_open h0_sub_img
  obtain ⟨r₁, hr₁_pos, hr₁_ball⟩ := Metric.isOpen_iff.mp hV_open 0 (h0_V rfl)
  have hr₁_sub :
      Metric.ball (0 : EuclideanPlane) r₁ ×ˢ (Set.univ : Set Torus2) ⊆ Ψ_adk_south '' U :=
    fun _ hp ↦ hVW_sub ⟨hr₁_ball hp.1, huniv_W trivial⟩
  have hU_s4_open : IsOpen (s4TorusEmbed '' U) := by
    have heq : s4TorusEmbed '' U =
        (Subtype.val : s4TorusTubularOpen → Sphere4) ''
          (s4TorusTubularTrivialization.symm '' U) := by
      ext x
      simp only [Set.mem_image]
      exact ⟨fun ⟨wt, hwt, hEq⟩ ↦ ⟨s4TorusTubularTrivialization.symm wt, ⟨wt, hwt, rfl⟩, hEq⟩,
        fun ⟨_, ⟨wt, hwt, rfl⟩, hEq⟩ ↦ ⟨wt, hwt, hEq⟩⟩
    rw [heq]
    exact s4TorusTubularOpen.2.isOpenEmbedding_subtypeVal.isOpenMap _
      (s4TorusTubularTrivialization.symm.toHomeomorph.isOpenMap _ hU_open)
  let C : Set Sphere4 := (s4TorusEmbed '' U)ᶜ
  have hfC_closed : IsClosed (s4ADKFibration '' C) :=
    (hU_s4_open.isClosed_compl.isCompact.image contMDiff_s4ADKFibration.continuous).isClosed
  have hsp_mem : s2SouthPole ∈ (s4ADKFibration '' C)ᶜ := by
    rintro ⟨x, hxC, hfx⟩
    obtain ⟨hr, hu, hv⟩ := (s4ADKFibration_eq_southPole_iff x).mp hfx
    let r2 : ℝ := Real.sqrt 2
    have hr2_sq : r2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    let t : Torus2 :=
      ⟨⟨vec2 (r2 * x.1 0) (r2 * x.1 1), mem_sphere_zero_iff_norm.mpr (by
        have hsq : ‖vec2 (r2 * x.1 0) (r2 * x.1 1)‖ ^ 2 = 1 := by
          rw [norm_sq_plane]; simp only [vec2_zero, vec2_one]
          calc
            (r2 * x.1 0) ^ 2 + (r2 * x.1 1) ^ 2 = r2 ^ 2 * (x.1 0 ^ 2 + x.1 1 ^ 2) := by ring
            _ = 1 := by rw [hr2_sq, hr]; norm_num
        nlinarith [norm_nonneg (vec2 (r2 * x.1 0) (r2 * x.1 1))])⟩,
      ⟨vec2 (r2 * x.1 2) (r2 * x.1 3), mem_sphere_zero_iff_norm.mpr (by
        have hsq : ‖vec2 (r2 * x.1 2) (r2 * x.1 3)‖ ^ 2 = 1 := by
          rw [norm_sq_plane]; simp only [vec2_zero, vec2_one]
          calc
            (r2 * x.1 2) ^ 2 + (r2 * x.1 3) ^ 2 = r2 ^ 2 * (x.1 2 ^ 2 + x.1 3 ^ 2) := by ring
            _ = 1 := by rw [hr2_sq, hu]; norm_num
        nlinarith [norm_nonneg (vec2 (r2 * x.1 2) (r2 * x.1 3))])⟩⟩
    have hx_eq : s4TorusEmbed (s4TorusDiskZero, t) = x := by
      have hs : Real.sqrt (1 / 2) * r2 = 1 := by
        dsimp only [r2]
        rw [← Real.sqrt_mul (by norm_num)]
        norm_num
      apply Subtype.ext
      refine ext_vec5 ?_ ?_ ?_ ?_ ?_
      · dsimp only [s4TorusEmbed, s4TorusEmbedRaw, t]
        simp only [coe_s4TorusDiskZero, PiLp.zero_apply, vec5_zero, vec2_zero, sub_zero,
          zero_pow (by decide : 2 ≠ 0)]
        linear_combination x.1 0 * hs
      · dsimp only [s4TorusEmbed, s4TorusEmbedRaw, t]
        simp only [coe_s4TorusDiskZero, PiLp.zero_apply, vec5_one, vec2_one, sub_zero,
          zero_pow (by decide : 2 ≠ 0)]
        linear_combination x.1 1 * hs
      · dsimp only [s4TorusEmbed, s4TorusEmbedRaw, t]
        simp only [coe_s4TorusDiskZero, PiLp.zero_apply, vec5_two, vec2_zero, add_zero]
        linear_combination x.1 2 * hs
      · dsimp only [s4TorusEmbed, s4TorusEmbedRaw, t]
        simp only [coe_s4TorusDiskZero, PiLp.zero_apply, vec5_three, vec2_one, add_zero]
        linear_combination x.1 3 * hs
      · dsimp only [s4TorusEmbed, s4TorusEmbedRaw]
        simp [hv]
    exact hxC ⟨(s4TorusDiskZero, t), hK_U ⟨rfl, trivial⟩, hx_eq⟩
  have hpre_open : IsOpen (northPoleStereoInv ⁻¹' (s4ADKFibration '' C)ᶜ) :=
    hfC_closed.isOpen_compl.preimage contMDiff_northPoleStereoInv.continuous
  have h0_mem_pre : (0 : EuclideanPlane) ∈ northPoleStereoInv ⁻¹' (s4ADKFibration '' C)ᶜ := by
    simpa [northPoleStereoInv_zero] using hsp_mem
  obtain ⟨r₂, hr₂_pos, hr₂_ball⟩ := Metric.isOpen_iff.mp hpre_open 0 h0_mem_pre
  let r := min r₁ r₂
  refine ⟨⟨U, hU_open, hK_U, hU_inj, hU_loc, r, lt_min hr₁_pos hr₂_pos,
    fun p hp ↦ hr₁_sub ⟨Metric.ball_subset_ball (min_le_left _ _) hp.1, hp.2⟩, ?_⟩⟩
  rintro x ⟨w, hw, hfx⟩
  by_contra hnot
  exact hr₂_ball (Metric.ball_subset_ball (min_le_right _ _) hw) ⟨x, hnot, hfx.symm⟩

/-- Chosen `ADKTorusTrivData` witness. -/
noncomputable def adkTorusTrivData : ADKTorusTrivData :=
  Classical.choice exists_adkTorusTrivData

/-- Positive stereographic base disk radius around `s2SouthPole`. -/
noncomputable def s4ADKTorusBaseDiskRadius : ℝ :=
  adkTorusTrivData.r

/-- Positivity `0 < s4ADKTorusBaseDiskRadius`. -/
theorem s4ADKTorusBaseDiskRadius_pos : 0 < s4ADKTorusBaseDiskRadius :=
  adkTorusTrivData.hr_pos

/-- Planar open coordinate disk `Metric.ball 0 s4ADKTorusBaseDiskRadius`. -/
noncomputable abbrev s4ADKTorusBaseDiskOpen : Opens EuclideanPlane :=
  ⟨Metric.ball (0 : EuclideanPlane) s4ADKTorusBaseDiskRadius, Metric.isOpen_ball⟩

/-- Nonempty open regular base disk `s4ADKTorusBaseRegion ⊂ Sphere2` containing `s2SouthPole`
in the $T^2$-fiber chamber of `s4ADKFibration`. -/
noncomputable def s4ADKTorusBaseRegion : Opens Sphere2 :=
  ⟨northPoleStereoInv '' Metric.ball (0 : EuclideanPlane) s4ADKTorusBaseDiskRadius,
    isOpenEmbedding_northPoleStereoInv.isOpenMap _ Metric.isOpen_ball⟩

/-- `s2SouthPole` lies in `s4ADKTorusBaseRegion`. -/
theorem s2SouthPole_mem_s4ADKTorusBaseRegion : s2SouthPole ∈ s4ADKTorusBaseRegion.1 :=
  ⟨0, Metric.mem_ball_self s4ADKTorusBaseDiskRadius_pos, northPoleStereoInv_zero⟩

/-- `s4ADKTorusBaseRegion` is nonempty. -/
theorem s4ADKTorusBaseRegion_nonempty : s4ADKTorusBaseRegion.1.Nonempty :=
  ⟨s2SouthPole, s2SouthPole_mem_s4ADKTorusBaseRegion⟩

/-- Smooth diffeomorphism `Metric.ball 0 s4ADKTorusBaseDiskRadius ≃ₘ s4ADKTorusBaseRegion`. -/
-- tier: T2
noncomputable def s4ADKTorusBaseDiskDiffeomorph :
    s4ADKTorusBaseDiskOpen ≃ₘ⟮𝓡 2, 𝓡 2⟯ s4ADKTorusBaseRegion where
  toFun w := ⟨northPoleStereoInv w.1, ⟨w.1, w.2, rfl⟩⟩
  invFun b := ⟨northPoleStereoChart b.1, by
    obtain ⟨w, hw, hw_eq⟩ := b.2
    rwa [← hw_eq, northPoleStereoChart_inv]⟩
  left_inv w := Subtype.ext (northPoleStereoChart_inv w.1)
  right_inv b := by
    obtain ⟨w, -, hw_eq⟩ := b.2
    apply Subtype.ext
    dsimp only
    rw [← hw_eq, northPoleStereoChart_inv]
  contMDiff_toFun :=
    (TauCeti.ContMDiff.subtypeVal_comp_iff s4ADKTorusBaseRegion _).mp
      (contMDiff_northPoleStereoInv.comp contMDiff_subtype_val)
  contMDiff_invFun := by
    have hne : ∀ b : s4ADKTorusBaseRegion, b.1 ≠ s2NorthPole := by
      rintro ⟨_, ⟨w, -, rfl⟩⟩
      exact northPoleStereoInv_ne_northPole w
    have hincl : ContMDiff (𝓡 2) (𝓡 2) ∞
        (fun b : s4ADKTorusBaseRegion ↦
          (⟨s2Antipodal b.1, s2Antipodal_ne_southPole_of_ne_northPole (hne b)⟩ :
            s2PuncturedSouth)) :=
      (TauCeti.ContMDiff.subtypeVal_comp_iff s2PuncturedSouth _).mp
        (s2Antipodal.contMDiff.comp contMDiff_subtype_val)
    exact (TauCeti.ContMDiff.subtypeVal_comp_iff s4ADKTorusBaseDiskOpen _).mp
      (southPoleStereoDiffeomorph.symm.contMDiff.comp hincl)

@[simp]
private theorem coe_s4ADKTorusBaseDiskDiffeomorph_symm (b : s4ADKTorusBaseRegion) :
    ((s4ADKTorusBaseDiskDiffeomorph.symm b : s4ADKTorusBaseDiskOpen) : EuclideanPlane) =
      northPoleStereoChart b.1 :=
  rfl

/-- Open preimage `s4ADKFibration ⁻¹' s4ADKTorusBaseRegion` in `Sphere4`. -/
noncomputable abbrev s4ADKTorusPreimageOpen : Opens Sphere4 :=
  ⟨s4ADKFibration ⁻¹' s4ADKTorusBaseRegion.1,
    s4ADKTorusBaseRegion.2.preimage contMDiff_s4ADKFibration.continuous⟩

/-- Containment `s4ADKTorusPreimageOpen ⊆ s4TorusTubularOpen`. -/
theorem s4ADKTorusPreimageOpen_mem_tubular {x : Sphere4}
    (hx : x ∈ s4ADKTorusPreimageOpen.1) : x ∈ s4TorusTubularOpen.1 := by
  obtain ⟨wt, -, rfl⟩ := adkTorusTrivData.hr_preimage_sub x hx
  exact s4TorusEmbed_mem_tubularOpen wt

/-- Canonical inclusion of `s4ADKTorusPreimageOpen` into `s4TorusDisk × Torus2`. -/
noncomputable def s4ADKTorusIncl (u : s4ADKTorusPreimageOpen) :
    s4TorusDisk × Torus2 :=
  s4TorusTubularTrivialization ⟨u.1, s4ADKTorusPreimageOpen_mem_tubular u.2⟩

private theorem s4TorusEmbed_s4ADKTorusIncl (u : s4ADKTorusPreimageOpen) :
    s4TorusEmbed (s4ADKTorusIncl u) = u.1 := by
  change (s4TorusTubularTrivialization.symm
    (s4TorusTubularTrivialization ⟨u.1, s4ADKTorusPreimageOpen_mem_tubular u.2⟩)).1 = u.1
  rw [s4TorusTubularTrivialization.symm_apply_apply]

private theorem s4ADKTorusIncl_mem_U (u : s4ADKTorusPreimageOpen) :
    s4ADKTorusIncl u ∈ adkTorusTrivData.U := by
  obtain ⟨wt, hwt, hEq⟩ := adkTorusTrivData.hr_preimage_sub u.1 u.2
  have hwt_triv : s4ADKTorusIncl u = wt := by
    have h1 : (⟨u.1, s4ADKTorusPreimageOpen_mem_tubular u.2⟩ : s4TorusTubularOpen) =
        s4TorusTubularTrivialization.symm wt :=
      Subtype.ext hEq.symm
    change s4TorusTubularTrivialization ⟨u.1, s4ADKTorusPreimageOpen_mem_tubular u.2⟩ = wt
    rw [h1, s4TorusTubularTrivialization.apply_symm_apply]
  rwa [hwt_triv]

private theorem contMDiff_s4ADKTorusIncl :
    ContMDiff (𝓡 4) ((𝓡 2).prod (𝓡 2)) ∞ s4ADKTorusIncl :=
  s4TorusTubularTrivialization.contMDiff.comp
    ((TauCeti.ContMDiff.subtypeVal_comp_iff s4TorusTubularOpen _).mp contMDiff_subtype_val)

private theorem isLocalDiffeomorph_s4ADKTorusIncl :
    IsLocalDiffeomorph (𝓡 4) ((𝓡 2).prod (𝓡 2)) ∞ s4ADKTorusIncl := by
  intro u
  let subMap : s4ADKTorusPreimageOpen → s4TorusTubularOpen :=
    fun v ↦ ⟨v.1, s4ADKTorusPreimageOpen_mem_tubular v.2⟩
  have hsub_loc : IsLocalDiffeomorphAt (𝓡 4) (𝓡 4) ∞ subMap u := by
    have hcomp : ((Subtype.val : s4TorusTubularOpen → Sphere4) ∘ subMap) =
        (Subtype.val : s4ADKTorusPreimageOpen → Sphere4) := rfl
    have hval1 : IsLocalDiffeomorphAt (𝓡 4) (𝓡 4) ∞
        (Subtype.val : s4ADKTorusPreimageOpen → Sphere4) u :=
      TauCeti.isLocalDiffeomorph_subtype_val u
    have hval2 : IsLocalDiffeomorphAt (𝓡 4) (𝓡 4) ∞
        (Subtype.val : s4TorusTubularOpen → Sphere4) (subMap u) :=
      TauCeti.isLocalDiffeomorph_subtype_val (subMap u)
    rw [← hcomp] at hval1
    exact hval1.of_comp_left hval2 ((continuous_subtype_val.subtype_mk _).continuousAt)
  exact hsub_loc.comp (hg := s4TorusTubularTrivialization.isLocalDiffeomorph (subMap u))

/-- Forward south-hemisphere trivialization map `s4ADKTorusPreimageOpen → s4ADKTorusBaseRegion ×
Torus2`. -/
noncomputable def s4ADKTorusTrivFun (u : s4ADKTorusPreimageOpen) :
    s4ADKTorusBaseRegion × Torus2 :=
  (⟨s4ADKFibration u.1, u.2⟩, (s4ADKTorusIncl u).2)

private theorem contMDiff_s4ADKTorusTrivFun :
    ContMDiff (𝓡 4) ((𝓡 2).prod (𝓡 2)) ∞ s4ADKTorusTrivFun :=
  ((TauCeti.ContMDiff.subtypeVal_comp_iff s4ADKTorusBaseRegion _).mp
      (contMDiff_s4ADKFibration.comp contMDiff_subtype_val)).prodMk
    (contMDiff_snd.comp contMDiff_s4ADKTorusIncl)

/-- Bijectivity of `s4ADKTorusTrivFun`. -/
theorem bijective_s4ADKTorusTrivFun : Function.Bijective s4ADKTorusTrivFun := by
  constructor
  · intro u₁ u₂ hEq
    have hf : s4ADKFibration u₁.1 = s4ADKFibration u₂.1 :=
      congrArg (fun p : s4ADKTorusBaseRegion × Torus2 ↦ p.1.1) hEq
    have ht : (s4ADKTorusIncl u₁).2 = (s4ADKTorusIncl u₂).2 :=
      congrArg (Prod.snd : s4ADKTorusBaseRegion × Torus2 → Torus2) hEq
    have hg : g_adk_south (s4ADKTorusIncl u₁) = g_adk_south (s4ADKTorusIncl u₂) := by
      apply injective_northPoleStereoInv
      rw [northPoleStereoInv_g_adk_south, northPoleStereoInv_g_adk_south,
        s4TorusEmbed_s4ADKTorusIncl, s4TorusEmbed_s4ADKTorusIncl, hf]
    have hincl : s4ADKTorusIncl u₁ = s4ADKTorusIncl u₂ :=
      adkTorusTrivData.hU_inj (s4ADKTorusIncl_mem_U u₁) (s4ADKTorusIncl_mem_U u₂)
        (Prod.ext hg ht)
    exact Subtype.ext <| calc
      u₁.1 = s4TorusEmbed (s4ADKTorusIncl u₁) := (s4TorusEmbed_s4ADKTorusIncl u₁).symm
      _ = s4TorusEmbed (s4ADKTorusIncl u₂) := congrArg s4TorusEmbed hincl
      _ = u₂.1 := s4TorusEmbed_s4ADKTorusIncl u₂
  · rintro ⟨⟨b, hb⟩, t⟩
    obtain ⟨w₀, hw₀, rfl⟩ := hb
    obtain ⟨wt, _, hΨ⟩ :=
      adkTorusTrivData.hr_sub_target (Set.mk_mem_prod hw₀ (Set.mem_univ t))
    have hg : g_adk_south wt = w₀ := congrArg Prod.fst hΨ
    have ht : wt.2 = t := congrArg Prod.snd hΨ
    let x := s4TorusEmbed wt
    have hx_pre : x ∈ s4ADKTorusPreimageOpen.1 := by
      change s4ADKFibration (s4TorusEmbed wt) ∈ s4ADKTorusBaseRegion.1
      rw [← northPoleStereoInv_g_adk_south wt, hg]
      exact ⟨w₀, hw₀, rfl⟩
    let u : s4ADKTorusPreimageOpen := ⟨x, hx_pre⟩
    have hu_incl : s4ADKTorusIncl u = wt := by
      have h1 : (⟨u.1, s4ADKTorusPreimageOpen_mem_tubular u.2⟩ : s4TorusTubularOpen) =
          s4TorusTubularTrivialization.symm wt := rfl
      change s4TorusTubularTrivialization ⟨u.1, s4ADKTorusPreimageOpen_mem_tubular u.2⟩ = wt
      rw [h1, s4TorusTubularTrivialization.apply_symm_apply]
    refine ⟨u, Prod.ext (Subtype.ext ?_) ?_⟩
    · change s4ADKFibration (s4TorusEmbed wt) = northPoleStereoInv w₀
      rw [← northPoleStereoInv_g_adk_south wt, hg]
    · dsimp only [s4ADKTorusTrivFun]
      rw [hu_incl, ht]

/-- Local diffeomorphism property of `s4ADKTorusTrivFun`. -/
-- tier: T2
theorem isLocalDiffeomorph_s4ADKTorusTrivFun :
    IsLocalDiffeomorph (𝓡 4) ((𝓡 2).prod (𝓡 2)) ∞ s4ADKTorusTrivFun := by
  let Φ₀ : s4ADKTorusBaseRegion × Torus2 → EuclideanPlane × Torus2 :=
    fun bt ↦ ((s4ADKTorusBaseDiskDiffeomorph.symm bt.1).1, bt.2)
  have hΦ₀_comp : Φ₀ ∘ s4ADKTorusTrivFun = Ψ_adk_south ∘ s4ADKTorusIncl := by
    funext u
    dsimp only [Function.comp_apply, Φ₀, s4ADKTorusTrivFun, Ψ_adk_south]
    refine Prod.ext ?_ rfl
    rw [coe_s4ADKTorusBaseDiskDiffeomorph_symm]
    change northPoleStereoChart (s4ADKFibration u.1) = g_adk_south (s4ADKTorusIncl u)
    rw [← s4TorusEmbed_s4ADKTorusIncl u]
    rfl
  have hΦ₀_loc :
      ∀ bt : s4ADKTorusBaseRegion × Torus2,
        IsLocalDiffeomorphAt ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) ∞ Φ₀ bt := by
    intro bt
    let d := s4ADKTorusBaseDiskDiffeomorph.symm.prodCongr (Diffeomorph.refl (𝓡 2) Torus2 ∞)
    let j : s4ADKTorusBaseDiskOpen × Torus2 → EuclideanPlane × Torus2 :=
      fun q ↦ (q.1.1, q.2)
    have hΦ₀_eq : Φ₀ = j ∘ ⇑d := rfl
    have hj_loc :
        IsLocalDiffeomorphAt ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) ∞ j (d bt) :=
      (TauCeti.isLocalDiffeomorph_subtype_val (I := 𝓡 2) (n := ∞) (d bt).1).prodMap
        ((Diffeomorph.refl (𝓡 2) Torus2 ∞).isLocalDiffeomorph (d bt).2)
    rw [hΦ₀_eq]
    exact (d.isLocalDiffeomorph bt).comp (hg := hj_loc)
  intro u
  have hΨu :
      IsLocalDiffeomorphAt ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) ∞
        Ψ_adk_south (s4ADKTorusIncl u) :=
    adkTorusTrivData.hU_loc ⟨s4ADKTorusIncl u, s4ADKTorusIncl_mem_U u⟩
  have hcomp_loc : IsLocalDiffeomorphAt (𝓡 4) ((𝓡 2).prod (𝓡 2)) ∞
      (Φ₀ ∘ s4ADKTorusTrivFun) u := by
    rw [hΦ₀_comp]
    exact (isLocalDiffeomorph_s4ADKTorusIncl u).comp (hg := hΨu)
  exact hcomp_loc.of_comp_left (hΦ₀_loc (s4ADKTorusTrivFun u))
    ((contMDiff_s4ADKTorusTrivFun u).continuousAt)

/-- Explicit smooth south-hemisphere trivialization
`s4ADKFibration ⁻¹' s4ADKTorusBaseRegion ≃ₘ s4ADKTorusBaseRegion × Torus2`. -/
-- tier: T2
noncomputable def s4ADKTorusTrivialization :
    s4ADKTorusPreimageOpen ≃ₘ⟮𝓡 4, (𝓡 2).prod (𝓡 2)⟯ (s4ADKTorusBaseRegion × Torus2) :=
  isLocalDiffeomorph_s4ADKTorusTrivFun.diffeomorphOfBijective bijective_s4ADKTorusTrivFun

/-- First-factor projection law `(s4ADKTorusTrivialization u).1 = ⟨s4ADKFibration u.1, u.2⟩`. -/
@[simp]
theorem s4ADKTorusTrivialization_fst (u : s4ADKTorusPreimageOpen) :
    (s4ADKTorusTrivialization u).1 = ⟨s4ADKFibration u.1, u.2⟩ := by
  rw [s4ADKTorusTrivialization, IsLocalDiffeomorph.coe_diffeomorphOfBijective]
  rfl

/-- Every point of `s4ADKFibration ⁻¹' s4ADKTorusBaseRegion` is a regular point of
`s4ADKFibration`. -/
-- tier: T2
theorem regular_on_s4ADKTorusBaseRegion :
    ∀ x ∈ s4ADKFibration ⁻¹' s4ADKTorusBaseRegion.1,
      Function.Surjective (mfderiv (𝓡 4) (𝓡 2) s4ADKFibration x) := by
  intro x hx
  let p' : s4ADKTorusPreimageOpen := ⟨x, hx⟩
  have hcomp_eq :
      s4ADKFibration ∘ (Subtype.val : s4ADKTorusPreimageOpen → Sphere4) =
        (Subtype.val : s4ADKTorusBaseRegion → Sphere2) ∘
          (Prod.fst ∘ ⇑s4ADKTorusTrivialization) :=
    funext fun q ↦ (congrArg Subtype.val (s4ADKTorusTrivialization_fst q)).symm
  have hf_at : MDifferentiableAt (𝓡 4) (𝓡 2) s4ADKFibration x :=
    (contMDiff_s4ADKFibration x).mdifferentiableAt (by simp)
  have hsub_in : MDifferentiableAt (𝓡 4) (𝓡 4)
      (Subtype.val : s4ADKTorusPreimageOpen → Sphere4) p' :=
    (TauCeti.isLocalDiffeomorph_subtype_val (I := 𝓡 4) (n := ∞)
      p').contMDiffAt.mdifferentiableAt (by simp)
  have htriv_at : MDifferentiableAt (𝓡 4) ((𝓡 2).prod (𝓡 2))
      (⇑s4ADKTorusTrivialization) p' :=
    (s4ADKTorusTrivialization.contMDiff p').mdifferentiableAt (by simp)
  have hfst_at : MDifferentiableAt ((𝓡 2).prod (𝓡 2)) (𝓡 2)
      (Prod.fst : s4ADKTorusBaseRegion × Torus2 → s4ADKTorusBaseRegion)
      (s4ADKTorusTrivialization p') :=
    ((contMDiff_fst (n := ∞)) (s4ADKTorusTrivialization p')).mdifferentiableAt (by simp)
  have hsub_out : MDifferentiableAt (𝓡 2) (𝓡 2)
      (Subtype.val : s4ADKTorusBaseRegion → Sphere2) (s4ADKTorusTrivialization p').1 :=
    (TauCeti.isLocalDiffeomorph_subtype_val (I := 𝓡 2) (n := ∞)
      (s4ADKTorusTrivialization p').1).contMDiffAt.mdifferentiableAt (by simp)
  have hlhs_comp := mfderiv_comp p' hf_at hsub_in
  have hrhs_comp :
      mfderiv (𝓡 4) (𝓡 2)
          ((Subtype.val : s4ADKTorusBaseRegion → Sphere2) ∘
            (Prod.fst ∘ ⇑s4ADKTorusTrivialization)) p' =
        (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : s4ADKTorusBaseRegion → Sphere2)
            (s4ADKTorusTrivialization p').1).comp
          ((mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 2)
              (Prod.fst : s4ADKTorusBaseRegion × Torus2 → s4ADKTorusBaseRegion)
              (s4ADKTorusTrivialization p')).comp
            (mfderiv (𝓡 4) ((𝓡 2).prod (𝓡 2)) (⇑s4ADKTorusTrivialization) p')) := by
    rw [mfderiv_comp p' hsub_out (hfst_at.comp p' htriv_at),
      mfderiv_comp p' hfst_at htriv_at]
    rfl
  have hsurj_triv : Function.Surjective
      (mfderiv (𝓡 4) ((𝓡 2).prod (𝓡 2)) (⇑s4ADKTorusTrivialization) p') :=
    (s4ADKTorusTrivialization.isLocalDiffeomorph p').isInvertible_mfderiv (by simp) |>.surjective
  have hsurj_fst : Function.Surjective
      (mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 2)
        (Prod.fst : s4ADKTorusBaseRegion × Torus2 → s4ADKTorusBaseRegion)
        (s4ADKTorusTrivialization p')) := fun v ↦ by
    rw [mfderiv_fst]; exact ⟨(v, 0), rfl⟩
  have hsurj_sub_out : Function.Surjective
      (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : s4ADKTorusBaseRegion → Sphere2)
        (s4ADKTorusTrivialization p').1) :=
    (TauCeti.isLocalDiffeomorph_subtype_val (I := 𝓡 2) (n := ∞)
      (s4ADKTorusTrivialization p').1).isInvertible_mfderiv (by simp) |>.surjective
  have hsurj_rhs : Function.Surjective
      (mfderiv (𝓡 4) (𝓡 2)
        ((Subtype.val : s4ADKTorusBaseRegion → Sphere2) ∘
          (Prod.fst ∘ ⇑s4ADKTorusTrivialization)) p') := by
    rw [hrhs_comp]
    exact hsurj_sub_out.comp (hsurj_fst.comp hsurj_triv)
  rw [← hcomp_eq, hlhs_comp] at hsurj_rhs
  exact Function.Surjective.of_comp hsurj_rhs

/-- Global ADK fibration `s4ADKFibration` packaged as a `RegularDiskFibration` over the
south-hemisphere $T^2$ chamber `s4ADKTorusBaseRegion` (`s2SouthPole ∈ s4ADKTorusBaseRegion`). -/
noncomputable def s4ADKTorusRegularDiskFibration :
    RegularDiskFibration (𝓡 4) Sphere4 (𝓡 2) Sphere2 Torus2 where
  toFun := s4ADKFibration
  contMDiff_toFun := contMDiff_s4ADKFibration
  baseRegion := s4ADKTorusBaseRegion
  baseRegion_nonempty := s4ADKTorusBaseRegion_nonempty
  regular_on_preimage := regular_on_s4ADKTorusBaseRegion
  baseDiskRadius := s4ADKTorusBaseDiskRadius
  baseDiskRadius_pos := s4ADKTorusBaseDiskRadius_pos
  baseDisk := s4ADKTorusBaseDiskDiffeomorph
  trivialization := s4ADKTorusTrivialization
  trivialization_fst := s4ADKTorusTrivialization_fst

/-- **Global ADK Broken Lefschetz Fibration on $S^4$ ($T^2$ Chamber, `SC-R6b`)**:
Trivializes the south-hemisphere Clifford-torus chamber around `s2SouthPole` with smooth fiber
`Torus2`, complementing `s4BrokenLefschetzFibration` ($S^2$ chamber around `s2NorthPole`). -/
-- tier: T2
noncomputable def s4ADKTorusBrokenLefschetzFibration :
    BrokenLefschetzFibration (𝓡 4) Sphere4 (𝓡 2) Sphere2 Torus2 where
  toRegularDiskFibration := s4ADKTorusRegularDiskFibration
  singularities_broken_lefschetz _ hp := Or.inr (isIndefiniteFoldAt_s4ADKFibration hp)

/-- Named `[AdmitsWrinkledOrBrokenLefschetzFibration Sphere4]` witness constructed from the global
ADK broken Lefschetz fibration `s4BrokenLefschetzFibration`. Not marked as a global `instance`
so `instAdmitsRegularDiskFibrationSphere4` remains unique in downstream modules. -/
-- tier: T2
@[instance_reducible]
noncomputable def s4ADKAdmits : AdmitsWrinkledOrBrokenLefschetzFibration Sphere4 :=
  AdmitsWrinkledOrBrokenLefschetzFibration.ofPurelyWrinkled S4PositiveVolumeForm Sphere2
    s4PurelyWrinkledFibration S2PositiveVolumeForm s4ADKTrivialization_pos_cooriented

/-- **ADK Broken Lefschetz Turing Completeness on $S^4$ (Option A)**:
Constructs on `Sphere4` an aligned positive volume 4-form `V`, a generically rank-`2` unimodular
Jacobian–Poisson structure `π_f` adapted to the global ADK broken Lefschetz fibration
`s4ADKFibration : Sphere4 → Sphere2` (with nonempty equatorial indefinite-fold critical circle),
and a smooth diffeomorphism `d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4` preserving `s4ADKFibration`,
`π_f`, regular $S^2$ leaf areas, `V.Ω`, and `V.μ` that satisfies `IsTuringComplete` (`≠ id`). -/
-- tier: T2
theorem exists_turingComplete_volumePreserving_poissonDiffeomorph_S4_ADK :
    ∃ (V : PositiveVolumeForm (𝓡 4) Sphere4)
      (π_f : PoissonStructure (𝓡 4) Sphere4)
      (d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4),
      π_f = jacobianPoissonOfPositiveVolume V S2VolumeForm s4ADKFibration
        contMDiff_s4ADKFibration ∧
      π_f.IsUnimodularWithVolume V.Ω ∧
      π_f.IsUnimodularPoisson ∧
      π_f.IsGenericallyRankTwo ∧
      (∀ x ∉ criticalPoints (𝓡 4) (𝓡 2) s4ADKFibration, π_f.rankAt x = 2) ∧
      (criticalPoints (𝓡 4) (𝓡 2) s4ADKFibration).Nonempty ∧
      (∀ x ∈ criticalPoints (𝓡 4) (𝓡 2) s4ADKFibration, π_f.rankAt x = 0) ∧
      s4ADKFibration ∘ ⇑d_bar = s4ADKFibration ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_bar d_bar.contMDiff ∧
      (∀ b : s4ADKBaseRegion,
        ∃ d_b : Sphere2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere2,
          (∀ z : Sphere2,
            d_bar (s4ADKRegularDiskFibration.embed (b, z)) =
              s4ADKRegularDiskFibration.embed (b, d_b z)) ∧
          TauCeti.SmoothForm.mpullback d_b d_b.contMDiff S2VolumeForm = S2VolumeForm ∧
          MeasurePreserving ⇑d_b S2PositiveVolumeForm.μ S2PositiveVolumeForm.μ) ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasurePreserving ⇑d_bar V.μ V.μ ∧
      IsTuringComplete ⇑d_bar ∧
      (⇑d_bar : Sphere4 → Sphere4) ≠ id ∧
      V.μ = TauCeti.RoughForm.measure V.Ω.1 := by
  obtain ⟨V, π_f, d_bar, hπ, hunimV, hunim, hgen, hrank2, hrank0, hfib, hpois, hleaf, hvol,
      hmeas, htc, hne, hμ_eq⟩ :=
    Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_fourManifold
      (A := s4ADKAdmits) Sphere4
  exact ⟨V, π_f, d_bar, hπ, hunimV, hunim, hgen, hrank2,
    ⟨s4ADKCritBase, s4ADKCritBase_mem_criticalPoints⟩,
    hrank0, hfib, hpois, hleaf, hvol, hmeas, htc, hne, hμ_eq⟩

/-- **ADK Poisson–Hamiltonian Realization on $S^4$ (Option A)**:
Exhibits a finite list `Hs : List C^∞⟮𝓡 4, Sphere4; ℝ⟯` of smooth Hamiltonians whose composed
time-`1` Poisson–Hamiltonian flow on `Sphere4` (adapted to `s4ADKAdmits`)
preserves `s4ADKFibration`, `Ω`, `μ`, and the generically rank-`2` unimodular Poisson structure
`π_f`, and is Turing complete (`IsTuringComplete`, `≠ id`). -/
-- tier: T2
theorem exists_poisson_hamiltonian_realization_S4_ADK :
    ∃ (V : PositiveVolumeForm (𝓡 4) Sphere4)
      (π_f : PoissonStructure (𝓡 4) Sphere4)
      (Hs : List C^∞⟮𝓡 4, Sphere4; ℝ⟯)
      (d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4),
      π_f.IsUnimodularWithVolume V.Ω ∧
      π_f.IsGenericallyRankTwo ∧
      d_bar = composePoissonHamiltonianTimeOneFlows
        (A := s4ADKAdmits.toAdmitsRegularDiskFibration) Sphere4 Hs ∧
      s4ADKFibration ∘ ⇑d_bar = s4ADKFibration ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_bar d_bar.contMDiff ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasurePreserving ⇑d_bar V.μ V.μ ∧
      IsTuringComplete ⇑d_bar ∧
      (⇑d_bar : Sphere4 → Sphere4) ≠ id ∧
      V.μ = TauCeti.RoughForm.measure V.Ω.1 := by
  obtain ⟨Hs, d_bar, hcomp, hfib, hpois, hvol, hmeas, htc, hne⟩ :=
    exists_poisson_hamiltonian_realization_fourManifold
      (A := s4ADKAdmits.toAdmitsRegularDiskFibration) Sphere4
  exact ⟨alignedPositiveVolume (A := s4ADKAdmits.toAdmitsRegularDiskFibration) Sphere4,
    adaptedJacobianPoisson (A := s4ADKAdmits.toAdmitsRegularDiskFibration) Sphere4,
    Hs, d_bar,
    isUnimodularWithVolume_adaptedJacobianPoisson
      (A := s4ADKAdmits.toAdmitsRegularDiskFibration) Sphere4,
    isGenericallyRankTwo_adaptedJacobianPoisson (A := s4ADKAdmits) Sphere4,
    hcomp, hfib, hpois, hvol, hmeas, htc, hne, rfl⟩

/-- **ADK Algorithmic Undecidability of Forward-Orbit Reachability on $S^4$ (`SC-R4`)**:
Exhibits on `Sphere4` an aligned positive volume 4-form `V`
(`V.μ = TauCeti.RoughForm.measure V.Ω.1`), a **generically rank-2** unimodular Jacobian–Poisson
structure `π_f` adapted to `s4ADKFibration`, a smooth leaf-preserving Poisson diffeomorphism
`d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4`, an open-tube chart
`openChart : Param × UnitDisk2 → Sphere4`, a `Computable` dyadic rational approximation `approx`,
and a `Computable` rational-box enumerator `targetBoxes : ℕ → RatBox2` generating `U` inside
`openChart` such that forward-orbit reachability into `U` is recursively enumerable (`REPred`) yet
algorithmically undecidable (`¬ ComputablePred`). -/
-- tier: T2
theorem undecidable_orbit_reachability_S4_ADK :
    ∃ (V : PositiveVolumeForm (𝓡 4) Sphere4)
      (π_f : PoissonStructure (𝓡 4) Sphere4)
      (d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4)
      (U : Opens Sphere4)
      (Param : Type) (instTopParam : TopologicalSpace Param) (param₀ : Param)
      (openChart : Param × UnitDisk2 → Sphere4)
      (chart : UnitDisk2 → Sphere4)
      (coord : Nat.Partrec.Code → UnitDisk2)
      (approx : Nat.Partrec.Code × ℕ → RatFrac × RatFrac)
      (targetBoxes : ℕ → RatBox2),
      s4ADKFibration ∘ ⇑d_bar = s4ADKFibration ∧
      π_f.IsUnimodularWithVolume V.Ω ∧
      π_f.IsGenericallyRankTwo ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_bar d_bar.contMDiff ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasurePreserving ⇑d_bar V.μ V.μ ∧
      U.1.Nonempty ∧
      @Topology.IsOpenEmbedding _ _ (@instTopologicalSpaceProd _ _ instTopParam _) _
        openChart ∧
      (∀ y : UnitDisk2, chart y = openChart (param₀, y)) ∧
      Continuous chart ∧
      Function.Injective chart ∧
      Computable approx ∧
      (∀ (c : Nat.Partrec.Code) (m : ℕ),
        ‖ratFracPairToEuclidean2 (approx (c, m)) - (coord c).1‖ ≤ (1 / 2 : ℝ) ^ m) ∧
      Computable targetBoxes ∧
      (∀ j : ℕ, (evalRatBox2 (targetBoxes j)).1.Nonempty) ∧
      U.1 = openChart '' (Set.univ ×ˢ ⋃ j : ℕ, (evalRatBox2 (targetBoxes j)).1) ∧
      (∀ c : Nat.Partrec.Code, chart (coord c) ∉ U) ∧
      REPred (fun c : Nat.Partrec.Code ↦ ∃ n : ℕ, (⇑d_bar)^[n] (chart (coord c)) ∈ U) ∧
      ¬ ComputablePred (fun c : Nat.Partrec.Code ↦
          ∃ n : ℕ, (⇑d_bar)^[n] (chart (coord c)) ∈ U) ∧
      (¬ ∃ dec : Nat.Partrec.Code → Bool,
          Computable dec ∧
          ∀ c : Nat.Partrec.Code,
            dec c = true ↔ ∃ n : ℕ, (⇑d_bar)^[n] (chart (coord c)) ∈ U) ∧
      V.μ = TauCeti.RoughForm.measure V.Ω.1 := by
  let _ : AdmitsWrinkledOrBrokenLefschetzFibration Sphere4 := s4ADKAdmits
  obtain ⟨U, Param, instTopParam, param₀, openChart, chart, coord, approx, targetBoxes, hU,
      hopen, hchart_eq, hcont, hinj, hcomp, hbound, hcomp_boxes, hbox_ne, hU_eq, hnot0, hre,
      hnotcomp, hnodec⟩ :=
    undecidable_orbit_reachability_leafwiseBumpDiffeomorph
      (A := s4ADKAdmits.toAdmitsRegularDiskFibration) Sphere4
  exact ⟨alignedPositiveVolume (A := s4ADKAdmits.toAdmitsRegularDiskFibration) Sphere4,
    adaptedJacobianPoisson (A := s4ADKAdmits.toAdmitsRegularDiskFibration) Sphere4,
    leafwiseBumpDiffeomorph (A := s4ADKAdmits.toAdmitsRegularDiskFibration) Sphere4,
    U, Param, instTopParam, param₀, openChart, chart, coord, approx, targetBoxes,
    fibration_comp_leafwiseBumpDiffeomorph
      (A := s4ADKAdmits.toAdmitsRegularDiskFibration) Sphere4,
    isUnimodularWithVolume_adaptedJacobianPoisson
      (A := s4ADKAdmits.toAdmitsRegularDiskFibration) Sphere4,
    isGenericallyRankTwo_adaptedJacobianPoisson (A := s4ADKAdmits) Sphere4,
    isPoissonMap_leafwiseBumpDiffeomorph
      (A := s4ADKAdmits.toAdmitsRegularDiskFibration) Sphere4,
    mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm
      (A := s4ADKAdmits.toAdmitsRegularDiskFibration) Sphere4,
    measurePreserving_leafwiseBumpDiffeomorph
      (A := s4ADKAdmits.toAdmitsRegularDiskFibration) Sphere4,
    hU, hopen, hchart_eq, hcont, hinj, hcomp, hbound, hcomp_boxes, hbox_ne, hU_eq, hnot0, hre,
    hnotcomp, hnodec, rfl⟩

/-- **Exact Round-Volume ADK Poisson–Hamiltonian Realization on $S^4$ (`SC-R3`)**:
Conjugates the ADK Poisson–Hamiltonian flow on `Sphere4` by the global Moser diffeomorphism `W.ψ`
so that `B_exact := s4BrokenLefschetzFibration.compDiffeomorph W.ψ` is a global broken Lefschetz
fibration on `Sphere4` with nonempty critical locus, `π_f` is a **generically rank-2** Poisson
structure unimodular with the **exact standard round volume form `S4PositiveVolumeForm.Ω`**, and
`d_exact` is a finite composition of time-`1` Hamiltonian flows of `π_f` preserving `B_exact.toFun`,
`π_f`, **`S4PositiveVolumeForm.Ω`**, and **`S4PositiveVolumeForm.μ`** (`IsTuringComplete ⇑d_exact`,
`≠ id`). -/
-- tier: T2
theorem exists_exactVolumePreserving_poisson_hamiltonian_realization_S4_ADK :
    ∃ (B_exact : BrokenLefschetzFibration (𝓡 4) Sphere4 (𝓡 2) Sphere2 Sphere2)
      (π_f : PoissonStructure (𝓡 4) Sphere4)
      (Hs : List C^∞⟮𝓡 4, Sphere4; ℝ⟯)
      (d_exact : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4),
      (criticalPoints (𝓡 4) (𝓡 2) B_exact.toFun).Nonempty ∧
      π_f.IsUnimodularWithVolume S4PositiveVolumeForm.Ω ∧
      π_f.IsGenericallyRankTwo ∧
      d_exact = composePoissonStructureTimeOneFlows Sphere4 π_f Hs ∧
      B_exact.toFun ∘ ⇑d_exact = B_exact.toFun ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_exact d_exact.contMDiff ∧
      TauCeti.SmoothForm.mpullback d_exact d_exact.contMDiff S4PositiveVolumeForm.Ω =
        S4PositiveVolumeForm.Ω ∧
      MeasurePreserving ⇑d_exact S4PositiveVolumeForm.μ S4PositiveVolumeForm.μ ∧
      IsTuringComplete ⇑d_exact ∧
      (⇑d_exact : Sphere4 → Sphere4) ≠ id ∧
      S4PositiveVolumeForm.μ = TauCeti.RoughForm.measure S4PositiveVolumeForm.Ω.1 := by
  let A_reg : AdmitsRegularDiskFibration Sphere4 := s4ADKAdmits.toAdmitsRegularDiskFibration
  let W : MoserVolume S4PositiveVolumeForm (alignedPositiveVolume (A := A_reg) Sphere4) :=
    MoserVolume.ofPositivelyCooriented S4PositiveVolumeForm
      (alignedPositiveVolume (A := A_reg) Sphere4)
      (fun x ↦ alignedVolumeForm_pos_cooriented (A := A_reg) Sphere4 x)
  let C_cmpp : HasCMPPCantorCirculationHamiltonians := universalReversibleSimulator_cmpp
  let _ : HasTuringCompleteAreaPreservingDiskIsotopy :=
    @instHasTuringCompleteAreaPreservingDiskIsotopyOfCMPP C_cmpp
  let Hs₀ : List C^∞⟮𝓡 4, Sphere4; ℝ⟯ :=
    C_cmpp.generators.map (liftPlanarHamiltonianTo4Manifold (A := A_reg) Sphere4)
  let Hs : List C^∞⟮𝓡 4, Sphere4; ℝ⟯ := Hs₀.map fun h ↦ h.comp ⟨W.ψ, W.ψ.contMDiff⟩
  have hcomp₀ :
      leafwiseBumpDiffeomorph (A := A_reg) Sphere4 =
        composePoissonStructureTimeOneFlows Sphere4
          (adaptedJacobianPoisson (A := A_reg) Sphere4) Hs₀ := by
    rw [composePoissonStructureTimeOneFlows_adaptedJacobianPoisson (A := A_reg)]
    exact (composePoissonHamiltonianTimeOneFlows_map_liftPlanarHamiltonian_eq (A := A_reg) Sphere4
      C_cmpp.r₀_mem_Ioo universalReversibleSimulator_cmpp_isAutonomous).symm
  have hcomp :
      W.conjDiffeomorph (leafwiseBumpDiffeomorph (A := A_reg) Sphere4) =
        composePoissonStructureTimeOneFlows Sphere4
          (W.pullbackJacobianPoisson s4ADKFibration contMDiff_s4ADKFibration) Hs := by
    rw [W.composePoissonStructureTimeOneFlows_map_comp s4ADKFibration contMDiff_s4ADKFibration Hs₀,
      show jacobianPoissonOfPositiveVolume (alignedPositiveVolume (A := A_reg) Sphere4)
          S2VolumeForm s4ADKFibration contMDiff_s4ADKFibration =
        adaptedJacobianPoisson (A := A_reg) Sphere4 from rfl,
      ← hcomp₀]
  have hcrit_ne :
      (criticalPoints (𝓡 4) (𝓡 2)
        (s4BrokenLefschetzFibration.compDiffeomorph W.ψ).toFun).Nonempty :=
    ⟨W.ψ.symm s4ADKCritBase,
      (W.mem_criticalPoints_comp_ψ_iff s4ADKFibration contMDiff_s4ADKFibration _).mpr
        (by rw [W.ψ.apply_symm_apply]; exact s4ADKCritBase_mem_criticalPoints)⟩
  exact ⟨s4BrokenLefschetzFibration.compDiffeomorph W.ψ,
    W.pullbackJacobianPoisson s4ADKFibration contMDiff_s4ADKFibration, Hs,
    W.conjDiffeomorph (leafwiseBumpDiffeomorph (A := A_reg) Sphere4),
    hcrit_ne,
    W.isUnimodularWithVolume_pullbackJacobianPoisson s4ADKFibration contMDiff_s4ADKFibration,
    (W.isGenericallyRankTwo_pullbackJacobianPoisson_iff s4ADKFibration
      contMDiff_s4ADKFibration).mpr
      (isGenericallyRankTwo_adaptedJacobianPoisson (A := s4ADKAdmits) Sphere4),
    hcomp,
    W.fibration_comp_conjDiffeomorph
      (fibration_comp_leafwiseBumpDiffeomorph (A := A_reg) Sphere4),
    W.isPoissonMap_conjDiffeomorph s4ADKFibration contMDiff_s4ADKFibration
      (isPoissonMap_leafwiseBumpDiffeomorph (A := A_reg) Sphere4),
    W.mpullback_conjDiffeomorph (connectedComponent_leafwiseBumpDiffeomorph (A := A_reg) Sphere4)
      (mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm (A := A_reg) Sphere4),
    W.measurePreserving_conjDiffeomorph
      (connectedComponent_leafwiseBumpDiffeomorph (A := A_reg) Sphere4)
      (mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm (A := A_reg) Sphere4),
    W.isTuringComplete_conjDiffeomorph
      (isTuringComplete_leafwiseBumpDiffeomorph (A := A_reg) Sphere4),
    W.conjDiffeomorph_ne_id (isTuringComplete_leafwiseBumpDiffeomorph (A := A_reg) Sphere4),
    rfl⟩

namespace Main

/-- **ADK Broken Lefschetz Theorem 1 on $S^4$ Preserving Exact Round Volume `S4PositiveVolumeForm`
(`SC-R3`, Full Poisson Bundle)**:
Moser conjugation on `Sphere4` produces a global `BrokenLefschetzFibration` `B_exact`
(`s4BrokenLefschetzFibration.compDiffeomorph W.ψ`) with nonempty critical locus, a **generically
rank-2** Poisson structure `π_f` unimodular with **`S4PositiveVolumeForm.Ω` itself**, and a
$C^\infty$ Turing complete Poisson diffeomorphism `d_exact` preserving `B_exact.toFun`,
**`S4PositiveVolumeForm.Ω`**, and **`S4PositiveVolumeForm.μ`**. -/
-- tier: T2
theorem exists_turingComplete_exactVolumePreserving_poissonDiffeomorph_S4_ADK :
    ∃ (B_exact : BrokenLefschetzFibration (𝓡 4) Sphere4 (𝓡 2) Sphere2 Sphere2)
      (π_f : PoissonStructure (𝓡 4) Sphere4)
      (d_exact : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4),
      (criticalPoints (𝓡 4) (𝓡 2) B_exact.toFun).Nonempty ∧
      π_f.IsUnimodularWithVolume S4PositiveVolumeForm.Ω ∧
      π_f.IsUnimodularPoisson ∧
      π_f.IsGenericallyRankTwo ∧
      (∀ x ∉ criticalPoints (𝓡 4) (𝓡 2) B_exact.toFun, π_f.rankAt x = 2) ∧
      (∀ x ∈ criticalPoints (𝓡 4) (𝓡 2) B_exact.toFun, π_f.rankAt x = 0) ∧
      B_exact.toFun ∘ ⇑d_exact = B_exact.toFun ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_exact d_exact.contMDiff ∧
      TauCeti.SmoothForm.mpullback d_exact d_exact.contMDiff S4PositiveVolumeForm.Ω =
        S4PositiveVolumeForm.Ω ∧
      MeasurePreserving ⇑d_exact S4PositiveVolumeForm.μ S4PositiveVolumeForm.μ ∧
      IsTuringComplete ⇑d_exact ∧
      (⇑d_exact : Sphere4 → Sphere4) ≠ id ∧
      S4PositiveVolumeForm.μ = TauCeti.RoughForm.measure S4PositiveVolumeForm.Ω.1 := by
  let A_reg : AdmitsRegularDiskFibration Sphere4 := s4ADKAdmits.toAdmitsRegularDiskFibration
  let W : MoserVolume S4PositiveVolumeForm (alignedPositiveVolume (A := A_reg) Sphere4) :=
    MoserVolume.ofPositivelyCooriented S4PositiveVolumeForm
      (alignedPositiveVolume (A := A_reg) Sphere4)
      (fun x ↦ alignedVolumeForm_pos_cooriented (A := A_reg) Sphere4 x)
  have hcrit_ne :
      (criticalPoints (𝓡 4) (𝓡 2)
        (s4BrokenLefschetzFibration.compDiffeomorph W.ψ).toFun).Nonempty :=
    ⟨W.ψ.symm s4ADKCritBase,
      (W.mem_criticalPoints_comp_ψ_iff s4ADKFibration contMDiff_s4ADKFibration _).mpr
        (by rw [W.ψ.apply_symm_apply]; exact s4ADKCritBase_mem_criticalPoints)⟩
  exact ⟨s4BrokenLefschetzFibration.compDiffeomorph W.ψ,
    W.pullbackJacobianPoisson s4ADKFibration contMDiff_s4ADKFibration,
    W.conjDiffeomorph (leafwiseBumpDiffeomorph (A := A_reg) Sphere4),
    hcrit_ne,
    W.isUnimodularWithVolume_pullbackJacobianPoisson s4ADKFibration contMDiff_s4ADKFibration,
    W.isUnimodularPoisson_pullbackJacobianPoisson s4ADKFibration contMDiff_s4ADKFibration,
    (W.isGenericallyRankTwo_pullbackJacobianPoisson_iff s4ADKFibration
      contMDiff_s4ADKFibration).mpr
      (isGenericallyRankTwo_adaptedJacobianPoisson (A := s4ADKAdmits) Sphere4),
    fun x hx ↦
      W.rankAt_pullbackJacobianPoisson_of_notMem_criticalPoints s4ADKFibration
        contMDiff_s4ADKFibration hx,
    fun x hx ↦
      W.rankAt_pullbackJacobianPoisson_of_mem_criticalPoints s4ADKFibration
        contMDiff_s4ADKFibration hx,
    W.fibration_comp_conjDiffeomorph
      (fibration_comp_leafwiseBumpDiffeomorph (A := A_reg) Sphere4),
    W.isPoissonMap_conjDiffeomorph s4ADKFibration contMDiff_s4ADKFibration
      (isPoissonMap_leafwiseBumpDiffeomorph (A := A_reg) Sphere4),
    W.mpullback_conjDiffeomorph (connectedComponent_leafwiseBumpDiffeomorph (A := A_reg) Sphere4)
      (mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm (A := A_reg) Sphere4),
    W.measurePreserving_conjDiffeomorph
      (connectedComponent_leafwiseBumpDiffeomorph (A := A_reg) Sphere4)
      (mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm (A := A_reg) Sphere4),
    W.isTuringComplete_conjDiffeomorph
      (isTuringComplete_leafwiseBumpDiffeomorph (A := A_reg) Sphere4),
    W.conjDiffeomorph_ne_id (isTuringComplete_leafwiseBumpDiffeomorph (A := A_reg) Sphere4),
    rfl⟩

/-- **ADK Broken Lefschetz Theorem 1 on $S^4$ Preserving Exact Round Volume `S4PositiveVolumeForm`
(`SC-R3`, Concise Headline Statement)**:
There exists a $C^\infty$ Turing complete Poisson diffeomorphism `d_exact` on `Sphere4` preserving a
global broken Lefschetz fibration `B_exact` (with nonempty critical locus), a **generically rank-2**
Poisson structure `π_f` unimodular with **`S4PositiveVolumeForm.Ω`**, and the **exact standard round
volume form `S4PositiveVolumeForm.Ω` and Borel measure `S4PositiveVolumeForm.μ`**. -/
-- tier: T2
theorem exists_turingComplete_exactVolumePreserving_diffeomorph_S4_ADK :
    ∃ (B_exact : BrokenLefschetzFibration (𝓡 4) Sphere4 (𝓡 2) Sphere2 Sphere2)
      (π_f : PoissonStructure (𝓡 4) Sphere4)
      (d_exact : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4),
      (criticalPoints (𝓡 4) (𝓡 2) B_exact.toFun).Nonempty ∧
      π_f.IsUnimodularWithVolume S4PositiveVolumeForm.Ω ∧
      π_f.IsGenericallyRankTwo ∧
      B_exact.toFun ∘ ⇑d_exact = B_exact.toFun ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_exact d_exact.contMDiff ∧
      TauCeti.SmoothForm.mpullback d_exact d_exact.contMDiff S4PositiveVolumeForm.Ω =
        S4PositiveVolumeForm.Ω ∧
      MeasurePreserving ⇑d_exact S4PositiveVolumeForm.μ S4PositiveVolumeForm.μ ∧
      IsTuringComplete ⇑d_exact ∧
      (⇑d_exact : Sphere4 → Sphere4) ≠ id := by
  obtain ⟨B_exact, π_f, d_exact, hcrit, hunimV, _, hgen, _, _, hfib, hpoiss, hvol, hmp, htc, hne,
      _⟩ :=
    exists_turingComplete_exactVolumePreserving_poissonDiffeomorph_S4_ADK
  exact ⟨B_exact, π_f, d_exact, hcrit, hunimV, hgen, hfib, hpoiss, hvol, hmp, htc, hne⟩

end Main

end ADKTrivializationAndTheorems

end S4TuringPoisson

