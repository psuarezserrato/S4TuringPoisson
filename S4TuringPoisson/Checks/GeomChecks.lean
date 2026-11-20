/-
Copyright (c) 2026 Pablo Suárez-Serrato. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Suárez-Serrato
-/
module

public import S4TuringPoisson.Interfaces
public import TauCeti.Geometry.Symplectic.Manifold.Sphere

/-!
# Adversarial Geometry & Volume Verification Checks (`GeomChecks`)

This file implements the Milestone M0–M2 geometric verification gates from Section 6 of
`MISSION_DIRECTIVE.md`:

- **M0 Non-Zero Top-Form & Pullback Sanity**:
  - `planeAreaForm_zero_ne_zero` & `planeAreaForm_ne_zero_smoothForm`: confirms `planeAreaForm` on
    `ℝ²` is non-zero at `(0 : EuclideanPlane)` and globally as a `SmoothForm`.
  - `mpullback_double_planeAreaForm_ne`: confirms `SmoothForm.mpullback` rejects radial doubling
    `y ↦ (2 : ℝ) • y` (`det = 4 ≠ 1`), ruling out trivial pullback implementations.
  - `s2VolumeForm_eq_sphereAreaForm`: confirms `S2VolumeForm` equals `TauCeti.sphereAreaForm`.
- **Gate 5 (Nontrivial $S^4$ Volume Measure Witness)**:
  - `s4_volume_ball_half_pos` & `s4_volume_ball_half_lt_univ` (for every `p : Sphere4`) and concrete
    witness `gate5_s4_nontrivial_volume_witness` at `s4BasePoint : Sphere4`, ruling out zero,
    infinite, and Dirac measures on $S^4$.
-/

@[expose] public section

open MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff ENNReal Manifold Topology

namespace S4TuringPoisson.Checks

/-! ## 1. M0.1 & M0.3 Non-Zero Form and Pullback Discrimination Checks -/

/-- `planeAreaForm` evaluates to a non-zero alternating 2-form at `0 : EuclideanPlane`. -/
theorem planeAreaForm_zero_ne_zero : planeAreaForm.1 (0 : EuclideanPlane) ≠ 0 :=
  planeAreaForm_ne_zero (0 : EuclideanPlane)

/-- `planeAreaForm` is a non-zero element of `SmoothForm (𝓡 2) EuclideanPlane ℝ 2`. -/
theorem planeAreaForm_ne_zero_smoothForm : planeAreaForm ≠ 0 := by
  intro h
  exact planeAreaForm_zero_ne_zero (congrFun (congrArg Subtype.val h) 0)

/-- `planeAreaForm` evaluates to `1` on the standard basis at the origin of `ℝ²`. -/
theorem planeAreaForm_zero_basis_eq_one :
    planeAreaForm.1 (0 : EuclideanPlane)
      (fun i ↦ (EuclideanSpace.basisFun (Fin 2) ℝ i :
        TangentSpace (𝓡 2) (0 : EuclideanPlane))) = 1 :=
  planeAreaForm_apply_basisFun 0

/-- Radial doubling continuous linear map `y ↦ (2 : ℝ) • y` on `ℝ²`. -/
noncomputable def doublePlaneCLM : EuclideanPlane →L[ℝ] EuclideanPlane :=
  (2 : ℝ) • ContinuousLinearMap.id ℝ EuclideanPlane

/-- Radial doubling `doublePlaneCLM` on `ℝ²` does NOT preserve `planeAreaForm` (`det = 4 ≠ 1`),
confirming non-vacuity of `SmoothForm.mpullback` and
`mpullback_planeAreaForm_eq_iff_det_fderiv_eq_one`. -/
theorem mpullback_double_planeAreaForm_ne :
    TauCeti.SmoothForm.mpullback ⇑doublePlaneCLM
      doublePlaneCLM.contDiff.contMDiff planeAreaForm ≠ planeAreaForm := by
  intro heq
  have h0 := (mpullback_planeAreaForm_eq_iff_det_fderiv_eq_one doublePlaneCLM.contDiff).mp heq 0
  rw [ContinuousLinearMap.fderiv] at h0
  change LinearMap.det ((2 : ℝ) • LinearMap.id (R := ℝ) (M := EuclideanPlane)) = 1 at h0
  rw [LinearMap.det_smul, finrank_euclideanSpace_fin, LinearMap.det_id] at h0
  norm_num at h0

/-- `S2VolumeForm` in `Interfaces.lean` equals `TauCeti.sphereAreaForm` (via
`TauCeti.sphereAreaForm_eq_sphereVolumeForm`, as `sphereAreaForm` is opaque across `module`
boundaries without `@[expose]`). -/
theorem s2VolumeForm_eq_sphereAreaForm : S2VolumeForm = TauCeti.sphereAreaForm :=
  TauCeti.sphereAreaForm_eq_sphereVolumeForm.symm

/-! ## 2. Section 6 Gate 5: Nontrivial $S^4$ Volume Measure Witness -/

/-- Explicit concrete basepoint `(1, 0, 0, 0, 0) ∈ S⁴`. -/
noncomputable def s4BasePoint : Sphere4 :=
  ⟨EuclideanSpace.basisFun (Fin 5) ℝ 0,
    mem_sphere_zero_iff_norm.mpr ((EuclideanSpace.basisFun (Fin 5) ℝ).orthonormal.1 0)⟩

/-- `S4VolumeForm` is non-zero at `s4BasePoint`. -/
theorem s4VolumeForm_basePoint_ne_zero : S4VolumeForm.1 s4BasePoint ≠ 0 :=
  S4VolumeForm_ne_zero s4BasePoint

/-- Antipodal involution `p ↦ -p` on `Sphere4`. -/
def s4Antipode (p : Sphere4) : Sphere4 :=
  ⟨-p.1, by simp [mem_sphere_zero_iff_norm.mp p.2]⟩

/-- Ambient chordal distance between any `p : Sphere4` and its antipode `s4Antipode p` equals `2`. -/
theorem dist_s4Antipode (p : Sphere4) : dist p (s4Antipode p) = 2 := by
  have hp : ‖p.1‖ = 1 := mem_sphere_zero_iff_norm.mp p.2
  calc
    dist p (s4Antipode p) = dist p.1 (-p.1) := Subtype.dist_eq p (s4Antipode p)
    _ = ‖p.1 - -p.1‖ := dist_eq_norm p.1 (-p.1)
    _ = ‖(2 : ℝ) • p.1‖ := by rw [sub_neg_eq_add, ← two_smul ℝ p.1]
    _ = ‖(2 : ℝ)‖ * ‖p.1‖ := norm_smul (2 : ℝ) p.1
    _ = 2 := by rw [hp, Real.norm_ofNat, mul_one]

/-- Strict positivity `0 < μ_Ω (Metric.ball p (1 / 2))` on `Sphere4` for every `p : Sphere4`. -/
theorem s4_volume_ball_half_pos (p : Sphere4) :
    0 < S4PositiveVolumeForm.μ (Metric.ball p (1 / 2)) :=
  S4PositiveVolumeForm.measure_isOpen_pos Metric.isOpen_ball
    ⟨p, Metric.mem_ball_self (by norm_num)⟩

/-- Strict upper bound `μ_Ω (Metric.ball p (1 / 2)) < μ_Ω Set.univ` on `Sphere4` for every
`p : Sphere4`, ruling out Dirac and degenerate full-support measures. -/
theorem s4_volume_ball_half_lt_univ (p : Sphere4) :
    S4PositiveVolumeForm.μ (Metric.ball p (1 / 2)) < S4PositiveVolumeForm.μ Set.univ := by
  refine S4PositiveVolumeForm.measure_lt_univ_of_disjoint_isOpen
    (u := Metric.ball (s4Antipode p) (1 / 2)) Metric.isOpen_ball
    ⟨s4Antipode p, Metric.mem_ball_self (by norm_num)⟩ ?_
  exact Metric.ball_disjoint_ball (by rw [dist_s4Antipode p]; norm_num)

/-- **Section 6 Gate 5 Witness**: Concrete point `s4BasePoint : Sphere4` satisfying
`0 < μ_Ω (Metric.ball s4BasePoint (1 / 2)) < μ_Ω Set.univ` with finite total volume. -/
theorem gate5_s4_nontrivial_volume_witness :
    0 < S4PositiveVolumeForm.μ (Metric.ball s4BasePoint (1 / 2)) ∧
      S4PositiveVolumeForm.μ (Metric.ball s4BasePoint (1 / 2)) <
        S4PositiveVolumeForm.μ Set.univ ∧
      S4PositiveVolumeForm.μ Set.univ < ⊤ :=
  ⟨s4_volume_ball_half_pos s4BasePoint,
    s4_volume_ball_half_lt_univ s4BasePoint,
    measure_lt_top S4PositiveVolumeForm.μ Set.univ⟩

end S4TuringPoisson.Checks
