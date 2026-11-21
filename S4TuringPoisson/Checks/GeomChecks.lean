/-
Copyright (c) 2026 Pablo Suárez-Serrato. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Suárez-Serrato
-/
module

public import S4TuringPoisson.Interfaces
public import S4TuringPoisson.Poisson.BivectorAndModular
public import S4TuringPoisson.Poisson.JacobianPoisson
public import S4TuringPoisson.Poisson.SingularCircleNormalForm
public import S4TuringPoisson.Fibration.LocalSingularModels
public import S4TuringPoisson.Fibration.S4Fibration
public import S4TuringPoisson.Fibration.WrinkledGeneral4Manifold
public import TauCeti.Geometry.Symplectic.Manifold.Sphere

/-!
# Adversarial Geometry, Poisson, Fibration & Volume Verification Checks (`GeomChecks`)

This file implements the Milestone M0–M2 geometric verification gates from Section 6 of
`MISSION_DIRECTIVE.md` together with cross-track M1+M2 integration checks:

- **M0 Non-Zero Top-Form & Pullback Sanity**:
  - `planeAreaForm_zero_ne_zero` & `planeAreaForm_ne_zero_smoothForm`: confirms `planeAreaForm` on
    `ℝ²` is non-zero at `(0 : EuclideanPlane)` and globally as a `SmoothForm`.
  - `mpullback_double_planeAreaForm_ne`: confirms `SmoothForm.mpullback` rejects radial doubling
    `y ↦ (2 : ℝ) • y` (`det = 4 ≠ 1`), ruling out trivial pullback implementations.
  - `s2VolumeForm_eq_sphereAreaForm`: confirms `S2VolumeForm` equals `TauCeti.sphereAreaForm`.
- **Gate 3 (Non-Zero Jacobian–Poisson Bracket Witness)**:
  - `gate3_proj01_bracket_coord_two_three_eq_one` & `gate3_nonzero_poisson_bracket_witness`:
    instantiates `euclideanJacobianPoisson` on `(x₀, x₁, x₂, x₃) ↦ (x₀, x₁)` (`ℝ⁴ → ℝ²`) and proves
    `{x₂, x₃}_{π_f} = 1 ≠ 0` (i.e. `{x₃, x₄}_{π_f} = 1 ≠ 0` in 1-indexed coordinates), `rankAt = 2`,
    and Casimirs `x₀, x₁`, ruling out zero-bivector junk-value bugs.
- **Gate 4 (Singular-to-Regular Rank-2 Witness for Equation (2) & `indefiniteFoldMap`)**:
  - `gate4_eq2_singular_to_regular_witness` & `m1_m2_indefiniteFoldMap_gate4_witness`: instantiates
    Equation (2) / `LocalSingularModels.indefiniteFoldMap` on `ℝ⁴ → ℝ²` and proves for every `t : ℝ`
    that `(0, 0, 0, t) ∈ Crit` has `rankAt = 0`, while `(1, 0, 0, t) ∉ Crit` has `rankAt = 2` with
    `{y₂, y₃}_{π_f} = 2 ≠ 0` and global unimodularity across both loci.
- **M1.3 Singular-Circle Normal Form Witness**:
  - `m1_singular_circle_normal_form_witness`: concrete singular (`(0, 0, 0, 0)`, `rankAt = 0`) and
    regular (`(0, 1/2, 0, 0)`, `rankAt = 2`, `{x₂, x₃} = 1/2 ≠ 0`) witnesses on `S¹ × B³` together
    with free Poisson involution `normalInvolution`.
- **Gate 5 (Nontrivial $S^4$ Volume Measure Witness)**:
  - `s4_volume_ball_half_pos` & `s4_volume_ball_half_lt_univ` (for every `p : Sphere4`) and concrete
    witness `gate5_s4_nontrivial_volume_witness` at `s4BasePoint : Sphere4`, ruling out zero,
    infinite, and Dirac measures on $S^4$.
- **Cross-Track M1+M2 $S^4$ Jacobian–Poisson & $S^2$ Symplectic Isotopy Lift Witnesses**:
  - `m1_m2_s4Fibration_jacobianPoisson_witness`: instantiates `jacobianPoissonOfPositiveVolume` on
    `s4Fibration : Sphere4 → Sphere2`, proving global unimodularity, `rankAt = 0` on
    `s4CriticalPoint ∈ criticalPoints` (nonempty!), and `rankAt = 2` on
    `s4RegularPoint ∈ s4PreimageOpen` (nonempty!).
  - `m2_s2_liftSliceDiffeomorph_witness`: instantiates `liftSliceDiffeomorph` on `Sphere2` under
    `[HasTuringCompleteAreaPreservingDiskIsotopy]`, verifying area pullback preservation,
    `MeasurePreserving`, `IsTuringComplete`, and `≠ id`.
-/

@[expose] public section

open MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff ENNReal InnerProductSpace Manifold Topology

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

/-! ## 2. Section 6 Gate 3: Non-Zero Jacobian–Poisson Bracket Witness (`ℝ⁴ → ℝ²`) -/

/-- Coordinate projection `(x₀, x₁, x₂, x₃) ↦ (x₀, x₁)` on `ℝ⁴ → ℝ²` as a continuous linear map. -/
noncomputable def proj01CLM : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 4)).smulRight (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 4)).smulRight (EuclideanSpace.basisFun (Fin 2) ℝ 1)

@[simp]
theorem proj01CLM_apply_zero (x : EuclideanSpace ℝ (Fin 4)) : (proj01CLM x) 0 = x 0 := by
  simp [proj01CLM, EuclideanSpace.basisFun_apply]

@[simp]
theorem proj01CLM_apply_one (x : EuclideanSpace ℝ (Fin 4)) : (proj01CLM x) 1 = x 1 := by
  simp [proj01CLM, EuclideanSpace.basisFun_apply]

/-- Explicit tuple formula `proj01CLM x = (x₀, x₁)` matching Section 6 Gate 3. -/
theorem proj01CLM_eq_toLp (x : EuclideanSpace ℝ (Fin 4)) :
    proj01CLM x = WithLp.toLp 2 ![x 0, x 1] := by
  ext i
  fin_cases i <;> simp

/-- Pointwise evaluation `{x₂, x₃}_{π_f}(x) = 1` (i.e. `{x₃, x₄}_{π_f} = 1`) on `ℝ⁴`. -/
theorem gate3_proj01_bracket_coord_two_three_apply (x : EuclideanSpace ℝ (Fin 4)) :
    ((euclideanJacobianPoisson ⇑proj01CLM proj01CLM.contDiff).bracket
      (euclideanCoord 2) (euclideanCoord 3)) x = 1 := by
  rw [euclideanJacobianPoisson_bracket_coord_two_three, proj01CLM.fderiv]
  simp [EuclideanSpace.basisFun_apply]

/-- Global identity `{x₂, x₃}_{π_f} = 1` in `C^∞(ℝ⁴)` for `(x₀, x₁, x₂, x₃) ↦ (x₀, x₁)`. -/
theorem gate3_proj01_bracket_coord_two_three_eq_one :
    (euclideanJacobianPoisson ⇑proj01CLM proj01CLM.contDiff).bracket
      (euclideanCoord 2) (euclideanCoord 3) = 1 := by
  ext x
  exact gate3_proj01_bracket_coord_two_three_apply x

/-- `proj01CLM` has empty critical set (every point of `ℝ⁴` is regular). -/
theorem proj01CLM_notMem_criticalSet (x : EuclideanSpace ℝ (Fin 4)) :
    x ∉ criticalSet (𝓡 4) (𝓡 2) ⇑proj01CLM := by
  rw [mem_criticalSet_iff, mfderiv_eq_fderiv, not_not]
  change Function.Surjective (fderiv ℝ ⇑proj01CLM x)
  rw [proj01CLM.fderiv]
  intro w
  refine ⟨WithLp.toLp 2 ![w 0, w 1, 0, 0], ?_⟩
  ext i
  fin_cases i <;> simp

/-- **Section 6 Gate 3 Witness**: For `f(x₀, x₁, x₂, x₃) = (x₀, x₁)`, `{x₂, x₃}_{π_f} = 1 ≠ 0`,
`rankAt 0 = 2`, `x₀` and `x₁` are Casimirs, and `π_f` is globally unimodular. -/
theorem gate3_nonzero_poisson_bracket_witness :
    ((euclideanJacobianPoisson ⇑proj01CLM proj01CLM.contDiff).bracket
        (euclideanCoord 2) (euclideanCoord 3)) 0 = 1 ∧
      (euclideanJacobianPoisson ⇑proj01CLM proj01CLM.contDiff).bracket
        (euclideanCoord 2) (euclideanCoord 3) ≠ 0 ∧
      (euclideanJacobianPoisson ⇑proj01CLM proj01CLM.contDiff).rankAt 0 = 2 ∧
      (euclideanJacobianPoisson ⇑proj01CLM proj01CLM.contDiff).IsCasimir (euclideanCoord 0) ∧
      (euclideanJacobianPoisson ⇑proj01CLM proj01CLM.contDiff).IsCasimir (euclideanCoord 1) ∧
      (euclideanJacobianPoisson ⇑proj01CLM proj01CLM.contDiff).IsUnimodularWithVolume
        euclidean4VolumeForm := by
  refine ⟨gate3_proj01_bracket_coord_two_three_apply 0, ?_, ?_, ?_, ?_,
    isUnimodularWithVolume_euclideanJacobianPoisson ⇑proj01CLM proj01CLM.contDiff⟩
  · intro h0
    have h1 := gate3_proj01_bracket_coord_two_three_apply 0
    rw [h0, ContMDiffMap.coe_zero, Pi.zero_apply] at h1
    exact one_ne_zero h1.symm
  · exact rankAt_jacobianPoisson_of_notMem_criticalSet euclidean4VolumeForm
      euclidean4VolumeForm_ne_zero planeAreaForm ⇑proj01CLM proj01CLM.contDiff.contMDiff
      (proj01CLM_notMem_criticalSet 0) (planeAreaForm_ne_zero _)
  · have hcas := isCasimir_comp_jacobianPoisson euclidean4VolumeForm euclidean4VolumeForm_ne_zero
      planeAreaForm ⇑proj01CLM proj01CLM.contDiff.contMDiff (euclideanCoord 0)
    have heq : (euclideanCoord 0).comp ⟨⇑proj01CLM, proj01CLM.contDiff.contMDiff⟩ =
        euclideanCoord 0 := by
      ext x
      exact proj01CLM_apply_zero x
    rwa [heq] at hcas
  · have hcas := isCasimir_comp_jacobianPoisson euclidean4VolumeForm euclidean4VolumeForm_ne_zero
      planeAreaForm ⇑proj01CLM proj01CLM.contDiff.contMDiff (euclideanCoord 1)
    have heq : (euclideanCoord 1).comp ⟨⇑proj01CLM, proj01CLM.contDiff.contMDiff⟩ =
        euclideanCoord 1 := by
      ext x
      exact proj01CLM_apply_one x
    rwa [heq] at hcas

/-! ## 3. Section 6 Gate 4: Singular-to-Regular Rank-2 Witness for Equation (2) -/

/-- Indefinite quadratic component `y₀² - (y₁² + y₂²) / 2` of Equation (2). -/
noncomputable def eq2FoldFirst (y : EuclideanSpace ℝ (Fin 4)) : ℝ :=
  (y 0) ^ 2 - ((y 1) ^ 2 + (y 2) ^ 2) / 2

/-- Local indefinite fold map of Equation (2) (`S4TCdiffeo-Aug-2026.tex`):
`(y₀, y₁, y₂, t) ↦ (y₀² - (y₁² + y₂²) / 2, t)` on `ℝ⁴ → ℝ²`. -/
noncomputable def eq2FoldMap (y : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 2) :=
  eq2FoldFirst y • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
    y 3 • EuclideanSpace.basisFun (Fin 2) ℝ 1

/-- Explicit tuple identity `eq2FoldMap y = (y₀² - (y₁² + y₂²) / 2, y₃)`. -/
theorem eq2FoldMap_eq_toLp (y : EuclideanSpace ℝ (Fin 4)) :
    eq2FoldMap y = WithLp.toLp 2 ![(y 0) ^ 2 - ((y 1) ^ 2 + (y 2) ^ 2) / 2, y 3] := by
  ext i
  fin_cases i <;> simp [eq2FoldMap, eq2FoldFirst, EuclideanSpace.basisFun_apply]

/-- Smoothness (`C^∞`) of `eq2FoldFirst`. -/
theorem contDiff_eq2FoldFirst : ContDiff ℝ ∞ eq2FoldFirst := by
  have hp (i : Fin 4) : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin 4) ↦ y i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  exact ((hp 0).pow 2).sub ((((hp 1).pow 2).add ((hp 2).pow 2)).div_const 2)

/-- Smoothness (`C^∞`) of `eq2FoldMap`. -/
theorem contDiff_eq2FoldMap : ContDiff ℝ ∞ eq2FoldMap := by
  have hp3 : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin 4) ↦ y (3 : Fin 4)) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (3 : Fin 4)).contDiff
  exact (contDiff_eq2FoldFirst.smul contDiff_const).add (hp3.smul contDiff_const)

/-- Explicit continuous linear Fréchet derivative of `eq2FoldFirst` at `y ∈ ℝ⁴`. -/
noncomputable def eq2FoldFirstFDeriv (y : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ :=
  (2 * y 0) • EuclideanSpace.proj (𝕜 := ℝ) 0 -
    y 1 • EuclideanSpace.proj (𝕜 := ℝ) 1 -
    y 2 • EuclideanSpace.proj (𝕜 := ℝ) 2

/-- Explicit continuous linear Fréchet derivative of `eq2FoldMap` at `y ∈ ℝ⁴`. -/
noncomputable def eq2FoldFDeriv (y : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (eq2FoldFirstFDeriv y).smulRight (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
    (EuclideanSpace.proj (𝕜 := ℝ) (3 : Fin 4)).smulRight (EuclideanSpace.basisFun (Fin 2) ℝ 1)

theorem hasFDerivAt_eq2FoldFirst (y : EuclideanSpace ℝ (Fin 4)) :
    HasFDerivAt eq2FoldFirst (eq2FoldFirstFDeriv y) y := by
  let p (i : Fin 4) : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) i
  have hsq (i : Fin 4) :
      HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 4) ↦ (z i) ^ 2) ((2 * y i) • p i) y := by
    have hm := ((p i).hasFDerivAt (x := y)).mul ((p i).hasFDerivAt (x := y))
    have hlin : p i y • p i + p i y • p i = (2 * y i) • p i := by
      ext v; simp [p]; ring
    rw [hlin] at hm
    exact hm.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z ↦ by simp [p, sq])
  have hdiv :
      HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 4) ↦ (1 / 2 : ℝ) • ((z 1) ^ 2 + (z 2) ^ 2))
        (y 1 • p 1 + y 2 • p 2) y := by
    have hc := ((hsq 1).add (hsq 2)).const_smul (1 / 2 : ℝ)
    have hlin : (1 / 2 : ℝ) • ((2 * y 1) • p 1 + (2 * y 2) • p 2) = y 1 • p 1 + y 2 • p 2 := by
      ext v
      simp only [_root_.smul_apply, _root_.add_apply, smul_eq_mul]
      ring
    rw [hlin] at hc
    exact hc.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ ↦ rfl)
  have hsub := (hsq 0).sub hdiv
  have hlin2 : (2 * y 0) • p 0 - (y 1 • p 1 + y 2 • p 2) = eq2FoldFirstFDeriv y := by
    ext v; simp [eq2FoldFirstFDeriv, p]; ring
  rw [hlin2] at hsub
  exact hsub.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z ↦ by
    change z 0 ^ 2 - ((z 1 ^ 2 + z 2 ^ 2) / 2) = z 0 ^ 2 - (1 / 2 : ℝ) * (z 1 ^ 2 + z 2 ^ 2)
    ring)

theorem hasFDerivAt_eq2FoldMap (y : EuclideanSpace ℝ (Fin 4)) :
    HasFDerivAt eq2FoldMap (eq2FoldFDeriv y) y := by
  have h1 := (hasFDerivAt_eq2FoldFirst y).smul_const (EuclideanSpace.basisFun (Fin 2) ℝ 0)
  have h2 := ((EuclideanSpace.proj (𝕜 := ℝ) (3 : Fin 4)).hasFDerivAt (x := y)).smul_const
    (EuclideanSpace.basisFun (Fin 2) ℝ 1)
  exact (h1.add h2).congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ ↦ rfl)

theorem fderiv_eq2FoldMap (y : EuclideanSpace ℝ (Fin 4)) :
    fderiv ℝ eq2FoldMap y = eq2FoldFDeriv y :=
  (hasFDerivAt_eq2FoldMap y).fderiv

@[simp]
theorem fderiv_eq2FoldMap_apply_zero (y v : EuclideanSpace ℝ (Fin 4)) :
    (fderiv ℝ eq2FoldMap y v) 0 = 2 * y 0 * v 0 - y 1 * v 1 - y 2 * v 2 := by
  rw [fderiv_eq2FoldMap]
  simp [eq2FoldFDeriv, eq2FoldFirstFDeriv, EuclideanSpace.basisFun_apply]

@[simp]
theorem fderiv_eq2FoldMap_apply_one (y v : EuclideanSpace ℝ (Fin 4)) :
    (fderiv ℝ eq2FoldMap y v) 1 = v 3 := by
  rw [fderiv_eq2FoldMap]
  simp [eq2FoldFDeriv, eq2FoldFirstFDeriv, EuclideanSpace.basisFun_apply]

/-- Singular locus point `(0, 0, 0, t) ∈ ℝ⁴` of Equation (2). -/
noncomputable def eq2SingPoint (t : ℝ) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![0, 0, 0, t]

/-- Regular locus point `(1, 0, 0, t) ∈ ℝ⁴` of Equation (2). -/
noncomputable def eq2RegPoint (t : ℝ) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![1, 0, 0, t]

/-- Every point `(0, 0, 0, t)` belongs to `Crit(eq2FoldMap)`. -/
theorem eq2SingPoint_mem_criticalSet (t : ℝ) :
    eq2SingPoint t ∈ criticalSet (𝓡 4) (𝓡 2) eq2FoldMap := by
  rw [mem_criticalSet_iff, mfderiv_eq_fderiv]
  change ¬ Function.Surjective (fderiv ℝ eq2FoldMap (eq2SingPoint t))
  intro hsurj
  obtain ⟨v, hv⟩ := hsurj (EuclideanSpace.basisFun (Fin 2) ℝ 0)
  have hv0 := congrArg (fun u : EuclideanSpace ℝ (Fin 2) ↦ u 0) hv
  dsimp only at hv0
  rw [fderiv_eq2FoldMap_apply_zero] at hv0
  simp [eq2SingPoint, EuclideanSpace.basisFun_apply] at hv0

/-- At `(0, 0, 0, t) ∈ Crit(eq2FoldMap)`, the Jacobian–Poisson structure has rank `0`. -/
theorem eq2_rankAt_singPoint_eq_zero (t : ℝ) :
    (euclideanJacobianPoisson eq2FoldMap contDiff_eq2FoldMap).rankAt (eq2SingPoint t) = 0 := by
  have hpul0 : (TauCeti.SmoothForm.mpullback eq2FoldMap contDiff_eq2FoldMap.contMDiff
      planeAreaForm).1 (eq2SingPoint t) = 0 := by
    ext w
    rw [TauCeti.SmoothForm.mpullback_apply, planeAreaForm_apply]
    let wE : Fin 2 → EuclideanSpace ℝ (Fin 4) := fun k ↦ (w k : EuclideanSpace ℝ (Fin 4))
    have hmf (k : Fin 2) :
        (mfderiv (𝓡 4) (𝓡 2) eq2FoldMap (eq2SingPoint t) (w k) : EuclideanSpace ℝ (Fin 2)) =
          fderiv ℝ eq2FoldMap (eq2SingPoint t) (wE k) := by
      rw [mfderiv_eq_fderiv]; rfl
    simp_rw [hmf]
    have hpair : (fun k : Fin 2 ↦ fderiv ℝ eq2FoldMap (eq2SingPoint t) (wE k)) =
        ![fderiv ℝ eq2FoldMap (eq2SingPoint t) (wE 0),
          fderiv ℝ eq2FoldMap (eq2SingPoint t) (wE 1)] := by
      funext k; fin_cases k <;> rfl
    have hz0 : (fderiv ℝ eq2FoldMap (eq2SingPoint t) (wE 0)) 0 = 0 := by
      rw [fderiv_eq2FoldMap_apply_zero]; simp [eq2SingPoint]
    have hz1 : (fderiv ℝ eq2FoldMap (eq2SingPoint t) (wE 1)) 0 = 0 := by
      rw [fderiv_eq2FoldMap_apply_zero]; simp [eq2SingPoint]
    rw [hpair, euclideanPlaneVolumeForm_pair, hz0, hz1]
    simp
  have hanch0 : (euclideanJacobianPoisson eq2FoldMap contDiff_eq2FoldMap).anchor
      (eq2SingPoint t) = 0 := by
    ext α : 1
    change jacobianAnchor euclidean4VolumeForm planeAreaForm eq2FoldMap
      contDiff_eq2FoldMap.contMDiff (eq2SingPoint t) α = 0
    rw [jacobianAnchor_eq_subTopDualVector, hpul0,
      ContinuousAlternatingMap.pairedWedge_zero_right, neg_zero]
    simp [subTopDualVector]
  simp [SmoothBivector.rankAt, hanch0]

/-- Every point `(1, 0, 0, t)` lies outside `Crit(eq2FoldMap)`. -/
theorem eq2RegPoint_notMem_criticalSet (t : ℝ) :
    eq2RegPoint t ∉ criticalSet (𝓡 4) (𝓡 2) eq2FoldMap := by
  rw [mem_criticalSet_iff, mfderiv_eq_fderiv, not_not]
  change Function.Surjective (fderiv ℝ eq2FoldMap (eq2RegPoint t))
  intro w
  refine ⟨WithLp.toLp 2 ![w 0 / 2, 0, 0, w 1], ?_⟩
  ext i
  fin_cases i
  · simp [eq2RegPoint]; ring
  · change (fderiv ℝ eq2FoldMap (eq2RegPoint t) (WithLp.toLp 2 ![w 0 / 2, 0, 0, w 1])) 1 = w 1
    rw [fderiv_eq2FoldMap_apply_one]
    rfl

/-- At `(1, 0, 0, t) ∉ Crit(eq2FoldMap)`, the Jacobian–Poisson structure has rank `2`. -/
theorem eq2_rankAt_regPoint_eq_two (t : ℝ) :
    (euclideanJacobianPoisson eq2FoldMap contDiff_eq2FoldMap).rankAt (eq2RegPoint t) = 2 :=
  rankAt_jacobianPoisson_of_notMem_criticalSet euclidean4VolumeForm euclidean4VolumeForm_ne_zero
    planeAreaForm eq2FoldMap contDiff_eq2FoldMap.contMDiff (eq2RegPoint_notMem_criticalSet t)
    (planeAreaForm_ne_zero _)

/-- At `(1, 0, 0, t)`, `{y₁, y₂}_{π_f} = 2 ≠ 0` (`{y₂, y₃}_{π_f} = 2` in 1-indexed notation). -/
theorem eq2_bracket_coord_one_two_regPoint (t : ℝ) :
    ((euclideanJacobianPoisson eq2FoldMap contDiff_eq2FoldMap).bracket
      (euclideanCoord 1) (euclideanCoord 2)) (eq2RegPoint t) = 2 := by
  rw [euclideanJacobianPoisson_bracket_coord_one_two]
  simp [eq2RegPoint, EuclideanSpace.basisFun_apply]

/-- **Section 6 Gate 4 Witness**: For Equation (2) `(y₁, y₂, y₃, t) ↦ (y₁² - (y₂² + y₃²)/2, t)`,
`(0, 0, 0, t) ∈ Crit` has `rankAt = 0`, `(1, 0, 0, t) ∉ Crit` has `rankAt = 2` and `{y₂, y₃} = 2`,
and `π_f` is globally unimodular across both singular and regular loci. -/
theorem gate4_eq2_singular_to_regular_witness (t : ℝ) :
    eq2SingPoint t ∈ criticalSet (𝓡 4) (𝓡 2) eq2FoldMap ∧
      (euclideanJacobianPoisson eq2FoldMap contDiff_eq2FoldMap).rankAt (eq2SingPoint t) = 0 ∧
      eq2RegPoint t ∉ criticalSet (𝓡 4) (𝓡 2) eq2FoldMap ∧
      (euclideanJacobianPoisson eq2FoldMap contDiff_eq2FoldMap).rankAt (eq2RegPoint t) = 2 ∧
      ((euclideanJacobianPoisson eq2FoldMap contDiff_eq2FoldMap).bracket
          (euclideanCoord 1) (euclideanCoord 2)) (eq2RegPoint t) = 2 ∧
      (euclideanJacobianPoisson eq2FoldMap contDiff_eq2FoldMap).IsUnimodularWithVolume
        euclidean4VolumeForm :=
  ⟨eq2SingPoint_mem_criticalSet t,
    eq2_rankAt_singPoint_eq_zero t,
    eq2RegPoint_notMem_criticalSet t,
    eq2_rankAt_regPoint_eq_two t,
    eq2_bracket_coord_one_two_regPoint t,
    isUnimodularWithVolume_euclideanJacobianPoisson eq2FoldMap contDiff_eq2FoldMap⟩

/-! ## 4. M1.3 Singular-Circle Normal Form Witness (`S¹ × B³`, Equations (3)–(5)) -/

/-- Concrete point `(0, 0, 0, 0) ∈ S¹ × B³` on the singular circle `singularCircleLocus`. -/
noncomputable def tubeSingPoint : NormalBundleTube :=
  (0, ⟨0, by simp [OpenBall3]⟩)

/-- Concrete regular point `(0, 1/2, 0, 0) ∈ S¹ × B³` outside `singularCircleLocus`. -/
noncomputable def tubeRegPoint : NormalBundleTube :=
  (0, ⟨(1 / 2 : ℝ) • EuclideanSpace.basisFun (Fin 3) ℝ 0, by
    change (1 / 2 : ℝ) • EuclideanSpace.basisFun (Fin 3) ℝ 0 ∈
      Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1
    rw [Metric.mem_ball, dist_zero_right, norm_smul,
      (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal.1 0]
    norm_num⟩)

/-- Concrete witness for Equations (3)–(5) on `S¹ × B³` (`k = 1`): `rankAt = 0` on the singular
circle, `rankAt = 2` with `{x₂, x₃} = 1/2 ≠ 0` off the singular circle, unimodularity, and free
Poisson involution `normalInvolution`. -/
theorem m1_singular_circle_normal_form_witness :
    tubeSingPoint ∈ singularCircleLocus ∧
      (singularCirclePoisson 1).rankAt tubeSingPoint = 0 ∧
      tubeRegPoint ∉ singularCircleLocus ∧
      (singularCirclePoisson 1).rankAt tubeRegPoint = 2 ∧
      ((singularCirclePoisson 1).bracket (tubeCoord 1) (tubeCoord 2)) tubeRegPoint = 1 / 2 ∧
      normalInvolution tubeRegPoint ≠ tubeRegPoint ∧
      SmoothBivector.IsPoissonMap
        (singularCirclePoisson 1).toSmoothBivector
        (singularCirclePoisson 1).toSmoothBivector
        normalInvolution contMDiff_normalInvolution ∧
      (singularCirclePoisson 1).IsUnimodularPoisson := by
  have hreg : tubeRegPoint ∉ singularCircleLocus := by
    rw [mem_singularCircleLocus_iff]
    intro h0
    have hval := congrArg (fun x : EuclideanSpace ℝ (Fin 3) ↦ x 0) h0
    simp [tubeRegPoint] at hval
  refine ⟨rfl, rankAt_eq_zero_of_mem_singularCircleLocus 1 rfl, hreg,
    rankAt_singularCirclePoisson_of_notMem_singularCircleLocus 1 hreg (fun h ↦ one_ne_zero h),
    ?_, normalInvolution_ne_self tubeRegPoint,
    isPoissonMap_normalInvolution 1 (fun _ ↦ rfl),
    isUnimodularPoisson_singularCirclePoisson 1 (fun _ ↦ one_ne_zero)⟩
  rw [singularCirclePoisson_bracket_coord_one_two]
  simp [tubeRegPoint]

/-! ## 5. Section 6 Gate 5: Nontrivial $S^4$ Volume Measure Witness -/

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

/-- Ambient chordal distance between any `p : Sphere4` and its antipode `s4Antipode p`
equals `2`. -/
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

/-! ## 6. Cross-Track M1+M2 Integration Witnesses (`indefiniteFoldMap`, `s4Fibration`, `Sphere2`) -/

/-- Definitional identity between M1's `criticalSet` and M2's `criticalPoints`. -/
theorem criticalSet_eq_criticalPoints
    {E H E' H' M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H' N]
    (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H') (f : M → N) :
    criticalSet I J f = criticalPoints I J f :=
  rfl

/-- M2.1's `indefiniteFoldMap` coincides with Gate 4's `eq2FoldMap`. -/
theorem indefiniteFoldMap_eq_eq2FoldMap : indefiniteFoldMap = eq2FoldMap := by
  funext p
  refine ext_vec2 ?_ ?_ <;> simp [eq2FoldMap, eq2FoldFirst, EuclideanSpace.basisFun_apply]

/-- Congruence of `euclideanJacobianPoisson` under function equality (`ContDiff` is
proof-irrelevant). -/
theorem euclideanJacobianPoisson_congr
    {f g : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 2)}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hfg : f = g) :
    euclideanJacobianPoisson f hf = euclideanJacobianPoisson g hg := by
  subst hfg
  rfl

/-- **Cross-Track Gate 4 Witness on `LocalSingularModels.indefiniteFoldMap`**:
Directly connects M2.1's `indefiniteFoldMap` and `criticalPoints` with M1.2's
`euclideanJacobianPoisson`. -/
theorem m1_m2_indefiniteFoldMap_gate4_witness (t : ℝ) :
    vec4 0 0 0 t ∈ criticalPoints (𝓡 4) (𝓡 2) indefiniteFoldMap ∧
      (euclideanJacobianPoisson indefiniteFoldMap contDiff_indefiniteFoldMap).rankAt
        (vec4 0 0 0 t) = 0 ∧
      vec4 1 0 0 t ∉ criticalPoints (𝓡 4) (𝓡 2) indefiniteFoldMap ∧
      (euclideanJacobianPoisson indefiniteFoldMap contDiff_indefiniteFoldMap).rankAt
        (vec4 1 0 0 t) = 2 ∧
      ((euclideanJacobianPoisson indefiniteFoldMap contDiff_indefiniteFoldMap).bracket
          (euclideanCoord 1) (euclideanCoord 2)) (vec4 1 0 0 t) = 2 ∧
      (euclideanJacobianPoisson indefiniteFoldMap contDiff_indefiniteFoldMap).IsUnimodularWithVolume
        euclidean4VolumeForm := by
  have hs : vec4 0 0 0 t = eq2SingPoint t := rfl
  have hr : vec4 1 0 0 t = eq2RegPoint t := rfl
  have hP : euclideanJacobianPoisson indefiniteFoldMap contDiff_indefiniteFoldMap =
      euclideanJacobianPoisson eq2FoldMap contDiff_eq2FoldMap :=
    euclideanJacobianPoisson_congr _ _ indefiniteFoldMap_eq_eq2FoldMap
  refine ⟨indefiniteFold_zero_mem_criticalPoints t, ?_,
    indefiniteFold_one_notMem_criticalPoints t, ?_, ?_,
    isUnimodularWithVolume_euclideanJacobianPoisson indefiniteFoldMap contDiff_indefiniteFoldMap⟩
  · rw [hP, hs]
    exact eq2_rankAt_singPoint_eq_zero t
  · rw [hP, hr]
    exact eq2_rankAt_regPoint_eq_two t
  · rw [hP, hr]
    exact eq2_bracket_coord_one_two_regPoint t

section S4CrossTrack

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

/-- Global Jacobian–Poisson structure `π_{s4Fibration}` on `Sphere4` built by combining M1's
`jacobianPoissonOfPositiveVolume` with M2's `s4Fibration : Sphere4 → Sphere2`. -/
noncomputable def s4JacobianPoisson : PoissonStructure (𝓡 4) Sphere4 :=
  jacobianPoissonOfPositiveVolume S4PositiveVolumeForm S2VolumeForm s4Fibration
    contMDiff_s4Fibration

/-- Concrete regular point `(0, 0, 0, 0, 1) ∈ s4PreimageOpen` of `s4Fibration` over
`s2NorthPole`. -/
noncomputable def s4RegularPoint : Sphere4 :=
  s4PlaneEmbed (⟨0, Metric.mem_ball_self s4BaseDiskRadius_pos⟩, s2NorthPole)

theorem s4RegularPoint_mem_s4PreimageOpen : s4RegularPoint ∈ s4PreimageOpen.1 :=
  s4PlaneEmbed_mem_preimage (⟨0, Metric.mem_ball_self s4BaseDiskRadius_pos⟩, s2NorthPole)

theorem s4PreimageOpen_nonempty : s4PreimageOpen.1.Nonempty :=
  ⟨s4RegularPoint, s4RegularPoint_mem_s4PreimageOpen⟩

theorem s4RegularPoint_notMem_criticalPoints :
    s4RegularPoint ∉ criticalPoints (𝓡 4) (𝓡 2) s4Fibration :=
  notMem_criticalPoints_iff.mpr
    (regular_on_s4BaseRegion s4RegularPoint s4RegularPoint_mem_s4PreimageOpen)

/-- At `s4RegularPoint ∈ s4PreimageOpen`, `s4JacobianPoisson` has rank `2`. -/
theorem s4JacobianPoisson_rankAt_regularPoint :
    s4JacobianPoisson.rankAt s4RegularPoint = 2 :=
  rankAt_jacobianPoisson_of_notMem_criticalSet S4PositiveVolumeForm.Ω S4PositiveVolumeForm.Ω_ne_zero
    S2VolumeForm s4Fibration contMDiff_s4Fibration s4RegularPoint_notMem_criticalPoints
    (S2VolumeForm_ne_zero _)

/-- At `s4CriticalPoint ∈ criticalPoints (𝓡 4) (𝓡 2) s4Fibration`, `s4JacobianPoisson` has
rank `0`. -/
theorem s4JacobianPoisson_rankAt_criticalPoint :
    s4JacobianPoisson.rankAt s4CriticalPoint = 0 := by
  let x := s4CriticalPoint
  let e₁ : TangentSpace (𝓡 2) (s4ProjPlane x.1) :=
    (NormedSpace.fromTangentSpace (s4ProjPlane x.1)).symm (vec2 0 1)
  let u₀ : TangentSpace (𝓡 2) (s4Fibration x) :=
    mfderiv (𝓡 2) (𝓡 2) southPoleStereoInv (s4ProjPlane x.1) e₁
  have hcollinear (v : TangentSpace (𝓡 4) x) :
      ∃ c : ℝ, mfderiv (𝓡 4) (𝓡 2) s4Fibration x v = c • u₀ := by
    let V : EuclideanSpace ℝ (Fin 5) :=
      mvfderiv (𝓡 4) (Subtype.val : Sphere4 → EuclideanSpace ℝ (Fin 5)) x v
    have hV_mem : V ∈ (ℝ ∙ (x : EuclideanSpace ℝ (Fin 5)))ᗮ := by
      rw [← range_mvfderiv_subtypeVal (n := 4) x]
      exact LinearMap.mem_range_self _ v
    have hinner : ⟪(x : EuclideanSpace ℝ (Fin 5)), V⟫_ℝ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp hV_mem
    rw [PiLp.inner_apply, Fin.sum_univ_five] at hinner
    have hV0 : V 0 = 0 := by
      simp only [x, s4CriticalPoint, vec5_zero, vec5_one, vec5_two, vec5_three, vec5_four,
        RCLike.inner_apply, conj_trivial] at hinner
      linarith
    have hcoe : MDifferentiableAt (𝓡 4) 𝓘(ℝ, EuclideanSpace ℝ (Fin 5))
        (Subtype.val : Sphere4 → EuclideanSpace ℝ (Fin 5)) x :=
      (contMDiff_coe_sphere (m := ∞) x).mdifferentiableAt (by simp)
    have hproj : MDifferentiableAt (𝓡 4) (𝓡 2) (s4ProjPlane ∘ Subtype.val) x :=
      (s4ProjPlane.contDiff.contMDiff.comp (contMDiff_coe_sphere (m := ∞)) x).mdifferentiableAt
        (by simp)
    have hst : MDifferentiableAt (𝓡 2) (𝓡 2) southPoleStereoInv (s4ProjPlane x.1) :=
      (contMDiff_southPoleStereoInv (s4ProjPlane x.1)).mdifferentiableAt (by simp)
    have hvalE : (mfderiv (𝓡 4) (𝓡 2) (s4ProjPlane ∘ Subtype.val) x v : EuclideanPlane) =
        V 1 • vec2 0 1 := by
      rw [← mvfderiv_apply_eq_mfderiv_apply, s4ProjPlane.mvfderiv_comp_apply hcoe v]
      change s4ProjPlane V = V 1 • vec2 0 1
      rw [s4ProjPlane_apply, hV0]
      refine ext_vec2 ?_ ?_ <;> simp
    have hvalT : mfderiv (𝓡 4) (𝓡 2) (s4ProjPlane ∘ Subtype.val) x v = V 1 • e₁ := by
      apply (NormedSpace.fromTangentSpace (s4ProjPlane x.1)).injective
      rw [map_smul, ContinuousLinearEquiv.apply_symm_apply]
      exact hvalE
    refine ⟨V 1, ?_⟩
    have hcomp := congrArg (· v) (mfderiv_comp x hst hproj)
    change mfderiv (𝓡 4) (𝓡 2) (southPoleStereoInv ∘ ⇑s4ProjPlane ∘ Subtype.val) x v =
      V 1 • u₀
    rw [hcomp, ContinuousLinearMap.comp_apply, hvalT, map_smul]
    rfl
  have hpul0 : (TauCeti.SmoothForm.mpullback s4Fibration contMDiff_s4Fibration S2VolumeForm).1 x =
      0 := by
    ext w
    rw [TauCeti.SmoothForm.mpullback_apply]
    obtain ⟨c₀, hc₀⟩ := hcollinear (w 0)
    obtain ⟨c₁, hc₁⟩ := hcollinear (w 1)
    let A := S2VolumeForm.1 (s4Fibration x)
    have hw_eq : (fun i : Fin 2 ↦ mfderiv (𝓡 4) (𝓡 2) s4Fibration x (w i)) =
        Function.update (Function.update ![u₀, u₀] 0 (c₀ • u₀)) 1 (c₁ • u₀) := by
      funext i
      fin_cases i
      · simpa using hc₀
      · simpa using hc₁
    have hupd1 : Function.update (Function.update ![u₀, u₀] 0 (c₀ • u₀)) 1 u₀ =
        Function.update ![u₀, u₀] 0 (c₀ • u₀) := by
      funext i; fin_cases i <;> rfl
    change A (fun i : Fin 2 ↦ mfderiv (𝓡 4) (𝓡 2) s4Fibration x (w i)) = 0
    rw [hw_eq, A.map_update_smul, hupd1, A.map_update_smul,
      A.map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide),
      smul_zero, smul_zero]
  have hanch0 : s4JacobianPoisson.anchor s4CriticalPoint = 0 := by
    ext α : 1
    change jacobianAnchor S4PositiveVolumeForm.Ω S2VolumeForm s4Fibration contMDiff_s4Fibration x
      α = 0
    rw [jacobianAnchor_eq_subTopDualVector, hpul0,
      ContinuousAlternatingMap.pairedWedge_zero_right, neg_zero]
    simp [subTopDualVector]
  simp [SmoothBivector.rankAt, hanch0]

/-- **Cross-Track M1+M2 $S^4$ Jacobian–Poisson Witness**:
On `Sphere4`, `s4JacobianPoisson` (`π_{s4Fibration}`) is globally unimodular with volume
`S4PositiveVolumeForm.Ω`, vanishes (`rankAt = 0`) on `s4CriticalPoint ∈ criticalPoints` (nonempty),
and has `rankAt = 2` on `s4RegularPoint ∈ s4PreimageOpen` (nonempty). -/
theorem m1_m2_s4Fibration_jacobianPoisson_witness :
    s4JacobianPoisson.IsUnimodularWithVolume S4PositiveVolumeForm.Ω ∧
      s4JacobianPoisson.IsUnimodularPoisson ∧
      (criticalPoints (𝓡 4) (𝓡 2) s4Fibration).Nonempty ∧
      s4CriticalPoint ∈ criticalPoints (𝓡 4) (𝓡 2) s4Fibration ∧
      s4JacobianPoisson.rankAt s4CriticalPoint = 0 ∧
      s4PreimageOpen.1.Nonempty ∧
      s4RegularPoint ∈ s4PreimageOpen.1 ∧
      s4RegularPoint ∉ criticalPoints (𝓡 4) (𝓡 2) s4Fibration ∧
      s4JacobianPoisson.rankAt s4RegularPoint = 2 :=
  ⟨isUnimodularWithVolume_jacobianPoisson S4PositiveVolumeForm.Ω S4PositiveVolumeForm.Ω_ne_zero
      S2VolumeForm s4Fibration contMDiff_s4Fibration,
    isUnimodularPoisson_jacobianPoissonOfPositiveVolume S4PositiveVolumeForm S2VolumeForm
      s4Fibration contMDiff_s4Fibration,
    criticalPoints_s4Fibration_nonempty,
    s4CriticalPoint_mem_criticalPoints,
    s4JacobianPoisson_rankAt_criticalPoint,
    s4PreimageOpen_nonempty,
    s4RegularPoint_mem_s4PreimageOpen,
    s4RegularPoint_notMem_criticalPoints,
    s4JacobianPoisson_rankAt_regularPoint⟩

end S4CrossTrack

section S2LiftCheck

set_option linter.concreteInstances false

variable [HasTuringCompleteAreaPreservingDiskIsotopy]

/-- Canonical Darboux symplectic disk chart on `Sphere2` induced by `S2PositiveVolumeForm`. -/
noncomputable def s2DiskChart : SymplecticDiskChart Sphere2 S2PositiveVolumeForm.Ω :=
  S2PositiveVolumeForm.symplecticDiskChart

/-- Time-`1` area-preserving smooth diffeomorphism on `Sphere2` lifted from the Turing-complete disk
isotopy. -/
noncomputable def s2TimeOneDiffeomorph : Sphere2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere2 :=
  s2DiskChart.liftSliceDiffeomorph 1

/-- **Cross-Track M2.3 $S^2$ Isotopy Lift Witness**:
Under `[HasTuringCompleteAreaPreservingDiskIsotopy]`, `s2TimeOneDiffeomorph` on `Sphere2` is
isotopic to `Diffeomorph.refl` (`t = 0`), preserves `S2PositiveVolumeForm.Ω` under pullback, is
`MeasurePreserving` for `S2PositiveVolumeForm.μ`, satisfies `IsTuringComplete`, and differs from
`id`. -/
theorem m2_s2_liftSliceDiffeomorph_witness :
    s2DiskChart.liftSliceDiffeomorph 0 = Diffeomorph.refl (𝓡 2) Sphere2 ∞ ∧
      TauCeti.SmoothForm.mpullback s2TimeOneDiffeomorph s2TimeOneDiffeomorph.contMDiff
        S2PositiveVolumeForm.Ω = S2PositiveVolumeForm.Ω ∧
      MeasurePreserving ⇑s2TimeOneDiffeomorph S2PositiveVolumeForm.μ S2PositiveVolumeForm.μ ∧
      IsTuringComplete ⇑s2TimeOneDiffeomorph ∧
      (⇑s2TimeOneDiffeomorph : Sphere2 → Sphere2) ≠ id :=
  ⟨s2DiskChart.liftSliceDiffeomorph_zero,
    s2DiskChart.mpullback_liftSliceDiffeomorph_eq 1,
    SymplecticDiskChart.measurePreserving_liftSliceDiffeomorph S2PositiveVolumeForm s2DiskChart 1,
    s2DiskChart.isTuringComplete_liftTimeOne,
    s2DiskChart.isTuringComplete_liftTimeOne.ne_id⟩

end S2LiftCheck

end S4TuringPoisson.Checks
