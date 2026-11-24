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

public import S4TuringPoisson.Interfaces
public import S4TuringPoisson.Poisson.BivectorAndModular
public import S4TuringPoisson.Poisson.JacobianPoisson
public import S4TuringPoisson.Poisson.SingularCircleNormalForm
public import S4TuringPoisson.Fibration.LocalSingularModels
public import S4TuringPoisson.Fibration.S4Fibration
public import S4TuringPoisson.Fibration.WrinkledGeneral4Manifold
public import S4TuringPoisson.Fibration.PurelyWrinkled
public import S4TuringPoisson.Fibration.LekiliMoves
public import S4TuringPoisson.Fibration.ClosedManifoldLocal
public import S4TuringPoisson.Fibration.ADKS4Fibration
public import S4TuringPoisson.Smoothing.DiskSmoothing
public import S4TuringPoisson.Main
public import TauCeti.Geometry.Symplectic.Manifold.Sphere

/-!
# Adversarial Geometry, Poisson, Fibration & Volume Verification Checks (`GeomChecks`)

This file implements the Milestone M0–M5 geometric verification gates from Section 6 of
`MISSION_DIRECTIVE.md` together with cross-track M1–M5 integration checks:

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
- **Unconditional M3.3 Hamiltonian Disk-Smoothing & $S^2$ Symplectomorphism Lift Witnesses**:
  - `m33_elementary_disk_moves_witness`: unconditionally instantiates `bumpedRotationIsotopy`
    (Figure 1 `ρ`), `canonicalSectorSwapIsotopy` (Figure 1 `σ`), and
    `bumpedHyperbolicStretchIsotopy` (Figure 2) at explicit radii and rational test points,
    verifying ODE core action, compact-support vanishing, `det (fderiv) = 1`, `planeAreaForm`
    pullback preservation, and `diskTimeOneMap ≠ id`.
  - `m33_unconditional_s2_sectorSwap_witness`: unconditionally lifts `canonicalSectorSwapIsotopy`
    through `s2DiskChart` onto `Sphere2` (zero typeclasses!), verifying smooth isotopy to
    `Diffeomorph.refl`, `S2PositiveVolumeForm.Ω` pullback invariance, `MeasurePreserving`, and
    `≠ id`.
- **Final M4–M5 Aligned Volume (Gate 5), Equation (1) & Main Theorem Synthesis Checks**:
  - `gate5_s4_aligned_volume_witness`: verifies Section 6 Gate 5 directly on M4's aligned volume
    measure `Main.s4AlignedPositiveVolume.μ` on `Sphere4` (`0 < μ_Ω (ball p (1/2)) < μ_Ω univ < ⊤`
    universally and at `s4BasePoint`, plus strict positive co-orientation with
    `S4PositiveVolumeForm.Ω`).
  - `m4_s4_equation1_and_adapted_poisson_witness`: verifies Equation (1)
    (`mpullback_innerPreimageOpen_alignedVolumeForm Sphere4`) on the nonempty open domain
    `innerPreimageOpen Sphere4` together with global unimodularity, `rankAt = 0` on
    `s4CriticalPoint`, and `rankAt = 2` on `s4RegularPoint` for `Main.s4AdaptedPoisson`.
  - `m4_m5_s4_unconditional_poisson_diffeomorph_witness`: verifies
    `Main.exists_nontrivial_volumePreserving_poissonDiffeomorph_S4_unconditional` and proves
    `Main.s4UnconditionalPoissonDiffeomorph s4CriticalPoint = s4CriticalPoint` while `≠ id`.
  - `m5_headline_theorems_S4_and_fourManifold_check` &
    `m5_cmpp_headline_theorems_S4_and_fourManifold_check`: verifies Theorem 1 and Corollary 2
    instantiated on `Sphere4` (including Gate 5 non-degeneracy on the existential volume `V`).
- **Gates G5.1–G5.3 & Unconditional Corollary 2 Checks (`Lekili`, `ADK`, `ClosedManifoldLocal`)**:
  - `gate51_definite_fold_exclusion_witness`: verifies `s4Fibration` has a definite fold
    at `s4CriticalPoint` that cannot lift to `BrokenLefschetzFibration` or
    `PurelyWrinkledFibration`.
  - `gate52_lekili_astroid_and_surgery_witness`: verifies Lekili Move 1's 3-cusp deltoid and
    indefinite fold together with `s4BrokenLefschetzFibration.exists_purelyWrinkledFibration`.
  - `gate53_adk_s4_topology_and_turing_witness`: verifies `S²` and `T²` regular fibers,
    indefinite-fold critical circle, and Turing completeness / Hamiltonian flow realization for
    the global ADK fibration on `Sphere4`.
  - `unconditional_corollary2_closedFourManifold_on_S4_check`: instantiates unconditional
    Corollary 2 (`Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_closedFourManifold`
    and `undecidable_orbit_reachability_closedFourManifold`) on `Sphere4`.
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

/-! ## 7. Unconditional Milestone M3.3 Hamiltonian Disk-Smoothing & $S^2$ Lift Witnesses -/

section M33SmoothingChecks

/-- Explicit outer compact-support radius `r₀ = 3 / 4 ∈ (0, 1)` for M3.3 concrete witnesses. -/
noncomputable def m33SupportRadius : ℝ := 3 / 4

theorem m33SupportRadius_mem_Ioo : m33SupportRadius ∈ Set.Ioo (0 : ℝ) 1 := by
  norm_num [m33SupportRadius]

/-- Explicit inner rotation-core radius `r_in = 1 / 4 ∈ (0, 3 / 4)` for M3.3 concrete witnesses. -/
noncomputable def m33InnerRadius : ℝ := 1 / 4

theorem m33InnerRadius_mem_Ioo : m33InnerRadius ∈ Set.Ioo (0 : ℝ) m33SupportRadius := by
  norm_num [m33InnerRadius, m33SupportRadius]

/-- Concrete inner test point `(1 / 8, 0)` inside `Metric.closedBall 0 (1 / 4)`. -/
noncomputable def m33InnerTestPoint : EuclideanPlane :=
  (1 / 8 : ℝ) • planeBasis0

/-- Concrete exterior test point `(7 / 8, 0)` outside `Metric.ball 0 (3 / 4)`. -/
noncomputable def m33OuterTestPoint : EuclideanPlane :=
  (7 / 8 : ℝ) • planeBasis0

theorem norm_m33InnerTestPoint : ‖m33InnerTestPoint‖ = 1 / 8 := by
  rw [m33InnerTestPoint, norm_smul, Real.norm_of_nonneg (by norm_num),
    EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp

theorem m33InnerTestPoint_mem_closedBall :
    m33InnerTestPoint ∈ Metric.closedBall (0 : EuclideanPlane) m33InnerRadius := by
  rw [Metric.mem_closedBall, dist_zero_right, norm_m33InnerTestPoint, m33InnerRadius]
  norm_num

theorem m33OuterTestPoint_notMem_ball :
    m33OuterTestPoint ∉ Metric.ball (0 : EuclideanPlane) m33SupportRadius := by
  have hnorm : ‖m33OuterTestPoint‖ = 7 / 8 := by
    rw [m33OuterTestPoint, norm_smul, Real.norm_of_nonneg (by norm_num),
      EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp
  rw [Metric.mem_ball, dist_zero_right, hnorm, m33SupportRadius]
  norm_num

/-- Unconditional M3.3 instantiation of Figure 1 elementary move `ρ` (`bumpedRotationIsotopy`). -/
noncomputable def m33BumpedRotation : AreaPreservingDiskIsotopy m33SupportRadius :=
  bumpedRotationIsotopy m33SupportRadius_mem_Ioo m33InnerRadius_mem_Ioo

/-- Unconditional M3.3 instantiation of Figure 1 elementary move `σ`
(`canonicalSectorSwapIsotopy`). -/
noncomputable def m33SectorSwap : AreaPreservingDiskIsotopy m33SupportRadius :=
  canonicalSectorSwapIsotopy m33SupportRadius_mem_Ioo

/-- Unconditional M3.3 instantiation of Figure 2 elementary hyperbolic squeeze
(`bumpedHyperbolicStretchIsotopy` with `μ = Real.log 3`, scaling by `(1/3, 3)` near `0`). -/
noncomputable def m33HyperbolicStretch : AreaPreservingDiskIsotopy m33SupportRadius :=
  bumpedHyperbolicStretchIsotopy m33SupportRadius_mem_Ioo 0 (r_out := 1 / 2) (by norm_num)
    (Metric.ball_subset_ball (by norm_num [m33SupportRadius])) (Real.log 3)

/-- Pythagorean rational test point `(3 / 200, 4 / 200)` of exact Euclidean norm `1 / 40`. -/
noncomputable def m33StretchTestPoint : EuclideanPlane :=
  WithLp.toLp 2 ![3 / 200, 4 / 200]

theorem norm_m33StretchTestPoint : ‖m33StretchTestPoint‖ = 1 / 40 := by
  rw [m33StretchTestPoint, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Real.norm_eq_abs, sq_abs]
  have hsq : (3 / 200 : ℝ) ^ 2 + (4 / 200 : ℝ) ^ 2 = (1 / 40 : ℝ) ^ 2 := by norm_num
  rw [hsq, Real.sqrt_sq (by norm_num)]

/-- At `t = 1`, `m33HyperbolicStretch` maps `(3 / 200, 4 / 200)` to `(1 / 200, 3 / 50)`,
preserving the hyperbolic product `(3/200)*(4/200) = (1/200)*(3/50) = 3/10000`. -/
theorem m33HyperbolicStretch_apply_testPoint :
    m33HyperbolicStretch.d (1, m33StretchTestPoint) = WithLp.toLp 2 ![1 / 200, 3 / 50] := by
  have hlog_pos : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hδ : Real.exp (2 * |Real.log (3 : ℝ)|) * (1 / 40) < (1 / 2 : ℝ) / 2 := by
    rw [abs_of_pos hlog_pos]
    have h2 : (2 : ℝ) * Real.log 3 = ((2 : ℕ) : ℝ) * Real.log 3 := by norm_num
    rw [h2, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_num
  have hy₀ : m33StretchTestPoint ∈ Metric.closedBall (0 : EuclideanPlane) (1 / 40) := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_m33StretchTestPoint]
  have hact := bumpedHyperbolicStretchIsotopy_timeOne_of_mem_closedBall
    m33SupportRadius_mem_Ioo 0 (r_out := 1 / 2) (δ := 1 / 40) (by norm_num)
    (Metric.ball_subset_ball (by norm_num [m33SupportRadius])) (Real.log 3) hδ hy₀
  change (bumpedHyperbolicStretchIsotopy m33SupportRadius_mem_Ioo 0 (r_out := 1 / 2) (by norm_num)
    (Metric.ball_subset_ball (by norm_num [m33SupportRadius])) (Real.log 3)).d
    (1, m33StretchTestPoint) = WithLp.toLp 2 ![1 / 200, 3 / 50]
  rw [hact, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  ext i
  fin_cases i <;> simp [m33StretchTestPoint] <;> norm_num

theorem m33HyperbolicStretch_diskTimeOneMap_ne_id :
    m33HyperbolicStretch.diskTimeOneMap ≠ id := by
  intro hid
  have hmem : m33StretchTestPoint ∈ UnitDisk2 := by
    rw [UnitDisk2, Metric.mem_ball, dist_zero_right, norm_m33StretchTestPoint]
    norm_num
  have heq := congrArg (fun u : UnitDisk2 ↦ u.1 0) (congrFun hid ⟨m33StretchTestPoint, hmem⟩)
  change m33HyperbolicStretch.d (1, m33StretchTestPoint) 0 = m33StretchTestPoint 0 at heq
  rw [m33HyperbolicStretch_apply_testPoint] at heq
  simp [m33StretchTestPoint] at heq
  norm_num at heq

/-- **M3.3 Elementary Hamiltonian Disk-Moves Verification Bundle**:
Unconditionally verifies all three `CMPP21` Figures 1–2 Hamiltonian disk moves (`ρ`, `σ`, and the
hyperbolic Cantor squeeze) integrated via `TauCeti.timeDependentFlowOf`: exact inner-core action,
exterior support fixing, `det (fderiv) = 1`, `planeAreaForm` pullback invariance, and `≠ id`. -/
theorem m33_elementary_disk_moves_witness :
    m33BumpedRotation.d (0, m33InnerTestPoint) = m33InnerTestPoint ∧
      m33BumpedRotation.d (1, m33InnerTestPoint) = -m33InnerTestPoint ∧
      m33BumpedRotation.d (1, m33OuterTestPoint) = m33OuterTestPoint ∧
      LinearMap.det (fderiv ℝ (fun y ↦ m33BumpedRotation.d (1, y)) m33InnerTestPoint).toLinearMap =
        1 ∧
      TauCeti.SmoothForm.mpullback (fun y ↦ m33BumpedRotation.d (1, y))
        (m33BumpedRotation.contDiff_slice 1).contMDiff planeAreaForm = planeAreaForm ∧
      m33BumpedRotation.diskTimeOneMap ≠ id ∧
      TauCeti.SmoothForm.mpullback (fun y ↦ m33SectorSwap.d (1, y))
        (m33SectorSwap.contDiff_slice 1).contMDiff planeAreaForm = planeAreaForm ∧
      m33SectorSwap.diskTimeOneMap ≠ id ∧
      m33HyperbolicStretch.d (1, m33StretchTestPoint) = WithLp.toLp 2 ![1 / 200, 3 / 50] ∧
      TauCeti.SmoothForm.mpullback (fun y ↦ m33HyperbolicStretch.d (1, y))
        (m33HyperbolicStretch.contDiff_slice 1).contMDiff planeAreaForm = planeAreaForm ∧
      m33HyperbolicStretch.diskTimeOneMap ≠ id :=
  ⟨m33BumpedRotation.time_zero m33InnerTestPoint,
    bumpedRotationIsotopy_timeOne_eq_neg m33SupportRadius_mem_Ioo m33InnerRadius_mem_Ioo
      m33InnerTestPoint_mem_closedBall,
    m33BumpedRotation.eq_self_of_notMem_ball 1 m33OuterTestPoint m33OuterTestPoint_notMem_ball,
    m33BumpedRotation.det_fderiv_eq_one 1 m33InnerTestPoint,
    m33BumpedRotation.mpullback_planeAreaForm_eq 1,
    bumpedRotationIsotopy_diskTimeOneMap_ne_id m33SupportRadius_mem_Ioo m33InnerRadius_mem_Ioo,
    m33SectorSwap.mpullback_planeAreaForm_eq 1,
    (canonicalSectorSwapIsotopy_properties m33SupportRadius_mem_Ioo).2.2.2.2.2,
    m33HyperbolicStretch_apply_testPoint,
    m33HyperbolicStretch.mpullback_planeAreaForm_eq 1,
    m33HyperbolicStretch_diskTimeOneMap_ne_id⟩

private theorem mpullback_congr_fun_two_checks {E₁ H₁ M₁ E₂ H₂ M₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [IsManifold I₁ 1 M₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    [IsManifold I₂ 1 M₂] {f g : M₁ → M₂}
    (hf : ContMDiff I₁ I₂ ∞ f) (hg : ContMDiff I₁ I₂ ∞ g) (hfg : f = g)
    (α : TauCeti.SmoothForm I₂ M₂ ℝ 2) :
    TauCeti.SmoothForm.mpullback f hf α = TauCeti.SmoothForm.mpullback g hg α := by
  subst hfg
  rfl

/-- Unconditional $C^\infty$ `Diffeomorph` of `Sphere2` obtained by lifting any
`AreaPreservingDiskIsotopy r₀` through a `SymplecticDiskChart Sphere2 S2PositiveVolumeForm.Ω`. -/
noncomputable def liftDiskIsotopyDiffeomorph
    (C : SymplecticDiskChart Sphere2 S2PositiveVolumeForm.Ω)
    {r₀ : ℝ} (I : AreaPreservingDiskIsotopy r₀) (t : ℝ) :
    Sphere2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere2 where
  toFun z := C.liftThroughChart I.d (t, z)
  invFun z := C.liftThroughChart I.dInv (t, z)
  left_inv z := C.liftThroughChart_comp_of_inv (fun s _ hw ↦ I.mem_unitDisk2 s hw)
    I.left_inv t z
  right_inv z := C.liftThroughChart_comp_of_inv (fun s _ hw ↦ I.symm.mem_unitDisk2 s hw)
    I.right_inv t z
  contMDiff_toFun :=
    (C.contMDiff_liftThroughChart I.contDiff_d (fun s _ hw ↦ I.mem_unitDisk2 s hw)
      I.r₀_lt_one I.eq_self_of_notMem_ball).comp (contMDiff_const.prodMk contMDiff_id)
  contMDiff_invFun :=
    (C.contMDiff_liftThroughChart I.contDiff_dInv (fun s _ hw ↦ I.symm.mem_unitDisk2 s hw)
      I.r₀_lt_one (fun s _ hw ↦ I.dInv_eq_self_of_notMem_ball s hw)).comp
      (contMDiff_const.prodMk contMDiff_id)

theorem liftDiskIsotopyDiffeomorph_zero
    (C : SymplecticDiskChart Sphere2 S2PositiveVolumeForm.Ω)
    {r₀ : ℝ} (I : AreaPreservingDiskIsotopy r₀) :
    liftDiskIsotopyDiffeomorph C I 0 = Diffeomorph.refl (𝓡 2) Sphere2 ∞ := by
  refine Diffeomorph.ext fun z ↦ ?_
  by_cases hz : z ∈ C.sourceOpen.1
  · obtain ⟨y, rfl⟩ := C.range_embed.symm.subset hz
    change C.liftThroughChart I.d (0, C.embed y) = C.embed y
    rw [C.liftThroughChart_embed (fun s _ hw ↦ I.mem_unitDisk2 s hw) 0 y]
    exact congrArg C.embed (Subtype.ext (I.time_zero y.1))
  · exact C.liftThroughChart_of_notMem _ 0 hz

theorem mpullback_liftDiskIsotopyDiffeomorph_eq
    (C : SymplecticDiskChart Sphere2 S2PositiveVolumeForm.Ω)
    {r₀ : ℝ} (I : AreaPreservingDiskIsotopy r₀) (t : ℝ) :
    TauCeti.SmoothForm.mpullback (liftDiskIsotopyDiffeomorph C I t)
        (liftDiskIsotopyDiffeomorph C I t).contMDiff S2PositiveVolumeForm.Ω =
      S2PositiveVolumeForm.Ω := by
  let Φ := liftDiskIsotopyDiffeomorph C I t
  let δ : diskOpen → diskOpen := fun y ↦ ⟨I.d (t, y.1), I.mem_unitDisk2 t y.2⟩
  have hδ : ContMDiff (𝓡 2) (𝓡 2) ∞ δ :=
    (TauCeti.ContMDiff.subtypeVal_comp_iff diskOpen _).mp
      ((I.contDiff_slice t).contMDiff.comp contMDiff_subtype_val)
  have hδ_area :
      TauCeti.SmoothForm.mpullback δ hδ
          (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val planeAreaForm) =
        TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val planeAreaForm := by
    have hval_δ : (Subtype.val : diskOpen → _) ∘ δ =
        (fun w ↦ I.d (t, w)) ∘ Subtype.val := rfl
    calc
      TauCeti.SmoothForm.mpullback δ hδ
          (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val planeAreaForm)
        = TauCeti.SmoothForm.mpullback ((fun w ↦ I.d (t, w)) ∘ Subtype.val)
            ((I.contDiff_slice t).contMDiff.comp contMDiff_subtype_val) planeAreaForm := by
          rw [TauCeti.SmoothForm.mpullback_mpullback]
          exact mpullback_congr_fun_two_checks _ _ hval_δ planeAreaForm
      _ = TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val
            (TauCeti.SmoothForm.mpullback (fun w ↦ I.d (t, w))
              (I.contDiff_slice t).contMDiff planeAreaForm) := by
          rw [← TauCeti.SmoothForm.mpullback_mpullback (Subtype.val : diskOpen → EuclideanPlane)
            (fun w ↦ I.d (t, w)) contMDiff_subtype_val (I.contDiff_slice t).contMDiff
            planeAreaForm]
      _ = TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val planeAreaForm := by
          rw [I.mpullback_planeAreaForm_eq t]
  have hpull_embed :
      TauCeti.SmoothForm.mpullback C.embed C.contMDiff_embed
          (TauCeti.SmoothForm.mpullback Φ Φ.contMDiff S2PositiveVolumeForm.Ω) =
        TauCeti.SmoothForm.mpullback C.embed C.contMDiff_embed S2PositiveVolumeForm.Ω := by
    have hcomm : ⇑Φ ∘ C.embed = C.embed ∘ δ :=
      funext fun y ↦ C.liftThroughChart_embed (fun s _ hw ↦ I.mem_unitDisk2 s hw) t y
    calc
      TauCeti.SmoothForm.mpullback C.embed C.contMDiff_embed
          (TauCeti.SmoothForm.mpullback Φ Φ.contMDiff S2PositiveVolumeForm.Ω)
        = TauCeti.SmoothForm.mpullback (C.embed ∘ δ) (C.contMDiff_embed.comp hδ)
            S2PositiveVolumeForm.Ω := by
          rw [TauCeti.SmoothForm.mpullback_mpullback]
          exact mpullback_congr_fun_two_checks _ _ hcomm S2PositiveVolumeForm.Ω
      _ = TauCeti.SmoothForm.mpullback δ hδ
            (TauCeti.SmoothForm.mpullback C.embed C.contMDiff_embed S2PositiveVolumeForm.Ω) := by
          rw [← TauCeti.SmoothForm.mpullback_mpullback δ C.embed hδ C.contMDiff_embed
            S2PositiveVolumeForm.Ω]
      _ = TauCeti.SmoothForm.mpullback C.embed C.contMDiff_embed S2PositiveVolumeForm.Ω := by
          rw [C.mpullback_embed_eq, map_smul, hδ_area]
  refine Subtype.ext (funext fun z ↦ ?_)
  by_cases hz : z ∈ C.sourceOpen.1
  · obtain ⟨y, rfl⟩ := C.range_embed.symm.subset hz
    have hsurj : Function.Surjective (mfderiv (𝓡 2) (𝓡 2) C.embed y) :=
      (C.isLocalDiffeomorph_embed.isInvertible_mfderiv (by simp) y).surjective
    refine (TauCeti.mpullback_apply_eq_mpullback_apply_iff hsurj).mp ?_
    simpa only [TauCeti.SmoothForm.coe_mpullback] using
      congrFun (congrArg Subtype.val hpull_embed) y
  · have hz_not_supp : z ∉ C.supportSet I.r₀_lt_one :=
      fun hmem ↦ hz (C.supportSet_subset_sourceOpen I.r₀_lt_one hmem)
    have hclosed : IsClosed (C.supportSet I.r₀_lt_one) :=
      (C.isCompact_supportSet I.r₀_lt_one).isClosed
    let V_compl : Opens Sphere2 := ⟨(C.supportSet I.r₀_lt_one)ᶜ, hclosed.isOpen_compl⟩
    let zV : V_compl := ⟨z, hz_not_supp⟩
    have hΦ_compl : ⇑Φ ∘ (Subtype.val : V_compl → Sphere2) = (Subtype.val : V_compl → Sphere2) :=
      funext fun w ↦ C.liftThroughChart_eq_self_of_notMem_supportSet
        I.r₀_lt_one I.eq_self_of_notMem_ball t w.2
    have hpull_compl :
        TauCeti.SmoothForm.mpullback (Subtype.val : V_compl → Sphere2) contMDiff_subtype_val
            (TauCeti.SmoothForm.mpullback Φ Φ.contMDiff S2PositiveVolumeForm.Ω) =
          TauCeti.SmoothForm.mpullback (Subtype.val : V_compl → Sphere2) contMDiff_subtype_val
            S2PositiveVolumeForm.Ω := by
      rw [TauCeti.SmoothForm.mpullback_mpullback]
      exact mpullback_congr_fun_two_checks _ _ hΦ_compl S2PositiveVolumeForm.Ω
    have hsurj_compl :
        Function.Surjective (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : V_compl → Sphere2) zV) :=
      ((TauCeti.isLocalDiffeomorph_subtype_val (I := 𝓡 2) (n := ∞) zV).isInvertible_mfderiv
        (by simp)).surjective
    refine (TauCeti.mpullback_apply_eq_mpullback_apply_iff hsurj_compl).mp ?_
    simpa only [TauCeti.SmoothForm.coe_mpullback] using
      congrFun (congrArg Subtype.val hpull_compl) zV

theorem liftDiskIsotopyDiffeomorph_ne_id
    (C : SymplecticDiskChart Sphere2 S2PositiveVolumeForm.Ω)
    {r₀ : ℝ} (I : AreaPreservingDiskIsotopy r₀) (hne : I.diskTimeOneMap ≠ id) :
    (⇑(liftDiskIsotopyDiffeomorph C I 1) : Sphere2 → Sphere2) ≠ id := by
  intro hid
  apply hne
  funext y
  have hemb :
      C.embed ⟨(I.diskTimeOneMap y).1, (I.diskTimeOneMap y).2⟩ = C.embed ⟨y.1, y.2⟩ := by
    calc
      C.embed ⟨(I.diskTimeOneMap y).1, (I.diskTimeOneMap y).2⟩
          = C.liftThroughChart I.d (1, C.embed ⟨y.1, y.2⟩) :=
            (C.liftThroughChart_embed (fun s _ hw ↦ I.mem_unitDisk2 s hw) 1 ⟨y.1, y.2⟩).symm
      _ = liftDiskIsotopyDiffeomorph C I 1 (C.embed ⟨y.1, y.2⟩) := rfl
      _ = C.embed ⟨y.1, y.2⟩ := congrFun hid (C.embed ⟨y.1, y.2⟩)
  exact Subtype.ext (congrArg Subtype.val (C.injective_embed hemb))

/-- Unconditional nontrivial area-preserving $C^\infty$ symplectomorphism of `Sphere2` obtained by
lifting `m33SectorSwap` (`canonicalSectorSwapIsotopy`) through `s2DiskChart`. -/
noncomputable def s2UnconditionalSectorSwap : Sphere2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere2 :=
  liftDiskIsotopyDiffeomorph s2DiskChart m33SectorSwap 1

/-- **Cross-Track M2+M3.3 Unconditional $S^2$ Symplectomorphism Witness**:
With **zero** typeclass assumptions, lifting `m33SectorSwap` through `s2DiskChart` produces a
smooth 1-parameter family of `Sphere2` diffeomorphisms starting at `Diffeomorph.refl` (`t = 0`),
preserving `S2PositiveVolumeForm.Ω` at every time `t : ℝ`, whose time-`1` map
`s2UnconditionalSectorSwap` is `MeasurePreserving` for `S2PositiveVolumeForm.μ` and strictly
nontrivial (`≠ id`). -/
theorem m33_unconditional_s2_sectorSwap_witness :
    liftDiskIsotopyDiffeomorph s2DiskChart m33SectorSwap 0 = Diffeomorph.refl (𝓡 2) Sphere2 ∞ ∧
      (∀ t : ℝ,
        TauCeti.SmoothForm.mpullback (liftDiskIsotopyDiffeomorph s2DiskChart m33SectorSwap t)
          (liftDiskIsotopyDiffeomorph s2DiskChart m33SectorSwap t).contMDiff
          S2PositiveVolumeForm.Ω = S2PositiveVolumeForm.Ω) ∧
      MeasurePreserving ⇑s2UnconditionalSectorSwap S2PositiveVolumeForm.μ S2PositiveVolumeForm.μ ∧
      (⇑s2UnconditionalSectorSwap : Sphere2 → Sphere2) ≠ id :=
  ⟨liftDiskIsotopyDiffeomorph_zero s2DiskChart m33SectorSwap,
    mpullback_liftDiskIsotopyDiffeomorph_eq s2DiskChart m33SectorSwap,
    S2PositiveVolumeForm.measurePreserving_of_mpullback_eq s2UnconditionalSectorSwap
      (mpullback_liftDiskIsotopyDiffeomorph_eq s2DiskChart m33SectorSwap 1),
    liftDiskIsotopyDiffeomorph_ne_id s2DiskChart m33SectorSwap
      (canonicalSectorSwapIsotopy_properties m33SupportRadius_mem_Ioo).2.2.2.2.2⟩

end M33SmoothingChecks

/-! ## 8. Final Milestone M4–M5 Gate 5, Equation (1) & Main Theorem Synthesis Checks -/

section M4M5UnconditionalChecks

/-- **Section 6 Gate 5 Witness on M4's Aligned Volume `Main.s4AlignedPositiveVolume`**:
Verifies `0 < μ_Ω (Metric.ball p (1 / 2)) < μ_Ω Set.univ` for every `p : Sphere4` and specifically
at `s4BasePoint`, finite total volume `< ⊤`, non-vanishing at `s4BasePoint`, and global strict
positive co-orientation with `S4PositiveVolumeForm.Ω`. -/
theorem gate5_s4_aligned_volume_witness :
    (∀ p : Sphere4,
      0 < Main.s4AlignedPositiveVolume.μ (Metric.ball p (1 / 2)) ∧
        Main.s4AlignedPositiveVolume.μ (Metric.ball p (1 / 2)) <
          Main.s4AlignedPositiveVolume.μ Set.univ) ∧
      0 < Main.s4AlignedPositiveVolume.μ (Metric.ball s4BasePoint (1 / 2)) ∧
      Main.s4AlignedPositiveVolume.μ (Metric.ball s4BasePoint (1 / 2)) <
        Main.s4AlignedPositiveVolume.μ Set.univ ∧
      Main.s4AlignedPositiveVolume.μ Set.univ < ⊤ ∧
      Main.s4AlignedPositiveVolume.Ω.1 s4BasePoint ≠ 0 ∧
      ∀ x : Sphere4, ∃ a : ℝ, 0 < a ∧
        Main.s4AlignedPositiveVolume.Ω.1 x = a • S4PositiveVolumeForm.Ω.1 x :=
  ⟨Main.s4AlignedPositiveVolume_ball_bounds,
    (Main.s4AlignedPositiveVolume_ball_bounds s4BasePoint).1,
    (Main.s4AlignedPositiveVolume_ball_bounds s4BasePoint).2,
    measure_lt_top Main.s4AlignedPositiveVolume.μ Set.univ,
    Main.s4AlignedPositiveVolume.Ω_ne_zero s4BasePoint,
    alignedVolumeForm_pos_cooriented Sphere4⟩

/-- Non-emptiness of the open 4-manifold domain `innerPreimageOpen Sphere4` on which Equation (1)
holds, ruling out vacuous pullback identities. -/
theorem innerPreimageOpen_s4_nonempty : (innerPreimageOpen Sphere4).1.Nonempty := by
  let x₀ : Sphere4 := s4WrinkledFibration.embed (s4WrinkledFibration.baseCenter, s2NorthPole)
  refine ⟨x₀, ?_⟩
  change s4Fibration x₀ ∈ (baseInnerOpen Sphere4).1
  have hf : s4Fibration x₀ = s4WrinkledFibration.baseCenter.1 :=
    s4WrinkledFibration.apply_embed s4WrinkledFibration.baseCenter s2NorthPole
  rw [hf]
  have hcore : s4WrinkledFibration.baseCenter.1 ∈ (baseCoreOpen Sphere4).1 :=
    baseCenter_mem_baseCoreOpen Sphere4
  have hclosed := baseOpenSubdisk_subset_baseClosedSubdisk Sphere4 (rCore Sphere4)
    (rCore_lt_baseRadius Sphere4) hcore
  exact baseClosedSubdisk_subset_baseOpenSubdisk Sphere4 (rCore_lt_baseRadius Sphere4)
    (rCore_lt_rInner Sphere4) hclosed

/-- **M4.1 Equation (1) & Adapted $S^4$ Jacobian–Poisson Witness**:
Verifies that `innerPreimageOpen Sphere4` is nonempty, `alignedVolumeForm Sphere4` satisfies
Equation (1) (`mpullback_innerPreimageOpen_alignedVolumeForm Sphere4`), and `Main.s4AdaptedPoisson`
is globally unimodular with `rankAt = 0` at `s4CriticalPoint` and `rankAt = 2` at
`s4RegularPoint`. -/
theorem m4_s4_equation1_and_adapted_poisson_witness :
    (innerPreimageOpen Sphere4).1.Nonempty ∧
      TauCeti.SmoothForm.mpullback (Subtype.val : innerPreimageOpen Sphere4 → Sphere4)
          contMDiff_subtype_val (alignedVolumeForm Sphere4) =
        TauCeti.SmoothForm.mpullback
          (Opens.inclusion (innerPreimageOpen_le_preimageOpen Sphere4))
          (contMDiff_inclusion _) (trivializedProductForm Sphere4) ∧
      Main.s4AdaptedPoisson.IsUnimodularWithVolume Main.s4AlignedPositiveVolume.Ω ∧
      Main.s4AdaptedPoisson.IsUnimodularPoisson ∧
      Main.s4AdaptedPoisson.rankAt s4CriticalPoint = 0 ∧
      Main.s4AdaptedPoisson.rankAt s4RegularPoint = 2 :=
  ⟨innerPreimageOpen_s4_nonempty,
    mpullback_innerPreimageOpen_alignedVolumeForm Sphere4,
    isUnimodularWithVolume_adaptedJacobianPoisson Sphere4,
    isUnimodularPoisson_adaptedJacobianPoisson Sphere4,
    rankAt_adaptedJacobianPoisson_of_mem_criticalPoints Sphere4 s4CriticalPoint_mem_criticalPoints,
    rankAt_adaptedJacobianPoisson_of_notMem_criticalPoints Sphere4
      s4RegularPoint_notMem_criticalPoints⟩

theorem s4CriticalPoint_notMem_s4PreimageOpen : s4CriticalPoint ∉ s4PreimageOpen.1 := by
  intro hmem
  have hb : s4Fibration s4CriticalPoint ∈ s4BaseRegion.1 := hmem
  have hcrit : s4Fibration s4CriticalPoint ∈
      s4Fibration '' criticalPoints (𝓡 4) (𝓡 2) s4Fibration :=
    ⟨s4CriticalPoint, s4CriticalPoint_mem_criticalPoints, rfl⟩
  exact Set.disjoint_left.mp disjoint_s4BaseRegion_criticalPoints hb hcrit

theorem s4UnconditionalPoissonDiffeomorph_criticalPoint :
    Main.s4UnconditionalPoissonDiffeomorph s4CriticalPoint = s4CriticalPoint :=
  leafwiseBumpDiffeomorphOfIsotopy_of_notMem Sphere4 Main.s4SectorSwapDiskIsotopy
    s4CriticalPoint_notMem_s4PreimageOpen

/-- **M4+M5 Unconditional $S^4$ Volume-Preserving Poisson Diffeomorphism Witness**:
Verifies `Main.exists_nontrivial_volumePreserving_poissonDiffeomorph_S4_unconditional` together
with singular-locus fixing (`d_bar s4CriticalPoint = s4CriticalPoint`) alongside global
non-triviality (`d_bar ≠ id`), ruling out 3D suspension shortcuts. -/
theorem m4_m5_s4_unconditional_poisson_diffeomorph_witness :
    (s4Fibration ∘ ⇑Main.s4UnconditionalPoissonDiffeomorph = s4Fibration ∧
      SmoothBivector.IsPoissonMap Main.s4AdaptedPoisson.toSmoothBivector
        Main.s4AdaptedPoisson.toSmoothBivector Main.s4UnconditionalPoissonDiffeomorph
        Main.s4UnconditionalPoissonDiffeomorph.contMDiff ∧
      TauCeti.SmoothForm.mpullback Main.s4UnconditionalPoissonDiffeomorph
        Main.s4UnconditionalPoissonDiffeomorph.contMDiff Main.s4AlignedPositiveVolume.Ω =
        Main.s4AlignedPositiveVolume.Ω ∧
      MeasurePreserving ⇑Main.s4UnconditionalPoissonDiffeomorph
        Main.s4AlignedPositiveVolume.μ Main.s4AlignedPositiveVolume.μ ∧
      (⇑Main.s4UnconditionalPoissonDiffeomorph : Sphere4 → Sphere4) ≠ id) ∧
      Main.s4UnconditionalPoissonDiffeomorph s4CriticalPoint = s4CriticalPoint :=
  ⟨Main.exists_nontrivial_volumePreserving_poissonDiffeomorph_S4_unconditional,
    s4UnconditionalPoissonDiffeomorph_criticalPoint⟩

/-- Any `PositiveVolumeForm (𝓡 4) Sphere4` automatically satisfies the Section 6 Gate 5 bounds at
`s4BasePoint`. -/
theorem positiveVolumeForm_s4_gate5 (V : PositiveVolumeForm (𝓡 4) Sphere4) :
    0 < V.μ (Metric.ball s4BasePoint (1 / 2)) ∧
      V.μ (Metric.ball s4BasePoint (1 / 2)) < V.μ Set.univ ∧
      V.μ Set.univ < ⊤ := by
  have hpos : 0 < V.μ (Metric.ball s4BasePoint (1 / 2)) :=
    V.measure_isOpen_pos Metric.isOpen_ball ⟨s4BasePoint, Metric.mem_ball_self (by norm_num)⟩
  have hlt : V.μ (Metric.ball s4BasePoint (1 / 2)) < V.μ Set.univ := by
    refine V.measure_lt_univ_of_disjoint_isOpen
      (u := Metric.ball (s4Antipode s4BasePoint) (1 / 2)) Metric.isOpen_ball
      ⟨s4Antipode s4BasePoint, Metric.mem_ball_self (by norm_num)⟩ ?_
    exact Metric.ball_disjoint_ball (by rw [dist_s4Antipode s4BasePoint]; norm_num)
  exact ⟨hpos, hlt, measure_lt_top V.μ Set.univ⟩

end M4M5UnconditionalChecks

section M5HeadlineChecks

set_option linter.concreteInstances false

/-- **M5 Headline Theorem 1 & Corollary 2 Synthesis Check on `Sphere4`**:
Under `[HasTuringCompleteAreaPreservingDiskIsotopy]`, verifies that both
`Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_S4` (Theorem 1) and
`Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_fourManifold Sphere4` (Corollary 2
instantiated on `Sphere4`) produce genuine Gate 5 non-degenerate volumes `V`, unimodular
generically rank-2 Jacobian–Poisson structures with nonempty rank-0 singular locus, and
leaf-preserving, volume-preserving, measure-preserving, Turing complete Poisson diffeomorphisms. -/
theorem m5_headline_theorems_S4_and_fourManifold_check
    [HasTuringCompleteAreaPreservingDiskIsotopy] :
    (∃ (V : PositiveVolumeForm (𝓡 4) Sphere4)
      (π_f : PoissonStructure (𝓡 4) Sphere4)
      (d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4),
      0 < V.μ (Metric.ball s4BasePoint (1 / 2)) ∧
      V.μ (Metric.ball s4BasePoint (1 / 2)) < V.μ Set.univ ∧
      V.μ Set.univ < ⊤ ∧
      π_f.IsUnimodularWithVolume V.Ω ∧
      (∀ x ∉ criticalPoints (𝓡 4) (𝓡 2) s4Fibration, π_f.rankAt x = 2) ∧
      (criticalPoints (𝓡 4) (𝓡 2) s4Fibration).Nonempty ∧
      (∀ x ∈ criticalPoints (𝓡 4) (𝓡 2) s4Fibration, π_f.rankAt x = 0) ∧
      s4Fibration ∘ ⇑d_bar = s4Fibration ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_bar d_bar.contMDiff ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasurePreserving ⇑d_bar V.μ V.μ ∧
      IsTuringComplete ⇑d_bar ∧
      (⇑d_bar : Sphere4 → Sphere4) ≠ id) ∧
    (∃ (V' : PositiveVolumeForm (𝓡 4) Sphere4)
      (π_f' : PoissonStructure (𝓡 4) Sphere4)
      (d_bar' : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4),
      0 < V'.μ (Metric.ball s4BasePoint (1 / 2)) ∧
      V'.μ (Metric.ball s4BasePoint (1 / 2)) < V'.μ Set.univ ∧
      π_f'.IsUnimodularWithVolume V'.Ω ∧
      s4Fibration ∘ ⇑d_bar' = s4Fibration ∧
      SmoothBivector.IsPoissonMap π_f'.toSmoothBivector π_f'.toSmoothBivector
        d_bar' d_bar'.contMDiff ∧
      MeasurePreserving ⇑d_bar' V'.μ V'.μ ∧
      IsTuringComplete ⇑d_bar' ∧
      (⇑d_bar' : Sphere4 → Sphere4) ≠ id) := by
  constructor
  · obtain ⟨V, π_f, d_bar, -, hunim, -, hreg, hne, hcrit, hfib, hpoiss, -, hpull, hmp, htc,
      hne_id⟩ := Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_S4
    obtain ⟨hpos, hlt, hfin⟩ := positiveVolumeForm_s4_gate5 V
    exact ⟨V, π_f, d_bar, hpos, hlt, hfin, hunim, hreg, hne, hcrit, hfib, hpoiss, hpull, hmp, htc,
      hne_id⟩
  · obtain ⟨V', π_f', d_bar', -, hunim', -, -, -, hfib', hpoiss', -, -, hmp', htc', hne_id'⟩ :=
      Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_fourManifold Sphere4
    obtain ⟨hpos', hlt', -⟩ := positiveVolumeForm_s4_gate5 V'
    exact ⟨V', π_f', d_bar', hpos', hlt', hunim', hfib', hpoiss', hmp', htc', hne_id'⟩

/-- **M3.3 + M5 CMPP Hamiltonian Synthesis Check on `Sphere4`**:
Verifies automatic synthesis of Theorem 1 and Corollary 2 (instantiated on `Sphere4`) from
`[HasCMPPCantorCirculationHamiltonians]`. -/
theorem m5_cmpp_headline_theorems_S4_and_fourManifold_check
    [HasCMPPCantorCirculationHamiltonians] :
    (∃ (V : PositiveVolumeForm (𝓡 4) Sphere4)
      (d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4),
      0 < V.μ (Metric.ball s4BasePoint (1 / 2)) ∧
      V.μ (Metric.ball s4BasePoint (1 / 2)) < V.μ Set.univ ∧
      s4Fibration ∘ ⇑d_bar = s4Fibration ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasurePreserving ⇑d_bar V.μ V.μ ∧
      IsTuringComplete ⇑d_bar) ∧
    ∃ (V' : PositiveVolumeForm (𝓡 4) Sphere4)
      (π_f' : PoissonStructure (𝓡 4) Sphere4)
      (d_bar' : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4),
      π_f'.IsUnimodularWithVolume V'.Ω ∧
      s4Fibration ∘ ⇑d_bar' = s4Fibration ∧
      SmoothBivector.IsPoissonMap π_f'.toSmoothBivector π_f'.toSmoothBivector
        d_bar' d_bar'.contMDiff ∧
      MeasurePreserving ⇑d_bar' V'.μ V'.μ ∧
      IsTuringComplete ⇑d_bar' := by
  constructor
  · obtain ⟨V, d_bar, hfib, hpull, hmp, htc⟩ :=
      Main.exists_turingComplete_volumePreserving_diffeomorph_S4_of_cmpp
    obtain ⟨hpos, hlt, -⟩ := positiveVolumeForm_s4_gate5 V
    exact ⟨V, d_bar, hpos, hlt, hfib, hpull, hmp, htc⟩
  · obtain ⟨V', π_f', d_bar', -, hunim', -, -, -, hfib', hpoiss', -, -, hmp', htc', -⟩ :=
      Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_fourManifold_of_cmpp Sphere4
    exact ⟨V', π_f', d_bar', hunim', hfib', hpoiss', hmp', htc'⟩

end M5HeadlineChecks

/-! ## 9. Gates G5.1–G5.3: Definite-Fold Exclusion, Lekili Surgery, ADK & Unconditional Cor. 2 -/

section LekiliAndADKChecks

set_option linter.concreteInstances false

/-- **Gate G5.1 Definite-Fold Exclusion Witness**:
`s4Fibration` at `s4CriticalPoint` satisfies neither `IsIndefiniteFoldAt`, `IsWrinkledCuspAt`,
nor `IsRealLefschetzAt`, so `s4Fibration` admits neither a `BrokenLefschetzFibration` nor a
`PurelyWrinkledFibration` lift. -/
theorem gate51_definite_fold_exclusion_witness :
    s4CriticalPoint ∈ criticalPoints (𝓡 4) (𝓡 2) s4Fibration ∧
      ¬ IsIndefiniteFoldAt (𝓡 4) (𝓡 2) s4Fibration s4CriticalPoint ∧
      ¬ IsWrinkledCuspAt (𝓡 4) (𝓡 2) s4Fibration s4CriticalPoint ∧
      ¬ IsRealLefschetzAt (𝓡 4) (𝓡 2) s4Fibration s4CriticalPoint ∧
      (∀ B : BrokenLefschetzFibration (𝓡 4) Sphere4 (𝓡 2) Sphere2 Sphere2,
        B.toFun ≠ s4Fibration) ∧
      ∀ P : PurelyWrinkledFibration (𝓡 4) Sphere4 (𝓡 2) Sphere2 Sphere2,
        P.toFun ≠ s4Fibration :=
  ⟨s4CriticalPoint_mem_criticalPoints,
    not_isIndefiniteFoldAt_s4Fibration s4CriticalPoint_mem_criticalPoints,
    not_isWrinkledCuspAt_s4Fibration s4CriticalPoint_mem_criticalPoints,
    not_isRealLefschetzAt_s4Fibration s4CriticalPoint_mem_criticalPoints,
    not_brokenLefschetzFibration_s4Fibration,
    not_purelyWrinkledFibration_s4Fibration⟩

/-- **Gate G5.2 Lekili Move 1 Deltoid Cusp & Broken-to-Purely-Wrinkled Surgery Witness**:
Verifies `lekiliMove1 1` produces three pairwise distinct cusps (`deriv = 0` at `0, 2π/3, 4π/3`),
an indefinite fold at `θ = π` (`deriv ≠ 0`), full cusp/fold classification on `Crit(lekiliMove1 1)`,
and `s4BrokenLefschetzFibration.exists_purelyWrinkledFibration` over `Sphere4`. -/
theorem gate52_lekili_astroid_and_surgery_witness :
    (deriv (lekiliMove1CritValue 1) 0 = 0 ∧
        deriv (lekiliMove1CritValue 1) (2 * Real.pi / 3) = 0 ∧
        deriv (lekiliMove1CritValue 1) (4 * Real.pi / 3) = 0 ∧
        deriv (lekiliMove1CritValue 1) Real.pi ≠ 0 ∧
        lekiliMove1CritValue 1 0 ≠ lekiliMove1CritValue 1 (2 * Real.pi / 3) ∧
        lekiliMove1CritValue 1 0 ≠ lekiliMove1CritValue 1 (4 * Real.pi / 3) ∧
        lekiliMove1CritValue 1 (2 * Real.pi / 3) ≠ lekiliMove1CritValue 1 (4 * Real.pi / 3)) ∧
      IsIndefiniteFoldAt (𝓡 4) (𝓡 2) (lekiliMove1 1) (lekiliMove1CritCurve 1 Real.pi) ∧
      (∀ p ∈ criticalPoints (𝓡 4) (𝓡 2) (lekiliMove1 1),
        IsIndefiniteFoldAt (𝓡 4) (𝓡 2) (lekiliMove1 1) p ∨
          IsWrinkledCuspAt (𝓡 4) (𝓡 2) (lekiliMove1 1) p) ∧
      ∃ P : PurelyWrinkledFibration (𝓡 4) Sphere4 (𝓡 2) Sphere2 Sphere2,
        0 < P.baseDiskRadius ∧
        P.baseRegion.1.Nonempty ∧
        P.baseRegion.1 ⊆ s4ADKBaseRegion.1 ∧
        ∀ x ∈ P.toFun ⁻¹' P.baseRegion.1, P.toFun x = s4ADKFibration x := by
  obtain ⟨h0, h23, h43, _, hpi_ne, hd1, hd2, hd3⟩ := gate52_lekiliMove1_three_cusps 1 one_ne_zero
  obtain ⟨P, _, hsub, hval⟩ := s4BrokenLefschetzFibration.exists_purelyWrinkledFibration
  exact ⟨⟨h0, h23, h43, hpi_ne, hd1, hd2, hd3⟩,
    isIndefiniteFoldAt_lekiliMove1_pi one_ne_zero,
    singularities_lekiliMove1 one_ne_zero,
    ⟨P, P.baseDiskRadius_pos, P.baseRegion_nonempty, hsub, hval⟩⟩

/-- **Gate G5.3 Global ADK Broken Lefschetz Fibration Topology & Turing Completeness on $S^4$**:
Verifies that `s4ADKFibration` has both `S²` (`s2NorthPole`) and `T²` (`s2SouthPole`) regular
fibers, an indefinite-fold critical point at `s4ADKCritBase`, an unconditional Turing complete
volume-preserving Poisson diffeomorphism (with Gate 5 bounds on `V`), and a finite
Poisson–Hamiltonian flow realization. -/
theorem gate53_adk_s4_topology_and_turing_witness :
    Nonempty (Sphere2 ≃ₜ {x : Sphere4 // s4ADKFibration x = s2NorthPole}) ∧
      Nonempty ((Metric.sphere (0 : EuclideanPlane) 1 × Metric.sphere (0 : EuclideanPlane) 1) ≃ₜ
        {x : Sphere4 // s4ADKFibration x = s2SouthPole}) ∧
      s4ADKCritBase ∈ criticalPoints (𝓡 4) (𝓡 2) s4ADKFibration ∧
      IsIndefiniteFoldAt (𝓡 4) (𝓡 2) s4ADKFibration s4ADKCritBase ∧
      (∃ (V : PositiveVolumeForm (𝓡 4) Sphere4)
        (π_f : PoissonStructure (𝓡 4) Sphere4)
        (d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4),
        0 < V.μ (Metric.ball s4BasePoint (1 / 2)) ∧
        V.μ (Metric.ball s4BasePoint (1 / 2)) < V.μ Set.univ ∧
        π_f.IsUnimodularWithVolume V.Ω ∧
        s4ADKFibration ∘ ⇑d_bar = s4ADKFibration ∧
        SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
          d_bar d_bar.contMDiff ∧
        TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
        MeasurePreserving ⇑d_bar V.μ V.μ ∧
        IsTuringComplete ⇑d_bar ∧
        (⇑d_bar : Sphere4 → Sphere4) ≠ id) ∧
      ∃ (V' : PositiveVolumeForm (𝓡 4) Sphere4)
        (π_f' : PoissonStructure (𝓡 4) Sphere4)
        (Hs : List C^∞⟮𝓡 4, Sphere4; ℝ⟯)
        (d_bar' : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4),
        d_bar' = composePoissonHamiltonianTimeOneFlows (A := s4ADKAdmits) Sphere4 Hs ∧
        s4ADKFibration ∘ ⇑d_bar' = s4ADKFibration ∧
        π_f'.IsUnimodularWithVolume V'.Ω ∧
        IsTuringComplete ⇑d_bar' := by
  have hcrit : s4ADKCritBase ∈ criticalPoints (𝓡 4) (𝓡 2) s4ADKFibration := by
    rw [criticalPoints_s4ADKFibration]
    exact ⟨rfl, rfl, rfl⟩
  refine ⟨⟨s4ADKNorthFiberHomeomorph⟩, ⟨s4ADKTorusFiberHomeomorph⟩, hcrit,
    isIndefiniteFoldAt_s4ADKFibration hcrit, ?_, ?_⟩
  · obtain ⟨V, π_f, d_bar, _, hunimV, _, _, _, _, hfib, hpoiss, _, hpull, hmp, htc, hne⟩ :=
      exists_turingComplete_volumePreserving_poissonDiffeomorph_S4_ADK
    obtain ⟨hpos, hlt, -⟩ := positiveVolumeForm_s4_gate5 V
    exact ⟨V, π_f, d_bar, hpos, hlt, hunimV, hfib, hpoiss, hpull, hmp, htc, hne⟩
  · obtain ⟨V', π_f', Hs, d_bar', hunimV', hcomp, hfib, _, _, _, htc, _⟩ :=
      exists_poisson_hamiltonian_realization_S4_ADK
    exact ⟨V', π_f', Hs, d_bar', hcomp, hfib, hunimV', htc⟩

/-- **Unconditional Closed 4-Manifold Corollary 2 Check (`L-R3`, Track B) on `Sphere4`**:
Instantiates the zero-fibration-hypothesis closed-manifold theorems
(`exists_turingComplete_volumePreserving_poissonDiffeomorph_closedFourManifold`,
`undecidable_orbit_reachability_closedFourManifold`, and
`exists_poisson_hamiltonian_realization_closedFourManifold`) on `(Sphere4, S4PositiveVolumeForm)`,
verifying Gate 5 ball-volume bounds on the existential co-oriented volume `V`. -/
theorem unconditional_corollary2_closedFourManifold_on_S4_check :
    (∃ (V : PositiveVolumeForm (𝓡 4) Sphere4)
      (π_f : PoissonStructure (𝓡 4) Sphere4)
      (f : Sphere4 → Sphere2)
      (d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4),
      0 < V.μ (Metric.ball s4BasePoint (1 / 2)) ∧
      V.μ (Metric.ball s4BasePoint (1 / 2)) < V.μ Set.univ ∧
      (∀ x : Sphere4, ∃ a : ℝ, 0 < a ∧ V.Ω.1 x = a • S4PositiveVolumeForm.Ω.1 x) ∧
      π_f.IsUnimodularWithVolume V.Ω ∧
      f ∘ ⇑d_bar = f ∧
      MeasurePreserving ⇑d_bar V.μ V.μ ∧
      IsTuringComplete ⇑d_bar ∧
      (⇑d_bar : Sphere4 → Sphere4) ≠ id) ∧
    (∃ (V : PositiveVolumeForm (𝓡 4) Sphere4)
      (d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4)
      (U : Opens Sphere4)
      (chart : UnitDisk2 → Sphere4)
      (coord : Nat.Partrec.Code → UnitDisk2),
      MeasurePreserving ⇑d_bar V.μ V.μ ∧
      U.1.Nonempty ∧
      REPred (fun c : Nat.Partrec.Code ↦ ∃ n : ℕ, (⇑d_bar)^[n] (chart (coord c)) ∈ U) ∧
      ¬ ComputablePred (fun c : Nat.Partrec.Code ↦
        ∃ n : ℕ, (⇑d_bar)^[n] (chart (coord c)) ∈ U)) ∧
    ∃ (V' : PositiveVolumeForm (𝓡 4) Sphere4)
      (π_f' : PoissonStructure (𝓡 4) Sphere4)
      (f' : Sphere4 → Sphere2)
      (Hs : List C^∞⟮𝓡 4, Sphere4; ℝ⟯)
      (d_bar' : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4),
      π_f'.IsUnimodularWithVolume V'.Ω ∧
      d_bar' = composePoissonStructureTimeOneFlows Sphere4 π_f' Hs ∧
      f' ∘ ⇑d_bar' = f' ∧
      IsTuringComplete ⇑d_bar' := by
  have : Nonempty Sphere4 := ⟨s4BasePoint⟩
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨V, π_f, f, _, d_bar, _, hposΩ, hunimV, _, _, _, hf_comp, _, _, _, hmp, htc, hne⟩ :=
      Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_closedFourManifold
        Sphere4 S4PositiveVolumeForm
    obtain ⟨hpos, hlt, -⟩ := positiveVolumeForm_s4_gate5 V
    exact ⟨V, π_f, f, d_bar, hpos, hlt, hposΩ, hunimV, hf_comp, hmp, htc, hne⟩
  · obtain ⟨V, _, d_bar, U, _, _, _, _, chart, coord, _, _, _, _, _, _, hmp, hU, _, _, _, _, _, _,
        _, _, _, _, hre, hnotcomp, _⟩ :=
      Main.undecidable_orbit_reachability_closedFourManifold Sphere4 S4PositiveVolumeForm
    exact ⟨V, d_bar, U, chart, coord, hmp, hU, hre, hnotcomp⟩
  · obtain ⟨V', π_f', f', Hs, d_bar', _, hunimV', hcomp, hf_comp, _, _, _, htc, _⟩ :=
      exists_poisson_hamiltonian_realization_closedFourManifold Sphere4 S4PositiveVolumeForm
    exact ⟨V', π_f', f', Hs, d_bar', hunimV', hcomp, hf_comp, htc⟩

end LekiliAndADKChecks

end S4TuringPoisson.Checks
