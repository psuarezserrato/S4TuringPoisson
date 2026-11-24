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

public import S4TuringPoisson.Main
public import S4TuringPoisson.Smoothing.CMPP.Simulator
public import S4TuringPoisson.Fibration.ClosedManifoldLocal
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# Poisson–Hamiltonian Realization on Smooth 4-Manifolds and $S^4$ (CMPP Milestone P / R5)

This module formalizes Milestone P (`S4TuringPoisson/Extension/PoissonHamiltonian.lean`) of the
`CMPP21` Hamiltonian realization pipeline (`MISSION_DIRECTIVE_CMPP.md` §1 R5, §4.5, §7 and
`docs/cmpp/geometry_spec.md` §4.1–§4.2):

1. **Fiber & 4-Manifold Hamiltonian Lifting (`fiberHamiltonianOfPlanar`,
   `liftPlanarHamiltonianTo4Manifold`)**:
   - Rescales any `P : CompactlySupportedPlanarHamiltonian r₀` by `C.areaScale = C.radius ^ 2 > 0`
     across `C : SymplecticDiskChart F η` to obtain a smooth compactly supported fiber Hamiltonian
     `fiberHamiltonianOfPlanar C P : F → ℝ` satisfying `h_F (C.embed y) = C.areaScale * P.H (0, y)`.
   - Multiplies `h_F` along the local product trivialization `Φ : f ⁻¹' baseRegion ≃ₘ B × F` by
     `bumpProfile M ∘ A.fibration` and extends smoothly by `0` to
     `liftPlanarHamiltonianTo4Manifold M P : C^∞⟮𝓡 4, M; ℝ⟯`.

2. **Completeness & Time-`1` Poisson–Hamiltonian Flow Groupoid
   (`poissonHamiltonianTimeOneDiffeomorph`, `composePoissonHamiltonianTimeOneFlows`)**:
   - Proves completeness of `(adaptedJacobianPoisson M).hamiltonianVectorField H` on every compact
     Hausdorff smooth 4-manifold `M` and packages its time-`1` diffeomorphism and right-fold list
     composition.

3. **Leafwise-to-Poisson–Hamiltonian Time-`1` Flow Equivalence
   (`poissonHamiltonianTimeOneDiffeomorph_liftPlanarHamiltonian_eq`)**:
   - Uses Equation (1) on `innerPreimageOpen M`, vanishing of `f^*(dρ) ∧ f^* μ_B = f^*(dρ ∧ μ_B)`
     in degree `3 > 2` on `Sphere2`, sub-top-form contraction uniqueness, and ODE uniqueness for
     autonomous planar Hamiltonians to identify the time-`1` flow of
     `liftPlanarHamiltonianTo4Manifold M P` with
     `leafwiseBumpDiffeomorphOfIsotopy M P.toDiskIsotopy`.

4. **Deliverable R5 (`exists_poisson_hamiltonian_realization_S4`, Zero Typeclasses)**:
   - Combines `universalReversibleSimulator_cmpp` and
     `universalReversibleSimulator_cmpp_isAutonomous`
     to exhibit an unconditional Turing-complete, foliation-preserving, volume-preserving,
     measure-preserving Poisson diffeomorphism on `Sphere4` generated as a finite composition of
     time-`1` flows of smooth Poisson–Hamiltonian vector fields of `s4AdaptedPoisson`.
-/

@[expose] public section

open Bundle Filter Function MeasureTheory Metric Module Set TopologicalSpace
open S4TuringPoisson.Main
open scoped ContDiff Manifold Topology

namespace S4TuringPoisson

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

/-! ## 1. Surface & 4-Manifold Lifting of Planar Hamiltonians -/

/-- Lift the time-`0` slice of `P : CompactlySupportedPlanarHamiltonian r₀` through a
`SymplecticDiskChart F η`, scaled in the numerator by `C.areaScale = C.radius ^ 2` so that
`fiberHamiltonianOfPlanar C P (C.embed y) = C.areaScale * P.H (0, y.1)`, and extended by `0`
outside `C.sourceOpen`. -/
noncomputable def fiberHamiltonianOfPlanar
    {F : Type*} [TopologicalSpace F] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F]
    [IsManifold (𝓡 2) ∞ F] {η : TauCeti.SmoothTwoForm (𝓡 2) F}
    (C : SymplecticDiskChart F η) {r₀ : ℝ}
    (P : CompactlySupportedPlanarHamiltonian r₀) (z : F) : ℝ :=
  letI := Classical.dec (z ∈ C.sourceOpen.1)
  if z ∈ C.sourceOpen.1 then
    C.areaScale * P.H (0, C.radius⁻¹ • C.rawChart z)
  else
    0

/-- `fiberHamiltonianOfPlanar C P` vanishes outside the compact support image
`C.supportSet P.r₀_mem_Ioo.2`. -/
-- tier: T1
theorem fiberHamiltonianOfPlanar_eq_zero_of_notMem_supportSet
    {F : Type*} [TopologicalSpace F] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F]
    [IsManifold (𝓡 2) ∞ F] {η : TauCeti.SmoothTwoForm (𝓡 2) F}
    (C : SymplecticDiskChart F η) {r₀ : ℝ}
    (P : CompactlySupportedPlanarHamiltonian r₀) {z : F}
    (hz : z ∉ C.supportSet P.r₀_mem_Ioo.2) :
    fiberHamiltonianOfPlanar C P z = 0 := by
  by_cases hsrc : z ∈ C.sourceOpen.1
  · obtain ⟨y, rfl⟩ := C.range_embed.symm.subset hsrc
    have hy_not_ball : y.1 ∉ Metric.ball (0 : EuclideanPlane) r₀ := by
      intro hy_ball
      exact hz ⟨⟨y.1, Metric.ball_subset_closedBall hy_ball⟩, Set.mem_univ _, rfl⟩
    simp only [fiberHamiltonianOfPlanar, C.embed_mem_sourceOpen y, ↓reduceIte,
      C.rawChart_embed y, inv_smul_smul₀ C.radius_pos.ne',
      P.eq_zero_of_notMem_ball 0 y.1 hy_not_ball, mul_zero]
  · simp only [fiberHamiltonianOfPlanar, hsrc, ↓reduceIte]

/-- `fiberHamiltonianOfPlanar C P` is $C^\infty$ smooth on any Hausdorff surface `F`. -/
-- tier: T2
theorem contMDiff_fiberHamiltonianOfPlanar
    {F : Type*} [TopologicalSpace F] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F]
    [IsManifold (𝓡 2) ∞ F] [T2Space F] {η : TauCeti.SmoothTwoForm (𝓡 2) F}
    (C : SymplecticDiskChart F η) {r₀ : ℝ}
    (P : CompactlySupportedPlanarHamiltonian r₀) :
    ContMDiff (𝓡 2) 𝓘(ℝ) ∞ (fiberHamiltonianOfPlanar C P) := by
  intro z₀
  by_cases hz₀ : z₀ ∈ C.sourceOpen.1
  · have hraw : ContMDiffAt (𝓡 2) (𝓡 2) ∞ C.rawChart z₀ :=
      C.rawChart.contMDiffOn_toFun.contMDiffAt (C.rawChart.open_source.mem_nhds hz₀.1)
    have hscale : ContMDiffAt (𝓡 2) (𝓡 2) ∞ (fun z : F ↦ C.radius⁻¹ • C.rawChart z) z₀ :=
      (contDiff_planeScale C.radius⁻¹).contMDiff.contMDiffAt.comp z₀ hraw
    have hslice : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ (fun w : EuclideanPlane ↦ C.areaScale * P.H (0, w)) :=
      (contDiff_const.mul (P.contDiff_slice 0)).contMDiff
    refine ((hslice _).comp z₀ hscale).congr_of_eventuallyEq ?_
    filter_upwards [C.sourceOpen.2.mem_nhds hz₀] with z hz
    simp only [fiberHamiltonianOfPlanar, hz, ↓reduceIte, Function.comp_apply]
  · have hz₀_not : z₀ ∉ C.supportSet P.r₀_mem_Ioo.2 :=
      fun hmem ↦ hz₀ (C.supportSet_subset_sourceOpen P.r₀_mem_Ioo.2 hmem)
    have hclosed : IsClosed (C.supportSet P.r₀_mem_Ioo.2) :=
      (C.isCompact_supportSet P.r₀_mem_Ioo.2).isClosed
    refine (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hclosed.isOpen_compl.mem_nhds hz₀_not] with z hz
    exact fiberHamiltonianOfPlanar_eq_zero_of_notMem_supportSet C P hz

/-- Underlying scalar function `M → ℝ` lifting a `CompactlySupportedPlanarHamiltonian r₀` onto `M`
by multiplying `bumpProfile M ∘ A.fibration` with `fiberHamiltonianOfPlanar` on
`A.fibration.preimageOpen` and extending by `0` outside. -/
noncomputable def liftPlanarHamiltonianRaw
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [A : AdmitsRegularDiskFibration M]
    {r₀ : ℝ} (P : CompactlySupportedPlanarHamiltonian r₀) (x : M) : ℝ :=
  letI := A.instTopologicalSpaceFiber
  letI := A.instChartedSpaceFiber
  letI := A.instIsManifoldFiber
  letI := A.instT2SpaceFiber
  letI := A.instCompactSpaceFiber
  letI := A.instNonemptyFiber
  letI := A.instMeasurableSpaceFiber
  letI := A.instBorelSpaceFiber
  letI := Classical.dec (x ∈ A.fibration.preimageOpen.1)
  if hx : x ∈ A.fibration.preimageOpen.1 then
    bumpProfile M (A.fibration x) *
      fiberHamiltonianOfPlanar (AdmitsRegularDiskFibration.fiberDiskChart M) P
        (A.fibration.trivialization ⟨x, hx⟩).2
  else
    0

/-- Global $C^\infty$ smoothness of `liftPlanarHamiltonianRaw M P` across all of `M`. -/
-- tier: T2
theorem contMDiff_liftPlanarHamiltonianRaw
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [A : AdmitsRegularDiskFibration M]
    {r₀ : ℝ} (P : CompactlySupportedPlanarHamiltonian r₀) :
    ContMDiff (𝓡 4) 𝓘(ℝ) ∞ (liftPlanarHamiltonianRaw M P) := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := A.instMeasurableSpaceFiber
  let _ := A.instBorelSpaceFiber
  let C := AdmitsRegularDiskFibration.fiberDiskChart M
  let K : Set M := A.fibration ⁻¹' tsupport (bumpProfile M)
  have hK_closed : IsClosed K :=
    (isClosed_tsupport (bumpProfile M)).preimage A.fibration.contMDiff_toFun.continuous
  have hK_sub : K ⊆ A.fibration.preimageOpen.1 := fun y hy ↦
    tsupport_bumpProfile_subset_baseRegion M hy
  intro x
  by_cases hx : x ∈ A.fibration.preimageOpen.1
  · let g : A.fibration.preimageOpen → ℝ := fun u ↦
      bumpProfile M (A.fibration u.1) *
        fiberHamiltonianOfPlanar C P (A.fibration.trivialization u).2
    have hg : ContMDiff (𝓡 4) 𝓘(ℝ) ∞ g :=
      ((contMDiff_bumpProfile M).comp
        (A.fibration.contMDiff_toFun.comp contMDiff_subtype_val)).mul
        ((contMDiff_fiberHamiltonianOfPlanar C P).comp
          (contMDiff_snd.comp A.fibration.trivialization.contMDiff))
    have hcomp :
        liftPlanarHamiltonianRaw M P ∘ (Subtype.val : A.fibration.preimageOpen → M) = g :=
      funext fun u ↦ by
        let _ := Classical.dec (u.1 ∈ A.fibration.preimageOpen.1)
        exact dite_eq_left u.2
    refine ((TauCeti.isLocalDiffeomorph_subtype_val (I := 𝓡 4) (n := ∞)
      (⟨x, hx⟩ : A.fibration.preimageOpen)).contMDiffAt_comp_iff le_rfl).mp ?_
    rw [hcomp]
    exact hg ⟨x, hx⟩
  · have hx_notK : x ∉ K := fun hy ↦ hx (hK_sub hy)
    refine (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hK_closed.isOpen_compl.mem_nhds hx_notK] with y hy
    have hρ0 : bumpProfile M (A.fibration y) = 0 := image_eq_zero_of_notMem_tsupport hy
    let _ := Classical.dec (y ∈ A.fibration.preimageOpen.1)
    by_cases hy_pre : y ∈ A.fibration.preimageOpen.1
    · change (if h : y ∈ A.fibration.preimageOpen.1 then _ else 0) = 0
      rw [dite_eq_left hy_pre, hρ0, zero_mul]
    · change (if h : y ∈ A.fibration.preimageOpen.1 then _ else 0) = 0
      exact dite_eq_right hy_pre

/-- Lift an autonomous `CompactlySupportedPlanarHamiltonian r₀` to a smooth global Hamiltonian
`H̃ : C^∞⟮𝓡 4, M; ℝ⟯` on any 4-manifold `M` with `[A : AdmitsRegularDiskFibration M]`,
defined on `Φ⁻¹(b, C.embed y)` by `(bumpProfile M b * C.areaScale) * P.H (0, y)` and extended
smoothly by `0` outside `f ⁻¹' baseRegion` and `C.sourceOpen`. -/
noncomputable def liftPlanarHamiltonianTo4Manifold
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [A : AdmitsRegularDiskFibration M]
    {r₀ : ℝ} (P : CompactlySupportedPlanarHamiltonian r₀) :
    C^∞⟮𝓡 4, M; ℝ⟯ :=
  ⟨liftPlanarHamiltonianRaw M P, contMDiff_liftPlanarHamiltonianRaw M P⟩

/-! ## 2. Completeness & Time-`1` Poisson–Hamiltonian Flow Diffeomorphisms -/

/-- Completeness of the Poisson–Hamiltonian vector field
`(adaptedJacobianPoisson M).hamiltonianVectorField H` on a compact Hausdorff 4-manifold `M`. -/
-- tier: T2
theorem isComplete_hamiltonianVectorField_adaptedJacobianPoisson
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
    [A : AdmitsRegularDiskFibration M]
    (H : C^∞⟮𝓡 4, M; ℝ⟯) :
    TauCeti.IsCompleteVectorField
      (TauCeti.timeDependentSuspensionField fun _ : ℝ ↦
        (adaptedJacobianPoisson M).hamiltonianVectorField H) :=
  TauCeti.isCompleteVectorField_timeDependentSuspensionField
    ((((adaptedJacobianPoisson M).contMDiff_hamiltonianVectorField H).comp contMDiff_snd).of_le
      (by simp))
    isCompact_univ
    (fun _ _ hy ↦ (hy (Set.mem_univ _)).elim)

/-- Time-`1` flow diffeomorphism `M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M` generated by the Poisson–Hamiltonian vector
field `(adaptedJacobianPoisson M).hamiltonianVectorField H` on a compact Hausdorff 4-manifold
`M`. -/
noncomputable def poissonHamiltonianTimeOneDiffeomorph
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
    [A : AdmitsRegularDiskFibration M]
    (H : C^∞⟮𝓡 4, M; ℝ⟯) :
    M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M :=
  TauCeti.timeDependentFlowDiffeomorph
    (isComplete_hamiltonianVectorField_adaptedJacobianPoisson M H)
    (n := (⊤ : ℕ∞)) le_top
    (((adaptedJacobianPoisson M).contMDiff_hamiltonianVectorField H).comp contMDiff_snd)
    0 1

/-- Right-fold composition of the time-`1` Poisson–Hamiltonian flow diffeomorphisms for a finite
list of smooth Hamiltonians `Hs : List C^∞⟮𝓡 4, M; ℝ⟯`. -/
noncomputable def composePoissonHamiltonianTimeOneFlows
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
    [A : AdmitsRegularDiskFibration M] :
    List C^∞⟮𝓡 4, M; ℝ⟯ → (M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M)
  | [] => Diffeomorph.refl (𝓡 4) M ∞
  | H :: Hs => (composePoissonHamiltonianTimeOneFlows M Hs).trans
      (poissonHamiltonianTimeOneDiffeomorph M H)

/-- Completeness of `π_str.hamiltonianVectorField H` for any Poisson structure `π_str` on a
compact Hausdorff smooth 4-manifold `M`. -/
-- tier: T2
theorem isComplete_hamiltonianVectorField_poissonStructure
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
    (π_str : PoissonStructure (𝓡 4) M) (H : C^∞⟮𝓡 4, M; ℝ⟯) :
    TauCeti.IsCompleteVectorField
      (TauCeti.timeDependentSuspensionField fun _ : ℝ ↦ π_str.hamiltonianVectorField H) :=
  TauCeti.isCompleteVectorField_timeDependentSuspensionField
    (((π_str.contMDiff_hamiltonianVectorField H).comp contMDiff_snd).of_le (by simp))
    isCompact_univ
    (fun _ _ hy ↦ (hy (Set.mem_univ _)).elim)

/-- Time-`1` flow diffeomorphism `M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M` generated by
`π_str.hamiltonianVectorField H` for any Poisson structure `π_str` on compact Hausdorff `M`. -/
noncomputable def poissonStructureTimeOneDiffeomorph
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
    (π_str : PoissonStructure (𝓡 4) M) (H : C^∞⟮𝓡 4, M; ℝ⟯) :
    M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M :=
  TauCeti.timeDependentFlowDiffeomorph
    (isComplete_hamiltonianVectorField_poissonStructure M π_str H)
    (n := (⊤ : ℕ∞)) le_top
    ((π_str.contMDiff_hamiltonianVectorField H).comp contMDiff_snd)
    0 1

/-- Right-fold composition of time-`1` Poisson–Hamiltonian flow diffeomorphisms for an arbitrary
Poisson structure `π_str` on compact Hausdorff `M`. -/
noncomputable def composePoissonStructureTimeOneFlows
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
    (π_str : PoissonStructure (𝓡 4) M) :
    List C^∞⟮𝓡 4, M; ℝ⟯ → (M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M)
  | [] => Diffeomorph.refl (𝓡 4) M ∞
  | H :: Hs => (composePoissonStructureTimeOneFlows M π_str Hs).trans
      (poissonStructureTimeOneDiffeomorph M π_str H)

/-- Compatibility between generic `composePoissonStructureTimeOneFlows` specialized to
`adaptedJacobianPoisson M` and `composePoissonHamiltonianTimeOneFlows M`. -/
-- tier: T2
theorem composePoissonStructureTimeOneFlows_adaptedJacobianPoisson
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
    [A : AdmitsRegularDiskFibration M] (Hs : List C^∞⟮𝓡 4, M; ℝ⟯) :
    composePoissonStructureTimeOneFlows M (adaptedJacobianPoisson M) Hs =
      composePoissonHamiltonianTimeOneFlows M Hs := by
  induction Hs with
  | nil => rfl
  | cons H Hs ih =>
    change (composePoissonStructureTimeOneFlows M (adaptedJacobianPoisson M) Hs).trans
        (poissonStructureTimeOneDiffeomorph M (adaptedJacobianPoisson M) H) =
      (composePoissonHamiltonianTimeOneFlows M Hs).trans
        (poissonHamiltonianTimeOneDiffeomorph M H)
    rw [ih]
    rfl

/-! ## 3. Basic Evaluation & Simp Projections -/

/-- On `C.sourceOpen`, `fiberHamiltonianOfPlanar C P z` evaluates to
`C.areaScale * P.H (0, C.radius⁻¹ • C.rawChart z)`. -/
-- tier: T0
theorem fiberHamiltonianOfPlanar_of_mem
    {F : Type*} [TopologicalSpace F] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F]
    [IsManifold (𝓡 2) ∞ F] {η : TauCeti.SmoothTwoForm (𝓡 2) F}
    (C : SymplecticDiskChart F η) {r₀ : ℝ}
    (P : CompactlySupportedPlanarHamiltonian r₀) {z : F} (hz : z ∈ C.sourceOpen.1) :
    fiberHamiltonianOfPlanar C P z = C.areaScale * P.H (0, C.radius⁻¹ • C.rawChart z) := by
  simp only [fiberHamiltonianOfPlanar, hz, ↓reduceIte]

/-- Outside `C.sourceOpen`, `fiberHamiltonianOfPlanar C P z` vanishes. -/
-- tier: T0
theorem fiberHamiltonianOfPlanar_of_notMem
    {F : Type*} [TopologicalSpace F] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F]
    [IsManifold (𝓡 2) ∞ F] {η : TauCeti.SmoothTwoForm (𝓡 2) F}
    (C : SymplecticDiskChart F η) {r₀ : ℝ}
    (P : CompactlySupportedPlanarHamiltonian r₀) {z : F} (hz : z ∉ C.sourceOpen.1) :
    fiberHamiltonianOfPlanar C P z = 0 := by
  simp only [fiberHamiltonianOfPlanar, hz, ↓reduceIte]

/-- Along `C.embed y` (`y : diskOpen`), `fiberHamiltonianOfPlanar C P (C.embed y)` equals
`C.areaScale * P.H (0, y.1)`. -/
-- tier: T0
theorem fiberHamiltonianOfPlanar_embed
    {F : Type*} [TopologicalSpace F] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F]
    [IsManifold (𝓡 2) ∞ F] {η : TauCeti.SmoothTwoForm (𝓡 2) F}
    (C : SymplecticDiskChart F η) {r₀ : ℝ}
    (P : CompactlySupportedPlanarHamiltonian r₀) (y : diskOpen) :
    fiberHamiltonianOfPlanar C P (C.embed y) = C.areaScale * P.H (0, y.1) := by
  rw [fiberHamiltonianOfPlanar_of_mem C P (C.embed_mem_sourceOpen y), C.rawChart_embed y,
    inv_smul_smul₀ C.radius_pos.ne']

/-- Coercion of `liftPlanarHamiltonianTo4Manifold M P` to a function equals
`liftPlanarHamiltonianRaw M P`. -/
-- tier: T0
@[simp]
theorem coe_liftPlanarHamiltonianTo4Manifold
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [A : AdmitsRegularDiskFibration M]
    {r₀ : ℝ} (P : CompactlySupportedPlanarHamiltonian r₀) :
    ⇑(liftPlanarHamiltonianTo4Manifold M P) = liftPlanarHamiltonianRaw M P :=
  by
  unfold liftPlanarHamiltonianTo4Manifold
  rcases liftPlanarHamiltonianTo4Manifold M P with ⟨f, hf⟩
  ext x
  rfl

/-- Pointwise evaluation of `poissonHamiltonianTimeOneDiffeomorph M H` as the time-`1` flow of
`(adaptedJacobianPoisson M).hamiltonianVectorField H`. -/
-- tier: T0
@[simp]
theorem poissonHamiltonianTimeOneDiffeomorph_apply
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
    [A : AdmitsRegularDiskFibration M]
    (H : C^∞⟮𝓡 4, M; ℝ⟯) (x : M) :
    poissonHamiltonianTimeOneDiffeomorph M H x =
      TauCeti.timeDependentFlowOf
        (fun _ : ℝ ↦ (adaptedJacobianPoisson M).hamiltonianVectorField H) 0 1 x :=
  by
  simp [poissonHamiltonianTimeOneDiffeomorph]

/-- Pointwise evaluation of `(poissonHamiltonianTimeOneDiffeomorph M H).symm` as the backward
flow from `t = 1` to `t = 0`. -/
-- tier: T0
@[simp]
theorem poissonHamiltonianTimeOneDiffeomorph_symm_apply
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
    [A : AdmitsRegularDiskFibration M]
    (H : C^∞⟮𝓡 4, M; ℝ⟯) (x : M) :
    (poissonHamiltonianTimeOneDiffeomorph M H).symm x =
      TauCeti.timeDependentFlowOf
        (fun _ : ℝ ↦ (adaptedJacobianPoisson M).hamiltonianVectorField H) 1 0 x := by
  simp [poissonHamiltonianTimeOneDiffeomorph]

/-- Right-fold composition on the empty Hamiltonian list `[]` is `Diffeomorph.refl`. -/
-- tier: T0
@[simp]
theorem composePoissonHamiltonianTimeOneFlows_nil
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
    [A : AdmitsRegularDiskFibration M] :
    composePoissonHamiltonianTimeOneFlows M [] = Diffeomorph.refl (𝓡 4) M ∞ :=
  by
  rfl

/-- Right-fold composition step for `H :: Hs`: applies `composePoissonHamiltonianTimeOneFlows M Hs`
followed by `poissonHamiltonianTimeOneDiffeomorph M H`. -/
-- tier: T0
@[simp]
theorem composePoissonHamiltonianTimeOneFlows_cons
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
    [A : AdmitsRegularDiskFibration M]
    (H : C^∞⟮𝓡 4, M; ℝ⟯) (Hs : List C^∞⟮𝓡 4, M; ℝ⟯) :
    composePoissonHamiltonianTimeOneFlows M (H :: Hs) =
      (composePoissonHamiltonianTimeOneFlows M Hs).trans
        (poissonHamiltonianTimeOneDiffeomorph M H) := by
  rfl

/-! ## 4. Trivialized Evaluation & Leafwise Bump Composition Groupoid -/

/-- Along `A.fibration.embed (b, z)`, `liftPlanarHamiltonianTo4Manifold M P` evaluates to
`bumpProfile M b.1 * fiberHamiltonianOfPlanar (fiberDiskChart M) P z`. -/
-- tier: T1
theorem liftPlanarHamiltonianTo4Manifold_embed
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [A : AdmitsRegularDiskFibration M]
    {r₀ : ℝ} (P : CompactlySupportedPlanarHamiltonian r₀)
    (b :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      A.fibration.baseRegion)
    (z : A.Fiber) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    letI := A.instMeasurableSpaceFiber
    letI := A.instBorelSpaceFiber
    liftPlanarHamiltonianTo4Manifold M P (A.fibration.embed (b, z)) =
      bumpProfile M b.1 *
        fiberHamiltonianOfPlanar
          (AdmitsRegularDiskFibration.fiberDiskChart M) P z := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := A.instMeasurableSpaceFiber
  let _ := A.instBorelSpaceFiber
  let u := A.fibration.trivialization.symm (b, z)
  have hmem : A.fibration.embed (b, z) ∈ A.fibration.preimageOpen.1 := u.2
  rw [coe_liftPlanarHamiltonianTo4Manifold]
  let _ := Classical.dec (A.fibration.embed (b, z) ∈ A.fibration.preimageOpen.1)
  change (if hx : A.fibration.embed (b, z) ∈ A.fibration.preimageOpen.1 then _ else 0) = _
  rw [dite_eq_left hmem, A.fibration.apply_embed b z]
  have hu : (⟨A.fibration.embed (b, z), hmem⟩ : A.fibration.preimageOpen) = u := rfl
  rw [hu, A.fibration.trivialization.apply_symm_apply]

/-- Along `A.fibration.embed (b, C.embed y)`, `liftPlanarHamiltonianTo4Manifold M P` evaluates to
`(bumpProfile M b.1 * C.areaScale) * P.H (0, y.1)` with sign `+1` and `C.areaScale` in the
numerator (`docs/cmpp/geometry_spec.md` §4.1). -/
-- tier: T1
theorem liftPlanarHamiltonianTo4Manifold_embed_disk
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [A : AdmitsRegularDiskFibration M]
    {r₀ : ℝ} (P : CompactlySupportedPlanarHamiltonian r₀)
    (b :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      A.fibration.baseRegion)
    (y : diskOpen) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    letI := A.instMeasurableSpaceFiber
    letI := A.instBorelSpaceFiber
    let C := AdmitsRegularDiskFibration.fiberDiskChart M
    liftPlanarHamiltonianTo4Manifold M P (A.fibration.embed (b, C.embed y)) =
      (bumpProfile M b.1 * C.areaScale) * P.H (0, y.1) := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := A.instMeasurableSpaceFiber
  let _ := A.instBorelSpaceFiber
  intro C
  rw [liftPlanarHamiltonianTo4Manifold_embed M P b (C.embed y), fiberHamiltonianOfPlanar_embed,
    mul_assoc]

/-- Lifting the identity disk isotopy `AreaPreservingDiskIsotopy.refl hr₀` to a surface slice
yields `Diffeomorph.refl`. -/
-- tier: T1
@[simp]
theorem SymplecticDiskChart.liftIsotopyDiffeomorph_refl
    {F : Type*} [TopologicalSpace F] [ChartedSpace EuclideanPlane F]
    [IsManifold (𝓡 2) ∞ F] [T2Space F] {η : TauCeti.SmoothTwoForm (𝓡 2) F}
    (C : SymplecticDiskChart F η) {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1) (t : ℝ) :
    C.liftIsotopyDiffeomorph (AreaPreservingDiskIsotopy.refl hr₀) t =
      Diffeomorph.refl (𝓡 2) F ∞ := by
  ext z
  by_cases hz : z ∈ C.sourceOpen.1
  · obtain ⟨y, rfl⟩ := C.range_embed.symm.subset hz
    exact C.liftIsotopyDiffeomorph_embed (AreaPreservingDiskIsotopy.refl hr₀) t y
  · exact C.liftThroughChart_of_notMem _ t hz

/-- Lifting a composed disk isotopy `I₂.compSame I₁` to a surface slice composes the lifted
diffeomorphisms in `Diffeomorph.trans` order (`I₁` followed by `I₂`). -/
-- tier: T1
theorem SymplecticDiskChart.liftIsotopyDiffeomorph_compSame
    {F : Type*} [TopologicalSpace F] [ChartedSpace EuclideanPlane F]
    [IsManifold (𝓡 2) ∞ F] [T2Space F] {η : TauCeti.SmoothTwoForm (𝓡 2) F}
    (C : SymplecticDiskChart F η) {r₀ : ℝ} (I₂ I₁ : AreaPreservingDiskIsotopy r₀) (t : ℝ) :
    C.liftIsotopyDiffeomorph (I₂.compSame I₁) t =
      (C.liftIsotopyDiffeomorph I₁ t).trans (C.liftIsotopyDiffeomorph I₂ t) := by
  ext z
  by_cases hz : z ∈ C.sourceOpen.1
  · obtain ⟨y, rfl⟩ := C.range_embed.symm.subset hz
    rw [C.liftIsotopyDiffeomorph_embed (I₂.compSame I₁) t y, Diffeomorph.coe_trans,
      Function.comp_apply, C.liftIsotopyDiffeomorph_embed I₁ t y,
      C.liftIsotopyDiffeomorph_embed I₂ t]
    rfl
  · rw [Diffeomorph.coe_trans, Function.comp_apply, C.liftIsotopyDiffeomorph_apply,
      C.liftIsotopyDiffeomorph_apply, C.liftIsotopyDiffeomorph_apply,
      C.liftThroughChart_of_notMem _ t hz, C.liftThroughChart_of_notMem _ t hz,
      C.liftThroughChart_of_notMem _ t hz]

/-- Lifting the identity disk isotopy `AreaPreservingDiskIsotopy.refl hr₀` to a 4-manifold `M`
yields `Diffeomorph.refl (𝓡 4) M ∞`. -/
-- tier: T1
@[simp]
theorem leafwiseBumpDiffeomorphOfIsotopy_refl
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [A : AdmitsRegularDiskFibration M]
    {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1) :
    leafwiseBumpDiffeomorphOfIsotopy M (AreaPreservingDiskIsotopy.refl hr₀) =
      Diffeomorph.refl (𝓡 4) M ∞ := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := A.instMeasurableSpaceFiber
  let _ := A.instBorelSpaceFiber
  ext x
  by_cases hx : x ∈ A.fibration.preimageOpen.1
  · let u : A.fibration.preimageOpen := ⟨x, hx⟩
    let bz := A.fibration.trivialization u
    have hx_eq : x = A.fibration.embed (bz.1, bz.2) := by
      change u.1 = (A.fibration.trivialization.symm (bz.1, bz.2)).1
      rw [Prod.mk.eta, A.fibration.trivialization.symm_apply_apply]
    rw [hx_eq, leafwiseBumpDiffeomorphOfIsotopy_embed M (AreaPreservingDiskIsotopy.refl hr₀)
      bz.1 bz.2, SymplecticDiskChart.liftIsotopyDiffeomorph_refl]
    rfl
  · exact leafwiseBumpDiffeomorphOfIsotopy_of_notMem M (AreaPreservingDiskIsotopy.refl hr₀) hx

/-- Lifting a composed disk isotopy `I₂.compSame I₁` to a 4-manifold `M` equals the
`Diffeomorph.trans` composition `(leafwiseBumpDiffeomorphOfIsotopy M I₁).trans
(leafwiseBumpDiffeomorphOfIsotopy M I₂)`. -/
-- tier: T1
theorem leafwiseBumpDiffeomorphOfIsotopy_compSame
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [A : AdmitsRegularDiskFibration M]
    {r₀ : ℝ} (I₂ I₁ : AreaPreservingDiskIsotopy r₀) :
    leafwiseBumpDiffeomorphOfIsotopy M (I₂.compSame I₁) =
      (leafwiseBumpDiffeomorphOfIsotopy M I₁).trans
        (leafwiseBumpDiffeomorphOfIsotopy M I₂) := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := A.instMeasurableSpaceFiber
  let _ := A.instBorelSpaceFiber
  ext x
  by_cases hx : x ∈ A.fibration.preimageOpen.1
  · let u : A.fibration.preimageOpen := ⟨x, hx⟩
    let bz := A.fibration.trivialization u
    have hx_eq : x = A.fibration.embed (bz.1, bz.2) := by
      change u.1 = (A.fibration.trivialization.symm (bz.1, bz.2)).1
      rw [Prod.mk.eta, A.fibration.trivialization.symm_apply_apply]
    rw [hx_eq, Diffeomorph.coe_trans, Function.comp_apply,
      leafwiseBumpDiffeomorphOfIsotopy_embed M (I₂.compSame I₁) bz.1 bz.2,
      leafwiseBumpDiffeomorphOfIsotopy_embed M I₁ bz.1 bz.2,
      leafwiseBumpDiffeomorphOfIsotopy_embed M I₂ bz.1,
      SymplecticDiskChart.liftIsotopyDiffeomorph_compSame]
    rfl
  · have hx₁ : leafwiseBumpDiffeomorphOfIsotopy M I₁ x = x :=
      leafwiseBumpDiffeomorphOfIsotopy_of_notMem M I₁ hx
    rw [Diffeomorph.coe_trans, Function.comp_apply, hx₁,
      leafwiseBumpDiffeomorphOfIsotopy_of_notMem M I₂ hx,
      leafwiseBumpDiffeomorphOfIsotopy_of_notMem M (I₂.compSame I₁) hx]

/-- Any `AreaPreservingDiskIsotopy` with `diskTimeOneMap ≠ id` lifts via
`leafwiseBumpDiffeomorphOfIsotopy` to a non-identity diffeomorphism of `M`. -/
-- tier: T1
theorem leafwiseBumpDiffeomorphOfIsotopy_ne_refl_of_diskTimeOneMap_ne_id
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [A : AdmitsRegularDiskFibration M]
    {r₀ : ℝ} {I_disk : AreaPreservingDiskIsotopy r₀}
    (hne : I_disk.diskTimeOneMap ≠ id) :
    leafwiseBumpDiffeomorphOfIsotopy M I_disk ≠ Diffeomorph.refl (𝓡 4) M ∞ := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := A.instMeasurableSpaceFiber
  let _ := A.instBorelSpaceFiber
  intro hrefl
  apply hne
  funext y
  let C := AdmitsRegularDiskFibration.fiberDiskChart M
  let b₀ := A.fibration.baseCenter
  have hb₀ : b₀.1 ∈ (baseCoreOpen M).1 := baseCenter_mem_baseCoreOpen M
  have hρ1 : bumpProfile M b₀.1 = 1 := bumpProfile_eq_one_of_mem_baseCoreOpen M hb₀
  let x₀ : M := A.fibration.embed (b₀, C.embed ⟨y.1, y.2⟩)
  have hx₀ : leafwiseBumpDiffeomorphOfIsotopy M I_disk x₀ = x₀ :=
    congrArg (fun φ : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M ↦ φ x₀) hrefl
  dsimp only [x₀] at hx₀
  rw [leafwiseBumpDiffeomorphOfIsotopy_embed M I_disk b₀ (C.embed ⟨y.1, y.2⟩),
    hρ1, C.liftIsotopyDiffeomorph_embed I_disk 1 ⟨y.1, y.2⟩] at hx₀
  have hinj_emb := A.fibration.isOpenEmbedding_embed.injective hx₀
  have hinj_C := C.injective_embed (Prod.mk.inj hinj_emb).2
  exact Subtype.ext (congrArg Subtype.val hinj_C)

/-! ## 5. Pointwise Poisson–Hamiltonian Vector Field & Time-`1` ODE Equivalence -/

/-- Any `1 ∧ 2` alternating wedge expression on the `2`-dimensional plane `EuclideanPlane`
vanishes identically (`finrank ℝ EuclideanPlane = 2 < 3`). -/
-- tier: T1
theorem wedge_one_two_plane_eq_zero (ℓ : EuclideanPlane →L[ℝ] ℝ)
    (ω_B : EuclideanPlane [⋀^Fin 2]→L[ℝ] ℝ) (u₀ u₁ u₂ : EuclideanPlane) :
    ℓ u₀ * ω_B ![u₁, u₂] - ℓ u₁ * ω_B ![u₀, u₂] + ℓ u₂ * ω_B ![u₀, u₁] = 0 := by
  let α : EuclideanPlane [⋀^Fin 1]→L[ℝ] ℝ :=
    ContinuousAlternatingMap.ofSubsingleton ℝ EuclideanPlane ℝ (0 : Fin 1) ℓ
  have htop : ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
      (ContinuousLinearMap.mul ℝ ℝ).continuous₂ α ω_B = 0 := by
    refine ContinuousAlternatingMap.eq_zero_of_finrank_lt _ ?_
    rw [finrank_euclideanSpace_fin, Fintype.card_fin]
    omega
  have h0 : ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
      (ContinuousLinearMap.mul ℝ ℝ).continuous₂ α ω_B ![u₀, u₁, u₂] = 0 := by
    rw [htop]
    rfl
  rw [pairedWedge_one_two_apply] at h0
  simpa only [α, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
    Matrix.cons_val_zero] using h0

/-- Congruence in the left factors of a `3`-term alternating sum `a₀ m₀ - a₁ m₁ + a₂ m₂`. -/
-- tier: T1
theorem threeTermAlt_congr_left {a₀ a₁ a₂ b₀ b₁ b₂ m₀ m₁ m₂ : ℝ}
    (ha0 : a₀ = b₀) (ha1 : a₁ = b₁) (ha2 : a₂ = b₂) :
    a₀ * m₀ - a₁ * m₁ + a₂ * m₂ = b₀ * m₀ - b₁ * m₁ + b₂ * m₂ := by
  subst ha0; subst ha1; subst ha2; rfl

/-- Congruence in the right factors of a `3`-term alternating sum `a₀ m₀ - a₁ m₁ + a₂ m₂`. -/
-- tier: T1
theorem threeTermAlt_congr_right {a₀ a₁ a₂ m₀ m₁ m₂ n₀ n₁ n₂ : ℝ}
    (hm0 : m₀ = n₀) (hm1 : m₁ = n₁) (hm2 : m₂ = n₂) :
    a₀ * m₀ - a₁ * m₁ + a₂ * m₂ = a₀ * n₀ - a₁ * n₁ + a₂ * n₂ := by
  subst hm0; subst hm1; subst hm2; rfl

/-- Congruence in both factors of a `3`-term alternating sum `a₀ m₀ - a₁ m₁ + a₂ m₂`. -/
-- tier: T1
theorem threeTermAlt_congr {a₀ a₁ a₂ b₀ b₁ b₂ m₀ m₁ m₂ n₀ n₁ n₂ : ℝ}
    (ha0 : a₀ = b₀) (ha1 : a₁ = b₁) (ha2 : a₂ = b₂)
    (hm0 : m₀ = n₀) (hm1 : m₁ = n₁) (hm2 : m₂ = n₂) :
    a₀ * m₀ - a₁ * m₁ + a₂ * m₂ = b₀ * n₀ - b₁ * n₁ + b₂ * n₂ := by
  subst ha0; subst ha1; subst ha2; subst hm0; subst hm1; subst hm2; rfl

/-- Adding a vanishing `3`-term alternating combination `(c₀ m₀ - c₁ m₁ + c₂ m₂ = 0)` to the left
factors leaves `a₀ m₀ - a₁ m₁ + a₂ m₂` unchanged. -/
-- tier: T1
theorem threeTermAlt_add_left_of_eq_zero {c₀ c₁ c₂ a₀ a₁ a₂ m₀ m₁ m₂ : ℝ}
    (hc : c₀ * m₀ - c₁ * m₁ + c₂ * m₂ = 0) :
    a₀ * m₀ - a₁ * m₁ + a₂ * m₂ =
      (c₀ + a₀) * m₀ - (c₁ + a₁) * m₁ + (c₂ + a₂) * m₂ := by
  linarith

/-- Contracting a `2 ∧ 2` alternating paired wedge `φ ∧ ψ` in slot `0` with a vector `v` that
annihilates `ψ` (`ψ ![v, u] = 0` for all `u`) yields the `1 ∧ 2` alternating expansion
`(ι_v φ) ∧ ψ`. -/
-- tier: T1
theorem pairedWedge_two_two_vecCons_of_right_zero
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (φ ψ : E [⋀^Fin 2]→L[ℝ] ℝ) (v : E) (w : Fin 3 → E)
    (hψ0 : ∀ u : E, ψ ![v, u] = 0) :
    ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
        (ContinuousLinearMap.mul ℝ ℝ).continuous₂ φ ψ (Matrix.vecCons v w) =
      φ ![v, w 0] * ψ ![w 1, w 2] -
        φ ![v, w 1] * ψ ![w 0, w 2] +
        φ ![v, w 2] * ψ ![w 0, w 1] := by
  have h1 := ContinuousAlternatingMap.curryLeftTopological_pairedWedge (k := 1) (l := 1)
    (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ φ ψ v w
  rw [ContinuousAlternatingMap.curryLeftTopological_apply_apply] at h1
  have hψ_curry : ContinuousAlternatingMap.curryLeftTopological (n := 1) ψ v = 0 := by
    ext u
    rw [ContinuousAlternatingMap.curryLeftTopological_apply_apply]
    have hu : Matrix.vecCons v u = ![v, u 0] := by
      funext i
      fin_cases i <;> rfl
    rw [hu]
    exact hψ0 (u 0)
  have hcast :
      (w ∘ Fin.cast (show 1 + (1 + 1) = 1 + 1 + 1 by omega)) = ![w 0, w 1, w 2] := by
    funext j
    fin_cases j <;> rfl
  have hz0 :
      (0 : E [⋀^Fin (1 + 1 + 1)]→L[ℝ] ℝ) w = 0 := rfl
  rw [h1, hψ_curry, ContinuousAlternatingMap.pairedWedge_zero_right, hz0,
    smul_zero, add_zero, hcast, pairedWedge_one_two_apply]
  simp only [ContinuousAlternatingMap.curryLeftTopological_apply_apply]

/-- Darboux symplectic contraction on `(F, η)`: pushing `P.vectorField 0 y.1` forward along
`C.embed : diskOpen → F` contracts `η` to `d(fiberHamiltonianOfPlanar C P)`. -/
-- tier: T2
theorem symplecticDiskChart_apply_mfderiv_embed_vectorField
    {F : Type*} [TopologicalSpace F] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F]
    [IsManifold (𝓡 2) ∞ F] [T2Space F] {η : TauCeti.SmoothTwoForm (𝓡 2) F}
    (C : SymplecticDiskChart F η) {r₀ : ℝ}
    (P : CompactlySupportedPlanarHamiltonian r₀) (y : diskOpen)
    (v_F : TangentSpace (𝓡 2) (C.embed y)) :
    let v_disk : TangentSpace (𝓡 2) y :=
      (TauCeti.Manifold.tangentSpaceOpenEquiv (I := 𝓡 2) y).symm (P.vectorField 0 y.1)
    η.1 (C.embed y) ![mfderiv (𝓡 2) (𝓡 2) C.embed y v_disk, v_F] =
      mvfderiv (𝓡 2) (fiberHamiltonianOfPlanar C P) (C.embed y) v_F := by
  intro v_disk
  have hsurj : Function.Surjective (mfderiv (𝓡 2) (𝓡 2) C.embed y) :=
    (C.isLocalDiffeomorph_embed.isInvertible_mfderiv (by simp) y).surjective
  obtain ⟨w_disk, rfl⟩ := hsurj v_F
  have hvec :
      (![mfderiv (𝓡 2) (𝓡 2) C.embed y v_disk, mfderiv (𝓡 2) (𝓡 2) C.embed y w_disk] :
          Fin 2 → TangentSpace (𝓡 2) (C.embed y)) =
        fun i ↦ mfderiv (𝓡 2) (𝓡 2) C.embed y (![v_disk, w_disk] i) := by
    funext i
    fin_cases i <;> rfl
  let w_plane : TangentSpace (𝓡 2) y.1 :=
    TauCeti.Manifold.tangentSpaceOpenEquiv (I := 𝓡 2) y w_disk
  have hlhs :
      η.1 (C.embed y) ![mfderiv (𝓡 2) (𝓡 2) C.embed y v_disk,
          mfderiv (𝓡 2) (𝓡 2) C.embed y w_disk] =
        C.areaScale * mvfderiv (𝓡 2) (P.slice 0) y.1 w_plane := by
    rw [hvec, ← TauCeti.SmoothForm.mpullback_apply C.embed C.contMDiff_embed η y ![v_disk, w_disk],
      C.mpullback_embed_eq, Submodule.coe_smul, Pi.smul_apply,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul,
      TauCeti.SmoothForm.mpullback_apply]
    have hsub_vec :
        (fun i : Fin 2 ↦
            mfderiv (𝓡 2) (𝓡 2) (Subtype.val : diskOpen → EuclideanPlane) y
              (![v_disk, w_disk] i)) =
          ![P.vectorField 0 y.1, w_plane] := by
      funext i
      rw [TauCeti.Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe]
      fin_cases i
      · exact (TauCeti.Manifold.tangentSpaceOpenEquiv (I := 𝓡 2) y).apply_symm_apply
          (P.vectorField 0 y.1)
      · rfl
    rw [hsub_vec]
    exact congrArg (C.areaScale * ·)
      (isSymplectic_planeAreaForm.isNondegenerate.apply_hamiltonianVectorField
        (P.slice 0) y.1 w_plane)
  have hf_diff : MDifferentiableAt (𝓡 2) 𝓘(ℝ) (fiberHamiltonianOfPlanar C P) (C.embed y) :=
    ((contMDiff_fiberHamiltonianOfPlanar C P) (C.embed y)).mdifferentiableAt (by simp)
  have hemb_diff : MDifferentiableAt (𝓡 2) (𝓡 2) C.embed y :=
    (C.contMDiff_embed y).mdifferentiableAt (by simp)
  have hcomp_eq :
      (fiberHamiltonianOfPlanar C P) ∘ C.embed =
        ((C.areaScale • P.slice 0 : EuclideanPlane → ℝ) ∘
          (Subtype.val : diskOpen → EuclideanPlane)) := by
    funext y'
    simp only [Function.comp_apply, fiberHamiltonianOfPlanar_embed, Pi.smul_apply,
      CompactlySupportedPlanarHamiltonian.slice, smul_eq_mul]
  have hrhs :
      mvfderiv (𝓡 2) (fiberHamiltonianOfPlanar C P) (C.embed y)
          (mfderiv (𝓡 2) (𝓡 2) C.embed y w_disk) =
        C.areaScale * mvfderiv (𝓡 2) (P.slice 0) y.1 w_plane := by
    rw [← mvfderiv_comp_apply y hf_diff hemb_diff w_disk, hcomp_eq]
    have hsc_diff : MDifferentiableAt (𝓡 2) 𝓘(ℝ) (C.areaScale • P.slice 0) y.1 :=
      (((contDiff_const.mul (P.contDiff_slice 0)).contMDiff) y.1).mdifferentiableAt (by simp)
    rw [mvfderiv_comp_apply y hsc_diff
        ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)) w_disk,
      TauCeti.Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
      TauCeti.mvfderiv_const_smul_field, smul_apply, smul_eq_mul]
  exact hlhs.trans hrhs.symm

/-- Whenever `H : C^∞⟮𝓡 4, M; ℝ⟯` vanishes in a neighborhood of `x`, its Jacobian–Poisson
Hamiltonian vector field vanishes at `x`. -/
-- tier: T1
theorem hamiltonianVectorField_adaptedJacobianPoisson_eq_zero_of_eventuallyEq
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
    [A : AdmitsRegularDiskFibration M]
    {H : C^∞⟮𝓡 4, M; ℝ⟯} {x : M}
    (hev : (⇑H : M → ℝ) =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ)) :
    (adaptedJacobianPoisson M).hamiltonianVectorField H x = 0 := by
  have hd : mvfderiv (𝓡 4) H x = 0 := by
    rw [hev.mvfderiv_eq, mvfderiv_const]
  rw [SmoothBivector.hamiltonianVectorField, hd, map_zero, neg_zero]

/-- `(adaptedJacobianPoisson M).hamiltonianVectorField (liftPlanarHamiltonianTo4Manifold M P)`
vanishes at every point `x : M` with `A.fibration x ∉ tsupport (bumpProfile M)`. -/
-- tier: T1
theorem hamiltonianVectorField_liftPlanarHamiltonian_eq_zero_of_notMem_tsupport_base
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
    [A : AdmitsRegularDiskFibration M]
    {r₀ : ℝ} (P : CompactlySupportedPlanarHamiltonian r₀) {x : M}
    (hx :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      A.fibration x ∉ tsupport (bumpProfile M)) :
    (adaptedJacobianPoisson M).hamiltonianVectorField
      (liftPlanarHamiltonianTo4Manifold M P) x = 0 := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := A.instMeasurableSpaceFiber
  let _ := A.instBorelSpaceFiber
  let K : Set M := A.fibration ⁻¹' tsupport (bumpProfile M)
  have hK_closed : IsClosed K :=
    (isClosed_tsupport (bumpProfile M)).preimage A.fibration.contMDiff_toFun.continuous
  refine hamiltonianVectorField_adaptedJacobianPoisson_eq_zero_of_eventuallyEq M ?_
  filter_upwards [hK_closed.isOpen_compl.mem_nhds hx] with y hy
  rw [coe_liftPlanarHamiltonianTo4Manifold]
  have hρ0 : bumpProfile M (A.fibration y) = 0 := image_eq_zero_of_notMem_tsupport hy
  let _ := Classical.dec (y ∈ A.fibration.preimageOpen.1)
  by_cases hy_pre : y ∈ A.fibration.preimageOpen.1
  · change (if h : y ∈ A.fibration.preimageOpen.1 then _ else 0) = 0
    rw [dite_eq_left hy_pre, hρ0, zero_mul]
  · change (if h : y ∈ A.fibration.preimageOpen.1 then _ else 0) = 0
    exact dite_eq_right hy_pre

/-- `(adaptedJacobianPoisson M).hamiltonianVectorField (liftPlanarHamiltonianTo4Manifold M P)`
vanishes at `A.fibration.embed (b, z)` whenever `z ∉ C.sourceOpen.1`. -/
-- tier: T1
theorem hamiltonianVectorField_liftPlanarHamiltonian_embed_of_notMem_sourceOpen
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
    [A : AdmitsRegularDiskFibration M]
    {r₀ : ℝ} (P : CompactlySupportedPlanarHamiltonian r₀)
    (b :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      A.fibration.baseRegion)
    {z : A.Fiber}
    (hz :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instMeasurableSpaceFiber
      letI := A.instBorelSpaceFiber
      z ∉ (AdmitsRegularDiskFibration.fiberDiskChart M).sourceOpen.1) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    (adaptedJacobianPoisson M).hamiltonianVectorField
      (liftPlanarHamiltonianTo4Manifold M P) (A.fibration.embed (b, z)) = 0 := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := A.instMeasurableSpaceFiber
  let _ := A.instBorelSpaceFiber
  let C := AdmitsRegularDiskFibration.fiberDiskChart M
  let S_fib : Set A.Fiber := C.supportSet P.r₀_mem_Ioo.2
  have hS_closed : IsClosed S_fib := (C.isCompact_supportSet P.r₀_mem_Ioo.2).isClosed
  have hz_notS : z ∉ S_fib := fun hm ↦ hz (C.supportSet_subset_sourceOpen P.r₀_mem_Ioo.2 hm)
  let U_prod : Set (A.fibration.baseRegion × A.Fiber) := Set.univ ×ˢ S_fibᶜ
  have hU_open : IsOpen (A.fibration.embed '' U_prod) :=
    A.fibration.isOpenEmbedding_embed.isOpenMap U_prod (isOpen_univ.prod hS_closed.isOpen_compl)
  have hx_mem : A.fibration.embed (b, z) ∈ A.fibration.embed '' U_prod :=
    ⟨(b, z), ⟨Set.mem_univ b, hz_notS⟩, rfl⟩
  refine hamiltonianVectorField_adaptedJacobianPoisson_eq_zero_of_eventuallyEq M ?_
  filter_upwards [hU_open.mem_nhds hx_mem] with w hw
  rcases hw with ⟨⟨b', z'⟩, ⟨_, hz'⟩, rfl⟩
  rw [liftPlanarHamiltonianTo4Manifold_embed M P b' z',
    fiberHamiltonianOfPlanar_eq_zero_of_notMem_supportSet C P hz', mul_zero]

/-- Pointwise evaluation of `productTargetForm M` as the `2 ∧ 2` paired wedge of `p₂^* ω_F` and
`(val ∘ p₁)^* μ_B`, avoiding `IsSmoothForm` degree `4` vs `2 + 2` `kabstract` unfolding. -/
-- tier: T1
theorem productTargetForm_apply_eq
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [A : AdmitsRegularDiskFibration M]
    (q :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      A.fibration.baseRegion × A.Fiber)
    (v :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      Fin 4 → TangentSpace ((𝓡 2).prod (𝓡 2)) q) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    letI := A.instMeasurableSpaceFiber
    letI := A.instBorelSpaceFiber
    (show ℝ from (productTargetForm M).1 q v) =
      ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
        (ContinuousLinearMap.mul ℝ ℝ).continuous₂
        ((TauCeti.SmoothForm.mpullback (I := (𝓡 2).prod (𝓡 2)) (I' := 𝓡 2)
            (Prod.snd : A.fibration.baseRegion × A.Fiber → A.Fiber)
            contMDiff_snd A.fiberVolume.Ω).1 q)
        ((TauCeti.SmoothForm.mpullback (I := (𝓡 2).prod (𝓡 2)) (I' := 𝓡 2)
            (Subtype.val ∘ Prod.fst : A.fibration.baseRegion × A.Fiber → Sphere2)
            ((contMDiff_subtype_val (I := 𝓡 2)).comp contMDiff_fst) S2VolumeForm).1 q)
        v := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := A.instMeasurableSpaceFiber
  let _ := A.instBorelSpaceFiber
  let ω_snd := TauCeti.SmoothForm.mpullback (I := (𝓡 2).prod (𝓡 2)) (I' := 𝓡 2)
    (Prod.snd : A.fibration.baseRegion × A.Fiber → A.Fiber) contMDiff_snd A.fiberVolume.Ω
  let μ_fst := TauCeti.SmoothForm.mpullback (I := (𝓡 2).prod (𝓡 2)) (I' := 𝓡 2)
    (Subtype.val ∘ Prod.fst : A.fibration.baseRegion × A.Fiber → Sphere2)
    ((contMDiff_subtype_val (I := 𝓡 2)).comp contMDiff_fst) S2VolumeForm
  have heq :
      (productTargetForm M :
          TauCeti.SmoothForm ((𝓡 2).prod (𝓡 2)) (A.fibration.baseRegion × A.Fiber) ℝ (2 + 2)) =
        TauCeti.SmoothForm.wedge ω_snd μ_fst := rfl
  have hw1 : (show ℝ from (productTargetForm M).1 q v) =
      (show ℝ from (TauCeti.SmoothForm.wedge ω_snd μ_fst).1 q v) :=
    DFunLike.congr_fun (congrFun (congrArg Subtype.val heq) q) v
  have hw2 : (show ℝ from (TauCeti.SmoothForm.wedge ω_snd μ_fst).1 q v) =
      ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
        (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (ω_snd.1 q) (μ_fst.1 q) v := by
    change ((TauCeti.SmoothForm.wedge ω_snd μ_fst :
        TauCeti.RoughForm ((𝓡 2).prod (𝓡 2)) (A.fibration.baseRegion × A.Fiber) ℝ (2 + 2)) q v) = _
    rw [TauCeti.SmoothForm.coe_wedge, TauCeti.RoughForm.wedge_def,
      TauCeti.RoughForm.wedgeWith_apply']
  exact hw1.trans hw2

/-- Directional derivative of `liftPlanarHamiltonianTo4Manifold M P` pushed forward along
`A.fibration.embed` at `(b, z)`: splits into base-bump derivative `α₂` plus fiber-Hamiltonian
derivative `α₁`. -/
-- tier: T2
theorem mvfderiv_liftPlanarHamiltonian_embed
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [A : AdmitsRegularDiskFibration M]
    {r₀ : ℝ} (P : CompactlySupportedPlanarHamiltonian r₀)
    (b :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      A.fibration.baseRegion)
    (z : A.Fiber)
    (v :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      TangentSpace ((𝓡 2).prod (𝓡 2)) (b, z)) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    letI := A.instMeasurableSpaceFiber
    letI := A.instBorelSpaceFiber
    let C := AdmitsRegularDiskFibration.fiberDiskChart M
    let L_base : TangentSpace ((𝓡 2).prod (𝓡 2)) (b, z) →L[ℝ] TangentSpace (𝓡 2) b.1 :=
      (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : A.fibration.baseRegion → Sphere2) b).comp
        (ContinuousLinearMap.fst ℝ (TangentSpace (𝓡 2) b) (TangentSpace (𝓡 2) z))
    mvfderiv (𝓡 4) (liftPlanarHamiltonianTo4Manifold M P) (A.fibration.embed (b, z))
        (mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 4) A.fibration.embed (b, z) v) =
      fiberHamiltonianOfPlanar C P z * mvfderiv (𝓡 2) (bumpProfile M) b.1 (L_base v) +
        bumpProfile M b.1 * mvfderiv (𝓡 2) (fiberHamiltonianOfPlanar C P) z v.2 := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := A.instMeasurableSpaceFiber
  let _ := A.instBorelSpaceFiber
  intro C L_base
  let H_lift := liftPlanarHamiltonianTo4Manifold M P
  let x := A.fibration.embed (b, z)
  have hH_diff : MDifferentiableAt (𝓡 4) 𝓘(ℝ) H_lift x :=
    (H_lift.contMDiff x).mdifferentiableAt (by simp)
  have hemb_diff : MDifferentiableAt ((𝓡 2).prod (𝓡 2)) (𝓡 4) A.fibration.embed (b, z) :=
    (A.fibration.contMDiff_embed (b, z)).mdifferentiableAt (by simp)
  let ρ_sub : A.fibration.baseRegion → ℝ :=
    bumpProfile M ∘ (Subtype.val : A.fibration.baseRegion → Sphere2)
  have hH_comp :
      (⇑H_lift : M → ℝ) ∘ A.fibration.embed =
        fun q : A.fibration.baseRegion × A.Fiber ↦
          ρ_sub q.1 * fiberHamiltonianOfPlanar C P q.2 :=
    funext fun ⟨b', z'⟩ ↦ liftPlanarHamiltonianTo4Manifold_embed M P b' z'
  have hρ_sub_diff : MDifferentiableAt (𝓡 2) 𝓘(ℝ) ρ_sub b :=
    (((contMDiff_bumpProfile M).comp (contMDiff_subtype_val (I := 𝓡 2))) b).mdifferentiableAt
      (by simp)
  have hf_diff : MDifferentiableAt (𝓡 2) 𝓘(ℝ) (fiberHamiltonianOfPlanar C P) z :=
    ((contMDiff_fiberHamiltonianOfPlanar C P) z).mdifferentiableAt (by simp)
  rw [← mvfderiv_comp_apply (b, z) hH_diff hemb_diff v, hH_comp,
    TauCeti.mvfderiv_comp_fst_mul_comp_snd_apply hρ_sub_diff hf_diff v]
  have hρ_fst :
      mvfderiv (𝓡 2) ρ_sub b v.1 =
        mvfderiv (𝓡 2) (bumpProfile M) b.1 (L_base v) := by
    rw [show ρ_sub = bumpProfile M ∘ (Subtype.val : A.fibration.baseRegion → Sphere2) from rfl,
      mvfderiv_comp_apply b (((contMDiff_bumpProfile M) b.1).mdifferentiableAt (by simp))
        ((contMDiff_subtype_val (I := 𝓡 2) (n := ∞)).mdifferentiableAt (by simp)) v.1]
    rfl
  rw [hρ_fst]
  dsimp only [ρ_sub, Function.comp_apply]
  ring

/-- Contraction of `(alignedPositiveVolume M).Ω` at `Ψ_b y = A.fibration.embed (b, C.embed y)`
(`b.1 ∈ baseClosedSubdisk M (rInner M) ...`) with the vertical vector
`bumpProfile M b.1 • d(Ψ_b)_y (P.vectorField 0 y.1)` and pushed-forward `w_prod`. -/
-- tier: T2
theorem alignedVolumeForm_embed_apply_vertical
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
    [A : AdmitsRegularDiskFibration M]
    {r₀ : ℝ} (P : CompactlySupportedPlanarHamiltonian r₀)
    (b :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      A.fibration.baseRegion)
    (hb_closed : b.1 ∈ baseClosedSubdisk M (rInner M) (rInner_lt_baseRadius M))
    (y : diskOpen)
    (w :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      letI := A.instMeasurableSpaceFiber
      letI := A.instBorelSpaceFiber
      let C := AdmitsRegularDiskFibration.fiberDiskChart M
      Fin 3 → TangentSpace (𝓡 4) (A.fibration.embed (b, C.embed y)))
    (w_prod :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      letI := A.instMeasurableSpaceFiber
      letI := A.instBorelSpaceFiber
      let C := AdmitsRegularDiskFibration.fiberDiskChart M
      Fin 3 → TangentSpace ((𝓡 2).prod (𝓡 2)) (b, C.embed y))
    (hw_prod :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      letI := A.instMeasurableSpaceFiber
      letI := A.instBorelSpaceFiber
      let C := AdmitsRegularDiskFibration.fiberDiskChart M
      ∀ j : Fin 3,
        mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 4) A.fibration.embed (b, C.embed y) (w_prod j) = w j) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    letI := A.instMeasurableSpaceFiber
    letI := A.instBorelSpaceFiber
    let C := AdmitsRegularDiskFibration.fiberDiskChart M
    let z := C.embed y
    let Ψ_b : diskOpen → M := fun w' ↦ A.fibration.embed (b, C.embed w')
    let v_disk : TangentSpace (𝓡 2) y :=
      (TauCeti.Manifold.tangentSpaceOpenEquiv (I := 𝓡 2) y).symm (P.vectorField 0 y.1)
    let μ_fst := TauCeti.SmoothForm.mpullback (I := (𝓡 2).prod (𝓡 2)) (I' := 𝓡 2)
      (Subtype.val ∘ Prod.fst : A.fibration.baseRegion × A.Fiber → Sphere2)
      ((contMDiff_subtype_val (I := 𝓡 2)).comp contMDiff_fst) S2VolumeForm
    let α₁ : TangentSpace ((𝓡 2).prod (𝓡 2)) (b, z) →L[ℝ] ℝ :=
      bumpProfile M b.1 •
        ((mvfderiv (𝓡 2) (fiberHamiltonianOfPlanar C P) z).comp
          (ContinuousLinearMap.snd ℝ (TangentSpace (𝓡 2) b) (TangentSpace (𝓡 2) z)))
    (show ℝ from (alignedPositiveVolume M).Ω.1 (Ψ_b y)
        (Matrix.vecCons (bumpProfile M b.1 • mfderiv (𝓡 2) (𝓡 4) Ψ_b y v_disk) w)) =
      α₁ (w_prod 0) * μ_fst.1 (b, z) ![w_prod 1, w_prod 2] -
        α₁ (w_prod 1) * μ_fst.1 (b, z) ![w_prod 0, w_prod 2] +
        α₁ (w_prod 2) * μ_fst.1 (b, z) ![w_prod 0, w_prod 1] := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := A.instMeasurableSpaceFiber
  let _ := A.instBorelSpaceFiber
  intro C z Ψ_b v_disk μ_fst α₁
  let x : M := Ψ_b y
  have hx_closed : A.fibration x ∈ baseClosedSubdisk M (rInner M) (rInner_lt_baseRadius M) :=
    (A.fibration.apply_embed b z) ▸ hb_closed
  let E_symm := A.fibration.trivialization.symm
  let D_emb : TangentSpace ((𝓡 2).prod (𝓡 2)) (b, z) →L[ℝ] TangentSpace (𝓡 4) x :=
    mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 4) A.fibration.embed (b, z)
  let Y_z : TangentSpace (𝓡 2) z := mfderiv (𝓡 2) (𝓡 2) C.embed y v_disk
  let V_bz : TangentSpace ((𝓡 2).prod (𝓡 2)) (b, z) :=
    ((0 : TangentSpace (𝓡 2) b), bumpProfile M b.1 • Y_z)
  have hu_cand :
      bumpProfile M b.1 • mfderiv (𝓡 2) (𝓡 4) Ψ_b y v_disk = D_emb V_bz := by
    let ι_y : diskOpen → A.fibration.baseRegion × A.Fiber := fun w' ↦ (b, C.embed w')
    have hι_diff : MDifferentiableAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) ι_y y :=
      mdifferentiableAt_const.prodMk ((C.contMDiff_embed y).mdifferentiableAt (by simp))
    have hemb_diff : MDifferentiableAt ((𝓡 2).prod (𝓡 2)) (𝓡 4) A.fibration.embed (b, z) :=
      (A.fibration.contMDiff_embed (b, z)).mdifferentiableAt (by simp)
    have hι_val : mfderiv (𝓡 2) ((𝓡 2).prod (𝓡 2)) ι_y y v_disk =
        (((0 : TangentSpace (𝓡 2) b), Y_z) : TangentSpace ((𝓡 2).prod (𝓡 2)) (b, z)) := by
      rw [show ι_y = fun w' : diskOpen ↦ (b, C.embed w') from rfl,
        mfderiv_prodMk mdifferentiableAt_const
          ((C.contMDiff_embed y).mdifferentiableAt (by simp)),
        mfderiv_const]
      rfl
    have hΨ_mf : mfderiv (𝓡 2) (𝓡 4) Ψ_b y v_disk =
        D_emb (mfderiv (𝓡 2) ((𝓡 2).prod (𝓡 2)) ι_y y v_disk) :=
      mfderiv_comp_apply y hemb_diff hι_diff v_disk
    rw [hΨ_mf, ← D_emb.map_smul]
    congr 1
    rw [hι_val]
    change (bumpProfile M b.1 • (0 : TangentSpace (𝓡 2) b), bumpProfile M b.1 • Y_z) = V_bz
    rw [smul_zero]
    rfl
  have hD_symm_eq (v : TangentSpace ((𝓡 2).prod (𝓡 2)) (b, z)) :
      (show TangentSpace (𝓡 4) x from
        mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 4) E_symm (b, z) v) = D_emb v := by
    have hsub :
        mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 4)
            ((Subtype.val : A.fibration.preimageOpen → M) ∘ E_symm) (b, z) v =
          mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 4) E_symm (b, z) v :=
      TauCeti.Manifold.mfderiv_subtype_val_comp_apply v
    exact hsub.symm
  have hlhs_prod :
      (show ℝ from (alignedPositiveVolume M).Ω.1 x
          (Matrix.vecCons (bumpProfile M b.1 • mfderiv (𝓡 2) (𝓡 4) Ψ_b y v_disk) w)) =
        (show ℝ from (productTargetForm M).1 (b, z) (Matrix.vecCons V_bz w_prod)) := by
    let v_sub : Fin 4 → TangentSpace (𝓡 4) (E_symm (b, z)) :=
      fun i ↦ mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 4) E_symm (b, z) (Matrix.vecCons V_bz w_prod i)
    have hv_eq : Matrix.vecCons (D_emb V_bz) w =
        (v_sub : Fin 4 → TangentSpace (𝓡 4) x) := by
      funext i
      change _ = (show TangentSpace (𝓡 4) x from
        mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 4) E_symm (b, z) (Matrix.vecCons V_bz w_prod i))
      rw [hD_symm_eq]
      cases i using Fin.cases with
      | zero => rfl
      | succ j => exact (hw_prod j).symm
    have h1 : (show ℝ from (alignedPositiveVolume M).Ω.1 x
          (v_sub : Fin 4 → TangentSpace (𝓡 4) x)) =
        (show ℝ from (trivializedProductForm M).1 (E_symm (b, z)) v_sub) :=
      DFunLike.congr_fun
        (alignedVolumeForm_eq_trivializedProductForm_of_mem_closedInner M hx_closed) v_sub
    have h2 : (show ℝ from (trivializedProductForm M).1 (E_symm (b, z)) v_sub) =
        (show ℝ from (productTargetForm M).1 (b, z) (Matrix.vecCons V_bz w_prod)) := by
      rw [show v_sub = fun i ↦ mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 4) E_symm (b, z)
            (Matrix.vecCons V_bz w_prod i) from rfl,
        ← TauCeti.SmoothForm.mpullback_apply E_symm E_symm.contMDiff
          (trivializedProductForm M) (b, z) (Matrix.vecCons V_bz w_prod)]
      unfold trivializedProductForm
      rw [show E_symm = A.fibration.trivialization.symm from rfl,
        TauCeti.SmoothForm.mpullback_symm_mpullback]
    rw [hu_cand, hv_eq]
    exact h1.trans h2
  let ω_snd := TauCeti.SmoothForm.mpullback (I := (𝓡 2).prod (𝓡 2)) (I' := 𝓡 2)
    (Prod.snd : A.fibration.baseRegion × A.Fiber → A.Fiber) contMDiff_snd A.fiberVolume.Ω
  have hμ0 (u : TangentSpace ((𝓡 2).prod (𝓡 2)) (b, z)) :
      μ_fst.1 (b, z) ![V_bz, u] = 0 := by
    rw [TauCeti.SmoothForm.mpullback_apply]
    have hf0 :
        mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 2)
          (Subtype.val ∘ Prod.fst : A.fibration.baseRegion × A.Fiber → Sphere2) (b, z)
          (![V_bz, u] 0) = 0 := by
      rw [Matrix.cons_val_zero]
      have hcomp := congrArg (· V_bz)
        (TauCeti.mfderiv_comp_fst (I := 𝓡 2) (J := 𝓡 2) (I'' := 𝓡 2)
          (Subtype.val : A.fibration.baseRegion → Sphere2) (b, z))
      exact hcomp.trans
        (map_zero (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : A.fibration.baseRegion → Sphere2) b))
    exact (S2VolumeForm.1 b.1).map_coord_zero 0 hf0
  have hω_eval (u : TangentSpace ((𝓡 2).prod (𝓡 2)) (b, z)) :
      ω_snd.1 (b, z) ![V_bz, u] = α₁ u := by
    rw [TauCeti.SmoothForm.mpullback_apply]
    have hsnd_vec :
        (fun i : Fin 2 ↦
            mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 2)
              (Prod.snd : A.fibration.baseRegion × A.Fiber → A.Fiber) (b, z)
              (![V_bz, u] i)) =
          ![bumpProfile M b.1 • Y_z, u.2] := by
      funext i
      rw [TauCeti.mfderiv_snd_apply]
      fin_cases i <;> rfl
    rw [hsnd_vec, map_vecCons_smul_slot0, smul_eq_mul,
      symplecticDiskChart_apply_mfderiv_embed_vectorField C P y u.2]
    rfl
  let φ_bz : TangentSpace ((𝓡 2).prod (𝓡 2)) (b, z) [⋀^Fin 2]→L[ℝ] ℝ := ω_snd.1 (b, z)
  let ψ_bz : TangentSpace ((𝓡 2).prod (𝓡 2)) (b, z) [⋀^Fin 2]→L[ℝ] ℝ := μ_fst.1 (b, z)
  have hp1 := productTargetForm_apply_eq M (b, z) (Matrix.vecCons V_bz w_prod)
  have hp2 := pairedWedge_two_two_vecCons_of_right_zero φ_bz ψ_bz V_bz w_prod (fun u ↦ hμ0 u)
  exact hlhs_prod.trans (hp1.trans (hp2.trans
    (threeTermAlt_congr_left (hω_eval (w_prod 0)) (hω_eval (w_prod 1)) (hω_eval (w_prod 2)))))

/-- Evaluation of `(d H_lift ∧ f^* μ_B)_x` (`x = A.fibration.embed (b, z)`) on `w = D_emb ∘ w_prod`,
annihilating the `d(bumpProfile M)` term via `wedge_one_two_plane_eq_zero`
(`finrank ℝ ℝ² = 2 < 3`). -/
-- tier: T2
theorem etaForm_liftPlanarHamiltonian_embed_apply
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [A : AdmitsRegularDiskFibration M]
    {r₀ : ℝ} (P : CompactlySupportedPlanarHamiltonian r₀)
    (b :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      A.fibration.baseRegion)
    (z : A.Fiber)
    (w :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      Fin 3 → TangentSpace (𝓡 4) (A.fibration.embed (b, z)))
    (w_prod :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      Fin 3 → TangentSpace ((𝓡 2).prod (𝓡 2)) (b, z))
    (hw_prod :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      ∀ j : Fin 3,
        mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 4) A.fibration.embed (b, z) (w_prod j) = w j) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    letI := A.instMeasurableSpaceFiber
    letI := A.instBorelSpaceFiber
    let C := AdmitsRegularDiskFibration.fiberDiskChart M
    let H_lift := liftPlanarHamiltonianTo4Manifold M P
    let η_form := TauCeti.SmoothForm.wedge (SmoothBivector.diffOneForm H_lift)
      (TauCeti.SmoothForm.mpullback A.fibration A.fibration.contMDiff_toFun S2VolumeForm)
    let μ_fst := TauCeti.SmoothForm.mpullback (I := (𝓡 2).prod (𝓡 2)) (I' := 𝓡 2)
      (Subtype.val ∘ Prod.fst : A.fibration.baseRegion × A.Fiber → Sphere2)
      ((contMDiff_subtype_val (I := 𝓡 2)).comp contMDiff_fst) S2VolumeForm
    let α₁ : TangentSpace ((𝓡 2).prod (𝓡 2)) (b, z) →L[ℝ] ℝ :=
      bumpProfile M b.1 •
        ((mvfderiv (𝓡 2) (fiberHamiltonianOfPlanar C P) z).comp
          (ContinuousLinearMap.snd ℝ (TangentSpace (𝓡 2) b) (TangentSpace (𝓡 2) z)))
    (show ℝ from η_form.1 (A.fibration.embed (b, z)) w) =
      α₁ (w_prod 0) * μ_fst.1 (b, z) ![w_prod 1, w_prod 2] -
        α₁ (w_prod 1) * μ_fst.1 (b, z) ![w_prod 0, w_prod 2] +
        α₁ (w_prod 2) * μ_fst.1 (b, z) ![w_prod 0, w_prod 1] := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := A.instMeasurableSpaceFiber
  let _ := A.instBorelSpaceFiber
  intro C H_lift η_form μ_fst α₁
  let x := A.fibration.embed (b, z)
  let D_emb : TangentSpace ((𝓡 2).prod (𝓡 2)) (b, z) →L[ℝ] TangentSpace (𝓡 4) x :=
    mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 4) A.fibration.embed (b, z)
  let L_base : TangentSpace ((𝓡 2).prod (𝓡 2)) (b, z) →L[ℝ] TangentSpace (𝓡 2) b.1 :=
    (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : A.fibration.baseRegion → Sphere2) b).comp
      (ContinuousLinearMap.fst ℝ (TangentSpace (𝓡 2) b) (TangentSpace (𝓡 2) z))
  let α₂ : TangentSpace ((𝓡 2).prod (𝓡 2)) (b, z) →L[ℝ] ℝ :=
    fiberHamiltonianOfPlanar C P z • ((mvfderiv (𝓡 2) (bumpProfile M) b.1).comp L_base)
  have hdH_pull (v : TangentSpace ((𝓡 2).prod (𝓡 2)) (b, z)) :
      mvfderiv (𝓡 4) H_lift x (D_emb v) = α₂ v + α₁ v :=
    mvfderiv_liftPlanarHamiltonian_embed M P b z v
  have hψ_pull (u₁ u₂ : TangentSpace ((𝓡 2).prod (𝓡 2)) (b, z)) :
      (show ℝ from (TauCeti.SmoothForm.mpullback A.fibration A.fibration.contMDiff_toFun
          S2VolumeForm).1 x ![D_emb u₁, D_emb u₂]) =
        (show ℝ from μ_fst.1 (b, z) ![u₁, u₂]) := by
    have hfib_emb : A.fibration ∘ A.fibration.embed =
        (Subtype.val ∘ Prod.fst : A.fibration.baseRegion × A.Fiber → Sphere2) :=
      funext fun q ↦ A.fibration.apply_embed q.1 q.2
    have hvec_emb :
        (![D_emb u₁, D_emb u₂] : Fin 2 → TangentSpace (𝓡 4) x) =
          fun i ↦ mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 4) A.fibration.embed (b, z) (![u₁, u₂] i) := by
      funext i
      fin_cases i <;> rfl
    have hp_emb :
        (show ℝ from (TauCeti.SmoothForm.mpullback A.fibration A.fibration.contMDiff_toFun
            S2VolumeForm).1 x ![D_emb u₁, D_emb u₂]) =
          (show ℝ from
            (TauCeti.SmoothForm.mpullback (I := (𝓡 2).prod (𝓡 2)) (I' := 𝓡 4)
              A.fibration.embed A.fibration.contMDiff_embed
              (TauCeti.SmoothForm.mpullback A.fibration A.fibration.contMDiff_toFun
                S2VolumeForm)).1 (b, z) ![u₁, u₂]) := by
      rw [hvec_emb]
      exact (TauCeti.SmoothForm.mpullback_apply A.fibration.embed
        A.fibration.contMDiff_embed _ (b, z) ![u₁, u₂]).symm
    have hform_eq :
        TauCeti.SmoothForm.mpullback (I := (𝓡 2).prod (𝓡 2)) (I' := 𝓡 4)
            A.fibration.embed A.fibration.contMDiff_embed
            (TauCeti.SmoothForm.mpullback A.fibration A.fibration.contMDiff_toFun
              S2VolumeForm) = μ_fst :=
      TauCeti.SmoothForm.mpullback_mpullback_of_comp_eq
        A.fibration.contMDiff_embed A.fibration.contMDiff_toFun
        ((contMDiff_subtype_val (I := 𝓡 2)).comp contMDiff_fst) contMDiff_id
        hfib_emb S2VolumeForm |>.trans (by simp only [TauCeti.SmoothForm.mpullback_id]; rfl)
    exact hp_emb.trans (DFunLike.congr_fun (congrFun (congrArg Subtype.val hform_eq) (b, z))
      ![u₁, u₂])
  have hrhs_exp :
      (show ℝ from η_form.1 x w) =
        (α₂ (w_prod 0) + α₁ (w_prod 0)) * μ_fst.1 (b, z) ![w_prod 1, w_prod 2] -
          (α₂ (w_prod 1) + α₁ (w_prod 1)) * μ_fst.1 (b, z) ![w_prod 0, w_prod 2] +
          (α₂ (w_prod 2) + α₁ (w_prod 2)) * μ_fst.1 (b, z) ![w_prod 0, w_prod 1] := by
    have hw_eq : w = ![D_emb (w_prod 0), D_emb (w_prod 1), D_emb (w_prod 2)] := by
      funext j
      fin_cases j <;> exact (hw_prod _).symm
    have hw1 : (show ℝ from η_form.1 x w) =
        (show ℝ from η_form.1 x ![D_emb (w_prod 0), D_emb (w_prod 1), D_emb (w_prod 2)]) :=
      congrArg (η_form.1 x) hw_eq
    have hw2a :
        (show ℝ from η_form.1 x ![D_emb (w_prod 0), D_emb (w_prod 1), D_emb (w_prod 2)]) =
          ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
            (ContinuousLinearMap.mul ℝ ℝ).continuous₂
            ((SmoothBivector.diffOneForm H_lift).1 x)
            ((TauCeti.SmoothForm.mpullback A.fibration A.fibration.contMDiff_toFun
                S2VolumeForm).1 x)
            ![D_emb (w_prod 0), D_emb (w_prod 1), D_emb (w_prod 2)] := by
      change ((η_form : TauCeti.RoughForm (𝓡 4) M ℝ (1 + 2)) x
          ![D_emb (w_prod 0), D_emb (w_prod 1), D_emb (w_prod 2)]) = _
      rw [show η_form = TauCeti.SmoothForm.wedge (SmoothBivector.diffOneForm H_lift)
            (TauCeti.SmoothForm.mpullback A.fibration A.fibration.contMDiff_toFun
              S2VolumeForm) from rfl,
        TauCeti.SmoothForm.coe_wedge, TauCeti.RoughForm.wedge_def,
        TauCeti.RoughForm.wedgeWith_apply']
    have hw2 := hw2a.trans (pairedWedge_one_two_apply
      ((SmoothBivector.diffOneForm H_lift).1 x : TangentSpace (𝓡 4) x [⋀^Fin 1]→L[ℝ] ℝ)
      ((TauCeti.SmoothForm.mpullback A.fibration A.fibration.contMDiff_toFun
          S2VolumeForm).1 x : TangentSpace (𝓡 4) x [⋀^Fin 2]→L[ℝ] ℝ)
      (D_emb (w_prod 0)) (D_emb (w_prod 1)) (D_emb (w_prod 2)))
    have hd0 := (SmoothBivector.diffOneForm_apply H_lift x (D_emb (w_prod 0))).trans
      (hdH_pull (w_prod 0))
    have hd1 := (SmoothBivector.diffOneForm_apply H_lift x (D_emb (w_prod 1))).trans
      (hdH_pull (w_prod 1))
    have hd2 := (SmoothBivector.diffOneForm_apply H_lift x (D_emb (w_prod 2))).trans
      (hdH_pull (w_prod 2))
    exact hw1.trans (hw2.trans (threeTermAlt_congr hd0 hd1 hd2
      (hψ_pull (w_prod 1) (w_prod 2))
      (hψ_pull (w_prod 0) (w_prod 2))
      (hψ_pull (w_prod 0) (w_prod 1))))
  have hvanish :
      α₂ (w_prod 0) * μ_fst.1 (b, z) ![w_prod 1, w_prod 2] -
        α₂ (w_prod 1) * μ_fst.1 (b, z) ![w_prod 0, w_prod 2] +
        α₂ (w_prod 2) * μ_fst.1 (b, z) ![w_prod 0, w_prod 1] = 0 := by
    have hμ_pair (u₁ u₂ : TangentSpace ((𝓡 2).prod (𝓡 2)) (b, z)) :
        (show ℝ from μ_fst.1 (b, z) ![u₁, u₂]) =
          (show ℝ from S2VolumeForm.1 b.1 ![L_base u₁, L_base u₂]) := by
      have hp := TauCeti.SmoothForm.mpullback_apply (I := (𝓡 2).prod (𝓡 2)) (I' := 𝓡 2)
        (Subtype.val ∘ Prod.fst : A.fibration.baseRegion × A.Fiber → Sphere2)
        ((contMDiff_subtype_val (I := 𝓡 2)).comp contMDiff_fst) S2VolumeForm (b, z) ![u₁, u₂]
      have harg :
          (fun i : Fin 2 ↦
              mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 2)
                (Subtype.val ∘ Prod.fst : A.fibration.baseRegion × A.Fiber → Sphere2)
                (b, z) (![u₁, u₂] i)) =
            ![L_base u₁, L_base u₂] := by
        funext i
        fin_cases i
        · exact congrArg (· u₁)
            (TauCeti.mfderiv_comp_fst (I := 𝓡 2) (J := 𝓡 2) (I'' := 𝓡 2)
              (Subtype.val : A.fibration.baseRegion → Sphere2) (b, z))
        · exact congrArg (· u₂)
            (TauCeti.mfderiv_comp_fst (I := 𝓡 2) (J := 𝓡 2) (I'' := 𝓡 2)
              (Subtype.val : A.fibration.baseRegion → Sphere2) (b, z))
      exact hp.trans (congrArg (S2VolumeForm.1 b.1) harg)
    have hα₂_eval (u : TangentSpace ((𝓡 2).prod (𝓡 2)) (b, z)) :
        α₂ u = (fiberHamiltonianOfPlanar C P z • mvfderiv (𝓡 2) (bumpProfile M) b.1) (L_base u) :=
      rfl
    exact (threeTermAlt_congr
      (hα₂_eval (w_prod 0)) (hα₂_eval (w_prod 1)) (hα₂_eval (w_prod 2))
      (hμ_pair (w_prod 1) (w_prod 2))
      (hμ_pair (w_prod 0) (w_prod 2))
      (hμ_pair (w_prod 0) (w_prod 1))).trans
        (wedge_one_two_plane_eq_zero
          (fiberHamiltonianOfPlanar C P z • mvfderiv (𝓡 2) (bumpProfile M) b.1)
          (S2VolumeForm.1 b.1) (L_base (w_prod 0)) (L_base (w_prod 1)) (L_base (w_prod 2)))
  exact hrhs_exp.trans (threeTermAlt_add_left_of_eq_zero hvanish).symm

/-- **Pointwise 4D Jacobian–Poisson Hamiltonian Vector Field Formula**
(`docs/cmpp/geometry_spec.md` §4.1):
On `Ψ_b y := A.fibration.embed (b, C.embed y)`, the Hamiltonian vector field of
`liftPlanarHamiltonianTo4Manifold M P` with respect to `adaptedJacobianPoisson M` equals
`bumpProfile M b.1 • d(Ψ_b)_y (P.vectorField 0 y.1)`. -/
-- tier: T2
theorem hamiltonianVectorField_liftPlanarHamiltonian_embed
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
    [A : AdmitsRegularDiskFibration M]
    {r₀ : ℝ} (P : CompactlySupportedPlanarHamiltonian r₀)
    (b :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      A.fibration.baseRegion)
    (y : diskOpen) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    letI := A.instMeasurableSpaceFiber
    letI := A.instBorelSpaceFiber
    let C := AdmitsRegularDiskFibration.fiberDiskChart M
    let Ψ_b : diskOpen → M := fun w ↦ A.fibration.embed (b, C.embed w)
    let v_disk : TangentSpace (𝓡 2) y :=
      (TauCeti.Manifold.tangentSpaceOpenEquiv (I := 𝓡 2) y).symm (P.vectorField 0 y.1)
    (adaptedJacobianPoisson M).hamiltonianVectorField
        (liftPlanarHamiltonianTo4Manifold M P) (Ψ_b y) =
      bumpProfile M b.1 • mfderiv (𝓡 2) (𝓡 4) Ψ_b y v_disk := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := A.instMeasurableSpaceFiber
  let _ := A.instBorelSpaceFiber
  intro C Ψ_b v_disk
  by_cases hb_supp : b.1 ∈ tsupport (bumpProfile M)
  · have hb_in : b.1 ∈ (baseInnerOpen M).1 :=
      tsupport_bumpProfile_subset_baseInnerOpen M hb_supp
    have hb_closed : b.1 ∈ baseClosedSubdisk M (rInner M) (rInner_lt_baseRadius M) :=
      baseOpenSubdisk_subset_baseClosedSubdisk M (rInner M) (rInner_lt_baseRadius M) hb_in
    let z : A.Fiber := C.embed y
    let x : M := Ψ_b y
    let Ω := (alignedPositiveVolume M).Ω
    have hΩ : ∀ w : M, Ω.1 w ≠ 0 := (alignedPositiveVolume M).Ω_ne_zero
    let H_lift := liftPlanarHamiltonianTo4Manifold M P
    let η_form := TauCeti.SmoothForm.wedge (SmoothBivector.diffOneForm H_lift)
      (TauCeti.SmoothForm.mpullback A.fibration A.fibration.contMDiff_toFun S2VolumeForm)
    let bM : Module.Basis (Fin 4) ℝ (TangentSpace (𝓡 4) x) :=
      (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis
    have hX_eq : (adaptedJacobianPoisson M).hamiltonianVectorField H_lift x =
        subTopDualVector bM (Ω.1 x) (η_form.1 x) := by
      refine eq_subTopDualVector_of_forall_vecCons bM (hΩ x) (η_form.1 x) fun w ↦ ?_
      have hint := DFunLike.congr_fun
        (congrFun (interior_hamiltonianVectorField_jacobianSmoothBivector Ω hΩ S2VolumeForm
          A.fibration A.fibration.contMDiff_toFun H_lift) x) w
      rw [TauCeti.RoughForm.interior_apply] at hint
      exact hint
    rw [hX_eq]
    symm
    refine eq_subTopDualVector_of_forall_vecCons bM (hΩ x) (η_form.1 x) fun w ↦ ?_
    have hD_surj :
        Function.Surjective (mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 4) A.fibration.embed (b, z)) :=
      (A.fibration.isLocalDiffeomorph_embed.isInvertible_mfderiv (by simp) (b, z)).surjective
    choose w_prod hw_prod using fun j : Fin 3 ↦ hD_surj (w j)
    exact (alignedVolumeForm_embed_apply_vertical M P b hb_closed y w w_prod hw_prod).trans
      (etaForm_liftPlanarHamiltonian_embed_apply M P b z w w_prod hw_prod).symm
  · have hρ0 : bumpProfile M b.1 = 0 := image_eq_zero_of_notMem_tsupport hb_supp
    have hfib : A.fibration (Ψ_b y) = b.1 := A.fibration.apply_embed b (C.embed y)
    rw [hρ0, zero_smul]
    exact hamiltonianVectorField_liftPlanarHamiltonian_eq_zero_of_notMem_tsupport_base M P
      (hfib.symm ▸ hb_supp)

/-- **Fundamental Leafwise-to-Poisson–Hamiltonian Time-`1` Flow Theorem**
(`docs/cmpp/geometry_spec.md` §4.2):
For every autonomous `P : CompactlySupportedPlanarHamiltonian r₀`, the time-`1` flow diffeomorphism
of `(adaptedJacobianPoisson M).hamiltonianVectorField (liftPlanarHamiltonianTo4Manifold M P)` equals
`leafwiseBumpDiffeomorphOfIsotopy M P.toDiskIsotopy`. -/
-- tier: T2
theorem poissonHamiltonianTimeOneDiffeomorph_liftPlanarHamiltonian_eq
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
    [A : AdmitsRegularDiskFibration M]
    {r₀ : ℝ} (P : CompactlySupportedPlanarHamiltonian r₀) (hP : P.IsAutonomous) :
    poissonHamiltonianTimeOneDiffeomorph M (liftPlanarHamiltonianTo4Manifold M P) =
      leafwiseBumpDiffeomorphOfIsotopy M P.toDiskIsotopy := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := A.instMeasurableSpaceFiber
  let _ := A.instBorelSpaceFiber
  let C := AdmitsRegularDiskFibration.fiberDiskChart M
  let H_lift := liftPlanarHamiltonianTo4Manifold M P
  let X₄ : (w : M) → TangentSpace (𝓡 4) w :=
    (adaptedJacobianPoisson M).hamiltonianVectorField H_lift
  have hX₄ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 4)) (𝓡 4).tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X₄ p.2⟩ : TangentBundle (𝓡 4) M)) :=
    (((adaptedJacobianPoisson M).contMDiff_hamiltonianVectorField H_lift).comp
      contMDiff_snd).of_le (by simp)
  ext x
  rw [poissonHamiltonianTimeOneDiffeomorph_apply]
  by_cases hx_pre : x ∈ A.fibration.preimageOpen.1
  · let u_pre : A.fibration.preimageOpen := ⟨x, hx_pre⟩
    let b := (A.fibration.trivialization u_pre).1
    let z := (A.fibration.trivialization u_pre).2
    have hx_emb : x = A.fibration.embed (b, z) := by
      change u_pre.1 = (A.fibration.trivialization.symm (b, z)).1
      rw [Prod.mk.eta, A.fibration.trivialization.symm_apply_apply]
    rw [hx_emb]
    by_cases hz_src : z ∈ C.sourceOpen.1
    · obtain ⟨y₀, hy₀⟩ := C.range_embed.symm.subset hz_src
      rw [← hy₀]
      let ρ_b : ℝ := bumpProfile M b.1
      let c_plane : ℝ → EuclideanPlane := fun u ↦ P.flow (u * ρ_b, y₀.1)
      have hc_smooth : ContDiff ℝ ∞ c_plane :=
        P.contDiff_flow.comp ((contDiff_id.mul contDiff_const).prodMk contDiff_const)
      let yCurve : ℝ → diskOpen :=
        fun u ↦ ⟨c_plane u, P.toDiskIsotopy.mem_unitDisk2 (u * ρ_b) y₀.2⟩
      have hyCurve_smooth : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ yCurve :=
        (TauCeti.ContMDiff.subtypeVal_comp_iff diskOpen yCurve).mp hc_smooth.contMDiff
      let Ψ_b : diskOpen → M := fun w ↦ A.fibration.embed (b, C.embed w)
      have hΨ_smooth : ContMDiff (𝓡 2) (𝓡 4) ∞ Ψ_b :=
        A.fibration.contMDiff_embed.comp (contMDiff_const.prodMk C.contMDiff_embed)
      let γ : ℝ → M := Ψ_b ∘ yCurve
      have hγ0 : γ 0 = A.fibration.embed (b, C.embed y₀) := by
        have hy0 : yCurve 0 = y₀ := by
          apply Subtype.ext
          change TauCeti.timeDependentFlowOf P.vectorField 0 (0 * ρ_b) y₀.1 = y₀.1
          rw [zero_mul, TauCeti.timeDependentFlowOf_self]
        simp [γ, Ψ_b, hy0]
      have hγ1 : γ 1 =
          leafwiseBumpDiffeomorphOfIsotopy M P.toDiskIsotopy
            (A.fibration.embed (b, C.embed y₀)) := by
        rw [leafwiseBumpDiffeomorphOfIsotopy_embed M P.toDiskIsotopy b (C.embed y₀),
          C.liftIsotopyDiffeomorph_embed P.toDiskIsotopy ρ_b y₀]
        change Ψ_b (yCurve 1) =
          Ψ_b ⟨P.toDiskIsotopy.d (ρ_b, y₀.1), P.toDiskIsotopy.mem_unitDisk2 ρ_b y₀.2⟩
        congr 1
        apply Subtype.ext
        change P.flow (1 * ρ_b, y₀.1) = P.flow (ρ_b, y₀.1)
        rw [one_mul]
      have hγ_deriv : ∀ u ∈ Set.Ioo (-1 : ℝ) 2,
          HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 4) γ u
            ((1 : ℝ →L[ℝ] ℝ).smulRight (X₄ (γ u))) := by
        intro u _
        have hdom : ((0, u * ρ_b), y₀.1) ∈ TauCeti.timeDependentFlowDomain P.vectorField := by
          rw [TauCeti.timeDependentFlowDomain_eq_univ P.isComplete_suspension]
          exact Set.mem_univ _
        have hflow_at : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 2)
            (fun t ↦ TauCeti.timeDependentFlowOf P.vectorField 0 t y₀.1) (u * ρ_b)
            ((1 : ℝ →L[ℝ] ℝ).smulRight (P.vectorField 0 (c_plane u))) := by
          have h1 := TauCeti.hasMFDerivAt_timeDependentFlowOf
            (P.contMDiff_vectorField.of_le (by simp)) hdom
          rwa [CMPP.vectorField_eq_of_isAutonomous hP (u * ρ_b)
            (TauCeti.timeDependentFlowOf P.vectorField 0 (u * ρ_b) y₀.1)] at h1
        have hmul := ((hasDerivAt_id' u).mul_const ρ_b).hasFDerivAt.hasMFDerivAt
        have hc_at := hflow_at.comp u hmul
        have hy_diff : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) yCurve u :=
          (hyCurve_smooth u).mdifferentiableAt (by simp)
        have hΨ_diff : MDifferentiableAt (𝓡 2) (𝓡 4) Ψ_b (yCurve u) :=
          (hΨ_smooth (yCurve u)).mdifferentiableAt (by simp)
        refine (hΨ_diff.hasMFDerivAt.comp u hy_diff.hasMFDerivAt).congr_mfderiv ?_
        apply ContinuousLinearMap.ext
        intro s
        let s₀ : ℝ := s
        have hsub_y :
            mfderiv 𝓘(ℝ, ℝ) (𝓡 2) ((Subtype.val : diskOpen → EuclideanPlane) ∘ yCurve) u s =
              mfderiv 𝓘(ℝ, ℝ) (𝓡 2) yCurve u s :=
          TauCeti.Manifold.mfderiv_subtype_val_comp_apply s
        have hc_mf : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) c_plane u s =
            s₀ • (ρ_b • P.vectorField 0 (c_plane u)) := by
          rw [show c_plane = (fun t ↦ TauCeti.timeDependentFlowOf P.vectorField 0 t y₀.1) ∘
              fun y ↦ y * ρ_b from rfl, hc_at.mfderiv]
          change ((1 : ℝ →L[ℝ] ℝ).smulRight (P.vectorField 0 (c_plane u)))
              (ContinuousLinearMap.toSpanSingleton ℝ (1 * ρ_b) s₀) = _
          rw [one_mul, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
            ContinuousLinearMap.smulRight_apply, one_apply_eq_self, mul_smul]
          rfl
        have hy_mf : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) yCurve u s =
            s₀ • (ρ_b • (TauCeti.Manifold.tangentSpaceOpenEquiv (I := 𝓡 2) (yCurve u)).symm
              (P.vectorField 0 (yCurve u).1)) := by
          apply (TauCeti.Manifold.tangentSpaceOpenEquiv (I := 𝓡 2) (yCurve u)).injective
          rw [← hsub_y, show (Subtype.val : diskOpen → EuclideanPlane) ∘ yCurve = c_plane from rfl,
            hc_mf, map_smul, map_smul, ContinuousLinearEquiv.apply_symm_apply]
          exact TauCeti.Manifold.tangentSpaceOpenEquiv_apply (yCurve u) _
        rw [ContinuousLinearMap.comp_apply, hy_mf, map_smul, map_smul]
        change s₀ • (ρ_b • _) = ((1 : ℝ →L[ℝ] ℝ) s₀) • X₄ (γ u)
        rw [one_apply_eq_self]
        congr 1
        exact (hamiltonianVectorField_liftPlanarHamiltonian_embed M P b (yCurve u)).symm
      have hode := TauCeti.timeDependentFlowOf_eq_of_hasMFDerivAt hX₄
        (s := (0 : ℝ)) (t := (1 : ℝ)) (a := (-1 : ℝ)) (b := (2 : ℝ))
        hγ_deriv ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      rwa [hγ0, hγ1] at hode
    · have hX0 : X₄ (A.fibration.embed (b, z)) = 0 :=
        hamiltonianVectorField_liftPlanarHamiltonian_embed_of_notMem_sourceOpen M P b hz_src
      rw [TauCeti.timeDependentFlowOf_eq_self_of_forall_eq_zero hX₄ (fun _ ↦ hX0) 0 1,
        leafwiseBumpDiffeomorphOfIsotopy_embed M P.toDiskIsotopy b z,
        SymplecticDiskChart.liftIsotopyDiffeomorph_apply,
        C.liftThroughChart_of_notMem P.toDiskIsotopy.d (bumpProfile M b.1) hz_src]
  · have hnot_base : A.fibration x ∉ tsupport (bumpProfile M) :=
      fun hm ↦ hx_pre (tsupport_bumpProfile_subset_baseRegion M hm)
    have hX0 : X₄ x = 0 :=
      hamiltonianVectorField_liftPlanarHamiltonian_eq_zero_of_notMem_tsupport_base M P hnot_base
    rw [TauCeti.timeDependentFlowOf_eq_self_of_forall_eq_zero hX₄ (fun _ ↦ hX0) 0 1,
      leafwiseBumpDiffeomorphOfIsotopy_of_notMem M P.toDiskIsotopy hx_pre]

/-- For any finite list `Ps` of autonomous `CompactlySupportedPlanarHamiltonian r₀`s, right-fold
composition `composePoissonHamiltonianTimeOneFlows M` of their lifted 4-manifold Hamiltonians
equals `leafwiseBumpDiffeomorphOfIsotopy M (listToDiskIsotopy hr₀ Ps)`. -/
-- tier: T1
theorem composePoissonHamiltonianTimeOneFlows_map_liftPlanarHamiltonian_eq
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
    [A : AdmitsRegularDiskFibration M]
    {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    {Ps : List (CompactlySupportedPlanarHamiltonian r₀)}
    (hPs : ∀ P ∈ Ps, P.IsAutonomous) :
    composePoissonHamiltonianTimeOneFlows M (Ps.map (liftPlanarHamiltonianTo4Manifold M)) =
      leafwiseBumpDiffeomorphOfIsotopy M
        (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy hr₀ Ps) := by
  induction Ps with
  | nil =>
    rw [List.map_nil, composePoissonHamiltonianTimeOneFlows_nil,
      CompactlySupportedPlanarHamiltonian.listToDiskIsotopy_nil,
      leafwiseBumpDiffeomorphOfIsotopy_refl M hr₀]
  | cons P Ps ih =>
    have hP : P.IsAutonomous := hPs P List.mem_cons_self
    have hPs_tail : ∀ Q ∈ Ps, Q.IsAutonomous :=
      fun Q hQ ↦ hPs Q (List.mem_cons_of_mem P hQ)
    rw [List.map_cons, composePoissonHamiltonianTimeOneFlows_cons, ih hPs_tail,
      poissonHamiltonianTimeOneDiffeomorph_liftPlanarHamiltonian_eq M P hP,
      CompactlySupportedPlanarHamiltonian.listToDiskIsotopy_cons,
      leafwiseBumpDiffeomorphOfIsotopy_compSame]

/-! ## 6. Deliverable R5: Unconditional Poisson–Hamiltonian Realization & Gate G5 Sanity -/

/-- **General 4-Manifold Poisson–Hamiltonian Realization**:
Every compact Hausdorff smooth 4-manifold `M` admitting a positively co-oriented regular-disk
fibration `[A : AdmitsRegularDiskFibration M]` carries a finite list of
smooth Hamiltonians `Hs : List C^∞⟮𝓡 4, M; ℝ⟯` whose composed time-`1` Poisson–Hamiltonian flow
`d_bar` preserves `A.fibration`, `(alignedPositiveVolume M).Ω`, `(alignedPositiveVolume M).μ`, and
`adaptedJacobianPoisson M`, and satisfies `IsTuringComplete ⇑d_bar` (`≠ id`). -/
-- tier: T2
theorem exists_poisson_hamiltonian_realization_fourManifold
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
    [A : AdmitsRegularDiskFibration M] :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    ∃ (Hs : List C^∞⟮𝓡 4, M; ℝ⟯)
      (d_bar : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M),
      d_bar = composePoissonHamiltonianTimeOneFlows M Hs ∧
      ⇑A.fibration ∘ ⇑d_bar = ⇑A.fibration ∧
      SmoothBivector.IsPoissonMap (adaptedJacobianPoisson M).toSmoothBivector
        (adaptedJacobianPoisson M).toSmoothBivector d_bar d_bar.contMDiff ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff (alignedPositiveVolume M).Ω =
        (alignedPositiveVolume M).Ω ∧
      MeasureTheory.MeasurePreserving ⇑d_bar
        (alignedPositiveVolume M).μ (alignedPositiveVolume M).μ ∧
      IsTuringComplete ⇑d_bar ∧
      (⇑d_bar : M → M) ≠ id := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let C_cmpp : HasCMPPCantorCirculationHamiltonians := universalReversibleSimulator_cmpp
  let _ : HasTuringCompleteAreaPreservingDiskIsotopy :=
    @instHasTuringCompleteAreaPreservingDiskIsotopyOfCMPP C_cmpp
  let Hs : List C^∞⟮𝓡 4, M; ℝ⟯ :=
    C_cmpp.generators.map (liftPlanarHamiltonianTo4Manifold M)
  have hcomp :
      leafwiseBumpDiffeomorph M = composePoissonHamiltonianTimeOneFlows M Hs :=
    (composePoissonHamiltonianTimeOneFlows_map_liftPlanarHamiltonian_eq M C_cmpp.r₀_mem_Ioo
      universalReversibleSimulator_cmpp_isAutonomous).symm
  exact ⟨Hs, leafwiseBumpDiffeomorph M, hcomp,
    fibration_comp_leafwiseBumpDiffeomorph M,
    isPoissonMap_leafwiseBumpDiffeomorph M,
    mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm M,
    measurePreserving_leafwiseBumpDiffeomorph M,
    isTuringComplete_leafwiseBumpDiffeomorph M,
    leafwiseBumpDiffeomorph_ne_id M⟩

/-- **Deliverable R5 (Unconditional Poisson–Hamiltonian Realization on `Sphere4`)**:
There exist a finite list of smooth Hamiltonians `Hs : List C^∞⟮𝓡 4, Sphere4; ℝ⟯` and a smooth
diffeomorphism `d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4` equal to the composition of the time-`1`
flows of the Poisson–Hamiltonian vector fields `s4AdaptedPoisson.hamiltonianVectorField H`
(`H ∈ Hs`) such that `d_bar` preserves `s4Fibration`, `s4AlignedPositiveVolume.Ω`,
`s4AlignedPositiveVolume.μ`, and `s4AdaptedPoisson`, and `IsTuringComplete ⇑d_bar`. -/
-- tier: T2
theorem exists_poisson_hamiltonian_realization_S4 :
    ∃ (Hs : List C^∞⟮𝓡 4, Sphere4; ℝ⟯)
      (d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4),
      d_bar = composePoissonHamiltonianTimeOneFlows Sphere4 Hs ∧
      s4Fibration ∘ ⇑d_bar = s4Fibration ∧
      SmoothBivector.IsPoissonMap s4AdaptedPoisson.toSmoothBivector
        s4AdaptedPoisson.toSmoothBivector d_bar d_bar.contMDiff ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff s4AlignedPositiveVolume.Ω =
        s4AlignedPositiveVolume.Ω ∧
      MeasureTheory.MeasurePreserving ⇑d_bar
        s4AlignedPositiveVolume.μ s4AlignedPositiveVolume.μ ∧
      IsTuringComplete ⇑d_bar ∧
      (⇑d_bar : Sphere4 → Sphere4) ≠ id :=
  exists_poisson_hamiltonian_realization_fourManifold Sphere4

/-- **Unconditional Closed 4-Manifold Poisson–Hamiltonian Realization (`L-R3`)**:
Every nonempty compact Hausdorff smooth 4-manifold `M` equipped with any positive volume 4-form
`V_M : PositiveVolumeForm (𝓡 4) M` (with zero fibration typeclasses) carries an aligned positive
volume 4-form `V` positively co-oriented with `V_M`, a smooth map `f : M → Sphere2`, a compatible
unimodular Jacobian–Poisson structure `π_f`, and a finite list of smooth Hamiltonians `Hs` whose
composed time-`1` Poisson–Hamiltonian flow `d_bar` preserves `f`, `V.Ω`, `V.μ`, and `π_f`, and
satisfies `IsTuringComplete ⇑d_bar` (`≠ id`). -/
-- tier: T2
theorem exists_poisson_hamiltonian_realization_closedFourManifold
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [T2Space M] [Nonempty M]
    (V_M : PositiveVolumeForm (𝓡 4) M) :
    ∃ (V : PositiveVolumeForm (𝓡 4) M)
      (π_f : PoissonStructure (𝓡 4) M)
      (f : M → Sphere2)
      (Hs : List C^∞⟮𝓡 4, M; ℝ⟯)
      (d_bar : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M),
      (∀ x : M, ∃ a : ℝ, 0 < a ∧ V.Ω.1 x = a • V_M.Ω.1 x) ∧
      π_f.IsUnimodularWithVolume V.Ω ∧
      d_bar = composePoissonStructureTimeOneFlows M π_f Hs ∧
      f ∘ ⇑d_bar = f ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_bar d_bar.contMDiff ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasureTheory.MeasurePreserving ⇑d_bar V.μ V.μ ∧
      IsTuringComplete ⇑d_bar ∧
      (⇑d_bar : M → M) ≠ id ∧
      V.μ = TauCeti.RoughForm.measure V.Ω.1 := by
  let A : AdmitsRegularDiskFibration M :=
    AdmitsRegularDiskFibration.ofPositiveVolumeForm V_M
  let _ : AdmitsRegularDiskFibration M := A
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := A.instMeasurableSpaceFiber
  let _ := A.instBorelSpaceFiber
  let C_cmpp : HasCMPPCantorCirculationHamiltonians := universalReversibleSimulator_cmpp
  let _ : HasTuringCompleteAreaPreservingDiskIsotopy :=
    @instHasTuringCompleteAreaPreservingDiskIsotopyOfCMPP C_cmpp
  let Hs : List C^∞⟮𝓡 4, M; ℝ⟯ :=
    C_cmpp.generators.map (liftPlanarHamiltonianTo4Manifold M)
  have hcomp :
      leafwiseBumpDiffeomorph M =
        composePoissonStructureTimeOneFlows M (adaptedJacobianPoisson M) Hs := by
    rw [composePoissonStructureTimeOneFlows_adaptedJacobianPoisson]
    exact (composePoissonHamiltonianTimeOneFlows_map_liftPlanarHamiltonian_eq M C_cmpp.r₀_mem_Ioo
      universalReversibleSimulator_cmpp_isAutonomous).symm
  exact ⟨alignedPositiveVolume M, adaptedJacobianPoisson M, ⇑A.fibration, Hs,
    leafwiseBumpDiffeomorph M,
    fun x ↦ alignedVolumeForm_pos_cooriented M x,
    isUnimodularWithVolume_adaptedJacobianPoisson M,
    hcomp,
    fibration_comp_leafwiseBumpDiffeomorph M,
    isPoissonMap_leafwiseBumpDiffeomorph M,
    mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm M,
    measurePreserving_leafwiseBumpDiffeomorph M,
    isTuringComplete_leafwiseBumpDiffeomorph M,
    leafwiseBumpDiffeomorph_ne_id M,
    rfl⟩

/-! ## 7. Purely Wrinkled, Broken Lefschetz & Exact-Volume Moser R5 Realizations (`SC-R2`/`SC-R3`)
-/

/-- Pointwise evaluation of `poissonStructureTimeOneDiffeomorph M π_str H` as the time-`1` flow of
`π_str.hamiltonianVectorField H`. -/
-- tier: T1
@[simp]
theorem poissonStructureTimeOneDiffeomorph_apply
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
    (π_str : PoissonStructure (𝓡 4) M) (H : C^∞⟮𝓡 4, M; ℝ⟯) (x : M) :
    poissonStructureTimeOneDiffeomorph M π_str H x =
      TauCeti.timeDependentFlowOf (fun _ : ℝ ↦ π_str.hamiltonianVectorField H) 0 1 x := by
  rw [poissonStructureTimeOneDiffeomorph, TauCeti.timeDependentFlowDiffeomorph_apply]

/-- **Moser Conjugation of Time-`1` Poisson–Hamiltonian Flows (`SC-R3`)**:
For any global Moser bundle `W : MoserVolume V₀ V₁`, smooth map `f : M → Sphere2`, and smooth
Hamiltonian `h : C^∞⟮𝓡 4, M; ℝ⟯`, the time-`1` Hamiltonian flow of `h ∘ W.ψ` with respect to
`W.pullbackJacobianPoisson f hf` equals `W.conjDiffeomorph` applied to the time-`1` Hamiltonian
flow of `h` with respect to `jacobianPoissonOfPositiveVolume V₁ S2VolumeForm f hf`. -/
-- tier: T2
theorem MoserVolume.poissonStructureTimeOneDiffeomorph_comp
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
    {V₀ V₁ : PositiveVolumeForm (𝓡 4) M} (W : MoserVolume V₀ V₁)
    (f : M → Sphere2) (hf : ContMDiff (𝓡 4) (𝓡 2) ∞ f) (h : C^∞⟮𝓡 4, M; ℝ⟯) :
    poissonStructureTimeOneDiffeomorph M (W.pullbackJacobianPoisson f hf)
        (h.comp ⟨W.ψ, W.ψ.contMDiff⟩) =
      W.conjDiffeomorph (poissonStructureTimeOneDiffeomorph M
        (jacobianPoissonOfPositiveVolume V₁ S2VolumeForm f hf) h) := by
  let P_pull := W.pullbackJacobianPoisson f hf
  let P₁ := jacobianPoissonOfPositiveVolume V₁ S2VolumeForm f hf
  let h_pull := h.comp ⟨W.ψ, W.ψ.contMDiff⟩
  let X_pull := P_pull.hamiltonianVectorField h_pull
  let X₁ := P₁.hamiltonianVectorField h
  have hX_pull : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 4)) (𝓡 4).tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X_pull p.2⟩ : TangentBundle (𝓡 4) M)) :=
    ((P_pull.contMDiff_hamiltonianVectorField h_pull).comp contMDiff_snd).of_le (by simp)
  have hX₁ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 4)) (𝓡 4).tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X₁ p.2⟩ : TangentBundle (𝓡 4) M)) :=
    ((P₁.contMDiff_hamiltonianVectorField h).comp contMDiff_snd).of_le (by simp)
  apply Diffeomorph.ext
  intro x
  let c : ℝ → M := fun u ↦ TauCeti.timeDependentFlowOf (fun _ : ℝ ↦ X₁) 0 u (W.ψ x)
  let γ : ℝ → M := fun u ↦ W.ψ.symm (c u)
  have hγ0 : γ 0 = x := by
    change W.ψ.symm (TauCeti.timeDependentFlowOf (fun _ : ℝ ↦ X₁) 0 0 (W.ψ x)) = x
    rw [TauCeti.timeDependentFlowOf_self, W.ψ.symm_apply_apply]
  have hγ1 : γ 1 = W.conjDiffeomorph (poissonStructureTimeOneDiffeomorph M P₁ h) x := by
    rw [MoserVolume.conjDiffeomorph_apply, poissonStructureTimeOneDiffeomorph_apply]
  have hγ_deriv : ∀ u ∈ Set.Ioo (-1 : ℝ) 2,
      HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 4) γ u ((1 : ℝ →L[ℝ] ℝ).smulRight (X_pull (γ u))) := by
    intro u _
    have hdom : ((0, u), W.ψ x) ∈ TauCeti.timeDependentFlowDomain (fun _ : ℝ ↦ X₁) := by
      rw [TauCeti.timeDependentFlowDomain_eq_univ
        (isComplete_hamiltonianVectorField_poissonStructure M P₁ h)]
      exact Set.mem_univ _
    have hc_at : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 4) c u ((1 : ℝ →L[ℝ] ℝ).smulRight (X₁ (c u))) :=
      TauCeti.hasMFDerivAt_timeDependentFlowOf hX₁ hdom
    have hsymm_at :
        HasMFDerivAt (𝓡 4) (𝓡 4) W.ψ.symm (c u) (mfderiv (𝓡 4) (𝓡 4) W.ψ.symm (c u)) :=
      (W.ψ.symm.contMDiff.mdifferentiableAt (by simp)).hasMFDerivAt
    refine (hsymm_at.comp u hc_at).congr_mfderiv ?_
    apply ContinuousLinearMap.ext
    intro s
    let s₀ : ℝ := s
    change mfderiv (𝓡 4) (𝓡 4) W.ψ.symm (c u) (((1 : ℝ →L[ℝ] ℝ) s₀) • X₁ (c u)) =
      ((1 : ℝ →L[ℝ] ℝ) s₀) • X_pull (γ u)
    rw [map_smul]
    congr 1
    have hrel := W.hamiltonianVectorField_pullbackJacobianPoisson_comp f hf h (γ u)
    have hψγ : W.ψ (γ u) = c u := W.ψ.apply_symm_apply (c u)
    change mfderiv (𝓡 4) (𝓡 4) W.ψ.symm (c u) (X₁ (c u)) = X_pull (γ u)
    dsimp only [X_pull, X₁, P_pull, P₁, h_pull]
    rw [hrel, hψγ]
  have hode := TauCeti.timeDependentFlowOf_eq_of_hasMFDerivAt hX_pull
    (s := (0 : ℝ)) (t := (1 : ℝ)) (a := (-1 : ℝ)) (b := (2 : ℝ))
    hγ_deriv ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
  rw [hγ0, hγ1] at hode
  rw [poissonStructureTimeOneDiffeomorph_apply]
  exact hode

/-- **Moser Conjugation of Right-Fold Poisson–Hamiltonian Flow Lists (`SC-R3`)**:
Pulling back a finite list `Hs : List C^∞⟮𝓡 4, M; ℝ⟯` of Hamiltonians along `W.ψ` conjugates
their composed time-`1` Poisson–Hamiltonian flow by `W.ψ`. -/
-- tier: T1
theorem MoserVolume.composePoissonStructureTimeOneFlows_map_comp
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
    {V₀ V₁ : PositiveVolumeForm (𝓡 4) M} (W : MoserVolume V₀ V₁)
    (f : M → Sphere2) (hf : ContMDiff (𝓡 4) (𝓡 2) ∞ f) (Hs : List C^∞⟮𝓡 4, M; ℝ⟯) :
    composePoissonStructureTimeOneFlows M (W.pullbackJacobianPoisson f hf)
        (Hs.map fun h ↦ h.comp ⟨W.ψ, W.ψ.contMDiff⟩) =
      W.conjDiffeomorph (composePoissonStructureTimeOneFlows M
        (jacobianPoissonOfPositiveVolume V₁ S2VolumeForm f hf) Hs) := by
  let P_pull := W.pullbackJacobianPoisson f hf
  let P₁ := jacobianPoissonOfPositiveVolume V₁ S2VolumeForm f hf
  induction Hs with
  | nil =>
    apply Diffeomorph.ext
    intro x
    change x = W.ψ.symm (W.ψ x)
    exact (W.ψ.symm_apply_apply x).symm
  | cons H Hs ih =>
    rw [List.map_cons]
    change (composePoissonStructureTimeOneFlows M P_pull
          (Hs.map fun h ↦ h.comp ⟨W.ψ, W.ψ.contMDiff⟩)).trans
        (poissonStructureTimeOneDiffeomorph M P_pull (H.comp ⟨W.ψ, W.ψ.contMDiff⟩)) =
      W.conjDiffeomorph ((composePoissonStructureTimeOneFlows M P₁ Hs).trans
        (poissonStructureTimeOneDiffeomorph M P₁ H))
    rw [ih, W.poissonStructureTimeOneDiffeomorph_comp f hf H]
    apply Diffeomorph.ext
    intro x
    change W.ψ.symm (poissonStructureTimeOneDiffeomorph M P₁ H
      (W.ψ (W.ψ.symm (composePoissonStructureTimeOneFlows M P₁ Hs (W.ψ x))))) =
      W.ψ.symm (poissonStructureTimeOneDiffeomorph M P₁ H
        (composePoissonStructureTimeOneFlows M P₁ Hs (W.ψ x)))
    rw [W.ψ.apply_symm_apply]

/-- **Poisson–Hamiltonian Realization over `PurelyWrinkledFibration` (`SC-R2` / R5 Companion)**:
For any positively co-oriented `PurelyWrinkledFibration` `P : M → Sphere2`, exhibits an aligned
positive volume 4-form `V` (`V.μ = TauCeti.RoughForm.measure V.Ω.1`), a **generically rank-2**
(`π_f.IsGenericallyRankTwo`) unimodular Jacobian–Poisson structure `π_f`, and a finite list `Hs` of
smooth Hamiltonians whose composed time-`1` Poisson–Hamiltonian flow `d_bar` preserves `P.toFun`,
`π_f`, `V.Ω`, and `V.μ`, and satisfies `IsTuringComplete ⇑d_bar` (`≠ id`). -/
-- tier: T2
theorem exists_poisson_hamiltonian_realization_of_purelyWrinkled
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
    (V_M : PositiveVolumeForm (𝓡 4) M)
    (F : Type) [TopologicalSpace F] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F]
    [IsManifold (𝓡 2) ∞ F] [T2Space F] [CompactSpace F] [Nonempty F]
    [MeasurableSpace F] [BorelSpace F]
    (P : PurelyWrinkledFibration (𝓡 4) M (𝓡 2) Sphere2 F)
    (V_F : PositiveVolumeForm (𝓡 2) F)
    (hpos : ∀ u : P.toRegularDiskFibration.preimageOpen, ∃ c : ℝ, 0 < c ∧
      (TauCeti.SmoothForm.mpullback P.trivialization P.trivialization.contMDiff
          (TauCeti.SmoothForm.wedge
            (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd V_F.Ω)
            (TauCeti.SmoothForm.mpullback (Subtype.val ∘ Prod.fst)
              (contMDiff_subtype_val.comp contMDiff_fst) S2VolumeForm))).1 u =
        c • (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val V_M.Ω).1 u) :
    ∃ (V : PositiveVolumeForm (𝓡 4) M)
      (π_f : PoissonStructure (𝓡 4) M)
      (Hs : List C^∞⟮𝓡 4, M; ℝ⟯)
      (d_bar : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M),
      (∀ x : M, ∃ a : ℝ, 0 < a ∧ V.Ω.1 x = a • V_M.Ω.1 x) ∧
      π_f.IsUnimodularWithVolume V.Ω ∧
      π_f.IsGenericallyRankTwo ∧
      d_bar = composePoissonStructureTimeOneFlows M π_f Hs ∧
      P.toFun ∘ ⇑d_bar = P.toFun ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_bar d_bar.contMDiff ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasureTheory.MeasurePreserving ⇑d_bar V.μ V.μ ∧
      IsTuringComplete ⇑d_bar ∧
      (⇑d_bar : M → M) ≠ id ∧
      V.μ = TauCeti.RoughForm.measure V.Ω.1 := by
  let A : AdmitsWrinkledOrBrokenLefschetzFibration M :=
    AdmitsWrinkledOrBrokenLefschetzFibration.ofPurelyWrinkled V_M F P V_F hpos
  let _ : AdmitsWrinkledOrBrokenLefschetzFibration M := A
  obtain ⟨Hs, d_bar, hcomp, hfib, hpoiss, hvol, hmp, htc, hne⟩ :=
    exists_poisson_hamiltonian_realization_fourManifold M
  have hcomp' : d_bar = composePoissonStructureTimeOneFlows M (adaptedJacobianPoisson M) Hs := by
    rw [composePoissonStructureTimeOneFlows_adaptedJacobianPoisson]
    exact hcomp
  exact ⟨alignedPositiveVolume M, adaptedJacobianPoisson M, Hs, d_bar,
    fun x ↦ alignedVolumeForm_pos_cooriented M x,
    isUnimodularWithVolume_adaptedJacobianPoisson M,
    isGenericallyRankTwo_adaptedJacobianPoisson M,
    hcomp', hfib, hpoiss, hvol, hmp, htc, hne, rfl⟩

/-- **Poisson–Hamiltonian Realization over `BrokenLefschetzFibration` (`SC-R2` / R5 Companion)**:
Deforms any positively co-oriented `BrokenLefschetzFibration` `B : M → Sphere2` via Lekili's
wrinkling deformation (`H : ℝ → M → Sphere2`, `H 0 = B.toFun`, `H 1 = P.toFun`) to a
`PurelyWrinkledFibration` `P : M → Sphere2` and realizes a Turing complete Poisson diffeomorphism on
`M` as a finite composition of time-`1` Hamiltonian flows of the **generically rank-2** unimodular
Jacobian–Poisson structure `π_f` adapted to `P.toFun`. -/
-- tier: T2
theorem exists_poisson_hamiltonian_realization_of_brokenLefschetz
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
    (V_M : PositiveVolumeForm (𝓡 4) M)
    (F : Type) [TopologicalSpace F] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F]
    [IsManifold (𝓡 2) ∞ F] [T2Space F] [CompactSpace F] [Nonempty F]
    [MeasurableSpace F] [BorelSpace F]
    (B : BrokenLefschetzFibration (𝓡 4) M (𝓡 2) Sphere2 F)
    (V_F : PositiveVolumeForm (𝓡 2) F)
    (hpos : ∀ u : B.toRegularDiskFibration.preimageOpen, ∃ c : ℝ, 0 < c ∧
      (TauCeti.SmoothForm.mpullback B.trivialization B.trivialization.contMDiff
          (TauCeti.SmoothForm.wedge
            (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd V_F.Ω)
            (TauCeti.SmoothForm.mpullback (Subtype.val ∘ Prod.fst)
              (contMDiff_subtype_val.comp contMDiff_fst) S2VolumeForm))).1 u =
        c • (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val V_M.Ω).1 u) :
    ∃ (P : PurelyWrinkledFibration (𝓡 4) M (𝓡 2) Sphere2 F)
      (K : Set M) (H : ℝ → M → Sphere2)
      (V : PositiveVolumeForm (𝓡 4) M)
      (π_f : PoissonStructure (𝓡 4) M)
      (Hs : List C^∞⟮𝓡 4, M; ℝ⟯)
      (d_bar : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M),
      IsCompact K ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 4)) (𝓡 2) ∞ (Function.uncurry H) ∧
      (∀ x, H 0 x = B.toFun x) ∧
      (∀ x, H 1 x = P.toFun x) ∧
      (∀ (t : ℝ), ∀ x ∉ K, H t x = B.toFun x) ∧
      (∀ x : M, ∃ a : ℝ, 0 < a ∧ V.Ω.1 x = a • V_M.Ω.1 x) ∧
      π_f.IsUnimodularWithVolume V.Ω ∧
      π_f.IsGenericallyRankTwo ∧
      d_bar = composePoissonStructureTimeOneFlows M π_f Hs ∧
      P.toFun ∘ ⇑d_bar = P.toFun ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_bar d_bar.contMDiff ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasureTheory.MeasurePreserving ⇑d_bar V.μ V.μ ∧
      IsTuringComplete ⇑d_bar ∧
      (⇑d_bar : M → M) ≠ id ∧
      V.μ = TauCeti.RoughForm.measure V.Ω.1 := by
  obtain ⟨P, K, H, _, _, hK_comp, _, _, _, _, hH_md, hH_0, hH_1, hH_stat, hpos_P⟩ :=
    Main.exists_pos_cooriented_purelyWrinkledFibration_of_brokenLefschetz M V_M F B V_F hpos
  obtain ⟨V, π_f, Hs, d_bar, hpos_V, hunimV, hgen, hcomp, hfib, hpoiss, hvol, hmp, htc, hne,
      hμ_eq⟩ :=
    exists_poisson_hamiltonian_realization_of_purelyWrinkled M V_M F P V_F hpos_P
  exact ⟨P, K, H, V, π_f, Hs, d_bar, hK_comp, hH_md, hH_0, hH_1, hH_stat, hpos_V, hunimV, hgen,
    hcomp, hfib, hpoiss, hvol, hmp, htc, hne, hμ_eq⟩

/-- **Exact-`V_M` Closed 4-Manifold Poisson–Hamiltonian Realization (`SC-R3`, Zero `ConnectedSpace`
Assumption)**:
Every nonempty compact Hausdorff smooth 4-manifold `M` equipped with **any** positive volume 4-form
`V_M : PositiveVolumeForm (𝓡 4) M` (requiring **zero** `[ConnectedSpace M]` assumption and **zero**
fibration typeclasses!) carries a smooth map `f : M → Sphere2`, a Poisson structure `π_f` globally
unimodular with **`V_M.Ω` itself**, and a finite list `Hs` of smooth Hamiltonians whose composed
time-`1` Poisson–Hamiltonian flow `d_exact` preserves `f`, `π_f`, **`V_M.Ω` itself**, and **`V_M.μ`
itself**, and satisfies `IsTuringComplete ⇑d_exact` (`≠ id`). -/
-- tier: T2
theorem exists_exactVolumePreserving_poisson_hamiltonian_realization_closedFourManifold
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [T2Space M] [Nonempty M]
    (V_M : PositiveVolumeForm (𝓡 4) M) :
    ∃ (π_f : PoissonStructure (𝓡 4) M)
      (f : M → Sphere2)
      (Hs : List C^∞⟮𝓡 4, M; ℝ⟯)
      (d_exact : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M),
      ContMDiff (𝓡 4) (𝓡 2) ∞ f ∧
      π_f.IsUnimodularWithVolume V_M.Ω ∧
      d_exact = composePoissonStructureTimeOneFlows M π_f Hs ∧
      f ∘ ⇑d_exact = f ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_exact d_exact.contMDiff ∧
      TauCeti.SmoothForm.mpullback d_exact d_exact.contMDiff V_M.Ω = V_M.Ω ∧
      MeasureTheory.MeasurePreserving ⇑d_exact V_M.μ V_M.μ ∧
      IsTuringComplete ⇑d_exact ∧
      (⇑d_exact : M → M) ≠ id := by
  let A : AdmitsRegularDiskFibration M := AdmitsRegularDiskFibration.ofPositiveVolumeForm V_M
  let _ : AdmitsRegularDiskFibration M := A
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := A.instMeasurableSpaceFiber
  let _ := A.instBorelSpaceFiber
  let W : MoserVolume V_M (alignedPositiveVolume M) :=
    MoserVolume.ofPositivelyCooriented V_M (alignedPositiveVolume M)
      (fun x ↦ alignedVolumeForm_pos_cooriented M x)
  let C_cmpp : HasCMPPCantorCirculationHamiltonians := universalReversibleSimulator_cmpp
  let _ : HasTuringCompleteAreaPreservingDiskIsotopy :=
    @instHasTuringCompleteAreaPreservingDiskIsotopyOfCMPP C_cmpp
  let Hs₀ : List C^∞⟮𝓡 4, M; ℝ⟯ := C_cmpp.generators.map (liftPlanarHamiltonianTo4Manifold M)
  let Hs : List C^∞⟮𝓡 4, M; ℝ⟯ := Hs₀.map fun h ↦ h.comp ⟨W.ψ, W.ψ.contMDiff⟩
  let f₀ : M → Sphere2 := ⇑A.fibration
  have hf₀ : ContMDiff (𝓡 4) (𝓡 2) ∞ f₀ := A.fibration.contMDiff_toFun
  have hcomp₀ :
      leafwiseBumpDiffeomorph M =
        composePoissonStructureTimeOneFlows M (adaptedJacobianPoisson M) Hs₀ := by
    rw [composePoissonStructureTimeOneFlows_adaptedJacobianPoisson]
    exact (composePoissonHamiltonianTimeOneFlows_map_liftPlanarHamiltonian_eq M C_cmpp.r₀_mem_Ioo
      universalReversibleSimulator_cmpp_isAutonomous).symm
  have hcomp :
      W.conjDiffeomorph (leafwiseBumpDiffeomorph M) =
        composePoissonStructureTimeOneFlows M (W.pullbackJacobianPoisson f₀ hf₀) Hs := by
    rw [W.composePoissonStructureTimeOneFlows_map_comp f₀ hf₀ Hs₀,
      show jacobianPoissonOfPositiveVolume (alignedPositiveVolume M) S2VolumeForm f₀ hf₀ =
        adaptedJacobianPoisson M from rfl, ← hcomp₀]
  exact ⟨W.pullbackJacobianPoisson f₀ hf₀, f₀ ∘ ⇑W.ψ, Hs,
    W.conjDiffeomorph (leafwiseBumpDiffeomorph M),
    hf₀.comp W.ψ.contMDiff,
    W.isUnimodularWithVolume_pullbackJacobianPoisson f₀ hf₀,
    hcomp,
    W.fibration_comp_conjDiffeomorph (fibration_comp_leafwiseBumpDiffeomorph M),
    W.isPoissonMap_conjDiffeomorph f₀ hf₀ (isPoissonMap_leafwiseBumpDiffeomorph M),
    W.mpullback_conjDiffeomorph (connectedComponent_leafwiseBumpDiffeomorph M)
      (mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm M),
    W.measurePreserving_conjDiffeomorph (connectedComponent_leafwiseBumpDiffeomorph M)
      (mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm M),
    W.isTuringComplete_conjDiffeomorph (isTuringComplete_leafwiseBumpDiffeomorph M),
    W.conjDiffeomorph_ne_id (isTuringComplete_leafwiseBumpDiffeomorph M)⟩

/-- **Exact Round-Volume Poisson–Hamiltonian Realization on `Sphere4` (`SC-R3`)**:
Exhibits a smooth map `f : Sphere4 → Sphere2`, a **generically rank-2** Poisson structure `π_f`
unimodular with the **exact standard round volume form `S4PositiveVolumeForm.Ω`**, and a finite list
`Hs` of smooth Hamiltonians whose composed time-`1` Poisson–Hamiltonian flow `d_exact` preserves
`f`, `π_f`, **`S4PositiveVolumeForm.Ω`**, and **`S4PositiveVolumeForm.μ`**, and is Turing complete
(`IsTuringComplete ⇑d_exact`, `≠ id`). -/
-- tier: T2
theorem exists_exactVolumePreserving_poisson_hamiltonian_realization_S4 :
    ∃ (π_f : PoissonStructure (𝓡 4) Sphere4)
      (f : Sphere4 → Sphere2)
      (Hs : List C^∞⟮𝓡 4, Sphere4; ℝ⟯)
      (d_exact : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4),
      ContMDiff (𝓡 4) (𝓡 2) ∞ f ∧
      π_f.IsUnimodularWithVolume S4PositiveVolumeForm.Ω ∧
      π_f.IsGenericallyRankTwo ∧
      d_exact = composePoissonStructureTimeOneFlows Sphere4 π_f Hs ∧
      f ∘ ⇑d_exact = f ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_exact d_exact.contMDiff ∧
      TauCeti.SmoothForm.mpullback d_exact d_exact.contMDiff S4PositiveVolumeForm.Ω =
        S4PositiveVolumeForm.Ω ∧
      MeasureTheory.MeasurePreserving ⇑d_exact S4PositiveVolumeForm.μ S4PositiveVolumeForm.μ ∧
      IsTuringComplete ⇑d_exact ∧
      (⇑d_exact : Sphere4 → Sphere4) ≠ id ∧
      S4PositiveVolumeForm.μ = TauCeti.RoughForm.measure S4PositiveVolumeForm.Ω.1 := by
  let W : MoserVolume S4PositiveVolumeForm s4AlignedPositiveVolume :=
    MoserVolume.ofPositivelyCooriented S4PositiveVolumeForm s4AlignedPositiveVolume
      (fun x ↦ alignedVolumeForm_pos_cooriented Sphere4 x)
  let C_cmpp : HasCMPPCantorCirculationHamiltonians := universalReversibleSimulator_cmpp
  let _ : HasTuringCompleteAreaPreservingDiskIsotopy :=
    @instHasTuringCompleteAreaPreservingDiskIsotopyOfCMPP C_cmpp
  let Hs₀ : List C^∞⟮𝓡 4, Sphere4; ℝ⟯ :=
    C_cmpp.generators.map (liftPlanarHamiltonianTo4Manifold Sphere4)
  let Hs : List C^∞⟮𝓡 4, Sphere4; ℝ⟯ := Hs₀.map fun h ↦ h.comp ⟨W.ψ, W.ψ.contMDiff⟩
  have hcomp₀ :
      s4TuringDiffeomorph = composePoissonStructureTimeOneFlows Sphere4 s4AdaptedPoisson Hs₀ := by
    change leafwiseBumpDiffeomorph Sphere4 =
      composePoissonStructureTimeOneFlows Sphere4 (adaptedJacobianPoisson Sphere4) Hs₀
    rw [composePoissonStructureTimeOneFlows_adaptedJacobianPoisson]
    exact (composePoissonHamiltonianTimeOneFlows_map_liftPlanarHamiltonian_eq Sphere4
      C_cmpp.r₀_mem_Ioo universalReversibleSimulator_cmpp_isAutonomous).symm
  have hcomp :
      W.conjDiffeomorph s4TuringDiffeomorph =
        composePoissonStructureTimeOneFlows Sphere4
          (W.pullbackJacobianPoisson s4Fibration contMDiff_s4Fibration) Hs := by
    rw [W.composePoissonStructureTimeOneFlows_map_comp s4Fibration contMDiff_s4Fibration Hs₀,
      show jacobianPoissonOfPositiveVolume s4AlignedPositiveVolume S2VolumeForm s4Fibration
          contMDiff_s4Fibration = s4AdaptedPoisson from rfl,
      ← hcomp₀]
  exact ⟨W.pullbackJacobianPoisson s4Fibration contMDiff_s4Fibration,
    s4Fibration ∘ ⇑W.ψ, Hs, W.conjDiffeomorph s4TuringDiffeomorph,
    contMDiff_s4Fibration.comp W.ψ.contMDiff,
    W.isUnimodularWithVolume_pullbackJacobianPoisson s4Fibration contMDiff_s4Fibration,
    (W.isGenericallyRankTwo_pullbackJacobianPoisson_iff s4Fibration contMDiff_s4Fibration).mpr
      isGenericallyRankTwo_s4AdaptedPoisson,
    hcomp,
    W.fibration_comp_conjDiffeomorph (fibration_comp_leafwiseBumpDiffeomorph Sphere4),
    W.isPoissonMap_conjDiffeomorph s4Fibration contMDiff_s4Fibration
      (isPoissonMap_leafwiseBumpDiffeomorph Sphere4),
    W.mpullback_conjDiffeomorph (connectedComponent_leafwiseBumpDiffeomorph Sphere4)
      (mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm Sphere4),
    W.measurePreserving_conjDiffeomorph (connectedComponent_leafwiseBumpDiffeomorph Sphere4)
      (mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm Sphere4),
    W.isTuringComplete_conjDiffeomorph (isTuringComplete_leafwiseBumpDiffeomorph Sphere4),
    W.conjDiffeomorph_ne_id (isTuringComplete_leafwiseBumpDiffeomorph Sphere4),
    rfl⟩

/-- **Exact-`V_M` Poisson–Hamiltonian Realization over `PurelyWrinkledFibration` (`SC-R2` +
`SC-R3`)**:
Combines `ofPurelyWrinkled` with componentwise Moser conjugation (`W.ψ`, zero `[ConnectedSpace M]`
assumption!) to obtain a `PurelyWrinkledFibration` `P_exact`, a **generically rank-2** Poisson
structure `π_f` unimodular with **`V_M.Ω` itself**, and a finite list `Hs` of smooth Hamiltonians
whose composed time-`1` flow `d_exact` preserves `P_exact.toFun`, `π_f`, **`V_M.Ω`**, and
**`V_M.μ`**, and satisfies `IsTuringComplete ⇑d_exact` (`≠ id`). -/
-- tier: T2
theorem exists_exactVolumePreserving_poisson_hamiltonian_realization_of_purelyWrinkled
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
    (V_M : PositiveVolumeForm (𝓡 4) M)
    (F : Type) [TopologicalSpace F] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F]
    [IsManifold (𝓡 2) ∞ F] [T2Space F] [CompactSpace F] [Nonempty F]
    [MeasurableSpace F] [BorelSpace F]
    (P : PurelyWrinkledFibration (𝓡 4) M (𝓡 2) Sphere2 F)
    (V_F : PositiveVolumeForm (𝓡 2) F)
    (hpos : ∀ u : P.toRegularDiskFibration.preimageOpen, ∃ c : ℝ, 0 < c ∧
      (TauCeti.SmoothForm.mpullback P.trivialization P.trivialization.contMDiff
          (TauCeti.SmoothForm.wedge
            (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd V_F.Ω)
            (TauCeti.SmoothForm.mpullback (Subtype.val ∘ Prod.fst)
              (contMDiff_subtype_val.comp contMDiff_fst) S2VolumeForm))).1 u =
        c • (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val V_M.Ω).1 u) :
    ∃ (P_exact : PurelyWrinkledFibration (𝓡 4) M (𝓡 2) Sphere2 F)
      (π_f : PoissonStructure (𝓡 4) M)
      (Hs : List C^∞⟮𝓡 4, M; ℝ⟯)
      (d_exact : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M),
      π_f.IsUnimodularWithVolume V_M.Ω ∧
      π_f.IsGenericallyRankTwo ∧
      d_exact = composePoissonStructureTimeOneFlows M π_f Hs ∧
      P_exact.toFun ∘ ⇑d_exact = P_exact.toFun ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_exact d_exact.contMDiff ∧
      TauCeti.SmoothForm.mpullback d_exact d_exact.contMDiff V_M.Ω = V_M.Ω ∧
      MeasureTheory.MeasurePreserving ⇑d_exact V_M.μ V_M.μ ∧
      IsTuringComplete ⇑d_exact ∧
      (⇑d_exact : M → M) ≠ id := by
  let A : AdmitsWrinkledOrBrokenLefschetzFibration M :=
    AdmitsWrinkledOrBrokenLefschetzFibration.ofPurelyWrinkled V_M F P V_F hpos
  let _ : AdmitsWrinkledOrBrokenLefschetzFibration M := A
  let W : MoserVolume V_M (alignedPositiveVolume M) :=
    MoserVolume.ofPositivelyCooriented V_M (alignedPositiveVolume M)
      (fun x ↦ alignedVolumeForm_pos_cooriented M x)
  let C_cmpp : HasCMPPCantorCirculationHamiltonians := universalReversibleSimulator_cmpp
  let _ : HasTuringCompleteAreaPreservingDiskIsotopy :=
    @instHasTuringCompleteAreaPreservingDiskIsotopyOfCMPP C_cmpp
  let Hs₀ : List C^∞⟮𝓡 4, M; ℝ⟯ := C_cmpp.generators.map (liftPlanarHamiltonianTo4Manifold M)
  let Hs : List C^∞⟮𝓡 4, M; ℝ⟯ := Hs₀.map fun h ↦ h.comp ⟨W.ψ, W.ψ.contMDiff⟩
  have hcomp₀ :
      leafwiseBumpDiffeomorph M =
        composePoissonStructureTimeOneFlows M (adaptedJacobianPoisson M) Hs₀ := by
    rw [composePoissonStructureTimeOneFlows_adaptedJacobianPoisson]
    exact (composePoissonHamiltonianTimeOneFlows_map_liftPlanarHamiltonian_eq M C_cmpp.r₀_mem_Ioo
      universalReversibleSimulator_cmpp_isAutonomous).symm
  have hcomp :
      W.conjDiffeomorph (leafwiseBumpDiffeomorph M) =
        composePoissonStructureTimeOneFlows M
          (W.pullbackJacobianPoisson P.toFun P.contMDiff_toFun) Hs := by
    rw [W.composePoissonStructureTimeOneFlows_map_comp P.toFun P.contMDiff_toFun Hs₀,
      show jacobianPoissonOfPositiveVolume (alignedPositiveVolume M) S2VolumeForm P.toFun
          P.contMDiff_toFun = adaptedJacobianPoisson M from rfl,
      ← hcomp₀]
  exact ⟨P.compDiffeomorph W.ψ, W.pullbackJacobianPoisson P.toFun P.contMDiff_toFun, Hs,
    W.conjDiffeomorph (leafwiseBumpDiffeomorph M),
    W.isUnimodularWithVolume_pullbackJacobianPoisson P.toFun P.contMDiff_toFun,
    (W.isGenericallyRankTwo_pullbackJacobianPoisson_iff P.toFun P.contMDiff_toFun).mpr
      (isGenericallyRankTwo_adaptedJacobianPoisson M),
    hcomp,
    W.fibration_comp_conjDiffeomorph (fibration_comp_leafwiseBumpDiffeomorph M),
    W.isPoissonMap_conjDiffeomorph P.toFun P.contMDiff_toFun
      (isPoissonMap_leafwiseBumpDiffeomorph M),
    W.mpullback_conjDiffeomorph (connectedComponent_leafwiseBumpDiffeomorph M)
      (mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm M),
    W.measurePreserving_conjDiffeomorph (connectedComponent_leafwiseBumpDiffeomorph M)
      (mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm M),
    W.isTuringComplete_conjDiffeomorph (isTuringComplete_leafwiseBumpDiffeomorph M),
    W.conjDiffeomorph_ne_id (isTuringComplete_leafwiseBumpDiffeomorph M)⟩

section Sanity

/-- Concrete autonomous planar rotation Hamiltonian (`r₀ = 3 / 4`, `r_in = 1 / 4`) used for Gate G5
single-Hamiltonian non-triviality verification on `Sphere4`. -/
noncomputable def s4RotationPlanarHamiltonian :
    CompactlySupportedPlanarHamiltonian (3 / 4) :=
  bumpedRotationHamiltonian ⟨by norm_num, by norm_num⟩ (r_in := 1 / 4) ⟨by norm_num, by norm_num⟩

/-- **Gate G5 Single-Hamiltonian Non-Triviality Witness on `Sphere4`**:
Lifting the concrete autonomous planar Hamiltonian `s4RotationPlanarHamiltonian` to `Sphere4`
produces a smooth Hamiltonian whose time-`1` Poisson–Hamiltonian diffeomorphism is strictly
non-trivial (`≠ Diffeomorph.refl (𝓡 4) Sphere4 ∞`). -/
-- tier: T1
theorem poissonHamiltonianTimeOneDiffeomorph_s4Rotation_ne_refl :
    poissonHamiltonianTimeOneDiffeomorph Sphere4
        (liftPlanarHamiltonianTo4Manifold Sphere4 s4RotationPlanarHamiltonian) ≠
      Diffeomorph.refl (𝓡 4) Sphere4 ∞ := by
  have hauto : s4RotationPlanarHamiltonian.IsAutonomous :=
    CMPP.bumpedRotationHamiltonian_isAutonomous ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩
  rw [poissonHamiltonianTimeOneDiffeomorph_liftPlanarHamiltonian_eq Sphere4
    s4RotationPlanarHamiltonian hauto]
  exact leafwiseBumpDiffeomorphOfIsotopy_ne_refl_of_diskTimeOneMap_ne_id Sphere4
    (bumpedRotationIsotopy_diskTimeOneMap_ne_id ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩)

/-- Corollary of `poissonHamiltonianTimeOneDiffeomorph_s4Rotation_ne_refl`: the lifted smooth
Hamiltonian `liftPlanarHamiltonianTo4Manifold Sphere4 s4RotationPlanarHamiltonian` is non-zero. -/
-- tier: T1
theorem liftPlanarHamiltonianTo4Manifold_s4Rotation_ne_zero :
    liftPlanarHamiltonianTo4Manifold Sphere4 s4RotationPlanarHamiltonian ≠ 0 := by
  intro h0
  apply poissonHamiltonianTimeOneDiffeomorph_s4Rotation_ne_refl
  apply Diffeomorph.ext
  intro x
  rw [h0, poissonHamiltonianTimeOneDiffeomorph_apply]
  have hX0 : (adaptedJacobianPoisson Sphere4).hamiltonianVectorField 0 = 0 :=
    SmoothBivector.hamiltonianVectorField_zero _
  have hX_smooth : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 4)) (𝓡 4).tangent 1
      (fun p : ℝ × Sphere4 ↦
        (⟨p.2, (adaptedJacobianPoisson Sphere4).hamiltonianVectorField 0 p.2⟩ :
          TangentBundle (𝓡 4) Sphere4)) :=
    (((adaptedJacobianPoisson Sphere4).contMDiff_hamiltonianVectorField 0).comp
      contMDiff_snd).of_le (by simp)
  exact TauCeti.timeDependentFlowOf_eq_self_of_forall_eq_zero hX_smooth
    (fun _ ↦ congrFun hX0 x) 0 1

end Sanity

end S4TuringPoisson
