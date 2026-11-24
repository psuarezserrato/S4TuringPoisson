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

public import S4TuringPoisson.Fibration.S4Fibration
public import TauCeti.Geometry.Symplectic.Manifold.Darboux
public import TauCeti.Geometry.Symplectic.Manifold.Sphere
public import TauCeti.Geometry.Symplectic.Manifold.Surface

/-!
# Wrinkled Fibrations on General Closed 4-Manifolds & Darboux Disk Lifting (M2.3)

This file implements Milestone M2.3 of `S4TuringPoisson`:

1. **Surface Symplectic Bridge (`isSymplectic_iff_ne_zero_surface`, `planeSymplecticForm`)**:
   - Connects `PositiveVolumeForm (𝓡 2) F` on any smooth 2-manifold `F` to
     `TauCeti.SmoothTwoForm.IsSymplectic` via
     `TauCeti.SmoothTwoForm.isSymplectic_iff_forall_ne_zero_of_finrank_eq_two`, and bridges
     `S2VolumeForm = TauCeti.sphereAreaForm`.
   - Constructs the canonical model symplectic form `planeSymplecticForm` on `EuclideanPlane`
     satisfying `planeSymplecticForm.constSmooth = planeAreaForm`.
2. **Regular-Disk vs. Genuine Wrinkled / Broken Lefschetz Fibration Typeclasses (`SC-R1`)**:
   - `AdmitsRegularDiskFibration`: packages a smooth 4-manifold `M` admitting a compatible
     `RegularDiskFibration` `f : M → Sphere2` with nonempty compact oriented smooth surface fiber
     `F` of arbitrary genus `g ≥ 0` and positive co-orientation over `baseRegion ⊂ Sphere2`
     (with unconditional `Sphere4` instance `instAdmitsRegularDiskFibrationSphere4` via
     `s4RegularDiskFibration`).
   - `AdmitsWrinkledOrBrokenLefschetzFibration` (`extends AdmitsRegularDiskFibration M`): adds the
     global `Gay–Kirby (2007)` / `Lekili (2009)` singularity classification requiring every
     critical point of `fibration.toFun` to satisfy `IsIndefiniteFoldAt ∨ IsWrinkledCuspAt ∨
     IsRealLefschetzAt` (inhabited on `Sphere4` by `s4ADKAdmits` in `ADKS4Fibration.lean`).
3. **Darboux Symplectic Disk Embedding (`SymplecticDiskChart`)**:
   - Uses `TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart_of_symplecticForm` to prove that
     **every** nonempty boundaryless smooth surface `(F, η)` carrying a symplectic 2-form `η`
     (of any genus `g ≥ 0`, without genus-reduction surgery) admits a smooth open disk embedding
     `embed : diskOpen → F` (`diskOpen = UnitDisk2`) that is a `C^∞` local diffeomorphism and pulls
     `η` back to `(radius ^ 2) • planeAreaForm|_{UnitDisk2}` (`0 < radius ^ 2`).
4. **Compactly Supported Area-Preserving Disk Isotopy Lift (`liftIsotopy`,
   `liftSliceDiffeomorph`)**:
   - Lifts any `[HasTuringCompleteAreaPreservingDiskIsotopy]` along `SymplecticDiskChart` by the
     identity outside the Darboux disk on any Hausdorff surface `(F, η)`, proving joint $C^\infty$
     smoothness on `ℝ × F`, smooth `Diffeomorph` slices starting at `id` at `t = 0`, exact pullback
     invariance `mpullback (liftSliceDiffeomorph t) _ η = η` (and `MeasurePreserving` for
     `V_F : PositiveVolumeForm (𝓡 2) F`), and `IsTuringComplete` at `t = 1`.
-/

@[expose] public section

open Function MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace S4TuringPoisson

/-! ## 1. Surface Symplectic Forms & `planeSymplecticForm` -/

section SurfaceSymplectic

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

/-- Canonical open unit disk `UnitDisk2` viewed as `Opens EuclideanPlane`. -/
noncomputable def diskOpen : Opens EuclideanPlane :=
  ⟨UnitDisk2, Metric.isOpen_ball⟩

@[simp]
theorem mem_diskOpen_iff (y : EuclideanPlane) : y ∈ diskOpen ↔ y ∈ UnitDisk2 :=
  Iff.rfl

/-- `S2VolumeForm` from `Interfaces.lean` agrees with `TauCeti.sphereAreaForm`. -/
theorem s2VolumeForm_eq_sphereAreaForm : S2VolumeForm = TauCeti.sphereAreaForm :=
  TauCeti.sphereAreaForm_eq_sphereVolumeForm.symm

/-- `S2VolumeForm` is a symplectic 2-form on `Sphere2`. -/
theorem isSymplectic_s2VolumeForm : TauCeti.SmoothTwoForm.IsSymplectic S2VolumeForm :=
  s2VolumeForm_eq_sphereAreaForm ▸ TauCeti.isSymplectic_sphereAreaForm

/-- On any smooth 2-manifold modeled on `𝓡 2`, a smooth 2-form `η` is symplectic if and only if it
vanishes nowhere. -/
theorem isSymplectic_iff_ne_zero_surface {F : Type*} [TopologicalSpace F]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F] [IsManifold (𝓡 2) ∞ F]
    (η : TauCeti.SmoothTwoForm (𝓡 2) F) :
    η.IsSymplectic ↔ ∀ x : F, η.1 x ≠ 0 :=
  TauCeti.SmoothTwoForm.isSymplectic_iff_forall_ne_zero_of_finrank_eq_two finrank_euclideanSpace_fin

/-- Every `PositiveVolumeForm (𝓡 2) F` on a smooth surface `F` is a symplectic 2-form. -/
theorem PositiveVolumeForm.isSymplectic_surface {F : Type*} [TopologicalSpace F]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F] [IsManifold (𝓡 2) ∞ F]
    [MeasurableSpace F] [BorelSpace F] (V : PositiveVolumeForm (𝓡 2) F) :
    TauCeti.SmoothTwoForm.IsSymplectic V.Ω :=
  (isSymplectic_iff_ne_zero_surface V.Ω).mpr V.Ω_ne_zero

/-- `planeAreaForm` (`dy₀ ∧ dy₁`) is a symplectic 2-form on `EuclideanPlane`. -/
theorem isSymplectic_planeAreaForm : TauCeti.SmoothTwoForm.IsSymplectic planeAreaForm :=
  (isSymplectic_iff_ne_zero_surface planeAreaForm).mpr planeAreaForm_ne_zero

/-- Canonical constant algebraic `TauCeti.SymplecticForm` on `EuclideanPlane` inducing
`planeAreaForm`. -/
noncomputable def planeSymplecticForm : TauCeti.SymplecticForm EuclideanPlane :=
  (isSymplectic_planeAreaForm.isNondegenerate.symplecticFormAt (0 : EuclideanPlane)).transport
    (NormedSpace.fromTangentSpace (0 : EuclideanPlane)).toLinearEquiv

/-- The constant smooth 2-form associated to `planeSymplecticForm` is `planeAreaForm`. -/
@[simp]
theorem planeSymplecticForm_constSmooth_eq_planeAreaForm :
    planeSymplecticForm.constSmooth = planeAreaForm := by
  refine TauCeti.SmoothBundleForm.ext_eval₂ fun x v w ↦ ?_
  rw [TauCeti.SymplecticForm.fromTangentSpace_constSmooth_apply, planeSymplecticForm,
    TauCeti.SymplecticForm.transport_apply,
    TauCeti.SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply,
    TauCeti.SmoothBundleForm.eval₂_apply, TauCeti.SmoothBundleForm.eval₂_apply,
    planeAreaForm_apply, planeAreaForm_apply]
  congr 1

/-- Homogeneous radial scaling `y ↦ r • y` on `EuclideanPlane`. -/
noncomputable def planeScale (r : ℝ) (y : EuclideanPlane) : EuclideanPlane :=
  r • y

@[simp]
theorem planeScale_apply (r : ℝ) (y : EuclideanPlane) : planeScale r y = r • y := rfl

theorem contDiff_planeScale (r : ℝ) : ContDiff ℝ ∞ (planeScale r) :=
  contDiff_const_smul r

/-- Radial scaling `y ↦ r • y` on `EuclideanPlane` pulls `planeAreaForm` back to
`(r ^ 2) • planeAreaForm`. -/
theorem mpullback_planeScale_planeAreaForm (r : ℝ) :
    TauCeti.SmoothForm.mpullback (planeScale r) (contDiff_planeScale r).contMDiff
        planeAreaForm =
      (r ^ 2) • planeAreaForm := by
  let b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  have hor : b.orientation = (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation := rfl
  let bT (y : EuclideanPlane) : Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) y) := b
  have hplane_bT (y : EuclideanPlane) : planeAreaForm.1 y ⇑(bT y) = 1 :=
    planeAreaForm_apply_basisFun y
  have hfderiv (y : EuclideanPlane) :
      fderiv ℝ (planeScale r) y = r • ContinuousLinearMap.id ℝ EuclideanPlane :=
    ((hasFDerivAt_id y).const_smul r).fderiv
  have hdet (y : EuclideanPlane) :
      LinearMap.det (fderiv ℝ (planeScale r) y).toLinearMap = r ^ 2 := by
    have hlin : (fderiv ℝ (planeScale r) y).toLinearMap =
        r • (LinearMap.id : EuclideanPlane →ₗ[ℝ] EuclideanPlane) := by
      rw [hfderiv y]
      rfl
    rw [hlin, LinearMap.det_smul, finrank_euclideanSpace_fin, LinearMap.det_id, mul_one]
  have hval (y : EuclideanPlane) :
      (TauCeti.SmoothForm.mpullback (planeScale r) (contDiff_planeScale r).contMDiff
          planeAreaForm).1 y ⇑(bT y) = r ^ 2 := by
    rw [TauCeti.SmoothForm.mpullback_apply, planeAreaForm_apply]
    have hmf (v : TangentSpace (𝓡 2) y) :
        (mfderiv (𝓡 2) (𝓡 2) (planeScale r) y v : EuclideanPlane) =
          fderiv ℝ (planeScale r) y v := by
      rw [mfderiv_eq_fderiv]
      rfl
    simp_rw [hmf]
    change b.orientation.volumeForm (⇑(fderiv ℝ (planeScale r) y).toLinearMap ∘ ⇑b) = r ^ 2
    rw [b.orientation.volumeForm_robust (EuclideanSpace.basisFun (Fin 2) ℝ) hor,
      b.det_comp, b.det_self, mul_one, hdet y]
  refine Subtype.ext (funext fun y ↦ ?_)
  ext v
  rw [ContinuousAlternatingMap.apply_eq_det_mul _ (bT y) v, Submodule.coe_smul, Pi.smul_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.apply_eq_det_mul _ (bT y) v,
    hval y, hplane_bT y, mul_one, smul_eq_mul, mul_comm]

end SurfaceSymplectic

/-! ## 2. `AdmitsRegularDiskFibration` & `AdmitsWrinkledOrBrokenLefschetzFibration` (`SC-R1`) -/

section FibrationClass

/-- Typeclass packaging a smooth 4-manifold `M` equipped with a positive volume 4-form `Ω_M` and a
smooth map `f : M → Sphere2` trivialized over one nonempty regular open base disk with nonempty
compact oriented smooth surface regular fiber `Fiber` (of arbitrary genus `g ≥ 0`) and strictly
positively co-oriented smooth trivialization over `fibration.baseRegion` (`SC-R1`).

Unlike `AdmitsWrinkledOrBrokenLefschetzFibration`, this base class imposes zero normal-form
restrictions on `criticalPoints (𝓡 4) (𝓡 2) fibration.toFun`; it powers the leafwise volume,
isotopy lift, and Poisson–Hamiltonian engine uniformly across both global wrinkled/ADK fibrations
and local coordinate-ball constructions (`ClosedManifoldLocal.lean`). -/
class AdmitsRegularDiskFibration (M : Type*)
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M]
    [MeasurableSpace M] [BorelSpace M] where
  /-- Ambient positive volume 4-form `Ω_M` on `M`. -/
  ambientVolume : PositiveVolumeForm (𝓡 4) M
  /-- Regular surface fiber `F` over `fibration.baseRegion`. -/
  Fiber : Type
  /-- Topology on `Fiber`. -/
  instTopologicalSpaceFiber : TopologicalSpace Fiber
  /-- Smooth 2D chart atlas on `Fiber`. -/
  instChartedSpaceFiber : @ChartedSpace (EuclideanSpace ℝ (Fin 2)) _ Fiber instTopologicalSpaceFiber
  /-- Smooth manifold structure on `Fiber`. -/
  instIsManifoldFiber :
    @IsManifold ℝ _ (EuclideanSpace ℝ (Fin 2)) _ _ (EuclideanSpace ℝ (Fin 2)) _ (𝓡 2) ∞ Fiber
      instTopologicalSpaceFiber instChartedSpaceFiber
  /-- Hausdorff separation on `Fiber`. -/
  instT2SpaceFiber : @T2Space Fiber instTopologicalSpaceFiber
  /-- Compactness of the closed regular surface fiber `Fiber`. -/
  instCompactSpaceFiber : @CompactSpace Fiber instTopologicalSpaceFiber
  /-- Non-emptiness of `Fiber`. -/
  instNonemptyFiber : Nonempty Fiber
  /-- Measurable space structure on `Fiber`. -/
  instMeasurableSpaceFiber : MeasurableSpace Fiber
  /-- Borel compatibility on `Fiber`. -/
  instBorelSpaceFiber : @BorelSpace Fiber instTopologicalSpaceFiber instMeasurableSpaceFiber
  /-- Underlying `RegularDiskFibration` `M → Sphere2` with regular fiber `Fiber`. -/
  fibration :
    letI := instTopologicalSpaceFiber
    letI := instChartedSpaceFiber
    letI := instIsManifoldFiber
    letI := instCompactSpaceFiber
    letI := instNonemptyFiber
    RegularDiskFibration (𝓡 4) M (𝓡 2) Sphere2 Fiber
  /-- Positive area / symplectic 2-form `ω_F` on `Fiber`. -/
  fiberVolume :
    letI := instTopologicalSpaceFiber
    letI := instChartedSpaceFiber
    letI := instIsManifoldFiber
    letI := instMeasurableSpaceFiber
    letI := instBorelSpaceFiber
    PositiveVolumeForm (𝓡 2) Fiber
  /-- Strict positive co-orientation of `fibration.trivialization` with `fiberVolume.Ω`,
  `S2VolumeForm`, and `ambientVolume.Ω` over `fibration.preimageOpen`. -/
  trivialization_pos_cooriented :
    letI := instTopologicalSpaceFiber
    letI := instChartedSpaceFiber
    letI := instIsManifoldFiber
    letI := instCompactSpaceFiber
    letI := instNonemptyFiber
    letI := instMeasurableSpaceFiber
    letI := instBorelSpaceFiber
    ∀ u : fibration.preimageOpen, ∃ c : ℝ, 0 < c ∧
      (TauCeti.SmoothForm.mpullback fibration.trivialization fibration.trivialization.contMDiff
          (TauCeti.SmoothForm.wedge
            (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd fiberVolume.Ω)
            (TauCeti.SmoothForm.mpullback (Subtype.val ∘ Prod.fst)
              (contMDiff_subtype_val.comp contMDiff_fst) S2VolumeForm))).1 u =
        c • (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val ambientVolume.Ω).1 u

/-- **Unconditional `AdmitsRegularDiskFibration` Instance for $S^4$**: `Sphere4` admits the
explicit positively co-oriented regular-disk fibration `s4RegularDiskFibration : Sphere4 → Sphere2`
with regular fiber `Sphere2` constructed in `S4Fibration.lean` (Milestone M2.2). -/
noncomputable instance instAdmitsRegularDiskFibrationSphere4 :
    AdmitsRegularDiskFibration Sphere4 where
  ambientVolume := S4PositiveVolumeForm
  Fiber := Sphere2
  instTopologicalSpaceFiber := inferInstance
  instChartedSpaceFiber := inferInstance
  instIsManifoldFiber := inferInstance
  instT2SpaceFiber := inferInstance
  instCompactSpaceFiber := inferInstance
  instNonemptyFiber := ⟨s2NorthPole⟩
  instMeasurableSpaceFiber := inferInstance
  instBorelSpaceFiber := inferInstance
  fibration := s4RegularDiskFibration
  fiberVolume := S2PositiveVolumeForm
  trivialization_pos_cooriented := s4Trivialization_pos_cooriented

/-- Typeclass packaging the genuine `Gay–Kirby (2007)` / `Lekili (2009)` existence of a positively
co-oriented wrinkled or broken Lefschetz fibration `f : M → Sphere2` on a smooth 4-manifold `M`
(`SC-R1`), extending `AdmitsRegularDiskFibration M` with the global singularity classification
requiring every critical point of `fibration.toFun` to be locally modeled on an indefinite
quadratic fold (`IsIndefiniteFoldAt`), a wrinkled cusp (`IsWrinkledCuspAt`), or an isolated real
Lefschetz point (`IsRealLefschetzAt`).

On `Sphere4`, this stronger class is inhabited unconditionally by `s4ADKAdmits`
(`ADKS4Fibration.lean`, kept as a `def` rather than a global `instance` to avoid a typeclass
diamond on `AdmitsRegularDiskFibration Sphere4` with `instAdmitsRegularDiskFibrationSphere4`). -/
class AdmitsWrinkledOrBrokenLefschetzFibration (M : Type*)
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    extends AdmitsRegularDiskFibration M where
  /-- Every critical point of `fibration.toFun` is an indefinite quadratic fold, a wrinkled cusp,
  or an isolated real Lefschetz point (`GK07`, `Lek09`, `ADK05`). -/
  singularities_wrinkled_or_lefschetz :
    letI := instTopologicalSpaceFiber
    letI := instChartedSpaceFiber
    letI := instIsManifoldFiber
    letI := instT2SpaceFiber
    letI := instCompactSpaceFiber
    letI := instNonemptyFiber
    ∀ p ∈ criticalPoints (𝓡 4) (𝓡 2) fibration.toFun,
      IsIndefiniteFoldAt (𝓡 4) (𝓡 2) fibration.toFun p ∨
        IsWrinkledCuspAt (𝓡 4) (𝓡 2) fibration.toFun p ∨
        IsRealLefschetzAt (𝓡 4) (𝓡 2) fibration.toFun p

/-- Construct `AdmitsWrinkledOrBrokenLefschetzFibration M` from a positively co-oriented
`BrokenLefschetzFibration` (`Auroux–Donaldson–Katzarkov` / `Baykur` / `Gay–Kirby`). -/
@[instance_reducible]
noncomputable def AdmitsWrinkledOrBrokenLefschetzFibration.ofBrokenLefschetz
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    (V_M : PositiveVolumeForm (𝓡 4) M)
    (F : Type) [TopologicalSpace F] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F]
    [IsManifold (𝓡 2) ∞ F] [T2Space F] [CompactSpace F] [Nonempty F]
    [MeasurableSpace F] [BorelSpace F]
    (B_fib : BrokenLefschetzFibration (𝓡 4) M (𝓡 2) Sphere2 F)
    (V_F : PositiveVolumeForm (𝓡 2) F)
    (hpos : ∀ u : B_fib.toRegularDiskFibration.preimageOpen, ∃ c : ℝ, 0 < c ∧
      (TauCeti.SmoothForm.mpullback B_fib.trivialization B_fib.trivialization.contMDiff
          (TauCeti.SmoothForm.wedge
            (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd V_F.Ω)
            (TauCeti.SmoothForm.mpullback (Subtype.val ∘ Prod.fst)
              (contMDiff_subtype_val.comp contMDiff_fst) S2VolumeForm))).1 u =
        c • (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val V_M.Ω).1 u) :
    AdmitsWrinkledOrBrokenLefschetzFibration M where
  ambientVolume := V_M
  Fiber := F
  instTopologicalSpaceFiber := inferInstance
  instChartedSpaceFiber := inferInstance
  instIsManifoldFiber := inferInstance
  instT2SpaceFiber := inferInstance
  instCompactSpaceFiber := inferInstance
  instNonemptyFiber := inferInstance
  instMeasurableSpaceFiber := inferInstance
  instBorelSpaceFiber := inferInstance
  fibration := B_fib.toRegularDiskFibration
  fiberVolume := V_F
  trivialization_pos_cooriented := hpos
  singularities_wrinkled_or_lefschetz p hp :=
    (B_fib.singularities_broken_lefschetz p hp).elim (fun h ↦ Or.inr (Or.inr h)) Or.inl

/-- For any `[A : AdmitsWrinkledOrBrokenLefschetzFibration M]`, the regular-point locus of
`A.fibration.toFun` is dense in `M`. -/
-- tier: T1
theorem AdmitsWrinkledOrBrokenLefschetzFibration.dense_regularPoints
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [A : AdmitsWrinkledOrBrokenLefschetzFibration M] :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    Dense {x : M | x ∉ criticalPoints (𝓡 4) (𝓡 2) A.fibration.toFun} := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  exact dense_regularPoints_of_wrinkled_or_lefschetz A.fibration.contMDiff_toFun
    A.singularities_wrinkled_or_lefschetz

end FibrationClass

/-! ## 3. Darboux Symplectic Disk Embedding on Arbitrary Surfaces (`SymplecticDiskChart`) -/

section DarbouxDisk

/-- A centered Darboux symplectic disk chart on a smooth 2-manifold `(F, η)`: packages a smooth
partial diffeomorphism `rawChart : F → EuclideanPlane` and a positive scaling radius `radius > 0`
with `Metric.ball 0 radius ⊆ rawChart.target`, inducing a smooth open disk embedding
`embed : diskOpen → F` (`y ↦ rawChart.symm (radius • y.1)`) that pulls `η` back to
`(radius ^ 2) • planeAreaForm|_{UnitDisk2}`. -/
structure SymplecticDiskChart (F : Type*) [TopologicalSpace F]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F] [IsManifold (𝓡 2) ∞ F]
    (η : TauCeti.SmoothTwoForm (𝓡 2) F) where
  /-- Underlying Darboux `PartialDiffeomorph` from `F` to `EuclideanPlane`. -/
  rawChart : PartialDiffeomorph (𝓡 2) (𝓡 2) F EuclideanPlane ∞
  /-- Positive Euclidean ball radius inside `rawChart.target`. -/
  radius : ℝ
  /-- Strict positivity `0 < radius`. -/
  radius_pos : 0 < radius
  /-- Inclusion `Metric.ball 0 radius ⊆ rawChart.target`. -/
  ball_subset_target : Metric.ball (0 : EuclideanPlane) radius ⊆ rawChart.target
  /-- Pointwise Darboux pullback identity on `rawChart.source`. -/
  eval₂_eq_planeSymplecticForm :
    ∀ x ∈ rawChart.source, ∀ v w : TangentSpace (𝓡 2) x,
      η.eval₂ x v w =
        planeSymplecticForm (mvfderiv (𝓡 2) rawChart x v) (mvfderiv (𝓡 2) rawChart x w)

namespace SymplecticDiskChart

variable {F : Type*} [TopologicalSpace F] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F]
  [IsManifold (𝓡 2) ∞ F] {η : TauCeti.SmoothTwoForm (𝓡 2) F}

/-- Positive area-scaling constant `c = radius ^ 2 > 0` of a `SymplecticDiskChart`. -/
noncomputable def areaScale (C : SymplecticDiskChart F η) : ℝ :=
  C.radius ^ 2

theorem areaScale_pos (C : SymplecticDiskChart F η) : 0 < C.areaScale :=
  sq_pos_of_pos C.radius_pos

theorem scale_mem_ball (C : SymplecticDiskChart F η) {y : EuclideanPlane} (hy : y ∈ UnitDisk2) :
    C.radius • y ∈ Metric.ball (0 : EuclideanPlane) C.radius := by
  have hy_norm : ‖y‖ < 1 := by simpa only [UnitDisk2, Metric.mem_ball, dist_zero_right] using hy
  rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg C.radius_pos.le]
  exact mul_lt_of_lt_one_right C.radius_pos hy_norm

theorem inv_scale_mem_unitDisk2 (C : SymplecticDiskChart F η) {w : EuclideanPlane}
    (hw : w ∈ Metric.ball (0 : EuclideanPlane) C.radius) :
    C.radius⁻¹ • w ∈ UnitDisk2 := by
  have hw_norm : ‖w‖ < C.radius := by simpa only [Metric.mem_ball, dist_zero_right] using hw
  rw [UnitDisk2, Metric.mem_ball, dist_zero_right, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr C.radius_pos.le)]
  exact (inv_mul_lt_iff₀ C.radius_pos).mpr (by linarith)

/-- Open Darboux disk image `rawChart.source ∩ rawChart ⁻¹' Metric.ball 0 radius` inside `F`. -/
noncomputable def sourceOpen (C : SymplecticDiskChart F η) : Opens F :=
  ⟨C.rawChart.source ∩ C.rawChart ⁻¹' Metric.ball (0 : EuclideanPlane) C.radius, by
    rw [← C.rawChart.toOpenPartialHomeomorph_source]
    exact C.rawChart.toOpenPartialHomeomorph.isOpen_inter_preimage Metric.isOpen_ball⟩

/-- Smooth diffeomorphism `diskOpen ≃ₘ⟮𝓡 2, 𝓡 2⟯ C.sourceOpen` sending `y ∈ UnitDisk2` to
`C.rawChart.toPartialEquiv.symm (C.radius • y)`. -/
noncomputable def diskEquivSource (C : SymplecticDiskChart F η) :
    diskOpen ≃ₘ⟮𝓡 2, 𝓡 2⟯ C.sourceOpen where
  toFun y :=
    ⟨C.rawChart.toPartialEquiv.symm (C.radius • y.1),
      ⟨C.rawChart.map_target (C.ball_subset_target (C.scale_mem_ball y.2)), by
        rw [Set.mem_preimage,
          C.rawChart.right_inv (C.ball_subset_target (C.scale_mem_ball y.2))]
        exact C.scale_mem_ball y.2⟩⟩
  invFun z := ⟨C.radius⁻¹ • C.rawChart z.1, C.inv_scale_mem_unitDisk2 z.2.2⟩
  left_inv y := by
    apply Subtype.ext
    dsimp only
    rw [C.rawChart.right_inv (C.ball_subset_target (C.scale_mem_ball y.2)),
      inv_smul_smul₀ C.radius_pos.ne']
  right_inv z := by
    apply Subtype.ext
    dsimp only
    rw [smul_inv_smul₀ C.radius_pos.ne', C.rawChart.left_inv z.2.1]
  contMDiff_toFun := by
    refine (TauCeti.ContMDiff.subtypeVal_comp_iff C.sourceOpen
      (fun y : diskOpen ↦ ⟨C.rawChart.toPartialEquiv.symm (C.radius • y.1),
        ⟨C.rawChart.map_target (C.ball_subset_target (C.scale_mem_ball y.2)), by
          rw [Set.mem_preimage,
            C.rawChart.right_inv (C.ball_subset_target (C.scale_mem_ball y.2))]
          exact C.scale_mem_ball y.2⟩⟩)).mp fun y ↦ ?_
    have hmem : C.radius • y.1 ∈ C.rawChart.target :=
      C.ball_subset_target (C.scale_mem_ball y.2)
    have hsymm : ContMDiffAt (𝓡 2) (𝓡 2) ∞ C.rawChart.toPartialEquiv.symm (C.radius • y.1) :=
      C.rawChart.contMDiffOn_invFun.contMDiffAt (C.rawChart.open_target.mem_nhds hmem)
    have hsc : ContMDiff (𝓡 2) (𝓡 2) ∞ (fun u : diskOpen ↦ C.radius • u.1) :=
      (contDiff_planeScale C.radius).contMDiff.comp contMDiff_subtype_val
    change ContMDiffAt (𝓡 2) (𝓡 2) ∞
      (C.rawChart.toPartialEquiv.symm ∘ fun u : diskOpen ↦ C.radius • u.1) y
    exact ContMDiffAt.comp y hsymm (hsc y)
  contMDiff_invFun := by
    refine (TauCeti.ContMDiff.subtypeVal_comp_iff diskOpen
      (fun z : C.sourceOpen ↦ ⟨C.radius⁻¹ • C.rawChart z.1,
        C.inv_scale_mem_unitDisk2 z.2.2⟩)).mp fun z ↦ ?_
    have hch : ContMDiffAt (𝓡 2) (𝓡 2) ∞ (fun u : C.sourceOpen ↦ C.rawChart u.1) z :=
      (C.rawChart.contMDiffOn_toFun.contMDiffAt
        (C.rawChart.open_source.mem_nhds z.2.1)).comp z (contMDiff_subtype_val z)
    exact (contDiff_planeScale C.radius⁻¹).contMDiff.contMDiffAt.comp z hch

/-- Smooth open disk embedding `embed : diskOpen → F` sending `y ∈ UnitDisk2` to
`C.rawChart.toPartialEquiv.symm (C.radius • y)`. -/
noncomputable def embed (C : SymplecticDiskChart F η) (y : diskOpen) : F :=
  (C.diskEquivSource y).1

@[simp]
theorem embed_apply (C : SymplecticDiskChart F η) (y : diskOpen) :
    C.embed y = C.rawChart.toPartialEquiv.symm (C.radius • y.1) :=
  rfl

theorem embed_eq_comp (C : SymplecticDiskChart F η) :
    C.embed = (Subtype.val : C.sourceOpen → F) ∘ ⇑C.diskEquivSource :=
  rfl

theorem embed_mem_sourceOpen (C : SymplecticDiskChart F η) (y : diskOpen) :
    C.embed y ∈ C.sourceOpen.1 :=
  (C.diskEquivSource y).2

@[simp]
theorem rawChart_embed (C : SymplecticDiskChart F η) (y : diskOpen) :
    C.rawChart (C.embed y) = C.radius • y.1 :=
  C.rawChart.right_inv (C.ball_subset_target (C.scale_mem_ball y.2))

theorem range_embed (C : SymplecticDiskChart F η) :
    Set.range C.embed = C.sourceOpen.1 := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact C.embed_mem_sourceOpen y
  · intro hz
    exact ⟨C.diskEquivSource.symm ⟨z, hz⟩,
      congrArg Subtype.val (C.diskEquivSource.apply_symm_apply ⟨z, hz⟩)⟩

/-- `C.embed` is $C^\infty$ smooth. -/
theorem contMDiff_embed (C : SymplecticDiskChart F η) :
    ContMDiff (𝓡 2) (𝓡 2) ∞ C.embed :=
  contMDiff_subtype_val.comp C.diskEquivSource.contMDiff

/-- `C.embed` is a topological open embedding `diskOpen → F`. -/
theorem isOpenEmbedding_embed (C : SymplecticDiskChart F η) :
    Topology.IsOpenEmbedding C.embed :=
  C.sourceOpen.2.isOpenEmbedding_subtypeVal.comp C.diskEquivSource.toHomeomorph.isOpenEmbedding

/-- `C.embed` is injective. -/
theorem injective_embed (C : SymplecticDiskChart F η) : Function.Injective C.embed :=
  C.isOpenEmbedding_embed.injective

/-- `C.embed` is a $C^\infty$ local diffeomorphism `diskOpen → F`. -/
theorem isLocalDiffeomorph_embed (C : SymplecticDiskChart F η) :
    IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ C.embed := fun y ↦
  (C.diskEquivSource.isLocalDiffeomorph y).comp
    (hg := TauCeti.isLocalDiffeomorph_subtype_val (C.diskEquivSource y))

private theorem mpullback_congr_fun_two {E₁ H₁ M₁ E₂ H₂ M₂ : Type*}
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

/-- **Darboux Disk Pullback Identity**: `C.embed : diskOpen → F` pulls the surface symplectic form
`η` back to `C.areaScale • planeAreaForm|_{UnitDisk2}` (`C.areaScale = C.radius ^ 2 > 0`). -/
theorem mpullback_embed_eq (C : SymplecticDiskChart F η) :
    TauCeti.SmoothForm.mpullback C.embed C.contMDiff_embed η =
      C.areaScale •
        TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val planeAreaForm := by
  let U₀ : Opens F := ⟨C.rawChart.source, C.rawChart.open_source⟩
  have hpull_U₀ :
      TauCeti.SmoothForm.mpullback (fun x : U₀ ↦ C.rawChart x.1)
          (C.rawChart.contMDiffOn_toFun.comp_contMDiff contMDiff_subtype_val fun x ↦ x.2)
          planeAreaForm =
        TauCeti.SmoothForm.mpullback (Subtype.val : U₀ → F) contMDiff_subtype_val η := by
    rw [← planeSymplecticForm_constSmooth_eq_planeAreaForm]
    exact (TauCeti.SmoothTwoForm.mpullback_constSmooth_eq_mpullback_subtype_val_iff
      η planeSymplecticForm C.rawChart).mpr C.eval₂_eq_planeSymplecticForm
  let j : diskOpen → U₀ :=
    fun y ↦ ⟨C.embed y, (C.embed_mem_sourceOpen y).1⟩
  have hj : ContMDiff (𝓡 2) (𝓡 2) ∞ j :=
    (TauCeti.ContMDiff.subtypeVal_comp_iff U₀ _).mp C.contMDiff_embed
  have hembed_factor : C.embed = (Subtype.val : U₀ → F) ∘ j := rfl
  have hchart_j :
      ((fun x : U₀ ↦ C.rawChart x.1) ∘ j) = planeScale C.radius ∘ (Subtype.val : diskOpen → _) :=
    funext fun y ↦ C.rawChart_embed y
  calc
    TauCeti.SmoothForm.mpullback C.embed C.contMDiff_embed η
      = TauCeti.SmoothForm.mpullback j hj
          (TauCeti.SmoothForm.mpullback (Subtype.val : U₀ → F) contMDiff_subtype_val η) := by
        rw [TauCeti.SmoothForm.mpullback_mpullback]
        exact mpullback_congr_fun_two _ _ hembed_factor η
    _ = TauCeti.SmoothForm.mpullback j hj
          (TauCeti.SmoothForm.mpullback (fun x : U₀ ↦ C.rawChart x.1)
            (C.rawChart.contMDiffOn_toFun.comp_contMDiff contMDiff_subtype_val fun x ↦ x.2)
            planeAreaForm) := by
        rw [hpull_U₀]
    _ = TauCeti.SmoothForm.mpullback (planeScale C.radius ∘ (Subtype.val : diskOpen → _))
          ((contDiff_planeScale C.radius).contMDiff.comp contMDiff_subtype_val) planeAreaForm := by
        rw [TauCeti.SmoothForm.mpullback_mpullback]
        exact mpullback_congr_fun_two _ _ hchart_j planeAreaForm
    _ = TauCeti.SmoothForm.mpullback (Subtype.val : diskOpen → _) contMDiff_subtype_val
          (TauCeti.SmoothForm.mpullback (planeScale C.radius)
            (contDiff_planeScale C.radius).contMDiff planeAreaForm) := by
        rw [← TauCeti.SmoothForm.mpullback_mpullback (Subtype.val : diskOpen → EuclideanPlane)
          (planeScale C.radius) contMDiff_subtype_val (contDiff_planeScale C.radius).contMDiff
          planeAreaForm]
    _ = C.areaScale •
          TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val planeAreaForm := by
        rw [mpullback_planeScale_planeAreaForm C.radius, map_smul, areaScale]

end SymplecticDiskChart

/-- **Existence of a Symplectic Disk Chart on Every Nonempty Symplectic Surface**:
Every nonempty smooth 2-manifold `(F, η)` modeled on `𝓡 2` (hence boundaryless, of any genus
`g ≥ 0`) carrying a symplectic 2-form `η` admits a `SymplecticDiskChart F η`. -/
theorem exists_symplecticDiskChart (F : Type*) [TopologicalSpace F]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F] [IsManifold (𝓡 2) ∞ F] [Nonempty F]
    {η : TauCeti.SmoothTwoForm (𝓡 2) F} (hη : η.IsSymplectic) :
    Nonempty (SymplecticDiskChart F η) := by
  let x₀ : F := Classical.arbitrary F
  obtain ⟨chart₀, hx₀, h0, hpull⟩ :=
    hη.exists_darbouxChart_of_symplecticForm planeSymplecticForm x₀
  have h0_tgt : (0 : EuclideanPlane) ∈ chart₀.target := h0 ▸ chart₀.map_source hx₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp chart₀.open_target 0 h0_tgt
  exact ⟨{
    rawChart := chart₀
    radius := ε
    radius_pos := hε
    ball_subset_target := hball
    eval₂_eq_planeSymplecticForm := hpull
  }⟩

/-- Canonical `SymplecticDiskChart` chosen on any nonempty smooth surface `(F, η)` with symplectic
`η`. -/
noncomputable def Classical.symplecticDiskChart (F : Type*) [TopologicalSpace F]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F] [IsManifold (𝓡 2) ∞ F] [Nonempty F]
    {η : TauCeti.SmoothTwoForm (𝓡 2) F} (hη : η.IsSymplectic) :
    SymplecticDiskChart F η :=
  Classical.choice (exists_symplecticDiskChart F hη)

/-- Canonical `SymplecticDiskChart F V.Ω` associated to any `PositiveVolumeForm (𝓡 2) F` on a
nonempty smooth surface `F` (of any genus `g ≥ 0`). -/
noncomputable def PositiveVolumeForm.symplecticDiskChart {F : Type*} [TopologicalSpace F]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F] [IsManifold (𝓡 2) ∞ F] [Nonempty F]
    [MeasurableSpace F] [BorelSpace F] (V : PositiveVolumeForm (𝓡 2) F) :
    SymplecticDiskChart F V.Ω :=
  Classical.symplecticDiskChart F V.isSymplectic_surface

/-- Headline existence theorem for Milestone M2.3: every nonempty smooth surface `(F, V)` carrying a
`PositiveVolumeForm` admits a $C^\infty$ open disk embedding `ι : diskOpen → F` that is a local
diffeomorphism and pulls `V.Ω` back to `c • planeAreaForm|_{UnitDisk2}` with `c > 0`. -/
theorem exists_symplectic_disk_embedding_of_positiveVolumeForm
    (F : Type*) [TopologicalSpace F] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F]
    [IsManifold (𝓡 2) ∞ F] [Nonempty F] [MeasurableSpace F] [BorelSpace F]
    (V : PositiveVolumeForm (𝓡 2) F) :
    ∃ (ι : diskOpen → F) (hι : ContMDiff (𝓡 2) (𝓡 2) ∞ ι) (c : ℝ),
      0 < c ∧
      Topology.IsOpenEmbedding ι ∧
      IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ ι ∧
      TauCeti.SmoothForm.mpullback ι hι V.Ω =
        c • TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val planeAreaForm :=
  let C := V.symplecticDiskChart
  ⟨C.embed, C.contMDiff_embed, C.areaScale, C.areaScale_pos,
    C.isOpenEmbedding_embed, C.isLocalDiffeomorph_embed, C.mpullback_embed_eq⟩

end DarbouxDisk

/-! ## 4. Lifting Compactly Supported Area-Preserving Disk Isotopies to Arbitrary Surfaces -/

section DiskIsotopyLift

namespace SymplecticDiskChart

variable {F : Type*} [TopologicalSpace F] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F]
  [IsManifold (𝓡 2) ∞ F] {η : TauCeti.SmoothTwoForm (𝓡 2) F}

/-- Lift a parameter-dependent planar map `f : ℝ × EuclideanPlane → EuclideanPlane` through a
`SymplecticDiskChart` by conjugating with `w ↦ C.rawChart.symm (C.radius • w)` on `C.sourceOpen`
and extending by the identity outside `C.sourceOpen`. -/
noncomputable def liftThroughChart (C : SymplecticDiskChart F η)
    (f : ℝ × EuclideanPlane → EuclideanPlane) (q : ℝ × F) : F :=
  letI := Classical.dec (q.2 ∈ C.sourceOpen.1)
  if q.2 ∈ C.sourceOpen.1 then
    C.rawChart.toPartialEquiv.symm (C.radius • f (q.1, C.radius⁻¹ • C.rawChart q.2))
  else
    q.2

theorem liftThroughChart_of_mem (C : SymplecticDiskChart F η)
    (f : ℝ × EuclideanPlane → EuclideanPlane) (t : ℝ) {z : F} (hz : z ∈ C.sourceOpen.1) :
    C.liftThroughChart f (t, z) =
      C.rawChart.toPartialEquiv.symm (C.radius • f (t, C.radius⁻¹ • C.rawChart z)) := by
  simp only [liftThroughChart, hz, ↓reduceIte]

theorem liftThroughChart_of_notMem (C : SymplecticDiskChart F η)
    (f : ℝ × EuclideanPlane → EuclideanPlane) (t : ℝ) {z : F} (hz : z ∉ C.sourceOpen.1) :
    C.liftThroughChart f (t, z) = z := by
  simp only [liftThroughChart, hz, ↓reduceIte]

/-- On `C.embed y`, `liftThroughChart` intertwines `C.embed` with `f` whenever `f` preserves
`UnitDisk2`. -/
theorem liftThroughChart_embed (C : SymplecticDiskChart F η)
    {f : ℝ × EuclideanPlane → EuclideanPlane}
    (hf_mem : ∀ (t : ℝ) {w : EuclideanPlane}, w ∈ UnitDisk2 → f (t, w) ∈ UnitDisk2)
    (t : ℝ) (y : diskOpen) :
    C.liftThroughChart f (t, C.embed y) = C.embed ⟨f (t, y.1), hf_mem t y.2⟩ := by
  rw [C.liftThroughChart_of_mem f t (C.embed_mem_sourceOpen y), C.rawChart_embed y,
    inv_smul_smul₀ C.radius_pos.ne', C.embed_apply]

theorem liftThroughChart_mem_sourceOpen_iff (C : SymplecticDiskChart F η)
    {f : ℝ × EuclideanPlane → EuclideanPlane}
    (hf_mem : ∀ (t : ℝ) {w : EuclideanPlane}, w ∈ UnitDisk2 → f (t, w) ∈ UnitDisk2)
    (t : ℝ) (z : F) :
    C.liftThroughChart f (t, z) ∈ C.sourceOpen.1 ↔ z ∈ C.sourceOpen.1 := by
  by_cases hz : z ∈ C.sourceOpen.1
  · obtain ⟨y, rfl⟩ := C.range_embed.symm.subset hz
    rw [C.liftThroughChart_embed hf_mem t y]
    exact ⟨fun _ ↦ C.embed_mem_sourceOpen y, fun _ ↦ C.embed_mem_sourceOpen _⟩
  · rw [C.liftThroughChart_of_notMem f t hz]

theorem liftThroughChart_comp_of_inv (C : SymplecticDiskChart F η)
    {f g : ℝ × EuclideanPlane → EuclideanPlane}
    (hf_mem : ∀ (t : ℝ) {w : EuclideanPlane}, w ∈ UnitDisk2 → f (t, w) ∈ UnitDisk2)
    (hgf : ∀ (t : ℝ) (w : EuclideanPlane), g (t, f (t, w)) = w)
    (t : ℝ) (z : F) :
    C.liftThroughChart g (t, C.liftThroughChart f (t, z)) = z := by
  by_cases hz : z ∈ C.sourceOpen.1
  · obtain ⟨y, rfl⟩ := C.range_embed.symm.subset hz
    rw [C.liftThroughChart_embed hf_mem t y, C.liftThroughChart_of_mem g t
      (C.embed_mem_sourceOpen _), C.rawChart_embed, inv_smul_smul₀ C.radius_pos.ne',
      hgf t y.1, C.embed_apply]
  · have hz' : C.liftThroughChart f (t, z) ∉ C.sourceOpen.1 := by
      rwa [C.liftThroughChart_mem_sourceOpen_iff hf_mem t z]
    rw [C.liftThroughChart_of_notMem g t hz', C.liftThroughChart_of_notMem f t hz]

/-- Compact image `C.embed '' (closedBall 0 r₀)` inside `C.sourceOpen.1` for `r₀ < 1`. -/
noncomputable def supportSet (C : SymplecticDiskChart F η) {r₀ : ℝ} (hr₀ : r₀ < 1) : Set F :=
  (fun x : Metric.closedBall (0 : EuclideanPlane) r₀ ↦
      C.embed ⟨x.1, Metric.closedBall_subset_ball hr₀ x.2⟩) '' Set.univ

theorem supportSet_subset_sourceOpen (C : SymplecticDiskChart F η) {r₀ : ℝ} (hr₀ : r₀ < 1) :
    C.supportSet hr₀ ⊆ C.sourceOpen.1 := by
  rintro _ ⟨x, -, rfl⟩
  exact C.embed_mem_sourceOpen _

theorem isCompact_supportSet (C : SymplecticDiskChart F η) {r₀ : ℝ} (hr₀ : r₀ < 1) :
    IsCompact (C.supportSet hr₀) := by
  let K := Metric.closedBall (0 : EuclideanPlane) r₀
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 r₀)
  have hcont_incl : Continuous (fun x : K ↦ (⟨x.1, Metric.closedBall_subset_ball hr₀ x.2⟩ :
      diskOpen)) :=
    continuous_subtype_val.subtype_mk _
  exact isCompact_univ.image (C.contMDiff_embed.continuous.comp hcont_incl)

theorem liftThroughChart_eq_self_of_notMem_supportSet (C : SymplecticDiskChart F η)
    {f : ℝ × EuclideanPlane → EuclideanPlane} {r₀ : ℝ} (hr₀ : r₀ < 1)
    (hf_supp : ∀ (t : ℝ) (w : EuclideanPlane),
      w ∉ Metric.ball (0 : EuclideanPlane) r₀ → f (t, w) = w)
    (t : ℝ) {z : F} (hz : z ∉ C.supportSet hr₀) :
    C.liftThroughChart f (t, z) = z := by
  by_cases hsrc : z ∈ C.sourceOpen.1
  · obtain ⟨y, rfl⟩ := C.range_embed.symm.subset hsrc
    have hy_not_ball : y.1 ∉ Metric.ball (0 : EuclideanPlane) r₀ := by
      intro hy_ball
      have hy_closed : y.1 ∈ Metric.closedBall (0 : EuclideanPlane) r₀ :=
        Metric.ball_subset_closedBall hy_ball
      exact hz ⟨⟨y.1, hy_closed⟩, Set.mem_univ _, rfl⟩
    rw [C.liftThroughChart_of_mem f t hsrc, C.rawChart_embed y,
      inv_smul_smul₀ C.radius_pos.ne', hf_supp t y.1 hy_not_ball, C.embed_apply]
  · exact C.liftThroughChart_of_notMem f t hsrc

/-- Joint $C^\infty$ smoothness of `C.liftThroughChart f` on `ℝ × F` for any Hausdorff surface `F`
and compactly supported planar family `f`. -/
theorem contMDiff_liftThroughChart [T2Space F] (C : SymplecticDiskChart F η)
    {f : ℝ × EuclideanPlane → EuclideanPlane} (hf : ContDiff ℝ ∞ f)
    (hf_mem : ∀ (t : ℝ) {w : EuclideanPlane}, w ∈ UnitDisk2 → f (t, w) ∈ UnitDisk2)
    {r₀ : ℝ} (hr₀ : r₀ < 1)
    (hf_supp : ∀ (t : ℝ) (w : EuclideanPlane),
      w ∉ Metric.ball (0 : EuclideanPlane) r₀ → f (t, w) = w) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ (C.liftThroughChart f) := by
  rintro ⟨t₀, z₀⟩
  by_cases hz₀ : z₀ ∈ C.sourceOpen.1
  · have h1 : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun q : ℝ × F ↦ C.rawChart q.2) (t₀, z₀) :=
      (C.rawChart.contMDiffOn_toFun.contMDiffAt
        (C.rawChart.open_source.mem_nhds hz₀.1)).comp (t₀, z₀) contMDiffAt_snd
    have h2 : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × EuclideanPlane) ∞
        (fun q : ℝ × F ↦ (q.1, C.radius⁻¹ • C.rawChart q.2)) (t₀, z₀) :=
      contMDiffAt_fst.prodMk_space
        ((contDiff_planeScale C.radius⁻¹).contMDiff.contMDiffAt.comp (t₀, z₀) h1)
    have hf_prod : ContMDiff 𝓘(ℝ, ℝ × EuclideanPlane) (𝓡 2) ∞
        (fun p : ℝ × EuclideanPlane ↦ C.radius • f p) :=
      ((contDiff_planeScale C.radius).comp hf).contMDiff
    have h3 : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun q : ℝ × F ↦ C.radius • f (q.1, C.radius⁻¹ • C.rawChart q.2)) (t₀, z₀) :=
      (hf_prod _).comp (t₀, z₀) h2
    have hw₀ : C.radius⁻¹ • C.rawChart z₀ ∈ UnitDisk2 := C.inv_scale_mem_unitDisk2 hz₀.2
    have hmem_tgt : C.radius • f (t₀, C.radius⁻¹ • C.rawChart z₀) ∈ C.rawChart.target :=
      C.ball_subset_target (C.scale_mem_ball (hf_mem t₀ hw₀))
    have h4 : ContMDiffAt (𝓡 2) (𝓡 2) ∞ C.rawChart.toPartialEquiv.symm
        (C.radius • f (t₀, C.radius⁻¹ • C.rawChart z₀)) :=
      C.rawChart.contMDiffOn_invFun.contMDiffAt (C.rawChart.open_target.mem_nhds hmem_tgt)
    refine (h4.comp (t₀, z₀) h3).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_univ.prod C.sourceOpen.2).mem_nhds ⟨Set.mem_univ t₀, hz₀⟩]
      with q hq
    exact C.liftThroughChart_of_mem f q.1 hq.2
  · have hz₀_not_supp : z₀ ∉ C.supportSet hr₀ :=
      fun hmem ↦ hz₀ (C.supportSet_subset_sourceOpen hr₀ hmem)
    have hclosed : IsClosed (C.supportSet hr₀) := (C.isCompact_supportSet hr₀).isClosed
    refine contMDiffAt_snd.congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_univ.prod hclosed.isOpen_compl).mem_nhds
      ⟨Set.mem_univ t₀, hz₀_not_supp⟩] with q hq
    exact C.liftThroughChart_eq_self_of_notMem_supportSet hr₀ hf_supp q.1 hq.2

section TuringIsotopy

set_option linter.concreteInstances false

variable [T2Space F] [H : HasTuringCompleteAreaPreservingDiskIsotopy]

/-- Jointly $C^\infty$ isotopy `ℝ × F → F` lifting `HasTuringCompleteAreaPreservingDiskIsotopy.d`
into `(F, η)` along `C : SymplecticDiskChart F η`. -/
noncomputable def liftIsotopy (C : SymplecticDiskChart F η) : ℝ × F → F :=
  C.liftThroughChart HasTuringCompleteAreaPreservingDiskIsotopy.d

/-- Jointly $C^\infty$ inverse family `ℝ × F → F` lifting
`HasTuringCompleteAreaPreservingDiskIsotopy.dInv` into `(F, η)`. -/
noncomputable def liftIsotopyInv (C : SymplecticDiskChart F η) : ℝ × F → F :=
  C.liftThroughChart HasTuringCompleteAreaPreservingDiskIsotopy.dInv

theorem dInv_mem_unitDisk2 (t : ℝ) {w : EuclideanPlane} (hw : w ∈ UnitDisk2) :
    HasTuringCompleteAreaPreservingDiskIsotopy.dInv (t, w) ∈ UnitDisk2 :=
  mem_unitDisk2_of_leftInverse_of_eq_self
    (f := fun z ↦ HasTuringCompleteAreaPreservingDiskIsotopy.dInv (t, z))
    (g := fun z ↦ HasTuringCompleteAreaPreservingDiskIsotopy.d (t, z))
    HasTuringCompleteAreaPreservingDiskIsotopy.r₀_lt_one (H.right_inv t)
    (fun _ hz ↦ HasTuringCompleteAreaPreservingDiskIsotopy.dInv_eq_self_of_notMem_ball t hz) hw

/-- `C.liftIsotopy` is jointly $C^\infty$ on `ℝ × F`. -/
theorem contMDiff_liftIsotopy (C : SymplecticDiskChart F η) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ C.liftIsotopy :=
  C.contMDiff_liftThroughChart H.contDiff_d
    (fun t _ hw ↦ HasTuringCompleteAreaPreservingDiskIsotopy.mem_unitDisk2 t hw)
    HasTuringCompleteAreaPreservingDiskIsotopy.r₀_lt_one H.eq_self_of_notMem_ball

/-- `C.liftIsotopyInv` is jointly $C^\infty$ on `ℝ × F`. -/
theorem contMDiff_liftIsotopyInv (C : SymplecticDiskChart F η) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ C.liftIsotopyInv :=
  C.contMDiff_liftThroughChart H.contDiff_dInv (fun t _ hw ↦ dInv_mem_unitDisk2 t hw)
    HasTuringCompleteAreaPreservingDiskIsotopy.r₀_lt_one
    (fun t _ hw ↦ HasTuringCompleteAreaPreservingDiskIsotopy.dInv_eq_self_of_notMem_ball t hw)

/-- Time-`t` slice of `C.liftIsotopy` packaged as a $C^\infty$ `Diffeomorph` of `F`. -/
noncomputable def liftSliceDiffeomorph (C : SymplecticDiskChart F η) (t : ℝ) :
    F ≃ₘ⟮𝓡 2, 𝓡 2⟯ F where
  toFun z := C.liftIsotopy (t, z)
  invFun z := C.liftIsotopyInv (t, z)
  left_inv z := C.liftThroughChart_comp_of_inv
    (fun s _ hw ↦ HasTuringCompleteAreaPreservingDiskIsotopy.mem_unitDisk2 s hw)
    H.left_inv t z
  right_inv z := C.liftThroughChart_comp_of_inv
    (fun s _ hw ↦ dInv_mem_unitDisk2 s hw) H.right_inv t z
  contMDiff_toFun := C.contMDiff_liftIsotopy.comp (contMDiff_const.prodMk contMDiff_id)
  contMDiff_invFun := C.contMDiff_liftIsotopyInv.comp (contMDiff_const.prodMk contMDiff_id)

@[simp]
theorem liftSliceDiffeomorph_apply (C : SymplecticDiskChart F η) (t : ℝ) (z : F) :
    C.liftSliceDiffeomorph t z = C.liftIsotopy (t, z) :=
  rfl

@[simp]
theorem liftSliceDiffeomorph_symm_apply (C : SymplecticDiskChart F η) (t : ℝ) (z : F) :
    (C.liftSliceDiffeomorph t).symm z = C.liftIsotopyInv (t, z) :=
  rfl

/-- At `t = 0`, `C.liftSliceDiffeomorph 0` is the identity diffeomorphism `Diffeomorph.refl`. -/
@[simp]
theorem liftSliceDiffeomorph_zero (C : SymplecticDiskChart F η) :
    C.liftSliceDiffeomorph 0 = Diffeomorph.refl (𝓡 2) F ∞ := by
  ext z
  by_cases hz : z ∈ C.sourceOpen.1
  · obtain ⟨y, rfl⟩ := C.range_embed.symm.subset hz
    change C.liftThroughChart HasTuringCompleteAreaPreservingDiskIsotopy.d (0, C.embed y) =
      C.embed y
    rw [C.liftThroughChart_embed
      (fun s _ hw ↦ HasTuringCompleteAreaPreservingDiskIsotopy.mem_unitDisk2 s hw) 0 y]
    exact congrArg C.embed (Subtype.ext (H.time_zero y.1))
  · exact C.liftThroughChart_of_notMem _ 0 hz

/-- Intertwining of `C.liftSliceDiffeomorph t` with the disk slice on `diskOpen`. -/
theorem liftSliceDiffeomorph_embed (C : SymplecticDiskChart F η) (t : ℝ) (y : diskOpen) :
    C.liftSliceDiffeomorph t (C.embed y) =
      C.embed ⟨HasTuringCompleteAreaPreservingDiskIsotopy.d (t, y.1),
        HasTuringCompleteAreaPreservingDiskIsotopy.mem_unitDisk2 t y.2⟩ :=
  C.liftThroughChart_embed
    (fun s _ hw ↦ HasTuringCompleteAreaPreservingDiskIsotopy.mem_unitDisk2 s hw) t y

/-- Every lifted slice `C.liftSliceDiffeomorph t` fixes all points outside `C.sourceOpen.1`. -/
theorem liftSliceDiffeomorph_eq_self_of_notMem_sourceOpen (C : SymplecticDiskChart F η) (t : ℝ)
    {z : F} (hz : z ∉ C.sourceOpen.1) :
    C.liftSliceDiffeomorph t z = z :=
  C.liftThroughChart_of_notMem _ t hz

/-- **Symplectic / Area Preservation of Lifted Slices**:
For every `t : ℝ`, `C.liftSliceDiffeomorph t` preserves the surface symplectic 2-form `η` under
smooth pullback (`(liftSliceDiffeomorph t)^* η = η`). -/
theorem mpullback_liftSliceDiffeomorph_eq (C : SymplecticDiskChart F η) (t : ℝ) :
    TauCeti.SmoothForm.mpullback (C.liftSliceDiffeomorph t)
        (C.liftSliceDiffeomorph t).contMDiff η = η := by
  let Φ := C.liftSliceDiffeomorph t
  let δ : diskOpen → diskOpen := fun y ↦
    ⟨HasTuringCompleteAreaPreservingDiskIsotopy.d (t, y.1),
      HasTuringCompleteAreaPreservingDiskIsotopy.mem_unitDisk2 t y.2⟩
  have hδ : ContMDiff (𝓡 2) (𝓡 2) ∞ δ :=
    (TauCeti.ContMDiff.subtypeVal_comp_iff diskOpen _).mp
      ((HasTuringCompleteAreaPreservingDiskIsotopy.contDiff_slice t).contMDiff.comp
        contMDiff_subtype_val)
  have hδ_area :
      TauCeti.SmoothForm.mpullback δ hδ
          (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val planeAreaForm) =
        TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val planeAreaForm := by
    have hval_δ : (Subtype.val : diskOpen → _) ∘ δ =
        (fun w ↦ HasTuringCompleteAreaPreservingDiskIsotopy.d (t, w)) ∘ Subtype.val := rfl
    calc
      TauCeti.SmoothForm.mpullback δ hδ
          (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val planeAreaForm)
        = TauCeti.SmoothForm.mpullback
            ((fun w ↦ HasTuringCompleteAreaPreservingDiskIsotopy.d (t, w)) ∘ Subtype.val)
            ((HasTuringCompleteAreaPreservingDiskIsotopy.contDiff_slice t).contMDiff.comp
              contMDiff_subtype_val) planeAreaForm := by
          rw [TauCeti.SmoothForm.mpullback_mpullback]
          exact mpullback_congr_fun_two _ _ hval_δ planeAreaForm
      _ = TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val
            (TauCeti.SmoothForm.mpullback
              (fun w ↦ HasTuringCompleteAreaPreservingDiskIsotopy.d (t, w))
              (HasTuringCompleteAreaPreservingDiskIsotopy.contDiff_slice t).contMDiff
              planeAreaForm) := by
          rw [← TauCeti.SmoothForm.mpullback_mpullback (Subtype.val : diskOpen → EuclideanPlane)
            (fun w ↦ HasTuringCompleteAreaPreservingDiskIsotopy.d (t, w)) contMDiff_subtype_val
            (HasTuringCompleteAreaPreservingDiskIsotopy.contDiff_slice t).contMDiff planeAreaForm]
      _ = TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val planeAreaForm := by
          rw [HasTuringCompleteAreaPreservingDiskIsotopy.mpullback_planeAreaForm_eq t]
  have hpull_embed :
      TauCeti.SmoothForm.mpullback C.embed C.contMDiff_embed
          (TauCeti.SmoothForm.mpullback Φ Φ.contMDiff η) =
        TauCeti.SmoothForm.mpullback C.embed C.contMDiff_embed η := by
    have hcomm : ⇑Φ ∘ C.embed = C.embed ∘ δ := funext fun y ↦ C.liftSliceDiffeomorph_embed t y
    calc
      TauCeti.SmoothForm.mpullback C.embed C.contMDiff_embed
          (TauCeti.SmoothForm.mpullback Φ Φ.contMDiff η)
        = TauCeti.SmoothForm.mpullback (C.embed ∘ δ) (C.contMDiff_embed.comp hδ) η := by
          rw [TauCeti.SmoothForm.mpullback_mpullback]
          exact mpullback_congr_fun_two _ _ hcomm η
      _ = TauCeti.SmoothForm.mpullback δ hδ
            (TauCeti.SmoothForm.mpullback C.embed C.contMDiff_embed η) := by
          rw [← TauCeti.SmoothForm.mpullback_mpullback δ C.embed hδ C.contMDiff_embed η]
      _ = TauCeti.SmoothForm.mpullback C.embed C.contMDiff_embed η := by
          rw [C.mpullback_embed_eq, map_smul, hδ_area]
  refine Subtype.ext (funext fun z ↦ ?_)
  by_cases hz : z ∈ C.sourceOpen.1
  · obtain ⟨y, rfl⟩ := C.range_embed.symm.subset hz
    have hsurj : Function.Surjective (mfderiv (𝓡 2) (𝓡 2) C.embed y) :=
      (C.isLocalDiffeomorph_embed.isInvertible_mfderiv (by simp) y).surjective
    refine (TauCeti.mpullback_apply_eq_mpullback_apply_iff hsurj).mp ?_
    simpa only [TauCeti.SmoothForm.coe_mpullback] using
      congrFun (congrArg Subtype.val hpull_embed) y
  · have hz_not_supp : z ∉ C.supportSet HasTuringCompleteAreaPreservingDiskIsotopy.r₀_lt_one :=
      fun hmem ↦ hz (C.supportSet_subset_sourceOpen
        HasTuringCompleteAreaPreservingDiskIsotopy.r₀_lt_one hmem)
    have hclosed : IsClosed (C.supportSet HasTuringCompleteAreaPreservingDiskIsotopy.r₀_lt_one) :=
      (C.isCompact_supportSet HasTuringCompleteAreaPreservingDiskIsotopy.r₀_lt_one).isClosed
    let V_compl : Opens F :=
      ⟨(C.supportSet HasTuringCompleteAreaPreservingDiskIsotopy.r₀_lt_one)ᶜ, hclosed.isOpen_compl⟩
    let zV : V_compl := ⟨z, hz_not_supp⟩
    have hΦ_compl : ⇑Φ ∘ (Subtype.val : V_compl → F) = (Subtype.val : V_compl → F) :=
      funext fun w ↦ C.liftThroughChart_eq_self_of_notMem_supportSet
        HasTuringCompleteAreaPreservingDiskIsotopy.r₀_lt_one H.eq_self_of_notMem_ball t w.2
    have hpull_compl :
        TauCeti.SmoothForm.mpullback (Subtype.val : V_compl → F) contMDiff_subtype_val
            (TauCeti.SmoothForm.mpullback Φ Φ.contMDiff η) =
          TauCeti.SmoothForm.mpullback (Subtype.val : V_compl → F) contMDiff_subtype_val η := by
      rw [TauCeti.SmoothForm.mpullback_mpullback]
      exact mpullback_congr_fun_two _ _ hΦ_compl η
    have hsurj_compl :
        Function.Surjective (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : V_compl → F) zV) :=
      ((TauCeti.isLocalDiffeomorph_subtype_val (I := 𝓡 2) (n := ∞) zV).isInvertible_mfderiv
        (by simp)).surjective
    refine (TauCeti.mpullback_apply_eq_mpullback_apply_iff hsurj_compl).mp ?_
    simpa only [TauCeti.SmoothForm.coe_mpullback] using
      congrFun (congrArg Subtype.val hpull_compl) zV

/-- When `η = V.Ω` for a `PositiveVolumeForm (𝓡 2) F`, every lifted slice `C.liftSliceDiffeomorph t`
is `MeasurePreserving` with respect to `V.μ`. -/
theorem measurePreserving_liftSliceDiffeomorph {F : Type*} [TopologicalSpace F]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F] [IsManifold (𝓡 2) ∞ F] [T2Space F]
    [MeasurableSpace F] [BorelSpace F] (V : PositiveVolumeForm (𝓡 2) F)
    (C : SymplecticDiskChart F V.Ω) (t : ℝ) :
    MeasurePreserving ⇑(C.liftSliceDiffeomorph t) V.μ V.μ :=
  V.measurePreserving_of_mpullback_eq (C.liftSliceDiffeomorph t)
    (C.mpullback_liftSliceDiffeomorph_eq t)

/-- **Turing Completeness of the Lifted Time-`1` Surface Symplectomorphism**:
On any nonempty Hausdorff smooth surface `(F, η)` (any genus `g ≥ 0`), the time-`1` slice
`C.liftSliceDiffeomorph 1 : F ≃ₘ⟮𝓡 2, 𝓡 2⟯ F` is Turing complete (`IsTuringComplete`). -/
theorem isTuringComplete_liftTimeOne (C : SymplecticDiskChart F η) :
    IsTuringComplete ⇑(C.liftSliceDiffeomorph 1) := by
  obtain ⟨W⟩ := HasTuringCompleteAreaPreservingDiskIsotopy.isTuringComplete_diskTimeOneMap
  let ι : UnitDisk2 → F := fun y ↦ C.embed ⟨y.1, y.2⟩
  have hι : Topology.IsOpenEmbedding ι := C.isOpenEmbedding_embed
  have hcomm : ∀ y : UnitDisk2,
      C.liftSliceDiffeomorph 1 (ι y) =
        ι (HasTuringCompleteAreaPreservingDiskIsotopy.diskTimeOneMap y) :=
    fun y ↦ C.liftSliceDiffeomorph_embed 1 ⟨y.1, y.2⟩
  have hiter : ∀ (y : UnitDisk2) (n : ℕ),
      (⇑(C.liftSliceDiffeomorph 1))^[n] (ι y) =
        ι (HasTuringCompleteAreaPreservingDiskIsotopy.diskTimeOneMap^[n] y) := by
    intro y n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, hcomm, Function.iterate_succ_apply']
  refine ⟨{
    encodePoint := fun M_tm t_in ↦ ι (W.encodePoint M_tm t_in)
    encodeOpen := fun M_tm k w ↦
      ⟨ι '' (W.encodeOpen M_tm k w).1, hι.isOpenMap _ (W.encodeOpen M_tm k w).2⟩
    encodeOpen_nonempty := fun M_tm k w ↦ (W.encodeOpen_nonempty M_tm k w).image ι
    orbit_mem_encodeOpen_iff := fun M_tm t_in k w ↦ by
      refine (exists_congr fun n ↦ ?_).trans (W.orbit_mem_encodeOpen_iff M_tm t_in k w)
      change (⇑(C.liftSliceDiffeomorph 1))^[n] (ι (W.encodePoint M_tm t_in)) ∈
        ι '' (W.encodeOpen M_tm k w).1 ↔ _
      rw [hiter, hι.injective.mem_set_image]
      rfl
    notMem_encodeOpen_of_step_ne_none := fun M_tm t_in k w hstep ↦ by
      change ι (W.encodePoint M_tm t_in) ∉ ι '' (W.encodeOpen M_tm k w).1
      rw [hι.injective.mem_set_image]
      exact W.notMem_encodeOpen_of_step_ne_none M_tm t_in k w hstep
    Param := W.Param
    instTopologicalSpaceParam := W.instTopologicalSpaceParam
    param₀ := W.param₀
    openChart := ι ∘ W.openChart
    openChart_isOpenEmbedding := by
      let _ := W.instTopologicalSpaceParam
      exact hι.comp W.openChart_isOpenEmbedding
    chart := fun y ↦ ι (W.chart y)
    chart_eq_openChart := fun y ↦ congrArg ι (W.chart_eq_openChart y)
    chart_continuous := hι.continuous.comp W.chart_continuous
    chart_injective := hι.injective.comp W.chart_injective
    coordPoint := W.coordPoint
    encodePoint_eq_chart := fun M_tm t_in ↦ congrArg ι (W.encodePoint_eq_chart M_tm t_in)
    computable_approx := W.computable_approx
    computable_encodeOpen := fun M_tm ↦ by
      obtain ⟨encΓ, enumBoxes, hcomp, hboxes⟩ := W.computable_encodeOpen M_tm
      refine ⟨encΓ, enumBoxes, hcomp, fun k w ↦ ⟨(hboxes k w).1, ?_⟩⟩
      change ι '' (W.encodeOpen M_tm k w).1 = _
      rw [(hboxes k w).2, ← Set.image_comp]
    orbit_encodePoint_injective := fun M_tm t_in n₁ n₂ h ↦ by
      dsimp only at h
      rw [hiter _ n₁, hiter _ n₂] at h
      exact W.orbit_encodePoint_injective M_tm t_in (hι.injective h)
  }⟩

end TuringIsotopy

end SymplecticDiskChart

/-! ## 5. Direct Fiber Accessors for `AdmitsRegularDiskFibration` -/

section FiberAccessors

set_option linter.concreteInstances false

/-- Canonical Darboux symplectic disk chart on the regular surface fiber `A.Fiber` of any
4-manifold `M` with `[A : AdmitsRegularDiskFibration M]`. -/
noncomputable def AdmitsRegularDiskFibration.fiberDiskChart
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [A : AdmitsRegularDiskFibration M] :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instMeasurableSpaceFiber
    letI := A.instBorelSpaceFiber
    SymplecticDiskChart A.Fiber A.fiberVolume.Ω := by
  letI := A.instTopologicalSpaceFiber
  letI := A.instChartedSpaceFiber
  letI := A.instIsManifoldFiber
  letI := A.instNonemptyFiber
  letI := A.instMeasurableSpaceFiber
  letI := A.instBorelSpaceFiber
  exact A.fiberVolume.symplecticDiskChart

/-- Open product embedding `A.fibration.baseRegion × diskOpen → M` over the regular base disk of any
`[A : AdmitsRegularDiskFibration M]`, directly usable by Milestone M4's leafwise bump
isotopy lift and `IsTuringComplete.transfer`. -/
noncomputable def AdmitsRegularDiskFibration.baseDiskProductEmbed
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [A : AdmitsRegularDiskFibration M] :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    A.fibration.baseRegion × diskOpen → M := by
  letI := A.instTopologicalSpaceFiber
  letI := A.instChartedSpaceFiber
  letI := A.instIsManifoldFiber
  letI := A.instT2SpaceFiber
  letI := A.instCompactSpaceFiber
  letI := A.instNonemptyFiber
  letI := A.instMeasurableSpaceFiber
  letI := A.instBorelSpaceFiber
  let C := AdmitsRegularDiskFibration.fiberDiskChart M
  exact fun by_pair ↦ A.fibration.embed (by_pair.1, C.embed by_pair.2)

/-- `baseDiskProductEmbed M` is $C^\infty$ smooth, an open embedding, and maps `(b, y)` into the
fiber of `A.fibration` over `b`. -/
theorem AdmitsRegularDiskFibration.isOpenEmbedding_baseDiskProductEmbed
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [A : AdmitsRegularDiskFibration M] :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    ContMDiff ((𝓡 2).prod (𝓡 2)) (𝓡 4) ∞
      (AdmitsRegularDiskFibration.baseDiskProductEmbed M) ∧
    Topology.IsOpenEmbedding
      (AdmitsRegularDiskFibration.baseDiskProductEmbed M) ∧
    ∀ p : A.fibration.baseRegion × diskOpen,
      A.fibration (AdmitsRegularDiskFibration.baseDiskProductEmbed M p) = p.1.1 := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := A.instMeasurableSpaceFiber
  let _ := A.instBorelSpaceFiber
  let C := AdmitsRegularDiskFibration.fiberDiskChart M
  refine ⟨?_, ?_, fun p ↦ A.fibration.apply_embed p.1 (C.embed p.2)⟩
  · exact A.fibration.contMDiff_embed.comp (contMDiff_fst.prodMk (C.contMDiff_embed.comp
      contMDiff_snd))
  · exact A.fibration.isOpenEmbedding_embed.comp
      (Topology.IsOpenEmbedding.id.prodMap C.isOpenEmbedding_embed)

end FiberAccessors

end DiskIsotopyLift

end S4TuringPoisson
