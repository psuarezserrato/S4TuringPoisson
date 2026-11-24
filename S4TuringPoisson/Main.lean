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

public import S4TuringPoisson.Extension.AlignedUnimodularVolume
public import S4TuringPoisson.Extension.BumpIsotopyLift
public import S4TuringPoisson.Extension.MoserVolume
public import S4TuringPoisson.Smoothing.CMPPInstance
public import S4TuringPoisson.Fibration.ClosedManifoldLocal
public import S4TuringPoisson.Fibration.LekiliMoves

/-!
# Main Theorems: Turing Complete Volume-Preserving Poisson Diffeomorphisms on $S^4$ and 4-Manifolds

This module implements Milestone M5 and CMPP Milestone Z (Deliverable R2) of `S4TuringPoisson`,
synthesizing Milestones M0–M4 together with the unconditional `CMPP21` autonomous Hamiltonian
realization (`S4TuringPoisson.Smoothing.CMPPInstance`) to export **unconditional** proofs (zero
external typeclass hypotheses on `Sphere4`) of all headline theorems of Pablo Suárez-Serrato,
*"Hamiltonian and Turing complete flows on smooth 4-manifolds"* (`S4TCdiffeo-Aug-2026.tex`):

1. **Theorem 1 (`exists_turingComplete_volumePreserving_poissonDiffeomorph_S4` &
   `exists_turingComplete_volumePreserving_diffeomorph_S4` — `UNCONDITIONAL`)**:
   - Constructs unconditionally on the standard unit 4-sphere `Sphere4` (`S⁴ ⊂ ℝ⁵`) a positive
     volume 4-form `s4AlignedPositiveVolume`, a generically rank-`2` unimodular Jacobian–Poisson
     structure `s4AdaptedPoisson` adapted to `s4Fibration : Sphere4 → Sphere2` (rank `2` outside
     `Crit`, rank `0` along the nonempty equatorial singular circle `Crit`), and a global $C^\infty$
     diffeomorphism `s4TuringDiffeomorph : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4` that:
     - preserves every fiber / leaf (`s4Fibration ∘ d_bar = s4Fibration`), acts as a global Poisson
       automorphism (`IsPoissonMap`), and restricts to an area-preserving symplectomorphism on
       every regular $S^2$ leaf over `s4BaseRegion`,
     - preserves the global unimodular volume 4-form (`d_bar^* Ω = Ω`) and its positive finite
       Borel measure (`MeasurePreserving ⇑d_bar μ_Ω μ_Ω`), and
     - is Turing complete (`IsTuringComplete ⇑d_bar`, hence `⇑d_bar ≠ id`).

2. **Corollary 2 (`exists_turingComplete_volumePreserving_poissonDiffeomorph_fourManifold` —
   `UNCONDITIONAL` in dynamics)**:
   - Establishes the complete analogous bundle on any compact Hausdorff smooth 4-manifold `M`
     admitting `[AdmitsWrinkledOrBrokenLefschetzFibration M]` (`Gay–Kirby` / `Lekili`), supporting
     regular surface fibers of arbitrary genus `g ≥ 0` via Darboux disk charts without topological
     genus-reduction surgery and with zero disk-isotopy typeclass assumptions.

3. **Algorithmic Undecidability on $S^4$ (`undecidable_orbit_reachability_S4` — `UNCONDITIONAL`)**:
   - Proves unconditionally that forward-orbit reachability of `s4TuringDiffeomorph` on `Sphere4`
     from computably `2⁻ᵐ`-approximable initial points into a fixed nonempty open target
     `U : Opens Sphere4` is recursively enumerable (`REPred`) yet algorithmically undecidable
     (`¬ ComputablePred`).

4. **Parametric `CMPP21` Specializations (`*_of_cmpp`) & Sector-Swap Witness**:
   - Retains all four parametric `[C : HasCMPPCantorCirculationHamiltonians]` specializations
     `*_of_cmpp` (proved genuinely from `C` via
     `instHasTuringCompleteAreaPreservingDiskIsotopyOfCMPP`) alongside the explicit sector-swap
     Poisson diffeomorphism `s4UnconditionalPoissonDiffeomorph`.
-/

@[expose] public section

open Function MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace S4TuringPoisson.Main

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

/-! ## 1. Canonical Adapted Volume & Jacobian–Poisson Package on $S^4$ -/

/-- Aligned positive volume 4-form and finite Borel measure `(Ω, μ_Ω)` on `Sphere4`. -/
noncomputable def s4AlignedPositiveVolume : PositiveVolumeForm (𝓡 4) Sphere4 :=
  alignedPositiveVolume Sphere4

/-- Generically rank-`2`, globally unimodular Jacobian–Poisson structure `π_f` on `Sphere4`
adapted to `s4Fibration : Sphere4 → Sphere2` and `s4AlignedPositiveVolume`. -/
noncomputable def s4AdaptedPoisson : PoissonStructure (𝓡 4) Sphere4 :=
  adaptedJacobianPoisson Sphere4

/-- `s4AdaptedPoisson` is generically rank `2` on `Sphere4` (`IsOpen` and `Dense` rank-`2` locus).
-/
-- tier: T1
theorem isGenericallyRankTwo_s4AdaptedPoisson :
    s4AdaptedPoisson.IsGenericallyRankTwo :=
  (isGenericallyRankTwo_adaptedJacobianPoisson_iff Sphere4).mpr dense_regularPoints_s4Fibration

/-- Antipodal point `-p ∈ Sphere4` of `p ∈ Sphere4`, used to witness non-atomic upper volume
bounds (`μ_Ω (ball p (1/2)) < μ_Ω univ`). -/
def s4Antipode (p : Sphere4) : Sphere4 :=
  ⟨-p.1, by simp⟩

/-- Euclidean chordal distance on `Sphere4 ⊂ ℝ⁵` between any point `p` and `s4Antipode p` is `2`. -/
theorem dist_s4Antipode (p : Sphere4) : dist p (s4Antipode p) = 2 := by
  have hp_norm : ‖p.1‖ = 1 := by simp
  change dist p.1 (-p.1) = 2
  rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ p.1, norm_smul, Real.norm_ofNat, hp_norm, mul_one]

/-- Gate 5 non-degeneracy bounds for `s4AlignedPositiveVolume.μ` on `Sphere4`: every radius-`1/2`
ball has strictly positive measure strictly smaller than total volume `μ_Ω Set.univ`. -/
theorem s4AlignedPositiveVolume_ball_bounds (p : Sphere4) :
    0 < s4AlignedPositiveVolume.μ (Metric.ball p (1 / 2)) ∧
      s4AlignedPositiveVolume.μ (Metric.ball p (1 / 2)) <
        s4AlignedPositiveVolume.μ Set.univ := by
  have hne_p : (Metric.ball p (1 / 2)).Nonempty := Metric.nonempty_ball.mpr (by norm_num)
  have hne_q : (Metric.ball (s4Antipode p) (1 / 2)).Nonempty :=
    Metric.nonempty_ball.mpr (by norm_num)
  have hdisj : Disjoint (Metric.ball p (1 / 2)) (Metric.ball (s4Antipode p) (1 / 2)) :=
    Metric.ball_disjoint_ball (by rw [dist_s4Antipode p]; norm_num)
  exact ⟨s4AlignedPositiveVolume.measure_isOpen_pos Metric.isOpen_ball hne_p,
    s4AlignedPositiveVolume.measure_lt_univ_of_disjoint_isOpen Metric.isOpen_ball hne_q hdisj⟩

/-! ## 2. Unconditional Nontrivial Volume-Preserving Poisson Diffeomorphism on $S^4$ -/

section UnconditionalS4Witness

/-- Unconditional compactly supported sector-swap disk isotopy (`r₀ = 3 / 4`) from Milestone
M3.3. -/
noncomputable def s4SectorSwapDiskIsotopy : AreaPreservingDiskIsotopy (3 / 4) :=
  canonicalSectorSwapIsotopy ⟨by norm_num, by norm_num⟩

/-- Unconditional smooth, leaf-preserving, volume-preserving Poisson diffeomorphism on `Sphere4`
lifting `s4SectorSwapDiskIsotopy` (requiring **zero** external typeclasses). -/
noncomputable def s4UnconditionalPoissonDiffeomorph : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4 :=
  leafwiseBumpDiffeomorphOfIsotopy Sphere4 s4SectorSwapDiskIsotopy

/-- Non-triviality (`≠ id`) of the sector-swap Poisson diffeomorphism
`s4UnconditionalPoissonDiffeomorph` on `Sphere4`. -/
theorem s4UnconditionalPoissonDiffeomorph_ne_id :
    (⇑s4UnconditionalPoissonDiffeomorph : Sphere4 → Sphere4) ≠ id := by
  intro hid
  have hdisk_ne : s4SectorSwapDiskIsotopy.diskTimeOneMap ≠ id :=
    (canonicalSectorSwapIsotopy_properties (r₀ := 3 / 4) ⟨by norm_num, by norm_num⟩).2.2.2.2.2
  apply hdisk_ne
  funext y
  let C : SymplecticDiskChart Sphere2 S2VolumeForm :=
    AdmitsRegularDiskFibration.fiberDiskChart Sphere4
  let b₀ := s4RegularDiskFibration.baseCenter
  have hb₀ : b₀.1 ∈ (baseCoreOpen Sphere4).1 := baseCenter_mem_baseCoreOpen Sphere4
  have hρ1 : bumpProfile Sphere4 b₀.1 = 1 :=
    bumpProfile_eq_one_of_mem_baseCoreOpen Sphere4 hb₀
  let x₀ : Sphere4 := s4RegularDiskFibration.embed (b₀, C.embed ⟨y.1, y.2⟩)
  have hx₀ : s4UnconditionalPoissonDiffeomorph x₀ = x₀ := congrFun hid x₀
  dsimp only [s4UnconditionalPoissonDiffeomorph, x₀] at hx₀
  have hemb_step :
      leafwiseBumpDiffeomorphOfIsotopy Sphere4 s4SectorSwapDiskIsotopy
          (s4RegularDiskFibration.embed (b₀, C.embed ⟨y.1, y.2⟩)) =
        s4RegularDiskFibration.embed
          (b₀, C.liftIsotopyDiffeomorph s4SectorSwapDiskIsotopy (bumpProfile Sphere4 b₀.1)
            (C.embed ⟨y.1, y.2⟩)) :=
    leafwiseBumpDiffeomorphOfIsotopy_embed Sphere4 s4SectorSwapDiskIsotopy b₀
      (C.embed ⟨y.1, y.2⟩)
  rw [hemb_step, hρ1, C.liftIsotopyDiffeomorph_embed s4SectorSwapDiskIsotopy 1 ⟨y.1, y.2⟩] at hx₀
  have hinj_emb := s4RegularDiskFibration.isOpenEmbedding_embed.injective hx₀
  have hinj_C := C.injective_embed (Prod.mk.inj hinj_emb).2
  exact Subtype.ext (congrArg Subtype.val hinj_C)

/-- **Unconditional $S^4$ Volume-Preserving Poisson Diffeomorphism Theorem** (zero typeclasses):
`s4UnconditionalPoissonDiffeomorph` preserves `s4Fibration`, `s4AlignedPositiveVolume.Ω`,
`s4AlignedPositiveVolume.μ`, and `s4AdaptedPoisson`, and satisfies `≠ id`. -/
theorem exists_nontrivial_volumePreserving_poissonDiffeomorph_S4_unconditional :
    s4Fibration ∘ ⇑s4UnconditionalPoissonDiffeomorph = s4Fibration ∧
      SmoothBivector.IsPoissonMap s4AdaptedPoisson.toSmoothBivector
        s4AdaptedPoisson.toSmoothBivector s4UnconditionalPoissonDiffeomorph
        s4UnconditionalPoissonDiffeomorph.contMDiff ∧
      TauCeti.SmoothForm.mpullback s4UnconditionalPoissonDiffeomorph
        s4UnconditionalPoissonDiffeomorph.contMDiff s4AlignedPositiveVolume.Ω =
        s4AlignedPositiveVolume.Ω ∧
      MeasurePreserving ⇑s4UnconditionalPoissonDiffeomorph
        s4AlignedPositiveVolume.μ s4AlignedPositiveVolume.μ ∧
      (⇑s4UnconditionalPoissonDiffeomorph : Sphere4 → Sphere4) ≠ id :=
  ⟨fibration_comp_leafwiseBumpDiffeomorphOfIsotopy Sphere4 s4SectorSwapDiskIsotopy,
    isPoissonMap_leafwiseBumpDiffeomorphOfIsotopy Sphere4 s4SectorSwapDiskIsotopy,
    mpullback_leafwiseBumpDiffeomorphOfIsotopy_alignedVolumeForm Sphere4 s4SectorSwapDiskIsotopy,
    measurePreserving_leafwiseBumpDiffeomorphOfIsotopy Sphere4 s4SectorSwapDiskIsotopy,
    s4UnconditionalPoissonDiffeomorph_ne_id⟩

end UnconditionalS4Witness

/-! ## 3. Headline Theorems 1, Corollary 2 & Undecidability (`MISSION_DIRECTIVE.md` §1 & M5/Z) -/

section ParametricHeadlineTheorems

set_option linter.concreteInstances false

variable [H : HasTuringCompleteAreaPreservingDiskIsotopy]

/-- Parametric helper for Theorem 1 (full Poisson/foliation/volume/Turing bundle on `Sphere4`)
indexed by an arbitrary `[HasTuringCompleteAreaPreservingDiskIsotopy]` instance. -/
-- tier: T2
private theorem exists_turingComplete_volumePreserving_poissonDiffeomorph_S4_of_isotopy :
    ∃ (V : PositiveVolumeForm (𝓡 4) Sphere4)
      (π_f : PoissonStructure (𝓡 4) Sphere4)
      (d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4),
      π_f = jacobianPoissonOfPositiveVolume V S2VolumeForm s4Fibration contMDiff_s4Fibration ∧
      π_f.IsUnimodularWithVolume V.Ω ∧
      π_f.IsUnimodularPoisson ∧
      π_f.IsGenericallyRankTwo ∧
      (∀ x ∉ criticalPoints (𝓡 4) (𝓡 2) s4Fibration, π_f.rankAt x = 2) ∧
      (criticalPoints (𝓡 4) (𝓡 2) s4Fibration).Nonempty ∧
      (∀ x ∈ criticalPoints (𝓡 4) (𝓡 2) s4Fibration, π_f.rankAt x = 0) ∧
      s4Fibration ∘ ⇑d_bar = s4Fibration ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_bar d_bar.contMDiff ∧
      (∀ b : s4BaseRegion,
        ∃ d_b : Sphere2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere2,
          (∀ z : Sphere2,
            d_bar (s4RegularDiskFibration.embed (b, z)) = s4RegularDiskFibration.embed (b, d_b z)) ∧
          TauCeti.SmoothForm.mpullback d_b d_b.contMDiff S2VolumeForm = S2VolumeForm ∧
          MeasurePreserving ⇑d_b S2PositiveVolumeForm.μ S2PositiveVolumeForm.μ) ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasurePreserving ⇑d_bar V.μ V.μ ∧
      IsTuringComplete ⇑d_bar ∧
      (⇑d_bar : Sphere4 → Sphere4) ≠ id ∧
      V.μ = TauCeti.RoughForm.measure V.Ω.1 := by
  refine ⟨s4AlignedPositiveVolume, s4AdaptedPoisson, leafwiseBumpDiffeomorph Sphere4,
    rfl,
    isUnimodularWithVolume_adaptedJacobianPoisson Sphere4,
    isUnimodularPoisson_adaptedJacobianPoisson Sphere4,
    isGenericallyRankTwo_s4AdaptedPoisson,
    fun x hx ↦ rankAt_adaptedJacobianPoisson_of_notMem_criticalPoints Sphere4 hx,
    criticalPoints_s4Fibration_nonempty,
    fun x hx ↦ rankAt_adaptedJacobianPoisson_of_mem_criticalPoints Sphere4 hx,
    fibration_comp_leafwiseBumpDiffeomorph Sphere4,
    isPoissonMap_leafwiseBumpDiffeomorph Sphere4,
    fun b ↦ ?_,
    mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm Sphere4,
    measurePreserving_leafwiseBumpDiffeomorph Sphere4,
    isTuringComplete_leafwiseBumpDiffeomorph Sphere4,
    leafwiseBumpDiffeomorph_ne_id Sphere4,
    rfl⟩
  let C : SymplecticDiskChart Sphere2 S2VolumeForm :=
    AdmitsRegularDiskFibration.fiberDiskChart Sphere4
  let d_b : Sphere2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere2 :=
    C.liftSliceDiffeomorph (bumpProfile Sphere4 b.1)
  exact ⟨d_b, fun z ↦ leafwiseBumpDiffeomorph_embed Sphere4 b z,
    C.mpullback_liftSliceDiffeomorph_eq (bumpProfile Sphere4 b.1),
    SymplecticDiskChart.measurePreserving_liftSliceDiffeomorph S2PositiveVolumeForm C
      (bumpProfile Sphere4 b.1)⟩

/-- Parametric helper for Theorem 1 (concise volume-preserving diffeomorphism bundle on `Sphere4`)
indexed by an arbitrary `[HasTuringCompleteAreaPreservingDiskIsotopy]` instance. -/
-- tier: T2
private theorem exists_turingComplete_volumePreserving_diffeomorph_S4_of_isotopy :
    ∃ (V : PositiveVolumeForm (𝓡 4) Sphere4)
      (d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4),
      s4Fibration ∘ ⇑d_bar = s4Fibration ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasurePreserving ⇑d_bar V.μ V.μ ∧
      IsTuringComplete ⇑d_bar ∧
      V.μ = TauCeti.RoughForm.measure V.Ω.1 :=
  ⟨s4AlignedPositiveVolume, leafwiseBumpDiffeomorph Sphere4,
    fibration_comp_leafwiseBumpDiffeomorph Sphere4,
    mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm Sphere4,
    measurePreserving_leafwiseBumpDiffeomorph Sphere4,
    isTuringComplete_leafwiseBumpDiffeomorph Sphere4,
    rfl⟩

/-- Parametric helper for Corollary 2 on general compact Hausdorff smooth 4-manifolds `M` indexed
by an arbitrary `[HasTuringCompleteAreaPreservingDiskIsotopy]` instance. -/
-- tier: T2
@[nolint unusedArguments]
private theorem exists_turingComplete_volumePreserving_poissonDiffeomorph_fourManifold_of_isotopy
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [T2Space M] [A : AdmitsWrinkledOrBrokenLefschetzFibration M] :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    letI := A.instMeasurableSpaceFiber
    letI := A.instBorelSpaceFiber
    ∃ (V : PositiveVolumeForm (𝓡 4) M)
      (π_f : PoissonStructure (𝓡 4) M)
      (d_bar : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M),
      π_f = jacobianPoissonOfPositiveVolume V S2VolumeForm A.fibration
        A.fibration.contMDiff_toFun ∧
      π_f.IsUnimodularWithVolume V.Ω ∧
      π_f.IsUnimodularPoisson ∧
      π_f.IsGenericallyRankTwo ∧
      (∀ x ∉ criticalPoints (𝓡 4) (𝓡 2) A.fibration, π_f.rankAt x = 2) ∧
      (∀ x ∈ criticalPoints (𝓡 4) (𝓡 2) A.fibration, π_f.rankAt x = 0) ∧
      ⇑A.fibration ∘ ⇑d_bar = ⇑A.fibration ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_bar d_bar.contMDiff ∧
      (∀ b : A.fibration.baseRegion,
        ∃ d_b : A.Fiber ≃ₘ⟮𝓡 2, 𝓡 2⟯ A.Fiber,
          (∀ z : A.Fiber,
            d_bar (A.fibration.embed (b, z)) = A.fibration.embed (b, d_b z)) ∧
          TauCeti.SmoothForm.mpullback d_b d_b.contMDiff A.fiberVolume.Ω = A.fiberVolume.Ω ∧
          MeasurePreserving ⇑d_b A.fiberVolume.μ A.fiberVolume.μ) ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasurePreserving ⇑d_bar V.μ V.μ ∧
      IsTuringComplete ⇑d_bar ∧
      (⇑d_bar : M → M) ≠ id ∧
      V.μ = TauCeti.RoughForm.measure V.Ω.1 := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := A.instMeasurableSpaceFiber
  let _ := A.instBorelSpaceFiber
  refine ⟨alignedPositiveVolume M, adaptedJacobianPoisson M, leafwiseBumpDiffeomorph M,
    rfl,
    isUnimodularWithVolume_adaptedJacobianPoisson M,
    isUnimodularPoisson_adaptedJacobianPoisson M,
    isGenericallyRankTwo_adaptedJacobianPoisson M,
    fun x hx ↦ rankAt_adaptedJacobianPoisson_of_notMem_criticalPoints M hx,
    fun x hx ↦ rankAt_adaptedJacobianPoisson_of_mem_criticalPoints M hx,
    fibration_comp_leafwiseBumpDiffeomorph M,
    isPoissonMap_leafwiseBumpDiffeomorph M,
    fun b ↦ ?_,
    mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm M,
    measurePreserving_leafwiseBumpDiffeomorph M,
    isTuringComplete_leafwiseBumpDiffeomorph M,
    leafwiseBumpDiffeomorph_ne_id M,
    rfl⟩
  let C := AdmitsRegularDiskFibration.fiberDiskChart M
  let d_b := C.liftSliceDiffeomorph (bumpProfile M b.1)
  exact ⟨d_b, fun z ↦ leafwiseBumpDiffeomorph_embed M b z,
    C.mpullback_liftSliceDiffeomorph_eq (bumpProfile M b.1),
    SymplecticDiskChart.measurePreserving_liftSliceDiffeomorph A.fiberVolume C
      (bumpProfile M b.1)⟩

/-- Parametric helper for algorithmic undecidability of forward-orbit reachability on `Sphere4`
indexed by an arbitrary `[HasTuringCompleteAreaPreservingDiskIsotopy]` instance. -/
-- tier: T2
private theorem undecidable_orbit_reachability_S4_of_isotopy :
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
      s4Fibration ∘ ⇑d_bar = s4Fibration ∧
      π_f.IsUnimodularWithVolume V.Ω ∧
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
  obtain ⟨U, Param, instTopParam, param₀, openChart, chart, coord, approx, targetBoxes, hU,
      hopen, hchart_eq, hcont, hinj, hcomp, hbound, hcomp_boxes, hbox_ne, hU_eq, hnot0, hre,
      hnotcomp, hnodec⟩ :=
    undecidable_orbit_reachability_leafwiseBumpDiffeomorph Sphere4
  exact ⟨s4AlignedPositiveVolume, s4AdaptedPoisson, leafwiseBumpDiffeomorph Sphere4, U, Param,
    instTopParam, param₀, openChart, chart, coord, approx, targetBoxes,
    fibration_comp_leafwiseBumpDiffeomorph Sphere4,
    isUnimodularWithVolume_adaptedJacobianPoisson Sphere4,
    isPoissonMap_leafwiseBumpDiffeomorph Sphere4,
    mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm Sphere4,
    measurePreserving_leafwiseBumpDiffeomorph Sphere4,
    hU, hopen, hchart_eq, hcont, hinj, hcomp, hbound, hcomp_boxes, hbox_ne, hU_eq, hnot0, hre,
    hnotcomp, hnodec, rfl⟩

end ParametricHeadlineTheorems

section HeadlineTheorems

/-- Headline unconditional smooth, leaf-preserving, volume-preserving, Turing complete Poisson
diffeomorphism `d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4` on the 4-sphere (`UNCONDITIONAL`). -/
noncomputable def s4TuringDiffeomorph : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4 :=
  leafwiseBumpDiffeomorph Sphere4

/-- **Theorem 1 (`S4TCdiffeo-Aug-2026.tex` — Full Poisson, Foliation, Volume & Turing Bundle)**:
On the standard smooth 4-sphere `Sphere4` (`S⁴`), there exist a positive volume 4-form `V`, a
generically rank-`2` unimodular Jacobian–Poisson structure `π_f` adapted to
`s4Fibration : Sphere4 → Sphere2` (with rank `2` off `Crit` and rank `0` along the nonempty
singular circle `Crit`), and a $C^\infty$ diffeomorphism `d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4`
such that:
- `s4Fibration ∘ d_bar = s4Fibration` (preserving every fiber / symplectic leaf), `d_bar` is a
  global Poisson automorphism of `(Sphere4, π_f)`, and on every regular $S^2$ leaf over
  `s4BaseRegion`, `d_bar` acts as a smooth area-preserving symplectomorphism for `S2VolumeForm`,
- `d_bar` preserves the global unimodular volume form (`d_bar^* V.Ω = V.Ω`) and its positive finite
  Borel volume measure (`MeasurePreserving ⇑d_bar V.μ V.μ`), and
- `d_bar` is Turing complete (`IsTuringComplete ⇑d_bar`, hence `⇑d_bar ≠ id`). -/
-- tier: T2
theorem exists_turingComplete_volumePreserving_poissonDiffeomorph_S4 :
    ∃ (V : PositiveVolumeForm (𝓡 4) Sphere4)
      (π_f : PoissonStructure (𝓡 4) Sphere4)
      (d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4),
      π_f = jacobianPoissonOfPositiveVolume V S2VolumeForm s4Fibration contMDiff_s4Fibration ∧
      π_f.IsUnimodularWithVolume V.Ω ∧
      π_f.IsUnimodularPoisson ∧
      π_f.IsGenericallyRankTwo ∧
      (∀ x ∉ criticalPoints (𝓡 4) (𝓡 2) s4Fibration, π_f.rankAt x = 2) ∧
      (criticalPoints (𝓡 4) (𝓡 2) s4Fibration).Nonempty ∧
      (∀ x ∈ criticalPoints (𝓡 4) (𝓡 2) s4Fibration, π_f.rankAt x = 0) ∧
      s4Fibration ∘ ⇑d_bar = s4Fibration ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_bar d_bar.contMDiff ∧
      (∀ b : s4BaseRegion,
        ∃ d_b : Sphere2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere2,
          (∀ z : Sphere2,
            d_bar (s4RegularDiskFibration.embed (b, z)) = s4RegularDiskFibration.embed (b, d_b z)) ∧
          TauCeti.SmoothForm.mpullback d_b d_b.contMDiff S2VolumeForm = S2VolumeForm ∧
          MeasurePreserving ⇑d_b S2PositiveVolumeForm.μ S2PositiveVolumeForm.μ) ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasurePreserving ⇑d_bar V.μ V.μ ∧
      IsTuringComplete ⇑d_bar ∧
      (⇑d_bar : Sphere4 → Sphere4) ≠ id ∧
      V.μ = TauCeti.RoughForm.measure V.Ω.1 :=
  exists_turingComplete_volumePreserving_poissonDiffeomorph_S4_of_isotopy

/-- **Theorem 1 (Concise Prose Statement on $S^4$)**:
There exist a positive smooth volume 4-form `V` on `Sphere4` and a $C^\infty$ diffeomorphism
`d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4` preserving `s4Fibration`, preserving `V.Ω` under pullback,
preserving the finite Borel volume measure `V.μ = TauCeti.RoughForm.measure V.Ω.1`, and satisfying
`IsTuringComplete ⇑d_bar`. -/
-- tier: T2
theorem exists_turingComplete_volumePreserving_diffeomorph_S4 :
    ∃ (V : PositiveVolumeForm (𝓡 4) Sphere4)
      (d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4),
      s4Fibration ∘ ⇑d_bar = s4Fibration ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasurePreserving ⇑d_bar V.μ V.μ ∧
      IsTuringComplete ⇑d_bar ∧
      V.μ = TauCeti.RoughForm.measure V.Ω.1 :=
  exists_turingComplete_volumePreserving_diffeomorph_S4_of_isotopy

/-- **Corollary 2 (`S4TCdiffeo-Aug-2026.tex` — General Closed Oriented 4-Manifolds)**:
Every compact Hausdorff smooth 4-manifold `M` admitting a positively co-oriented wrinkled or broken
Lefschetz fibration `[A : AdmitsWrinkledOrBrokenLefschetzFibration M]` carries a positive volume
4-form `V` (`V.μ = TauCeti.RoughForm.measure V.Ω.1`), a compatible generically rank-`2` unimodular
Jacobian–Poisson structure `π_f`, and a smooth, leaf-preserving, area-preserving on regular fibers,
volume-preserving, measure-preserving, Turing complete Poisson diffeomorphism
`d_bar : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M`. -/
-- tier: T2
theorem exists_turingComplete_volumePreserving_poissonDiffeomorph_fourManifold
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [T2Space M] [A : AdmitsWrinkledOrBrokenLefschetzFibration M] :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    letI := A.instMeasurableSpaceFiber
    letI := A.instBorelSpaceFiber
    ∃ (V : PositiveVolumeForm (𝓡 4) M)
      (π_f : PoissonStructure (𝓡 4) M)
      (d_bar : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M),
      π_f = jacobianPoissonOfPositiveVolume V S2VolumeForm A.fibration
        A.fibration.contMDiff_toFun ∧
      π_f.IsUnimodularWithVolume V.Ω ∧
      π_f.IsUnimodularPoisson ∧
      π_f.IsGenericallyRankTwo ∧
      (∀ x ∉ criticalPoints (𝓡 4) (𝓡 2) A.fibration, π_f.rankAt x = 2) ∧
      (∀ x ∈ criticalPoints (𝓡 4) (𝓡 2) A.fibration, π_f.rankAt x = 0) ∧
      ⇑A.fibration ∘ ⇑d_bar = ⇑A.fibration ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_bar d_bar.contMDiff ∧
      (∀ b : A.fibration.baseRegion,
        ∃ d_b : A.Fiber ≃ₘ⟮𝓡 2, 𝓡 2⟯ A.Fiber,
          (∀ z : A.Fiber,
            d_bar (A.fibration.embed (b, z)) = A.fibration.embed (b, d_b z)) ∧
          TauCeti.SmoothForm.mpullback d_b d_b.contMDiff A.fiberVolume.Ω = A.fiberVolume.Ω ∧
          MeasurePreserving ⇑d_b A.fiberVolume.μ A.fiberVolume.μ) ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasurePreserving ⇑d_bar V.μ V.μ ∧
      IsTuringComplete ⇑d_bar ∧
      (⇑d_bar : M → M) ≠ id ∧
      V.μ = TauCeti.RoughForm.measure V.Ω.1 :=
  exists_turingComplete_volumePreserving_poissonDiffeomorph_fourManifold_of_isotopy M

/-- **Algorithmic Undecidability of Forward-Orbit Reachability on $S^4$**:
There exist a smooth leaf-preserving, volume-preserving, measure-preserving Poisson diffeomorphism
`d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4`, a nonempty open target `U : Opens Sphere4`, an open-tube
embedding `openChart : Param × UnitDisk2 → Sphere4`, a continuous injective disk slice
`chart y = openChart (param₀, y)`, initial coordinates `coord : Nat.Partrec.Code → UnitDisk2`, a
`Computable` dyadic rational approximation procedure `approx : Nat.Partrec.Code × ℕ → RatFrac ×
RatFrac` (`≤ 2⁻ᵐ`), and a `Computable` rational-box enumerator `targetBoxes : ℕ → RatBox2`
generating `U` inside `openChart` such that forward-orbit reachability
`∃ n, d_bar^[n] (chart (coord c)) ∈ U` is recursively enumerable (`REPred`) yet algorithmically
undecidable (`¬ ComputablePred`), with no total computable `Bool` decision procedure. -/
-- tier: T2
theorem undecidable_orbit_reachability_S4 :
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
      s4Fibration ∘ ⇑d_bar = s4Fibration ∧
      π_f.IsUnimodularWithVolume V.Ω ∧
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
      V.μ = TauCeti.RoughForm.measure V.Ω.1 :=
  undecidable_orbit_reachability_S4_of_isotopy

section UnconditionalClosedFourManifold

/-- **Corollary 2 (Unconditional Local Coordinate-Ball Realization on Closed Oriented
4-Manifolds, `L-R3` / Track B)**:
Every nonempty compact Hausdorff smooth 4-manifold `M` equipped with a positive volume 4-form
`V_M : PositiveVolumeForm (𝓡 4) M` (with zero `[AdmitsWrinkledOrBrokenLefschetzFibration M]` or
disk-isotopy assumptions) carries an aligned positive volume 4-form `V` strictly positively
co-oriented with `V_M`, a smooth regular-disk map `f : M → Sphere2` (constant outside one oriented
coordinate ball; see `not_isGenericallyRankTwo_closedManifoldLocal` in `ClosedManifoldLocal.lean`),
a compatible globally unimodular Jacobian–Poisson structure `π_f` (rank `2` off `Crit(f)`, rank `0`
on `Crit(f)`), and a $C^\infty$ diffeomorphism `d_bar : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M` preserving `f`, `π_f`,
regular `S²` leaf areas over `s4BaseRegion`, `V.Ω`, and `V.μ` that is Turing complete
(`IsTuringComplete ⇑d_bar`, `≠ id`). -/
-- tier: T2
theorem exists_turingComplete_volumePreserving_poissonDiffeomorph_closedFourManifold
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [T2Space M] [Nonempty M]
    (V_M : PositiveVolumeForm (𝓡 4) M) :
    ∃ (V : PositiveVolumeForm (𝓡 4) M)
      (π_f : PoissonStructure (𝓡 4) M)
      (f : M → Sphere2)
      (hf : ContMDiff (𝓡 4) (𝓡 2) ∞ f)
      (d_bar : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M),
      π_f = jacobianPoissonOfPositiveVolume V S2VolumeForm f hf ∧
      (∀ x : M, ∃ a : ℝ, 0 < a ∧ V.Ω.1 x = a • V_M.Ω.1 x) ∧
      π_f.IsUnimodularWithVolume V.Ω ∧
      π_f.IsUnimodularPoisson ∧
      (∀ x ∉ criticalPoints (𝓡 4) (𝓡 2) f, π_f.rankAt x = 2) ∧
      (∀ x ∈ criticalPoints (𝓡 4) (𝓡 2) f, π_f.rankAt x = 0) ∧
      f ∘ ⇑d_bar = f ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_bar d_bar.contMDiff ∧
      (∀ b : s4BaseRegion,
        ∃ (embed : Sphere2 → M) (d_b : Sphere2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere2),
          (∀ z : Sphere2, f (embed z) = b.1 ∧ d_bar (embed z) = embed (d_b z)) ∧
          TauCeti.SmoothForm.mpullback d_b d_b.contMDiff S2VolumeForm = S2VolumeForm ∧
          MeasurePreserving ⇑d_b S2PositiveVolumeForm.μ S2PositiveVolumeForm.μ) ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasurePreserving ⇑d_bar V.μ V.μ ∧
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
  let C : SymplecticDiskChart Sphere2 S2VolumeForm :=
    AdmitsRegularDiskFibration.fiberDiskChart M
  refine ⟨alignedPositiveVolume M, adaptedJacobianPoisson M,
    ⇑A.fibration, A.fibration.contMDiff_toFun, leafwiseBumpDiffeomorph M,
    rfl,
    fun x ↦ alignedVolumeForm_pos_cooriented M x,
    isUnimodularWithVolume_adaptedJacobianPoisson M,
    isUnimodularPoisson_adaptedJacobianPoisson M,
    fun x hx ↦ rankAt_adaptedJacobianPoisson_of_notMem_criticalPoints M hx,
    fun x hx ↦ rankAt_adaptedJacobianPoisson_of_mem_criticalPoints M hx,
    fibration_comp_leafwiseBumpDiffeomorph M,
    isPoissonMap_leafwiseBumpDiffeomorph M,
    fun b ↦ ?_,
    mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm M,
    measurePreserving_leafwiseBumpDiffeomorph M,
    isTuringComplete_leafwiseBumpDiffeomorph M,
    leafwiseBumpDiffeomorph_ne_id M,
    rfl⟩
  let d_b : Sphere2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere2 :=
    C.liftSliceDiffeomorph (bumpProfile M b.1)
  exact ⟨fun z ↦ A.fibration.embed (b, z), d_b,
    fun z ↦ ⟨A.fibration.apply_embed b z, leafwiseBumpDiffeomorph_embed M b z⟩,
    C.mpullback_liftSliceDiffeomorph_eq (bumpProfile M b.1),
    SymplecticDiskChart.measurePreserving_liftSliceDiffeomorph S2PositiveVolumeForm C
      (bumpProfile M b.1)⟩

/-- Concise unconditional Corollary 2 on every nonempty compact Hausdorff oriented smooth
4-manifold `(M, V_M)` (`L-R3`, with `V.μ = TauCeti.RoughForm.measure V.Ω.1`). -/
-- tier: T2
theorem exists_turingComplete_volumePreserving_diffeomorph_closedFourManifold
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [T2Space M] [Nonempty M]
    (V_M : PositiveVolumeForm (𝓡 4) M) :
    ∃ (V : PositiveVolumeForm (𝓡 4) M)
      (f : M → Sphere2)
      (d_bar : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M),
      (∀ x : M, ∃ a : ℝ, 0 < a ∧ V.Ω.1 x = a • V_M.Ω.1 x) ∧
      f ∘ ⇑d_bar = f ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasurePreserving ⇑d_bar V.μ V.μ ∧
      IsTuringComplete ⇑d_bar ∧
      V.μ = TauCeti.RoughForm.measure V.Ω.1 := by
  obtain ⟨V, _, f, _, d_bar, _, hpos, _, _, _, _, hf_comp, _, _, hV, hμ, htc, _, hμ_eq⟩ :=
    exists_turingComplete_volumePreserving_poissonDiffeomorph_closedFourManifold M V_M
  exact ⟨V, f, d_bar, hpos, hf_comp, hV, hμ, htc, hμ_eq⟩

/-- Unconditional algorithmic undecidability of forward-orbit reachability on any nonempty compact
Hausdorff oriented smooth 4-manifold `(M, V_M)`. -/
-- tier: T2
theorem undecidable_orbit_reachability_closedFourManifold
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [T2Space M] [Nonempty M]
    (V_M : PositiveVolumeForm (𝓡 4) M) :
    ∃ (V : PositiveVolumeForm (𝓡 4) M)
      (π_f : PoissonStructure (𝓡 4) M)
      (d_bar : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M)
      (U : Opens M)
      (Param : Type) (instTopParam : TopologicalSpace Param) (param₀ : Param)
      (openChart : Param × UnitDisk2 → M)
      (chart : UnitDisk2 → M)
      (coord : Nat.Partrec.Code → UnitDisk2)
      (approx : Nat.Partrec.Code × ℕ → RatFrac × RatFrac)
      (targetBoxes : ℕ → RatBox2),
      (∀ x : M, ∃ a : ℝ, 0 < a ∧ V.Ω.1 x = a • V_M.Ω.1 x) ∧
      π_f.IsUnimodularWithVolume V.Ω ∧
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
  obtain ⟨U, Param, instTopParam, param₀, openChart, chart, coord, approx, targetBoxes, hU,
      hopen, hchart_eq, hcont, hinj, hcomp, hbound, hcomp_boxes, hbox_ne, hU_eq, hnot0, hre,
      hnotcomp, hnodec⟩ :=
    undecidable_orbit_reachability_leafwiseBumpDiffeomorph M
  exact ⟨alignedPositiveVolume M, adaptedJacobianPoisson M, leafwiseBumpDiffeomorph M, U, Param,
    instTopParam, param₀, openChart, chart, coord, approx, targetBoxes,
    fun x ↦ alignedVolumeForm_pos_cooriented M x,
    isUnimodularWithVolume_adaptedJacobianPoisson M,
    isPoissonMap_leafwiseBumpDiffeomorph M,
    mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm M,
    measurePreserving_leafwiseBumpDiffeomorph M,
    hU, hopen, hchart_eq, hcont, hinj, hcomp, hbound, hcomp_boxes, hbox_ne, hU_eq, hnot0, hre,
    hnotcomp, hnodec, rfl⟩

end UnconditionalClosedFourManifold

end HeadlineTheorems

/-! ## 4. Direct `[HasCMPPCantorCirculationHamiltonians]` Specializations (Milestone M3.3 Bridge) -/

section CMPPSpecializations

set_option linter.concreteInstances false

variable [C : HasCMPPCantorCirculationHamiltonians]

/-- Specialization of `exists_turingComplete_volumePreserving_poissonDiffeomorph_S4` to
`[HasCMPPCantorCirculationHamiltonians]` via
`instHasTuringCompleteAreaPreservingDiskIsotopyOfCMPP`. -/
-- tier: T2
theorem exists_turingComplete_volumePreserving_poissonDiffeomorph_S4_of_cmpp :
    ∃ (V : PositiveVolumeForm (𝓡 4) Sphere4)
      (π_f : PoissonStructure (𝓡 4) Sphere4)
      (d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4),
      π_f = jacobianPoissonOfPositiveVolume V S2VolumeForm s4Fibration contMDiff_s4Fibration ∧
      π_f.IsUnimodularWithVolume V.Ω ∧
      π_f.IsUnimodularPoisson ∧
      π_f.IsGenericallyRankTwo ∧
      (∀ x ∉ criticalPoints (𝓡 4) (𝓡 2) s4Fibration, π_f.rankAt x = 2) ∧
      (criticalPoints (𝓡 4) (𝓡 2) s4Fibration).Nonempty ∧
      (∀ x ∈ criticalPoints (𝓡 4) (𝓡 2) s4Fibration, π_f.rankAt x = 0) ∧
      s4Fibration ∘ ⇑d_bar = s4Fibration ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_bar d_bar.contMDiff ∧
      (∀ b : s4BaseRegion,
        ∃ d_b : Sphere2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere2,
          (∀ z : Sphere2,
            d_bar (s4RegularDiskFibration.embed (b, z)) = s4RegularDiskFibration.embed (b, d_b z)) ∧
          TauCeti.SmoothForm.mpullback d_b d_b.contMDiff S2VolumeForm = S2VolumeForm ∧
          MeasurePreserving ⇑d_b S2PositiveVolumeForm.μ S2PositiveVolumeForm.μ) ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasurePreserving ⇑d_bar V.μ V.μ ∧
      IsTuringComplete ⇑d_bar ∧
      (⇑d_bar : Sphere4 → Sphere4) ≠ id ∧
      V.μ = TauCeti.RoughForm.measure V.Ω.1 :=
  @exists_turingComplete_volumePreserving_poissonDiffeomorph_S4_of_isotopy
    (@instHasTuringCompleteAreaPreservingDiskIsotopyOfCMPP C)

/-- Specialization of `exists_turingComplete_volumePreserving_diffeomorph_S4` to
`[HasCMPPCantorCirculationHamiltonians]`. -/
-- tier: T2
theorem exists_turingComplete_volumePreserving_diffeomorph_S4_of_cmpp :
    ∃ (V : PositiveVolumeForm (𝓡 4) Sphere4)
      (d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4),
      s4Fibration ∘ ⇑d_bar = s4Fibration ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasurePreserving ⇑d_bar V.μ V.μ ∧
      IsTuringComplete ⇑d_bar ∧
      V.μ = TauCeti.RoughForm.measure V.Ω.1 :=
  @exists_turingComplete_volumePreserving_diffeomorph_S4_of_isotopy
    (@instHasTuringCompleteAreaPreservingDiskIsotopyOfCMPP C)

/-- Specialization of `exists_turingComplete_volumePreserving_poissonDiffeomorph_fourManifold` to
`[HasCMPPCantorCirculationHamiltonians]`. -/
-- tier: T2
theorem exists_turingComplete_volumePreserving_poissonDiffeomorph_fourManifold_of_cmpp
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [T2Space M] [A : AdmitsWrinkledOrBrokenLefschetzFibration M] :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    letI := A.instMeasurableSpaceFiber
    letI := A.instBorelSpaceFiber
    ∃ (V : PositiveVolumeForm (𝓡 4) M)
      (π_f : PoissonStructure (𝓡 4) M)
      (d_bar : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M),
      π_f = jacobianPoissonOfPositiveVolume V S2VolumeForm A.fibration
        A.fibration.contMDiff_toFun ∧
      π_f.IsUnimodularWithVolume V.Ω ∧
      π_f.IsUnimodularPoisson ∧
      π_f.IsGenericallyRankTwo ∧
      (∀ x ∉ criticalPoints (𝓡 4) (𝓡 2) A.fibration, π_f.rankAt x = 2) ∧
      (∀ x ∈ criticalPoints (𝓡 4) (𝓡 2) A.fibration, π_f.rankAt x = 0) ∧
      ⇑A.fibration ∘ ⇑d_bar = ⇑A.fibration ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_bar d_bar.contMDiff ∧
      (∀ b : A.fibration.baseRegion,
        ∃ d_b : A.Fiber ≃ₘ⟮𝓡 2, 𝓡 2⟯ A.Fiber,
          (∀ z : A.Fiber,
            d_bar (A.fibration.embed (b, z)) = A.fibration.embed (b, d_b z)) ∧
          TauCeti.SmoothForm.mpullback d_b d_b.contMDiff A.fiberVolume.Ω = A.fiberVolume.Ω ∧
          MeasurePreserving ⇑d_b A.fiberVolume.μ A.fiberVolume.μ) ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasurePreserving ⇑d_bar V.μ V.μ ∧
      IsTuringComplete ⇑d_bar ∧
      (⇑d_bar : M → M) ≠ id ∧
      V.μ = TauCeti.RoughForm.measure V.Ω.1 :=
  exists_turingComplete_volumePreserving_poissonDiffeomorph_fourManifold_of_isotopy
    (H := @instHasTuringCompleteAreaPreservingDiskIsotopyOfCMPP C) M

/-- Specialization of `undecidable_orbit_reachability_S4` to
`[HasCMPPCantorCirculationHamiltonians]`. -/
-- tier: T2
theorem undecidable_orbit_reachability_S4_of_cmpp :
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
      s4Fibration ∘ ⇑d_bar = s4Fibration ∧
      π_f.IsUnimodularWithVolume V.Ω ∧
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
      V.μ = TauCeti.RoughForm.measure V.Ω.1 :=
  @undecidable_orbit_reachability_S4_of_isotopy
    (@instHasTuringCompleteAreaPreservingDiskIsotopyOfCMPP C)

end CMPPSpecializations

/-! ## 5. `PurelyWrinkledFibration` & `BrokenLefschetzFibration` Corollary 2 Suite (`SC-R2`) -/

section PurelyWrinkledAndBrokenLefschetzCorollary2

/-- **Corollary 2 over Explicit `PurelyWrinkledFibration` (`SC-R2` / Recommendation `(iv)`)**:
Given a compact smooth 4-manifold `(M, V_M)` and any positively co-oriented
`PurelyWrinkledFibration` `P : M → Sphere2` with closed regular surface fiber `(F, V_F)`
(indefinite folds and wrinkled cusps only, zero real Lefschetz points or definite folds; `Lekili
2009`, `Suárez-Serrato–Torres Orozco 2016`),
`AdmitsWrinkledOrBrokenLefschetzFibration.ofPurelyWrinkled` yields an aligned positive volume 4-form
`V` positively co-oriented with `V_M` (`V.μ = TauCeti.RoughForm.measure V.Ω.1`), a compatible
**generically rank-2** (`π_f.IsGenericallyRankTwo`: open and dense rank-`2` locus) unimodular
Jacobian–Poisson structure `π_f` adapted to `P.toFun`, and a $C^\infty$ Turing complete
diffeomorphism `d_bar` preserving `P.toFun`, `π_f`, regular `F` leaf areas, `V.Ω`, and `V.μ`. -/
-- tier: T2
theorem exists_turingComplete_volumePreserving_poissonDiffeomorph_of_purelyWrinkled
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
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
      (d_bar : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M),
      π_f = jacobianPoissonOfPositiveVolume V S2VolumeForm P.toFun P.contMDiff_toFun ∧
      (∀ x : M, ∃ a : ℝ, 0 < a ∧ V.Ω.1 x = a • V_M.Ω.1 x) ∧
      π_f.IsUnimodularWithVolume V.Ω ∧
      π_f.IsUnimodularPoisson ∧
      π_f.IsGenericallyRankTwo ∧
      (∀ x ∉ criticalPoints (𝓡 4) (𝓡 2) P.toFun, π_f.rankAt x = 2) ∧
      (∀ x ∈ criticalPoints (𝓡 4) (𝓡 2) P.toFun, π_f.rankAt x = 0) ∧
      P.toFun ∘ ⇑d_bar = P.toFun ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_bar d_bar.contMDiff ∧
      (∀ b : P.baseRegion,
        ∃ d_b : F ≃ₘ⟮𝓡 2, 𝓡 2⟯ F,
          (∀ z : F,
            d_bar (P.toRegularDiskFibration.embed (b, z)) =
              P.toRegularDiskFibration.embed (b, d_b z)) ∧
          TauCeti.SmoothForm.mpullback d_b d_b.contMDiff V_F.Ω = V_F.Ω ∧
          MeasurePreserving ⇑d_b V_F.μ V_F.μ) ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasurePreserving ⇑d_bar V.μ V.μ ∧
      IsTuringComplete ⇑d_bar ∧
      (⇑d_bar : M → M) ≠ id ∧
      V.μ = TauCeti.RoughForm.measure V.Ω.1 := by
  let A : AdmitsWrinkledOrBrokenLefschetzFibration M :=
    AdmitsWrinkledOrBrokenLefschetzFibration.ofPurelyWrinkled V_M F P V_F hpos
  let _ : AdmitsWrinkledOrBrokenLefschetzFibration M := A
  let C : SymplecticDiskChart F V_F.Ω := AdmitsRegularDiskFibration.fiberDiskChart M
  refine ⟨alignedPositiveVolume M, adaptedJacobianPoisson M, leafwiseBumpDiffeomorph M,
    rfl,
    fun x ↦ alignedVolumeForm_pos_cooriented M x,
    isUnimodularWithVolume_adaptedJacobianPoisson M,
    isUnimodularPoisson_adaptedJacobianPoisson M,
    isGenericallyRankTwo_adaptedJacobianPoisson M,
    fun x hx ↦ rankAt_adaptedJacobianPoisson_of_notMem_criticalPoints M hx,
    fun x hx ↦ rankAt_adaptedJacobianPoisson_of_mem_criticalPoints M hx,
    fibration_comp_leafwiseBumpDiffeomorph M,
    isPoissonMap_leafwiseBumpDiffeomorph M,
    fun b ↦ ?_,
    mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm M,
    measurePreserving_leafwiseBumpDiffeomorph M,
    isTuringComplete_leafwiseBumpDiffeomorph M,
    leafwiseBumpDiffeomorph_ne_id M,
    rfl⟩
  let d_b : F ≃ₘ⟮𝓡 2, 𝓡 2⟯ F := C.liftSliceDiffeomorph (bumpProfile M b.1)
  exact ⟨d_b, fun z ↦ leafwiseBumpDiffeomorph_embed M b z,
    C.mpullback_liftSliceDiffeomorph_eq (bumpProfile M b.1),
    SymplecticDiskChart.measurePreserving_liftSliceDiffeomorph V_F C (bumpProfile M b.1)⟩

/-- Algorithmic undecidability of forward-orbit reachability for any positively co-oriented
`PurelyWrinkledFibration` `P : M → Sphere2` (`SC-R2`, Recommendation `(iv)`). -/
-- tier: T2
theorem undecidable_orbit_reachability_of_purelyWrinkled
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
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
      (d_bar : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M)
      (U : Opens M)
      (Param : Type) (instTopParam : TopologicalSpace Param) (param₀ : Param)
      (openChart : Param × UnitDisk2 → M)
      (chart : UnitDisk2 → M)
      (coord : Nat.Partrec.Code → UnitDisk2)
      (approx : Nat.Partrec.Code × ℕ → RatFrac × RatFrac)
      (targetBoxes : ℕ → RatBox2),
      (∀ x : M, ∃ a : ℝ, 0 < a ∧ V.Ω.1 x = a • V_M.Ω.1 x) ∧
      P.toFun ∘ ⇑d_bar = P.toFun ∧
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
  let A : AdmitsWrinkledOrBrokenLefschetzFibration M :=
    AdmitsWrinkledOrBrokenLefschetzFibration.ofPurelyWrinkled V_M F P V_F hpos
  let _ : AdmitsWrinkledOrBrokenLefschetzFibration M := A
  obtain ⟨U, Param, instTopParam, param₀, openChart, chart, coord, approx, targetBoxes, hU,
      hopen, hchart_eq, hcont, hinj, hcomp, hbound, hcomp_boxes, hbox_ne, hU_eq, hnot0, hre,
      hnotcomp, hnodec⟩ :=
    undecidable_orbit_reachability_leafwiseBumpDiffeomorph M
  exact ⟨alignedPositiveVolume M, adaptedJacobianPoisson M, leafwiseBumpDiffeomorph M, U, Param,
    instTopParam, param₀, openChart, chart, coord, approx, targetBoxes,
    fun x ↦ alignedVolumeForm_pos_cooriented M x,
    fibration_comp_leafwiseBumpDiffeomorph M,
    isUnimodularWithVolume_adaptedJacobianPoisson M,
    isGenericallyRankTwo_adaptedJacobianPoisson M,
    isPoissonMap_leafwiseBumpDiffeomorph M,
    mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm M,
    measurePreserving_leafwiseBumpDiffeomorph M,
    hU, hopen, hchart_eq, hcont, hinj, hcomp, hbound, hcomp_boxes, hbox_ne, hU_eq, hnot0, hre,
    hnotcomp, hnodec, rfl⟩

private noncomputable def restrictPurelyWrinkledTrivialization
    {M F : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [TopologicalSpace F] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F]
    [IsManifold (𝓡 2) ∞ F] [T2Space F] [CompactSpace F] [Nonempty F]
    (B : BrokenLefschetzFibration (𝓡 4) M (𝓡 2) Sphere2 F)
    (P₀ : PurelyWrinkledFibration (𝓡 4) M (𝓡 2) Sphere2 F)
    (hsub : (P₀.baseRegion : Set Sphere2) ⊆ B.baseRegion.1)
    (hB_to_P₀ : ∀ x : M, B.toFun x ∈ (P₀.baseRegion : Set Sphere2) →
      P₀.toFun x ∈ (P₀.baseRegion : Set Sphere2))
    (hP₀_val : ∀ x ∈ P₀.toFun ⁻¹' P₀.baseRegion.1, P₀.toFun x = B.toFun x) :
    P₀.toRegularDiskFibration.preimageOpen ≃ₘ⟮𝓡 4, (𝓡 2).prod (𝓡 2)⟯ (P₀.baseRegion × F) :=
  let U_P : Opens M := P₀.toRegularDiskFibration.preimageOpen
  let U_B : Opens M := B.toRegularDiskFibration.preimageOpen
  let incl_M : U_P → U_B := fun u ↦
    ⟨u.1, by
      have hmem : B.toFun u.1 ∈ (P₀.baseRegion : Set Sphere2) := by
        have hu : P₀.toFun u.1 ∈ (P₀.baseRegion : Set Sphere2) := u.2
        rwa [← hP₀_val u.1 u.2]
      exact hsub hmem⟩
  let incl_B : P₀.baseRegion → B.baseRegion := fun b ↦ ⟨b.1, hsub b.2⟩
  let trivInv : P₀.baseRegion × F → U_P := fun bz ↦
    ⟨(B.trivialization.symm (incl_B bz.1, bz.2)).1, by
      let w := B.trivialization.symm (incl_B bz.1, bz.2)
      have hfst := congrArg Subtype.val (B.trivialization_fst w)
      rw [B.trivialization.apply_symm_apply] at hfst
      have hfst' : bz.1.1 = B.toFun w.1 := hfst
      have hmem_B : B.toFun w.1 ∈ (P₀.baseRegion : Set Sphere2) := by
        rw [← hfst']
        exact bz.1.2
      exact hB_to_P₀ w.1 hmem_B⟩
  { toFun := fun u ↦ (⟨P₀.toFun u.1, u.2⟩, (B.trivialization (incl_M u)).2)
    invFun := trivInv
    left_inv := fun u ↦ by
      apply Subtype.ext
      have hfst_eq : incl_B ⟨P₀.toFun u.1, u.2⟩ = (B.trivialization (incl_M u)).1 := by
        apply Subtype.ext
        have h1 := congrArg Subtype.val (B.trivialization_fst (incl_M u))
        exact (hP₀_val u.1 u.2).trans h1.symm
      change (B.trivialization.symm
        (incl_B ⟨P₀.toFun u.1, u.2⟩, (B.trivialization (incl_M u)).2)).1 = u.1
      rw [hfst_eq, Prod.mk.eta, B.trivialization.symm_apply_apply]
    right_inv := fun bz ↦ by
      let w := B.trivialization.symm (incl_B bz.1, bz.2)
      have hw : incl_M (trivInv bz) = w := Subtype.ext rfl
      apply Prod.ext
      · apply Subtype.ext
        have h1 : P₀.toFun (trivInv bz).1 = B.toFun w.1 := hP₀_val _ (trivInv bz).2
        have h2 := congrArg Subtype.val (B.trivialization_fst w)
        rw [B.trivialization.apply_symm_apply] at h2
        exact h1.trans h2.symm
      · change (B.trivialization (incl_M (trivInv bz))).2 = bz.2
        rw [hw, B.trivialization.apply_symm_apply]
    contMDiff_toFun := by
      have hincl_M : ContMDiff (𝓡 4) (𝓡 4) ∞ incl_M :=
        (TauCeti.ContMDiff.subtypeVal_comp_iff U_B incl_M).mp contMDiff_subtype_val
      refine ContMDiff.prodMk ?_ ?_
      · exact (TauCeti.ContMDiff.subtypeVal_comp_iff P₀.baseRegion _).mp
          (P₀.contMDiff_toFun.comp contMDiff_subtype_val)
      · exact contMDiff_snd.comp (B.trivialization.contMDiff.comp hincl_M)
    contMDiff_invFun := by
      have hincl_B : ContMDiff (𝓡 2) (𝓡 2) ∞ incl_B :=
        (TauCeti.ContMDiff.subtypeVal_comp_iff B.baseRegion incl_B).mp contMDiff_subtype_val
      refine (TauCeti.ContMDiff.subtypeVal_comp_iff U_P trivInv).mp ?_
      change ContMDiff ((𝓡 2).prod (𝓡 2)) (𝓡 4) ∞
        (Subtype.val ∘ ⇑B.trivialization.symm ∘ fun bz : P₀.baseRegion × F ↦
          (incl_B bz.1, bz.2))
      exact contMDiff_subtype_val.comp
        (B.trivialization.symm.contMDiff.comp
          ((hincl_B.comp contMDiff_fst).prodMk contMDiff_snd)) }

private theorem restrictPurelyWrinkledTrivialization_apply
    {M F : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [TopologicalSpace F] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F]
    [IsManifold (𝓡 2) ∞ F] [T2Space F] [CompactSpace F] [Nonempty F]
    (B : BrokenLefschetzFibration (𝓡 4) M (𝓡 2) Sphere2 F)
    (P₀ : PurelyWrinkledFibration (𝓡 4) M (𝓡 2) Sphere2 F)
    (hsub : (P₀.baseRegion : Set Sphere2) ⊆ B.baseRegion.1)
    (hB_to_P₀ : ∀ x : M, B.toFun x ∈ (P₀.baseRegion : Set Sphere2) →
      P₀.toFun x ∈ (P₀.baseRegion : Set Sphere2))
    (hP₀_val : ∀ x ∈ P₀.toFun ⁻¹' P₀.baseRegion.1, P₀.toFun x = B.toFun x)
    (u : P₀.toRegularDiskFibration.preimageOpen)
    (hu_B : u.1 ∈ B.toRegularDiskFibration.preimageOpen) :
    restrictPurelyWrinkledTrivialization B P₀ hsub hB_to_P₀ hP₀_val u =
      (⟨P₀.toFun u.1, u.2⟩, (B.trivialization ⟨u.1, hu_B⟩).2) :=
  rfl

private noncomputable def replacePurelyWrinkledTrivialization
    {M F : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [TopologicalSpace F] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F]
    [IsManifold (𝓡 2) ∞ F] [T2Space F] [CompactSpace F] [Nonempty F]
    (B : BrokenLefschetzFibration (𝓡 4) M (𝓡 2) Sphere2 F)
    (P₀ : PurelyWrinkledFibration (𝓡 4) M (𝓡 2) Sphere2 F)
    (hsub : (P₀.baseRegion : Set Sphere2) ⊆ B.baseRegion.1)
    (hB_to_P₀ : ∀ x : M, B.toFun x ∈ (P₀.baseRegion : Set Sphere2) →
      P₀.toFun x ∈ (P₀.baseRegion : Set Sphere2))
    (hP₀_val : ∀ x ∈ P₀.toFun ⁻¹' P₀.baseRegion.1, P₀.toFun x = B.toFun x) :
    PurelyWrinkledFibration (𝓡 4) M (𝓡 2) Sphere2 F where
  toRegularDiskFibration :=
    { toFun := P₀.toFun
      contMDiff_toFun := P₀.contMDiff_toFun
      baseRegion := P₀.baseRegion
      baseRegion_nonempty := P₀.baseRegion_nonempty
      regular_on_preimage := P₀.regular_on_preimage
      baseDiskRadius := P₀.baseDiskRadius
      baseDiskRadius_pos := P₀.baseDiskRadius_pos
      baseDisk := P₀.baseDisk
      trivialization := restrictPurelyWrinkledTrivialization B P₀ hsub hB_to_P₀ hP₀_val
      trivialization_fst := fun u ↦ by
        have hu_B : u.1 ∈ B.toRegularDiskFibration.preimageOpen := by
          change B.toFun u.1 ∈ (B.baseRegion : Set Sphere2)
          refine hsub ?_
          have hu : P₀.toFun u.1 ∈ (P₀.baseRegion : Set Sphere2) := u.2
          rwa [← hP₀_val u.1 u.2]
        rw [restrictPurelyWrinkledTrivialization_apply B P₀ hsub hB_to_P₀ hP₀_val u hu_B] }
  singularities_purely_wrinkled := P₀.singularities_purely_wrinkled

private theorem mpullback_incl_productWedge
    {F : Type*} [TopologicalSpace F] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F]
    [IsManifold (𝓡 2) ∞ F] [MeasurableSpace F] [BorelSpace F]
    (V_F : PositiveVolumeForm (𝓡 2) F) {R_P R_B : Opens Sphere2}
    (incl_B : R_P → R_B) (hincl_B : ContMDiff (𝓡 2) (𝓡 2) ∞ incl_B)
    (hcompB : (Subtype.val : R_B → Sphere2) ∘ incl_B = Subtype.val) :
    TauCeti.mpullback ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2))
        (fun bz : R_P × F ↦ (incl_B bz.1, bz.2))
        (TauCeti.SmoothForm.wedge
          (TauCeti.SmoothForm.mpullback (Prod.snd : R_B × F → F) contMDiff_snd V_F.Ω)
          (TauCeti.SmoothForm.mpullback (Subtype.val ∘ (Prod.fst : R_B × F → R_B))
            (contMDiff_subtype_val.comp contMDiff_fst) S2VolumeForm)).1 =
      (TauCeti.SmoothForm.wedge
        (TauCeti.SmoothForm.mpullback (Prod.snd : R_P × F → F) contMDiff_snd V_F.Ω)
        (TauCeti.SmoothForm.mpullback (Subtype.val ∘ (Prod.fst : R_P × F → R_P))
          (contMDiff_subtype_val.comp contMDiff_fst) S2VolumeForm)).1 := by
  have hincl_prod : MDifferentiable ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2))
      (fun bz : R_P × F ↦ (incl_B bz.1, bz.2)) :=
    ((hincl_B.comp contMDiff_fst).prodMk contMDiff_snd).mdifferentiable (by simp)
  have hsub_fst : MDifferentiable ((𝓡 2).prod (𝓡 2)) (𝓡 2)
      (Subtype.val ∘ (Prod.fst : R_B × F → R_B)) :=
    ((contMDiff_subtype_val (n := ∞)).comp contMDiff_fst).mdifferentiable (by simp)
  have hcomp2 :
      (Subtype.val ∘ (Prod.fst : R_B × F → R_B)) ∘ (fun bz : R_P × F ↦ (incl_B bz.1, bz.2)) =
        Subtype.val ∘ (Prod.fst : R_P × F → R_P) :=
    funext fun bz ↦ congrFun hcompB bz.1
  have h1 :
      TauCeti.mpullback ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2))
        (fun bz : R_P × F ↦ (incl_B bz.1, bz.2))
        (TauCeti.SmoothForm.mpullback (Prod.snd : R_B × F → F) contMDiff_snd V_F.Ω).1 =
      (TauCeti.SmoothForm.mpullback (Prod.snd : R_P × F → F) contMDiff_snd V_F.Ω).1 := by
    rw [TauCeti.SmoothForm.coe_mpullback, TauCeti.SmoothForm.coe_mpullback,
      ← TauCeti.mpullback_comp hincl_prod mdifferentiable_snd]
    rfl
  have h2 :
      TauCeti.mpullback ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2))
        (fun bz : R_P × F ↦ (incl_B bz.1, bz.2))
        (TauCeti.SmoothForm.mpullback (Subtype.val ∘ (Prod.fst : R_B × F → R_B))
          (contMDiff_subtype_val.comp contMDiff_fst) S2VolumeForm).1 =
      (TauCeti.SmoothForm.mpullback (Subtype.val ∘ (Prod.fst : R_P × F → R_P))
        (contMDiff_subtype_val.comp contMDiff_fst) S2VolumeForm).1 := by
    rw [TauCeti.SmoothForm.coe_mpullback, TauCeti.SmoothForm.coe_mpullback,
      ← TauCeti.mpullback_comp hincl_prod hsub_fst, hcomp2]
  exact (congrArg (TauCeti.mpullback ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2))
        (fun bz : R_P × F ↦ (incl_B bz.1, bz.2)))
      (TauCeti.SmoothForm.coe_wedge _ _)).trans
    ((TauCeti.mpullback_wedge _ _ _).trans
      ((congrArg₂ TauCeti.RoughForm.wedge h1 h2).trans
        (TauCeti.SmoothForm.coe_wedge _ _).symm))

private theorem mpullback_triv_eq_of_comm
    {M F : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [TopologicalSpace F] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F]
    [IsManifold (𝓡 2) ∞ F]
    (V_M : PositiveVolumeForm (𝓡 4) M) {U_P U_B : Opens M} {R_P R_B : Opens Sphere2}
    (incl_M : U_P → U_B) (hincl_M : ContMDiff (𝓡 4) (𝓡 4) ∞ incl_M)
    (hcompM : (Subtype.val : U_B → M) ∘ incl_M = Subtype.val)
    (incl_B : R_P → R_B) (hincl_B : ContMDiff (𝓡 2) (𝓡 2) ∞ incl_B)
    (Φ_B : U_B ≃ₘ⟮𝓡 4, (𝓡 2).prod (𝓡 2)⟯ (R_B × F))
    (Φ_P : U_P ≃ₘ⟮𝓡 4, (𝓡 2).prod (𝓡 2)⟯ (R_P × F))
    (ω_B : TauCeti.SmoothForm ((𝓡 2).prod (𝓡 2)) (R_B × F) ℝ 4)
    (ω_P : TauCeti.SmoothForm ((𝓡 2).prod (𝓡 2)) (R_P × F) ℝ 4)
    (hω : TauCeti.mpullback ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2))
        (fun bz : R_P × F ↦ (incl_B bz.1, bz.2)) ω_B.1 = ω_P.1)
    (hcomm : (fun bz : R_P × F ↦ (incl_B bz.1, bz.2)) ∘ ⇑Φ_P = ⇑Φ_B ∘ incl_M)
    (u : U_P) (c : ℝ)
    (hc_eq : (TauCeti.SmoothForm.mpullback Φ_B Φ_B.contMDiff ω_B).1 (incl_M u) =
      c • (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val V_M.Ω).1 (incl_M u)) :
    (TauCeti.SmoothForm.mpullback Φ_P Φ_P.contMDiff ω_P).1 u =
      c • (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val V_M.Ω).1 u := by
  have hω' :
      TauCeti.SmoothForm.mpullback (fun bz : R_P × F ↦ (incl_B bz.1, bz.2))
        ((hincl_B.comp contMDiff_fst).prodMk contMDiff_snd) ω_B = ω_P :=
    Subtype.ext ((TauCeti.SmoothForm.coe_mpullback _ _ _).trans hω)
  have htriv_pull :
      TauCeti.SmoothForm.mpullback Φ_P Φ_P.contMDiff ω_P =
      TauCeti.SmoothForm.mpullback incl_M hincl_M
        (TauCeti.SmoothForm.mpullback Φ_B Φ_B.contMDiff ω_B) := by
    rw [← hω', TauCeti.SmoothForm.mpullback_mpullback,
      TauCeti.SmoothForm.mpullback_mpullback]
    apply Subtype.ext
    rw [TauCeti.SmoothForm.coe_mpullback, TauCeti.SmoothForm.coe_mpullback, hcomm]
  have hM_pull :
      TauCeti.SmoothForm.mpullback (Subtype.val : U_P → M) contMDiff_subtype_val V_M.Ω =
      TauCeti.SmoothForm.mpullback incl_M hincl_M
        (TauCeti.SmoothForm.mpullback (Subtype.val : U_B → M) contMDiff_subtype_val V_M.Ω) := by
    apply Subtype.ext
    rw [TauCeti.SmoothForm.mpullback_mpullback, TauCeti.SmoothForm.coe_mpullback,
      TauCeti.SmoothForm.coe_mpullback, hcompM]
  rw [htriv_pull, hM_pull]
  ext v
  rw [TauCeti.SmoothForm.mpullback_apply, hc_eq, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.smul_apply, ← TauCeti.SmoothForm.mpullback_apply]

/-- **Positively Co-Oriented Broken-to-Purely-Wrinkled Deformation (`Lekili 2009`, §3.1 & §4)**:
Deforms any positively co-oriented `BrokenLefschetzFibration` `B : M → Sphere2` via
`BrokenLefschetzFibration.exists_purelyWrinkledFibration` into a `PurelyWrinkledFibration`
`P : M → Sphere2` connected to `B.toFun` by a jointly $C^\infty$ global homotopy `H` supported
inside a compact set `K` disjoint from `B.toFun ⁻¹' closure P.baseRegion.1` and from all
non-Lefschetz critical points of `B`, while transporting positive co-orientation `hpos` from
`B.trivialization` to `P.trivialization` over `P.baseRegion ⊆ B.baseRegion`. -/
-- tier: T2
theorem exists_pos_cooriented_purelyWrinkledFibration_of_brokenLefschetz
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
      (K : Set M) (H : ℝ → M → Sphere2),
      P.baseDiskRadius = B.baseDiskRadius / 2 ∧
      P.baseRegion.1 ⊆ B.baseRegion.1 ∧
      IsCompact K ∧
      Disjoint K (B.toFun ⁻¹' closure (P.baseRegion : Set Sphere2)) ∧
      (∀ p ∈ criticalPoints (𝓡 4) (𝓡 2) B.toFun,
        ¬ IsRealLefschetzAt (𝓡 4) (𝓡 2) B.toFun p → p ∉ K) ∧
      (∀ x ∉ K, P.toFun x = B.toFun x) ∧
      (∀ x ∈ P.toFun ⁻¹' P.baseRegion.1, P.toFun x = B.toFun x) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 4)) (𝓡 2) ∞ (Function.uncurry H) ∧
      (∀ x, H 0 x = B.toFun x) ∧
      (∀ x, H 1 x = P.toFun x) ∧
      (∀ (t : ℝ), ∀ x ∉ K, H t x = B.toFun x) ∧
      ∀ u : P.toRegularDiskFibration.preimageOpen, ∃ c : ℝ, 0 < c ∧
        (TauCeti.SmoothForm.mpullback P.trivialization P.trivialization.contMDiff
            (TauCeti.SmoothForm.wedge
              (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd V_F.Ω)
              (TauCeti.SmoothForm.mpullback (Subtype.val ∘ Prod.fst)
                (contMDiff_subtype_val.comp contMDiff_fst) S2VolumeForm))).1 u =
          c • (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val V_M.Ω).1 u :=
  B.exists_purelyWrinkledFibration.elim fun P₀ h1 ↦
    h1.elim fun K h2 ↦
      h2.elim fun H hS ↦
        have hB_to_P₀ : ∀ x : M, B.toFun x ∈ (P₀.baseRegion : Set Sphere2) →
            P₀.toFun x ∈ (P₀.baseRegion : Set Sphere2) := fun x hx ↦ by
          have hx_cl : x ∈ B.toFun ⁻¹' closure (P₀.baseRegion : Set Sphere2) := subset_closure hx
          have hx_notK : x ∉ K := Set.disjoint_right.mp hS.2.2.2.1 hx_cl
          rwa [hS.2.2.2.2.2.1 x hx_notK]
        have hu_mem (q : P₀.toRegularDiskFibration.preimageOpen) :
            q.1 ∈ B.toRegularDiskFibration.preimageOpen := by
          change B.toFun q.1 ∈ (B.baseRegion : Set Sphere2)
          refine hS.2.1 ?_
          have hq : P₀.toFun q.1 ∈ (P₀.baseRegion : Set Sphere2) := q.2
          rwa [← hS.2.2.2.2.2.2.1 q.1 q.2]
        have hincl_M : ContMDiff (𝓡 4) (𝓡 4) ∞
            (fun q : P₀.toRegularDiskFibration.preimageOpen ↦
              (⟨q.1, hu_mem q⟩ : B.toRegularDiskFibration.preimageOpen)) :=
          (TauCeti.ContMDiff.subtypeVal_comp_iff B.toRegularDiskFibration.preimageOpen _).mp
            contMDiff_subtype_val
        have hincl_B : ContMDiff (𝓡 2) (𝓡 2) ∞
            (fun b : P₀.baseRegion ↦ (⟨b.1, hS.2.1 b.2⟩ : B.baseRegion)) :=
          (TauCeti.ContMDiff.subtypeVal_comp_iff B.baseRegion _).mp contMDiff_subtype_val
        have hcomm :
            ((fun bz : P₀.baseRegion × F ↦ ((⟨bz.1.1, hS.2.1 bz.1.2⟩ : B.baseRegion), bz.2)) ∘
              ⇑(restrictPurelyWrinkledTrivialization B P₀ hS.2.1 hB_to_P₀ hS.2.2.2.2.2.2.1)) =
            (⇑B.trivialization ∘ fun q : P₀.toRegularDiskFibration.preimageOpen ↦
              (⟨q.1, hu_mem q⟩ : B.toRegularDiskFibration.preimageOpen)) := by
          funext q
          rw [Function.comp_apply, Function.comp_apply,
            restrictPurelyWrinkledTrivialization_apply B P₀ hS.2.1 hB_to_P₀ hS.2.2.2.2.2.2.1 q
              (hu_mem q)]
          refine Prod.ext (Subtype.ext ?_) rfl
          have h1' := congrArg Subtype.val (B.trivialization_fst ⟨q.1, hu_mem q⟩)
          exact (hS.2.2.2.2.2.2.1 q.1 q.2).trans h1'.symm
        ⟨replacePurelyWrinkledTrivialization B P₀ hS.2.1 hB_to_P₀ hS.2.2.2.2.2.2.1,
          K, H, hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1, hS.2.2.2.2.1,
          hS.2.2.2.2.2.1, hS.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.1,
          hS.2.2.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.2.2.2,
          fun u ↦ (hpos ⟨u.1, hu_mem u⟩).elim fun c hc ↦
            ⟨c, hc.1, mpullback_triv_eq_of_comm V_M _ hincl_M rfl _ hincl_B
              B.trivialization
              (restrictPurelyWrinkledTrivialization B P₀ hS.2.1 hB_to_P₀ hS.2.2.2.2.2.2.1)
              _ _ (mpullback_incl_productWedge V_F _ hincl_B rfl)
              hcomm u c hc.2⟩⟩

/-- **Corollary 2 over `BrokenLefschetzFibration` via Lekili Deformation (`SC-R2` / Rec `(iv)`)**:
Given a compact Hausdorff smooth 4-manifold `(M, V_M)` and a positively co-oriented
`BrokenLefschetzFibration` `B : M → Sphere2` (`Auroux–Donaldson–Katzarkov` / `Gay–Kirby`), Lekili's
Move 1 wrinkling deformation (`BrokenLefschetzFibration.exists_purelyWrinkledFibration`) produces a
`PurelyWrinkledFibration` `P : M → Sphere2`, a compact surgery support `K ⊆ M`, and a jointly
$C^\infty$ global homotopy `H : ℝ → M → Sphere2` (`H 0 = B.toFun`, `H 1 = P.toFun`, stationary
outside `K`), together with an aligned positive volume 4-form `V`
(`V.μ = TauCeti.RoughForm.measure V.Ω.1`), a compatible **generically rank-2**
(`π_f.IsGenericallyRankTwo`) unimodular Jacobian–Poisson structure `π_f` adapted to `P.toFun`, and
a $C^\infty$ Turing complete Poisson diffeomorphism `d_bar` preserving `P.toFun`, `π_f`, regular
`F` leaf areas, `V.Ω`, and `V.μ`. -/
-- tier: T2
theorem exists_turingComplete_volumePreserving_poissonDiffeomorph_of_brokenLefschetz
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
      (d_bar : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M),
      P.baseDiskRadius = B.baseDiskRadius / 2 ∧
      P.baseRegion.1 ⊆ B.baseRegion.1 ∧
      IsCompact K ∧
      Disjoint K (B.toFun ⁻¹' closure (P.baseRegion : Set Sphere2)) ∧
      (∀ p ∈ criticalPoints (𝓡 4) (𝓡 2) B.toFun,
        ¬ IsRealLefschetzAt (𝓡 4) (𝓡 2) B.toFun p → p ∉ K) ∧
      (∀ x ∉ K, P.toFun x = B.toFun x) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 4)) (𝓡 2) ∞ (Function.uncurry H) ∧
      (∀ x, H 0 x = B.toFun x) ∧
      (∀ x, H 1 x = P.toFun x) ∧
      (∀ (t : ℝ), ∀ x ∉ K, H t x = B.toFun x) ∧
      π_f = jacobianPoissonOfPositiveVolume V S2VolumeForm P.toFun P.contMDiff_toFun ∧
      (∀ x : M, ∃ a : ℝ, 0 < a ∧ V.Ω.1 x = a • V_M.Ω.1 x) ∧
      π_f.IsUnimodularWithVolume V.Ω ∧
      π_f.IsUnimodularPoisson ∧
      π_f.IsGenericallyRankTwo ∧
      (∀ x ∉ criticalPoints (𝓡 4) (𝓡 2) P.toFun, π_f.rankAt x = 2) ∧
      (∀ x ∈ criticalPoints (𝓡 4) (𝓡 2) P.toFun, π_f.rankAt x = 0) ∧
      P.toFun ∘ ⇑d_bar = P.toFun ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_bar d_bar.contMDiff ∧
      (∀ b : P.baseRegion,
        ∃ d_b : F ≃ₘ⟮𝓡 2, 𝓡 2⟯ F,
          (∀ z : F,
            d_bar (P.toRegularDiskFibration.embed (b, z)) =
              P.toRegularDiskFibration.embed (b, d_b z)) ∧
          TauCeti.SmoothForm.mpullback d_b d_b.contMDiff V_F.Ω = V_F.Ω ∧
          MeasurePreserving ⇑d_b V_F.μ V_F.μ) ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasurePreserving ⇑d_bar V.μ V.μ ∧
      IsTuringComplete ⇑d_bar ∧
      (⇑d_bar : M → M) ≠ id ∧
      V.μ = TauCeti.RoughForm.measure V.Ω.1 := by
  obtain ⟨P, K, H, hrad, hsub, hK_comp, hK_disj, hK_crit, hP_out, _,
      hH_md, hH_0, hH_1, hH_stat, hpos_P⟩ :=
    exists_pos_cooriented_purelyWrinkledFibration_of_brokenLefschetz M V_M F B V_F hpos
  obtain ⟨V, π_f, d_bar, hπ, hpos_V, hunimV, hunim, hgen, hr2, hr0, hfib, hpoiss, hleaf,
      hvol, hmp, htc, hne, hμ_eq⟩ :=
    exists_turingComplete_volumePreserving_poissonDiffeomorph_of_purelyWrinkled M V_M F P V_F
      hpos_P
  exact ⟨P, K, H, V, π_f, d_bar, hrad, hsub, hK_comp, hK_disj, hK_crit, hP_out,
    hH_md, hH_0, hH_1, hH_stat, hπ, hpos_V, hunimV, hunim, hgen, hr2, hr0, hfib, hpoiss, hleaf,
    hvol, hmp, htc, hne, hμ_eq⟩

/-- Algorithmic undecidability of forward-orbit reachability for any positively co-oriented
`BrokenLefschetzFibration` `B : M → Sphere2` via Lekili Move 1 deformation to `P` (`SC-R2`). -/
-- tier: T2
theorem undecidable_orbit_reachability_of_brokenLefschetz
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
      (d_bar : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M)
      (U : Opens M)
      (Param : Type) (instTopParam : TopologicalSpace Param) (param₀ : Param)
      (openChart : Param × UnitDisk2 → M)
      (chart : UnitDisk2 → M)
      (coord : Nat.Partrec.Code → UnitDisk2)
      (approx : Nat.Partrec.Code × ℕ → RatFrac × RatFrac)
      (targetBoxes : ℕ → RatBox2),
      IsCompact K ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 4)) (𝓡 2) ∞ (Function.uncurry H) ∧
      (∀ x, H 0 x = B.toFun x) ∧
      (∀ x, H 1 x = P.toFun x) ∧
      (∀ (t : ℝ), ∀ x ∉ K, H t x = B.toFun x) ∧
      P.toFun ∘ ⇑d_bar = P.toFun ∧
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
  obtain ⟨P, K, H, _, _, hK_comp, _, _, _, _, hH_md, hH_0, hH_1, hH_stat, hpos_P⟩ :=
    exists_pos_cooriented_purelyWrinkledFibration_of_brokenLefschetz M V_M F B V_F hpos
  obtain ⟨V, π_f, d_bar, U, Param, instTopParam, param₀, openChart, chart, coord, approx,
      targetBoxes, _, hfib, hunimV, hgen, hpoiss, hvol, hmp, hU, hopen, hchart_eq, hcont, hinj,
      hcomp, hbound, hcomp_boxes, hbox_ne, hU_eq, hnot0, hre, hnotcomp, hnodec, hμ_eq⟩ :=
    undecidable_orbit_reachability_of_purelyWrinkled M V_M F P V_F hpos_P
  exact ⟨P, K, H, V, π_f, d_bar, U, Param, instTopParam, param₀, openChart, chart, coord,
    approx, targetBoxes, hK_comp, hH_md, hH_0, hH_1, hH_stat, hfib, hunimV, hgen, hpoiss,
    hvol, hmp, hU, hopen, hchart_eq, hcont, hinj, hcomp, hbound, hcomp_boxes, hbox_ne, hU_eq,
    hnot0, hre, hnotcomp, hnodec, hμ_eq⟩

end PurelyWrinkledAndBrokenLefschetzCorollary2

/-! ## 6. Exact-Volume Moser Conjugation Suite (`SC-R3`, Zero `ConnectedSpace` Assumption) -/

section ExactMoserVolumeTheorems

/-- **Literal Unconditional Corollary 2 with Exact `V_M` Preservation (`SC-R3`, Full Poisson
Bundle)**:
Every nonempty compact Hausdorff smooth 4-manifold `M` equipped with **any** positive volume
4-form `V_M : PositiveVolumeForm (𝓡 4) M` (requiring **zero** `[ConnectedSpace M]` assumption and
**zero** fibration typeclasses!) carries a smooth map `f : M → Sphere2` (constant outside one
coordinate domain), a compatible Poisson structure `π_f` globally unimodular with respect to
**`V_M.Ω` itself** (`π_f.IsUnimodularWithVolume V_M.Ω`), and a $C^\infty$ diffeomorphism
`d_exact : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M` preserving `f`, preserving `π_f` (`IsPoissonMap`), preserving the
**exact input volume 4-form `V_M.Ω` and Borel measure `V_M.μ`** (`d_exact^* V_M.Ω = V_M.Ω`,
`MeasurePreserving ⇑d_exact V_M.μ V_M.μ`), and satisfying `IsTuringComplete ⇑d_exact` (`≠ id`). -/
-- tier: T2
theorem exists_turingComplete_exactVolumePreserving_poissonDiffeomorph_closedFourManifold
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [T2Space M] [Nonempty M]
    (V_M : PositiveVolumeForm (𝓡 4) M) :
    ∃ (π_f : PoissonStructure (𝓡 4) M)
      (f : M → Sphere2)
      (d_exact : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M),
      ContMDiff (𝓡 4) (𝓡 2) ∞ f ∧
      π_f.IsUnimodularWithVolume V_M.Ω ∧
      π_f.IsUnimodularPoisson ∧
      (∀ x ∉ criticalPoints (𝓡 4) (𝓡 2) f, π_f.rankAt x = 2) ∧
      (∀ x ∈ criticalPoints (𝓡 4) (𝓡 2) f, π_f.rankAt x = 0) ∧
      f ∘ ⇑d_exact = f ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_exact d_exact.contMDiff ∧
      TauCeti.SmoothForm.mpullback d_exact d_exact.contMDiff V_M.Ω = V_M.Ω ∧
      MeasurePreserving ⇑d_exact V_M.μ V_M.μ ∧
      IsTuringComplete ⇑d_exact ∧
      (⇑d_exact : M → M) ≠ id := by
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
  let W : MoserVolume V_M (alignedPositiveVolume M) :=
    MoserVolume.ofPositivelyCooriented V_M (alignedPositiveVolume M)
      (fun x ↦ alignedVolumeForm_pos_cooriented M x)
  let f₀ : M → Sphere2 := ⇑A.fibration
  have hf₀ : ContMDiff (𝓡 4) (𝓡 2) ∞ f₀ := A.fibration.contMDiff_toFun
  let d_bar : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M := leafwiseBumpDiffeomorph M
  exact ⟨W.pullbackJacobianPoisson f₀ hf₀, f₀ ∘ ⇑W.ψ, W.conjDiffeomorph d_bar,
    hf₀.comp W.ψ.contMDiff,
    W.isUnimodularWithVolume_pullbackJacobianPoisson f₀ hf₀,
    W.isUnimodularPoisson_pullbackJacobianPoisson f₀ hf₀,
    fun x hx ↦ W.rankAt_pullbackJacobianPoisson_of_notMem_criticalPoints f₀ hf₀ hx,
    fun x hx ↦ W.rankAt_pullbackJacobianPoisson_of_mem_criticalPoints f₀ hf₀ hx,
    W.fibration_comp_conjDiffeomorph (fibration_comp_leafwiseBumpDiffeomorph M),
    W.isPoissonMap_conjDiffeomorph f₀ hf₀ (isPoissonMap_leafwiseBumpDiffeomorph M),
    W.mpullback_conjDiffeomorph (connectedComponent_leafwiseBumpDiffeomorph M)
      (mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm M),
    W.measurePreserving_conjDiffeomorph (connectedComponent_leafwiseBumpDiffeomorph M)
      (mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm M),
    W.isTuringComplete_conjDiffeomorph (isTuringComplete_leafwiseBumpDiffeomorph M),
    W.conjDiffeomorph_ne_id (isTuringComplete_leafwiseBumpDiffeomorph M)⟩

/-- **Literal Unconditional Corollary 2 (`S4TCdiffeo-Aug-2026.tex`, `SC-R3`, Concise Exact-Volume
Statement)**:
On any nonempty compact Hausdorff smooth 4-manifold `M` equipped with **any** positive smooth
volume 4-form `V_M : PositiveVolumeForm (𝓡 4) M` (requiring **zero** `[ConnectedSpace M]`
assumption!), componentwise Moser conjugation (`Moser 1965` + `TauCeti` top-degree de Rham
cohomology) produces a smooth map `f : M → Sphere2`, a Poisson structure `π_f` unimodular with
respect to `V_M.Ω`, and a $C^\infty$ diffeomorphism `d_exact : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M` preserving `f`,
`π_f`, **`V_M.Ω` itself**, and **`V_M.μ` itself** that is Turing complete (`IsTuringComplete
⇑d_exact`, `≠ id`). -/
-- tier: T2
theorem exists_turingComplete_exactVolumePreserving_diffeomorph_closedFourManifold
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [T2Space M] [Nonempty M]
    (V_M : PositiveVolumeForm (𝓡 4) M) :
    ∃ (π_f : PoissonStructure (𝓡 4) M)
      (f : M → Sphere2)
      (d_exact : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M),
      π_f.IsUnimodularWithVolume V_M.Ω ∧
      f ∘ ⇑d_exact = f ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_exact d_exact.contMDiff ∧
      TauCeti.SmoothForm.mpullback d_exact d_exact.contMDiff V_M.Ω = V_M.Ω ∧
      MeasurePreserving ⇑d_exact V_M.μ V_M.μ ∧
      IsTuringComplete ⇑d_exact ∧
      (⇑d_exact : M → M) ≠ id := by
  obtain ⟨π_f, f, d_exact, _, hunimV, _, _, _, hf_comp, hpoiss, hvol, hmp, htc, hne⟩ :=
    exists_turingComplete_exactVolumePreserving_poissonDiffeomorph_closedFourManifold M V_M
  exact ⟨π_f, f, d_exact, hunimV, hf_comp, hpoiss, hvol, hmp, htc, hne⟩

/-- Exact-`V_M` algorithmic undecidability of forward-orbit reachability on any nonempty compact
Hausdorff smooth 4-manifold `(M, V_M)` (`SC-R3`, zero `[ConnectedSpace M]` assumption). -/
-- tier: T2
theorem undecidable_orbit_reachability_exactVolumePreserving_closedFourManifold
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [T2Space M] [Nonempty M]
    (V_M : PositiveVolumeForm (𝓡 4) M) :
    ∃ (π_f : PoissonStructure (𝓡 4) M)
      (d_exact : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M)
      (U : Opens M)
      (Param : Type) (instTopParam : TopologicalSpace Param) (param₀ : Param)
      (openChart : Param × UnitDisk2 → M)
      (chart : UnitDisk2 → M)
      (coord : Nat.Partrec.Code → UnitDisk2)
      (approx : Nat.Partrec.Code × ℕ → RatFrac × RatFrac)
      (targetBoxes : ℕ → RatBox2),
      π_f.IsUnimodularWithVolume V_M.Ω ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_exact d_exact.contMDiff ∧
      TauCeti.SmoothForm.mpullback d_exact d_exact.contMDiff V_M.Ω = V_M.Ω ∧
      MeasurePreserving ⇑d_exact V_M.μ V_M.μ ∧
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
      REPred (fun c : Nat.Partrec.Code ↦ ∃ n : ℕ, (⇑d_exact)^[n] (chart (coord c)) ∈ U) ∧
      ¬ ComputablePred (fun c : Nat.Partrec.Code ↦
          ∃ n : ℕ, (⇑d_exact)^[n] (chart (coord c)) ∈ U) ∧
      ¬ ∃ dec : Nat.Partrec.Code → Bool,
          Computable dec ∧
          ∀ c : Nat.Partrec.Code,
            dec c = true ↔ ∃ n : ℕ, (⇑d_exact)^[n] (chart (coord c)) ∈ U := by
  obtain ⟨π_f, _, d_exact, _, hunimV, _, _, _, _, hpoiss, hvol, hmp, htc, _⟩ :=
    exists_turingComplete_exactVolumePreserving_poissonDiffeomorph_closedFourManifold M V_M
  obtain ⟨U, Param, instTopParam, param₀, openChart, chart, coord, approx, targetBoxes, hU,
      hopen, hchart_eq, hcont, hinj, hcomp, hbound, hcomp_boxes, hbox_ne, hU_eq, hnot0, hre,
      hnotcomp, hnodec⟩ :=
    htc.undecidable_orbit_reachability
  exact ⟨π_f, d_exact, U, Param, instTopParam, param₀, openChart, chart, coord, approx,
    targetBoxes, hunimV, hpoiss, hvol, hmp, hU, hopen, hchart_eq, hcont, hinj, hcomp, hbound,
    hcomp_boxes, hbox_ne, hU_eq, hnot0, hre, hnotcomp, hnodec⟩

/-- **Theorem 1 on $S^4$ Preserving the Exact Round Volume Form `S4PositiveVolumeForm` (`SC-R3`,
Full Poisson Bundle)**:
Moser conjugation on `Sphere4` produces a smooth map `f : Sphere4 → Sphere2` (`s4Fibration ∘ ⇑ψ`),
a **generically rank-2** Poisson structure `π_f` unimodular with respect to the **exact standard
round volume form `S4PositiveVolumeForm.Ω`**, and a $C^\infty$ diffeomorphism
`d_exact : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4` preserving `f`, `π_f`, **`S4PositiveVolumeForm.Ω`**, and
**`S4PositiveVolumeForm.μ`** that is Turing complete (`IsTuringComplete ⇑d_exact`, `≠ id`). -/
-- tier: T2
theorem exists_turingComplete_exactVolumePreserving_poissonDiffeomorph_S4 :
    ∃ (π_f : PoissonStructure (𝓡 4) Sphere4)
      (f : Sphere4 → Sphere2)
      (d_exact : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4),
      ContMDiff (𝓡 4) (𝓡 2) ∞ f ∧
      π_f.IsUnimodularWithVolume S4PositiveVolumeForm.Ω ∧
      π_f.IsUnimodularPoisson ∧
      π_f.IsGenericallyRankTwo ∧
      (∀ x ∉ criticalPoints (𝓡 4) (𝓡 2) f, π_f.rankAt x = 2) ∧
      (criticalPoints (𝓡 4) (𝓡 2) f).Nonempty ∧
      (∀ x ∈ criticalPoints (𝓡 4) (𝓡 2) f, π_f.rankAt x = 0) ∧
      f ∘ ⇑d_exact = f ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_exact d_exact.contMDiff ∧
      TauCeti.SmoothForm.mpullback d_exact d_exact.contMDiff S4PositiveVolumeForm.Ω =
        S4PositiveVolumeForm.Ω ∧
      MeasurePreserving ⇑d_exact S4PositiveVolumeForm.μ S4PositiveVolumeForm.μ ∧
      IsTuringComplete ⇑d_exact ∧
      (⇑d_exact : Sphere4 → Sphere4) ≠ id ∧
      S4PositiveVolumeForm.μ = TauCeti.RoughForm.measure S4PositiveVolumeForm.Ω.1 := by
  let W : MoserVolume S4PositiveVolumeForm s4AlignedPositiveVolume :=
    MoserVolume.ofPositivelyCooriented S4PositiveVolumeForm s4AlignedPositiveVolume
      (fun x ↦ alignedVolumeForm_pos_cooriented Sphere4 x)
  obtain ⟨p₀, hp₀⟩ := criticalPoints_s4Fibration_nonempty
  have hcrit_ne : (criticalPoints (𝓡 4) (𝓡 2) (s4Fibration ∘ ⇑W.ψ)).Nonempty :=
    ⟨W.ψ.symm p₀, (W.mem_criticalPoints_comp_ψ_iff s4Fibration contMDiff_s4Fibration _).mpr
      (by rwa [W.ψ.apply_symm_apply])⟩
  exact ⟨W.pullbackJacobianPoisson s4Fibration contMDiff_s4Fibration,
    s4Fibration ∘ ⇑W.ψ, W.conjDiffeomorph s4TuringDiffeomorph,
    contMDiff_s4Fibration.comp W.ψ.contMDiff,
    W.isUnimodularWithVolume_pullbackJacobianPoisson s4Fibration contMDiff_s4Fibration,
    W.isUnimodularPoisson_pullbackJacobianPoisson s4Fibration contMDiff_s4Fibration,
    (W.isGenericallyRankTwo_pullbackJacobianPoisson_iff s4Fibration contMDiff_s4Fibration).mpr
      isGenericallyRankTwo_s4AdaptedPoisson,
    fun x hx ↦
      W.rankAt_pullbackJacobianPoisson_of_notMem_criticalPoints s4Fibration contMDiff_s4Fibration
        hx,
    hcrit_ne,
    fun x hx ↦
      W.rankAt_pullbackJacobianPoisson_of_mem_criticalPoints s4Fibration contMDiff_s4Fibration hx,
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

/-- **Theorem 1 on $S^4$ Preserving the Exact Round Volume Form `S4PositiveVolumeForm` (`SC-R3`,
Concise Headline Statement)**:
There exists a $C^\infty$ diffeomorphism `d_exact : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4` preserving a
generically rank-`2` unimodular Poisson structure `π_f` and smooth map `f : Sphere4 → Sphere2`,
preserving the **exact standard round volume form `S4PositiveVolumeForm.Ω`** under pullback and its
finite Borel measure **`S4PositiveVolumeForm.μ`**, and satisfying `IsTuringComplete ⇑d_exact`
(`≠ id`). -/
-- tier: T2
theorem exists_turingComplete_exactVolumePreserving_diffeomorph_S4 :
    ∃ (π_f : PoissonStructure (𝓡 4) Sphere4)
      (f : Sphere4 → Sphere2)
      (d_exact : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4),
      π_f.IsUnimodularWithVolume S4PositiveVolumeForm.Ω ∧
      π_f.IsGenericallyRankTwo ∧
      f ∘ ⇑d_exact = f ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_exact d_exact.contMDiff ∧
      TauCeti.SmoothForm.mpullback d_exact d_exact.contMDiff S4PositiveVolumeForm.Ω =
        S4PositiveVolumeForm.Ω ∧
      MeasurePreserving ⇑d_exact S4PositiveVolumeForm.μ S4PositiveVolumeForm.μ ∧
      IsTuringComplete ⇑d_exact ∧
      (⇑d_exact : Sphere4 → Sphere4) ≠ id := by
  obtain ⟨π_f, f, d_exact, _, hunimV, _, hgen, _, _, _, hf_comp, hpoiss, hvol, hmp, htc, hne, _⟩ :=
    exists_turingComplete_exactVolumePreserving_poissonDiffeomorph_S4
  exact ⟨π_f, f, d_exact, hunimV, hgen, hf_comp, hpoiss, hvol, hmp, htc, hne⟩

/-- **Exact-`V_M` Generically Rank-`2` Corollary 2 over `PurelyWrinkledFibration` (`SC-R2` +
`SC-R3`)**:
Conjugates `exists_turingComplete_volumePreserving_poissonDiffeomorph_of_purelyWrinkled` by the
componentwise Moser diffeomorphism `W.ψ` (requiring **zero** `[ConnectedSpace M]` assumption!) to
obtain a `PurelyWrinkledFibration` `P_exact := P.compDiffeomorph W.ψ`, a **generically rank-2**
Poisson structure `π_f` unimodular with **`V_M.Ω` itself**, and a $C^\infty$ Turing complete
Poisson diffeomorphism `d_exact` preserving `P_exact.toFun`, **`V_M.Ω`**, and **`V_M.μ`**. -/
-- tier: T2
theorem exists_turingComplete_exactVolumePreserving_poissonDiffeomorph_of_purelyWrinkled
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
      (d_exact : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M),
      π_f.IsUnimodularWithVolume V_M.Ω ∧
      π_f.IsUnimodularPoisson ∧
      π_f.IsGenericallyRankTwo ∧
      (∀ x ∉ criticalPoints (𝓡 4) (𝓡 2) P_exact.toFun, π_f.rankAt x = 2) ∧
      (∀ x ∈ criticalPoints (𝓡 4) (𝓡 2) P_exact.toFun, π_f.rankAt x = 0) ∧
      P_exact.toFun ∘ ⇑d_exact = P_exact.toFun ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_exact d_exact.contMDiff ∧
      TauCeti.SmoothForm.mpullback d_exact d_exact.contMDiff V_M.Ω = V_M.Ω ∧
      MeasurePreserving ⇑d_exact V_M.μ V_M.μ ∧
      IsTuringComplete ⇑d_exact ∧
      (⇑d_exact : M → M) ≠ id := by
  let A : AdmitsWrinkledOrBrokenLefschetzFibration M :=
    AdmitsWrinkledOrBrokenLefschetzFibration.ofPurelyWrinkled V_M F P V_F hpos
  let _ : AdmitsWrinkledOrBrokenLefschetzFibration M := A
  let W : MoserVolume V_M (alignedPositiveVolume M) :=
    MoserVolume.ofPositivelyCooriented V_M (alignedPositiveVolume M)
      (fun x ↦ alignedVolumeForm_pos_cooriented M x)
  let P_exact := P.compDiffeomorph W.ψ
  exact ⟨P_exact, W.pullbackJacobianPoisson P.toFun P.contMDiff_toFun,
    W.conjDiffeomorph (leafwiseBumpDiffeomorph M),
    W.isUnimodularWithVolume_pullbackJacobianPoisson P.toFun P.contMDiff_toFun,
    W.isUnimodularPoisson_pullbackJacobianPoisson P.toFun P.contMDiff_toFun,
    (W.isGenericallyRankTwo_pullbackJacobianPoisson_iff P.toFun P.contMDiff_toFun).mpr
      (isGenericallyRankTwo_adaptedJacobianPoisson M),
    fun x hx ↦
      W.rankAt_pullbackJacobianPoisson_of_notMem_criticalPoints P.toFun P.contMDiff_toFun hx,
    fun x hx ↦
      W.rankAt_pullbackJacobianPoisson_of_mem_criticalPoints P.toFun P.contMDiff_toFun hx,
    W.fibration_comp_conjDiffeomorph (fibration_comp_leafwiseBumpDiffeomorph M),
    W.isPoissonMap_conjDiffeomorph P.toFun P.contMDiff_toFun
      (isPoissonMap_leafwiseBumpDiffeomorph M),
    W.mpullback_conjDiffeomorph (connectedComponent_leafwiseBumpDiffeomorph M)
      (mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm M),
    W.measurePreserving_conjDiffeomorph (connectedComponent_leafwiseBumpDiffeomorph M)
      (mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm M),
    W.isTuringComplete_conjDiffeomorph (isTuringComplete_leafwiseBumpDiffeomorph M),
    W.conjDiffeomorph_ne_id (isTuringComplete_leafwiseBumpDiffeomorph M)⟩

/-- **Exact-`V_M` Generically Rank-`2` Corollary 2 over `BrokenLefschetzFibration` (`SC-R2` +
`SC-R3`)**:
Combines Lekili's Move 1 wrinkling deformation (`B → P`) with componentwise Moser isotopy
conjugation (`W.isotopy`, requiring **zero** `[ConnectedSpace M]` assumption!) to produce a
`PurelyWrinkledFibration` `P_exact` connected to `B.toFun` by a jointly $C^\infty$ global homotopy
`H_exact` (`H_exact 0 = B.toFun`, `H_exact 1 = P_exact.toFun`), a **generically rank-2** Poisson
structure `π_f` unimodular with **`V_M.Ω` itself**, and a $C^\infty$ Turing complete Poisson
diffeomorphism `d_exact` preserving `P_exact.toFun`, **`V_M.Ω`**, and **`V_M.μ`**. -/
-- tier: T2
theorem exists_turingComplete_exactVolumePreserving_poissonDiffeomorph_of_brokenLefschetz
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
    ∃ (P_exact : PurelyWrinkledFibration (𝓡 4) M (𝓡 2) Sphere2 F)
      (H_exact : ℝ → M → Sphere2)
      (π_f : PoissonStructure (𝓡 4) M)
      (d_exact : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M),
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 4)) (𝓡 2) ∞ (Function.uncurry H_exact) ∧
      (∀ x, H_exact 0 x = B.toFun x) ∧
      (∀ x, H_exact 1 x = P_exact.toFun x) ∧
      π_f.IsUnimodularWithVolume V_M.Ω ∧
      π_f.IsUnimodularPoisson ∧
      π_f.IsGenericallyRankTwo ∧
      (∀ x ∉ criticalPoints (𝓡 4) (𝓡 2) P_exact.toFun, π_f.rankAt x = 2) ∧
      (∀ x ∈ criticalPoints (𝓡 4) (𝓡 2) P_exact.toFun, π_f.rankAt x = 0) ∧
      P_exact.toFun ∘ ⇑d_exact = P_exact.toFun ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_exact d_exact.contMDiff ∧
      TauCeti.SmoothForm.mpullback d_exact d_exact.contMDiff V_M.Ω = V_M.Ω ∧
      MeasurePreserving ⇑d_exact V_M.μ V_M.μ ∧
      IsTuringComplete ⇑d_exact ∧
      (⇑d_exact : M → M) ≠ id := by
  obtain ⟨P, _, H, _, _, _, _, _, _, _, hH_md, hH_0, hH_1, _, hpos_P⟩ :=
    exists_pos_cooriented_purelyWrinkledFibration_of_brokenLefschetz M V_M F B V_F hpos
  let A : AdmitsWrinkledOrBrokenLefschetzFibration M :=
    AdmitsWrinkledOrBrokenLefschetzFibration.ofPurelyWrinkled V_M F P V_F hpos_P
  let _ : AdmitsWrinkledOrBrokenLefschetzFibration M := A
  let W : MoserVolume V_M (alignedPositiveVolume M) :=
    MoserVolume.ofPositivelyCooriented V_M (alignedPositiveVolume M)
      (fun x ↦ alignedVolumeForm_pos_cooriented M x)
  let P_exact := P.compDiffeomorph W.ψ
  let H_exact : ℝ → M → Sphere2 := fun t x ↦ H t (W.isotopy t x)
  have hH_exact_md : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 4)) (𝓡 2) ∞ (Function.uncurry H_exact) := by
    have heq : Function.uncurry H_exact =
        Function.uncurry H ∘ fun p : ℝ × M ↦ (p.1, W.isotopy p.1 p.2) := rfl
    rw [heq]
    exact hH_md.comp (contMDiff_fst.prodMk W.contMDiff_isotopy)
  have hH_exact_0 : ∀ x : M, H_exact 0 x = B.toFun x := fun x ↦ by
    change H 0 (W.isotopy 0 x) = B.toFun x
    rw [W.isotopy_zero]
    exact hH_0 x
  have hH_exact_1 : ∀ x : M, H_exact 1 x = P_exact.toFun x := fun x ↦ by
    change H 1 (W.isotopy 1 x) = P.toFun (W.ψ x)
    rw [W.isotopy_one]
    exact hH_1 (W.ψ x)
  exact ⟨P_exact, H_exact, W.pullbackJacobianPoisson P.toFun P.contMDiff_toFun,
    W.conjDiffeomorph (leafwiseBumpDiffeomorph M),
    hH_exact_md, hH_exact_0, hH_exact_1,
    W.isUnimodularWithVolume_pullbackJacobianPoisson P.toFun P.contMDiff_toFun,
    W.isUnimodularPoisson_pullbackJacobianPoisson P.toFun P.contMDiff_toFun,
    (W.isGenericallyRankTwo_pullbackJacobianPoisson_iff P.toFun P.contMDiff_toFun).mpr
      (isGenericallyRankTwo_adaptedJacobianPoisson M),
    fun x hx ↦
      W.rankAt_pullbackJacobianPoisson_of_notMem_criticalPoints P.toFun P.contMDiff_toFun hx,
    fun x hx ↦
      W.rankAt_pullbackJacobianPoisson_of_mem_criticalPoints P.toFun P.contMDiff_toFun hx,
    W.fibration_comp_conjDiffeomorph (fibration_comp_leafwiseBumpDiffeomorph M),
    W.isPoissonMap_conjDiffeomorph P.toFun P.contMDiff_toFun
      (isPoissonMap_leafwiseBumpDiffeomorph M),
    W.mpullback_conjDiffeomorph (connectedComponent_leafwiseBumpDiffeomorph M)
      (mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm M),
    W.measurePreserving_conjDiffeomorph (connectedComponent_leafwiseBumpDiffeomorph M)
      (mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm M),
    W.isTuringComplete_conjDiffeomorph (isTuringComplete_leafwiseBumpDiffeomorph M),
    W.conjDiffeomorph_ne_id (isTuringComplete_leafwiseBumpDiffeomorph M)⟩

end ExactMoserVolumeTheorems

end S4TuringPoisson.Main
