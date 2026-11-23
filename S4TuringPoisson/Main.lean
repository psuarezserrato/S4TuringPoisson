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
public import S4TuringPoisson.Smoothing.CMPPInstance

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

/-! ## 1. Canonical Adapted Volume & Jacobian–Poisson Package on $S^4$ -/

/-- Aligned positive volume 4-form and finite Borel measure `(Ω, μ_Ω)` on `Sphere4`. -/
noncomputable def s4AlignedPositiveVolume : PositiveVolumeForm (𝓡 4) Sphere4 :=
  alignedPositiveVolume Sphere4

/-- Generically rank-`2`, globally unimodular Jacobian–Poisson structure `π_f` on `Sphere4`
adapted to `s4Fibration : Sphere4 → Sphere2` and `s4AlignedPositiveVolume`. -/
noncomputable def s4AdaptedPoisson : PoissonStructure (𝓡 4) Sphere4 :=
  adaptedJacobianPoisson Sphere4

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
    AdmitsWrinkledOrBrokenLefschetzFibration.fiberDiskChart Sphere4
  let b₀ := s4WrinkledFibration.baseCenter
  have hb₀ : b₀.1 ∈ (baseCoreOpen Sphere4).1 := baseCenter_mem_baseCoreOpen Sphere4
  have hρ1 : bumpProfile Sphere4 b₀.1 = 1 :=
    bumpProfile_eq_one_of_mem_baseCoreOpen Sphere4 hb₀
  let x₀ : Sphere4 := s4WrinkledFibration.embed (b₀, C.embed ⟨y.1, y.2⟩)
  have hx₀ : s4UnconditionalPoissonDiffeomorph x₀ = x₀ := congrFun hid x₀
  dsimp only [s4UnconditionalPoissonDiffeomorph, x₀] at hx₀
  have hemb_step :
      leafwiseBumpDiffeomorphOfIsotopy Sphere4 s4SectorSwapDiskIsotopy
          (s4WrinkledFibration.embed (b₀, C.embed ⟨y.1, y.2⟩)) =
        s4WrinkledFibration.embed
          (b₀, C.liftIsotopyDiffeomorph s4SectorSwapDiskIsotopy (bumpProfile Sphere4 b₀.1)
            (C.embed ⟨y.1, y.2⟩)) :=
    leafwiseBumpDiffeomorphOfIsotopy_embed Sphere4 s4SectorSwapDiskIsotopy b₀
      (C.embed ⟨y.1, y.2⟩)
  rw [hemb_step, hρ1, C.liftIsotopyDiffeomorph_embed s4SectorSwapDiskIsotopy 1 ⟨y.1, y.2⟩] at hx₀
  have hinj_emb := s4WrinkledFibration.isOpenEmbedding_embed.injective hx₀
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
      (∀ x ∉ criticalPoints (𝓡 4) (𝓡 2) s4Fibration, π_f.rankAt x = 2) ∧
      (criticalPoints (𝓡 4) (𝓡 2) s4Fibration).Nonempty ∧
      (∀ x ∈ criticalPoints (𝓡 4) (𝓡 2) s4Fibration, π_f.rankAt x = 0) ∧
      s4Fibration ∘ ⇑d_bar = s4Fibration ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_bar d_bar.contMDiff ∧
      (∀ b : s4BaseRegion,
        ∃ d_b : Sphere2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere2,
          (∀ z : Sphere2,
            d_bar (s4WrinkledFibration.embed (b, z)) = s4WrinkledFibration.embed (b, d_b z)) ∧
          TauCeti.SmoothForm.mpullback d_b d_b.contMDiff S2VolumeForm = S2VolumeForm ∧
          MeasurePreserving ⇑d_b S2PositiveVolumeForm.μ S2PositiveVolumeForm.μ) ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasurePreserving ⇑d_bar V.μ V.μ ∧
      IsTuringComplete ⇑d_bar ∧
      (⇑d_bar : Sphere4 → Sphere4) ≠ id := by
  refine ⟨s4AlignedPositiveVolume, s4AdaptedPoisson, leafwiseBumpDiffeomorph Sphere4,
    rfl,
    isUnimodularWithVolume_adaptedJacobianPoisson Sphere4,
    isUnimodularPoisson_adaptedJacobianPoisson Sphere4,
    fun x hx ↦ rankAt_adaptedJacobianPoisson_of_notMem_criticalPoints Sphere4 hx,
    criticalPoints_s4Fibration_nonempty,
    fun x hx ↦ rankAt_adaptedJacobianPoisson_of_mem_criticalPoints Sphere4 hx,
    fibration_comp_leafwiseBumpDiffeomorph Sphere4,
    isPoissonMap_leafwiseBumpDiffeomorph Sphere4,
    fun b ↦ ?_,
    mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm Sphere4,
    measurePreserving_leafwiseBumpDiffeomorph Sphere4,
    isTuringComplete_leafwiseBumpDiffeomorph Sphere4,
    leafwiseBumpDiffeomorph_ne_id Sphere4⟩
  let C : SymplecticDiskChart Sphere2 S2VolumeForm :=
    AdmitsWrinkledOrBrokenLefschetzFibration.fiberDiskChart Sphere4
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
      IsTuringComplete ⇑d_bar :=
  ⟨s4AlignedPositiveVolume, leafwiseBumpDiffeomorph Sphere4,
    fibration_comp_leafwiseBumpDiffeomorph Sphere4,
    mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm Sphere4,
    measurePreserving_leafwiseBumpDiffeomorph Sphere4,
    isTuringComplete_leafwiseBumpDiffeomorph Sphere4⟩

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
      (⇑d_bar : M → M) ≠ id := by
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
    fun x hx ↦ rankAt_adaptedJacobianPoisson_of_notMem_criticalPoints M hx,
    fun x hx ↦ rankAt_adaptedJacobianPoisson_of_mem_criticalPoints M hx,
    fibration_comp_leafwiseBumpDiffeomorph M,
    isPoissonMap_leafwiseBumpDiffeomorph M,
    fun b ↦ ?_,
    mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm M,
    measurePreserving_leafwiseBumpDiffeomorph M,
    isTuringComplete_leafwiseBumpDiffeomorph M,
    leafwiseBumpDiffeomorph_ne_id M⟩
  let C := AdmitsWrinkledOrBrokenLefschetzFibration.fiberDiskChart M
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
      (chart : UnitDisk2 → Sphere4)
      (coord : Nat.Partrec.Code → UnitDisk2)
      (approx : Nat.Partrec.Code × ℕ → RatFrac × RatFrac),
      s4Fibration ∘ ⇑d_bar = s4Fibration ∧
      π_f.IsUnimodularWithVolume V.Ω ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_bar d_bar.contMDiff ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasurePreserving ⇑d_bar V.μ V.μ ∧
      U.1.Nonempty ∧
      Continuous chart ∧
      Function.Injective chart ∧
      Computable approx ∧
      (∀ (c : Nat.Partrec.Code) (m : ℕ),
        ‖ratFracPairToEuclidean2 (approx (c, m)) - (coord c).1‖ ≤ (1 / 2 : ℝ) ^ m) ∧
      (∀ c : Nat.Partrec.Code, chart (coord c) ∉ U) ∧
      REPred (fun c : Nat.Partrec.Code ↦ ∃ n : ℕ, (⇑d_bar)^[n] (chart (coord c)) ∈ U) ∧
      ¬ ComputablePred (fun c : Nat.Partrec.Code ↦
          ∃ n : ℕ, (⇑d_bar)^[n] (chart (coord c)) ∈ U) ∧
      ¬ ∃ dec : Nat.Partrec.Code → Bool,
          Computable dec ∧
          ∀ c : Nat.Partrec.Code,
            dec c = true ↔ ∃ n : ℕ, (⇑d_bar)^[n] (chart (coord c)) ∈ U := by
  obtain ⟨U, chart, coord, approx, hU, hcont, hinj, hcomp, hbound, hnot0, hre, hnotcomp, hnodec⟩ :=
    undecidable_orbit_reachability_leafwiseBumpDiffeomorph Sphere4
  exact ⟨s4AlignedPositiveVolume, s4AdaptedPoisson, leafwiseBumpDiffeomorph Sphere4, U, chart,
    coord, approx,
    fibration_comp_leafwiseBumpDiffeomorph Sphere4,
    isUnimodularWithVolume_adaptedJacobianPoisson Sphere4,
    isPoissonMap_leafwiseBumpDiffeomorph Sphere4,
    mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm Sphere4,
    measurePreserving_leafwiseBumpDiffeomorph Sphere4,
    hU, hcont, hinj, hcomp, hbound, hnot0, hre, hnotcomp, hnodec⟩

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
      (∀ x ∉ criticalPoints (𝓡 4) (𝓡 2) s4Fibration, π_f.rankAt x = 2) ∧
      (criticalPoints (𝓡 4) (𝓡 2) s4Fibration).Nonempty ∧
      (∀ x ∈ criticalPoints (𝓡 4) (𝓡 2) s4Fibration, π_f.rankAt x = 0) ∧
      s4Fibration ∘ ⇑d_bar = s4Fibration ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_bar d_bar.contMDiff ∧
      (∀ b : s4BaseRegion,
        ∃ d_b : Sphere2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere2,
          (∀ z : Sphere2,
            d_bar (s4WrinkledFibration.embed (b, z)) = s4WrinkledFibration.embed (b, d_b z)) ∧
          TauCeti.SmoothForm.mpullback d_b d_b.contMDiff S2VolumeForm = S2VolumeForm ∧
          MeasurePreserving ⇑d_b S2PositiveVolumeForm.μ S2PositiveVolumeForm.μ) ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasurePreserving ⇑d_bar V.μ V.μ ∧
      IsTuringComplete ⇑d_bar ∧
      (⇑d_bar : Sphere4 → Sphere4) ≠ id :=
  exists_turingComplete_volumePreserving_poissonDiffeomorph_S4_of_isotopy

/-- **Theorem 1 (Concise Prose Statement on $S^4$)**:
There exist a positive smooth volume 4-form `V` on `Sphere4` and a $C^\infty$ diffeomorphism
`d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4` preserving `s4Fibration`, preserving `V.Ω` under pullback,
preserving the finite Borel volume measure `V.μ`, and satisfying `IsTuringComplete ⇑d_bar`. -/
-- tier: T2
theorem exists_turingComplete_volumePreserving_diffeomorph_S4 :
    ∃ (V : PositiveVolumeForm (𝓡 4) Sphere4)
      (d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4),
      s4Fibration ∘ ⇑d_bar = s4Fibration ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasurePreserving ⇑d_bar V.μ V.μ ∧
      IsTuringComplete ⇑d_bar :=
  exists_turingComplete_volumePreserving_diffeomorph_S4_of_isotopy

/-- **Corollary 2 (`S4TCdiffeo-Aug-2026.tex` — General Closed Oriented 4-Manifolds)**:
Every compact Hausdorff smooth 4-manifold `M` admitting a positively co-oriented wrinkled or broken
Lefschetz fibration `[A : AdmitsWrinkledOrBrokenLefschetzFibration M]` carries a positive volume
4-form `V`, a compatible generically rank-`2` unimodular Jacobian–Poisson structure `π_f`, and a
smooth, leaf-preserving, area-preserving on regular fibers, volume-preserving, measure-preserving,
Turing complete Poisson diffeomorphism `d_bar : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M`. -/
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
      (⇑d_bar : M → M) ≠ id :=
  exists_turingComplete_volumePreserving_poissonDiffeomorph_fourManifold_of_isotopy M

/-- **Algorithmic Undecidability of Forward-Orbit Reachability on $S^4$**:
There exist a smooth leaf-preserving, volume-preserving, measure-preserving Poisson diffeomorphism
`d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4`, a nonempty open target `U : Opens Sphere4`, a continuous
injective disk chart `chart : UnitDisk2 → Sphere4`, initial coordinates
`coord : Nat.Partrec.Code → UnitDisk2`, and a `Computable` dyadic rational approximation procedure
`approx : Nat.Partrec.Code × ℕ → RatFrac × RatFrac` (`≤ 2⁻ᵐ`) such that forward-orbit reachability
`∃ n, d_bar^[n] (chart (coord c)) ∈ U` is recursively enumerable (`REPred`) yet algorithmically
undecidable (`¬ ComputablePred`), with no total computable `Bool` decision procedure. -/
-- tier: T2
theorem undecidable_orbit_reachability_S4 :
    ∃ (V : PositiveVolumeForm (𝓡 4) Sphere4)
      (π_f : PoissonStructure (𝓡 4) Sphere4)
      (d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4)
      (U : Opens Sphere4)
      (chart : UnitDisk2 → Sphere4)
      (coord : Nat.Partrec.Code → UnitDisk2)
      (approx : Nat.Partrec.Code × ℕ → RatFrac × RatFrac),
      s4Fibration ∘ ⇑d_bar = s4Fibration ∧
      π_f.IsUnimodularWithVolume V.Ω ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_bar d_bar.contMDiff ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasurePreserving ⇑d_bar V.μ V.μ ∧
      U.1.Nonempty ∧
      Continuous chart ∧
      Function.Injective chart ∧
      Computable approx ∧
      (∀ (c : Nat.Partrec.Code) (m : ℕ),
        ‖ratFracPairToEuclidean2 (approx (c, m)) - (coord c).1‖ ≤ (1 / 2 : ℝ) ^ m) ∧
      (∀ c : Nat.Partrec.Code, chart (coord c) ∉ U) ∧
      REPred (fun c : Nat.Partrec.Code ↦ ∃ n : ℕ, (⇑d_bar)^[n] (chart (coord c)) ∈ U) ∧
      ¬ ComputablePred (fun c : Nat.Partrec.Code ↦
          ∃ n : ℕ, (⇑d_bar)^[n] (chart (coord c)) ∈ U) ∧
      ¬ ∃ dec : Nat.Partrec.Code → Bool,
          Computable dec ∧
          ∀ c : Nat.Partrec.Code,
            dec c = true ↔ ∃ n : ℕ, (⇑d_bar)^[n] (chart (coord c)) ∈ U :=
  undecidable_orbit_reachability_S4_of_isotopy

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
      (∀ x ∉ criticalPoints (𝓡 4) (𝓡 2) s4Fibration, π_f.rankAt x = 2) ∧
      (criticalPoints (𝓡 4) (𝓡 2) s4Fibration).Nonempty ∧
      (∀ x ∈ criticalPoints (𝓡 4) (𝓡 2) s4Fibration, π_f.rankAt x = 0) ∧
      s4Fibration ∘ ⇑d_bar = s4Fibration ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_bar d_bar.contMDiff ∧
      (∀ b : s4BaseRegion,
        ∃ d_b : Sphere2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere2,
          (∀ z : Sphere2,
            d_bar (s4WrinkledFibration.embed (b, z)) = s4WrinkledFibration.embed (b, d_b z)) ∧
          TauCeti.SmoothForm.mpullback d_b d_b.contMDiff S2VolumeForm = S2VolumeForm ∧
          MeasurePreserving ⇑d_b S2PositiveVolumeForm.μ S2PositiveVolumeForm.μ) ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasurePreserving ⇑d_bar V.μ V.μ ∧
      IsTuringComplete ⇑d_bar ∧
      (⇑d_bar : Sphere4 → Sphere4) ≠ id :=
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
      IsTuringComplete ⇑d_bar :=
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
      (⇑d_bar : M → M) ≠ id :=
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
      (chart : UnitDisk2 → Sphere4)
      (coord : Nat.Partrec.Code → UnitDisk2)
      (approx : Nat.Partrec.Code × ℕ → RatFrac × RatFrac),
      s4Fibration ∘ ⇑d_bar = s4Fibration ∧
      π_f.IsUnimodularWithVolume V.Ω ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_bar d_bar.contMDiff ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasurePreserving ⇑d_bar V.μ V.μ ∧
      U.1.Nonempty ∧
      Continuous chart ∧
      Function.Injective chart ∧
      Computable approx ∧
      (∀ (c : Nat.Partrec.Code) (m : ℕ),
        ‖ratFracPairToEuclidean2 (approx (c, m)) - (coord c).1‖ ≤ (1 / 2 : ℝ) ^ m) ∧
      (∀ c : Nat.Partrec.Code, chart (coord c) ∉ U) ∧
      REPred (fun c : Nat.Partrec.Code ↦ ∃ n : ℕ, (⇑d_bar)^[n] (chart (coord c)) ∈ U) ∧
      ¬ ComputablePred (fun c : Nat.Partrec.Code ↦
          ∃ n : ℕ, (⇑d_bar)^[n] (chart (coord c)) ∈ U) ∧
      ¬ ∃ dec : Nat.Partrec.Code → Bool,
          Computable dec ∧
          ∀ c : Nat.Partrec.Code,
            dec c = true ↔ ∃ n : ℕ, (⇑d_bar)^[n] (chart (coord c)) ∈ U :=
  @undecidable_orbit_reachability_S4_of_isotopy
    (@instHasTuringCompleteAreaPreservingDiskIsotopyOfCMPP C)

end CMPPSpecializations

end S4TuringPoisson.Main
