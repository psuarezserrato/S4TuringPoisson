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
public import S4TuringPoisson.Fibration.PurelyWrinkled
public import TauCeti.Geometry.Manifold.DeRham.Integration.Bijective
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Positivity
public import TauCeti.Geometry.Manifold.DifferentialForm.Flow.Family

/-!
# Moser's Volume Theorem and Exact Volume Conjugation on Smooth 4-Manifolds (`SC-R3`)

This module formalizes Deliverable `SC-R3` of `MISSION_DIRECTIVE_SOUND_AND_COMPLETE.md` (closing
Semantic Findings `S1`, `S6b` and Recommendations `(i)`, `(iv)`), proving **Moser's Volume Theorem**
(`Moser 1965`, *Trans. Amer. Math. Soc.* **120**, 286–294) on compact smooth boundaryless
4-manifolds and lifting it componentwise across clopen connected components with **zero**
`[ConnectedSpace M]` assumption:

1. **Connected Moser's Volume Theorem (`exists_moser_diffeomorph_connected`)**:
   - On any compact connected Hausdorff smooth 4-manifold `M` equipped with two positively
     co-oriented `PositiveVolumeForm`s `V₀` and `V₁` (`∀ x, ∃ a > 0, V₁.Ω.1 x = a • V₀.Ω.1 x`),
     uses `TauCeti.integralTopForm_pos` and
     `TauCeti.mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero` (backed by
     `TauCeti.compactlySupportedDeRhamCohomology.bijective_integral`) to obtain `c > 0` and a
     smooth `3`-form primitive `β` with `dβ = V₁.Ω - c • V₀.Ω`.
   - Integrates the complete time-dependent Moser vector field along a smooth `[0, 1]` transition
     profile via `TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_eq` to produce a smooth
     isotopy `H_iso : ℝ → (M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M)` with `H_iso 0 = refl`, `H_iso 1 = ψ`, and
     `ψ^* V₁.Ω = c • V₀.Ω`.

2. **Componentwise Moser Bundle Without Connectedness (`MoserVolume`,
   `MoserVolume.ofPositivelyCooriented`)**:
   - Proves that every connected component of a smooth 4-manifold `M` is clopen, hence a compact
     connected smooth open submanifold when `[CompactSpace M]`.
   - Glues the componentwise de Rham constants `c_i > 0` into a locally constant positive smooth
     function `scale : C^∞⟮𝓡 4, M; ℝ⟯` and glues the componentwise `3`-form primitives into a
     single global `3`-form `β_glob`, running a single global Moser flow `ψ : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M`
     isotopic to `id` (`connectedComponent (ψ x) = connectedComponent x`) satisfying
     `ψ^* V₁.Ω = SmoothForm.funSMulₗ scale V₀.Ω`.
   - For any diffeomorphism `d_bar` preserving `V₁.Ω` and preserving each connected component of
     `M` (in particular every `leafwiseBumpDiffeomorphOfIsotopy M I_disk` and
     `leafwiseBumpDiffeomorph M`), the conjugate `d_exact := ψ.trans (d_bar.trans ψ.symm)`
     preserves the **exact input volume form `V₀.Ω` and Borel measure `V₀.μ`** on `M`:
     `d_exact^* V₀.Ω = V₀.Ω ∧ MeasurePreserving ⇑d_exact V₀.μ V₀.μ`.

3. **Transport of Unimodular Jacobian–Poisson Structures, Fibrations & Turing Completeness**:
   - Transports `jacobianPoissonOfPositiveVolume V₁ S2VolumeForm f hf` along `ψ` to a smooth
     Poisson structure `W.pullbackJacobianPoisson f hf` unimodular with respect to the **exact**
     input volume `V₀.Ω` (`IsUnimodularWithVolume V₀.Ω`, `IsUnimodularPoisson`), preserving
     `IsGenericallyRankTwo`, rank-`2` / rank-`0` regular-vs.-critical stratification for `f ∘ ⇑ψ`,
     `PurelyWrinkledFibration` / `BrokenLefschetzFibration` normal forms, and `IsTuringComplete`.
-/

@[expose] public section

noncomputable section

open Bundle Filter Function MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace S4TuringPoisson

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

/-! ## 1. Smooth `[0, 1]` Time Cutoff for Global Moser Interpolation on `ℝ × M` -/

section TimeCutoff

/-- Bump function centered at `t = 1` with `rIn = 1 / 4` and `rOut = 3 / 4`, vanishing at `t = 0`
and equal to `1` near `t = 1`. -/
def moserTimeBump : ContDiffBump (1 : ℝ) where
  rIn := 1 / 4
  rOut := 3 / 4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- Smooth scalar transition `τ : ℝ → ℝ` (`0 ≤ τ t ≤ 1`, `τ 0 = 0`, `τ 1 = 1`) ensuring the
interpolated top form `(1 - τ t) • (c • Ω₀) + τ t • Ω₁` is non-vanishing for **every** `t : ℝ`
(not merely `t ∈ [0, 1]`). -/
def moserTimeCutoff (t : ℝ) : ℝ :=
  moserTimeBump t

/-- `moserTimeCutoff` is `C^∞` smooth on `ℝ`. -/
-- tier: T1
theorem contDiff_moserTimeCutoff : ContDiff ℝ ∞ moserTimeCutoff :=
  moserTimeBump.contDiff

/-- `0 ≤ moserTimeCutoff t` for all `t : ℝ`. -/
-- tier: T1
theorem moserTimeCutoff_nonneg (t : ℝ) : 0 ≤ moserTimeCutoff t :=
  moserTimeBump.nonneg

/-- `moserTimeCutoff t ≤ 1` for all `t : ℝ`. -/
-- tier: T1
theorem moserTimeCutoff_le_one (t : ℝ) : moserTimeCutoff t ≤ 1 :=
  moserTimeBump.le_one

/-- `moserTimeCutoff 0 = 0`. -/
-- tier: T1
@[simp]
theorem moserTimeCutoff_zero : moserTimeCutoff 0 = 0 := by
  unfold moserTimeCutoff
  apply Function.notMem_support.mp
  rw [moserTimeBump.support_eq, Metric.mem_ball, Real.dist_eq]
  change ¬ |(0 : ℝ) - 1| < 3 / 4
  norm_num

/-- `moserTimeCutoff 1 = 1`. -/
-- tier: T1
@[simp]
theorem moserTimeCutoff_one : moserTimeCutoff 1 = 1 :=
  moserTimeBump.one_of_mem_closedBall (Metric.mem_closedBall_self moserTimeBump.rIn_pos.le)

/-- Pointwise `HasDerivAt` for `moserTimeCutoff`. -/
-- tier: T1
theorem hasDerivAt_moserTimeCutoff (t : ℝ) :
    HasDerivAt moserTimeCutoff (deriv moserTimeCutoff t) t :=
  (contDiff_moserTimeCutoff.differentiable (by simp) t).hasDerivAt

/-- `deriv moserTimeCutoff` is `C^∞` smooth on `ℝ`. -/
-- tier: T1
theorem contDiff_deriv_moserTimeCutoff : ContDiff ℝ ∞ (deriv moserTimeCutoff) := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ moserTimeCutoff) :=
    contDiff_moserTimeCutoff.fderiv_right (by simp)
  have heq : deriv moserTimeCutoff = fun t ↦ fderiv ℝ moserTimeCutoff t 1 :=
    funext fun t ↦ by
      rw [(hasDerivAt_moserTimeCutoff t).hasFDerivAt.fderiv]
      simp
  rw [heq]
  exact (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).contDiff.comp hfd

/-- Strict positivity of `(1 - moserTimeCutoff t) * c + moserTimeCutoff t * a` for all `t : ℝ`
whenever `0 < c` and `0 < a`. -/
-- tier: T1
theorem moserConvex_pos {c a : ℝ} (hc : 0 < c) (ha : 0 < a) (t : ℝ) :
    0 < (1 - moserTimeCutoff t) * c + moserTimeCutoff t * a := by
  have h0 := moserTimeCutoff_nonneg t
  have h1 := moserTimeCutoff_le_one t
  by_cases hhalf : moserTimeCutoff t ≤ 1 / 2
  · have hleft : 0 < (1 - moserTimeCutoff t) * c := mul_pos (by linarith) hc
    have hright : 0 ≤ moserTimeCutoff t * a := mul_nonneg h0 ha.le
    linarith
  · have hleft : 0 ≤ (1 - moserTimeCutoff t) * c := mul_nonneg (by linarith) hc.le
    have hright : 0 < moserTimeCutoff t * a := mul_pos (by linarith) ha
    linarith

end TimeCutoff

/-! ## 2. Top-Degree De Rham Integral Ratio & Exact Difference on Connected 4-Manifolds -/

section ConnectedDeRham

/-- Smooth density ratio `divVolume V₀.Ω V₀.Ω_ne_zero V₁.Ω` is strictly positive everywhere when
`V₁` is positively co-oriented with `V₀`. -/
-- tier: T1
theorem divVolume_pos_of_pos_cooriented
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    (V₀ V₁ : PositiveVolumeForm (𝓡 4) M)
    (hpos : ∀ x : M, ∃ a : ℝ, 0 < a ∧ V₁.Ω.1 x = a • V₀.Ω.1 x) (x : M) :
    0 < (divVolume V₀.Ω V₀.Ω_ne_zero V₁.Ω) x := by
  obtain ⟨a, ha_pos, ha_eq⟩ := hpos x
  have hsmul : (divVolume V₀.Ω V₀.Ω_ne_zero V₁.Ω) x • V₀.Ω.1 x = a • V₀.Ω.1 x :=
    (divVolume_apply_smul V₀.Ω V₀.Ω_ne_zero V₁.Ω x).trans ha_eq
  have heq : (divVolume V₀.Ω V₀.Ω_ne_zero V₁.Ω) x = a :=
    smul_left_injective ℝ (V₀.Ω_ne_zero x) hsmul
  rwa [heq]

/-- On any nonempty compact smooth 4-manifold `M`, every smooth top form positively co-oriented
with `V₀` has strictly positive `TauCeti.integralTopForm` against `V₀.orientation`. -/
-- tier: T2
theorem integralTopForm_pos_of_pos_cooriented
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]
    (V₀ V₁ : PositiveVolumeForm (𝓡 4) M)
    (hpos : ∀ x : M, ∃ a : ℝ, 0 < a ∧ V₁.Ω.1 x = a • V₀.Ω.1 x) :
    0 < TauCeti.integralTopForm V₀.orientation V₁.Ω.1 := by
  have h_pos_basis : ∀ (x : M) (b : Module.Basis (Fin 4) ℝ (TangentSpace (𝓡 4) x)),
      b.orientation = V₀.orientation.orientationAt x → 0 < V₁.Ω.1 x b := by
    intro x b hb
    have hV₀_pos : 0 < V₀.Ω.1 x b :=
      (TauCeti.Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff
        finrank_euclideanSpace_fin (V₀.Ω.isSmoothForm.of_le bot_le) V₀.Ω_ne_zero b).mp hb
    obtain ⟨a, ha_pos, ha_eq⟩ := hpos x
    rw [ha_eq, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    exact mul_pos ha_pos hV₀_pos
  have hc :
      IsCompact (_root_.tsupport (α := EuclideanSpace ℝ (Fin 4) [⋀^Fin 4]→L[ℝ] ℝ) V₁.Ω.1) :=
    isCompact_univ.of_isClosed_subset
      (_root_.isClosed_tsupport (α := EuclideanSpace ℝ (Fin 4) [⋀^Fin 4]→L[ℝ] ℝ) _)
      (Set.subset_univ _)
  let x₀ : M := Classical.arbitrary M
  let bE : Module.Basis (Fin 4) ℝ (TangentSpace (𝓡 4) x₀) :=
    (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis
  let c₀ : Module.Basis (Fin 4) ℝ (TangentSpace (𝓡 4) x₀) :=
    bE.adjustToOrientation (V₀.orientation.orientationAt x₀)
  have hc₀ : c₀.orientation = V₀.orientation.orientationAt x₀ :=
    bE.orientation_adjustToOrientation _
  exact TauCeti.integralTopForm_pos V₀.orientation (V₁.Ω.isSmoothForm.of_le bot_le) hc
    (fun x b hb ↦ (h_pos_basis x b hb).le) ⟨x₀, c₀, hc₀, h_pos_basis x₀ c₀ hc₀⟩

/-- Self-positivity `0 < ∫_M V₀.Ω` against `V₀.orientation` on a nonempty compact smooth
4-manifold `M`. -/
-- tier: T1
theorem integralTopForm_self_pos
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]
    (V₀ : PositiveVolumeForm (𝓡 4) M) :
    0 < TauCeti.integralTopForm V₀.orientation V₀.Ω.1 :=
  integralTopForm_pos_of_pos_cooriented V₀ V₀ fun _ ↦ ⟨1, one_pos, (one_smul ℝ _).symm⟩

/-- **Top-Degree De Rham Exactness of Rescaled Volume Difference**:
On a compact connected Hausdorff smooth 4-manifold `M`, for any two positively co-oriented
`PositiveVolumeForm`s `V₀, V₁`, the ratio `c = (∫_M V₁.Ω) / (∫_M V₀.Ω) > 0` makes `V₁.Ω - c • V₀.Ω`
exact (`V₁.Ω - c • V₀.Ω = dβ` for a smooth `3`-form `β`), via
`TauCeti.compactlySupportedDeRhamCohomology.bijective_integral` and
`TauCeti.mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero`. -/
-- tier: T2
theorem exists_primitive_of_pos_cooriented_connected
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [T2Space M] [ConnectedSpace M]
    (V₀ V₁ : PositiveVolumeForm (𝓡 4) M)
    (hpos : ∀ x : M, ∃ a : ℝ, 0 < a ∧ V₁.Ω.1 x = a • V₀.Ω.1 x) :
    ∃ (c : ℝ) (β : TauCeti.SmoothForm (𝓡 4) M ℝ 3),
      0 < c ∧
      Function.Bijective
        (TauCeti.compactlySupportedDeRhamCohomology.integral V₀.orientation) ∧
      TauCeti.mextDerivₗ (𝓡 4) 3 β = V₁.Ω - c • V₀.Ω := by
  have hbij : Function.Bijective
      (TauCeti.compactlySupportedDeRhamCohomology.integral V₀.orientation) :=
    TauCeti.compactlySupportedDeRhamCohomology.bijective_integral V₀.orientation
  have hI₀ : 0 < TauCeti.integralTopForm V₀.orientation V₀.Ω.1 :=
    integralTopForm_self_pos V₀
  have hI₁ : 0 < TauCeti.integralTopForm V₀.orientation V₁.Ω.1 :=
    integralTopForm_pos_of_pos_cooriented V₀ V₁ hpos
  let c : ℝ :=
    TauCeti.integralTopForm V₀.orientation V₁.Ω.1 /
      TauCeti.integralTopForm V₀.orientation V₀.Ω.1
  have hc_pos : 0 < c := div_pos hI₁ hI₀
  let bE : Module.Basis (Fin 4) ℝ (EuclideanSpace ℝ (Fin 4)) :=
    (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis
  have hint (φ : TauCeti.SmoothForm (𝓡 4) M ℝ 4) : TauCeti.IntegrableTopForm φ.1 :=
    (φ.isSmoothForm.of_le bot_le).integrableTopForm
      (isCompact_univ.of_isClosed_subset
        (_root_.isClosed_tsupport (α := EuclideanSpace ℝ (Fin 4) [⋀^Fin 4]→L[ℝ] ℝ) _)
        (Set.subset_univ _))
      bE
  have hint_zero : TauCeti.integralTopForm V₀.orientation (V₁.Ω - c • V₀.Ω).1 = 0 := by
    change TauCeti.integralTopForm V₀.orientation (V₁.Ω.1 - (c • V₀.Ω).1) = 0
    rw [TauCeti.integralTopForm_sub_of_integrable V₀.orientation (hint V₁.Ω) (hint (c • V₀.Ω)),
      TauCeti.SmoothForm.smul_toRoughForm, TauCeti.integralTopForm_smul]
    dsimp only [c]
    rw [div_mul_cancel₀ _ hI₀.ne', sub_self]
  have hcs : V₁.Ω - c • V₀.Ω ∈ TauCeti.compactlySupportedForms (𝓡 4) M 4 := by
    rw [TauCeti.compactlySupportedForms_eq_top]
    trivial
  have hexact : V₁.Ω - c • V₀.Ω ∈ TauCeti.exactCompactlySupportedForms (𝓡 4) M 4 :=
    (TauCeti.mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero
      V₀.orientation hcs).mpr hint_zero
  rw [TauCeti.exactCompactlySupportedForms_succ, Submodule.mem_map] at hexact
  obtain ⟨β, _, hβ⟩ := hexact
  exact ⟨c, β, hc_pos, hbij, hβ⟩

end ConnectedDeRham

/-! ## 3. Global Moser Time-Dependent Flow & Connected Moser Theorem -/

section GlobalMoserFlow

/-- Smooth scalar map `(t, x) ↦ moserTimeCutoff t` on `ℝ × M`. -/
noncomputable def moserTimeCutoffMap
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] :
    C^∞⟮𝓘(ℝ, ℝ).prod (𝓡 4), ℝ × M; ℝ⟯ :=
  ⟨fun p ↦ moserTimeCutoff p.1, contDiff_moserTimeCutoff.contMDiff.comp contMDiff_fst⟩

/-- Smooth time-dependent `4`-form family `α` on `ℝ × M` interpolating between
`SmoothForm.funSMulₗ c_loc V₀.Ω` at `t = 0` and `V₁.Ω` at `t = 1` via `moserTimeCutoff`. -/
noncomputable def moserSpacetimeForm
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    (V₀ V₁ : PositiveVolumeForm (𝓡 4) M) (c_loc : C^∞⟮𝓡 4, M; ℝ⟯) :
    TauCeti.SmoothForm (𝓘(ℝ, ℝ).prod (𝓡 4)) (ℝ × M) ℝ 4 :=
  let Ω_base := TauCeti.SmoothForm.funSMulₗ c_loc V₀.Ω
  TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd Ω_base +
    TauCeti.SmoothForm.funSMulₗ (moserTimeCutoffMap M)
      (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd (V₁.Ω - Ω_base))

/-- Slice of `moserSpacetimeForm V₀ V₁ c_loc` at time `t : ℝ`:
`(ι_t^* α)_x = (c_loc • V₀.Ω)_x + moserTimeCutoff t • (V₁.Ω - c_loc • V₀.Ω)_x`. -/
-- tier: T2
theorem mpullback_prodMk_moserSpacetimeForm
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    (V₀ V₁ : PositiveVolumeForm (𝓡 4) M) (c_loc : C^∞⟮𝓡 4, M; ℝ⟯) (t : ℝ) :
    TauCeti.mpullback (𝓡 4) (𝓘(ℝ, ℝ).prod (𝓡 4)) (Prod.mk t)
        (moserSpacetimeForm V₀ V₁ c_loc).1 =
      (TauCeti.SmoothForm.funSMulₗ c_loc V₀.Ω).1 +
        moserTimeCutoff t • (V₁.Ω - TauCeti.SmoothForm.funSMulₗ c_loc V₀.Ω).1 := by
  let Ω_base := TauCeti.SmoothForm.funSMulₗ c_loc V₀.Ω
  have hι : ContMDiff (𝓡 4) (𝓘(ℝ, ℝ).prod (𝓡 4)) ∞ (Prod.mk t : M → ℝ × M) :=
    contMDiff_const.prodMk contMDiff_id
  have hpull (η : TauCeti.SmoothForm (𝓡 4) M ℝ 4) :
      TauCeti.mpullback (𝓡 4) (𝓘(ℝ, ℝ).prod (𝓡 4)) (Prod.mk t)
        (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd η).1 = η.1 := by
    have hs : TauCeti.SmoothForm.mpullback (Prod.mk t) hι
        (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd η) = η := by
      rw [TauCeti.SmoothForm.mpullback_mpullback]
      have hcongr : TauCeti.SmoothForm.mpullback (Prod.snd ∘ Prod.mk t)
            (contMDiff_snd.comp hι) η =
          TauCeti.SmoothForm.mpullback id contMDiff_id η := rfl
      rw [hcongr, TauCeti.SmoothForm.mpullback_id]
      rfl
    simpa only [TauCeti.SmoothForm.coe_mpullback] using congrArg Subtype.val hs
  rw [moserSpacetimeForm, Submodule.coe_add, TauCeti.SmoothForm.coe_funSMulₗ,
    TauCeti.mpullback_add, TauCeti.mpullback_fun_smul, hpull Ω_base, hpull (V₁.Ω - Ω_base)]
  rfl

/-- Pointwise evaluation of the slice `ι_t^* (moserSpacetimeForm V₀ V₁ c_loc)` as a positive
multiple of `V₀.Ω.1 x`. -/
-- tier: T1
theorem mpullback_prodMk_moserSpacetimeForm_apply_eq_smul
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    (V₀ V₁ : PositiveVolumeForm (𝓡 4) M) (c_loc : C^∞⟮𝓡 4, M; ℝ⟯) (t : ℝ) (x : M) :
    TauCeti.mpullback (𝓡 4) (𝓘(ℝ, ℝ).prod (𝓡 4)) (Prod.mk t)
        (moserSpacetimeForm V₀ V₁ c_loc).1 x =
      ((1 - moserTimeCutoff t) * c_loc x +
          moserTimeCutoff t * (divVolume V₀.Ω V₀.Ω_ne_zero V₁.Ω) x) •
        V₀.Ω.1 x := by
  rw [mpullback_prodMk_moserSpacetimeForm]
  ext v
  have hf := DFunLike.congr_fun (divVolume_apply_smul V₀.Ω V₀.Ω_ne_zero V₁.Ω x) v
  simp only [Pi.add_apply, Pi.smul_apply, Submodule.coe_sub, Pi.sub_apply,
    TauCeti.SmoothForm.coe_funSMulₗ, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.sub_apply,
    smul_eq_mul] at hf ⊢
  rw [← hf]
  ring

/-- Time-derivative slice identity for `moserSpacetimeForm`:
`ι_t^* (L_{∂_t} α) = deriv moserTimeCutoff t • (V₁.Ω - c_loc • V₀.Ω)`. -/
-- tier: T2
theorem mpullback_prodMk_timeDeriv_moserSpacetimeForm
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    (V₀ V₁ : PositiveVolumeForm (𝓡 4) M) (c_loc : C^∞⟮𝓡 4, M; ℝ⟯) (t : ℝ) :
    TauCeti.mpullback (𝓡 4) (𝓘(ℝ, ℝ).prod (𝓡 4)) (Prod.mk t)
        (TauCeti.mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 4))))
          (moserSpacetimeForm V₀ V₁ c_loc).1) =
      deriv moserTimeCutoff t • (V₁.Ω - TauCeti.SmoothForm.funSMulₗ c_loc V₀.Ω).1 := by
  let α := moserSpacetimeForm V₀ V₁ c_loc
  let Ω_base := TauCeti.SmoothForm.funSMulₗ c_loc V₀.Ω
  let Δ := (V₁.Ω - Ω_base).1
  funext x
  let ω₀ : EuclideanSpace ℝ (Fin 4) [⋀^Fin 4]→L[ℝ] ℝ := Ω_base.1 x
  let δ₀ : EuclideanSpace ℝ (Fin 4) [⋀^Fin 4]→L[ℝ] ℝ := Δ x
  have hd1 := TauCeti.hasDerivAt_mpullback_prodMk (I := 𝓡 4) t x (α.mdifferentiableAt (t, x))
  have hd2 :=
    (hasDerivAt_const (F := EuclideanSpace ℝ (Fin 4) [⋀^Fin 4]→L[ℝ] ℝ) t ω₀).add
      ((hasDerivAt_moserTimeCutoff t).smul_const δ₀)
  have hd2' := hd2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u ↦
    congrFun (mpullback_prodMk_moserSpacetimeForm V₀ V₁ c_loc u) x)
  have huniq := hd1.unique hd2'
  rw [zero_add] at huniq
  ext v
  exact DFunLike.congr_fun huniq v

/-- Smooth time-dependent Moser vector field on `ℝ × M`:
`X_t(x) = (-deriv τ(t) / ((1 - τ(t)) c_loc(x) + τ(t) (V₁ / V₀)(x))) • X₀(x)`,
where `ι_{X₀} V₀.Ω = β`. -/
noncomputable def moserVectorField
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    (V₀ V₁ : PositiveVolumeForm (𝓡 4) M) (c_loc : C^∞⟮𝓡 4, M; ℝ⟯)
    (β : TauCeti.SmoothForm (𝓡 4) M ℝ 3) (t : ℝ) (x : M) : TangentSpace (𝓡 4) x :=
  ((-deriv moserTimeCutoff t) /
      ((1 - moserTimeCutoff t) * c_loc x +
        moserTimeCutoff t * (divVolume V₀.Ω V₀.Ω_ne_zero V₁.Ω) x)) •
    vectorFieldOfSubTopForm V₀.Ω β x

/-- Joint `C^∞` smoothness of `moserVectorField` on `ℝ × M` whenever `0 < c_loc x` and `V₁` is
positively co-oriented with `V₀`. -/
-- tier: T2
theorem contMDiff_moserVectorField
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    (V₀ V₁ : PositiveVolumeForm (𝓡 4) M)
    (hpos : ∀ x : M, ∃ a : ℝ, 0 < a ∧ V₁.Ω.1 x = a • V₀.Ω.1 x)
    (c_loc : C^∞⟮𝓡 4, M; ℝ⟯) (hc_pos : ∀ x : M, 0 < c_loc x)
    (β : TauCeti.SmoothForm (𝓡 4) M ℝ 3) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 4)) (𝓡 4).tangent ∞
      (fun p : ℝ × M ↦
        (⟨p.2, moserVectorField V₀ V₁ c_loc β p.1 p.2⟩ : TangentBundle (𝓡 4) M)) := by
  let f_rat := divVolume V₀.Ω V₀.Ω_ne_zero V₁.Ω
  have hτ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 4)) 𝓘(ℝ) ∞ (fun p : ℝ × M ↦ moserTimeCutoff p.1) :=
    contDiff_moserTimeCutoff.contMDiff.comp contMDiff_fst
  have hdτ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 4)) 𝓘(ℝ) ∞
      (fun p : ℝ × M ↦ -deriv moserTimeCutoff p.1) :=
    (contDiff_deriv_moserTimeCutoff.neg.contMDiff).comp contMDiff_fst
  have hden : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 4)) 𝓘(ℝ) ∞
      (fun p : ℝ × M ↦
        (1 - moserTimeCutoff p.1) * c_loc p.2 + moserTimeCutoff p.1 * f_rat p.2) :=
    ((contMDiff_const.sub hτ).mul (c_loc.contMDiff.comp contMDiff_snd)).add
      (hτ.mul (f_rat.contMDiff.comp contMDiff_snd))
  have hden_ne : ∀ p : ℝ × M,
      (1 - moserTimeCutoff p.1) * c_loc p.2 + moserTimeCutoff p.1 * f_rat p.2 ≠ 0 :=
    fun p ↦ (moserConvex_pos (hc_pos p.2) (divVolume_pos_of_pos_cooriented V₀ V₁ hpos p.2) p.1).ne'
  have hcoeff : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 4)) 𝓘(ℝ) ∞
      (fun p : ℝ × M ↦
        (-deriv moserTimeCutoff p.1) /
          ((1 - moserTimeCutoff p.1) * c_loc p.2 + moserTimeCutoff p.1 * f_rat p.2)) :=
    hdτ.div₀ hden hden_ne
  have hX₀_sec := contMDiff_vectorFieldOfSubTopForm V₀.Ω V₀.Ω_ne_zero β
  intro p₀
  rw [contMDiffAt_totalSpace_iff]
  refine ⟨contMDiffAt_snd, ?_⟩
  let e := trivializationAt (EuclideanSpace ℝ (Fin 4)) (TangentSpace (𝓡 4)) p₀.2
  have hp₀_base : p₀.2 ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p₀.2
  have hX₀_pull : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 4)) (𝓡 4).tangent ∞
      (fun p : ℝ × M ↦ (⟨p.2, vectorFieldOfSubTopForm V₀.Ω β p.2⟩ : TangentBundle (𝓡 4) M)) p₀ :=
    (hX₀_sec p₀.2).comp p₀ contMDiffAt_snd
  rw [contMDiffAt_totalSpace_iff] at hX₀_pull
  refine ((hcoeff p₀).smul hX₀_pull.2).congr_of_eventuallyEq ?_
  filter_upwards [continuous_snd.continuousAt (e.open_baseSet.mem_nhds hp₀_base)] with p hp
  exact (e.linear ℝ hp).map_smul _ _

/-- Pointwise interior contraction identity for `moserVectorField`:
`ι_{X_t} Ω_t = -deriv moserTimeCutoff t • β`. -/
-- tier: T2
theorem interior_moserVectorField_eq
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    (V₀ V₁ : PositiveVolumeForm (𝓡 4) M)
    (hpos : ∀ x : M, ∃ a : ℝ, 0 < a ∧ V₁.Ω.1 x = a • V₀.Ω.1 x)
    (c_loc : C^∞⟮𝓡 4, M; ℝ⟯) (hc_pos : ∀ x : M, 0 < c_loc x)
    (β : TauCeti.SmoothForm (𝓡 4) M ℝ 3) (t : ℝ) :
    TauCeti.RoughForm.interior (moserVectorField V₀ V₁ c_loc β t)
        (TauCeti.mpullback (𝓡 4) (𝓘(ℝ, ℝ).prod (𝓡 4)) (Prod.mk t)
          (moserSpacetimeForm V₀ V₁ c_loc).1) =
      ((-deriv moserTimeCutoff t) • β).1 := by
  funext x
  ext w
  rw [TauCeti.RoughForm.interior_apply,
    mpullback_prodMk_moserSpacetimeForm_apply_eq_smul V₀ V₁ c_loc t x,
    moserVectorField, ContinuousAlternatingMap.smul_apply, map_vecCons_smul_slot0]
  have hden_ne :
      (1 - moserTimeCutoff t) * c_loc x +
        moserTimeCutoff t * (divVolume V₀.Ω V₀.Ω_ne_zero V₁.Ω) x ≠ 0 :=
    (moserConvex_pos (hc_pos x) (divVolume_pos_of_pos_cooriented V₀ V₁ hpos x) t).ne'
  have hX₀ : V₀.Ω.1 x (Matrix.vecCons (vectorFieldOfSubTopForm V₀.Ω β x) w) = β.1 x w := by
    simpa only [TauCeti.RoughForm.interior_apply] using
      DFunLike.congr_fun (congrFun (interior_vectorFieldOfSubTopForm V₀.Ω V₀.Ω_ne_zero β) x) w
  rw [hX₀]
  simp only [TauCeti.SmoothForm.smul_toRoughForm, Pi.smul_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  field_simp [hden_ne]

/-- **Master Global Moser Flow Theorem from a `3`-Form Primitive**:
Given positively co-oriented `V₀, V₁`, a smooth positive scaling function `c_loc : C^∞⟮𝓡 4, M; ℝ⟯`,
and a smooth `3`-form `β` satisfying `dβ = V₁.Ω - SmoothForm.funSMulₗ c_loc V₀.Ω` on a compact
Hausdorff smooth 4-manifold `M` (requiring **zero** connectedness assumption), the Moser flow
produces a smooth isotopy `H_iso : ℝ → (M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M)` (`H_iso 0 = refl`, `H_iso 1 = ψ`)
preserving every connected component of `M` and satisfying
`ψ^* V₁.Ω = SmoothForm.funSMulₗ c_loc V₀.Ω`. -/
-- tier: T2
theorem exists_moserDiffeomorph_of_primitive
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
    (V₀ V₁ : PositiveVolumeForm (𝓡 4) M)
    (hpos : ∀ x : M, ∃ a : ℝ, 0 < a ∧ V₁.Ω.1 x = a • V₀.Ω.1 x)
    (c_loc : C^∞⟮𝓡 4, M; ℝ⟯) (hc_pos : ∀ x : M, 0 < c_loc x)
    (β : TauCeti.SmoothForm (𝓡 4) M ℝ 3)
    (hβ : TauCeti.mextDerivₗ (𝓡 4) 3 β = V₁.Ω - TauCeti.SmoothForm.funSMulₗ c_loc V₀.Ω) :
    ∃ (ψ : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M) (H_iso : ℝ → (M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M)),
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 4)) (𝓡 4) ∞ (fun p : ℝ × M ↦ H_iso p.1 p.2) ∧
      H_iso 0 = Diffeomorph.refl (𝓡 4) M ∞ ∧
      H_iso 1 = ψ ∧
      (∀ x : M, connectedComponent (ψ x) = connectedComponent x) ∧
      (∀ x : M, connectedComponent (ψ.symm x) = connectedComponent x) ∧
      TauCeti.SmoothForm.mpullback ψ ψ.contMDiff V₁.Ω =
        TauCeti.SmoothForm.funSMulₗ c_loc V₀.Ω := by
  let X := moserVectorField V₀ V₁ c_loc β
  have hX_inf := contMDiff_moserVectorField V₀ V₁ hpos c_loc hc_pos β
  have hX_two := hX_inf.of_le (m := 2) (by simp)
  have hc : TauCeti.IsCompleteVectorField (TauCeti.timeDependentSuspensionField X) :=
    TauCeti.isCompleteVectorField_timeDependentSuspensionField
      (hX_inf.of_le (by simp)) isCompact_univ (fun _ _ hy ↦ (hy (Set.mem_univ _)).elim)
  let H_iso (t : ℝ) : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M :=
    TauCeti.timeDependentFlowDiffeomorph hc (n := ⊤) le_top hX_inf 0 t
  let ψ : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M := H_iso 1
  have hH_coe : (fun p : ℝ × M ↦ H_iso p.1 p.2) =
      fun p : ℝ × M ↦ TauCeti.timeDependentFlowOf X 0 p.1 p.2 :=
    funext fun p ↦ TauCeti.timeDependentFlowDiffeomorph_apply hc le_top hX_inf 0 p.1 p.2
  have hH_smooth : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 4)) (𝓡 4) ∞ (fun p : ℝ × M ↦ H_iso p.1 p.2) := by
    rw [hH_coe]
    have hflow := TauCeti.contMDiff_timeDependentFlowOf hc (n := ⊤) (by simp) hX_inf
    exact hflow.comp (((contMDiff_const (c := (0 : ℝ))).prodMk contMDiff_fst).prodMk contMDiff_snd)
  have hH0 : H_iso 0 = Diffeomorph.refl (𝓡 4) M ∞ := by
    ext x
    change H_iso 0 x = x
    exact (TauCeti.timeDependentFlowDiffeomorph_apply hc le_top hX_inf 0 0 x).trans
      (TauCeti.timeDependentFlowOf_self X 0 x)
  have hcomp_pres : ∀ x : M, connectedComponent (ψ x) = connectedComponent x := by
    intro x
    let γ : ℝ → M := fun t ↦ H_iso t x
    have hγ_cont : Continuous γ :=
      hH_smooth.continuous.comp (continuous_id.prodMk continuous_const)
    have hpre : IsPreconnected (γ '' Set.Icc (0 : ℝ) 1) :=
      isPreconnected_Icc.image γ hγ_cont.continuousOn
    have hx0 : x ∈ γ '' Set.Icc (0 : ℝ) 1 :=
      ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [γ, hH0]⟩
    have hx1 : ψ x ∈ γ '' Set.Icc (0 : ℝ) 1 :=
      ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
    exact (connectedComponent_eq (hpre.subset_connectedComponent hx0 hx1)).symm
  have hcomp_symm : ∀ x : M, connectedComponent (ψ.symm x) = connectedComponent x := by
    intro x
    have h := (hcomp_pres (ψ.symm x)).symm
    rwa [ψ.apply_symm_apply] at h
  let α := moserSpacetimeForm V₀ V₁ c_loc
  have hL : ∀ t : ℝ,
      TauCeti.mpullback (𝓡 4) (𝓘(ℝ, ℝ).prod (𝓡 4)) (Prod.mk t)
          (TauCeti.mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 4)))) α.1) +
        TauCeti.mlieDerivForm (X t)
          (TauCeti.mpullback (𝓡 4) (𝓘(ℝ, ℝ).prod (𝓡 4)) (Prod.mk t) α.1) = 0 := by
    intro t
    let hι : ContMDiff (𝓡 4) (𝓘(ℝ, ℝ).prod (𝓡 4)) ∞ (Prod.mk t : M → ℝ × M) :=
      contMDiff_const.prodMk contMDiff_id
    let α_t : TauCeti.SmoothForm (𝓡 4) M ℝ 4 := TauCeti.SmoothForm.mpullback (Prod.mk t) hι α
    have hα_t_coe :
        α_t.1 = TauCeti.mpullback (𝓡 4) (𝓘(ℝ, ℝ).prod (𝓡 4)) (Prod.mk t) α.1 :=
      TauCeti.SmoothForm.coe_mpullback _ _ _
    have hXt : MDifferentiable (𝓡 4) (𝓡 4).tangent
        (fun y ↦ (⟨y, X t y⟩ : TangentBundle (𝓡 4) M)) :=
      (hX_inf.comp ((contMDiff_const (c := t)).prodMk contMDiff_id)).mdifferentiable (by simp)
    have hd_top : TauCeti.mextDeriv α_t.1 = 0 :=
      (TauCeti.SmoothForm.isClosed_def α_t).mp
        (TauCeti.SmoothForm.isClosed_of_finrank_le finrank_euclideanSpace_fin.le α_t)
    have hcartan : TauCeti.mlieDerivForm (X t) α_t.1 =
        TauCeti.mextDeriv (TauCeti.RoughForm.interior (X t) α_t.1) :=
      TauCeti.mlieDerivForm_eq_mextDeriv_interior α_t.mdifferentiable hXt hd_top
    rw [← hα_t_coe, mpullback_prodMk_timeDeriv_moserSpacetimeForm V₀ V₁ c_loc t, hcartan,
      hα_t_coe, interior_moserVectorField_eq V₀ V₁ hpos c_loc hc_pos β t,
      ← TauCeti.mextDerivₗ_apply (𝓡 4) 3 ((-deriv moserTimeCutoff t) • β),
      LinearMap.map_smul, hβ, TauCeti.SmoothForm.smul_toRoughForm, neg_smul, add_neg_cancel]
  have hm := TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_eq hX_two hc
    (α.contMDiff.of_le (by simp)) hL 0 1
  have hslice1 :
      TauCeti.mpullback (𝓡 4) (𝓘(ℝ, ℝ).prod (𝓡 4)) (Prod.mk 1) α.1 = V₁.Ω.1 := by
    rw [mpullback_prodMk_moserSpacetimeForm, moserTimeCutoff_one, one_smul,
      Submodule.coe_sub, add_sub_cancel]
  have hslice0 :
      TauCeti.mpullback (𝓡 4) (𝓘(ℝ, ℝ).prod (𝓡 4)) (Prod.mk 0) α.1 =
        (TauCeti.SmoothForm.funSMulₗ c_loc V₀.Ω).1 := by
    rw [mpullback_prodMk_moserSpacetimeForm, moserTimeCutoff_zero, zero_smul, add_zero]
  rw [hslice1, hslice0] at hm
  have hψ_coe : (⇑ψ : M → M) = TauCeti.timeDependentFlowOf X 0 1 :=
    funext fun x ↦ TauCeti.timeDependentFlowDiffeomorph_apply hc le_top hX_inf 0 1 x
  have hpul : TauCeti.SmoothForm.mpullback ψ ψ.contMDiff V₁.Ω =
      TauCeti.SmoothForm.funSMulₗ c_loc V₀.Ω := by
    apply Subtype.ext
    rw [TauCeti.SmoothForm.coe_mpullback, hψ_coe]
    exact hm
  exact ⟨ψ, H_iso, hH_smooth, hH0, rfl, hcomp_pres, hcomp_symm, hpul⟩

/-- **Moser's Volume Theorem on Compact Connected Smooth 4-Manifolds (`Moser 1965`)**:
On a compact connected Hausdorff smooth boundaryless 4-manifold `M`, for any two positively
co-oriented `PositiveVolumeForm`s `V₀, V₁`, there exist `c > 0`, a smooth diffeomorphism
`ψ : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M`, and a smooth isotopy `H_iso : ℝ → (M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M)` from `id` to `ψ`
such that `ψ^* V₁.Ω = c • V₀.Ω`. -/
-- tier: T2
theorem exists_moser_diffeomorph_connected
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [T2Space M] [ConnectedSpace M]
    (V₀ V₁ : PositiveVolumeForm (𝓡 4) M)
    (hpos : ∀ x : M, ∃ a : ℝ, 0 < a ∧ V₁.Ω.1 x = a • V₀.Ω.1 x) :
    ∃ (c : ℝ) (ψ : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M) (H_iso : ℝ → (M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M)),
      0 < c ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 4)) (𝓡 4) ∞ (fun p : ℝ × M ↦ H_iso p.1 p.2) ∧
      H_iso 0 = Diffeomorph.refl (𝓡 4) M ∞ ∧
      H_iso 1 = ψ ∧
      TauCeti.SmoothForm.mpullback ψ ψ.contMDiff V₁.Ω = c • V₀.Ω := by
  obtain ⟨c, β, hc_pos, _, hβ⟩ := exists_primitive_of_pos_cooriented_connected V₀ V₁ hpos
  let cMap : C^∞⟮𝓡 4, M; ℝ⟯ := ContMDiffMap.C c
  have hsmul_eq : TauCeti.SmoothForm.funSMulₗ cMap V₀.Ω = c • V₀.Ω := by
    apply Subtype.ext
    funext x
    rw [TauCeti.SmoothForm.coe_funSMulₗ, TauCeti.SmoothForm.smul_toRoughForm]
    rfl
  obtain ⟨ψ, H_iso, hH_smooth, hH0, hH1, _, _, hpul⟩ :=
    exists_moserDiffeomorph_of_primitive V₀ V₁ hpos cMap (fun _ ↦ hc_pos) β
      (hsmul_eq.symm ▸ hβ)
  exact ⟨c, ψ, H_iso, hc_pos, hH_smooth, hH0, hH1, hpul.trans hsmul_eq⟩

end GlobalMoserFlow

/-! ## 4. Clopen Connected-Component Lift (`MoserVolume`, Zero `ConnectedSpace` Assumption) -/

section ClopenComponentMoser

/-- Every connected component of a space charted over `EuclideanSpace ℝ (Fin 4)` is open (since
Euclidean coordinate balls are open and preconnected). -/
-- tier: T2
theorem isOpen_connectedComponent_manifold
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] (x : M) :
    IsOpen (connectedComponent x) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  let e := chartAt (EuclideanSpace ℝ (Fin 4)) y
  have hy_src : y ∈ e.source := mem_chart_source _ y
  have hy_tgt : e y ∈ e.target := e.map_source hy_src
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp e.open_target (e y) hy_tgt
  let B : Set (EuclideanSpace ℝ (Fin 4)) := Metric.ball (e y) r
  let U : Set M := e.symm '' B
  have hU_open : IsOpen U := by
    have hpre : e.symm '' (e.target ∩ B) = e.source ∩ e ⁻¹' B := by
      ext z
      constructor
      · rintro ⟨w, ⟨hw_t, hw_B⟩, rfl⟩
        refine ⟨e.map_target hw_t, ?_⟩
        rw [Set.mem_preimage, e.right_inv hw_t]
        exact hw_B
      · rintro ⟨hz_s, hz_B⟩
        exact ⟨e z, ⟨e.map_source hz_s, hz_B⟩, e.left_inv hz_s⟩
    rw [show U = e.symm '' (e.target ∩ B) by rw [Set.inter_eq_self_of_subset_right hr_sub], hpre]
    exact e.continuousOn_toFun.isOpen_inter_preimage e.open_source Metric.isOpen_ball
  have hy_U : y ∈ U := ⟨e y, Metric.mem_ball_self hr_pos, e.left_inv hy_src⟩
  have hU_pre : IsPreconnected U :=
    (convex_ball (e y) r).isPreconnected.image e.symm
      (e.continuousOn_invFun.mono hr_sub)
  have hU_sub : U ⊆ connectedComponent x := by
    rw [connectedComponent_eq hy]
    exact hU_pre.subset_connectedComponent hy_U
  exact Filter.mem_of_superset (hU_open.mem_nhds hy_U) hU_sub

private theorem preimage_connectedComponentsMk_eq {M : Type*} [TopologicalSpace M] (x : M) :
    ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk x} = connectedComponent x := by
  ext y
  simp only [Set.mem_preimage, Set.mem_singleton_iff, ConnectedComponents.coe_eq_coe]
  exact ⟨fun h ↦ h ▸ mem_connectedComponent, fun h ↦ (connectedComponent_eq h).symm⟩

/-- Clopen connected component `ConnectedComponents.mk ⁻¹' {q}` packaged as an `Opens M`
submanifold. -/
def connectedComponentOpen
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (q : ConnectedComponents M) : Opens M :=
  ⟨ConnectedComponents.mk ⁻¹' {q}, by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe q
    rw [preimage_connectedComponentsMk_eq x]
    exact isOpen_connectedComponent_manifold x⟩

/-- Every `connectedComponentOpen q` is closed in `M` (hence compact when `[CompactSpace M]`). -/
-- tier: T1
theorem isClosed_connectedComponentOpen
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (q : ConnectedComponents M) :
    IsClosed (connectedComponentOpen q).1 := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe q
  change IsClosed (ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk x})
  rw [preimage_connectedComponentsMk_eq x]
  exact isClosed_connectedComponent

/-- Every `connectedComponentOpen q` is a `ConnectedSpace`. -/
-- tier: T1
instance instConnectedSpaceConnectedComponentOpen
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (q : ConnectedComponents M) :
    ConnectedSpace (connectedComponentOpen q) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe q
  refine Subtype.connectedSpace ?_
  change IsConnected (ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk x})
  rw [preimage_connectedComponentsMk_eq x]
  exact isConnected_connectedComponent

/-- On `[CompactSpace M]`, every `connectedComponentOpen q` is compact. -/
-- tier: T1
instance instCompactSpaceConnectedComponentOpen
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [CompactSpace M]
    (q : ConnectedComponents M) :
    CompactSpace (connectedComponentOpen q) :=
  isCompact_iff_compactSpace.mp (isClosed_connectedComponentOpen q).isCompact

/-- Restrict a `PositiveVolumeForm (𝓡 4) M` to any compact open subset `U : Opens M`
`[CompactSpace U]`. -/
noncomputable def restrictPositiveVolumeForm
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    (V : PositiveVolumeForm (𝓡 4) M) (U : Opens M) [CompactSpace U] :
    PositiveVolumeForm (𝓡 4) U :=
  PositiveVolumeForm.ofSmoothTopForm
    (TauCeti.SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtype_val V.Ω)
    (fun u ↦ by
      intro h0
      apply V.Ω_ne_zero u.1
      ext v
      have hv := DFunLike.congr_fun
        (TauCeti.SmoothForm.coe_mpullback_subtype_val_apply V.Ω u) v
      have h0v : (TauCeti.SmoothForm.mpullback (Subtype.val : U → M)
          contMDiff_subtype_val V.Ω).1 u v = 0 :=
        DFunLike.congr_fun h0 v
      exact hv.symm.trans h0v)

/-- **Componentwise Global Moser Bundle (`SC-R3`, Zero `ConnectedSpace` Assumption)**:
Packages for two positively co-oriented `PositiveVolumeForm`s `V₀, V₁` on a compact Hausdorff
smooth 4-manifold `M` a global `C^∞` diffeomorphism `ψ : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M` preserving every
connected component of `M` together with a locally constant positive smooth scale
`scale : C^∞⟮𝓡 4, M; ℝ⟯` such that `ψ^* V₁.Ω = SmoothForm.funSMulₗ scale V₀.Ω`. -/
structure MoserVolume
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    (V₀ V₁ : PositiveVolumeForm (𝓡 4) M) where
  /-- Global Moser diffeomorphism `ψ : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M`. -/
  ψ : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M
  /-- Smooth isotopy `H_iso : ℝ → (M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M)` from `refl` to `ψ`. -/
  isotopy : ℝ → (M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M)
  /-- Joint `C^∞` smoothness of `(t, x) ↦ isotopy t x`. -/
  contMDiff_isotopy :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 4)) (𝓡 4) ∞ (fun p : ℝ × M ↦ isotopy p.1 p.2)
  /-- `isotopy 0 = Diffeomorph.refl`. -/
  isotopy_zero : isotopy 0 = Diffeomorph.refl (𝓡 4) M ∞
  /-- `isotopy 1 = ψ`. -/
  isotopy_one : isotopy 1 = ψ
  /-- Locally constant positive scaling density `scale : C^∞⟮𝓡 4, M; ℝ⟯`. -/
  scale : C^∞⟮𝓡 4, M; ℝ⟯
  /-- Strict positivity `0 < scale x`. -/
  scale_pos : ∀ x : M, 0 < scale x
  /-- `scale` is constant along every connected component of `M`. -/
  scale_eq_of_connectedComponent :
    ∀ {x y : M}, connectedComponent x = connectedComponent y → scale x = scale y
  /-- `scale` is locally constant (`mvfderiv (𝓡 4) scale x = 0` everywhere). -/
  mvfderiv_scale_eq_zero : ∀ x : M, mvfderiv (𝓡 4) scale x = 0
  /-- `ψ` preserves every connected component of `M`. -/
  connectedComponent_ψ : ∀ x : M, connectedComponent (ψ x) = connectedComponent x
  /-- `ψ.symm` preserves every connected component of `M`. -/
  connectedComponent_ψ_symm : ∀ x : M, connectedComponent (ψ.symm x) = connectedComponent x
  /-- Componentwise Moser pullback law `ψ^* V₁.Ω = SmoothForm.funSMulₗ scale V₀.Ω`. -/
  mpullback_ψ_eq :
    TauCeti.SmoothForm.mpullback ψ ψ.contMDiff V₁.Ω =
      TauCeti.SmoothForm.funSMulₗ scale V₀.Ω

/-- Construct a global `MoserVolume V₀ V₁` bundle on any compact Hausdorff smooth 4-manifold `M`
(with **zero** `[ConnectedSpace M]` assumption) from positive co-orientation
`∀ x, ∃ a > 0, V₁.Ω.1 x = a • V₀.Ω.1 x`. -/
-- tier: T2
noncomputable def MoserVolume.ofPositivelyCooriented
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
    (V₀ V₁ : PositiveVolumeForm (𝓡 4) M)
    (hpos : ∀ x : M, ∃ a : ℝ, 0 < a ∧ V₁.Ω.1 x = a • V₀.Ω.1 x) :
    MoserVolume V₀ V₁ := by
  have hcomp_prim : ∀ q : ConnectedComponents M,
      ∃ (c : ℝ) (β : TauCeti.SmoothForm (𝓡 4) (connectedComponentOpen q) ℝ 3),
        0 < c ∧
        TauCeti.mextDerivₗ (𝓡 4) 3 β =
          (restrictPositiveVolumeForm V₁ (connectedComponentOpen q)).Ω -
            c • (restrictPositiveVolumeForm V₀ (connectedComponentOpen q)).Ω := by
    intro q
    let U := connectedComponentOpen q
    have hpos_U : ∀ u : U, ∃ a : ℝ, 0 < a ∧
        (restrictPositiveVolumeForm V₁ U).Ω.1 u =
          a • (restrictPositiveVolumeForm V₀ U).Ω.1 u := by
      intro u
      obtain ⟨a, ha_pos, ha_eq⟩ := hpos u.1
      refine ⟨a, ha_pos, ?_⟩
      ext v
      have h1 : ((restrictPositiveVolumeForm V₁ U).Ω.1 u v : ℝ) = (V₁.Ω.1 u.1 v : ℝ) :=
        DFunLike.congr_fun (TauCeti.SmoothForm.coe_mpullback_subtype_val_apply V₁.Ω u) v
      have h0 : ((restrictPositiveVolumeForm V₀ U).Ω.1 u v : ℝ) = (V₀.Ω.1 u.1 v : ℝ) :=
        DFunLike.congr_fun (TauCeti.SmoothForm.coe_mpullback_subtype_val_apply V₀.Ω u) v
      have ha_v : (V₁.Ω.1 u.1 v : ℝ) = a • (V₀.Ω.1 u.1 v : ℝ) := by
        rw [ha_eq]
        rfl
      change ((restrictPositiveVolumeForm V₁ U).Ω.1 u v : ℝ) =
        a • ((restrictPositiveVolumeForm V₀ U).Ω.1 u v : ℝ)
      rw [h1, h0, ha_v]
    obtain ⟨c, β, hc_pos, _, hβ⟩ :=
      exists_primitive_of_pos_cooriented_connected
        (restrictPositiveVolumeForm V₀ U) (restrictPositiveVolumeForm V₁ U) hpos_U
    exact ⟨c, β, hc_pos, hβ⟩
  choose c_q β_q hc_q_pos hβ_q using hcomp_prim
  let scaleFun (x : M) : ℝ := c_q (ConnectedComponents.mk x)
  have hscale_ev (x₀ : M) : scaleFun =ᶠ[𝓝 x₀] fun _ ↦ scaleFun x₀ := by
    let U := connectedComponentOpen (ConnectedComponents.mk x₀)
    have hx₀_U : x₀ ∈ U.1 := rfl
    filter_upwards [U.2.mem_nhds hx₀_U] with y hy
    have hmk : ConnectedComponents.mk y = ConnectedComponents.mk x₀ := hy
    dsimp only [scaleFun]
    rw [hmk]
  have hscale_smooth : ContMDiff (𝓡 4) 𝓘(ℝ) ∞ scaleFun :=
    fun x₀ ↦ (contMDiffAt_const (c := scaleFun x₀)).congr_of_eventuallyEq (hscale_ev x₀)
  let scale : C^∞⟮𝓡 4, M; ℝ⟯ := ⟨scaleFun, hscale_smooth⟩
  have hscale_deriv (x₀ : M) : mvfderiv (𝓡 4) scale x₀ = 0 := by
    ext v
    rw [mvfderiv_apply_eq_mfderiv_apply]
    have hmf : mfderiv (𝓡 4) 𝓘(ℝ) scaleFun x₀ =
        mfderiv (𝓡 4) 𝓘(ℝ) (fun _ : M ↦ scaleFun x₀) x₀ :=
      Filter.EventuallyEq.mfderiv_eq (hscale_ev x₀)
    change mfderiv (𝓡 4) 𝓘(ℝ) scaleFun x₀ v = 0
    rw [hmf, mfderiv_const, zero_apply]
  have hscale_comp : ∀ {x y : M}, connectedComponent x = connectedComponent y →
      scale x = scale y := by
    intro x y hxy
    have hmk : ConnectedComponents.mk x = ConnectedComponents.mk y :=
      ConnectedComponents.coe_eq_coe.mpr hxy
    change c_q (ConnectedComponents.mk x) = c_q (ConnectedComponents.mk y)
    rw [hmk]
  let β_raw : TauCeti.RoughForm (𝓡 4) M ℝ 3 := fun x ↦
    show TangentSpace (𝓡 4) x [⋀^Fin 3]→L[ℝ] Bundle.Trivial M ℝ x from
      (β_q (ConnectedComponents.mk x)).1 ⟨x, rfl⟩
  have hβ_pull_eq (q : ConnectedComponents M) :
      TauCeti.mpullback (𝓡 4) (𝓡 4) (Subtype.val : connectedComponentOpen q → M) β_raw =
        (β_q q).1 := by
    funext u
    ext v
    have hsub :
        (show ℝ from TauCeti.mpullback (𝓡 4) (𝓡 4)
          (Subtype.val : connectedComponentOpen q → M) β_raw u v) =
        (show ℝ from β_raw u.1 v) :=
      DFunLike.congr_fun (TauCeti.mpullback_subtype_val_apply β_raw u) v
    refine hsub.trans ?_
    rcases u with ⟨x, hx⟩
    have hx' : ConnectedComponents.mk x = q := hx
    subst hx'
    rfl
  have hβ_smooth : TauCeti.IsSmoothForm (𝓡 4) ∞ β_raw := by
    rw [TauCeti.isSmoothForm_def]
    intro x
    let q := ConnectedComponents.mk x
    let u₀ : connectedComponentOpen q := ⟨x, rfl⟩
    have hloc : TauCeti.IsSmoothForm (𝓡 4) ∞
        (TauCeti.mpullback (𝓡 4) (𝓡 4) (Subtype.val : connectedComponentOpen q → M) β_raw) := by
      rw [hβ_pull_eq q]
      exact (β_q q).isSmoothForm
    exact ((TauCeti.isLocalDiffeomorph_subtype_val (I := 𝓡 4) (n := ∞)
      u₀).contMDiffAt_mpullback_form_iff (by simp)).mp (hloc.contMDiff u₀)
  let β_glob : TauCeti.SmoothForm (𝓡 4) M ℝ 3 := ⟨β_raw, hβ_smooth.mem_smoothBundleForms⟩
  have hβ_glob_pull (q : ConnectedComponents M) :
      TauCeti.SmoothForm.mpullback (Subtype.val : connectedComponentOpen q → M)
        contMDiff_subtype_val β_glob = β_q q :=
    Subtype.ext ((TauCeti.SmoothForm.coe_mpullback _ _ _).trans (hβ_pull_eq q))
  have hβ_glob_d :
      TauCeti.mextDerivₗ (𝓡 4) 3 β_glob = V₁.Ω - TauCeti.SmoothForm.funSMulₗ scale V₀.Ω := by
    refine TauCeti.SmoothBundleForm.ext fun x v ↦ ?_
    let q := ConnectedComponents.mk x
    let U := connectedComponentOpen q
    let u₀ : U := ⟨x, rfl⟩
    let v_U : Fin 4 → TangentSpace (𝓡 4) u₀ := v
    have hpul_d :
        (show ℝ from (TauCeti.SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtype_val
          (TauCeti.mextDerivₗ (𝓡 4) 3 β_glob)).1 u₀ v_U) =
        (show ℝ from ((restrictPositiveVolumeForm V₁ U).Ω -
          c_q q • (restrictPositiveVolumeForm V₀ U).Ω).1 u₀ v_U) := by
      have h1 := congrArg (fun η : TauCeti.SmoothForm (𝓡 4) U ℝ 4 ↦ (η.1 u₀ v_U : ℝ))
        (TauCeti.SmoothForm.mextDerivₗ_mpullback (Subtype.val : U → M) contMDiff_subtype_val 3
          β_glob).symm
      rw [hβ_glob_pull q, hβ_q q] at h1
      exact h1
    have hlhs :
        (show ℝ from (TauCeti.SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtype_val
          (TauCeti.mextDerivₗ (𝓡 4) 3 β_glob)).1 u₀ v_U) =
        (show ℝ from (TauCeti.mextDerivₗ (𝓡 4) 3 β_glob).1 x v) :=
      DFunLike.congr_fun
        (TauCeti.SmoothForm.coe_mpullback_subtype_val_apply
          (TauCeti.mextDerivₗ (𝓡 4) 3 β_glob) u₀) v_U
    have hV₁ :
        (show ℝ from (restrictPositiveVolumeForm V₁ U).Ω.1 u₀ v_U) =
          (show ℝ from V₁.Ω.1 x v) :=
      DFunLike.congr_fun (TauCeti.SmoothForm.coe_mpullback_subtype_val_apply V₁.Ω u₀) v_U
    have hV₀ :
        (show ℝ from (restrictPositiveVolumeForm V₀ U).Ω.1 u₀ v_U) =
          (show ℝ from V₀.Ω.1 x v) :=
      DFunLike.congr_fun (TauCeti.SmoothForm.coe_mpullback_subtype_val_apply V₀.Ω u₀) v_U
    have hrhs_U :
        (show ℝ from ((restrictPositiveVolumeForm V₁ U).Ω -
          c_q q • (restrictPositiveVolumeForm V₀ U).Ω).1 u₀ v_U) =
        (show ℝ from (restrictPositiveVolumeForm V₁ U).Ω.1 u₀ v_U) -
          c_q q * (show ℝ from (restrictPositiveVolumeForm V₀ U).Ω.1 u₀ v_U) := by
      simp only [Submodule.coe_sub, TauCeti.SmoothForm.smul_toRoughForm,
        Pi.sub_apply, Pi.smul_apply, ContinuousAlternatingMap.sub_apply,
        ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    have hrhs_M :
        (show ℝ from (V₁.Ω - TauCeti.SmoothForm.funSMulₗ scale V₀.Ω).1 x v) =
        (show ℝ from V₁.Ω.1 x v) - c_q q * (show ℝ from V₀.Ω.1 x v) := by
      simp only [Submodule.coe_sub, TauCeti.SmoothForm.coe_funSMulₗ,
        Pi.sub_apply, ContinuousAlternatingMap.sub_apply,
        ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      rfl
    change (show ℝ from (TauCeti.mextDerivₗ (𝓡 4) 3 β_glob).1 x v) =
      (show ℝ from (V₁.Ω - TauCeti.SmoothForm.funSMulₗ scale V₀.Ω).1 x v)
    rw [← hlhs, hpul_d, hrhs_U, hV₁, hV₀, hrhs_M]
  have hflow := exists_moserDiffeomorph_of_primitive V₀ V₁ hpos scale (fun x ↦ hc_q_pos _)
    β_glob hβ_glob_d
  let ψ := hflow.choose
  let H_iso := hflow.choose_spec.choose
  have hspec := hflow.choose_spec.choose_spec
  exact
    { ψ := ψ
      isotopy := H_iso
      contMDiff_isotopy := hspec.1
      isotopy_zero := hspec.2.1
      isotopy_one := hspec.2.2.1
      scale := scale
      scale_pos := fun x ↦ hc_q_pos _
      scale_eq_of_connectedComponent := hscale_comp
      mvfderiv_scale_eq_zero := hscale_deriv
      connectedComponent_ψ := hspec.2.2.2.1
      connectedComponent_ψ_symm := hspec.2.2.2.2.1
      mpullback_ψ_eq := hspec.2.2.2.2.2 }

end ClopenComponentMoser

/-! ## 5. Exact Conjugation of Volume Forms, Measures, Poisson Structures & Turing Dynamics -/

namespace MoserVolume

section ExactConjugation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
  {V₀ V₁ : PositiveVolumeForm (𝓡 4) M} (W : MoserVolume V₀ V₁)

/-- Conjugate a global diffeomorphism `d_bar : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M` by `W.ψ`:
`W.conjDiffeomorph d_bar x = W.ψ.symm (d_bar (W.ψ x))`. -/
def conjDiffeomorph (d_bar : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M) : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M :=
  W.ψ.trans (d_bar.trans W.ψ.symm)

/-- Pointwise evaluation of `W.conjDiffeomorph d_bar`. -/
@[simp]
theorem conjDiffeomorph_apply (d_bar : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M) (x : M) :
    W.conjDiffeomorph d_bar x = W.ψ.symm (d_bar (W.ψ x)) :=
  rfl

/-- Smooth inverse scaling density `scale⁻¹ : C^∞⟮𝓡 4, M; ℝ⟯`. -/
def invScale : C^∞⟮𝓡 4, M; ℝ⟯ :=
  ⟨fun x ↦ (W.scale x)⁻¹, W.scale.contMDiff.inv₀ fun x ↦ (W.scale_pos x).ne'⟩

/-- Pointwise evaluation of `W.invScale`. -/
@[simp]
theorem invScale_apply (x : M) : W.invScale x = (W.scale x)⁻¹ :=
  rfl

/-- Inverse pullback identity `(W.ψ.symm)^* V₀.Ω = SmoothForm.funSMulₗ W.invScale V₁.Ω`. -/
-- tier: T2
theorem mpullback_ψ_symm_eq :
    TauCeti.SmoothForm.mpullback W.ψ.symm W.ψ.symm.contMDiff V₀.Ω =
      TauCeti.SmoothForm.funSMulₗ W.invScale V₁.Ω := by
  have hpul := congrArg (TauCeti.SmoothForm.mpullback W.ψ.symm W.ψ.symm.contMDiff) W.mpullback_ψ_eq
  rw [TauCeti.SmoothForm.mpullback_symm_mpullback] at hpul
  refine TauCeti.SmoothBundleForm.ext fun x v ↦ ?_
  have hx := DFunLike.congr_fun (congrFun (congrArg Subtype.val hpul) x) v
  have hrhs :
      (TauCeti.SmoothForm.mpullback W.ψ.symm W.ψ.symm.contMDiff
          (TauCeti.SmoothForm.funSMulₗ W.scale V₀.Ω)).1 x v =
        W.scale x *
          (TauCeti.SmoothForm.mpullback W.ψ.symm W.ψ.symm.contMDiff V₀.Ω).1 x v := by
    rw [TauCeti.SmoothForm.mpullback_apply, TauCeti.SmoothForm.coe_funSMulₗ,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul,
      W.scale_eq_of_connectedComponent (W.connectedComponent_ψ_symm x),
      ← TauCeti.SmoothForm.mpullback_apply W.ψ.symm W.ψ.symm.contMDiff V₀.Ω x v]
  rw [hrhs] at hx
  rw [TauCeti.SmoothForm.coe_funSMulₗ, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    invScale_apply, hx]
  have hne : W.scale x ≠ 0 := (W.scale_pos x).ne'
  field_simp [hne]

/-- **Exact Preservation of the Input Volume Form `V₀.Ω` (`SC-R3`)**:
Whenever `d_bar` preserves `V₁.Ω` under pullback and maps every connected component of `M` to
itself, `W.conjDiffeomorph d_bar` preserves **`V₀.Ω` itself** (`d_exact^* V₀.Ω = V₀.Ω`), requiring
**zero** `[ConnectedSpace M]` assumption! -/
-- tier: T2
theorem mpullback_conjDiffeomorph
    {d_bar : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M}
    (hd_comp : ∀ x : M, connectedComponent (d_bar x) = connectedComponent x)
    (hd_vol : TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V₁.Ω = V₁.Ω) :
    TauCeti.SmoothForm.mpullback (W.conjDiffeomorph d_bar)
        (W.conjDiffeomorph d_bar).contMDiff V₀.Ω = V₀.Ω := by
  unfold conjDiffeomorph
  rw [TauCeti.SmoothForm.mpullback_trans, TauCeti.SmoothForm.mpullback_trans,
    W.mpullback_ψ_symm_eq]
  have hd_step :
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff
          (TauCeti.SmoothForm.funSMulₗ W.invScale V₁.Ω) =
        TauCeti.SmoothForm.funSMulₗ W.invScale V₁.Ω := by
    refine TauCeti.SmoothBundleForm.ext fun y v ↦ ?_
    have hlhs :
        (TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff
            (TauCeti.SmoothForm.funSMulₗ W.invScale V₁.Ω)).1 y v =
          W.invScale (d_bar y) •
            (TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V₁.Ω).1 y v := by
      rw [TauCeti.SmoothForm.mpullback_apply, TauCeti.SmoothForm.coe_funSMulₗ,
        ContinuousAlternatingMap.smul_apply,
        ← TauCeti.SmoothForm.mpullback_apply d_bar d_bar.contMDiff V₁.Ω y v]
    rw [hlhs, hd_vol, TauCeti.SmoothForm.coe_funSMulₗ, ContinuousAlternatingMap.smul_apply]
    have hsc : W.invScale (d_bar y) = W.invScale y :=
      congrArg Inv.inv (W.scale_eq_of_connectedComponent (hd_comp y))
    rw [hsc]
  rw [hd_step]
  refine TauCeti.SmoothBundleForm.ext fun x v ↦ ?_
  have hlhs :
      (TauCeti.SmoothForm.mpullback W.ψ W.ψ.contMDiff
          (TauCeti.SmoothForm.funSMulₗ W.invScale V₁.Ω)).1 x v =
        W.invScale (W.ψ x) •
          (TauCeti.SmoothForm.mpullback W.ψ W.ψ.contMDiff V₁.Ω).1 x v := by
    rw [TauCeti.SmoothForm.mpullback_apply, TauCeti.SmoothForm.coe_funSMulₗ,
      ContinuousAlternatingMap.smul_apply,
      ← TauCeti.SmoothForm.mpullback_apply W.ψ W.ψ.contMDiff V₁.Ω x v]
  rw [hlhs, W.mpullback_ψ_eq, TauCeti.SmoothForm.coe_funSMulₗ,
    ContinuousAlternatingMap.smul_apply]
  have hsc : W.invScale (W.ψ x) = (W.scale x)⁻¹ :=
    congrArg Inv.inv (W.scale_eq_of_connectedComponent (W.connectedComponent_ψ x))
  rw [hsc, smul_smul, inv_mul_cancel₀ (W.scale_pos x).ne', one_smul]

/-- **Exact Borel Measure Preservation (`MeasurePreserving ⇑d_exact V₀.μ V₀.μ`)**:
`W.conjDiffeomorph d_bar` preserves the exact Borel measure `V₀.μ` of the input volume form `V₀`. -/
-- tier: T1
theorem measurePreserving_conjDiffeomorph
    {d_bar : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M}
    (hd_comp : ∀ x : M, connectedComponent (d_bar x) = connectedComponent x)
    (hd_vol : TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V₁.Ω = V₁.Ω) :
    MeasurePreserving ⇑(W.conjDiffeomorph d_bar) V₀.μ V₀.μ :=
  V₀.measurePreserving_of_mpullback_eq (W.conjDiffeomorph d_bar)
    (W.mpullback_conjDiffeomorph hd_comp hd_vol)

/-- **Exact Conjugation of Turing Completeness (`IsTuringComplete`)**:
Since `W.ψ.symm : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M` is an open embedding intertwining `d_bar` with
`W.conjDiffeomorph d_bar`, `IsTuringComplete ⇑d_bar` transfers directly to
`IsTuringComplete ⇑(W.conjDiffeomorph d_bar)` (preserving `RatBox2` open-tube enumerators and
non-repeating forward orbits). -/
-- tier: T1
theorem isTuringComplete_conjDiffeomorph
    {d_bar : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M} (htc : IsTuringComplete ⇑d_bar) :
    IsTuringComplete ⇑(W.conjDiffeomorph d_bar) :=
  htc.of_openEmbedding W.ψ.symm.toHomeomorph.isOpenEmbedding fun y ↦ by
    simp [conjDiffeomorph]

/-- Non-triviality `⇑(W.conjDiffeomorph d_bar) ≠ id` when `IsTuringComplete ⇑d_bar`. -/
-- tier: T1
theorem conjDiffeomorph_ne_id
    {d_bar : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M} (htc : IsTuringComplete ⇑d_bar) :
    (⇑(W.conjDiffeomorph d_bar) : M → M) ≠ id :=
  (W.isTuringComplete_conjDiffeomorph htc).ne_id

/-- Pulled-back volume form `W.ψ^* V₁.Ω` vanishes nowhere on `M`. -/
-- tier: T1
theorem mpullback_ψ_ne_zero (x : M) :
    (TauCeti.SmoothForm.mpullback W.ψ W.ψ.contMDiff V₁.Ω).1 x ≠ 0 := by
  rw [W.mpullback_ψ_eq, TauCeti.SmoothForm.coe_funSMulₗ]
  exact smul_ne_zero (W.scale_pos x).ne' (V₀.Ω_ne_zero x)

/-- **Pulled-Back Unimodular Jacobian–Poisson Structure `ψ^* π_f` (`SC-R3`)**:
Pulls `jacobianPoissonOfPositiveVolume V₁ S2VolumeForm f hf` back along `W.ψ` to the
Jacobian–Poisson structure of `(W.ψ^* V₁.Ω, S2VolumeForm, f ∘ ⇑W.ψ)`, which is globally unimodular
with respect to **`V₀.Ω` itself** because `W.scale` is locally constant! -/
def pullbackJacobianPoisson (f : M → Sphere2) (hf : ContMDiff (𝓡 4) (𝓡 2) ∞ f) :
    PoissonStructure (𝓡 4) M :=
  jacobianPoisson (TauCeti.SmoothForm.mpullback W.ψ W.ψ.contMDiff V₁.Ω) W.mpullback_ψ_ne_zero
    S2VolumeForm (f ∘ ⇑W.ψ) (hf.comp W.ψ.contMDiff)

/-- **Exact Unimodularity with Input Volume `V₀.Ω`**:
`W.pullbackJacobianPoisson f hf` satisfies `IsUnimodularWithVolume V₀.Ω` for the **exact** input
volume form `V₀.Ω` (since `W.scale` is locally constant on `M`, so `X_{log scale} = 0`). -/
-- tier: T2
theorem isUnimodularWithVolume_pullbackJacobianPoisson
    (f : M → Sphere2) (hf : ContMDiff (𝓡 4) (𝓡 2) ∞ f) :
    (W.pullbackJacobianPoisson f hf).IsUnimodularWithVolume V₀.Ω := by
  let P := W.pullbackJacobianPoisson f hf
  rw [P.isUnimodularWithVolume_iff_modularDerivation_eq_zero V₀.Ω V₀.Ω_ne_zero]
  have hunim_scaled :
      P.IsUnimodularWithVolume (TauCeti.SmoothForm.funSMulₗ W.scale V₀.Ω) := by
    rw [← W.mpullback_ψ_eq]
    exact isUnimodularWithVolume_jacobianPoisson
      (TauCeti.SmoothForm.mpullback W.ψ W.ψ.contMDiff V₁.Ω) W.mpullback_ψ_ne_zero
      S2VolumeForm (f ∘ ⇑W.ψ) (hf.comp W.ψ.contMDiff)
  have hmod_scaled :=
    (P.isUnimodularWithVolume_iff_modularDerivation_eq_zero
      (TauCeti.SmoothForm.funSMulₗ W.scale V₀.Ω)
      (funSMulₗ_ne_zero V₀.Ω_ne_zero fun x ↦ (W.scale_pos x).ne')).mp hunim_scaled
  rw [P.modularDerivation_funSMul V₀.Ω V₀.Ω_ne_zero W.scale W.scale_pos, sub_eq_zero] at hmod_scaled
  rw [hmod_scaled]
  ext g x
  change (P.toSmoothBivector.bracket g
    ⟨fun y ↦ Real.log (W.scale y), W.scale.contMDiff.log fun y ↦ (W.scale_pos y).ne'⟩) x = 0
  rw [P.toSmoothBivector.bracket_log_right W.scale_pos g x, SmoothBivector.bracket_apply,
    W.mvfderiv_scale_eq_zero x, SmoothBivector.bivector_apply, zero_apply, mul_zero]

/-- `(M, W.pullbackJacobianPoisson f hf)` satisfies `IsUnimodularPoisson`. -/
-- tier: T1
theorem isUnimodularPoisson_pullbackJacobianPoisson
    (f : M → Sphere2) (hf : ContMDiff (𝓡 4) (𝓡 2) ∞ f) :
    (W.pullbackJacobianPoisson f hf).IsUnimodularPoisson :=
  (W.isUnimodularWithVolume_pullbackJacobianPoisson f hf).isUnimodularPoisson

omit [MeasurableSpace M] [BorelSpace M] in
private theorem diffOneForm_mpullback_eq
    (Φ : M → M) (hΦ : ContMDiff (𝓡 4) (𝓡 4) ∞ Φ) (u : C^∞⟮𝓡 4, M; ℝ⟯) :
    TauCeti.SmoothForm.mpullback Φ hΦ (SmoothBivector.diffOneForm u) =
      SmoothBivector.diffOneForm (u.comp ⟨Φ, hΦ⟩) := by
  refine TauCeti.SmoothBundleForm.ext fun x v ↦ ?_
  have hv : v = ![v 0] := funext fun i ↦ by fin_cases i; rfl
  rw [hv, TauCeti.SmoothForm.mpullback_apply_one, SmoothBivector.diffOneForm_apply,
    SmoothBivector.diffOneForm_apply]
  have hud : MDifferentiableAt (𝓡 4) 𝓘(ℝ) u (Φ x) := u.contMDiff.mdifferentiableAt (by simp)
  have hΦd : MDifferentiableAt (𝓡 4) (𝓡 4) Φ x := hΦ.mdifferentiableAt (by simp)
  change mvfderiv (𝓡 4) u (Φ x) (mfderiv (𝓡 4) (𝓡 4) Φ x (v 0)) =
    mvfderiv (𝓡 4) (u ∘ Φ) x (v 0)
  rw [mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply]
  exact (congrArg (· (v 0)) (mfderiv_comp x hud hΦd)).symm

/-- `W.ψ` is a smooth Poisson diffeomorphism from `(M, W.pullbackJacobianPoisson f hf)` to
`(M, jacobianPoissonOfPositiveVolume V₁ S2VolumeForm f hf)`. -/
-- tier: T2
theorem isPoissonMap_ψ (f : M → Sphere2) (hf : ContMDiff (𝓡 4) (𝓡 2) ∞ f) :
    SmoothBivector.IsPoissonMap
      (W.pullbackJacobianPoisson f hf).toSmoothBivector
      (jacobianPoissonOfPositiveVolume V₁ S2VolumeForm f hf).toSmoothBivector
      W.ψ W.ψ.contMDiff := by
  let P_pull := W.pullbackJacobianPoisson f hf
  let P₁ := jacobianPoissonOfPositiveVolume V₁ S2VolumeForm f hf
  let Ω_pull := TauCeti.SmoothForm.mpullback W.ψ W.ψ.contMDiff V₁.Ω
  let ψMap : C^∞⟮𝓡 4, M; 𝓡 4, M⟯ := ⟨W.ψ, W.ψ.contMDiff⟩
  intro g h
  ext x
  have h1 := funSMulₗ_bracket_jacobianPoisson Ω_pull W.mpullback_ψ_ne_zero S2VolumeForm
    (f ∘ ⇑W.ψ) (hf.comp W.ψ.contMDiff) (g.comp ψMap) (h.comp ψMap)
  have h2 := congrArg (TauCeti.SmoothForm.mpullback W.ψ W.ψ.contMDiff)
    (funSMulₗ_bracket_jacobianPoisson V₁.Ω V₁.Ω_ne_zero S2VolumeForm f hf g h)
  have hw1 := TauCeti.SmoothForm.mpullback_wedge (k := 2) (l := 2) W.ψ W.ψ.contMDiff
    (TauCeti.SmoothForm.wedge (SmoothBivector.diffOneForm g) (SmoothBivector.diffOneForm h))
    (TauCeti.SmoothForm.mpullback f hf S2VolumeForm)
  have hw2 := TauCeti.SmoothForm.mpullback_wedge (k := 1) (l := 1) W.ψ W.ψ.contMDiff
    (SmoothBivector.diffOneForm g) (SmoothBivector.diffOneForm h)
  have hbase :
      TauCeti.SmoothForm.mpullback W.ψ W.ψ.contMDiff
          (TauCeti.SmoothForm.mpullback f hf S2VolumeForm) =
        TauCeti.SmoothForm.mpullback (f ∘ ⇑W.ψ) (hf.comp W.ψ.contMDiff) S2VolumeForm := by
    rw [TauCeti.SmoothForm.mpullback_mpullback]
  rw [hw1, hw2, diffOneForm_mpullback_eq W.ψ W.ψ.contMDiff g,
    diffOneForm_mpullback_eq W.ψ W.ψ.contMDiff h, hbase, ← h1] at h2
  have hlhs_x :
      (TauCeti.SmoothForm.mpullback W.ψ W.ψ.contMDiff
          (TauCeti.SmoothForm.funSMulₗ (P₁.bracket g h) V₁.Ω)).1 x =
        (P₁.bracket g h) (W.ψ x) • Ω_pull.1 x := by
    ext v
    rw [TauCeti.SmoothForm.mpullback_apply, TauCeti.SmoothForm.coe_funSMulₗ,
      ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.smul_apply,
      ← TauCeti.SmoothForm.mpullback_apply W.ψ W.ψ.contMDiff V₁.Ω x v]
  have hx_eq :
      (P₁.bracket g h) (W.ψ x) • Ω_pull.1 x =
        (P_pull.bracket (g.comp ψMap) (h.comp ψMap)) x • Ω_pull.1 x := by
    calc
      (P₁.bracket g h) (W.ψ x) • Ω_pull.1 x
        = (TauCeti.SmoothForm.mpullback W.ψ W.ψ.contMDiff
            (TauCeti.SmoothForm.funSMulₗ (P₁.bracket g h) V₁.Ω)).1 x := hlhs_x.symm
      _ = (TauCeti.SmoothForm.funSMulₗ
            (P_pull.bracket (g.comp ψMap) (h.comp ψMap)) Ω_pull).1 x :=
          congrFun (congrArg Subtype.val h2) x
      _ = (P_pull.bracket (g.comp ψMap) (h.comp ψMap)) x • Ω_pull.1 x := by
          rw [TauCeti.SmoothForm.coe_funSMulₗ]
  exact (smul_left_injective ℝ (W.mpullback_ψ_ne_zero x) hx_eq).symm

/-- `W.ψ.symm` is a smooth Poisson diffeomorphism from
`(M, jacobianPoissonOfPositiveVolume V₁ S2VolumeForm f hf)` to
`(M, W.pullbackJacobianPoisson f hf)`. -/
-- tier: T2
theorem isPoissonMap_ψ_symm (f : M → Sphere2) (hf : ContMDiff (𝓡 4) (𝓡 2) ∞ f) :
    SmoothBivector.IsPoissonMap
      (jacobianPoissonOfPositiveVolume V₁ S2VolumeForm f hf).toSmoothBivector
      (W.pullbackJacobianPoisson f hf).toSmoothBivector
      W.ψ.symm W.ψ.symm.contMDiff := by
  intro g h
  let ψMap : C^∞⟮𝓡 4, M; 𝓡 4, M⟯ := ⟨W.ψ, W.ψ.contMDiff⟩
  let ψSymmMap : C^∞⟮𝓡 4, M; 𝓡 4, M⟯ := ⟨W.ψ.symm, W.ψ.symm.contMDiff⟩
  have hg : (g.comp ψSymmMap).comp ψMap = g := by
    ext x
    change g (W.ψ.symm (W.ψ x)) = g x
    rw [W.ψ.symm_apply_apply]
  have hh : (h.comp ψSymmMap).comp ψMap = h := by
    ext x
    change h (W.ψ.symm (W.ψ x)) = h x
    rw [W.ψ.symm_apply_apply]
  have hp := W.isPoissonMap_ψ f hf (g.comp ψSymmMap) (h.comp ψSymmMap)
  rw [hg, hh] at hp
  ext y
  have hy := congrArg (fun u : C^∞⟮𝓡 4, M; ℝ⟯ ↦ u (W.ψ.symm y)) hp.symm
  change (jacobianPoissonOfPositiveVolume V₁ S2VolumeForm f hf).bracket
      (g.comp ψSymmMap) (h.comp ψSymmMap) y =
    (W.pullbackJacobianPoisson f hf).bracket g h (W.ψ.symm y)
  have hlhs :
      (((jacobianPoissonOfPositiveVolume V₁ S2VolumeForm f hf).bracket
        (g.comp ψSymmMap) (h.comp ψSymmMap)).comp ψMap) (W.ψ.symm y) =
      (jacobianPoissonOfPositiveVolume V₁ S2VolumeForm f hf).bracket
        (g.comp ψSymmMap) (h.comp ψSymmMap) y := by
    change (jacobianPoissonOfPositiveVolume V₁ S2VolumeForm f hf).bracket
        (g.comp ψSymmMap) (h.comp ψSymmMap) (W.ψ (W.ψ.symm y)) = _
    rw [W.ψ.apply_symm_apply]
  exact hlhs.symm.trans hy

omit [MeasurableSpace M] [BorelSpace M] in
/-- Composition of two `SmoothBivector.IsPoissonMap`s is a `SmoothBivector.IsPoissonMap`. -/
-- tier: T1
theorem isPoissonMap_comp {B₁ B₂ B₃ : SmoothBivector (𝓡 4) M} {φ₁ φ₂ : M → M}
    (hφ₁ : ContMDiff (𝓡 4) (𝓡 4) ∞ φ₁) (hφ₂ : ContMDiff (𝓡 4) (𝓡 4) ∞ φ₂)
    (hp₁ : SmoothBivector.IsPoissonMap B₁ B₂ φ₁ hφ₁)
    (hp₂ : SmoothBivector.IsPoissonMap B₂ B₃ φ₂ hφ₂) :
    SmoothBivector.IsPoissonMap B₁ B₃ (φ₂ ∘ φ₁) (hφ₂.comp hφ₁) := by
  intro g h
  let m₁ : C^∞⟮𝓡 4, M; 𝓡 4, M⟯ := ⟨φ₁, hφ₁⟩
  let m₂ : C^∞⟮𝓡 4, M; 𝓡 4, M⟯ := ⟨φ₂, hφ₂⟩
  let m₁₂ : C^∞⟮𝓡 4, M; 𝓡 4, M⟯ := ⟨φ₂ ∘ φ₁, hφ₂.comp hφ₁⟩
  have hg : g.comp m₁₂ = (g.comp m₂).comp m₁ := rfl
  have hh : h.comp m₁₂ = (h.comp m₂).comp m₁ := rfl
  rw [hg, hh, hp₁ (g.comp m₂) (h.comp m₂), hp₂ g h]
  rfl

/-- **Exact Poisson Automorphism Conjugation**:
Whenever `d_bar` is a Poisson automorphism of
`jacobianPoissonOfPositiveVolume V₁ S2VolumeForm f hf`, its Moser conjugate
`W.conjDiffeomorph d_bar` is a Poisson automorphism of `W.pullbackJacobianPoisson f hf`. -/
-- tier: T1
theorem isPoissonMap_conjDiffeomorph (f : M → Sphere2) (hf : ContMDiff (𝓡 4) (𝓡 2) ∞ f)
    {d_bar : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M}
    (hpoiss : SmoothBivector.IsPoissonMap
      (jacobianPoissonOfPositiveVolume V₁ S2VolumeForm f hf).toSmoothBivector
      (jacobianPoissonOfPositiveVolume V₁ S2VolumeForm f hf).toSmoothBivector
      d_bar d_bar.contMDiff) :
    SmoothBivector.IsPoissonMap
      (W.pullbackJacobianPoisson f hf).toSmoothBivector
      (W.pullbackJacobianPoisson f hf).toSmoothBivector
      (W.conjDiffeomorph d_bar) (W.conjDiffeomorph d_bar).contMDiff :=
  isPoissonMap_comp W.ψ.contMDiff (d_bar.trans W.ψ.symm).contMDiff (W.isPoissonMap_ψ f hf)
    (isPoissonMap_comp d_bar.contMDiff W.ψ.symm.contMDiff hpoiss (W.isPoissonMap_ψ_symm f hf))

/-- Foliation invariance `(f ∘ ⇑W.ψ) ∘ ⇑(W.conjDiffeomorph d_bar) = f ∘ ⇑W.ψ` whenever
`f ∘ ⇑d_bar = f`. -/
-- tier: T1
theorem fibration_comp_conjDiffeomorph {f : M → Sphere2} {d_bar : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M}
    (hf_comp : f ∘ ⇑d_bar = f) :
    (f ∘ ⇑W.ψ) ∘ ⇑(W.conjDiffeomorph d_bar) = f ∘ ⇑W.ψ := by
  funext x
  simp only [Function.comp_apply, conjDiffeomorph_apply, Diffeomorph.apply_symm_apply]
  exact congrFun hf_comp (W.ψ x)

/-- Critical-point conjugacy `x ∈ criticalPoints (f ∘ ⇑W.ψ) ↔ W.ψ x ∈ criticalPoints f`. -/
-- tier: T1
theorem mem_criticalPoints_comp_ψ_iff (f : M → Sphere2) (hf : ContMDiff (𝓡 4) (𝓡 2) ∞ f)
    (x : M) :
    x ∈ criticalPoints (𝓡 4) (𝓡 2) (f ∘ ⇑W.ψ) ↔ W.ψ x ∈ criticalPoints (𝓡 4) (𝓡 2) f := by
  change ¬ Function.Surjective (mfderiv (𝓡 4) (𝓡 2) (f ∘ ⇑W.ψ) x) ↔
    ¬ Function.Surjective (mfderiv (𝓡 4) (𝓡 2) f (W.ψ x))
  refine not_congr ?_
  rw [mfderiv_comp x (hf.mdifferentiableAt (by simp)) (W.ψ.contMDiff.mdifferentiableAt (by simp))]
  have hsurj_ψ : Function.Surjective (mfderiv (𝓡 4) (𝓡 4) W.ψ x) :=
    ((W.ψ.isLocalDiffeomorph x).isInvertible_mfderiv (by simp)).surjective
  change Function.Surjective (⇑(mfderiv (𝓡 4) (𝓡 2) f (W.ψ x)) ∘ ⇑(mfderiv (𝓡 4) (𝓡 4) W.ψ x)) ↔
    Function.Surjective (mfderiv (𝓡 4) (𝓡 2) f (W.ψ x))
  exact ⟨fun h ↦ h.of_comp, fun h ↦ h.comp hsurj_ψ⟩

/-- Regular rank-`2` characterization for `W.pullbackJacobianPoisson f hf`. -/
-- tier: T1
theorem rankAt_pullbackJacobianPoisson_of_notMem_criticalPoints
    (f : M → Sphere2) (hf : ContMDiff (𝓡 4) (𝓡 2) ∞ f) {x : M}
    (hreg : x ∉ criticalPoints (𝓡 4) (𝓡 2) (f ∘ ⇑W.ψ)) :
    (W.pullbackJacobianPoisson f hf).rankAt x = 2 :=
  rankAt_jacobianPoisson_of_notMem_criticalSet
    (TauCeti.SmoothForm.mpullback W.ψ W.ψ.contMDiff V₁.Ω) W.mpullback_ψ_ne_zero
    S2VolumeForm (f ∘ ⇑W.ψ) (hf.comp W.ψ.contMDiff) hreg (S2VolumeForm_ne_zero _)

/-- Critical rank-`0` characterization for `W.pullbackJacobianPoisson f hf`. -/
-- tier: T1
theorem rankAt_pullbackJacobianPoisson_of_mem_criticalPoints
    (f : M → Sphere2) (hf : ContMDiff (𝓡 4) (𝓡 2) ∞ f) {x : M}
    (hcrit : x ∈ criticalPoints (𝓡 4) (𝓡 2) (f ∘ ⇑W.ψ)) :
    (W.pullbackJacobianPoisson f hf).rankAt x = 0 :=
  rankAt_jacobianPoisson_of_mem_criticalSet
    (TauCeti.SmoothForm.mpullback W.ψ W.ψ.contMDiff V₁.Ω) W.mpullback_ψ_ne_zero
    S2VolumeForm (f ∘ ⇑W.ψ) (hf.comp W.ψ.contMDiff) hcrit

/-- `W.pullbackJacobianPoisson f hf` is `IsGenericallyRankTwo` if and only if
`jacobianPoissonOfPositiveVolume V₁ S2VolumeForm f hf` is `IsGenericallyRankTwo`. -/
-- tier: T2
theorem isGenericallyRankTwo_pullbackJacobianPoisson_iff
    (f : M → Sphere2) (hf : ContMDiff (𝓡 4) (𝓡 2) ∞ f) :
    (W.pullbackJacobianPoisson f hf).IsGenericallyRankTwo ↔
      (jacobianPoissonOfPositiveVolume V₁ S2VolumeForm f hf).IsGenericallyRankTwo := by
  rw [pullbackJacobianPoisson,
    isGenericallyRankTwo_jacobianPoisson_iff _ W.mpullback_ψ_ne_zero S2VolumeForm
      S2VolumeForm_ne_zero (f ∘ ⇑W.ψ) (hf.comp W.ψ.contMDiff),
    isGenericallyRankTwo_jacobianPoissonOfPositiveVolume_iff V₁ S2VolumeForm
      S2VolumeForm_ne_zero f hf]
  have hpre :
      {x : M | x ∉ criticalSet (𝓡 4) (𝓡 2) (f ∘ ⇑W.ψ)} =
        ⇑W.ψ ⁻¹' {y : M | y ∉ criticalSet (𝓡 4) (𝓡 2) f} := by
    ext x
    exact not_congr (W.mem_criticalPoints_comp_ψ_iff f hf x)
  rw [hpre]
  simp only [dense_iff_inter_open]
  constructor
  · intro h U hU ⟨y, hyU⟩
    obtain ⟨x, hxU, hxS⟩ := h (⇑W.ψ ⁻¹' U) (hU.preimage W.ψ.continuous)
      ⟨W.ψ.symm y, by simpa only [Set.mem_preimage, W.ψ.apply_symm_apply] using hyU⟩
    exact ⟨W.ψ x, hxU, hxS⟩
  · intro h U hU ⟨x, hxU⟩
    obtain ⟨y, hyU, hyS⟩ := h (⇑W.ψ.symm ⁻¹' U) (hU.preimage W.ψ.symm.continuous)
      ⟨W.ψ x, by simpa only [Set.mem_preimage, W.ψ.symm_apply_apply] using hxU⟩
    exact ⟨W.ψ.symm y, hyU, by simpa only [Set.mem_preimage, W.ψ.apply_symm_apply] using hyS⟩

/-- Pushforward relatedness of Hamiltonian vector fields under `W.ψ`:
`(W.pullbackJacobianPoisson f hf).hamiltonianVectorField (h ∘ W.ψ) x =
  mfderiv W.ψ.symm (W.ψ x) (π_f.hamiltonianVectorField h (W.ψ x))`. -/
-- tier: T2
theorem hamiltonianVectorField_pullbackJacobianPoisson_comp [T2Space M]
    (f : M → Sphere2) (hf : ContMDiff (𝓡 4) (𝓡 2) ∞ f) (h : C^∞⟮𝓡 4, M; ℝ⟯) (x : M) :
    (W.pullbackJacobianPoisson f hf).hamiltonianVectorField (h.comp ⟨W.ψ, W.ψ.contMDiff⟩) x =
      mfderiv (𝓡 4) (𝓡 4) W.ψ.symm (W.ψ x)
        ((jacobianPoissonOfPositiveVolume V₁ S2VolumeForm f hf).hamiltonianVectorField
          h (W.ψ x)) := by
  let P_pull := W.pullbackJacobianPoisson f hf
  let P₁ := jacobianPoissonOfPositiveVolume V₁ S2VolumeForm f hf
  let ψMap : C^∞⟮𝓡 4, M; 𝓡 4, M⟯ := ⟨W.ψ, W.ψ.contMDiff⟩
  let ψSymmMap : C^∞⟮𝓡 4, M; 𝓡 4, M⟯ := ⟨W.ψ.symm, W.ψ.symm.contMDiff⟩
  refine PoissonStructure.eq_of_forall_mvfderiv_eq fun G ↦ ?_
  let g : C^∞⟮𝓡 4, M; ℝ⟯ := G.comp ψSymmMap
  have hG : G = g.comp ψMap := by
    ext z
    change G z = G (W.ψ.symm (W.ψ z))
    rw [W.ψ.symm_apply_apply]
  rw [← P_pull.bracket_apply_eq_mvfderiv_hamiltonianVectorField, hG]
  have hp :
      (P_pull.bracket (g.comp ψMap) (h.comp ψMap)) x = (P₁.bracket g h) (W.ψ x) :=
    congrArg (fun u : C^∞⟮𝓡 4, M; ℝ⟯ ↦ u x) (W.isPoissonMap_ψ f hf g h)
  rw [hp, P₁.bracket_apply_eq_mvfderiv_hamiltonianVectorField]
  have hGd : MDifferentiableAt (𝓡 4) 𝓘(ℝ) G x := G.contMDiff.mdifferentiableAt (by simp)
  have hsymmd : MDifferentiableAt (𝓡 4) (𝓡 4) W.ψ.symm (W.ψ x) :=
    W.ψ.symm.contMDiff.mdifferentiableAt (by simp)
  have hgd : mvfderiv (𝓡 4) g (W.ψ x) =
      (mvfderiv (𝓡 4) G (W.ψ.symm (W.ψ x))).comp (mfderiv (𝓡 4) (𝓡 4) W.ψ.symm (W.ψ x)) := by
    ext v
    simp only [mvfderiv_apply_eq_mfderiv_apply, ContinuousLinearMap.comp_apply]
    exact congrArg (· v) (mfderiv_comp (W.ψ x) (by simpa using hGd) hsymmd)
  rw [hgd, ContinuousLinearMap.comp_apply]
  have hcast :
      (mvfderiv (𝓡 4) G (W.ψ.symm (W.ψ x)) : EuclideanSpace ℝ (Fin 4) → ℝ)
          (mfderiv (𝓡 4) (𝓡 4) W.ψ.symm (W.ψ x) (P₁.hamiltonianVectorField h (W.ψ x))) =
        (mvfderiv (𝓡 4) G x : EuclideanSpace ℝ (Fin 4) → ℝ)
          (mfderiv (𝓡 4) (𝓡 4) W.ψ.symm (W.ψ x) (P₁.hamiltonianVectorField h (W.ψ x))) :=
    congrArg
      (fun z ↦ (mvfderiv (𝓡 4) G z : EuclideanSpace ℝ (Fin 4) → ℝ)
        (mfderiv (𝓡 4) (𝓡 4) W.ψ.symm (W.ψ x) (P₁.hamiltonianVectorField h (W.ψ x))))
      (W.ψ.symm_apply_apply x)
  exact hcast.trans (congrArg (fun u : C^∞⟮𝓡 4, M; ℝ⟯ ↦ mvfderiv (𝓡 4) u x _) hG)

end ExactConjugation

end MoserVolume

/-! ## 6. Connected-Component Preservation for Leafwise Bump Diffeomorphisms & Fibration Pullback -/

section LeafwiseComponentAndFibrationTransport

/-- Every `leafwiseBumpDiffeomorphOfIsotopy M I_disk` preserves each connected component of `M`
(via the continuous fiberwise path `s ∈ [0, 1] ↦ Φ⁻¹(b, d_{s ρ(b)}^F(z))`). -/
-- tier: T2
theorem connectedComponent_leafwiseBumpDiffeomorphOfIsotopy
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [A : AdmitsRegularDiskFibration M] {r₀ : ℝ} (I_disk : AreaPreservingDiskIsotopy r₀) (x : M) :
    connectedComponent (leafwiseBumpDiffeomorphOfIsotopy M I_disk x) = connectedComponent x := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := A.instMeasurableSpaceFiber
  let _ := A.instBorelSpaceFiber
  by_cases hx : x ∈ A.fibration.preimageOpen.1
  · let u : A.fibration.preimageOpen := ⟨x, hx⟩
    let b := (A.fibration.trivialization u).1
    let z := (A.fibration.trivialization u).2
    have hx_emb : x = A.fibration.embed (b, z) := by
      change u.1 = (A.fibration.trivialization.symm (b, z)).1
      rw [Prod.mk.eta, A.fibration.trivialization.symm_apply_apply]
    let C := AdmitsRegularDiskFibration.fiberDiskChart M
    let γ : ℝ → M := fun s ↦
      A.fibration.embed (b, C.liftThroughChart I_disk.d (s * bumpProfile M b.1, z))
    have hlift_cont : Continuous (C.liftThroughChart I_disk.d) :=
      (C.contMDiff_liftThroughChart I_disk.contDiff_d (fun s _ hw ↦ I_disk.mem_unitDisk2 s hw)
        I_disk.r₀_lt_one I_disk.eq_self_of_notMem_ball).continuous
    have hγ_cont : Continuous γ :=
      A.fibration.contMDiff_embed.continuous.comp
        (continuous_const.prodMk
          (hlift_cont.comp ((continuous_id.mul continuous_const).prodMk continuous_const)))
    have hγ0 : γ 0 = x := by
      rw [hx_emb]
      dsimp only [γ]
      rw [zero_mul]
      change A.fibration.embed (b, C.liftIsotopyDiffeomorph I_disk 0 z) = _
      rw [C.liftIsotopyDiffeomorph_zero I_disk]
      rfl
    have hγ1 : γ 1 = leafwiseBumpDiffeomorphOfIsotopy M I_disk x := by
      rw [hx_emb, leafwiseBumpDiffeomorphOfIsotopy_embed M I_disk b z]
      dsimp only [γ]
      rw [one_mul]
      rfl
    have hpre : IsPreconnected (γ '' Set.Icc (0 : ℝ) 1) :=
      isPreconnected_Icc.image γ hγ_cont.continuousOn
    have hm0 : x ∈ γ '' Set.Icc (0 : ℝ) 1 := ⟨0, ⟨le_rfl, zero_le_one⟩, hγ0⟩
    have hm1 : leafwiseBumpDiffeomorphOfIsotopy M I_disk x ∈ γ '' Set.Icc (0 : ℝ) 1 :=
      ⟨1, ⟨zero_le_one, le_rfl⟩, hγ1⟩
    exact (connectedComponent_eq (hpre.subset_connectedComponent hm0 hm1)).symm
  · rw [leafwiseBumpDiffeomorphOfIsotopy_of_notMem M I_disk hx]

set_option linter.concreteInstances false in
/-- `leafwiseBumpDiffeomorph M` preserves every connected component of `M`. -/
-- tier: T1
theorem connectedComponent_leafwiseBumpDiffeomorph
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [A : AdmitsRegularDiskFibration M] [HasTuringCompleteAreaPreservingDiskIsotopy] (x : M) :
    connectedComponent (leafwiseBumpDiffeomorph M x) = connectedComponent x :=
  connectedComponent_leafwiseBumpDiffeomorphOfIsotopy M AreaPreservingDiskIsotopy.ofTypeclass x

/-- Precomposing any smooth map `f : M → Base` with a global diffeomorphism `ψ : N ≃ₘ⟮I_N, I_M⟯ M`
preserves `IsLocallyModeledOn`. -/
-- tier: T1
theorem IsLocallyModeledOn.comp_diffeomorph
    {E_N H_N N E_M H_M M E_B H_B Base : Type*}
    [NormedAddCommGroup E_N] [NormedSpace ℝ E_N] [TopologicalSpace H_N]
    {I_N : ModelWithCorners ℝ E_N H_N} [TopologicalSpace N] [ChartedSpace H_N N]
    [NormedAddCommGroup E_M] [NormedSpace ℝ E_M] [TopologicalSpace H_M]
    {I_M : ModelWithCorners ℝ E_M H_M} [TopologicalSpace M] [ChartedSpace H_M M]
    [NormedAddCommGroup E_B] [NormedSpace ℝ E_B] [TopologicalSpace H_B]
    {I_B : ModelWithCorners ℝ E_B H_B} [TopologicalSpace Base] [ChartedSpace H_B Base]
    {f : M → Base} {x : N} (ψ : N ≃ₘ⟮I_N, I_M⟯ M)
    {model : EuclideanSpace ℝ (Fin 4) → EuclideanPlane} {p₀ : EuclideanSpace ℝ (Fin 4)}
    (h : IsLocallyModeledOn I_M I_B f (ψ x) model p₀) :
    IsLocallyModeledOn I_N I_B (f ∘ ⇑ψ) x model p₀ := by
  obtain ⟨φ, χ, hpφ, hfpχ, hφ0, hχ0, hmod⟩ := h
  let φ' : PartialDiffeomorph I_N (𝓡 4) N (EuclideanSpace ℝ (Fin 4)) ∞ :=
    { toFun := fun q ↦ φ (ψ q)
      invFun := fun y ↦ ψ.symm (φ.toPartialEquiv.symm y)
      source := ⇑ψ ⁻¹' φ.source
      target := φ.target
      map_source' := fun _ hq ↦ φ.map_source hq
      map_target' := fun _ hy ↦ by
        simp only [Set.mem_preimage, ψ.apply_symm_apply]
        exact φ.map_target hy
      left_inv' := fun _ hq ↦ by
        rw [φ.left_inv hq, ψ.symm_apply_apply]
      right_inv' := fun _ hy ↦ by
        rw [ψ.apply_symm_apply, φ.right_inv hy]
      open_source := φ.open_source.preimage ψ.continuous
      open_target := φ.open_target
      contMDiffOn_toFun := φ.contMDiffOn.comp ψ.contMDiff.contMDiffOn (fun _ hq ↦ hq)
      contMDiffOn_invFun := (ψ.symm.contMDiff.contMDiffOn (s := Set.univ)).comp φ.contMDiffOn_invFun
        (fun _ _ ↦ Set.mem_univ _) }
  exact ⟨φ', χ, hpφ, hfpχ, hφ0, hχ0, fun q hq ↦ hmod (ψ q) hq⟩

/-- Precomposing `RegularDiskFibration` with a global diffeomorphism `ψ : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M`. -/
noncomputable def RegularDiskFibration.compDiffeomorph
    {M Base Fiber : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M]
    [TopologicalSpace Base] [ChartedSpace EuclideanPlane Base] [IsManifold (𝓡 2) ∞ Base]
    [TopologicalSpace Fiber] [ChartedSpace EuclideanPlane Fiber] [IsManifold (𝓡 2) ∞ Fiber]
    [T2Space Fiber] [CompactSpace Fiber] [Nonempty Fiber]
    (R : RegularDiskFibration (𝓡 4) M (𝓡 2) Base Fiber) (ψ : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M) :
    RegularDiskFibration (𝓡 4) M (𝓡 2) Base Fiber := by
  let U_new : Opens M := ⟨(R.toFun ∘ ⇑ψ) ⁻¹' R.baseRegion.1,
    R.baseRegion.2.preimage (R.contMDiff_toFun.comp ψ.contMDiff).continuous⟩
  let ψ_sub : U_new ≃ₘ⟮𝓡 4, 𝓡 4⟯ R.preimageOpen :=
    { toFun := fun u ↦ ⟨ψ u.1, u.2⟩
      invFun := fun v ↦ ⟨ψ.symm v.1, by
        change R.toFun (ψ (ψ.symm v.1)) ∈ R.baseRegion.1
        rw [ψ.apply_symm_apply]
        exact v.2⟩
      left_inv := fun u ↦ Subtype.ext (ψ.symm_apply_apply u.1)
      right_inv := fun v ↦ Subtype.ext (ψ.apply_symm_apply v.1)
      contMDiff_toFun :=
        (TauCeti.ContMDiff.subtypeVal_comp_iff R.preimageOpen _).mp
          (ψ.contMDiff.comp contMDiff_subtype_val)
      contMDiff_invFun :=
        (TauCeti.ContMDiff.subtypeVal_comp_iff U_new _).mp
          (ψ.symm.contMDiff.comp contMDiff_subtype_val) }
  exact
    { toFun := R.toFun ∘ ⇑ψ
      contMDiff_toFun := R.contMDiff_toFun.comp ψ.contMDiff
      baseRegion := R.baseRegion
      baseRegion_nonempty := R.baseRegion_nonempty
      regular_on_preimage := fun x hx ↦ by
        rw [mfderiv_comp x (R.contMDiff_toFun.mdifferentiableAt (by simp))
          (ψ.contMDiff.mdifferentiableAt (by simp))]
        exact (R.regular_on_preimage (ψ x) hx).comp
          ((ψ.isLocalDiffeomorph x).isInvertible_mfderiv (by simp)).surjective
      baseDiskRadius := R.baseDiskRadius
      baseDiskRadius_pos := R.baseDiskRadius_pos
      baseDisk := R.baseDisk
      trivialization := ψ_sub.trans R.trivialization
      trivialization_fst := fun u ↦ R.trivialization_fst (ψ_sub u) }

/-- Precomposing `PurelyWrinkledFibration` with a global diffeomorphism `ψ : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M`. -/
noncomputable def PurelyWrinkledFibration.compDiffeomorph
    {M Base Fiber : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M]
    [TopologicalSpace Base] [ChartedSpace EuclideanPlane Base] [IsManifold (𝓡 2) ∞ Base]
    [TopologicalSpace Fiber] [ChartedSpace EuclideanPlane Fiber] [IsManifold (𝓡 2) ∞ Fiber]
    [T2Space Fiber] [CompactSpace Fiber] [Nonempty Fiber]
    (P : PurelyWrinkledFibration (𝓡 4) M (𝓡 2) Base Fiber) (ψ : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M) :
    PurelyWrinkledFibration (𝓡 4) M (𝓡 2) Base Fiber where
  toRegularDiskFibration := P.toRegularDiskFibration.compDiffeomorph ψ
  singularities_purely_wrinkled x hx := by
    have hψx : ψ x ∈ criticalPoints (𝓡 4) (𝓡 2) P.toFun := by
      intro hsurj
      apply hx
      change Function.Surjective (mfderiv (𝓡 4) (𝓡 2) (P.toFun ∘ ⇑ψ) x)
      rw [mfderiv_comp x (P.contMDiff_toFun.mdifferentiableAt (by simp))
        (ψ.contMDiff.mdifferentiableAt (by simp))]
      exact hsurj.comp ((ψ.isLocalDiffeomorph x).isInvertible_mfderiv (by simp)).surjective
    exact (P.singularities_purely_wrinkled (ψ x) hψx).imp
      (fun h ↦ h.comp_diffeomorph ψ) (fun h ↦ h.comp_diffeomorph ψ)

/-- Precomposing `BrokenLefschetzFibration` with a global diffeomorphism `ψ : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M`. -/
noncomputable def BrokenLefschetzFibration.compDiffeomorph
    {M Base Fiber : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M]
    [TopologicalSpace Base] [ChartedSpace EuclideanPlane Base] [IsManifold (𝓡 2) ∞ Base]
    [TopologicalSpace Fiber] [ChartedSpace EuclideanPlane Fiber] [IsManifold (𝓡 2) ∞ Fiber]
    [T2Space Fiber] [CompactSpace Fiber] [Nonempty Fiber]
    (B : BrokenLefschetzFibration (𝓡 4) M (𝓡 2) Base Fiber) (ψ : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M) :
    BrokenLefschetzFibration (𝓡 4) M (𝓡 2) Base Fiber where
  toRegularDiskFibration := B.toRegularDiskFibration.compDiffeomorph ψ
  singularities_broken_lefschetz x hx := by
    have hψx : ψ x ∈ criticalPoints (𝓡 4) (𝓡 2) B.toFun := by
      intro hsurj
      apply hx
      change Function.Surjective (mfderiv (𝓡 4) (𝓡 2) (B.toFun ∘ ⇑ψ) x)
      rw [mfderiv_comp x (B.contMDiff_toFun.mdifferentiableAt (by simp))
        (ψ.contMDiff.mdifferentiableAt (by simp))]
      exact hsurj.comp ((ψ.isLocalDiffeomorph x).isInvertible_mfderiv (by simp)).surjective
    exact (B.singularities_broken_lefschetz (ψ x) hψx).imp
      (fun h ↦ h.comp_diffeomorph ψ) (fun h ↦ h.comp_diffeomorph ψ)

end LeafwiseComponentAndFibrationTransport

end S4TuringPoisson
