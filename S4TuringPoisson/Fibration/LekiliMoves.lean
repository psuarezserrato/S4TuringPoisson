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
public import S4TuringPoisson.Fibration.LocalSingularModels
public import S4TuringPoisson.Fibration.PurelyWrinkled
public import TauCeti.Analysis.Analytic.Complexification.Weierstrass
public import TauCeti.Analysis.Calculus.InverseFunctionTheorem
public import TauCeti.Analysis.Normed.Algebra.SquareRoot
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Manifold.RegularValue.Open
public import TauCeti.Geometry.Manifold.RegularValue.Rank
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Lekili's Four Moves, 3-Cusp Deltoid Witness, and Chart Wrinkling (`Lekili 2009`)

This module formalizes the four explicit local `ℝ⁴ → ℝ²` 1-parameter singular-fibration normal-form
families of Lekili (`Geom. Topol.` 13, 2009, §3.1–§3.2), together with global chart surgery (§4 /
Theorem 4):
1. **Move 1 (`lekiliMove1`, §3.1) & Gate 5.2**: Local `ℝ⁴ → ℝ²` wrinkling of an isolated real
   Lefschetz point `(z₁, z₂) ↦ z₁² + z₂² + 2s z̄₁` into a circle of singularities with **three
   distinct cusps** at `θ = 0, 2π/3, 4π/3` (`deriv = 0`) and regular immersion elsewhere
   (`deriv ≠ 0` at `θ = π`), plus `IsWrinkledCuspAt` and `IsIndefiniteFoldAt` local normal-form
   equivalences.
2. **Moves 2–4 (`lekiliMove2`–`lekiliMove4`, §3.2)**: Explicit local `ℝ⁴ → ℝ²` 1-parameter families
   for birth/death of a 2-cusp eye (`t, x₁³ + 3(t² - s) x₁ + Q`), cusp-merge
   (`t, x₁³ - 3(t² - s) x₁ + Q`), and flip/swallowtail (`t, x₁⁴/4 + s x₁²/2 - t x₁ + Q`), with
   exact `HasFDerivAt`, `criticalPoints`, and `IsIndefiniteFoldAt` / `IsWrinkledCuspAt` normal-form
   classifications for all four moves.
3. **Compactly Supported Chart Wrinkling & Global Surgery (`compactLefschetzWrinkle`,
   §4 / Theorem 4)**: Globalizes Move 1 onto manifolds via a radial bump modification
   (`rIn = 1, rOut = 2`) with an explicit quantitative collar right-inverse bound, replacing
   isolated `IsRealLefschetzAt` points outside `closure P.baseRegion` while preserving
   `WrinkledFibration` and exporting compact surgery support `K` and smooth global homotopy `H` in
   `BrokenLefschetzFibration.exists_purelyWrinkledFibration`.
-/

@[expose] public section

open Filter Function Metric Set Topology
open scoped ContDiff Manifold

namespace S4TuringPoisson

section Helpers

/-- Continuity constructor for `ℝ⁴`-valued maps from four coordinate functions. -/
theorem continuous_vec4 {α : Type*} [TopologicalSpace α] {f₀ f₁ f₂ f₃ : α → ℝ}
    (h₀ : Continuous f₀) (h₁ : Continuous f₁)
    (h₂ : Continuous f₂) (h₃ : Continuous f₃) :
    Continuous (fun p ↦ vec4 (f₀ p) (f₁ p) (f₂ p) (f₃ p)) := by
  have hpi : Continuous (fun p ↦ ![f₀ p, f₁ p, f₂ p, f₃ p]) := by
    refine continuous_pi fun i ↦ ?_
    fin_cases i
    · exact h₀
    · exact h₁
    · exact h₂
    · exact h₃
  exact ((EuclideanSpace.equiv (Fin 4) ℝ).symm.continuous).comp hpi

/-- Continuity constructor for `ℝ²`-valued maps from two coordinate functions. -/
theorem continuous_vec2 {α : Type*} [TopologicalSpace α] {f₀ f₁ : α → ℝ}
    (h₀ : Continuous f₀) (h₁ : Continuous f₁) :
    Continuous (fun p ↦ vec2 (f₀ p) (f₁ p)) := by
  have hpi : Continuous (fun p ↦ ![f₀ p, f₁ p]) := by
    refine continuous_pi fun i ↦ ?_
    fin_cases i
    · exact h₀
    · exact h₁
  exact ((EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous).comp hpi

/-- Smoothness (`ContDiffOn ℝ ∞`) constructor for `ℝ⁴`-valued maps from four coordinates. -/
theorem contDiffOn_vec4 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {f₀ f₁ f₂ f₃ : E → ℝ}
    (h₀ : ContDiffOn ℝ ∞ f₀ s) (h₁ : ContDiffOn ℝ ∞ f₁ s)
    (h₂ : ContDiffOn ℝ ∞ f₂ s) (h₃ : ContDiffOn ℝ ∞ f₃ s) :
    ContDiffOn ℝ ∞ (fun p ↦ vec4 (f₀ p) (f₁ p) (f₂ p) (f₃ p)) s := by
  have hpi : ContDiffOn ℝ ∞ (fun p ↦ ![f₀ p, f₁ p, f₂ p, f₃ p]) s := by
    refine contDiffOn_pi.mpr fun i ↦ ?_
    fin_cases i
    · exact h₀
    · exact h₁
    · exact h₂
    · exact h₃
  exact ((EuclideanSpace.equiv (Fin 4) ℝ).symm.contDiff).contDiffOn.comp hpi
    (fun _ _ ↦ Set.mem_univ _)

/-- Smoothness (`ContDiffOn ℝ ∞`) constructor for `ℝ²`-valued maps from two coordinates. -/
theorem contDiffOn_vec2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {f₀ f₁ : E → ℝ}
    (h₀ : ContDiffOn ℝ ∞ f₀ s) (h₁ : ContDiffOn ℝ ∞ f₁ s) :
    ContDiffOn ℝ ∞ (fun p ↦ vec2 (f₀ p) (f₁ p)) s := by
  have hpi : ContDiffOn ℝ ∞ (fun p ↦ ![f₀ p, f₁ p]) s := by
    refine contDiffOn_pi.mpr fun i ↦ ?_
    fin_cases i
    · exact h₀
    · exact h₁
  exact ((EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff).contDiffOn.comp hpi
    (fun _ _ ↦ Set.mem_univ _)

/-- Clean Fréchet derivative constructor for `ℝ⁴`-valued maps with explicit `vec4` CLM. -/
theorem hasFDerivAt_vec4' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f₀ f₁ f₂ f₃ : E → ℝ} {g₀ g₁ g₂ g₃ : E →L[ℝ] ℝ} {x : E}
    (h₀ : HasFDerivAt f₀ g₀ x) (h₁ : HasFDerivAt f₁ g₁ x)
    (h₂ : HasFDerivAt f₂ g₂ x) (h₃ : HasFDerivAt f₃ g₃ x) :
    HasFDerivAt (fun y ↦ vec4 (f₀ y) (f₁ y) (f₂ y) (f₃ y))
      ((EuclideanSpace.equiv (Fin 4) ℝ).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi ![g₀, g₁, g₂, g₃])) x :=
  ((EuclideanSpace.equiv (Fin 4) ℝ).symm.hasFDerivAt).comp x
    (hasFDerivAt_pi.mpr fun i ↦ by fin_cases i <;> assumption)

/-- Evaluates the `EuclideanSpace` `vec4` CLM built in `hasFDerivAt_vec4'`. -/
@[simp]
theorem clmVec4_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g₀ g₁ g₂ g₃ : E →L[ℝ] ℝ) (v : E) :
    ((EuclideanSpace.equiv (Fin 4) ℝ).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi ![g₀, g₁, g₂, g₃])) v =
      vec4 (g₀ v) (g₁ v) (g₂ v) (g₃ v) := by
  ext i
  fin_cases i <;> rfl

/-- Derivative constructor for `EuclideanPlane`-valued curves `ℝ → EuclideanPlane`. -/
theorem hasDerivAt_vec2 {f₀ f₁ : ℝ → ℝ} {a₀ a₁ θ : ℝ}
    (h₀ : HasDerivAt f₀ a₀ θ) (h₁ : HasDerivAt f₁ a₁ θ) :
    HasDerivAt (fun t ↦ vec2 (f₀ t) (f₁ t)) (vec2 a₀ a₁) θ := by
  rw [hasDerivAt_iff_hasFDerivAt] at h₀ h₁ ⊢
  refine (hasFDerivAt_vec2 h₀ h₁).congr_fderiv ?_
  apply ContinuousLinearMap.ext_ring
  refine ext_vec2 ?_ ?_ <;>
    simp [clmVec2_apply, ContinuousLinearMap.toSpanSingleton_apply, one_smul, smul_eq_mul,
      vec2_zero, vec2_one]

/-- Surjectivity on finite-dimensional spaces of linear maps within operator distance `< 1` of
the identity. -/
theorem surjective_of_norm_sub_id_lt_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {T : E →L[ℝ] E} (hT : ‖T - ContinuousLinearMap.id ℝ E‖ < 1) :
    Function.Surjective T := by
  have hinj : Function.Injective T := by
    intro x y hxy
    suffices hx : x - y = 0 from sub_eq_zero.mp hx
    set z := x - y
    have hz : T z = 0 := by simp only [z, map_sub, hxy, sub_self]
    by_contra hz0
    have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hsub : (T - ContinuousLinearMap.id ℝ E) z = -z := by
      rw [sub_apply, ContinuousLinearMap.id_apply, hz, zero_sub]
    have hle1 : ‖z‖ ≤ ‖T - ContinuousLinearMap.id ℝ E‖ * ‖z‖ := by
      calc
        ‖z‖ = ‖-z‖ := (norm_neg z).symm
        _ = ‖(T - ContinuousLinearMap.id ℝ E) z‖ := by rw [hsub]
        _ ≤ ‖T - ContinuousLinearMap.id ℝ E‖ * ‖z‖ := ContinuousLinearMap.le_opNorm _ _
    have hlt : ‖T - ContinuousLinearMap.id ℝ E‖ * ‖z‖ < 1 * ‖z‖ :=
      mul_lt_mul_of_pos_right hT hnorm_pos
    linarith
  exact LinearMap.surjective_of_injective (f := (T : E →ₗ[ℝ] E)) hinj

/-- Local invariance of `IsLocallyModeledOn` under eventual equality near `p`. -/
-- tier: T2
theorem isLocallyModeledOn_congr {E_M H_M E_B H_B M Base : Type*}
    [NormedAddCommGroup E_M] [NormedSpace ℝ E_M] [TopologicalSpace H_M]
    {I_M : ModelWithCorners ℝ E_M H_M}
    [NormedAddCommGroup E_B] [NormedSpace ℝ E_B] [TopologicalSpace H_B]
    {I_B : ModelWithCorners ℝ E_B H_B}
    [TopologicalSpace M] [ChartedSpace H_M M]
    [TopologicalSpace Base] [ChartedSpace H_B Base]
    {f g : M → Base} {p : M} {model : EuclideanSpace ℝ (Fin 4) → EuclideanPlane}
    {p₀ : EuclideanSpace ℝ (Fin 4)} (hfg : f =ᶠ[𝓝 p] g)
    (hf : IsLocallyModeledOn I_M I_B f p model p₀) :
    IsLocallyModeledOn I_M I_B g p model p₀ := by
  obtain ⟨φ, ψ, hpφ, hfpψ, hφp, hψfp, hmodel⟩ := hf
  obtain ⟨U, hUeq, hU_open, hpU⟩ := _root_.eventually_nhds_iff.mp hfg
  let V : Set M := φ.source ∩ U
  have hV_open : IsOpen V := φ.open_source.inter hU_open
  let φ' := φ.restrOpen V hV_open
  have hφ'_src : φ'.source = φ.source ∩ V :=
    PartialDiffeomorph.restrOpen_source φ hV_open
  have hφ'_eq : ∀ q, φ' q = φ q := fun q ↦ by
    change (φ.restrOpen V hV_open).toPartialEquiv q = φ.toPartialEquiv q
    rw [PartialDiffeomorph.restrOpen_toPartialEquiv]
    rfl
  refine ⟨φ', ψ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hφ'_src]
    exact ⟨hpφ, hpφ, hpU⟩
  · rw [← hUeq p hpU]
    exact hfpψ
  · rw [hφ'_eq, hφp]
  · rw [← hUeq p hpU, hψfp]
  · intro q hq
    rw [hφ'_src] at hq
    have hqV : q ∈ V := hq.2
    rw [← hUeq q hqV.2, hφ'_eq]
    exact hmodel q hq.1

/-- Local invariance of `IsIndefiniteFoldAt` under eventual equality near `p`. -/
-- tier: T2
theorem isIndefiniteFoldAt_congr {E_M H_M E_B H_B M Base : Type*}
    [NormedAddCommGroup E_M] [NormedSpace ℝ E_M] [TopologicalSpace H_M]
    {I_M : ModelWithCorners ℝ E_M H_M}
    [NormedAddCommGroup E_B] [NormedSpace ℝ E_B] [TopologicalSpace H_B]
    {I_B : ModelWithCorners ℝ E_B H_B}
    [TopologicalSpace M] [ChartedSpace H_M M]
    [TopologicalSpace Base] [ChartedSpace H_B Base]
    {f g : M → Base} {p : M} (hfg : f =ᶠ[𝓝 p] g)
    (hf : IsIndefiniteFoldAt I_M I_B f p) :
    IsIndefiniteFoldAt I_M I_B g p :=
  isLocallyModeledOn_congr hfg hf

/-- Local invariance of `IsWrinkledCuspAt` under eventual equality near `p`. -/
-- tier: T2
theorem isWrinkledCuspAt_congr {E_M H_M E_B H_B M Base : Type*}
    [NormedAddCommGroup E_M] [NormedSpace ℝ E_M] [TopologicalSpace H_M]
    {I_M : ModelWithCorners ℝ E_M H_M}
    [NormedAddCommGroup E_B] [NormedSpace ℝ E_B] [TopologicalSpace H_B]
    {I_B : ModelWithCorners ℝ E_B H_B}
    [TopologicalSpace M] [ChartedSpace H_M M]
    [TopologicalSpace Base] [ChartedSpace H_B Base]
    {f g : M → Base} {p : M} (hfg : f =ᶠ[𝓝 p] g)
    (hf : IsWrinkledCuspAt I_M I_B f p) :
    IsWrinkledCuspAt I_M I_B g p :=
  isLocallyModeledOn_congr hfg hf

/-- Transport `IsLocallyModeledOn` on Euclidean models via
`ContDiffOn.exists_openPartialHomeomorph`.
If `Φ : ℝ⁴ → ℝ⁴` and `Ψ : ℝ² → ℝ²` are smooth near `p_*` and `f p_*` with invertible Fréchet
derivatives `eΦ, eΨ`, satisfying `Ψ (f p) = model (Φ p)` near `p_*` (`Φ p_* = p₀`), then `f` is
locally modeled on `model` at `p_*`. -/
-- tier: T2
theorem isLocallyModeledOn_of_contDiff_maps
    {f model : EuclideanSpace ℝ (Fin 4) → EuclideanPlane}
    {Φ : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4)}
    {Ψ : EuclideanPlane → EuclideanPlane}
    {p_star p₀ : EuclideanSpace ℝ (Fin 4)}
    {U_dom : Set (EuclideanSpace ℝ (Fin 4))} {U_tgt : Set EuclideanPlane}
    (hU_dom : IsOpen U_dom) (hp_dom : p_star ∈ U_dom)
    (hU_tgt : IsOpen U_tgt) (hfp_tgt : f p_star ∈ U_tgt)
    (hΦ : ContDiffOn ℝ ∞ Φ U_dom) (hΨ : ContDiffOn ℝ ∞ Ψ U_tgt)
    (eΦ : EuclideanSpace ℝ (Fin 4) ≃L[ℝ] EuclideanSpace ℝ (Fin 4))
    (heΦ : (eΦ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) = fderiv ℝ Φ p_star)
    (eΨ : EuclideanPlane ≃L[ℝ] EuclideanPlane)
    (heΨ : (eΨ : EuclideanPlane →L[ℝ] EuclideanPlane) = fderiv ℝ Ψ (f p_star))
    (hΦ_p : Φ p_star = p₀) (hΨ_fp : Ψ (f p_star) = model p₀)
    (heq : ∀ᶠ p in 𝓝 p_star, f p ∈ U_tgt ∧ Ψ (f p) = model (Φ p))
    (hf_cont : ContinuousAt f p_star) :
    IsLocallyModeledOn (𝓡 4) (𝓡 2) f p_star model p₀ := by
  obtain ⟨Θ₁, hΘ₁_coe, hp_Θ₁, hΘ₁_sub, hΘ₁_symm⟩ :=
    TauCeti.ContDiffOn.exists_openPartialHomeomorph hΦ hU_dom hp_dom (by simp) heΦ
  obtain ⟨Θ₂, hΘ₂_coe, hfp_Θ₂, hΘ₂_sub, hΘ₂_symm⟩ :=
    TauCeti.ContDiffOn.exists_openPartialHomeomorph hΨ hU_tgt hfp_tgt (by simp) heΨ
  let φ₀ := TauCeti.PartialDiffeomorph.ofOpenPartialHomeomorph Θ₁
    (hΘ₁_coe ▸ hΦ.mono hΘ₁_sub) hΘ₁_symm
  let ψ := TauCeti.PartialDiffeomorph.ofOpenPartialHomeomorph Θ₂
    (hΘ₂_coe ▸ hΨ.mono hΘ₂_sub) hΘ₂_symm
  have hp_φ₀ : p_star ∈ φ₀.source := by
    rw [TauCeti.PartialDiffeomorph.ofOpenPartialHomeomorph_toPartialEquiv]
    exact hp_Θ₁
  have hfp_ψ : f p_star ∈ ψ.source := by
    rw [TauCeti.PartialDiffeomorph.ofOpenPartialHomeomorph_toPartialEquiv]
    exact hfp_Θ₂
  have hpre : {p | f p ∈ ψ.source ∧ f p ∈ U_tgt ∧ Ψ (f p) = model (Φ p)} ∈ 𝓝 p_star := by
    have h1 : f ⁻¹' ψ.source ∈ 𝓝 p_star :=
      hf_cont.preimage_mem_nhds (ψ.open_source.mem_nhds hfp_ψ)
    exact Filter.Eventually.and h1 heq
  obtain ⟨W, hW_sub, hW_open, hpW⟩ := _root_.eventually_nhds_iff.mp hpre
  let φ := φ₀.restrOpen (φ₀.source ∩ W) (φ₀.open_source.inter hW_open)
  have hφ_src : φ.source = φ₀.source ∩ (φ₀.source ∩ W) :=
    PartialDiffeomorph.restrOpen_source φ₀ (φ₀.open_source.inter hW_open)
  have hφ_eq : ∀ q, φ q = Φ q := fun q ↦ by
    change (φ₀.restrOpen _ _).toPartialEquiv q = Φ q
    rw [PartialDiffeomorph.restrOpen_toPartialEquiv]
    change φ₀.toPartialEquiv q = Φ q
    rw [TauCeti.PartialDiffeomorph.ofOpenPartialHomeomorph_toPartialEquiv,
      OpenPartialHomeomorph.coe_toPartialEquiv, hΘ₁_coe]
  have hψ_eq : ∀ y, ψ y = Ψ y := fun y ↦ by
    rw [TauCeti.PartialDiffeomorph.ofOpenPartialHomeomorph_toPartialEquiv,
      OpenPartialHomeomorph.coe_toPartialEquiv, hΘ₂_coe]
  refine ⟨φ, ψ, ?_, hfp_ψ, by rw [hφ_eq, hΦ_p], by rw [hψ_eq, hΨ_fp], ?_⟩
  · rw [hφ_src]
    exact ⟨hp_φ₀, hp_φ₀, hpW⟩
  · intro q hq
    rw [hφ_src] at hq
    have hqW := hW_sub q hq.2.2
    refine ⟨hqW.1, ?_⟩
    rw [hψ_eq, hφ_eq, hqW.2.2]

end Helpers

/-! ## 1. Lekili Move 1 & Gate 5.2 (3-Cusp Deltoid Witness) -/

section Move1AndGate52

/-- **Lekili Move 1 (Wrinkling a Real Lefschetz Singularity)**:
Perturbs `realLefschetzMap` (`z₁² + z₂²`) by `(x₀, x₁, x₂, x₃) ↦ (2 s x₀, -2 s x₁)`, i.e.
`z₁² + z₂² + 2 s z̄₁`. At `s = 0` this is `realLefschetzMap`; for `s ≠ 0` the critical locus is
the circle `p₀² + p₁² = s², p₂ = p₃ = 0` with three wrinkled cusps (`θ = 0, 2π/3, 4π/3`). -/
-- tier: T2
noncomputable def lekiliMove1 (s : ℝ) (p : EuclideanSpace ℝ (Fin 4)) : EuclideanPlane :=
  realLefschetzMap p + vec2 (2 * s * p 0) (-2 * s * p 1)

@[simp]
theorem lekiliMove1_apply_zero (s : ℝ) (p : EuclideanSpace ℝ (Fin 4)) :
    lekiliMove1 s p 0 = p 0 ^ 2 - p 1 ^ 2 + p 2 ^ 2 - p 3 ^ 2 + 2 * s * p 0 :=
  rfl

@[simp]
theorem lekiliMove1_apply_one (s : ℝ) (p : EuclideanSpace ℝ (Fin 4)) :
    lekiliMove1 s p 1 = 2 * p 0 * p 1 + 2 * p 2 * p 3 - 2 * s * p 1 := by
  simp [lekiliMove1, realLefschetzMap, sub_eq_add_neg]

@[simp]
theorem lekiliMove1_zero (p : EuclideanSpace ℝ (Fin 4)) :
    lekiliMove1 0 p = realLefschetzMap p := by
  refine ext_vec2 ?_ ?_ <;> simp

/-- Smoothness (`ContDiff ℝ ∞`) of `lekiliMove1 s`. -/
theorem contDiff_lekiliMove1 (s : ℝ) : ContDiff ℝ ∞ (lekiliMove1 s) := by
  have hp (i : Fin 4) : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 4) ↦ p i) :=
    (euclidProj i).contDiff
  have hpert :
      ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 4) ↦ vec2 (2 * s * p 0) (-2 * s * p 1)) :=
    contDiff_vec2 (contDiff_const.mul (hp 0)) (contDiff_const.mul (hp 1))
  exact contDiff_realLefschetzMap.add hpert

/-- Manifold smoothness of `lekiliMove1 s`. -/
-- tier: T2
theorem contMDiff_lekiliMove1 (s : ℝ) : ContMDiff (𝓡 4) (𝓡 2) ∞ (lekiliMove1 s) :=
  (contDiff_lekiliMove1 s).contMDiff

/-- Continuous linear map representing `fderiv ℝ (lekiliMove1 s) p`. -/
noncomputable def lekiliMove1FDerivCLM (s : ℝ) (p : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanPlane :=
  realLefschetzFDerivCLM p +
    clmVec2 ((2 * s) • euclidProj (0 : Fin 4)) ((-2 * s) • euclidProj (1 : Fin 4))

@[simp]
theorem lekiliMove1FDerivCLM_apply (s : ℝ) (p v : EuclideanSpace ℝ (Fin 4)) :
    lekiliMove1FDerivCLM s p v =
      vec2 (2 * (p 0 + s) * v 0 - 2 * p 1 * v 1 + 2 * p 2 * v 2 - 2 * p 3 * v 3)
        (2 * p 1 * v 0 + 2 * (p 0 - s) * v 1 + 2 * p 3 * v 2 + 2 * p 2 * v 3) := by
  refine ext_vec2 ?_ ?_ <;>
    simp [lekiliMove1FDerivCLM, realLefschetzFDerivCLM, euclidProj] <;> ring

/-- Exact Fréchet derivative of `lekiliMove1 s` at `p`. -/
theorem hasFDerivAt_lekiliMove1 (s : ℝ) (p : EuclideanSpace ℝ (Fin 4)) :
    HasFDerivAt (lekiliMove1 s) (lekiliMove1FDerivCLM s p) p := by
  have hp0 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ 2 * s * x 0)
      ((2 * s) • euclidProj (0 : Fin 4)) p := by
    convert ((euclidProj (0 : Fin 4)).hasFDerivAt.const_smul (2 * s)) using 1
    funext x
    simp [smul_eq_mul]
  have hp1 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ -2 * s * x 1)
      ((-2 * s) • euclidProj (1 : Fin 4)) p := by
    convert ((euclidProj (1 : Fin 4)).hasFDerivAt.const_smul (-2 * s)) using 1
    funext x
    simp [smul_eq_mul]
  exact (hasFDerivAt_realLefschetzMap p).add (hasFDerivAt_vec2 hp0 hp1)

/-- `fderiv ℝ (lekiliMove1 s) p = lekiliMove1FDerivCLM s p`. -/
@[simp]
theorem fderiv_lekiliMove1 (s : ℝ) (p : EuclideanSpace ℝ (Fin 4)) :
    fderiv ℝ (lekiliMove1 s) p = lekiliMove1FDerivCLM s p :=
  (hasFDerivAt_lekiliMove1 s p).fderiv

/-- Surjectivity characterization of `fderiv ℝ (lekiliMove1 s) p`. -/
theorem surjective_fderiv_lekiliMove1_iff (s : ℝ) (p : EuclideanSpace ℝ (Fin 4)) :
    Function.Surjective (fderiv ℝ (lekiliMove1 s) p) ↔
      ¬ (p 0 ^ 2 + p 1 ^ 2 = s ^ 2 ∧ p 2 = 0 ∧ p 3 = 0) := by
  rw [fderiv_lekiliMove1]
  constructor
  · rintro hsurj ⟨h01, hp2, hp3⟩
    by_cases hp10 : p 0 = s ∧ p 1 = 0
    · obtain ⟨v, hv⟩ := hsurj (vec2 0 1)
      have hv1 := congrArg (fun u : EuclideanPlane ↦ u 1) hv
      simp only [lekiliMove1FDerivCLM_apply, vec2_one, hp10.1, hp10.2, hp2, hp3] at hv1
      linarith
    · obtain ⟨v, hv⟩ := hsurj (vec2 (p 0 - s) (p 1))
      have hv0 := congrArg (fun u : EuclideanPlane ↦ u 0) hv
      have hv1 := congrArg (fun u : EuclideanPlane ↦ u 1) hv
      simp only [lekiliMove1FDerivCLM_apply, vec2_zero, vec2_one, hp2, hp3, mul_zero, zero_mul,
        add_zero, sub_zero] at hv0 hv1
      have hcomb : (p 0 - s) * (p 0 - s) + p 1 * p 1 = 0 := by
        calc
          (p 0 - s) * (p 0 - s) + p 1 * p 1
            = (p 0 - s) * (2 * (p 0 + s) * v 0 - 2 * p 1 * v 1) +
                p 1 * (2 * p 1 * v 0 + 2 * (p 0 - s) * v 1) := by rw [hv0, hv1]
          _ = 2 * v 0 * (p 0 ^ 2 + p 1 ^ 2 - s ^ 2) := by ring
          _ = 0 := by rw [h01, sub_self, mul_zero]
      have hps : p 0 = s := by
        have : (p 0 - s) ^ 2 = 0 := by nlinarith [sq_nonneg (p 0 - s), sq_nonneg (p 1)]
        linarith [sq_eq_zero_iff.mp this]
      have hp1 : p 1 = 0 := by
        have : p 1 ^ 2 = 0 := by nlinarith [sq_nonneg (p 0 - s), sq_nonneg (p 1)]
        exact sq_eq_zero_iff.mp this
      exact hp10 ⟨hps, hp1⟩
  · intro hnot w
    by_cases h23 : p 2 ^ 2 + p 3 ^ 2 ≠ 0
    · let r := p 2 ^ 2 + p 3 ^ 2
      refine ⟨vec4 0 0 ((p 2 * w 0 + p 3 * w 1) / (2 * r))
          ((-p 3 * w 0 + p 2 * w 1) / (2 * r)), ext_vec2 ?_ ?_⟩
      · simp only [lekiliMove1FDerivCLM_apply, vec2_zero, vec4_zero, vec4_one, vec4_two,
          vec4_three, r]
        field_simp [h23]
        ring
      · simp only [lekiliMove1FDerivCLM_apply, vec2_one, vec4_zero, vec4_one, vec4_two,
          vec4_three, r]
        field_simp [h23]
        ring
    · push Not at h23
      have hp2 : p 2 = 0 := by nlinarith [sq_nonneg (p 2), sq_nonneg (p 3)]
      have hp3 : p 3 = 0 := by nlinarith [sq_nonneg (p 2), sq_nonneg (p 3)]
      have hd : p 0 ^ 2 + p 1 ^ 2 - s ^ 2 ≠ 0 := by
        intro hd0
        exact hnot ⟨by linarith, hp2, hp3⟩
      let d := p 0 ^ 2 + p 1 ^ 2 - s ^ 2
      refine ⟨vec4 (((p 0 - s) * w 0 + p 1 * w 1) / (2 * d))
          ((-p 1 * w 0 + (p 0 + s) * w 1) / (2 * d)) 0 0, ext_vec2 ?_ ?_⟩
      · simp only [lekiliMove1FDerivCLM_apply, vec2_zero, vec4_zero, vec4_one, vec4_two,
          vec4_three, d]
        field_simp [hd]
        ring
      · simp only [lekiliMove1FDerivCLM_apply, vec2_one, vec4_zero, vec4_one, vec4_two,
          vec4_three, d]
        field_simp [hd]
        ring

/-- Exact critical locus of `lekiliMove1 s`: the circle `p₀² + p₁² = s², p₂ = p₃ = 0`. -/
-- tier: T2
theorem criticalPoints_lekiliMove1 (s : ℝ) :
    criticalPoints (𝓡 4) (𝓡 2) (lekiliMove1 s) =
      {p : EuclideanSpace ℝ (Fin 4) | p 0 ^ 2 + p 1 ^ 2 = s ^ 2 ∧ p 2 = 0 ∧ p 3 = 0} := by
  rw [criticalPoints_euclidean_eq]
  ext p
  rw [mem_euclideanCriticalPoints_iff, surjective_fderiv_lekiliMove1_iff, not_not,
    Set.mem_ofPred_eq]

/-- Parametric critical circle `θ ↦ (s cos θ, s sin θ, 0, 0)` of `lekiliMove1 s`. -/
noncomputable def lekiliMove1CritCurve (s θ : ℝ) : EuclideanSpace ℝ (Fin 4) :=
  vec4 (s * Real.cos θ) (s * Real.sin θ) 0 0

/-- Every point of `lekiliMove1CritCurve s` lies in `criticalPoints (𝓡 4) (𝓡 2) (lekiliMove1 s)`. -/
theorem lekiliMove1CritCurve_mem_criticalPoints (s θ : ℝ) :
    lekiliMove1CritCurve s θ ∈ criticalPoints (𝓡 4) (𝓡 2) (lekiliMove1 s) := by
  rw [criticalPoints_lekiliMove1]
  refine ⟨?_, rfl, rfl⟩
  simp only [lekiliMove1CritCurve, vec4_zero, vec4_one]
  nlinarith [Real.cos_sq_add_sin_sq θ]

/-- Critical-value deltoid curve `θ ↦ lekiliMove1 s (lekiliMove1CritCurve s θ)`. -/
noncomputable def lekiliMove1CritValue (s θ : ℝ) : EuclideanPlane :=
  lekiliMove1 s (lekiliMove1CritCurve s θ)

/-- Trigonometric expansion `s² (cos 2θ + 2 cos θ, sin 2θ - 2 sin θ)` of `lekiliMove1CritValue`.
-/
theorem lekiliMove1CritValue_eq (s θ : ℝ) :
    lekiliMove1CritValue s θ =
      vec2 (s ^ 2 * (Real.cos (2 * θ) + 2 * Real.cos θ))
        (s ^ 2 * (Real.sin (2 * θ) - 2 * Real.sin θ)) := by
  refine ext_vec2 ?_ ?_
  · simp only [lekiliMove1CritValue, lekiliMove1CritCurve, lekiliMove1_apply_zero, vec4_zero,
      vec4_one, vec4_two, vec4_three, vec2_zero, Real.cos_two_mul]
    nlinarith [Real.cos_sq_add_sin_sq θ]
  · simp only [lekiliMove1CritValue, lekiliMove1CritCurve, lekiliMove1_apply_one, vec4_zero,
      vec4_one, vec4_two, vec4_three, vec2_one, Real.sin_two_mul]
    ring

/-- Exact derivative of the critical-value curve `lekiliMove1CritValue s`. -/
theorem hasDerivAt_lekiliMove1CritValue (s θ : ℝ) :
    HasDerivAt (lekiliMove1CritValue s)
      (vec2 (s ^ 2 * (-2 * Real.sin (2 * θ) - 2 * Real.sin θ))
        (s ^ 2 * (2 * Real.cos (2 * θ) - 2 * Real.cos θ))) θ := by
  have heq : lekiliMove1CritValue s = fun t ↦
      vec2 (s ^ 2 * (Real.cos (2 * t) + 2 * Real.cos t))
        (s ^ 2 * (Real.sin (2 * t) - 2 * Real.sin t)) :=
    funext (lekiliMove1CritValue_eq s)
  rw [heq]
  have h2t : HasDerivAt (fun t : ℝ ↦ 2 * t) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have hc2 : HasDerivAt (fun t : ℝ ↦ Real.cos (2 * t)) (-Real.sin (2 * θ) * 2) θ :=
    (Real.hasDerivAt_cos (2 * θ)).comp θ h2t
  have hs2 : HasDerivAt (fun t : ℝ ↦ Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ h2t
  have h0 : HasDerivAt (fun t : ℝ ↦ s ^ 2 * (Real.cos (2 * t) + 2 * Real.cos t))
      (s ^ 2 * (-2 * Real.sin (2 * θ) - 2 * Real.sin θ)) θ := by
    convert (hc2.add ((Real.hasDerivAt_cos θ).const_mul 2)).const_mul (s ^ 2) using 1
    ring
  have h1 : HasDerivAt (fun t : ℝ ↦ s ^ 2 * (Real.sin (2 * t) - 2 * Real.sin t))
      (s ^ 2 * (2 * Real.cos (2 * θ) - 2 * Real.cos θ)) θ := by
    convert (hs2.sub ((Real.hasDerivAt_sin θ).const_mul 2)).const_mul (s ^ 2) using 1
    ring
  exact hasDerivAt_vec2 h0 h1

private theorem cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
  have h : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]
  ring

private theorem sin_two_pi_div_three : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
  have h : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [h, Real.sin_pi_sub, Real.sin_pi_div_three]

private theorem cos_four_pi_div_three : Real.cos (4 * Real.pi / 3) = -1 / 2 := by
  have h : 4 * Real.pi / 3 = Real.pi / 3 + Real.pi := by ring
  rw [h, Real.cos_add_pi, Real.cos_pi_div_three]
  ring

private theorem sin_four_pi_div_three : Real.sin (4 * Real.pi / 3) = -Real.sqrt 3 / 2 := by
  have h : 4 * Real.pi / 3 = Real.pi / 3 + Real.pi := by ring
  rw [h, Real.sin_add_pi, Real.sin_pi_div_three]
  ring

private theorem cos_eight_pi_div_three : Real.cos (2 * (4 * Real.pi / 3)) = -1 / 2 := by
  have h : 2 * (4 * Real.pi / 3) = 2 * Real.pi / 3 + 2 * Real.pi := by ring
  rw [h, Real.cos_add_two_pi, cos_two_pi_div_three]

private theorem sin_eight_pi_div_three :
    Real.sin (2 * (4 * Real.pi / 3)) = Real.sqrt 3 / 2 := by
  have h : 2 * (4 * Real.pi / 3) = 2 * Real.pi / 3 + 2 * Real.pi := by ring
  rw [h, Real.sin_add_two_pi, sin_two_pi_div_three]

/-- **Gate 5.2 (Three Deltoid Cusps)**: For `s ≠ 0`, `lekiliMove1CritValue s` has vanishing
derivative at the three angles `θ = 0, 2π/3, 4π/3`, achieves three pairwise distinct critical
values there, and has nonzero derivative (`vec2 0 (4 * s ^ 2)`) at `θ = π`. -/
theorem gate52_lekiliMove1_three_cusps (s : ℝ) (hs : s ≠ 0) :
    deriv (lekiliMove1CritValue s) 0 = 0 ∧
      deriv (lekiliMove1CritValue s) (2 * Real.pi / 3) = 0 ∧
      deriv (lekiliMove1CritValue s) (4 * Real.pi / 3) = 0 ∧
      deriv (lekiliMove1CritValue s) Real.pi = vec2 0 (4 * s ^ 2) ∧
      deriv (lekiliMove1CritValue s) Real.pi ≠ 0 ∧
      lekiliMove1CritValue s 0 ≠ lekiliMove1CritValue s (2 * Real.pi / 3) ∧
      lekiliMove1CritValue s 0 ≠ lekiliMove1CritValue s (4 * Real.pi / 3) ∧
      lekiliMove1CritValue s (2 * Real.pi / 3) ≠ lekiliMove1CritValue s (4 * Real.pi / 3) := by
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have hderiv (θ : ℝ) : deriv (lekiliMove1CritValue s) θ =
      vec2 (s ^ 2 * (-2 * Real.sin (2 * θ) - 2 * Real.sin θ))
        (s ^ 2 * (2 * Real.cos (2 * θ) - 2 * Real.cos θ)) :=
    (hasDerivAt_lekiliMove1CritValue s θ).deriv
  have h0 : deriv (lekiliMove1CritValue s) 0 = 0 := by
    rw [hderiv, mul_zero, Real.sin_zero, Real.cos_zero]
    refine ext_vec2 ?_ ?_ <;> (simp only [vec2_zero, vec2_one, PiLp.zero_apply]; ring)
  have h23 : deriv (lekiliMove1CritValue s) (2 * Real.pi / 3) = 0 := by
    rw [hderiv, show 2 * (2 * Real.pi / 3) = 4 * Real.pi / 3 by ring, cos_two_pi_div_three,
      sin_two_pi_div_three, cos_four_pi_div_three, sin_four_pi_div_three]
    refine ext_vec2 ?_ ?_ <;> (simp only [vec2_zero, vec2_one, PiLp.zero_apply]; ring)
  have h43 : deriv (lekiliMove1CritValue s) (4 * Real.pi / 3) = 0 := by
    rw [hderiv, cos_four_pi_div_three, sin_four_pi_div_three, cos_eight_pi_div_three,
      sin_eight_pi_div_three]
    refine ext_vec2 ?_ ?_ <;> (simp only [vec2_zero, vec2_one, PiLp.zero_apply]; ring)
  have hpi : deriv (lekiliMove1CritValue s) Real.pi = vec2 0 (4 * s ^ 2) := by
    rw [hderiv, Real.sin_two_mul, Real.cos_two_mul, Real.sin_pi, Real.cos_pi]
    refine ext_vec2 ?_ ?_ <;> (simp only [vec2_zero, vec2_one]; ring)
  have hpi_ne : deriv (lekiliMove1CritValue s) Real.pi ≠ 0 := by
    rw [hpi]
    intro h
    have h1 := congrArg (fun v : EuclideanPlane ↦ v 1) h
    simp only [vec2_one, PiLp.zero_apply] at h1
    exact hs2 (by linarith)
  have hv0 : lekiliMove1CritValue s 0 = vec2 (3 * s ^ 2) 0 := by
    rw [lekiliMove1CritValue_eq, mul_zero, Real.cos_zero, Real.sin_zero]
    refine ext_vec2 ?_ ?_ <;> (simp only [vec2_zero, vec2_one]; ring)
  have hv23 : lekiliMove1CritValue s (2 * Real.pi / 3) =
      vec2 (-3 / 2 * s ^ 2) (-3 * Real.sqrt 3 / 2 * s ^ 2) := by
    rw [lekiliMove1CritValue_eq, show 2 * (2 * Real.pi / 3) = 4 * Real.pi / 3 by ring,
      cos_two_pi_div_three, sin_two_pi_div_three, cos_four_pi_div_three, sin_four_pi_div_three]
    refine ext_vec2 ?_ ?_ <;> (simp only [vec2_zero, vec2_one]; ring)
  have hv43 : lekiliMove1CritValue s (4 * Real.pi / 3) =
      vec2 (-3 / 2 * s ^ 2) (3 * Real.sqrt 3 / 2 * s ^ 2) := by
    rw [lekiliMove1CritValue_eq, cos_four_pi_div_three, sin_four_pi_div_three,
      cos_eight_pi_div_three, sin_eight_pi_div_three]
    refine ext_vec2 ?_ ?_ <;> (simp only [vec2_zero, vec2_one]; ring)
  refine ⟨h0, h23, h43, hpi, hpi_ne, ?_, ?_, ?_⟩
  · intro h
    have h0c := congrArg (fun v : EuclideanPlane ↦ v 0) h
    rw [hv0, hv23, vec2_zero, vec2_zero] at h0c
    exact hs2 (by linarith)
  · intro h
    have h0c := congrArg (fun v : EuclideanPlane ↦ v 0) h
    rw [hv0, hv43, vec2_zero, vec2_zero] at h0c
    exact hs2 (by linarith)
  · intro h
    have h1c := congrArg (fun v : EuclideanPlane ↦ v 1) h
    rw [hv23, hv43, vec2_one, vec2_one] at h1c
    have hsqrt_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    have hprod : 3 * Real.sqrt 3 * s ^ 2 = 0 := by linarith
    have hs_zero : s ^ 2 = 0 := by
      rcases mul_eq_zero.mp hprod with h3 | hs0
      · exfalso; linarith
      · exact hs0
    exact hs2 hs_zero

end Move1AndGate52

/-! ## 2. Classification of All Critical Points of `lekiliMove1` (3 Cusps & Folds) -/

section Move1Singularities

/-- Transport `IsLocallyModeledOn (𝓡 4) (𝓡 2)` across global linear equivalences `D, T`. -/
-- tier: T2
theorem isLocallyModeledOn_comp_equiv
    {f g : EuclideanSpace ℝ (Fin 4) → EuclideanPlane}
    {model : EuclideanSpace ℝ (Fin 4) → EuclideanPlane}
    {p p₀ : EuclideanSpace ℝ (Fin 4)}
    (D : EuclideanSpace ℝ (Fin 4) ≃L[ℝ] EuclideanSpace ℝ (Fin 4))
    (T : EuclideanPlane ≃L[ℝ] EuclideanPlane)
    (heq : ∀ q, T (g q) = f (D q))
    (hf : IsLocallyModeledOn (𝓡 4) (𝓡 2) f (D p) model p₀) :
    IsLocallyModeledOn (𝓡 4) (𝓡 2) g p model p₀ := by
  obtain ⟨φ, ψ, hDpφ, hfDpψ, hφDp, hψfDp, hmodel⟩ := hf
  let Dp : PartialDiffeomorph (𝓡 4) (𝓡 4)
      (EuclideanSpace ℝ (Fin 4)) (EuclideanSpace ℝ (Fin 4)) ∞ := D.toPartialDiffeomorph
  let Tp : PartialDiffeomorph (𝓡 2) (𝓡 2) EuclideanPlane EuclideanPlane ∞ :=
    T.toPartialDiffeomorph
  let φ' := Dp.trans φ
  let ψ' := Tp.trans ψ
  have hφ'_src : φ'.source = Dp.source ∩ Dp.toPartialEquiv ⁻¹' φ.source :=
    PartialDiffeomorph.trans_source Dp φ
  have hψ'_src : ψ'.source = Tp.source ∩ Tp.toPartialEquiv ⁻¹' ψ.source :=
    PartialDiffeomorph.trans_source Tp ψ
  have hDp_eq : ∀ q, Dp.toPartialEquiv q = D q := fun q ↦ by
    simp [Dp, ContinuousLinearEquiv.toPartialDiffeomorph_toPartialEquiv]
  have hTp_eq : ∀ w, Tp.toPartialEquiv w = T w := fun w ↦ by
    simp [Tp, ContinuousLinearEquiv.toPartialDiffeomorph_toPartialEquiv]
  have hDp_src : ∀ q, q ∈ Dp.source := fun q ↦ by
    simp [Dp, ContinuousLinearEquiv.toPartialDiffeomorph_toPartialEquiv]
  have hTp_src : ∀ w, w ∈ Tp.source := fun w ↦ by
    simp [Tp, ContinuousLinearEquiv.toPartialDiffeomorph_toPartialEquiv]
  have hφ'_eq : ∀ q, φ' q = φ (D q) := fun q ↦ by
    rw [PartialDiffeomorph.coe_trans, Function.comp_apply, hDp_eq]
  have hψ'_eq : ∀ w, ψ' w = ψ (T w) := fun w ↦ by
    rw [PartialDiffeomorph.coe_trans, Function.comp_apply, hTp_eq]
  refine ⟨φ', ψ', ?_, ?_, ?_, ?_, ?_⟩
  · rw [hφ'_src]
    refine ⟨hDp_src p, ?_⟩
    rw [mem_preimage, hDp_eq]
    exact hDpφ
  · rw [hψ'_src]
    refine ⟨hTp_src (g p), ?_⟩
    rw [mem_preimage, hTp_eq, heq]
    exact hfDpψ
  · rw [hφ'_eq, hφDp]
  · rw [hψ'_eq, heq, hψfDp]
  · intro q hq
    rw [hφ'_src] at hq
    have hDq_mem : D q ∈ φ.source := by
      have hq' := hq.2
      rw [mem_preimage, hDp_eq] at hq'
      exact hq'
    obtain ⟨hmem, hmod⟩ := hmodel (D q) hDq_mem
    refine ⟨?_, ?_⟩
    · rw [hψ'_src]
      refine ⟨hTp_src (g q), ?_⟩
      rw [mem_preimage, hTp_eq, heq]
      exact hmem
    · rw [hψ'_eq, hφ'_eq, heq, hmod]

/-- Domain negation `(-p₀, -p₁, p₂, p₃)` reversing the sign of `s` in `lekiliMove1 s`. -/
private noncomputable def flipSignDom :
    EuclideanSpace ℝ (Fin 4) ≃L[ℝ] EuclideanSpace ℝ (Fin 4) where
  toFun p := vec4 (-p 0) (-p 1) (p 2) (p 3)
  invFun p := vec4 (-p 0) (-p 1) (p 2) (p 3)
  map_add' u v := by refine ext_vec4 ?_ ?_ ?_ ?_ <;> simp [add_comm]
  map_smul' r v := by refine ext_vec4 ?_ ?_ ?_ ?_ <;> simp
  left_inv v := by refine ext_vec4 ?_ ?_ ?_ ?_ <;> simp
  right_inv v := by refine ext_vec4 ?_ ?_ ?_ ?_ <;> simp
  continuous_toFun := continuous_vec4
    (euclidProj 0).continuous.neg (euclidProj 1).continuous.neg
    (euclidProj 2).continuous (euclidProj 3).continuous
  continuous_invFun := continuous_vec4
    (euclidProj 0).continuous.neg (euclidProj 1).continuous.neg
    (euclidProj 2).continuous (euclidProj 3).continuous

private theorem flipSignDom_apply (p : EuclideanSpace ℝ (Fin 4)) :
    flipSignDom p = vec4 (-p 0) (-p 1) (p 2) (p 3) := rfl

@[simp]
private theorem lekiliMove1_flipSignDom (s : ℝ) (p : EuclideanSpace ℝ (Fin 4)) :
    lekiliMove1 s (flipSignDom p) = lekiliMove1 (-s) p := by
  refine ext_vec2 ?_ ?_ <;>
    (simp only [lekiliMove1, realLefschetzMap, flipSignDom_apply, PiLp.add_apply,
       vec4_zero, vec4_one, vec4_two, vec4_three, vec2_zero, vec2_one]; ring)

/-- Domain `2π/3`-rotation `z₁ ↦ ω z₁, z₂ ↦ ω z₂` with `ω = -1/2 + i √3/2`. -/
private noncomputable def rotC3Dom :
    EuclideanSpace ℝ (Fin 4) ≃L[ℝ] EuclideanSpace ℝ (Fin 4) where
  toFun p := vec4 (-1 / 2 * p 0 - Real.sqrt 3 / 2 * p 1)
    (Real.sqrt 3 / 2 * p 0 - 1 / 2 * p 1)
    (-1 / 2 * p 2 - Real.sqrt 3 / 2 * p 3)
    (Real.sqrt 3 / 2 * p 2 - 1 / 2 * p 3)
  invFun p := vec4 (-1 / 2 * p 0 + Real.sqrt 3 / 2 * p 1)
    (-Real.sqrt 3 / 2 * p 0 - 1 / 2 * p 1)
    (-1 / 2 * p 2 + Real.sqrt 3 / 2 * p 3)
    (-Real.sqrt 3 / 2 * p 2 - 1 / 2 * p 3)
  map_add' u v := by refine ext_vec4 ?_ ?_ ?_ ?_ <;> (simp; ring)
  map_smul' r v := by refine ext_vec4 ?_ ?_ ?_ ?_ <;> (simp; ring)
  left_inv v := by
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    refine ext_vec4 ?_ ?_ ?_ ?_ <;>
      (simp only [vec4_zero, vec4_one, vec4_two, vec4_three]; ring_nf; rw [h3]; ring)
  right_inv v := by
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    refine ext_vec4 ?_ ?_ ?_ ?_ <;>
      (simp only [vec4_zero, vec4_one, vec4_two, vec4_three]; ring_nf; rw [h3]; ring)
  continuous_toFun := continuous_vec4
    ((continuous_const.mul (euclidProj 0).continuous).sub
      (continuous_const.mul (euclidProj 1).continuous))
    ((continuous_const.mul (euclidProj 0).continuous).sub
      (continuous_const.mul (euclidProj 1).continuous))
    ((continuous_const.mul (euclidProj 2).continuous).sub
      (continuous_const.mul (euclidProj 3).continuous))
    ((continuous_const.mul (euclidProj 2).continuous).sub
      (continuous_const.mul (euclidProj 3).continuous))
  continuous_invFun := continuous_vec4
    ((continuous_const.mul (euclidProj 0).continuous).add
      (continuous_const.mul (euclidProj 1).continuous))
    ((continuous_const.mul (euclidProj 0).continuous).sub
      (continuous_const.mul (euclidProj 1).continuous))
    ((continuous_const.mul (euclidProj 2).continuous).add
      (continuous_const.mul (euclidProj 3).continuous))
    ((continuous_const.mul (euclidProj 2).continuous).sub
      (continuous_const.mul (euclidProj 3).continuous))

private theorem rotC3Dom_apply (p : EuclideanSpace ℝ (Fin 4)) :
    rotC3Dom p = vec4 (-1 / 2 * p 0 - Real.sqrt 3 / 2 * p 1)
      (Real.sqrt 3 / 2 * p 0 - 1 / 2 * p 1)
      (-1 / 2 * p 2 - Real.sqrt 3 / 2 * p 3)
      (Real.sqrt 3 / 2 * p 2 - 1 / 2 * p 3) := rfl

/-- Target `4π/3`-rotation `w ↦ ω² w` intertwining `rotC3Dom` with `lekiliMove1 s`. -/
private noncomputable def rotC3Tgt : EuclideanPlane ≃L[ℝ] EuclideanPlane where
  toFun w := vec2 (-1 / 2 * w 0 + Real.sqrt 3 / 2 * w 1)
    (-Real.sqrt 3 / 2 * w 0 - 1 / 2 * w 1)
  invFun w := vec2 (-1 / 2 * w 0 - Real.sqrt 3 / 2 * w 1)
    (Real.sqrt 3 / 2 * w 0 - 1 / 2 * w 1)
  map_add' u v := by refine ext_vec2 ?_ ?_ <;> (simp; ring)
  map_smul' r v := by refine ext_vec2 ?_ ?_ <;> (simp; ring)
  left_inv v := by
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    refine ext_vec2 ?_ ?_ <;>
      (simp only [vec2_zero, vec2_one]; ring_nf; rw [h3]; ring)
  right_inv v := by
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    refine ext_vec2 ?_ ?_ <;>
      (simp only [vec2_zero, vec2_one]; ring_nf; rw [h3]; ring)
  continuous_toFun := continuous_vec2
    ((continuous_const.mul (euclidProj 0).continuous).add
      (continuous_const.mul (euclidProj 1).continuous))
    ((continuous_const.mul (euclidProj 0).continuous).sub
      (continuous_const.mul (euclidProj 1).continuous))
  continuous_invFun := continuous_vec2
    ((continuous_const.mul (euclidProj 0).continuous).sub
      (continuous_const.mul (euclidProj 1).continuous))
    ((continuous_const.mul (euclidProj 0).continuous).sub
      (continuous_const.mul (euclidProj 1).continuous))

private theorem rotC3Tgt_apply (w : EuclideanPlane) :
    rotC3Tgt w = vec2 (-1 / 2 * w 0 + Real.sqrt 3 / 2 * w 1)
      (-Real.sqrt 3 / 2 * w 0 - 1 / 2 * w 1) := rfl

private theorem lekiliMove1_rotC3Dom (s : ℝ) (p : EuclideanSpace ℝ (Fin 4)) :
    lekiliMove1 s (rotC3Dom p) = rotC3Tgt (lekiliMove1 s p) := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ext_vec2 ?_ ?_ <;>
    (simp only [lekiliMove1, realLefschetzMap, rotC3Dom_apply, rotC3Tgt_apply, PiLp.add_apply,
       vec4_zero, vec4_one, vec4_two, vec4_three, vec2_zero, vec2_one];
     ring_nf;
     rw [h3];
     ring)

/-- Exhaustion of the 3 cusp points on `criticalPoints (lekiliMove1 s)` where `p₀³ - 3 p₀ p₁² = s³`.
-/
private theorem eq_cusp_orbit_of_cubed_eq {s : ℝ} {p : EuclideanSpace ℝ (Fin 4)}
    (hp : p ∈ criticalPoints (𝓡 4) (𝓡 2) (lekiliMove1 s))
    (hcusp : p 0 ^ 3 - 3 * p 0 * p 1 ^ 2 = s ^ 3) :
    p = vec4 s 0 0 0 ∨
      p = rotC3Dom (vec4 s 0 0 0) ∨
      p = rotC3Dom (rotC3Dom (vec4 s 0 0 0)) := by
  rw [criticalPoints_lekiliMove1, Set.mem_ofPred_eq] at hp
  obtain ⟨h01, hp2, hp3⟩ := hp
  have hfac : (p 0 - s) * (2 * p 0 + s) ^ 2 = 0 := by
    linear_combination hcusp + 3 * p 0 * h01
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rcases mul_eq_zero.mp hfac with hp0s | h2p0s
  · left
    have hp0 : p 0 = s := sub_eq_zero.mp hp0s
    have hp1sq : p 1 ^ 2 = 0 := by linear_combination h01 - (p 0 + s) * hp0
    have hp1 : p 1 = 0 := sq_eq_zero_iff.mp hp1sq
    exact ext_vec4 hp0 hp1 hp2 hp3
  · right
    have h2p0 : 2 * p 0 + s = 0 := sq_eq_zero_iff.mp h2p0s
    have hp0 : p 0 = -1 / 2 * s := by linarith
    have hp1sq : p 1 ^ 2 = (Real.sqrt 3 / 2 * s) ^ 2 := by
      calc
        p 1 ^ 2 = s ^ 2 - p 0 ^ 2 := by linarith
        _ = 3 / 4 * s ^ 2 := by rw [hp0]; ring
        _ = Real.sqrt 3 ^ 2 / 4 * s ^ 2 := by rw [h3]
        _ = (Real.sqrt 3 / 2 * s) ^ 2 := by ring
    have hrot1 : rotC3Dom (vec4 s 0 0 0) = vec4 (-1 / 2 * s) (Real.sqrt 3 / 2 * s) 0 0 := by
      refine ext_vec4 ?_ ?_ ?_ ?_ <;>
        (simp only [rotC3Dom_apply, vec4_zero, vec4_one, vec4_two, vec4_three]; ring)
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hp1sq with hp1 | hp1
    · left
      rw [hrot1]
      exact ext_vec4 hp0 hp1 hp2 hp3
    · right
      rw [hrot1]
      refine ext_vec4 ?_ ?_ ?_ ?_
      · simp only [rotC3Dom_apply, vec4_zero, vec4_one, hp0]; ring_nf; rw [h3]; ring
      · simp only [rotC3Dom_apply, vec4_zero, vec4_one, hp1]; ring
      · simp only [rotC3Dom_apply, vec4_two, vec4_three, hp2]; ring
      · simp only [rotC3Dom_apply, vec4_two, vec4_three, hp3]; ring

/-- Auxiliary lemma: `(TauCeti.sqrtNearOne ℝ x)^2 = x` near `x = 1` gives
`deriv sqrtNearOne 1 = 1/2`. -/
private theorem deriv_sqrtNearOne_one : deriv (TauCeti.sqrtNearOne ℝ) 1 = 1 / 2 := by
  have hev : (fun x : ℝ ↦ TauCeti.sqrtNearOne ℝ x * TauCeti.sqrtNearOne ℝ x) =ᶠ[𝓝 1] id := by
    filter_upwards [Metric.ball_mem_nhds (1 : ℝ) zero_lt_one] with x hx
    exact TauCeti.mul_self_sqrtNearOne hx
  have hdiff : DifferentiableAt ℝ (TauCeti.sqrtNearOne ℝ) 1 :=
    (TauCeti.analyticAt_sqrtNearOne (A := ℝ)).differentiableAt
  have hprod := (hdiff.hasDerivAt).mul (hdiff.hasDerivAt)
  have hid : HasDerivAt id 1 (1 : ℝ) := hasDerivAt_id 1
  have hsq : HasDerivAt id
      (deriv (TauCeti.sqrtNearOne ℝ) 1 * TauCeti.sqrtNearOne ℝ 1 +
        TauCeti.sqrtNearOne ℝ 1 * deriv (TauCeti.sqrtNearOne ℝ) 1) 1 :=
    hprod.congr_of_eventuallyEq hev.symm
  have heq := hid.unique hsq
  rw [TauCeti.sqrtNearOne_one] at heq
  linarith

/-- Cusp normal form at `(s, 0, 0, 0)` for `0 < s` via `d = 3` real Weierstrass preparation. -/
-- tier: T2
private theorem isWrinkledCuspAt_lekiliMove1_pos {s : ℝ} (hs : 0 < s) :
    IsWrinkledCuspAt (𝓡 4) (𝓡 2) (lekiliMove1 s) (vec4 s 0 0 0) := by
  let p_star := vec4 s 0 0 0
  let s4 : ℝ := 4 * s ^ 2
  let m2 : ℝ := 2 * s
  have hs4 : 0 < s4 := by positivity
  have hm2 : 0 < m2 := by positivity
  have hs4_ne : s4 ≠ 0 := hs4.ne'
  have hm2_ne : m2 ≠ 0 := hm2.ne'
  let toF2 : EuclideanPlane → (Fin 2 → ℝ) := fun w i ↦ w i
  let G : (Fin 2 → ℝ) × ℝ → ℝ := fun q ↦
    2 * q.2 * (m2 * TauCeti.sqrtNearOne ℝ (1 + (q.1 0 + q.2 ^ 2) / s4) - m2) - q.1 1
  have hG_an : AnalyticAt ℝ G ((0 : Fin 2 → ℝ), (0 : ℝ)) := by
    have hq10 : AnalyticAt ℝ (fun q : (Fin 2 → ℝ) × ℝ ↦ q.1 0) (0, 0) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0).analyticAt _).comp
        analyticAt_fst
    have hq11 : AnalyticAt ℝ (fun q : (Fin 2 → ℝ) × ℝ ↦ q.1 1) (0, 0) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1).analyticAt _).comp
        analyticAt_fst
    have hq2 : AnalyticAt ℝ (fun q : (Fin 2 → ℝ) × ℝ ↦ q.2) (0, 0) := analyticAt_snd
    have harg : AnalyticAt ℝ (fun q : (Fin 2 → ℝ) × ℝ ↦ 1 + (q.1 0 + q.2 ^ 2) / s4) (0, 0) :=
      analyticAt_const.add ((hq10.add (hq2.pow 2)).div analyticAt_const hs4_ne)
    have hsqrt : AnalyticAt ℝ
        (fun q : (Fin 2 → ℝ) × ℝ ↦ TauCeti.sqrtNearOne ℝ (1 + (q.1 0 + q.2 ^ 2) / s4))
        (0, 0) := by
      have h0 : (1 + ((0 : Fin 2 → ℝ) 0 + (0 : ℝ) ^ 2) / s4) = 1 := by simp
      have hsq :
          AnalyticAt ℝ (TauCeti.sqrtNearOne ℝ) (1 + ((0 : Fin 2 → ℝ) 0 + (0 : ℝ) ^ 2) / s4) := by
        rw [h0]
        exact TauCeti.analyticAt_sqrtNearOne (A := ℝ)
      exact hsq.comp (f := fun q : (Fin 2 → ℝ) × ℝ ↦ 1 + (q.1 0 + q.2 ^ 2) / s4) harg
    exact ((analyticAt_const.mul hq2).mul ((analyticAt_const.mul hsqrt).sub analyticAt_const)).sub
      hq11
  let den0 : ℝ → ℝ := fun y ↦ m2 * TauCeti.sqrtNearOne ℝ (1 + y ^ 2 / s4) + m2
  have hden0_an : AnalyticAt ℝ den0 0 := by
    have harg : AnalyticAt ℝ (fun y : ℝ ↦ 1 + y ^ 2 / s4) 0 :=
      analyticAt_const.add ((analyticAt_id.pow 2).div analyticAt_const hs4_ne)
    have hsqrt : AnalyticAt ℝ (fun y : ℝ ↦ TauCeti.sqrtNearOne ℝ (1 + y ^ 2 / s4)) 0 := by
      have h0 : 1 + (0 : ℝ) ^ 2 / s4 = 1 := by simp
      have hsq : AnalyticAt ℝ (TauCeti.sqrtNearOne ℝ) (1 + (0 : ℝ) ^ 2 / s4) := by
        rw [h0]
        exact TauCeti.analyticAt_sqrtNearOne (A := ℝ)
      exact hsq.comp (f := fun y : ℝ ↦ 1 + y ^ 2 / s4) harg
    exact (analyticAt_const.mul hsqrt).add analyticAt_const
  have hden0_val : den0 0 = 4 * s := by
    simp [den0, m2, TauCeti.sqrtNearOne_one]
    ring
  have hden0_ne : den0 0 ≠ 0 := by rw [hden0_val]; positivity
  have hG_slice : (fun y : ℝ ↦ G (0, y)) =ᶠ[𝓝 0] fun y ↦ y ^ 3 * (2 / den0 y) := by
    have h1 : ∀ᶠ y in 𝓝 (0 : ℝ), ‖(1 + y ^ 2 / s4) - 1‖ < 1 := by
      have hc : ContinuousAt (fun y : ℝ ↦ 1 + y ^ 2 / s4) 0 := by fun_prop
      have hmem : Metric.ball (1 : ℝ) 1 ∈ 𝓝 ((fun y : ℝ ↦ 1 + y ^ 2 / s4) 0) := by
        simpa using Metric.ball_mem_nhds (1 : ℝ) zero_lt_one
      exact hc hmem
    have h2 : ∀ᶠ y in 𝓝 (0 : ℝ), den0 y ≠ 0 :=
      hden0_an.continuousAt.eventually_ne hden0_ne
    filter_upwards [h1, h2] with y hy1 hy2
    have hsq : TauCeti.sqrtNearOne ℝ (1 + y ^ 2 / s4) ^ 2 = 1 + y ^ 2 / s4 := by
      simpa [sq] using TauCeti.mul_self_sqrtNearOne hy1
    have hm2_sq : m2 ^ 2 = s4 := by simp [m2, s4]; ring
    have hdiff_sq :
        (m2 * TauCeti.sqrtNearOne ℝ (1 + y ^ 2 / s4) - m2) * den0 y = y ^ 2 := by
      dsimp only [den0]
      calc
        (m2 * TauCeti.sqrtNearOne ℝ (1 + y ^ 2 / s4) - m2) *
            (m2 * TauCeti.sqrtNearOne ℝ (1 + y ^ 2 / s4) + m2)
          = m2 ^ 2 * TauCeti.sqrtNearOne ℝ (1 + y ^ 2 / s4) ^ 2 - m2 ^ 2 := by ring
        _ = s4 * (1 + y ^ 2 / s4) - s4 := by rw [hsq, hm2_sq]
        _ = y ^ 2 := by field_simp [hs4_ne]; ring
    dsimp only [G]
    simp only [Pi.zero_apply, zero_add, sub_zero]
    rw [← mul_div_assoc, eq_div_iff hy2]
    linear_combination 2 * y * hdiff_sq
  have hord : analyticOrderAt (fun y : ℝ ↦ G (0, y)) 0 = (3 : ℕ) := by
    rw [analyticOrderAt_congr hG_slice]
    have hq_an : AnalyticAt ℝ (fun y : ℝ ↦ 2 / den0 y) 0 :=
      analyticAt_const.div hden0_an hden0_ne
    have hq_ne : (2 / den0 0 : ℝ) ≠ 0 := div_ne_zero (by norm_num) hden0_ne
    have hpow_an : AnalyticAt ℝ ((id : ℝ → ℝ) ^ 3) 0 := analyticAt_id.pow 3
    have hmul : analyticOrderAt (((id : ℝ → ℝ) ^ 3) * (fun y : ℝ ↦ 2 / den0 y)) 0 =
        analyticOrderAt ((id : ℝ → ℝ) ^ 3) 0 + analyticOrderAt (fun y : ℝ ↦ 2 / den0 y) 0 :=
      analyticOrderAt_mul hpow_an hq_an
    change analyticOrderAt (((id : ℝ → ℝ) ^ 3) * (fun y : ℝ ↦ 2 / den0 y)) 0 = (3 : ℕ)
    rw [hmul, analyticOrderAt_pow analyticAt_id 3, analyticOrderAt_id,
      (hq_an.analyticOrderAt_eq_zero).2 hq_ne]
    simp
  obtain ⟨c, u, hc_an, hc0, hu_an, hu0, heq_wp⟩ :=
    hG_an.exists_weierstrassPreparation_real hord
  have hu_val : u (0, 0) = 1 / (2 * s) := by
    have hcomb : (fun y : ℝ ↦ y ^ 3 * u (0, y)) =ᶠ[𝓝 0] fun y ↦ y ^ 3 * (2 / den0 y) := by
      have hslice_ev : (fun y : ℝ ↦ G (0, y)) =ᶠ[𝓝 0] fun y ↦ y ^ 3 * u (0, y) := by
        have ht : Tendsto (fun y : ℝ ↦ ((0 : Fin 2 → ℝ), y)) (𝓝 0) (𝓝 (0, 0)) :=
          ContinuousAt.tendsto (continuousAt_const.prodMk continuousAt_id)
        filter_upwards [ht.eventually heq_wp] with y hy
        rw [hy, TauCeti.Polynomial.eval_monicOfCoeff, Fin.sum_univ_three]
        simp [hc0, sub_zero]
      exact hslice_ev.symm.trans hG_slice
    have hu_eq : (fun y : ℝ ↦ u (0, y)) =ᶠ[𝓝[≠] 0] fun y ↦ 2 / den0 y := by
      filter_upwards [nhdsWithin_le_nhds hcomb, self_mem_nhdsWithin] with y hy hy0
      have hy3 : y ^ 3 ≠ 0 := pow_ne_zero 3 hy0
      exact mul_left_cancel₀ hy3 hy
    have ht1 : Tendsto (fun y : ℝ ↦ u (0, y)) (𝓝[≠] 0) (𝓝 (u (0, 0))) :=
      ((hu_an.continuousAt.comp (continuousAt_const.prodMk continuousAt_id))).mono_left
        nhdsWithin_le_nhds
    have ht2 : Tendsto (fun y : ℝ ↦ 2 / den0 y) (𝓝[≠] 0) (𝓝 (2 / den0 0)) :=
      ((analyticAt_const.div hden0_an hden0_ne).continuousAt).mono_left nhdsWithin_le_nhds
    have hu_eq_lim := tendsto_nhds_unique ht1 (ht2.congr' hu_eq.symm)
    rw [hu_eq_lim, hden0_val]
    field_simp [hs.ne']
    ring
  have hu_pos : 0 < u (0, 0) := by rw [hu_val]; positivity
  have hc0_fderiv : fderiv ℝ (c 0) 0 = (-2 * s) • ContinuousLinearMap.proj 1 := by
    have hprod_ev : (fun w : Fin 2 → ℝ ↦ c 0 w * u (w, 0)) =ᶠ[𝓝 0] fun w ↦ -w 1 := by
      have ht : Tendsto (fun w : Fin 2 → ℝ ↦ (w, (0 : ℝ))) (𝓝 0) (𝓝 (0, 0)) :=
        ContinuousAt.tendsto (continuousAt_id.prodMk continuousAt_const)
      filter_upwards [ht.eventually heq_wp] with w hw
      have hG0 : G (w, 0) = -w 1 := by simp [G]
      rw [← hG0, hw, TauCeti.Polynomial.eval_monicOfCoeff, Fin.sum_univ_three]
      simp
    have h1 : HasFDerivAt (fun w : Fin 2 → ℝ ↦ c 0 w * u (w, 0))
        (u (0, 0) • fderiv ℝ (c 0) 0) 0 := by
      have hc0d : HasFDerivAt (c 0) (fderiv ℝ (c 0) 0) 0 :=
        (hc_an 0).differentiableAt.hasFDerivAt
      have hud : HasFDerivAt (fun w : Fin 2 → ℝ ↦ u (w, (0 : ℝ)))
          (fderiv ℝ (fun w : Fin 2 → ℝ ↦ u (w, (0 : ℝ))) 0) 0 := by
        have hmap : AnalyticAt ℝ (fun w : Fin 2 → ℝ ↦ (w, (0 : ℝ))) 0 :=
          (analyticAt_id (𝕜 := ℝ) (E := Fin 2 → ℝ)).prod
            (analyticAt_const (𝕜 := ℝ) (v := (0 : ℝ)))
        exact (hu_an.comp_of_eq hmap rfl).differentiableAt.hasFDerivAt
      have hm := hc0d.mul hud
      refine hm.congr_fderiv ?_
      ext v
      simp [smul_apply, hc0 0, zero_smul]
    have h2 : HasFDerivAt (fun w : Fin 2 → ℝ ↦ -w 1)
        (-(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1)) 0 :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1).hasFDerivAt).neg
    have hfeq := h1.unique (h2.congr_of_eventuallyEq hprod_ev)
    rw [hu_val] at hfeq
    ext v
    have hscal : 2 * s * ((1 / (2 * s)) * fderiv ℝ (c 0) 0 v) = -(2 * s * v 1) := by
      have hv := congrArg (fun F : (Fin 2 → ℝ) →L[ℝ] ℝ ↦ 2 * s * F v) hfeq
      simpa [smul_apply, smul_eq_mul] using hv
    have hcancel : 2 * s * (1 / (2 * s)) = 1 := by field_simp [hs.ne']
    calc
      fderiv ℝ (c 0) 0 v = 2 * s * (1 / (2 * s)) * fderiv ℝ (c 0) 0 v := by rw [hcancel, one_mul]
      _ = 2 * s * ((1 / (2 * s)) * fderiv ℝ (c 0) 0 v) := by ring
      _ = -(2 * s * v 1) := hscal
      _ = -2 * s * v 1 := by ring
  let v₀ : Fin 2 → ℝ := ![1, 0]
  have hc1_v0 : (fderiv ℝ (c 1) 0) v₀ = 1 := by
    have hG_t_eq : ∀ᶠ ty in 𝓝 ((0 : ℝ), (0 : ℝ)),
        G (ty.1 • v₀, ty.2) =
          (ty.2 ^ 3 + ∑ i : Fin 3, c i (ty.1 • v₀) * ty.2 ^ (i : ℕ)) * u (ty.1 • v₀, ty.2) ∧
          ‖(1 + (ty.1 + ty.2 ^ 2) / s4) - 1‖ < 1 ∧
          AnalyticAt ℝ u (ty.1 • v₀, ty.2) := by
      have ht1 : ContinuousAt (fun ty : ℝ × ℝ ↦ (ty.1 • v₀, ty.2)) (0, 0) :=
        ((continuousAt_fst.smul continuousAt_const).prodMk continuousAt_snd)
      have ht2 : ContinuousAt (fun ty : ℝ × ℝ ↦ 1 + (ty.1 + ty.2 ^ 2) / s4) (0, 0) := by
        fun_prop
      have h00 : ((0 : ℝ) • v₀, (0 : ℝ)) = ((0 : Fin 2 → ℝ), (0 : ℝ)) := by simp
      have hball0 : Metric.ball (1 : ℝ) 1 ∈
          𝓝 ((fun ty : ℝ × ℝ ↦ 1 + (ty.1 + ty.2 ^ 2) / s4) (0, 0)) := by
        simpa using Metric.ball_mem_nhds (1 : ℝ) zero_lt_one
      filter_upwards [ht1.tendsto.eventually (h00 ▸ heq_wp), ht2 hball0,
        ht1.tendsto.eventually (h00 ▸ hu_an.eventually_analyticAt)] with ty hty1 hty2 hty3
      refine ⟨?_, by simpa [Metric.mem_ball, dist_eq_norm] using hty2, hty3⟩
      rw [hty1, TauCeti.Polynomial.eval_monicOfCoeff, sub_zero]
    obtain ⟨r, hr_pos, hr_sub⟩ := Metric.eventually_nhds_iff.mp hG_t_eq
    have hc_deriv (i : Fin 3) :
        HasDerivAt (fun t : ℝ ↦ c i (t • v₀)) ((fderiv ℝ (c i) 0) v₀) 0 := by
      rw [hasDerivAt_iff_hasFDerivAt]
      have h0v : (0 : ℝ) • v₀ = 0 := zero_smul _ _
      have hf := (hc_an i).differentiableAt.hasFDerivAt
      rw [← h0v] at hf
      have hcomp := hf.comp (0 : ℝ) ((hasFDerivAt_id (0 : ℝ)).smul_const v₀)
      refine hcomp.congr_fderiv ?_
      apply ContinuousLinearMap.ext_ring
      simp [one_smul]
    have hc0_v0 : (fderiv ℝ (c 0) 0) v₀ = 0 := by
      simp [hc0_fderiv, v₀]
    have hu_cont_t : ContinuousAt (fun y : ℝ ↦ (fderiv ℝ u (0, y)) (v₀, 0)) 0 := by
      have hudiff : ContinuousAt (fderiv ℝ u) (0, 0) :=
        ((hu_an.contDiffAt (n := ∞)).fderiv_right (m := 0) (by simp)).continuousAt
      have hev_eval : ContinuousAt
          (fun F : (Fin 2 → ℝ) × ℝ →L[ℝ] ℝ ↦ F (v₀, 0)) (fderiv ℝ u (0, 0)) :=
        (ContinuousLinearMap.apply ℝ ℝ (v₀, (0 : ℝ))).continuous.continuousAt
      exact hev_eval.tendsto.comp
        (hudiff.tendsto.comp (continuousAt_const.prodMk continuousAt_id).tendsto)
    have hsqrt_deriv_at (y : ℝ) (hmem : 1 + y ^ 2 / s4 ∈ Metric.ball (1 : ℝ) 1) :
        HasDerivAt (fun t : ℝ ↦ TauCeti.sqrtNearOne ℝ (1 + (t + y ^ 2) / s4))
          (deriv (TauCeti.sqrtNearOne ℝ) (1 + y ^ 2 / s4) * (1 / s4)) 0 := by
      have ha' : AnalyticAt ℝ (TauCeti.sqrtNearOne ℝ) (1 + y ^ 2 / s4) :=
        TauCeti.analyticOnNhd_sqrtNearOne (A := ℝ) _ hmem
      have h0y : 1 + ((0 : ℝ) + y ^ 2) / s4 = 1 + y ^ 2 / s4 := by simp
      have harg : HasDerivAt (fun t : ℝ ↦ 1 + (t + y ^ 2) / s4) (1 / s4) 0 := by
        have h1 := ((hasDerivAt_id (0 : ℝ)).add_const (y ^ 2)).mul_const (1 / s4)
        have h2 := h1.const_add (1 : ℝ)
        refine (h2.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)).congr_deriv ?_
        · dsimp only [id_eq]; ring
        · simp
      rw [← h0y] at ha'
      exact (ha'.differentiableAt.hasDerivAt.comp (0 : ℝ) harg).congr_deriv (by rw [h0y])
    have hderiv_eq : (fun y : ℝ ↦ 2 * (m2 / s4) * deriv (TauCeti.sqrtNearOne ℝ) (1 + y ^ 2 / s4))
        =ᶠ[𝓝[≠] 0] fun y : ℝ ↦
          ((fderiv ℝ (c 2) 0) v₀ * y + (fderiv ℝ (c 1) 0) v₀) * u (0, y) +
            y ^ 2 * (fderiv ℝ u (0, y)) (v₀, 0) := by
      have hball : Metric.ball (0 : ℝ) (r / 2) ∈ 𝓝 (0 : ℝ) :=
        Metric.ball_mem_nhds 0 (half_pos hr_pos)
      filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with y hy hy0
      have hy_abs : |y| < r / 2 := by simpa [Metric.mem_ball, Real.dist_eq] using hy
      have h0y_ball : dist ((0 : ℝ), y) (0, 0) < r := by
        calc
          dist ((0 : ℝ), y) (0, 0) = |y| := by simp [Prod.dist_eq]
          _ < r / 2 := hy_abs
          _ < r := by linarith
      have hmem1 : 1 + y ^ 2 / s4 ∈ Metric.ball (1 : ℝ) 1 := by
        simpa [Metric.mem_ball, dist_eq_norm] using (hr_sub h0y_ball).2.1
      have hu_y_an : AnalyticAt ℝ u (0, y) := by simpa using (hr_sub h0y_ball).2.2
      have h_ty_eq : (fun t : ℝ ↦ G (t • v₀, y)) =ᶠ[𝓝 0] fun t : ℝ ↦
          (y ^ 3 + (c 0 (t • v₀) * 1 + c 1 (t • v₀) * y + c 2 (t • v₀) * y ^ 2)) *
            u (t • v₀, y) := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (half_pos hr_pos)] with t ht
        have ht_abs : |t| < r / 2 := by simpa [Metric.mem_ball, Real.dist_eq] using ht
        have hty_ball : dist (t, y) (0, 0) < r := by
          rw [Prod.dist_eq]
          exact max_lt (by simpa [Real.dist_eq] using ht_abs.trans (by linarith))
            (by simpa [Real.dist_eq] using hy_abs.trans (by linarith))
        have h1 := (hr_sub hty_ball).1
        rw [Fin.sum_univ_three] at h1
        simpa [pow_zero, pow_one] using h1
      have hL : HasDerivAt (fun t : ℝ ↦ G (t • v₀, y))
          (2 * y * (m2 / s4) * deriv (TauCeti.sqrtNearOne ℝ) (1 + y ^ 2 / s4)) 0 := by
        have hg0 : (fun t : ℝ ↦ G (t • v₀, y)) = fun t : ℝ ↦
            2 * y * (m2 * TauCeti.sqrtNearOne ℝ (1 + (t + y ^ 2) / s4) - m2) := by
          funext t
          simp [G, v₀]
        rw [hg0]
        have hs' := ((hsqrt_deriv_at y hmem1).const_mul m2).sub_const m2 |>.const_mul (2 * y)
        refine hs'.congr_deriv ?_
        ring
      have hpoly : HasDerivAt
          (fun t : ℝ ↦ y ^ 3 + (c 0 (t • v₀) * 1 + c 1 (t • v₀) * y + c 2 (t • v₀) * y ^ 2))
          ((fderiv ℝ (c 1) 0) v₀ * y + (fderiv ℝ (c 2) 0) v₀ * y ^ 2) 0 := by
        have hp1 := ((hc_deriv 0).mul_const 1).add ((hc_deriv 1).mul_const y)
        have hp2 := (hp1.add ((hc_deriv 2).mul_const (y ^ 2))).const_add (y ^ 3)
        refine hp2.congr_deriv ?_
        rw [hc0_v0]
        ring
      have hu_t : HasDerivAt (fun t : ℝ ↦ u (t • v₀, y)) ((fderiv ℝ u (0, y)) (v₀, 0)) 0 := by
        rw [hasDerivAt_iff_hasFDerivAt]
        have h0vy : ((0 : ℝ) • v₀, y) = ((0 : Fin 2 → ℝ), y) := by simp
        have hpath : HasFDerivAt (fun t : ℝ ↦ (t • v₀, y))
            (((ContinuousLinearMap.id ℝ ℝ).smulRight v₀).prod (0 : ℝ →L[ℝ] ℝ)) 0 := by
          exact ((hasFDerivAt_id (0 : ℝ)).smul_const v₀).prodMk (hasFDerivAt_const y (0 : ℝ))
        have hu_f := hu_y_an.differentiableAt.hasFDerivAt
        rw [← h0vy] at hu_f
        refine (hu_f.comp (0 : ℝ) hpath).congr_fderiv ?_
        apply ContinuousLinearMap.ext_ring
        simp
      have hR := (hpoly.mul hu_t).congr_of_eventuallyEq h_ty_eq
      have heq_d := hL.unique hR
      simp only [zero_smul, hc0, zero_mul, add_zero] at heq_d
      apply mul_left_cancel₀ hy0
      linear_combination heq_d
    have ht_lhs : Tendsto
        (fun y : ℝ ↦ 2 * (m2 / s4) * deriv (TauCeti.sqrtNearOne ℝ) (1 + y ^ 2 / s4))
        (𝓝[≠] 0)
        (𝓝 (2 * (m2 / s4) * deriv (TauCeti.sqrtNearOne ℝ) 1)) := by
      have hcd : ContinuousAt (deriv (TauCeti.sqrtNearOne ℝ)) 1 := by
        have h1 : ContDiffAt ℝ ∞ (TauCeti.sqrtNearOne ℝ) 1 :=
          TauCeti.contDiffAt_sqrtNearOne (A := ℝ)
        have hf1 : ContinuousAt (fderiv ℝ (TauCeti.sqrtNearOne ℝ)) 1 :=
          (h1.fderiv_right (m := 0) (by simp)).continuousAt
        have heq_d : deriv (TauCeti.sqrtNearOne ℝ) =
            fun x ↦ fderiv ℝ (TauCeti.sqrtNearOne ℝ) x 1 := by
          funext x
          rw [fderiv_eq_smul_deriv]
          simp [smul_eq_mul]
        rw [heq_d]
        exact ((ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).continuous.continuousAt).comp hf1
      have harg : Tendsto (fun y : ℝ ↦ 1 + y ^ 2 / s4) (𝓝[≠] 0) (𝓝 1) := by
        have hc : ContinuousAt (fun y : ℝ ↦ 1 + y ^ 2 / s4) 0 := by fun_prop
        simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
      exact ((tendsto_const_nhds.mul (hcd.tendsto.comp harg)))
    have ht_rhs : Tendsto
        (fun y : ℝ ↦
          ((fderiv ℝ (c 2) 0) v₀ * y + (fderiv ℝ (c 1) 0) v₀) * u (0, y) +
            y ^ 2 * (fderiv ℝ u (0, y)) (v₀, 0))
        (𝓝[≠] 0)
        (𝓝 (((fderiv ℝ (c 2) 0) v₀ * 0 + (fderiv ℝ (c 1) 0) v₀) * u (0, 0) +
          0 ^ 2 * (fderiv ℝ u (0, 0)) (v₀, 0))) := by
      have hcu : ContinuousAt (fun y : ℝ ↦ u (0, y)) 0 :=
        hu_an.continuousAt.comp (continuousAt_const.prodMk continuousAt_id)
      have hc_lin : ContinuousAt (fun y : ℝ ↦ (fderiv ℝ (c 2) 0) v₀ * y + (fderiv ℝ (c 1) 0) v₀)
          0 := by fun_prop
      have hc_sq : ContinuousAt (fun y : ℝ ↦ y ^ 2) 0 := by fun_prop
      exact ((hc_lin.mul hcu).add (hc_sq.mul hu_cont_t)).tendsto.mono_left nhdsWithin_le_nhds
    have hlim := tendsto_nhds_unique ht_lhs (ht_rhs.congr' hderiv_eq.symm)
    rw [deriv_sqrtNearOne_one, hu_val] at hlim
    have hlim' : 2 * (m2 / s4) * (1 / 2) = (fderiv ℝ (c 1) 0) v₀ * (1 / (2 * s)) := by
      simpa using hlim
    dsimp only [m2, s4] at hlim'
    have hfin : 1 / (2 * s) = (fderiv ℝ (c 1) 0) v₀ * (1 / (2 * s)) := by
      calc
        1 / (2 * s) = 2 * (2 * s / (4 * s ^ 2)) * (1 / 2) := by field_simp [hs.ne']; ring
        _ = (fderiv ℝ (c 1) 0) v₀ * (1 / (2 * s)) := hlim'
    have h2s_ne : (1 / (2 * s) : ℝ) ≠ 0 := by positivity
    exact (mul_left_cancel₀ h2s_ne (by linarith)).symm
  let toF2CLM : EuclideanPlane →L[ℝ] (Fin 2 → ℝ) :=
    (EuclideanSpace.equiv (Fin 2) ℝ).toContinuousLinearMap
  have htoF2_apply (w : EuclideanPlane) (i : Fin 2) : toF2CLM w i = w i := rfl
  have htoF2_decomp (w : EuclideanPlane) : toF2CLM w = w 0 • v₀ + w 1 • ![0, 1] := by
    ext i
    fin_cases i <;> simp [toF2CLM, v₀]
  let shiftF2 : Fin 2 → ℝ := ![3 * s ^ 2, 0]
  let wShift : EuclideanPlane → (Fin 2 → ℝ) := fun w ↦ toF2CLM w - shiftF2
  have hwShift_pstar : wShift (lekiliMove1 s p_star) = 0 := by
    ext i
    fin_cases i
    · dsimp only [wShift, shiftF2, toF2CLM, lekiliMove1, realLefschetzMap, p_star]
      simp [vec2_zero, vec4_zero, vec4_one, vec4_two, vec4_three]; ring
    · dsimp only [wShift, shiftF2, toF2CLM, lekiliMove1, realLefschetzMap, p_star]
      simp [vec2_one, vec4_zero, vec4_one, vec4_two, vec4_three]
  have hwShift_diff : ContDiff ℝ ∞ wShift := toF2CLM.contDiff.sub contDiff_const
  have hwShift_fderiv (w : EuclideanPlane) : HasFDerivAt wShift toF2CLM w :=
    toF2CLM.hasFDerivAt.sub_const shiftF2
  have hev_c : ∀ᶠ w : Fin 2 → ℝ in 𝓝 0,
      AnalyticAt ℝ (c 0) w ∧ AnalyticAt ℝ (c 1) w ∧ AnalyticAt ℝ (c 2) w :=
    (hc_an 0).eventually_analyticAt.and
      ((hc_an 1).eventually_analyticAt.and (hc_an 2).eventually_analyticAt)
  obtain ⟨U_c, hU_c_sub, hU_c_open, h0_Uc⟩ := _root_.eventually_nhds_iff.mp hev_c
  have hc_contDiff (i : Fin 3) : ContDiffOn ℝ ∞ (c i) U_c := fun w hw ↦ by
    have ha : AnalyticAt ℝ (c i) w := by
      fin_cases i
      · exact (hU_c_sub w hw).1
      · exact (hU_c_sub w hw).2.1
      · exact (hU_c_sub w hw).2.2
    exact ha.contDiffAt.contDiffWithinAt
  have hev_u : ∀ᶠ q : (Fin 2 → ℝ) × ℝ in 𝓝 (0, 0), AnalyticAt ℝ u q :=
    hu_an.eventually_analyticAt
  obtain ⟨U_u, hU_u_sub, hU_u_open, h0_Uu⟩ := _root_.eventually_nhds_iff.mp hev_u
  have hu_contDiff : ContDiffOn ℝ ∞ u U_u := fun q hq ↦ (hU_u_sub q hq).contDiffAt.contDiffWithinAt
  let xFn : EuclideanSpace ℝ (Fin 4) → ℝ := fun p ↦ p 0 - s
  let w₀Fn : EuclideanSpace ℝ (Fin 4) → ℝ := fun p ↦ (lekiliMove1 s p) 0 - 3 * s ^ 2
  let RFn : EuclideanSpace ℝ (Fin 4) → ℝ := fun p ↦ 4 * s ^ 2 + w₀Fn p + p 1 ^ 2
  let DFn : EuclideanSpace ℝ (Fin 4) → ℝ := fun p ↦ (xFn p + 2 * s) + Real.sqrt (RFn p)
  let aFn : EuclideanSpace ℝ (Fin 4) → ℝ := fun p ↦ 2 * p 1 / DFn p
  let puvFn : EuclideanSpace ℝ (Fin 4) → ℝ := fun p ↦ (p 2 + p 3) / 2
  let quvFn : EuclideanSpace ℝ (Fin 4) → ℝ := fun p ↦ (p 2 - p 3) / 2
  let UFn : EuclideanSpace ℝ (Fin 4) → ℝ := fun p ↦ Real.sqrt 2 * (puvFn p - aFn p * quvFn p)
  let VFn : EuclideanSpace ℝ (Fin 4) → ℝ := fun p ↦ Real.sqrt (2 * (1 + aFn p ^ 2)) * quvFn p
  let TFn : EuclideanPlane → ℝ := fun w ↦ c 2 (wShift w) ^ 2 / 9 - c 1 (wShift w) / 3
  let WFn : EuclideanPlane → ℝ := fun w ↦
    -(c 0 (wShift w) - c 1 (wShift w) * c 2 (wShift w) / 3 + 2 * c 2 (wShift w) ^ 3 / 27)
  let QFn : EuclideanSpace ℝ (Fin 4) → ℝ := fun p ↦ p 1 + c 2 (wShift (lekiliMove1 s p)) / 3
  let invSqrtU : EuclideanSpace ℝ (Fin 4) → ℝ :=
    fun p ↦ (Real.sqrt (u (wShift (lekiliMove1 s p), p 1)))⁻¹
  let Φ : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4) := fun p ↦
    vec4 (TFn (lekiliMove1 s p)) (QFn p) (UFn p * invSqrtU p) (VFn p * invSqrtU p)
  let Ψ : EuclideanPlane → EuclideanPlane := fun w ↦ vec2 (TFn w) (WFn w)
  let U_tgt : Set EuclideanPlane := wShift ⁻¹' U_c
  have hU_tgt_open : IsOpen U_tgt := hU_c_open.preimage hwShift_diff.continuous
  have hfp_tgt : lekiliMove1 s p_star ∈ U_tgt := by simpa [U_tgt, hwShift_pstar] using h0_Uc
  let U_dom : Set (EuclideanSpace ℝ (Fin 4)) :=
    {p | lekiliMove1 s p ∈ U_tgt ∧ (wShift (lekiliMove1 s p), p 1) ∈ U_u ∧
      0 < u (wShift (lekiliMove1 s p), p 1) ∧ 0 < RFn p ∧ 0 < xFn p + 2 * s}
  have hU_dom_open : IsOpen U_dom := by
    have hL_cont : Continuous (lekiliMove1 s) := (contDiff_lekiliMove1 s).continuous
    have hw_cont : Continuous (fun p ↦ (wShift (lekiliMove1 s p), p 1)) :=
      (hwShift_diff.continuous.comp hL_cont).prodMk (euclidProj 1).continuous
    have hu_cont : ContinuousOn (fun p ↦ u (wShift (lekiliMove1 s p), p 1))
        ((fun p ↦ (wShift (lekiliMove1 s p), p 1)) ⁻¹' U_u) :=
      hu_contDiff.continuousOn.comp hw_cont.continuousOn (fun _ hx ↦ hx)
    have h1 : IsOpen (lekiliMove1 s ⁻¹' U_tgt) := hU_tgt_open.preimage hL_cont
    have h2 : IsOpen ((fun p ↦ (wShift (lekiliMove1 s p), p 1)) ⁻¹' U_u) :=
      hU_u_open.preimage hw_cont
    have h3 : IsOpen {p ∈ (fun p ↦ (wShift (lekiliMove1 s p), p 1)) ⁻¹' U_u |
        0 < u (wShift (lekiliMove1 s p), p 1)} :=
      hu_cont.isOpen_inter_preimage h2 isOpen_Ioi
    have hR_cont : Continuous RFn := by
      dsimp only [RFn, w₀Fn]
      have h0 : Continuous (fun p ↦ (lekiliMove1 s p) 0 - 3 * s ^ 2) :=
        ((euclidProj 0).continuous.comp hL_cont).sub continuous_const
      exact (continuous_const.add h0).add ((euclidProj 1).continuous.pow 2)
    have h4 : IsOpen {p | 0 < RFn p} := isOpen_lt continuous_const hR_cont
    have h5 : IsOpen {p | 0 < xFn p + 2 * s} :=
      isOpen_lt continuous_const
        (((euclidProj 0).continuous.sub continuous_const).add continuous_const)
    have hU_eq : U_dom = lekiliMove1 s ⁻¹' U_tgt ∩
        {p ∈ (fun p ↦ (wShift (lekiliMove1 s p), p 1)) ⁻¹' U_u |
          0 < u (wShift (lekiliMove1 s p), p 1)} ∩
        ({p | 0 < RFn p} ∩ {p | 0 < xFn p + 2 * s}) := by
      ext p
      simp [U_dom, and_assoc]
    rw [hU_eq]
    exact (h1.inter h3).inter (h4.inter h5)
  have hp_dom : p_star ∈ U_dom := by
    refine ⟨hfp_tgt, ?_, ?_, ?_, ?_⟩
    · simpa [hwShift_pstar, p_star] using h0_Uu
    · simpa [hwShift_pstar, p_star] using hu_pos
    · have hR_val : RFn p_star = 4 * s ^ 2 := by
        simp [RFn, w₀Fn, p_star, lekiliMove1]; ring
      rw [hR_val]; positivity
    · simp [xFn, p_star]; positivity
  have hc_comp_diff (i : Fin 3) : ContDiffOn ℝ ∞ (fun w ↦ c i (wShift w)) U_tgt :=
    (hc_contDiff i).comp hwShift_diff.contDiffOn (fun _ hw ↦ hw)
  have hΨ_diff : ContDiffOn ℝ ∞ Ψ U_tgt := by
    have hT_diff : ContDiffOn ℝ ∞ TFn U_tgt :=
      (((hc_comp_diff 2).pow 2).div_const 9).sub ((hc_comp_diff 1).div_const 3)
    have hW_diff : ContDiffOn ℝ ∞ WFn U_tgt :=
      ((((hc_comp_diff 0).sub (((hc_comp_diff 1).mul (hc_comp_diff 2)).div_const 3)).add
        ((contDiff_const.contDiffOn.mul ((hc_comp_diff 2).pow 3)).div_const 27))).neg
    have hpi : ContDiffOn ℝ ∞ (fun w ↦ ![TFn w, WFn w]) U_tgt := by
      refine contDiffOn_pi.mpr fun i ↦ ?_
      fin_cases i
      · exact hT_diff
      · exact hW_diff
    exact ((EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff).contDiffOn.comp hpi
      (fun _ _ ↦ Set.mem_univ _)
  have hΦ_diff : ContDiffOn ℝ ∞ Φ U_dom := by
    have hL_diff : ContDiffOn ℝ ∞ (lekiliMove1 s) U_dom :=
      (contDiff_lekiliMove1 s).contDiffOn
    have hp_fn (i : Fin 4) : ContDiffOn ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 4) ↦ p i) U_dom :=
      (euclidProj i).contDiff.contDiffOn
    have hT_comp : ContDiffOn ℝ ∞ (fun p ↦ TFn (lekiliMove1 s p)) U_dom :=
      (((hc_comp_diff 2).pow 2).div_const 9 |>.sub ((hc_comp_diff 1).div_const 3)).comp
        hL_diff (fun _ hp ↦ hp.1)
    have hc2_comp : ContDiffOn ℝ ∞ (fun p ↦ c 2 (wShift (lekiliMove1 s p))) U_dom :=
      (hc_comp_diff 2).comp hL_diff (fun _ hp ↦ hp.1)
    have hQ_diff : ContDiffOn ℝ ∞ QFn U_dom := (hp_fn 1).add (hc2_comp.div_const 3)
    have hw₀_diff : ContDiffOn ℝ ∞ w₀Fn U_dom :=
      (((euclidProj 0).contDiff.contDiffOn.comp hL_diff (fun _ _ ↦ Set.mem_univ _)).sub
        contDiff_const.contDiffOn)
    have hR_diff : ContDiffOn ℝ ∞ RFn U_dom :=
      (contDiff_const.contDiffOn.add hw₀_diff).add ((hp_fn 1).pow 2)
    have hD_diff : ContDiffOn ℝ ∞ DFn U_dom :=
      (((hp_fn 0).sub contDiff_const.contDiffOn).add contDiff_const.contDiffOn).add
        (hR_diff.sqrt fun _ hp ↦ hp.2.2.2.1.ne')
    have hD_ne : ∀ p ∈ U_dom, DFn p ≠ 0 := fun p hp ↦ by
      have hr : 0 ≤ Real.sqrt (RFn p) := Real.sqrt_nonneg _
      have hx : 0 < xFn p + 2 * s := hp.2.2.2.2
      dsimp only [DFn]; linarith
    have ha_diff : ContDiffOn ℝ ∞ aFn U_dom :=
      (contDiff_const.contDiffOn.mul (hp_fn 1)).div hD_diff hD_ne
    have hpuv_diff : ContDiffOn ℝ ∞ puvFn U_dom := ((hp_fn 2).add (hp_fn 3)).div_const 2
    have hquv_diff : ContDiffOn ℝ ∞ quvFn U_dom := ((hp_fn 2).sub (hp_fn 3)).div_const 2
    have hU_diff : ContDiffOn ℝ ∞ UFn U_dom :=
      contDiff_const.contDiffOn.mul (hpuv_diff.sub (ha_diff.mul hquv_diff))
    have hV_diff : ContDiffOn ℝ ∞ VFn U_dom := by
      have harg : ContDiffOn ℝ ∞ (fun p ↦ 2 * (1 + aFn p ^ 2)) U_dom :=
        contDiff_const.contDiffOn.mul (contDiff_const.contDiffOn.add (ha_diff.pow 2))
      have harg_ne : ∀ p ∈ U_dom, 2 * (1 + aFn p ^ 2) ≠ 0 := fun p _ ↦ by positivity
      exact (harg.sqrt harg_ne).mul hquv_diff
    have hu_comp : ContDiffOn ℝ ∞ (fun p ↦ u (wShift (lekiliMove1 s p), p 1)) U_dom :=
      hu_contDiff.comp
        ((hwShift_diff.contDiffOn.comp hL_diff (fun _ _ ↦ Set.mem_univ _)).prodMk (hp_fn 1))
        (fun _ hp ↦ hp.2.1)
    have hsqrtU_diff : ContDiffOn ℝ ∞
        (fun p ↦ Real.sqrt (u (wShift (lekiliMove1 s p), p 1))) U_dom :=
      hu_comp.sqrt fun _ hp ↦ hp.2.2.1.ne'
    have hinv_diff : ContDiffOn ℝ ∞ invSqrtU U_dom :=
      hsqrtU_diff.inv fun _ hp ↦ (Real.sqrt_pos.mpr hp.2.2.1).ne'
    have hpi : ContDiffOn ℝ ∞
        (fun p ↦ ![TFn (lekiliMove1 s p), QFn p, UFn p * invSqrtU p, VFn p * invSqrtU p])
        U_dom := by
      refine contDiffOn_pi.mpr fun i ↦ ?_
      fin_cases i
      · exact hT_comp
      · exact hQ_diff
      · exact hU_diff.mul hinv_diff
      · exact hV_diff.mul hinv_diff
    exact ((EuclideanSpace.equiv (Fin 4) ℝ).symm.contDiff).contDiffOn.comp hpi
      (fun _ _ ↦ Set.mem_univ _)
  let k₁₁ : ℝ := (fderiv ℝ (c 1) 0) ![0, 1]
  let c₂₀ : ℝ := (fderiv ℝ (c 2) 0) v₀
  let rtu : ℝ := Real.sqrt (u (0, 0))
  have hrtu_pos : 0 < rtu := Real.sqrt_pos.mpr hu_pos
  have hrtu_ne : rtu ≠ 0 := hrtu_pos.ne'
  let K₂ : ℝ := Real.sqrt 2 / (2 * rtu)
  have hK₂_ne : K₂ ≠ 0 := div_ne_zero (Real.sqrt_pos.mpr (by norm_num)).ne' (by positivity)
  have hs_ne : s ≠ 0 := hs.ne'
  let eΨ : EuclideanPlane ≃L[ℝ] EuclideanPlane :=
    { toFun v := vec2 (-(1 / 3 : ℝ) * (v 0 + k₁₁ * v 1)) ((2 * s) * v 1)
      invFun z := vec2 (-3 * z 0 - k₁₁ / (2 * s) * z 1) (z 1 / (2 * s))
      map_add' u v := by refine ext_vec2 ?_ ?_ <;> (simp; ring)
      map_smul' r v := by refine ext_vec2 ?_ ?_ <;> (simp; ring)
      left_inv v := by
        refine ext_vec2 ?_ ?_
        · simp only [vec2_zero, vec2_one]; field_simp [hs_ne]; ring
        · simp only [vec2_one]; field_simp [hs_ne]
      right_inv z := by
        refine ext_vec2 ?_ ?_
        · simp only [vec2_zero, vec2_one]; field_simp [hs_ne]; ring
        · simp only [vec2_one]; field_simp [hs_ne]
      continuous_toFun := continuous_vec2
        (continuous_const.mul ((euclidProj 0).continuous.add
          (continuous_const.mul (euclidProj 1).continuous)))
        (continuous_const.mul (euclidProj 1).continuous)
      continuous_invFun := continuous_vec2
        ((continuous_const.mul (euclidProj 0).continuous).sub
          (continuous_const.mul (euclidProj 1).continuous))
        ((euclidProj 1).continuous.div_const (2 * s)) }
  let eΦ : EuclideanSpace ℝ (Fin 4) ≃L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    { toFun v := vec4 (-(4 * s / 3) * v 0) (v 1 + (4 * s * c₂₀ / 3) * v 0)
        (K₂ * (v 2 + v 3)) (K₂ * (v 2 - v 3))
      invFun a :=
        let x₀ := -3 * a 0 / (4 * s)
        vec4 x₀ (a 1 - (4 * s * c₂₀ / 3) * x₀)
          ((a 2 + a 3) / (2 * K₂)) ((a 2 - a 3) / (2 * K₂))
      map_add' u v := by
        refine ext_vec4 ?_ ?_ ?_ ?_ <;> (simp; ring)
      map_smul' r v := by
        refine ext_vec4 ?_ ?_ ?_ ?_ <;> (simp; ring)
      left_inv v := by
        refine ext_vec4 ?_ ?_ ?_ ?_
        · simp only [vec4_zero]; field_simp [hs_ne]
        · simp only [vec4_zero, vec4_one]; field_simp [hs_ne]; ring
        · simp only [vec4_two, vec4_three]; field_simp [hK₂_ne]; ring
        · simp only [vec4_two, vec4_three]; field_simp [hK₂_ne]; ring
      right_inv a := by
        refine ext_vec4 ?_ ?_ ?_ ?_
        · simp only [vec4_zero]; field_simp [hs_ne]
        · simp only [vec4_zero, vec4_one]; field_simp [hs_ne]; ring
        · simp only [vec4_two, vec4_three]; field_simp [hK₂_ne]; ring
        · simp only [vec4_two, vec4_three]; field_simp [hK₂_ne]; ring
      continuous_toFun := continuous_vec4
        (continuous_const.mul (euclidProj 0).continuous)
        ((euclidProj 1).continuous.add (continuous_const.mul (euclidProj 0).continuous))
        (continuous_const.mul ((euclidProj 2).continuous.add (euclidProj 3).continuous))
        (continuous_const.mul ((euclidProj 2).continuous.sub (euclidProj 3).continuous))
      continuous_invFun := continuous_vec4
        ((continuous_const.mul (euclidProj 0).continuous).div_const (4 * s))
        ((euclidProj 1).continuous.sub (continuous_const.mul
          ((continuous_const.mul (euclidProj 0).continuous).div_const (4 * s))))
        (((euclidProj 2).continuous.add (euclidProj 3).continuous).div_const (2 * K₂))
        (((euclidProj 2).continuous.sub (euclidProj 3).continuous).div_const (2 * K₂)) }
  have heΦ_apply (v : EuclideanSpace ℝ (Fin 4)) :
      eΦ v = vec4 (-(4 * s / 3) * v 0) (v 1 + (4 * s * c₂₀ / 3) * v 0)
        (K₂ * (v 2 + v 3)) (K₂ * (v 2 - v 3)) := rfl
  have hc_w_hasFDeriv (i : Fin 3) (w : EuclideanPlane) (hw : w ∈ U_tgt) :
      HasFDerivAt (fun z ↦ c i (wShift z))
        ((fderiv ℝ (c i) (wShift w)).comp toF2CLM) w := by
    have hci : AnalyticAt ℝ (c i) (wShift w) := by
      have hw' : wShift w ∈ U_c := hw
      fin_cases i
      · exact (hU_c_sub _ hw').1
      · exact (hU_c_sub _ hw').2.1
      · exact (hU_c_sub _ hw').2.2
    exact (hci.differentiableAt.hasFDerivAt).comp w (hwShift_fderiv w)
  have hT_hasFDeriv_wstar : HasFDerivAt TFn
      ((-1 / 3 : ℝ) • ((fderiv ℝ (c 1) 0).comp toF2CLM)) (lekiliMove1 s p_star) := by
    have h2 := hc_w_hasFDeriv 2 (lekiliMove1 s p_star) hfp_tgt
    have h1 := hc_w_hasFDeriv 1 (lekiliMove1 s p_star) hfp_tgt
    rw [hwShift_pstar] at h2 h1
    have h2_sq : HasFDerivAt (fun w : EuclideanPlane ↦ c 2 (wShift w) ^ 2 / 9)
        (0 : EuclideanPlane →L[ℝ] ℝ) (lekiliMove1 s p_star) := by
      have heq : (fun w ↦ c 2 (wShift w) ^ 2 / 9) = fun w ↦ c 2 (wShift w) ^ 2 * (1 / 9 : ℝ) := by
        funext w; ring
      rw [heq]
      refine ((h2.pow 2).mul_const (1 / 9 : ℝ)).congr_fderiv ?_
      ext v
      simp [hwShift_pstar, hc0 2]
    have h1_div : HasFDerivAt (fun w ↦ c 1 (wShift w) / 3)
        ((1 / 3 : ℝ) • ((fderiv ℝ (c 1) 0).comp toF2CLM)) (lekiliMove1 s p_star) := by
      have heq : (fun w ↦ c 1 (wShift w) / 3) = fun w ↦ c 1 (wShift w) * (1 / 3 : ℝ) := by
        funext w; ring
      rw [heq]
      refine (h1.mul_const (1 / 3 : ℝ)).congr_fderiv ?_
      ext v; simp [smul_apply, smul_eq_mul]
    have hm := h2_sq.sub h1_div
    refine hm.congr_fderiv ?_
    ext v
    simp [smul_apply]
    ring
  have hW_hasFDeriv_wstar : HasFDerivAt WFn
      (-((fderiv ℝ (c 0) 0).comp toF2CLM)) (lekiliMove1 s p_star) := by
    have h0 := hc_w_hasFDeriv 0 (lekiliMove1 s p_star) hfp_tgt
    have h1 := hc_w_hasFDeriv 1 (lekiliMove1 s p_star) hfp_tgt
    have h2 := hc_w_hasFDeriv 2 (lekiliMove1 s p_star) hfp_tgt
    rw [hwShift_pstar] at h0 h1 h2
    have h12 : HasFDerivAt (fun w : EuclideanPlane ↦ c 1 (wShift w) * c 2 (wShift w) / 3)
        (0 : EuclideanPlane →L[ℝ] ℝ) (lekiliMove1 s p_star) := by
      have heq : (fun w : EuclideanPlane ↦ c 1 (wShift w) * c 2 (wShift w) / 3) =
          fun w ↦ (c 1 (wShift w) * c 2 (wShift w)) * (1 / 3 : ℝ) := by funext w; ring
      rw [heq]
      refine ((h1.mul h2).mul_const (1 / 3 : ℝ)).congr_fderiv ?_
      ext v
      simp [hwShift_pstar, hc0 1, hc0 2]
    have h2c : HasFDerivAt (fun w : EuclideanPlane ↦ 2 * c 2 (wShift w) ^ 3 / 27)
        (0 : EuclideanPlane →L[ℝ] ℝ) (lekiliMove1 s p_star) := by
      have heq : (fun w : EuclideanPlane ↦ 2 * c 2 (wShift w) ^ 3 / 27) =
          fun w ↦ (2 * c 2 (wShift w) ^ 3) * (1 / 27 : ℝ) := by funext w; ring
      rw [heq]
      refine (((h2.pow 3).const_mul 2).mul_const (1 / 27 : ℝ)).congr_fderiv ?_
      ext v
      simp [hwShift_pstar, hc0 2]
    exact (((h0.sub h12).add h2c).neg).congr_fderiv (by ext v; simp)
  have heΨ : (eΨ : EuclideanPlane →L[ℝ] EuclideanPlane) =
      fderiv ℝ Ψ (lekiliMove1 s p_star) := by
    rw [(hasFDerivAt_vec2 hT_hasFDeriv_wstar hW_hasFDeriv_wstar).fderiv]
    ext v i
    have h_toF2 := htoF2_decomp v
    fin_cases i
    · simp only [eΨ, clmVec2_apply, smul_apply, ContinuousLinearMap.comp_apply,
        smul_eq_mul]
      rw [h_toF2, map_add, map_smul, map_smul, hc1_v0]
      simp [k₁₁]
      ring
    · simp only [eΨ, clmVec2_apply, neg_apply, ContinuousLinearMap.comp_apply]
      rw [hc0_fderiv]
      simp [htoF2_apply]
  have heΦ : (eΦ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) =
      fderiv ℝ Φ p_star := by
    have hp (i : Fin 4) : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 4) ↦ q i)
        (euclidProj i) p_star := (euclidProj i).hasFDerivAt
    have hL_fderiv : HasFDerivAt (lekiliMove1 s) (lekiliMove1FDerivCLM s p_star) p_star :=
      hasFDerivAt_lekiliMove1 s p_star
    have hL_p_eval (v : EuclideanSpace ℝ (Fin 4)) :
        lekiliMove1FDerivCLM s p_star v = vec2 (4 * s * v 0) 0 := by
      dsimp only [p_star]
      refine ext_vec2 ?_ ?_ <;>
        (simp only [lekiliMove1FDerivCLM_apply, vec4_zero, vec4_one, vec4_two, vec4_three,
           vec2_zero, vec2_one]; ring)
    have hT_p_der : HasFDerivAt (fun q ↦ TFn (lekiliMove1 s q))
        (-(4 * s / 3) • euclidProj (0 : Fin 4)) p_star := by
      refine (hT_hasFDeriv_wstar.comp p_star hL_fderiv).congr_fderiv ?_
      ext v
      simp only [smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
      rw [hL_p_eval, htoF2_decomp (vec2 (4 * s * v 0) 0), vec2_zero, vec2_one, zero_smul,
        add_zero, map_smul, smul_eq_mul, hc1_v0, euclidProj, EuclideanSpace.proj, PiLp.proj_apply]
      ring
    have hc2_p_der : HasFDerivAt (fun q ↦ c 2 (wShift (lekiliMove1 s q)))
        ((4 * s * c₂₀) • euclidProj (0 : Fin 4)) p_star := by
      have h2 := hc_w_hasFDeriv 2 (lekiliMove1 s p_star) hfp_tgt
      rw [hwShift_pstar] at h2
      refine (h2.comp p_star hL_fderiv).congr_fderiv ?_
      ext v
      simp only [smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
      rw [hL_p_eval, htoF2_decomp (vec2 (4 * s * v 0) 0), vec2_zero, vec2_one, zero_smul,
        add_zero, map_smul, smul_eq_mul, euclidProj, EuclideanSpace.proj, PiLp.proj_apply]
      dsimp only [c₂₀]
      ring
    have hQ_p_der : HasFDerivAt QFn
        (euclidProj (1 : Fin 4) + (4 * s * c₂₀ / 3) • euclidProj (0 : Fin 4)) p_star := by
      have heq_Q : QFn = fun q ↦ q 1 + c 2 (wShift (lekiliMove1 s q)) * (1 / 3 : ℝ) := by
        funext q; dsimp only [QFn]; ring
      rw [heq_Q]
      refine ((hp 1).add (hc2_p_der.mul_const (1 / 3 : ℝ))).congr_fderiv ?_
      ext v
      simp [add_apply, smul_apply, smul_eq_mul]
      ring
    have hD_diffAt : DifferentiableAt ℝ DFn p_star := by
      have hRc : ContDiffAt ℝ ∞ RFn p_star := by
        have hw₀c : ContDiffAt ℝ ∞ w₀Fn p_star :=
          (((euclidProj 0).contDiff.contDiffAt.comp p_star
            (contDiff_lekiliMove1 s).contDiffAt).sub contDiffAt_const)
        exact (contDiffAt_const.add hw₀c).add (((euclidProj 1).contDiff.contDiffAt).pow 2)
      have hR_ne : RFn p_star ≠ 0 := by
        have hR_val : RFn p_star = 4 * s ^ 2 := by
          simp [RFn, w₀Fn, p_star, lekiliMove1, realLefschetzMap]; ring
        rw [hR_val]; positivity
      have hD_at : ContDiffAt ℝ ∞ DFn p_star :=
        ((((euclidProj 0).contDiff.contDiffAt).sub contDiffAt_const).add contDiffAt_const).add
          (hRc.sqrt hR_ne)
      exact hD_at.differentiableAt (by simp)
    have ha_diffAt : DifferentiableAt ℝ aFn p_star := by
      have hD_ne : DFn p_star ≠ 0 := by
        have hR_val : RFn p_star = 4 * s ^ 2 := by
          simp [RFn, w₀Fn, p_star, lekiliMove1, realLefschetzMap]; ring
        simp only [DFn, xFn, p_star, vec4_zero, hR_val]
        have : 0 ≤ Real.sqrt (4 * s ^ 2) := Real.sqrt_nonneg _
        linarith
      have hnum : DifferentiableAt ℝ (fun q : EuclideanSpace ℝ (Fin 4) ↦ 2 * q 1) p_star :=
        (differentiableAt_const (2 : ℝ)).mul (euclidProj (1 : Fin 4)).differentiableAt
      have heq_a : aFn = fun q ↦ (2 * q 1) * (DFn q)⁻¹ := funext fun q ↦ div_eq_mul_inv _ _
      rw [heq_a]
      exact hnum.mul (hD_diffAt.fun_inv hD_ne)
    have hpuv_der : HasFDerivAt puvFn
        ((1 / 2 : ℝ) • (euclidProj (2 : Fin 4) + euclidProj (3 : Fin 4))) p_star := by
      have heq_puv : puvFn = fun q ↦ (q 2 + q 3) * (1 / 2 : ℝ) := by
        funext q; dsimp only [puvFn]; ring
      rw [heq_puv]
      refine (((hp 2).add (hp 3)).mul_const (1 / 2 : ℝ)).congr_fderiv ?_
      ext v; simp [add_apply, smul_apply, smul_eq_mul]
    have hquv_der : HasFDerivAt quvFn
        ((1 / 2 : ℝ) • (euclidProj (2 : Fin 4) - euclidProj (3 : Fin 4))) p_star := by
      have heq_quv : quvFn = fun q ↦ (q 2 - q 3) * (1 / 2 : ℝ) := by
        funext q; dsimp only [quvFn]; ring
      rw [heq_quv]
      refine (((hp 2).sub (hp 3)).mul_const (1 / 2 : ℝ)).congr_fderiv ?_
      ext v; simp [sub_apply, smul_apply, smul_eq_mul]
    have haquv_der : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 4) ↦ aFn q * quvFn q)
        (0 : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ) p_star := by
      have ha_zero : aFn p_star = 0 := by simp [aFn, p_star]
      have hq_zero : quvFn p_star = 0 := by simp [quvFn, p_star]
      refine (ha_diffAt.hasFDerivAt.mul hquv_der).congr_fderiv ?_
      ext v; simp [ha_zero, hq_zero]
    have hU_der : HasFDerivAt UFn
        ((Real.sqrt 2 / 2) • (euclidProj (2 : Fin 4) + euclidProj (3 : Fin 4))) p_star := by
      refine ((hpuv_der.sub haquv_der).const_mul (Real.sqrt 2)).congr_fderiv ?_
      ext v; simp [add_apply, smul_apply, smul_eq_mul]; ring
    have hV_der : HasFDerivAt VFn
        ((Real.sqrt 2 / 2) • (euclidProj (2 : Fin 4) - euclidProj (3 : Fin 4))) p_star := by
      have harg_at : ContDiffAt ℝ ∞ (fun q ↦ 2 * (1 + aFn q ^ 2)) p_star := by
        have ha_cd : ContDiffOn ℝ ∞ aFn U_dom := by
          have hL_diff : ContDiffOn ℝ ∞ (lekiliMove1 s) U_dom := (contDiff_lekiliMove1 s).contDiffOn
          have hp_fn (i : Fin 4) : ContDiffOn ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 4) ↦ p i) U_dom :=
            (euclidProj i).contDiff.contDiffOn
          have hw₀_diff : ContDiffOn ℝ ∞ w₀Fn U_dom :=
            (((euclidProj 0).contDiff.contDiffOn.comp hL_diff (fun _ _ ↦ Set.mem_univ _)).sub
              contDiff_const.contDiffOn)
          have hR_diff : ContDiffOn ℝ ∞ RFn U_dom :=
            (contDiff_const.contDiffOn.add hw₀_diff).add ((hp_fn 1).pow 2)
          have hD_diff : ContDiffOn ℝ ∞ DFn U_dom :=
            (((hp_fn 0).sub contDiff_const.contDiffOn).add contDiff_const.contDiffOn).add
              (hR_diff.sqrt fun _ hp ↦ hp.2.2.2.1.ne')
          have hD_ne : ∀ p ∈ U_dom, DFn p ≠ 0 := fun p hp ↦ by
            have hr : 0 ≤ Real.sqrt (RFn p) := Real.sqrt_nonneg _
            have hx : 0 < xFn p + 2 * s := hp.2.2.2.2
            dsimp only [DFn]; linarith
          exact (contDiff_const.contDiffOn.mul (hp_fn 1)).div hD_diff hD_ne
        have h1 : ContDiffAt ℝ ∞ aFn p_star := ha_cd.contDiffAt (hU_dom_open.mem_nhds hp_dom)
        exact contDiffAt_const.mul (contDiffAt_const.add (h1.pow 2))
      have hsqrt_at : DifferentiableAt ℝ (fun q ↦ Real.sqrt (2 * (1 + aFn q ^ 2))) p_star :=
        (harg_at.sqrt (by simp [aFn, p_star])).differentiableAt (by simp)
      refine (hsqrt_at.hasFDerivAt.mul hquv_der).congr_fderiv ?_
      ext v
      have ha0 : aFn p_star = 0 := by simp [aFn, p_star]
      have hq0 : quvFn p_star = 0 := by simp [quvFn, p_star]
      simp only [add_apply, smul_apply, sub_apply, ha0, hq0]
      rw [show (0 : ℝ) ^ 2 = 0 by norm_num, show (2 : ℝ) * (1 + 0) = 2 by ring]
      simp only [smul_eq_mul]
      ring
    have hinv_diffAt : DifferentiableAt ℝ invSqrtU p_star := by
      have hL_diff : ContDiffOn ℝ ∞ (lekiliMove1 s) U_dom := (contDiff_lekiliMove1 s).contDiffOn
      have hp1_diff : ContDiffOn ℝ ∞ (fun q : EuclideanSpace ℝ (Fin 4) ↦ q 1) U_dom :=
        (euclidProj 1).contDiff.contDiffOn
      have hu_comp : ContDiffOn ℝ ∞ (fun q ↦ u (wShift (lekiliMove1 s q), q 1)) U_dom :=
        hu_contDiff.comp
          ((hwShift_diff.contDiffOn.comp hL_diff (fun _ _ ↦ Set.mem_univ _)).prodMk hp1_diff)
          (fun _ hq ↦ hq.2.1)
      have hinv_cd : ContDiffOn ℝ ∞ invSqrtU U_dom :=
        (hu_comp.sqrt fun _ hq ↦ hq.2.2.1.ne').inv fun _ hq ↦
          (Real.sqrt_pos.mpr hq.2.2.1).ne'
      exact (hinv_cd.contDiffAt (hU_dom_open.mem_nhds hp_dom)).differentiableAt (by simp)
    have hU0 : UFn p_star = 0 := by simp [UFn, puvFn, quvFn, p_star]
    have hV0 : VFn p_star = 0 := by simp [VFn, quvFn, p_star]
    have hinv_val : invSqrtU p_star = rtu⁻¹ := by simp [invSqrtU, rtu, hwShift_pstar, p_star]
    have hU_tilde_der : HasFDerivAt (fun q ↦ UFn q * invSqrtU q)
        (K₂ • (euclidProj (2 : Fin 4) + euclidProj (3 : Fin 4))) p_star := by
      refine (hU_der.mul hinv_diffAt.hasFDerivAt).congr_fderiv ?_
      ext v
      simp only [add_apply, smul_apply, hU0, zero_smul, zero_add, hinv_val, smul_eq_mul, K₂]
      ring
    have hV_tilde_der : HasFDerivAt (fun q ↦ VFn q * invSqrtU q)
        (K₂ • (euclidProj (2 : Fin 4) - euclidProj (3 : Fin 4))) p_star := by
      refine (hV_der.mul hinv_diffAt.hasFDerivAt).congr_fderiv ?_
      ext v
      simp only [smul_apply, sub_apply, hV0, zero_smul, zero_add, hinv_val, smul_eq_mul, K₂]
      ring
    rw [(hasFDerivAt_vec4' hT_p_der hQ_p_der hU_tilde_der hV_tilde_der).fderiv]
    refine ContinuousLinearMap.ext fun v ↦ ?_
    rw [ContinuousLinearEquiv.coe_coe, heΦ_apply]
    refine ext_vec4 ?_ ?_ ?_ ?_
    · simp only [vec4_zero, clmVec4_apply, smul_apply, euclidProj,
        EuclideanSpace.proj, PiLp.proj_apply, smul_eq_mul]
    · simp only [vec4_one, clmVec4_apply, add_apply, smul_apply, euclidProj,
        EuclideanSpace.proj, PiLp.proj_apply, smul_eq_mul]
    · simp only [vec4_two, clmVec4_apply, add_apply, smul_apply, euclidProj,
        EuclideanSpace.proj, PiLp.proj_apply, smul_eq_mul]
    · simp only [vec4_three, clmVec4_apply, sub_apply, smul_apply, euclidProj,
        EuclideanSpace.proj, PiLp.proj_apply, smul_eq_mul]
  have hΦ_p : Φ p_star = 0 := by
    refine ext_vec4 ?_ ?_ ?_ ?_
    · change TFn (lekiliMove1 s p_star) = 0
      simp only [TFn, hwShift_pstar, hc0 1, hc0 2]; ring
    · change QFn p_star = 0
      simp only [QFn, hwShift_pstar, hc0 2, p_star, vec4_one]; ring
    · change UFn p_star * invSqrtU p_star = 0
      simp only [UFn, puvFn, quvFn, p_star, vec4_two, vec4_three]; ring
    · change VFn p_star * invSqrtU p_star = 0
      simp only [VFn, quvFn, p_star, vec4_two, vec4_three]; ring
  have hΨ_fp : Ψ (lekiliMove1 s p_star) = wrinkledCuspMap 0 := by
    have hwc0 : wrinkledCuspMap (0 : EuclideanSpace ℝ (Fin 4)) = vec2 0 0 := by
      refine ext_vec2 ?_ ?_ <;>
        simp only [wrinkledCuspMap, vec2_zero, vec2_one, PiLp.zero_apply]
      ring
    rw [hwc0]
    refine ext_vec2 ?_ ?_
    · simp only [Ψ, TFn, hwShift_pstar, hc0 1, hc0 2, vec2_zero]; ring
    · simp only [Ψ, WFn, hwShift_pstar, hc0 0, hc0 1, hc0 2, vec2_one]; ring
  refine isLocallyModeledOn_of_contDiff_maps hU_dom_open hp_dom hU_tgt_open hfp_tgt
    hΦ_diff hΨ_diff eΦ heΦ eΨ heΨ hΦ_p hΨ_fp ?_
    (contDiff_lekiliMove1 s).continuous.continuousAt
  have hG_at : ∀ᶠ q in 𝓝 p_star,
      G (wShift (lekiliMove1 s q), q 1) =
        ((QFn q ^ 3 - 3 * TFn (lekiliMove1 s q) * QFn q - WFn (lekiliMove1 s q)) *
          u (wShift (lekiliMove1 s q), q 1)) := by
    have hcont : ContinuousAt (fun q : EuclideanSpace ℝ (Fin 4) ↦ (wShift (lekiliMove1 s q), q 1))
        p_star :=
      ((hwShift_diff.continuous.comp (contDiff_lekiliMove1 s).continuous).prodMk
        (euclidProj 1).continuous).continuousAt
    have hp0 : (wShift (lekiliMove1 s p_star), p_star 1) = (0, 0) :=
      Prod.ext hwShift_pstar (by simp [p_star])
    filter_upwards [hcont.tendsto.eventually (hp0 ▸ heq_wp)] with q hq
    rw [hq, TauCeti.Polynomial.eval_monicOfCoeff, Fin.sum_univ_three]
    dsimp only [QFn, TFn, WFn]
    simp only [sub_zero, Fin.val_zero, pow_zero, mul_one, Fin.val_one, pow_one, Fin.val_two]
    ring
  have hsqrt_ball : ∀ᶠ q in 𝓝 p_star,
      ‖(1 + ((wShift (lekiliMove1 s q)) 0 + q 1 ^ 2) / s4) - 1‖ < 1 ∧
        0 < TauCeti.sqrtNearOne ℝ (1 + ((wShift (lekiliMove1 s q)) 0 + q 1 ^ 2) / s4) := by
    have harg_cont : ContinuousAt
        (fun q : EuclideanSpace ℝ (Fin 4) ↦ 1 + ((wShift (lekiliMove1 s q)) 0 + q 1 ^ 2) / s4)
        p_star := by
      have hL := (contDiff_lekiliMove1 s).continuous
      have hdiv : Continuous
          (fun q : EuclideanSpace ℝ (Fin 4) ↦ ((wShift (lekiliMove1 s q)) 0 + q 1 ^ 2) / s4) :=
        (((continuous_apply 0).comp (hwShift_diff.continuous.comp hL)).add
          ((euclidProj 1).continuous.pow 2)).div continuous_const (fun _ ↦ hs4_ne)
      exact (continuous_const.add hdiv).continuousAt
    have h01 : 1 + ((wShift (lekiliMove1 s p_star)) 0 + p_star 1 ^ 2) / s4 = 1 := by
      dsimp only [wShift, toF2CLM, shiftF2, p_star, lekiliMove1, realLefschetzMap]
      simp [vec2_zero, vec4_zero, vec4_one, vec4_two, vec4_three]
      left
      ring
    have hsq_pos : 0 < TauCeti.sqrtNearOne ℝ 1 := by rw [TauCeti.sqrtNearOne_one]; norm_num
    have h1 : ∀ᶠ q in 𝓝 p_star,
        ‖(1 + ((wShift (lekiliMove1 s q)) 0 + q 1 ^ 2) / s4) - 1‖ < 1 := by
      have hball : Metric.ball (1 : ℝ) 1 ∈
          𝓝 (1 + ((wShift (lekiliMove1 s p_star)) 0 + p_star 1 ^ 2) / s4) := by
        simpa [h01] using Metric.ball_mem_nhds (1 : ℝ) zero_lt_one
      exact harg_cont hball
    have h2 : ∀ᶠ q in 𝓝 p_star,
        0 < TauCeti.sqrtNearOne ℝ (1 + ((wShift (lekiliMove1 s q)) 0 + q 1 ^ 2) / s4) := by
      have hsq_cont : ContinuousAt (TauCeti.sqrtNearOne ℝ)
          (1 + ((wShift (lekiliMove1 s p_star)) 0 + p_star 1 ^ 2) / s4) := by
        rw [h01]; exact TauCeti.continuousAt_sqrtNearOne (A := ℝ)
      have hIoi : Set.Ioi (0 : ℝ) ∈ 𝓝 (TauCeti.sqrtNearOne ℝ
          (1 + ((wShift (lekiliMove1 s p_star)) 0 + p_star 1 ^ 2) / s4)) := by
        rw [h01]; exact Ioi_mem_nhds hsq_pos
      exact (hsq_cont.tendsto.comp harg_cont.tendsto) hIoi
    exact h1.and h2
  filter_upwards [hU_dom_open.mem_nhds hp_dom, hG_at, hsqrt_ball] with q hq hG hball
  refine ⟨hq.1, ?_⟩
  have hsq_near : TauCeti.sqrtNearOne ℝ (1 + ((wShift (lekiliMove1 s q)) 0 + q 1 ^ 2) / s4) ^ 2 =
      1 + ((wShift (lekiliMove1 s q)) 0 + q 1 ^ 2) / s4 := by
    simpa [sq] using TauCeti.mul_self_sqrtNearOne hball.1
  have hshift0 : (wShift (lekiliMove1 s q)) 0 = w₀Fn q := by
    dsimp only [wShift, w₀Fn, toF2CLM, shiftF2]; simp
  have hshift1 : (wShift (lekiliMove1 s q)) 1 = (lekiliMove1 s q) 1 := by
    dsimp only [wShift, toF2CLM, shiftF2]; simp
  have hR_pos : 0 < RFn q := hq.2.2.2.1
  have hm2_sq : m2 * TauCeti.sqrtNearOne ℝ (1 + ((wShift (lekiliMove1 s q)) 0 + q 1 ^ 2) / s4) =
      Real.sqrt (RFn q) := by
    have hpos1 : 0 ≤ m2 * TauCeti.sqrtNearOne ℝ
        (1 + ((wShift (lekiliMove1 s q)) 0 + q 1 ^ 2) / s4) :=
      mul_nonneg hm2.le hball.2.le
    have hpos2 : 0 ≤ Real.sqrt (RFn q) := Real.sqrt_nonneg _
    refine (sq_eq_sq₀ hpos1 hpos2).mp ?_
    rw [mul_pow, hsq_near, Real.sq_sqrt hR_pos.le, hshift0]
    dsimp only [RFn, m2, s4]
    field_simp [hs4_ne]
    ring
  have hG_lhs : G (wShift (lekiliMove1 s q), q 1) =
      2 * q 1 * (Real.sqrt (RFn q) - m2) - (lekiliMove1 s q) 1 := by
    dsimp only [G]
    rw [hm2_sq, hshift1]
  have hu_q_pos : 0 < u (wShift (lekiliMove1 s q), q 1) := hq.2.2.1
  have hD_pos : 0 < DFn q := by
    have hx : 0 < xFn q + 2 * s := hq.2.2.2.2
    have hr : 0 ≤ Real.sqrt (RFn q) := Real.sqrt_nonneg _
    dsimp only [DFn]; linarith
  have hD_ne : DFn q ≠ 0 := hD_pos.ne'
  have hdec : (lekiliMove1 s q) 1 - 2 * q 1 * (Real.sqrt (RFn q) - m2) =
      UFn q ^ 2 - VFn q ^ 2 := by
    have hR_diff : (xFn q + 2 * s) ^ 2 - RFn q = -4 * puvFn q * quvFn q := by
      dsimp only [xFn, RFn, w₀Fn, puvFn, quvFn, lekiliMove1, realLefschetzMap]
      simp only [PiLp.add_apply, vec2_zero]
      ring
    have hlin : (xFn q + 2 * s - Real.sqrt (RFn q)) * DFn q = -4 * puvFn q * quvFn q := by
      calc
        (xFn q + 2 * s - Real.sqrt (RFn q)) * DFn q
          = (xFn q + 2 * s) ^ 2 - Real.sqrt (RFn q) ^ 2 := by dsimp only [DFn]; ring
        _ = (xFn q + 2 * s) ^ 2 - RFn q := by rw [Real.sq_sqrt hR_pos.le]
        _ = -4 * puvFn q * quvFn q := hR_diff
    have hUV :
        UFn q ^ 2 - VFn q ^ 2 =
          2 * (puvFn q ^ 2 - quvFn q ^ 2 - 2 * aFn q * puvFn q * quvFn q) := by
      dsimp only [UFn, VFn]
      have harg_nn : 0 ≤ 2 * (1 + aFn q ^ 2) := by positivity
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt harg_nn]
      ring
    have hw1 : (lekiliMove1 s q) 1 - 2 * q 1 * (Real.sqrt (RFn q) - m2) =
        2 * q 1 * (xFn q + 2 * s - Real.sqrt (RFn q)) + 2 * (puvFn q ^ 2 - quvFn q ^ 2) := by
      dsimp only [xFn, puvFn, quvFn, m2, lekiliMove1, realLefschetzMap]
      simp only [PiLp.add_apply, vec2_one]
      ring
    rw [hw1, hUV]
    dsimp only [aFn]
    have hlin_div : xFn q + 2 * s - Real.sqrt (RFn q) = (-4 * puvFn q * quvFn q) / DFn q := by
      rw [eq_div_iff hD_ne]; exact hlin
    rw [hlin_div]
    field_simp [hD_ne]
    ring
  have hinv_sq : invSqrtU q ^ 2 = (u (wShift (lekiliMove1 s q), q 1))⁻¹ := by
    dsimp only [invSqrtU]
    rw [inv_pow, Real.sq_sqrt hu_q_pos.le]
  have hG_final : WFn (lekiliMove1 s q) =
      QFn q ^ 3 - 3 * TFn (lekiliMove1 s q) * QFn q +
        (UFn q * invSqrtU q) ^ 2 - (VFn q * invSqrtU q) ^ 2 := by
    have h1 : (QFn q ^ 3 - 3 * TFn (lekiliMove1 s q) * QFn q - WFn (lekiliMove1 s q)) *
        u (wShift (lekiliMove1 s q), q 1) = VFn q ^ 2 - UFn q ^ 2 := by
      calc
        (QFn q ^ 3 - 3 * TFn (lekiliMove1 s q) * QFn q - WFn (lekiliMove1 s q)) *
            u (wShift (lekiliMove1 s q), q 1)
          = G (wShift (lekiliMove1 s q), q 1) := hG.symm
        _ = -((lekiliMove1 s q) 1 - 2 * q 1 * (Real.sqrt (RFn q) - m2)) := by
            rw [hG_lhs]; ring
        _ = VFn q ^ 2 - UFn q ^ 2 := by rw [hdec]; ring
    have hu_ne : u (wShift (lekiliMove1 s q), q 1) ≠ 0 := hu_q_pos.ne'
    have h2 : QFn q ^ 3 - 3 * TFn (lekiliMove1 s q) * QFn q - WFn (lekiliMove1 s q) =
        (VFn q ^ 2 - UFn q ^ 2) * invSqrtU q ^ 2 := by
      rw [hinv_sq, ← div_eq_mul_inv, eq_div_iff hu_ne]
      exact h1
    linear_combination -h2
  refine ext_vec2 rfl ?_
  simp only [Ψ, Φ, wrinkledCuspMap, vec2_one, vec4_zero, vec4_one, vec4_two, vec4_three]
  exact hG_final

/-- For every `s ≠ 0`, all three cusp points on `criticalPoints (lekiliMove1 s)` where
`p₀³ - 3 p₀ p₁² = s³` are locally modeled on `wrinkledCuspMap` (`IsWrinkledCuspAt`). -/
-- tier: T2
theorem isWrinkledCuspAt_lekiliMove1 {s : ℝ} (hs : s ≠ 0) {p : EuclideanSpace ℝ (Fin 4)}
    (hp : p ∈ criticalPoints (𝓡 4) (𝓡 2) (lekiliMove1 s))
    (hcusp : p 0 ^ 3 - 3 * p 0 * p 1 ^ 2 = s ^ 3) :
    IsWrinkledCuspAt (𝓡 4) (𝓡 2) (lekiliMove1 s) p := by
  suffices hpos : ∀ {t : ℝ} (ht : 0 < t) {q : EuclideanSpace ℝ (Fin 4)},
      q ∈ criticalPoints (𝓡 4) (𝓡 2) (lekiliMove1 t) →
      q 0 ^ 3 - 3 * q 0 * q 1 ^ 2 = t ^ 3 →
      IsWrinkledCuspAt (𝓡 4) (𝓡 2) (lekiliMove1 t) q by
    rcases lt_or_gt_of_ne hs with hneg | hpos_s
    · have ht : 0 < -s := neg_pos.mpr hneg
      have hf0 : (flipSignDom p) 0 = -p 0 := rfl
      have hf1 : (flipSignDom p) 1 = -p 1 := rfl
      have hf2 : (flipSignDom p) 2 = p 2 := rfl
      have hf3 : (flipSignDom p) 3 = p 3 := rfl
      have hcrit : flipSignDom p ∈ criticalPoints (𝓡 4) (𝓡 2) (lekiliMove1 (-s)) := by
        rw [criticalPoints_lekiliMove1, Set.mem_ofPred_eq] at hp ⊢
        rw [hf0, hf1, hf2, hf3]
        exact ⟨by linear_combination hp.1, hp.2.1, hp.2.2⟩
      have hcusp' : (flipSignDom p) 0 ^ 3 - 3 * (flipSignDom p) 0 * (flipSignDom p) 1 ^ 2 =
          (-s) ^ 3 := by
        rw [hf0, hf1]
        linear_combination -hcusp
      have hbase := hpos ht hcrit hcusp'
      change IsLocallyModeledOn (𝓡 4) (𝓡 2) (lekiliMove1 (-s)) (flipSignDom p)
        wrinkledCuspMap 0 at hbase
      change IsLocallyModeledOn (𝓡 4) (𝓡 2) (lekiliMove1 s) p wrinkledCuspMap 0
      exact isLocallyModeledOn_comp_equiv flipSignDom (ContinuousLinearEquiv.refl ℝ EuclideanPlane)
        (fun q ↦ by rw [ContinuousLinearEquiv.refl_apply, lekiliMove1_flipSignDom, neg_neg])
        hbase
    · exact hpos hpos_s hp hcusp
  intro t ht q hq hqcusp
  have hsymm (x : EuclideanSpace ℝ (Fin 4)) :
      rotC3Tgt.symm (lekiliMove1 t x) = lekiliMove1 t (rotC3Dom.symm x) := by
    rw [rotC3Tgt.symm_apply_eq, ← lekiliMove1_rotC3Dom, ContinuousLinearEquiv.apply_symm_apply]
  have h0 : IsLocallyModeledOn (𝓡 4) (𝓡 2) (lekiliMove1 t) (vec4 t 0 0 0) wrinkledCuspMap 0 :=
    isWrinkledCuspAt_lekiliMove1_pos ht
  rcases eq_cusp_orbit_of_cubed_eq hq hqcusp with rfl | rfl | rfl
  · exact h0
  · change IsLocallyModeledOn (𝓡 4) (𝓡 2) (lekiliMove1 t) (rotC3Dom (vec4 t 0 0 0))
      wrinkledCuspMap 0
    exact isLocallyModeledOn_comp_equiv rotC3Dom.symm rotC3Tgt.symm hsymm
      (by simpa [ContinuousLinearEquiv.symm_apply_apply] using h0)
  · have h1 : IsLocallyModeledOn (𝓡 4) (𝓡 2) (lekiliMove1 t)
        (rotC3Dom (vec4 t 0 0 0)) wrinkledCuspMap 0 :=
      isLocallyModeledOn_comp_equiv rotC3Dom.symm rotC3Tgt.symm hsymm
        (by simpa [ContinuousLinearEquiv.symm_apply_apply] using h0)
    change IsLocallyModeledOn (𝓡 4) (𝓡 2) (lekiliMove1 t)
      (rotC3Dom (rotC3Dom (vec4 t 0 0 0))) wrinkledCuspMap 0
    exact isLocallyModeledOn_comp_equiv rotC3Dom.symm rotC3Tgt.symm hsymm
      (by simpa [ContinuousLinearEquiv.symm_apply_apply] using h1)

/-- Algebraic half-angle parameters `(α, β)` with `α² + β² = 1`, `α² - β² = p₀ / s`,
`2 α β = p₁ / s`, `C = α³ - 3 α β²`, `S = β³ - 3 α² β`, and `S ≠ 0` away from the 3 cusps. -/
private theorem exists_half_angle_params {s p0 p1 : ℝ} (hs : 0 < s)
    (h01 : p0 ^ 2 + p1 ^ 2 = s ^ 2) (hnc : p0 ^ 3 - 3 * p0 * p1 ^ 2 ≠ s ^ 3) :
    ∃ α β C S : ℝ,
      α ^ 2 + β ^ 2 = 1 ∧
      α ^ 2 - β ^ 2 = p0 / s ∧
      2 * α * β = p1 / s ∧
      C = α ^ 3 - 3 * α * β ^ 2 ∧
      S = β ^ 3 - 3 * α ^ 2 * β ∧
      C ^ 2 + S ^ 2 = 1 ∧
      S ≠ 0 := by
  have hs_ne : s ≠ 0 := hs.ne'
  obtain ⟨α, β, hab1, hab_re, hab_im⟩ :
      ∃ α β : ℝ, α ^ 2 + β ^ 2 = 1 ∧ α ^ 2 - β ^ 2 = p0 / s ∧ 2 * α * β = p1 / s := by
    by_cases hneg : p0 = -s
    · have hp1sq : p1 ^ 2 = 0 := by linear_combination h01 - (p0 - s) * hneg
      have hp1 : p1 = 0 := sq_eq_zero_iff.mp hp1sq
      refine ⟨0, 1, by norm_num, ?_, ?_⟩
      · rw [hneg]; field_simp [hs_ne]; ring
      · simp [hp1]
    · have hp0_sq : p0 ^ 2 ≤ s ^ 2 := by linarith [sq_nonneg p1]
      have hp0_ge : -s ≤ p0 := by
        by_contra hlt
        have h1 : s < -p0 := by linarith
        nlinarith [sq_nonneg p0]
      have hsp_pos : 0 < s + p0 := lt_of_le_of_ne (by linarith) (fun heq ↦ hneg (by linarith))
      have harg_pos : 0 < (1 + p0 / s) / 2 := by
        have h1 : 1 + p0 / s = (s + p0) / s := by field_simp [hs_ne]
        rw [h1]
        exact half_pos (div_pos hsp_pos hs)
      let α : ℝ := Real.sqrt ((1 + p0 / s) / 2)
      have hα_pos : 0 < α := Real.sqrt_pos.mpr harg_pos
      have hα_ne : α ≠ 0 := hα_pos.ne'
      have hα2 : α ^ 2 = (1 + p0 / s) / 2 := Real.sq_sqrt harg_pos.le
      let β : ℝ := (p1 / s) / (2 * α)
      have hβ2 : β ^ 2 = (1 - p0 / s) / 2 := by
        have h1 : (p1 / s) ^ 2 = (1 - p0 / s) * (1 + p0 / s) := by
          have hp : p1 ^ 2 = (s - p0) * (s + p0) := by linear_combination h01
          field_simp [hs_ne]
          exact hp
        dsimp only [β]
        rw [div_pow, mul_pow, hα2, h1]
        have hpos1 : 1 + p0 / s ≠ 0 := by linarith
        field_simp [hpos1]
      refine ⟨α, β, by linarith, by linarith, ?_⟩
      dsimp only [β]
      field_simp [hα_ne]
  let C : ℝ := α ^ 3 - 3 * α * β ^ 2
  let S : ℝ := β ^ 3 - 3 * α ^ 2 * β
  have hCS1 : C ^ 2 + S ^ 2 = 1 := by
    calc
      C ^ 2 + S ^ 2 = (α ^ 2 + β ^ 2) ^ 3 := by dsimp only [C, S]; ring
      _ = 1 := by rw [hab1, one_pow]
  have hCS2 : C ^ 2 - S ^ 2 = (p0 ^ 3 - 3 * p0 * p1 ^ 2) / s ^ 3 := by
    calc
      C ^ 2 - S ^ 2 = (α ^ 2 - β ^ 2) * ((α ^ 2 - β ^ 2) ^ 2 - 3 * (2 * α * β) ^ 2) := by
        dsimp only [C, S]; ring
      _ = (p0 / s) * ((p0 / s) ^ 2 - 3 * (p1 / s) ^ 2) := by rw [hab_re, hab_im]
      _ = (p0 ^ 3 - 3 * p0 * p1 ^ 2) / s ^ 3 := by field_simp [hs_ne]
  have hS_ne : S ≠ 0 := by
    intro hS0
    have hC2 : C ^ 2 = 1 := by
      rw [hS0] at hCS1
      linarith
    have h1 : (p0 ^ 3 - 3 * p0 * p1 ^ 2) / s ^ 3 = 1 := by
      rw [hC2, hS0] at hCS2
      linarith
    exact hnc ((div_eq_one_iff_eq (pow_ne_zero 3 hs_ne)).mp h1)
  exact ⟨α, β, C, S, hab1, hab_re, hab_im, rfl, rfl, hCS1, hS_ne⟩

/-- Degree-`2` Weierstrass preparation for the non-cusp indefinite fold profile
`G₂(w, y) = 4 s C w₁ / E(y) + w₁² / E(y)² - y² - w₀` where `E(y) = 2(y - 2 s S)`. -/
private theorem lekiliMove1_fold_weierstrass {s C S : ℝ} (hs : 0 < s) (hS : S ≠ 0) :
    ∃ (c : Fin 2 → (Fin 2 → ℝ) → ℝ) (u : (Fin 2 → ℝ) × ℝ → ℝ),
      (∀ i : Fin 2, AnalyticAt ℝ (c i) 0) ∧
      (∀ i : Fin 2, c i 0 = 0) ∧
      AnalyticAt ℝ u (0, 0) ∧
      u (0, 0) = -1 ∧
      ((fun q : (Fin 2 → ℝ) × ℝ ↦
          4 * s * C * q.1 1 / (2 * (q.2 - 2 * s * S)) +
            q.1 1 ^ 2 / (2 * (q.2 - 2 * s * S)) ^ 2 - q.2 ^ 2 - q.1 0) =ᶠ[𝓝 (0, 0)]
        fun q ↦ (q.2 ^ 2 + c 1 q.1 * q.2 + c 0 q.1) * u q) ∧
      fderiv ℝ (c 0) 0 =
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0 +
          (C / S) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1 := by
  let E : ℝ → ℝ := fun y ↦ 2 * (y - 2 * s * S)
  let G₂ : (Fin 2 → ℝ) × ℝ → ℝ := fun q ↦
    4 * s * C * q.1 1 / E q.2 + q.1 1 ^ 2 / E q.2 ^ 2 - q.2 ^ 2 - q.1 0
  have hE_an : AnalyticAt ℝ E 0 :=
    analyticAt_const.mul (analyticAt_id.sub analyticAt_const)
  have hE0 : E 0 = -4 * s * S := by dsimp only [E]; ring
  have hE0_ne : E 0 ≠ 0 := by rw [hE0]; exact mul_ne_zero (mul_ne_zero (by norm_num) hs.ne') hS
  have hG₂_an : AnalyticAt ℝ G₂ (0, 0) := by
    have hq1_0 : AnalyticAt ℝ (fun q : (Fin 2 → ℝ) × ℝ ↦ q.1 0) (0, 0) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0).comp
        (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) ℝ)).analyticAt (0, 0)
    have hq1_1 : AnalyticAt ℝ (fun q : (Fin 2 → ℝ) × ℝ ↦ q.1 1) (0, 0) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1).comp
        (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) ℝ)).analyticAt (0, 0)
    have hq2 : AnalyticAt ℝ (fun q : (Fin 2 → ℝ) × ℝ ↦ q.2) (0, 0) :=
      (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) ℝ).analyticAt (0, 0)
    have hE_q : AnalyticAt ℝ (fun q : (Fin 2 → ℝ) × ℝ ↦ E q.2) (0, 0) :=
      hE_an.comp_of_eq hq2 rfl
    exact (((((analyticAt_const.mul hq1_1).div hE_q hE0_ne).add
      ((hq1_1.pow 2).div (hE_q.pow 2) (pow_ne_zero 2 hE0_ne))).sub (hq2.pow 2)).sub hq1_0)
  have hG₂_slice : (fun y : ℝ ↦ G₂ (0, y)) = fun y : ℝ ↦ (-1 : ℝ) * y ^ 2 := by
    funext y; simp [G₂]
  have hord : analyticOrderAt (fun y : ℝ ↦ G₂ (0, y)) 0 = (2 : ℕ) := by
    rw [hG₂_slice]
    have hm : analyticOrderAt ((fun _ : ℝ ↦ (-1 : ℝ)) * (id : ℝ → ℝ) ^ 2) 0 =
        analyticOrderAt (fun _ : ℝ ↦ (-1 : ℝ)) 0 + analyticOrderAt ((id : ℝ → ℝ) ^ 2) 0 :=
      analyticOrderAt_mul analyticAt_const (analyticAt_id.pow 2)
    change analyticOrderAt ((fun _ : ℝ ↦ (-1 : ℝ)) * (id : ℝ → ℝ) ^ 2) 0 = (2 : ℕ)
    rw [hm, ((analyticAt_const (𝕜 := ℝ) (v := (-1 : ℝ))).analyticOrderAt_eq_zero).2
      (by norm_num), analyticOrderAt_pow analyticAt_id 2, analyticOrderAt_id]
    simp
  obtain ⟨c, u, hc_an, hc0, hu_an, hu0, heq_wp⟩ :=
    hG₂_an.exists_weierstrassPreparation_real hord
  have heq_ev : G₂ =ᶠ[𝓝 (0, 0)] fun q ↦ (q.2 ^ 2 + c 1 q.1 * q.2 + c 0 q.1) * u q := by
    filter_upwards [heq_wp] with q hq
    rw [hq, TauCeti.Polynomial.eval_monicOfCoeff, Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, sub_zero]
    ring
  have hu_val : u (0, 0) = -1 := by
    have hslice : (fun y : ℝ ↦ (-1 : ℝ) * y ^ 2) =ᶠ[𝓝 0] fun y : ℝ ↦ y ^ 2 * u (0, y) := by
      have ht : Tendsto (fun y : ℝ ↦ ((0 : Fin 2 → ℝ), y)) (𝓝 0) (𝓝 (0, 0)) :=
        ContinuousAt.tendsto (continuousAt_const.prodMk continuousAt_id)
      filter_upwards [ht.eventually heq_ev] with y hy
      have hy0 := congrFun hG₂_slice y
      rw [← hy0, hy, hc0 0, hc0 1]
      ring
    have hu_eq : (fun y : ℝ ↦ u (0, y)) =ᶠ[𝓝[≠] 0] fun _ : ℝ ↦ (-1 : ℝ) := by
      filter_upwards [nhdsWithin_le_nhds hslice, self_mem_nhdsWithin] with y hy hy0
      exact mul_left_cancel₀ (pow_ne_zero 2 hy0) (by linear_combination -hy)
    have ht1 : Tendsto (fun y : ℝ ↦ u (0, y)) (𝓝[≠] 0) (𝓝 (u (0, 0))) :=
      (hu_an.continuousAt.comp (continuousAt_const.prodMk continuousAt_id)).mono_left
        nhdsWithin_le_nhds
    exact tendsto_nhds_unique ht1 (tendsto_const_nhds.congr' hu_eq.symm)
  have hc0_fderiv : fderiv ℝ (c 0) 0 =
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0 +
        (C / S) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1 := by
    have hprod_ev : (fun w : Fin 2 → ℝ ↦ c 0 w * u (w, 0)) =ᶠ[𝓝 0]
        fun w : Fin 2 → ℝ ↦ -(w 0 + (C / S) * w 1) + w 1 ^ 2 / E 0 ^ 2 := by
      have ht : Tendsto (fun w : Fin 2 → ℝ ↦ (w, (0 : ℝ))) (𝓝 0) (𝓝 (0, 0)) :=
        ContinuousAt.tendsto (continuousAt_id.prodMk continuousAt_const)
      filter_upwards [ht.eventually heq_ev] with w hw
      have hG0 : G₂ (w, 0) = -(w 0 + (C / S) * w 1) + w 1 ^ 2 / E 0 ^ 2 := by
        dsimp only [G₂]
        rw [hE0]
        field_simp [hs.ne', hS]
        ring
      rw [← hG0, hw]
      ring
    have h1 : HasFDerivAt (fun w : Fin 2 → ℝ ↦ c 0 w * u (w, (0 : ℝ)))
        (-(fderiv ℝ (c 0) 0)) 0 := by
      have hc0d : HasFDerivAt (c 0) (fderiv ℝ (c 0) 0) 0 :=
        (hc_an 0).differentiableAt.hasFDerivAt
      have hmap : AnalyticAt ℝ (fun w : Fin 2 → ℝ ↦ (w, (0 : ℝ))) 0 :=
        (analyticAt_id (𝕜 := ℝ) (E := Fin 2 → ℝ)).prod
          (analyticAt_const (𝕜 := ℝ) (v := (0 : ℝ)))
      have hud : HasFDerivAt (fun w : Fin 2 → ℝ ↦ u (w, (0 : ℝ)))
          (fderiv ℝ (fun w : Fin 2 → ℝ ↦ u (w, (0 : ℝ))) 0) 0 :=
        (hu_an.comp_of_eq hmap rfl).differentiableAt.hasFDerivAt
      refine (hc0d.mul hud).congr_fderiv ?_
      ext v
      simp [hc0 0, hu_val, zero_smul]
    have h2 : HasFDerivAt
        (fun w : Fin 2 → ℝ ↦ -(w 0 + (C / S) * w 1) + w 1 ^ 2 / E 0 ^ 2)
        (-(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0 +
          (C / S) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1)) 0 := by
      have hp0 : HasFDerivAt (fun w : Fin 2 → ℝ ↦ w 0)
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0) 0 :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0).hasFDerivAt
      have hp1 : HasFDerivAt (fun w : Fin 2 → ℝ ↦ w 1)
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1) 0 :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1).hasFDerivAt
      have hlin := (hp0.add (hp1.const_mul (C / S))).neg
      have hquad : HasFDerivAt (fun w : Fin 2 → ℝ ↦ w 1 ^ 2 / E 0 ^ 2)
          (0 : (Fin 2 → ℝ) →L[ℝ] ℝ) 0 := by
        have heq_q : (fun w : Fin 2 → ℝ ↦ w 1 ^ 2 / E 0 ^ 2) =
            fun w ↦ w 1 ^ 2 * (1 / E 0 ^ 2 : ℝ) := by funext w; ring
        rw [heq_q]
        refine ((hp1.pow 2).mul_const (1 / E 0 ^ 2 : ℝ)).congr_fderiv ?_
        ext v; simp
      refine (hlin.add hquad).congr_fderiv ?_
      ext v; simp [smul_eq_mul]
    have hfeq := h1.unique (h2.congr_of_eventuallyEq hprod_ev)
    exact neg_inj.mp hfeq
  exact ⟨c, u, hc_an, hc0, hu_an, hu_val, heq_ev, hc0_fderiv⟩

/-- Bundled parameters and Weierstrass preparation data at a non-cusp critical point of
`lekiliMove1 s` (`s > 0`). -/
private structure LekiliFoldData where
  s : ℝ
  hs : 0 < s
  p : EuclideanSpace ℝ (Fin 4)
  h01 : p 0 ^ 2 + p 1 ^ 2 = s ^ 2
  hp2 : p 2 = 0
  hp3 : p 3 = 0
  α : ℝ
  β : ℝ
  C : ℝ
  S : ℝ
  hab1 : α ^ 2 + β ^ 2 = 1
  hab_re : α ^ 2 - β ^ 2 = p 0 / s
  hab_im : 2 * α * β = p 1 / s
  hC_eq : C = α ^ 3 - 3 * α * β ^ 2
  hS_eq : S = β ^ 3 - 3 * α ^ 2 * β
  hS_ne : S ≠ 0
  c : Fin 2 → (Fin 2 → ℝ) → ℝ
  u : (Fin 2 → ℝ) × ℝ → ℝ
  hc_an : ∀ i, AnalyticAt ℝ (c i) 0
  hc0 : ∀ i, c i 0 = 0
  hu_an : AnalyticAt ℝ u (0, 0)
  hu_val : u (0, 0) = -1
  heq_wp :
    (fun q : (Fin 2 → ℝ) × ℝ ↦
        4 * s * C * q.1 1 / (2 * (q.2 - 2 * s * S)) +
          q.1 1 ^ 2 / (2 * (q.2 - 2 * s * S)) ^ 2 - q.2 ^ 2 - q.1 0) =ᶠ[𝓝 (0, 0)]
      fun q ↦ (q.2 ^ 2 + c 1 q.1 * q.2 + c 0 q.1) * u q
  hc0_fderiv :
    fderiv ℝ (c 0) 0 =
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0 +
        (C / S) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1
  U_c : Set (Fin 2 → ℝ)
  hU_c_sub : ∀ w ∈ U_c, AnalyticAt ℝ (c 0) w ∧ AnalyticAt ℝ (c 1) w
  hU_c_open : IsOpen U_c
  h0_Uc : (0 : Fin 2 → ℝ) ∈ U_c
  U_u : Set ((Fin 2 → ℝ) × ℝ)
  hU_u_sub : ∀ q ∈ U_u, AnalyticAt ℝ u q
  hU_u_open : IsOpen U_u
  h0_Uu : ((0 : Fin 2 → ℝ), (0 : ℝ)) ∈ U_u

namespace LekiliFoldData

private noncomputable def a (d : LekiliFoldData) : ℝ := d.p 0 / d.s
private noncomputable def b (d : LekiliFoldData) : ℝ := d.p 1 / d.s
private noncomputable def CdivS (d : LekiliFoldData) : ℝ := d.C / d.S
private noncomputable def rB (d : LekiliFoldData) : ℝ := Real.sqrt (1 + d.CdivS ^ 2)

private noncomputable def kₓ (d : LekiliFoldData) : ℝ :=
  (1 / 2 : ℝ) * (fderiv ℝ (d.c 1) 0) ![4 * d.s * d.C, -4 * d.s * d.S]

private theorem hs_ne (d : LekiliFoldData) : d.s ≠ 0 := d.hs.ne'

private theorem hrB_pos (d : LekiliFoldData) : 0 < d.rB :=
  Real.sqrt_pos.mpr (by positivity)

private theorem hrB_ne (d : LekiliFoldData) : d.rB ≠ 0 := d.hrB_pos.ne'

private theorem hr2_ne : (Real.sqrt 2 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'

private theorem hab_norm (d : LekiliFoldData) : d.a ^ 2 + d.b ^ 2 = 1 := by
  calc
    d.a ^ 2 + d.b ^ 2 = (d.α ^ 2 - d.β ^ 2) ^ 2 + (2 * d.α * d.β) ^ 2 := by
      dsimp only [a, b]; rw [← d.hab_re, ← d.hab_im]
    _ = (d.α ^ 2 + d.β ^ 2) ^ 2 := by ring
    _ = 1 := by rw [d.hab1, one_pow]

private theorem hp0_eq (d : LekiliFoldData) : d.p 0 = d.s * (d.α ^ 2 - d.β ^ 2) := by
  rw [d.hab_re]; field_simp [d.hs_ne]

private theorem hp1_eq (d : LekiliFoldData) : d.p 1 = 2 * d.s * d.α * d.β := by
  calc
    d.p 1 = d.s * (d.p 1 / d.s) := by field_simp [d.hs_ne]
    _ = d.s * (2 * d.α * d.β) := by rw [← d.hab_im]
    _ = 2 * d.s * d.α * d.β := by ring

private noncomputable def L₀ (d : LekiliFoldData) : EuclideanPlane →L[ℝ] ℝ :=
  d.a • euclidProj (0 : Fin 2) - d.b • euclidProj (1 : Fin 2)

private noncomputable def L₁ (d : LekiliFoldData) : EuclideanPlane →L[ℝ] ℝ :=
  d.b • euclidProj (0 : Fin 2) + d.a • euclidProj (1 : Fin 2)

private noncomputable def rotWCLM (d : LekiliFoldData) : EuclideanPlane →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi ![d.L₀, d.L₁]

private theorem hrot0 (d : LekiliFoldData) (w : EuclideanPlane) :
    d.rotWCLM w 0 = d.a * w 0 - d.b * w 1 := by
  simp [rotWCLM, L₀, euclidProj]

private theorem hrot1 (d : LekiliFoldData) (w : EuclideanPlane) :
    d.rotWCLM w 1 = d.b * w 0 + d.a * w 1 := by
  simp [rotWCLM, L₁, euclidProj]

private noncomputable def wShift (d : LekiliFoldData) : EuclideanPlane → (Fin 2 → ℝ) :=
  fun w ↦ d.rotWCLM (w - lekiliMove1 d.s d.p)

private theorem hwShift0 (d : LekiliFoldData) (w : EuclideanPlane) :
    d.wShift w 0 =
      d.a * (w 0 - (lekiliMove1 d.s d.p) 0) - d.b * (w 1 - (lekiliMove1 d.s d.p) 1) := by
  simp [wShift, hrot0]

private theorem hwShift1 (d : LekiliFoldData) (w : EuclideanPlane) :
    d.wShift w 1 =
      d.b * (w 0 - (lekiliMove1 d.s d.p) 0) + d.a * (w 1 - (lekiliMove1 d.s d.p) 1) := by
  simp [wShift, hrot1]

private theorem hwShift_p (d : LekiliFoldData) : d.wShift (lekiliMove1 d.s d.p) = 0 := by
  simp [wShift]

private theorem hwShift_diff (d : LekiliFoldData) : ContDiff ℝ ∞ d.wShift :=
  d.rotWCLM.contDiff.comp (contDiff_id.sub contDiff_const)

private theorem hwShift_fderiv (d : LekiliFoldData) (w : EuclideanPlane) :
    HasFDerivAt d.wShift d.rotWCLM w := by
  have hsub : HasFDerivAt (fun z : EuclideanPlane ↦ z - lekiliMove1 d.s d.p)
      (ContinuousLinearMap.id ℝ EuclideanPlane) w :=
    (hasFDerivAt_id w).sub_const _
  simpa [wShift] using (d.rotWCLM.hasFDerivAt.comp w hsub)

private noncomputable def XFn (d : LekiliFoldData) : EuclideanSpace ℝ (Fin 4) → ℝ :=
  fun q ↦ d.α * (q 0 - d.p 0) - d.β * (q 1 - d.p 1)

private noncomputable def YFn (d : LekiliFoldData) : EuclideanSpace ℝ (Fin 4) → ℝ :=
  fun q ↦ d.β * (q 0 - d.p 0) + d.α * (q 1 - d.p 1)

private noncomputable def uFn (d : LekiliFoldData) : EuclideanSpace ℝ (Fin 4) → ℝ :=
  fun q ↦ d.α * q 2 - d.β * q 3

private noncomputable def vFn (d : LekiliFoldData) : EuclideanSpace ℝ (Fin 4) → ℝ :=
  fun q ↦ d.β * q 2 + d.α * q 3

private noncomputable def EFn (d : LekiliFoldData) : ℝ → ℝ :=
  fun y ↦ 2 * (y - 2 * d.s * d.S)

private noncomputable def MFn (d : LekiliFoldData) : EuclideanSpace ℝ (Fin 4) → ℝ :=
  fun q ↦ 4 * d.s * d.C * d.EFn (d.YFn q) + 2 * (d.wShift (lekiliMove1 d.s q)) 1

private noncomputable def denQFn (d : LekiliFoldData) : EuclideanSpace ℝ (Fin 4) → ℝ :=
  fun q ↦ d.EFn (d.YFn q) ^ 2 + 4 * d.vFn q ^ 2

private noncomputable def AFn (d : LekiliFoldData) : EuclideanSpace ℝ (Fin 4) → ℝ :=
  fun q ↦ 1 + 4 * d.vFn q ^ 2 / d.EFn (d.YFn q) ^ 2

private noncomputable def bFn (d : LekiliFoldData) : EuclideanSpace ℝ (Fin 4) → ℝ :=
  fun q ↦ d.MFn q / d.denQFn q

private noncomputable def BFn (d : LekiliFoldData) : EuclideanSpace ℝ (Fin 4) → ℝ :=
  fun q ↦ 1 + d.MFn q ^ 2 / (d.EFn (d.YFn q) ^ 2 * d.denQFn q)

private noncomputable def Utilde (d : LekiliFoldData) : EuclideanSpace ℝ (Fin 4) → ℝ :=
  fun q ↦ Real.sqrt (d.AFn q) * (d.uFn q - d.bFn q * d.vFn q)

private noncomputable def Vtilde (d : LekiliFoldData) : EuclideanSpace ℝ (Fin 4) → ℝ :=
  fun q ↦ Real.sqrt (d.BFn q) * d.vFn q

private noncomputable def uplus (d : LekiliFoldData) : (Fin 2 → ℝ) × ℝ → ℝ :=
  fun q ↦ -d.u q

private noncomputable def invSqrtU (d : LekiliFoldData) : EuclideanSpace ℝ (Fin 4) → ℝ :=
  fun q ↦ (Real.sqrt (d.uplus (d.wShift (lekiliMove1 d.s q), d.YFn q)))⁻¹

private noncomputable def Φ (d : LekiliFoldData) :
    EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4) := fun q ↦
  vec4
    (d.Utilde q * d.invSqrtU q)
    (Real.sqrt 2 * (d.YFn q + d.c 1 (d.wShift (lekiliMove1 d.s q)) / 2))
    (Real.sqrt 2 * d.Vtilde q * d.invSqrtU q)
    ((d.wShift (lekiliMove1 d.s q)) 1)

private noncomputable def Ψ (d : LekiliFoldData) : EuclideanPlane → EuclideanPlane := fun w ↦
  vec2 (d.c 0 (d.wShift w) - d.c 1 (d.wShift w) ^ 2 / 4) ((d.wShift w) 1)

private noncomputable def U_tgt (d : LekiliFoldData) : Set EuclideanPlane :=
  d.wShift ⁻¹' d.U_c

private noncomputable def U_dom (d : LekiliFoldData) : Set (EuclideanSpace ℝ (Fin 4)) :=
  {q | lekiliMove1 d.s q ∈ d.U_tgt ∧ (d.wShift (lekiliMove1 d.s q), d.YFn q) ∈ d.U_u ∧
    0 < d.uplus (d.wShift (lekiliMove1 d.s q), d.YFn q) ∧ d.EFn (d.YFn q) ≠ 0}

private theorem hc_contDiff (d : LekiliFoldData) (i : Fin 2) :
    ContDiffOn ℝ ∞ (d.c i) d.U_c := fun w hw ↦ by
  have hci : AnalyticAt ℝ (d.c i) w := by
    fin_cases i
    · exact (d.hU_c_sub w hw).1
    · exact (d.hU_c_sub w hw).2
  exact hci.contDiffAt.contDiffWithinAt

private theorem hu_contDiff (d : LekiliFoldData) : ContDiffOn ℝ ∞ d.u d.U_u :=
  fun q hq ↦ (d.hU_u_sub q hq).contDiffAt.contDiffWithinAt

private theorem hU_tgt_open (d : LekiliFoldData) : IsOpen d.U_tgt :=
  d.hU_c_open.preimage d.hwShift_diff.continuous

private theorem hfp_tgt (d : LekiliFoldData) : lekiliMove1 d.s d.p ∈ d.U_tgt := by
  simpa [U_tgt, d.hwShift_p] using d.h0_Uc

private theorem hY_cd (d : LekiliFoldData) : ContDiff ℝ ∞ d.YFn :=
  (contDiff_const.mul ((euclidProj 0).contDiff.sub contDiff_const)).add
    (contDiff_const.mul ((euclidProj 1).contDiff.sub contDiff_const))

private theorem hu_cd (d : LekiliFoldData) : ContDiff ℝ ∞ d.uFn :=
  (contDiff_const.mul (euclidProj 2).contDiff).sub (contDiff_const.mul (euclidProj 3).contDiff)

private theorem hv_cd (d : LekiliFoldData) : ContDiff ℝ ∞ d.vFn :=
  (contDiff_const.mul (euclidProj 2).contDiff).add (contDiff_const.mul (euclidProj 3).contDiff)

private theorem hE_cd (d : LekiliFoldData) : ContDiff ℝ ∞ (fun q ↦ d.EFn (d.YFn q)) :=
  contDiff_const.mul (d.hY_cd.sub contDiff_const)

private theorem hU_dom_open (d : LekiliFoldData) : IsOpen d.U_dom := by
  have hL_cont : Continuous (lekiliMove1 d.s) := (contDiff_lekiliMove1 d.s).continuous
  have hpair : Continuous (fun q ↦ (d.wShift (lekiliMove1 d.s q), d.YFn q)) :=
    (d.hwShift_diff.continuous.comp hL_cont).prodMk d.hY_cd.continuous
  have hu_cont : ContinuousOn (fun q ↦ d.uplus (d.wShift (lekiliMove1 d.s q), d.YFn q))
      ((fun q ↦ (d.wShift (lekiliMove1 d.s q), d.YFn q)) ⁻¹' d.U_u) :=
    (d.hu_contDiff.continuousOn.neg).comp hpair.continuousOn (fun _ hx ↦ hx)
  have h1 : IsOpen (lekiliMove1 d.s ⁻¹' d.U_tgt) := d.hU_tgt_open.preimage hL_cont
  have h2 : IsOpen ((fun q ↦ (d.wShift (lekiliMove1 d.s q), d.YFn q)) ⁻¹' d.U_u) :=
    d.hU_u_open.preimage hpair
  have h3 : IsOpen {q ∈ (fun q ↦ (d.wShift (lekiliMove1 d.s q), d.YFn q)) ⁻¹' d.U_u |
      0 < d.uplus (d.wShift (lekiliMove1 d.s q), d.YFn q)} :=
    hu_cont.isOpen_inter_preimage h2 isOpen_Ioi
  have h4 : IsOpen {q | d.EFn (d.YFn q) ≠ 0} := isOpen_ne.preimage d.hE_cd.continuous
  convert h1.inter (h3.inter h4) using 1
  ext q
  simp only [U_dom, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, and_assoc]

private theorem hYp (d : LekiliFoldData) : d.YFn d.p = 0 := by dsimp only [YFn]; ring

private theorem hup (d : LekiliFoldData) : d.uFn d.p = 0 := by
  dsimp only [uFn]; rw [d.hp2, d.hp3]; ring

private theorem hvp (d : LekiliFoldData) : d.vFn d.p = 0 := by
  dsimp only [vFn]; rw [d.hp2, d.hp3]; ring

private theorem hp_dom (d : LekiliFoldData) : d.p ∈ d.U_dom := by
  have hEp : d.EFn 0 = -4 * d.s * d.S := by dsimp only [EFn]; ring
  have huplus_p : d.uplus (0, 0) = 1 := by dsimp only [uplus]; rw [d.hu_val]; norm_num
  refine ⟨d.hfp_tgt, ?_, ?_, ?_⟩
  · simpa [d.hwShift_p, d.hYp] using d.h0_Uu
  · rw [d.hwShift_p, d.hYp, huplus_p]; norm_num
  · rw [d.hYp, hEp]; exact mul_ne_zero (mul_ne_zero (by norm_num) d.hs_ne) d.hS_ne

private theorem hΨ_diff (d : LekiliFoldData) : ContDiffOn ℝ ∞ d.Ψ d.U_tgt := by
  have hc_comp (i : Fin 2) : ContDiffOn ℝ ∞ (fun w ↦ d.c i (d.wShift w)) d.U_tgt :=
    (d.hc_contDiff i).comp d.hwShift_diff.contDiffOn (fun _ hw ↦ hw)
  have h0 := (hc_comp 0).sub (((hc_comp 1).pow 2).div_const 4)
  have h1 : ContDiffOn ℝ ∞ (fun w ↦ (d.wShift w) 1) d.U_tgt :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1).contDiff.comp
      d.hwShift_diff).contDiffOn
  exact contDiffOn_vec2 h0 h1

private theorem hdenQ_pos (d : LekiliFoldData) {q : EuclideanSpace ℝ (Fin 4)}
    (hq : q ∈ d.U_dom) : 0 < d.denQFn q := by
  have hE_sq : 0 < d.EFn (d.YFn q) ^ 2 := sq_pos_iff.mpr hq.2.2.2
  have hv_sq : 0 ≤ 4 * d.vFn q ^ 2 := by positivity
  dsimp only [denQFn]; linarith

private theorem hA_pos (d : LekiliFoldData) {q : EuclideanSpace ℝ (Fin 4)}
    (_ : q ∈ d.U_dom) : 0 < d.AFn q := by
  have h1 : 0 ≤ 4 * d.vFn q ^ 2 / d.EFn (d.YFn q) ^ 2 := by positivity
  dsimp only [AFn]; linarith

private theorem hB_pos (d : LekiliFoldData) {q : EuclideanSpace ℝ (Fin 4)}
    (hq : q ∈ d.U_dom) : 0 < d.BFn q := by
  have hE_sq : 0 ≤ d.EFn (d.YFn q) ^ 2 := sq_nonneg _
  have hd_pos : 0 < d.denQFn q := d.hdenQ_pos hq
  have hq_nn : 0 ≤ d.MFn q ^ 2 / (d.EFn (d.YFn q) ^ 2 * d.denQFn q) := by positivity
  dsimp only [BFn]; linarith

private theorem hL_cd (d : LekiliFoldData) : ContDiffOn ℝ ∞ (lekiliMove1 d.s) d.U_dom :=
  (contDiff_lekiliMove1 d.s).contDiffOn

private theorem hW1_cd (d : LekiliFoldData) :
    ContDiffOn ℝ ∞ (fun q ↦ (d.wShift (lekiliMove1 d.s q)) 1) d.U_dom :=
  (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1).contDiff.comp
    d.hwShift_diff).contDiffOn).comp d.hL_cd (fun _ _ ↦ Set.mem_univ _)

private theorem hM_cd (d : LekiliFoldData) : ContDiffOn ℝ ∞ d.MFn d.U_dom :=
  ((contDiff_const (c := 4 * d.s * d.C)).contDiffOn.mul d.hE_cd.contDiffOn).add
    ((contDiff_const (c := (2 : ℝ))).contDiffOn.mul d.hW1_cd)

private theorem hden_cd (d : LekiliFoldData) : ContDiffOn ℝ ∞ d.denQFn d.U_dom :=
  ((d.hE_cd.pow 2).contDiffOn).add
    ((contDiff_const (c := (4 : ℝ))).contDiffOn.mul (d.hv_cd.pow 2).contDiffOn)

private theorem hA_cd (d : LekiliFoldData) : ContDiffOn ℝ ∞ d.AFn d.U_dom :=
  (contDiff_const (c := (1 : ℝ))).contDiffOn.add
    (((contDiff_const (c := (4 : ℝ))).contDiffOn.mul (d.hv_cd.pow 2).contDiffOn).div
      (d.hE_cd.pow 2).contDiffOn fun _ hq ↦ pow_ne_zero 2 hq.2.2.2)

private theorem hb_cd (d : LekiliFoldData) : ContDiffOn ℝ ∞ d.bFn d.U_dom :=
  d.hM_cd.div d.hden_cd fun _ hq ↦ (d.hdenQ_pos hq).ne'

private theorem hB_cd (d : LekiliFoldData) : ContDiffOn ℝ ∞ d.BFn d.U_dom :=
  (contDiff_const (c := (1 : ℝ))).contDiffOn.add
    ((d.hM_cd.pow 2).div ((d.hE_cd.pow 2).contDiffOn.mul d.hden_cd)
      fun _ hq ↦ mul_ne_zero (pow_ne_zero 2 hq.2.2.2) (d.hdenQ_pos hq).ne')

private theorem hinv_cd (d : LekiliFoldData) : ContDiffOn ℝ ∞ d.invSqrtU d.U_dom :=
  (((d.hu_contDiff.neg).comp
      ((d.hwShift_diff.contDiffOn.comp d.hL_cd (fun _ _ ↦ Set.mem_univ _)).prodMk
        d.hY_cd.contDiffOn)
      (fun _ hq ↦ hq.2.1)).sqrt fun _ hq ↦ hq.2.2.1.ne').inv fun _ hq ↦
    (Real.sqrt_pos.mpr hq.2.2.1).ne'

private theorem hΦ_diff (d : LekiliFoldData) : ContDiffOn ℝ ∞ d.Φ d.U_dom := by
  have hUtilde_cd : ContDiffOn ℝ ∞ d.Utilde d.U_dom :=
    (d.hA_cd.sqrt fun _ hq ↦ (d.hA_pos hq).ne').mul
      (d.hu_cd.contDiffOn.sub (d.hb_cd.mul d.hv_cd.contDiffOn))
  have hVtilde_cd : ContDiffOn ℝ ∞ d.Vtilde d.U_dom :=
    (d.hB_cd.sqrt fun _ hq ↦ (d.hB_pos hq).ne').mul d.hv_cd.contDiffOn
  have hc1_comp : ContDiffOn ℝ ∞ (fun q ↦ d.c 1 (d.wShift (lekiliMove1 d.s q))) d.U_dom :=
    (d.hc_contDiff 1).comp (d.hwShift_diff.contDiffOn.comp d.hL_cd (fun _ _ ↦ Set.mem_univ _))
      (fun _ hq ↦ hq.1)
  have h0 : ContDiffOn ℝ ∞ (fun q ↦ d.Utilde q * d.invSqrtU q) d.U_dom :=
    hUtilde_cd.mul d.hinv_cd
  have h1 : ContDiffOn ℝ ∞
      (fun q ↦ Real.sqrt 2 * (d.YFn q + d.c 1 (d.wShift (lekiliMove1 d.s q)) / 2)) d.U_dom :=
    (contDiff_const (c := Real.sqrt 2)).contDiffOn.mul
      (d.hY_cd.contDiffOn.add (hc1_comp.div_const 2))
  have h2 : ContDiffOn ℝ ∞ (fun q ↦ Real.sqrt 2 * d.Vtilde q * d.invSqrtU q) d.U_dom :=
    ((contDiff_const (c := Real.sqrt 2)).contDiffOn.mul hVtilde_cd).mul d.hinv_cd
  exact contDiffOn_vec4 h0 h1 h2 d.hW1_cd

private theorem hab_norm_fwd1 (d : LekiliFoldData) (v0 v1 : ℝ) :
    d.a * (d.a * v0 - d.b * v1) + d.b * (d.b * v0 + d.a * v1) = v0 := by
  linear_combination v0 * d.hab_norm

private theorem hab_norm_fwd2 (d : LekiliFoldData) (v0 v1 : ℝ) :
    -d.b * (d.a * v0 - d.b * v1) + d.a * (d.b * v0 + d.a * v1) = v1 := by
  linear_combination v1 * d.hab_norm

private theorem hab_norm_inv1 (d : LekiliFoldData) (l0 l1 : ℝ) :
    d.a * (d.a * l0 + d.b * l1) - d.b * (-d.b * l0 + d.a * l1) = l0 := by
  linear_combination l0 * d.hab_norm

private theorem hab_norm_inv2 (d : LekiliFoldData) (l0 l1 : ℝ) :
    d.b * (d.a * l0 + d.b * l1) + d.a * (-d.b * l0 + d.a * l1) = l1 := by
  linear_combination l1 * d.hab_norm

private theorem h1_fwd1 (d : LekiliFoldData) (v0 v1 : ℝ) :
    d.α * (d.α * v0 - d.β * v1) + d.β * (d.β * v0 + d.α * v1) = v0 := by
  linear_combination v0 * d.hab1

private theorem h1_fwd2 (d : LekiliFoldData) (v0 v1 : ℝ) :
    -d.β * (d.α * v0 - d.β * v1) + d.α * (d.β * v0 + d.α * v1) = v1 := by
  linear_combination v1 * d.hab1

private theorem h1_inv1 (d : LekiliFoldData) (x0 y0 : ℝ) :
    d.α * (d.α * x0 + d.β * y0) - d.β * (-d.β * x0 + d.α * y0) = x0 := by
  linear_combination x0 * d.hab1

private theorem h1_inv2 (d : LekiliFoldData) (x0 y0 : ℝ) :
    d.β * (d.α * x0 + d.β * y0) + d.α * (-d.β * x0 + d.α * y0) = y0 := by
  linear_combination y0 * d.hab1

private noncomputable def eΨ (d : LekiliFoldData) : EuclideanPlane ≃L[ℝ] EuclideanPlane :=
  { toFun v :=
      let l₀ := d.a * v 0 - d.b * v 1
      let l₁ := d.b * v 0 + d.a * v 1
      vec2 (l₀ + d.CdivS * l₁) l₁
    invFun z :=
      let l₀ := z 0 - d.CdivS * z 1
      let l₁ := z 1
      vec2 (d.a * l₀ + d.b * l₁) (-d.b * l₀ + d.a * l₁)
    map_add' u v := by
      refine ext_vec2 ?_ ?_ <;>
        (simp only [PiLp.add_apply, vec2_zero, vec2_one]; ring)
    map_smul' r v := by
      refine ext_vec2 ?_ ?_ <;>
        (simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, vec2_zero, vec2_one]; ring)
    left_inv v := by
      refine ext_vec2 ?_ ?_
      · simp only [vec2_zero, vec2_one]
        rw [show (d.a * v 0 - d.b * v 1 + d.CdivS * (d.b * v 0 + d.a * v 1)) -
            d.CdivS * (d.b * v 0 + d.a * v 1) = d.a * v 0 - d.b * v 1 by ring,
          d.hab_norm_fwd1]
      · simp only [vec2_zero, vec2_one]
        rw [show (d.a * v 0 - d.b * v 1 + d.CdivS * (d.b * v 0 + d.a * v 1)) -
            d.CdivS * (d.b * v 0 + d.a * v 1) = d.a * v 0 - d.b * v 1 by ring,
          d.hab_norm_fwd2]
    right_inv z := by
      refine ext_vec2 ?_ ?_
      · simp only [vec2_zero, vec2_one]
        rw [d.hab_norm_inv1, d.hab_norm_inv2]; ring
      · simp only [vec2_zero, vec2_one]
        rw [d.hab_norm_inv2]
    continuous_toFun := continuous_vec2
      (((continuous_const.mul (euclidProj 0).continuous).sub
        (continuous_const.mul (euclidProj 1).continuous)).add
        (continuous_const.mul
          ((continuous_const.mul (euclidProj 0).continuous).add
            (continuous_const.mul (euclidProj 1).continuous))))
      ((continuous_const.mul (euclidProj 0).continuous).add
        (continuous_const.mul (euclidProj 1).continuous))
    continuous_invFun := continuous_vec2
      ((continuous_const.mul ((euclidProj 0).continuous.sub
        (continuous_const.mul (euclidProj 1).continuous))).add
        (continuous_const.mul (euclidProj 1).continuous))
      ((continuous_const.mul ((euclidProj 0).continuous.sub
        (continuous_const.mul (euclidProj 1).continuous))).add
        (continuous_const.mul (euclidProj 1).continuous)) }

private theorem heΨ_apply (d : LekiliFoldData) (v : EuclideanPlane) :
    d.eΨ v = vec2 ((d.a * v 0 - d.b * v 1) + d.CdivS * (d.b * v 0 + d.a * v 1))
      (d.b * v 0 + d.a * v 1) := rfl

private noncomputable def eΦ (d : LekiliFoldData) :
    EuclideanSpace ℝ (Fin 4) ≃L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  { toFun v :=
      let X' := d.α * v 0 - d.β * v 1
      let Y' := d.β * v 0 + d.α * v 1
      let u' := d.α * v 2 - d.β * v 3
      let v' := d.β * v 2 + d.α * v 3
      vec4 (u' + d.CdivS * v') (Real.sqrt 2 * (Y' + d.kₓ * X')) (Real.sqrt 2 * d.rB * v')
        (-4 * d.s * d.S * X')
    invFun z :=
      let X' := -z 3 / (4 * d.s * d.S)
      let Y' := z 1 / Real.sqrt 2 - d.kₓ * X'
      let v' := z 2 / (Real.sqrt 2 * d.rB)
      let u' := z 0 - d.CdivS * v'
      vec4 (d.α * X' + d.β * Y') (-d.β * X' + d.α * Y')
        (d.α * u' + d.β * v') (-d.β * u' + d.α * v')
    map_add' u v := by
      refine ext_vec4 ?_ ?_ ?_ ?_ <;>
        (simp only [PiLp.add_apply, vec4_zero, vec4_one, vec4_two, vec4_three]; ring)
    map_smul' r v := by
      refine ext_vec4 ?_ ?_ ?_ ?_ <;>
        (simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, vec4_zero, vec4_one,
          vec4_two, vec4_three]; ring)
    left_inv v := by
      refine ext_vec4 ?_ ?_ ?_ ?_
      · simp only [vec4_zero, vec4_one, vec4_two, vec4_three]
        rw [show -(-4 * d.s * d.S * (d.α * v 0 - d.β * v 1)) / (4 * d.s * d.S) =
              d.α * v 0 - d.β * v 1 by field_simp [d.hs_ne, d.hS_ne],
          show Real.sqrt 2 * (d.β * v 0 + d.α * v 1 + d.kₓ * (d.α * v 0 - d.β * v 1)) /
              Real.sqrt 2 - d.kₓ * (d.α * v 0 - d.β * v 1) = d.β * v 0 + d.α * v 1 by
            field_simp [hr2_ne]; ring,
          d.h1_fwd1]
      · simp only [vec4_zero, vec4_one, vec4_two, vec4_three]
        rw [show -(-4 * d.s * d.S * (d.α * v 0 - d.β * v 1)) / (4 * d.s * d.S) =
              d.α * v 0 - d.β * v 1 by field_simp [d.hs_ne, d.hS_ne],
          show Real.sqrt 2 * (d.β * v 0 + d.α * v 1 + d.kₓ * (d.α * v 0 - d.β * v 1)) /
              Real.sqrt 2 - d.kₓ * (d.α * v 0 - d.β * v 1) = d.β * v 0 + d.α * v 1 by
            field_simp [hr2_ne]; ring,
          d.h1_fwd2]
      · simp only [vec4_zero, vec4_one, vec4_two, vec4_three]
        rw [show Real.sqrt 2 * d.rB * (d.β * v 2 + d.α * v 3) / (Real.sqrt 2 * d.rB) =
            d.β * v 2 + d.α * v 3 by field_simp [hr2_ne, d.hrB_ne],
          show d.α * v 2 - d.β * v 3 + d.CdivS * (d.β * v 2 + d.α * v 3) -
              d.CdivS * (d.β * v 2 + d.α * v 3) = d.α * v 2 - d.β * v 3 by ring,
          d.h1_fwd1]
      · simp only [vec4_zero, vec4_one, vec4_two, vec4_three]
        rw [show Real.sqrt 2 * d.rB * (d.β * v 2 + d.α * v 3) / (Real.sqrt 2 * d.rB) =
            d.β * v 2 + d.α * v 3 by field_simp [hr2_ne, d.hrB_ne],
          show d.α * v 2 - d.β * v 3 + d.CdivS * (d.β * v 2 + d.α * v 3) -
              d.CdivS * (d.β * v 2 + d.α * v 3) = d.α * v 2 - d.β * v 3 by ring,
          d.h1_fwd2]
    right_inv z := by
      refine ext_vec4 ?_ ?_ ?_ ?_
      · simp only [vec4_zero, vec4_one, vec4_two, vec4_three]
        rw [d.h1_inv1, d.h1_inv2]; ring
      · simp only [vec4_zero, vec4_one, vec4_two, vec4_three]
        rw [d.h1_inv1, d.h1_inv2]; field_simp [d.hs_ne, d.hS_ne, hr2_ne]; ring
      · simp only [vec4_zero, vec4_one, vec4_two, vec4_three]
        rw [d.h1_inv2]; field_simp [hr2_ne, d.hrB_ne]
      · simp only [vec4_zero, vec4_one, vec4_two, vec4_three]
        rw [d.h1_inv1]; field_simp [d.hs_ne, d.hS_ne]
    continuous_toFun := by
      have h0 := (euclidProj (0 : Fin 4)).continuous
      have h1 := (euclidProj (1 : Fin 4)).continuous
      have h2 := (euclidProj (2 : Fin 4)).continuous
      have h3 := (euclidProj (3 : Fin 4)).continuous
      have hX' : Continuous (fun v : EuclideanSpace ℝ (Fin 4) ↦ d.α * v 0 - d.β * v 1) :=
        (continuous_const.mul h0).sub (continuous_const.mul h1)
      have hY' : Continuous (fun v : EuclideanSpace ℝ (Fin 4) ↦ d.β * v 0 + d.α * v 1) :=
        (continuous_const.mul h0).add (continuous_const.mul h1)
      have hu' : Continuous (fun v : EuclideanSpace ℝ (Fin 4) ↦ d.α * v 2 - d.β * v 3) :=
        (continuous_const.mul h2).sub (continuous_const.mul h3)
      have hv' : Continuous (fun v : EuclideanSpace ℝ (Fin 4) ↦ d.β * v 2 + d.α * v 3) :=
        (continuous_const.mul h2).add (continuous_const.mul h3)
      exact continuous_vec4
        (hu'.add (continuous_const.mul hv'))
        (continuous_const.mul (hY'.add (continuous_const.mul hX')))
        (continuous_const.mul hv')
        (continuous_const.mul hX')
    continuous_invFun := by
      have hz0 := (euclidProj (0 : Fin 4)).continuous
      have hz1 := (euclidProj (1 : Fin 4)).continuous
      have hz2 := (euclidProj (2 : Fin 4)).continuous
      have hz3 := (euclidProj (3 : Fin 4)).continuous
      have hX' : Continuous (fun z : EuclideanSpace ℝ (Fin 4) ↦ -z 3 / (4 * d.s * d.S)) :=
        hz3.neg.div_const (4 * d.s * d.S)
      have hY' : Continuous (fun z : EuclideanSpace ℝ (Fin 4) ↦
          z 1 / Real.sqrt 2 - d.kₓ * (-z 3 / (4 * d.s * d.S))) :=
        (hz1.div_const (Real.sqrt 2)).sub (continuous_const.mul hX')
      have hv' : Continuous (fun z : EuclideanSpace ℝ (Fin 4) ↦
          z 2 / (Real.sqrt 2 * d.rB)) :=
        hz2.div_const (Real.sqrt 2 * d.rB)
      have hu' : Continuous (fun z : EuclideanSpace ℝ (Fin 4) ↦
          z 0 - d.CdivS * (z 2 / (Real.sqrt 2 * d.rB))) :=
        hz0.sub (continuous_const.mul hv')
      exact continuous_vec4
        ((continuous_const.mul hX').add (continuous_const.mul hY'))
        ((continuous_const.mul hX').add (continuous_const.mul hY'))
        ((continuous_const.mul hu').add (continuous_const.mul hv'))
        ((continuous_const.mul hu').add (continuous_const.mul hv')) }

private theorem heΦ_apply (d : LekiliFoldData) (v : EuclideanSpace ℝ (Fin 4)) :
    d.eΦ v = vec4 ((d.α * v 2 - d.β * v 3) + d.CdivS * (d.β * v 2 + d.α * v 3))
      (Real.sqrt 2 * ((d.β * v 0 + d.α * v 1) + d.kₓ * (d.α * v 0 - d.β * v 1)))
      (Real.sqrt 2 * d.rB * (d.β * v 2 + d.α * v 3))
      (-4 * d.s * d.S * (d.α * v 0 - d.β * v 1)) := rfl

private theorem hc_w_hasFDeriv (d : LekiliFoldData) (i : Fin 2) (w : EuclideanPlane)
    (hw : w ∈ d.U_tgt) :
    HasFDerivAt (fun z ↦ d.c i (d.wShift z))
      ((fderiv ℝ (d.c i) (d.wShift w)).comp d.rotWCLM) w := by
  have hci : AnalyticAt ℝ (d.c i) (d.wShift w) := by
    have hw' : d.wShift w ∈ d.U_c := hw
    fin_cases i
    · exact (d.hU_c_sub _ hw').1
    · exact (d.hU_c_sub _ hw').2
  exact (hci.differentiableAt.hasFDerivAt).comp w (d.hwShift_fderiv w)

private theorem heΨ (d : LekiliFoldData) :
    (d.eΨ : EuclideanPlane →L[ℝ] EuclideanPlane) = fderiv ℝ d.Ψ (lekiliMove1 d.s d.p) := by
  have h0 := d.hc_w_hasFDeriv 0 (lekiliMove1 d.s d.p) d.hfp_tgt
  have h1 := d.hc_w_hasFDeriv 1 (lekiliMove1 d.s d.p) d.hfp_tgt
  rw [d.hwShift_p] at h0 h1
  have h1sq : HasFDerivAt (fun z : EuclideanPlane ↦ d.c 1 (d.wShift z) ^ 2 / 4)
      (0 : EuclideanPlane →L[ℝ] ℝ) (lekiliMove1 d.s d.p) := by
    have heq_q : (fun z : EuclideanPlane ↦ d.c 1 (d.wShift z) ^ 2 / 4) =
        fun z ↦ d.c 1 (d.wShift z) ^ 2 * (1 / 4 : ℝ) := by funext z; ring
    rw [heq_q]
    refine ((h1.pow 2).mul_const (1 / 4 : ℝ)).congr_fderiv ?_
    ext v; simp [d.hwShift_p, d.hc0 1]
  have hΨ0 : HasFDerivAt (fun w ↦ d.c 0 (d.wShift w) - d.c 1 (d.wShift w) ^ 2 / 4)
      ((fderiv ℝ (d.c 0) 0).comp d.rotWCLM) (lekiliMove1 d.s d.p) :=
    (h0.sub h1sq).congr_fderiv (by ext v; simp)
  have hΨ1 : HasFDerivAt (fun w ↦ (d.wShift w) 1)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1).comp d.rotWCLM)
      (lekiliMove1 d.s d.p) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1).hasFDerivAt).comp
      (lekiliMove1 d.s d.p) (d.hwShift_fderiv (lekiliMove1 d.s d.p))
  have hfΨ : HasFDerivAt d.Ψ
      (clmVec2 ((fderiv ℝ (d.c 0) 0).comp d.rotWCLM)
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1).comp d.rotWCLM))
      (lekiliMove1 d.s d.p) :=
    hasFDerivAt_vec2 hΨ0 hΨ1
  rw [hfΨ.fderiv]
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [ContinuousLinearEquiv.coe_coe, heΨ_apply]
  refine ext_vec2 ?_ ?_
  · simp only [clmVec2_apply, vec2_zero, ContinuousLinearMap.comp_apply, d.hc0_fderiv,
      add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, d.hrot0, d.hrot1, CdivS]
  · simp only [clmVec2_apply, vec2_one, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, d.hrot1]

private theorem hqp (d : LekiliFoldData) (i : Fin 4) :
    HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 4) ↦ q i) (euclidProj i) d.p :=
  (euclidProj i).hasFDerivAt

private theorem hY_der (d : LekiliFoldData) :
    HasFDerivAt d.YFn (d.β • euclidProj (0 : Fin 4) + d.α • euclidProj (1 : Fin 4)) d.p := by
  refine (((d.hqp 0).sub_const _).const_mul d.β |>.add
    (((d.hqp 1).sub_const _).const_mul d.α)).congr_fderiv ?_
  ext v
  simp only [add_apply, smul_apply, smul_eq_mul]

private theorem hu_der (d : LekiliFoldData) :
    HasFDerivAt d.uFn (d.α • euclidProj (2 : Fin 4) - d.β • euclidProj (3 : Fin 4)) d.p := by
  refine (((d.hqp 2).const_mul d.α).sub ((d.hqp 3).const_mul d.β)).congr_fderiv ?_
  ext v
  simp only [sub_apply, smul_apply, smul_eq_mul]

private theorem hv_der (d : LekiliFoldData) :
    HasFDerivAt d.vFn (d.β • euclidProj (2 : Fin 4) + d.α • euclidProj (3 : Fin 4)) d.p := by
  refine (((d.hqp 2).const_mul d.β).add ((d.hqp 3).const_mul d.α)).congr_fderiv ?_
  ext v
  simp only [add_apply, smul_apply, smul_eq_mul]

private theorem hrot_eval (d : LekiliFoldData) (v : EuclideanSpace ℝ (Fin 4)) :
    d.rotWCLM (lekiliMove1FDerivCLM d.s d.p v) =
      ![4 * d.s * d.C * (d.α * v 0 - d.β * v 1),
        -4 * d.s * d.S * (d.α * v 0 - d.β * v 1)] := by
  have hs_add : d.s * (d.α ^ 2 - d.β ^ 2) + d.s = 2 * d.s * d.α ^ 2 := by
    calc
      d.s * (d.α ^ 2 - d.β ^ 2) + d.s =
          d.s * (d.α ^ 2 - d.β ^ 2) + d.s * (d.α ^ 2 + d.β ^ 2) := by rw [d.hab1, mul_one]
      _ = 2 * d.s * d.α ^ 2 := by ring
  have hs_sub : d.s * (d.α ^ 2 - d.β ^ 2) - d.s = -2 * d.s * d.β ^ 2 := by
    calc
      d.s * (d.α ^ 2 - d.β ^ 2) - d.s =
          d.s * (d.α ^ 2 - d.β ^ 2) - d.s * (d.α ^ 2 + d.β ^ 2) := by rw [d.hab1, mul_one]
      _ = -2 * d.s * d.β ^ 2 := by ring
  have heq0 : (d.rotWCLM (lekiliMove1FDerivCLM d.s d.p v)) 0 =
      4 * d.s * d.C * (d.α * v 0 - d.β * v 1) := by
    rw [d.hrot0]
    dsimp only [a, b]
    simp only [lekiliMove1FDerivCLM_apply, vec2_zero, vec2_one, d.hp2, d.hp3, mul_zero]
    rw [← d.hab_re, ← d.hab_im, d.hp0_eq, d.hp1_eq, d.hC_eq, hs_add, hs_sub]
    ring
  have heq1 : (d.rotWCLM (lekiliMove1FDerivCLM d.s d.p v)) 1 =
      -4 * d.s * d.S * (d.α * v 0 - d.β * v 1) := by
    rw [d.hrot1]
    dsimp only [a, b]
    simp only [lekiliMove1FDerivCLM_apply, vec2_zero, vec2_one, d.hp2, d.hp3, mul_zero]
    rw [← d.hab_re, ← d.hab_im, d.hp0_eq, d.hp1_eq, d.hS_eq, hs_add, hs_sub]
    ring
  funext i
  fin_cases i
  · exact heq0
  · exact heq1

private theorem hW1_der (d : LekiliFoldData) :
    HasFDerivAt (fun q ↦ (d.wShift (lekiliMove1 d.s q)) 1)
      ((-4 * d.s * d.S * d.α) • euclidProj (0 : Fin 4) -
        (-4 * d.s * d.S * d.β) • euclidProj (1 : Fin 4)) d.p := by
  have h1 : HasFDerivAt (fun w ↦ (d.wShift w) 1)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1).comp d.rotWCLM)
      (lekiliMove1 d.s d.p) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1).hasFDerivAt).comp
      (lekiliMove1 d.s d.p) (d.hwShift_fderiv (lekiliMove1 d.s d.p))
  refine (h1.comp d.p (hasFDerivAt_lekiliMove1 d.s d.p)).congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    sub_apply, smul_apply, smul_eq_mul, d.hrot_eval,
    Matrix.cons_val_one, Matrix.cons_val_zero, euclidProj, EuclideanSpace.proj, PiLp.proj_apply]
  ring

private theorem hc1_p_der (d : LekiliFoldData) :
    HasFDerivAt (fun q ↦ d.c 1 (d.wShift (lekiliMove1 d.s q)))
      ((2 * d.kₓ * d.α) • euclidProj (0 : Fin 4) -
        (2 * d.kₓ * d.β) • euclidProj (1 : Fin 4)) d.p := by
  have h1 := d.hc_w_hasFDeriv 1 (lekiliMove1 d.s d.p) d.hfp_tgt
  rw [d.hwShift_p] at h1
  refine (h1.comp d.p (hasFDerivAt_lekiliMove1 d.s d.p)).congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.comp_apply, d.hrot_eval, sub_apply,
    smul_apply, smul_eq_mul]
  have hlin : (fderiv ℝ (d.c 1) 0) ![4 * d.s * d.C * (d.α * v 0 - d.β * v 1),
      -4 * d.s * d.S * (d.α * v 0 - d.β * v 1)] =
      (d.α * v 0 - d.β * v 1) * (fderiv ℝ (d.c 1) 0) ![4 * d.s * d.C, -4 * d.s * d.S] := by
    have hsm : ![4 * d.s * d.C * (d.α * v 0 - d.β * v 1),
          -4 * d.s * d.S * (d.α * v 0 - d.β * v 1)] =
        (d.α * v 0 - d.β * v 1) • ![4 * d.s * d.C, -4 * d.s * d.S] := by
      funext i
      fin_cases i
      · change 4 * d.s * d.C * (d.α * v 0 - d.β * v 1) =
          (d.α * v 0 - d.β * v 1) * (4 * d.s * d.C); ring
      · change -4 * d.s * d.S * (d.α * v 0 - d.β * v 1) =
          (d.α * v 0 - d.β * v 1) * (-4 * d.s * d.S); ring
    rw [hsm, map_smul, smul_eq_mul]
  rw [hlin]
  dsimp only [kₓ]
  simp only [euclidProj, EuclideanSpace.proj, PiLp.proj_apply]
  ring

private theorem hWp1 (d : LekiliFoldData) :
    (d.wShift (lekiliMove1 d.s d.p)) 1 = 0 := by rw [d.hwShift_p]; rfl

private theorem hEp (d : LekiliFoldData) :
    d.EFn (d.YFn d.p) = -4 * d.s * d.S := by dsimp only [EFn]; rw [d.hYp]; ring

private theorem hAp (d : LekiliFoldData) : d.AFn d.p = 1 := by
  dsimp only [AFn]; rw [d.hvp]; norm_num

private theorem hbp (d : LekiliFoldData) : d.bFn d.p = -d.CdivS := by
  simp only [bFn, MFn, denQFn, d.hWp1, d.hvp, d.hEp]
  dsimp only [CdivS]
  field_simp [d.hs_ne, d.hS_ne]
  ring

private theorem hBp (d : LekiliFoldData) : d.BFn d.p = 1 + d.CdivS ^ 2 := by
  simp only [BFn, MFn, denQFn, d.hWp1, d.hvp, d.hEp]
  dsimp only [CdivS]
  field_simp [d.hs_ne, d.hS_ne]
  ring

private theorem hinv_p (d : LekiliFoldData) : d.invSqrtU d.p = 1 := by
  dsimp only [invSqrtU, uplus]
  rw [d.hwShift_p, d.hYp, d.hu_val]
  norm_num

private theorem hUtilde_p (d : LekiliFoldData) : d.Utilde d.p = 0 := by
  dsimp only [Utilde]; rw [d.hup, d.hvp]; ring

private theorem hVtilde_p (d : LekiliFoldData) : d.Vtilde d.p = 0 := by
  dsimp only [Vtilde]; rw [d.hvp]; ring

private theorem hinv_diffAt (d : LekiliFoldData) : DifferentiableAt ℝ d.invSqrtU d.p :=
  (d.hinv_cd.contDiffAt (d.hU_dom_open.mem_nhds d.hp_dom)).differentiableAt (by simp)

private theorem hUtilde_der (d : LekiliFoldData) :
    HasFDerivAt d.Utilde
      ((d.α • euclidProj (2 : Fin 4) - d.β • euclidProj (3 : Fin 4)) +
        d.CdivS • (d.β • euclidProj (2 : Fin 4) + d.α • euclidProj (3 : Fin 4))) d.p := by
  have hA_diffAt : DifferentiableAt ℝ (fun q ↦ Real.sqrt (d.AFn q)) d.p :=
    ((d.hA_cd.sqrt fun _ hq ↦ (d.hA_pos hq).ne').contDiffAt
      (d.hU_dom_open.mem_nhds d.hp_dom)).differentiableAt (by simp)
  have hb_diffAt : DifferentiableAt ℝ d.bFn d.p :=
    (d.hb_cd.contDiffAt (d.hU_dom_open.mem_nhds d.hp_dom)).differentiableAt (by simp)
  have hbv : HasFDerivAt (fun q ↦ d.bFn q * d.vFn q)
      ((-d.CdivS) • (d.β • euclidProj (2 : Fin 4) + d.α • euclidProj (3 : Fin 4))) d.p := by
    refine (hb_diffAt.hasFDerivAt.mul d.hv_der).congr_fderiv ?_
    ext v
    simp only [add_apply, smul_apply, smul_eq_mul,
      d.hvp, d.hbp, zero_mul, add_zero]
  have hsub : HasFDerivAt (fun q ↦ d.uFn q - d.bFn q * d.vFn q)
      ((d.α • euclidProj (2 : Fin 4) - d.β • euclidProj (3 : Fin 4)) +
        d.CdivS • (d.β • euclidProj (2 : Fin 4) + d.α • euclidProj (3 : Fin 4))) d.p :=
    (d.hu_der.sub hbv).congr_fderiv (by
      ext v
      simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
      ring)
  refine (hA_diffAt.hasFDerivAt.mul hsub).congr_fderiv ?_
  ext v
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul, d.hAp, d.hup, d.hvp, mul_zero,
    sub_self, Real.sqrt_one, one_mul, zero_mul, add_zero]

private theorem hPhi0_der (d : LekiliFoldData) :
    HasFDerivAt (fun q ↦ d.Utilde q * d.invSqrtU q)
      ((d.α • euclidProj (2 : Fin 4) - d.β • euclidProj (3 : Fin 4)) +
        d.CdivS • (d.β • euclidProj (2 : Fin 4) + d.α • euclidProj (3 : Fin 4))) d.p := by
  refine (d.hUtilde_der.mul d.hinv_diffAt.hasFDerivAt).congr_fderiv ?_
  ext v
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul, d.hUtilde_p, d.hinv_p, one_mul,
    zero_mul, zero_add]

private theorem hPhi1_der (d : LekiliFoldData) :
    HasFDerivAt (fun q ↦ Real.sqrt 2 * (d.YFn q + d.c 1 (d.wShift (lekiliMove1 d.s q)) / 2))
      (Real.sqrt 2 • ((d.β • euclidProj (0 : Fin 4) + d.α • euclidProj (1 : Fin 4)) +
        d.kₓ • (d.α • euclidProj (0 : Fin 4) - d.β • euclidProj (1 : Fin 4)))) d.p := by
  have hc1_half : HasFDerivAt (fun q ↦ d.c 1 (d.wShift (lekiliMove1 d.s q)) / 2)
      ((d.kₓ * d.α) • euclidProj (0 : Fin 4) - (d.kₓ * d.β) • euclidProj (1 : Fin 4)) d.p := by
    have heq_h : (fun q ↦ d.c 1 (d.wShift (lekiliMove1 d.s q)) / 2) =
        fun q ↦ d.c 1 (d.wShift (lekiliMove1 d.s q)) * (1 / 2 : ℝ) := by funext q; ring
    rw [heq_h]
    refine (d.hc1_p_der.mul_const (1 / 2 : ℝ)).congr_fderiv ?_
    ext v
    simp only [smul_apply, sub_apply, smul_eq_mul]
    ring
  refine ((d.hY_der.add hc1_half).const_mul (Real.sqrt 2)).congr_fderiv ?_
  ext v
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
  ring

private theorem hPhi2_der (d : LekiliFoldData) :
    HasFDerivAt (fun q ↦ Real.sqrt 2 * d.Vtilde q * d.invSqrtU q)
      ((Real.sqrt 2 * d.rB) • (d.β • euclidProj (2 : Fin 4) + d.α • euclidProj (3 : Fin 4)))
      d.p := by
  have hB_diffAt : DifferentiableAt ℝ (fun q ↦ Real.sqrt (d.BFn q)) d.p :=
    ((d.hB_cd.sqrt fun _ hq ↦ (d.hB_pos hq).ne').contDiffAt
      (d.hU_dom_open.mem_nhds d.hp_dom)).differentiableAt (by simp)
  have hVtilde_der : HasFDerivAt d.Vtilde
      (d.rB • (d.β • euclidProj (2 : Fin 4) + d.α • euclidProj (3 : Fin 4))) d.p := by
    refine (hB_diffAt.hasFDerivAt.mul d.hv_der).congr_fderiv ?_
    ext v
    simp only [add_apply, smul_apply, smul_eq_mul, d.hvp, zero_mul, add_zero, rB, d.hBp]
  have hmul : HasFDerivAt (fun q ↦ Real.sqrt 2 * d.Vtilde q)
      ((Real.sqrt 2 * d.rB) • (d.β • euclidProj (2 : Fin 4) + d.α • euclidProj (3 : Fin 4)))
      d.p :=
    (hVtilde_der.const_mul (Real.sqrt 2)).congr_fderiv
      (by ext v; simp only [smul_apply, smul_eq_mul]; ring)
  refine (hmul.mul d.hinv_diffAt.hasFDerivAt).congr_fderiv ?_
  ext v
  simp only [add_apply, smul_apply, smul_eq_mul, d.hVtilde_p, d.hinv_p, mul_zero, one_mul,
    zero_mul, zero_add]

private theorem heΦ (d : LekiliFoldData) :
    (d.eΦ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) = fderiv ℝ d.Φ d.p := by
  have hfΦ : HasFDerivAt d.Φ _ d.p :=
    hasFDerivAt_vec4' d.hPhi0_der d.hPhi1_der d.hPhi2_der d.hW1_der
  rw [hfΦ.fderiv]
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [ContinuousLinearEquiv.coe_coe, heΦ_apply]
  refine ext_vec4 ?_ ?_ ?_ ?_
  · simp only [vec4_zero, clmVec4_apply, add_apply, sub_apply, smul_apply, euclidProj,
      EuclideanSpace.proj, PiLp.proj_apply, smul_eq_mul]
  · simp only [vec4_one, clmVec4_apply, add_apply, sub_apply, smul_apply, euclidProj,
      EuclideanSpace.proj, PiLp.proj_apply, smul_eq_mul]
  · simp only [vec4_two, clmVec4_apply, add_apply, smul_apply, euclidProj,
      EuclideanSpace.proj, PiLp.proj_apply, smul_eq_mul]
  · simp only [vec4_three, clmVec4_apply, sub_apply, smul_apply, euclidProj,
      EuclideanSpace.proj, PiLp.proj_apply, smul_eq_mul]
    ring

private theorem hΦ_p (d : LekiliFoldData) : d.Φ d.p = 0 := by
  refine ext_vec4 ?_ ?_ ?_ ?_
  · change d.Utilde d.p * d.invSqrtU d.p = 0
    rw [d.hUtilde_p, zero_mul]
  · change Real.sqrt 2 * (d.YFn d.p + d.c 1 (d.wShift (lekiliMove1 d.s d.p)) / 2) = 0
    rw [d.hYp, d.hwShift_p, d.hc0 1]; ring
  · change Real.sqrt 2 * d.Vtilde d.p * d.invSqrtU d.p = 0
    rw [d.hVtilde_p, mul_zero, zero_mul]
  · change (d.wShift (lekiliMove1 d.s d.p)) 1 = 0
    exact d.hWp1

private theorem hΨ_fp (d : LekiliFoldData) :
    d.Ψ (lekiliMove1 d.s d.p) = indefiniteFoldMap 0 := by
  have hind0 : indefiniteFoldMap (0 : EuclideanSpace ℝ (Fin 4)) = vec2 0 0 := by
    refine ext_vec2 ?_ ?_
    · simp only [indefiniteFoldMap, vec2_zero, PiLp.zero_apply]; norm_num
    · simp only [indefiniteFoldMap, vec2_one, PiLp.zero_apply]
  rw [hind0]
  refine ext_vec2 ?_ ?_
  · simp only [Ψ, d.hwShift_p, d.hc0 0, d.hc0 1, vec2_zero]; ring
  · simp only [Ψ, d.hwShift_p, Pi.zero_apply, vec2_one]

private theorem heq_on_nhds (d : LekiliFoldData) :
    ∀ᶠ q in 𝓝 d.p,
      lekiliMove1 d.s q ∈ d.U_tgt ∧ d.Ψ (lekiliMove1 d.s q) = indefiniteFoldMap (d.Φ q) := by
  have hG_at : ∀ᶠ q in 𝓝 d.p,
      4 * d.s * d.C * (d.wShift (lekiliMove1 d.s q)) 1 / d.EFn (d.YFn q) +
          (d.wShift (lekiliMove1 d.s q)) 1 ^ 2 / d.EFn (d.YFn q) ^ 2 - d.YFn q ^ 2 -
          (d.wShift (lekiliMove1 d.s q)) 0 =
        (d.YFn q ^ 2 + d.c 1 (d.wShift (lekiliMove1 d.s q)) * d.YFn q +
            d.c 0 (d.wShift (lekiliMove1 d.s q))) *
          (-d.uplus (d.wShift (lekiliMove1 d.s q), d.YFn q)) := by
    have hcont : ContinuousAt (fun q ↦ (d.wShift (lekiliMove1 d.s q), d.YFn q)) d.p :=
      ((d.hwShift_diff.continuous.comp (contDiff_lekiliMove1 d.s).continuous).prodMk
        d.hY_cd.continuous).continuousAt
    have hp0 : (d.wShift (lekiliMove1 d.s d.p), d.YFn d.p) = (0, 0) :=
      Prod.ext d.hwShift_p d.hYp
    filter_upwards [hcont.tendsto.eventually (hp0 ▸ d.heq_wp)] with q hq
    simpa only [uplus, EFn, neg_neg] using hq
  filter_upwards [d.hU_dom_open.mem_nhds d.hp_dom, hG_at] with q hq hG
  refine ⟨hq.1, ?_⟩
  have hE_ne : d.EFn (d.YFn q) ≠ 0 := hq.2.2.2
  have hdenQ_ne : d.denQFn q ≠ 0 := (d.hdenQ_pos hq).ne'
  have huplus_pos : 0 < d.uplus (d.wShift (lekiliMove1 d.s q), d.YFn q) := hq.2.2.1
  let Δ₀ := q 0 - d.p 0
  let Δ₁ := q 1 - d.p 1
  have hd0 : lekiliMove1 d.s q 0 - lekiliMove1 d.s d.p 0 =
      4 * d.s * d.α ^ 2 * Δ₀ - 4 * d.s * d.α * d.β * Δ₁ + Δ₀ ^ 2 - Δ₁ ^ 2 +
        q 2 ^ 2 - q 3 ^ 2 := by
    simp only [lekiliMove1_apply_zero, d.hp2, d.hp3]
    dsimp only [Δ₀, Δ₁]
    rw [d.hp0_eq, d.hp1_eq]
    linear_combination (2 * d.s * (q 0 - d.s * (d.α ^ 2 - d.β ^ 2))) * (-d.hab1)
  have hd1 : lekiliMove1 d.s q 1 - lekiliMove1 d.s d.p 1 =
      4 * d.s * d.α * d.β * Δ₀ - 4 * d.s * d.β ^ 2 * Δ₁ + 2 * Δ₀ * Δ₁ +
        2 * q 2 * q 3 := by
    simp only [lekiliMove1_apply_one, d.hp2, d.hp3]
    dsimp only [Δ₀, Δ₁]
    rw [d.hp0_eq, d.hp1_eq]
    linear_combination (2 * d.s * (q 1 - 2 * d.s * d.α * d.β)) * d.hab1
  have hw_rot_0 : (d.wShift (lekiliMove1 d.s q)) 0 =
      4 * d.s * d.C * d.XFn q + d.XFn q ^ 2 - d.YFn q ^ 2 + d.uFn q ^ 2 - d.vFn q ^ 2 := by
    rw [d.hwShift0, hd0, hd1]
    dsimp only [a, b, XFn, YFn, uFn, vFn, Δ₀, Δ₁]
    rw [← d.hab_re, ← d.hab_im, d.hC_eq]
    ring
  have hw_rot_1 : (d.wShift (lekiliMove1 d.s q)) 1 =
      d.EFn (d.YFn q) * d.XFn q + 2 * d.uFn q * d.vFn q := by
    rw [d.hwShift1, hd0, hd1]
    dsimp only [a, b, EFn, XFn, YFn, uFn, vFn, Δ₀, Δ₁]
    rw [← d.hab_re, ← d.hab_im, d.hS_eq]
    ring
  have hX_eq : d.XFn q =
      ((d.wShift (lekiliMove1 d.s q)) 1 - 2 * d.uFn q * d.vFn q) / d.EFn (d.YFn q) := by
    rw [eq_div_iff hE_ne]
    linear_combination -hw_rot_1
  have hdec : d.Utilde q ^ 2 - d.Vtilde q ^ 2 =
      (d.wShift (lekiliMove1 d.s q)) 0 -
        (4 * d.s * d.C * (d.wShift (lekiliMove1 d.s q)) 1 / d.EFn (d.YFn q) +
          (d.wShift (lekiliMove1 d.s q)) 1 ^ 2 / d.EFn (d.YFn q) ^ 2 - d.YFn q ^ 2) := by
    dsimp only [Utilde, Vtilde]
    rw [mul_pow, mul_pow, Real.sq_sqrt (d.hA_pos hq).le, Real.sq_sqrt (d.hB_pos hq).le]
    dsimp only [AFn, bFn, BFn, MFn, denQFn]
    rw [hw_rot_0, hX_eq]
    field_simp [hE_ne, hdenQ_ne]
    ring
  have hinv_sq : d.invSqrtU q ^ 2 = (d.uplus (d.wShift (lekiliMove1 d.s q), d.YFn q))⁻¹ := by
    dsimp only [invSqrtU]
    rw [inv_pow, Real.sq_sqrt huplus_pos.le]
  have hψ0 :
      d.c 0 (d.wShift (lekiliMove1 d.s q)) - d.c 1 (d.wShift (lekiliMove1 d.s q)) ^ 2 / 4 =
        (d.Utilde q * d.invSqrtU q) ^ 2 -
          ((Real.sqrt 2 * (d.YFn q + d.c 1 (d.wShift (lekiliMove1 d.s q)) / 2)) ^ 2 +
            (Real.sqrt 2 * d.Vtilde q * d.invSqrtU q) ^ 2) / 2 := by
    have h1 :
        ((d.YFn q + d.c 1 (d.wShift (lekiliMove1 d.s q)) / 2) ^ 2 +
            (d.c 0 (d.wShift (lekiliMove1 d.s q)) -
              d.c 1 (d.wShift (lekiliMove1 d.s q)) ^ 2 / 4)) *
            d.uplus (d.wShift (lekiliMove1 d.s q), d.YFn q) =
          d.Utilde q ^ 2 - d.Vtilde q ^ 2 := by
      calc
        ((d.YFn q + d.c 1 (d.wShift (lekiliMove1 d.s q)) / 2) ^ 2 +
            (d.c 0 (d.wShift (lekiliMove1 d.s q)) -
              d.c 1 (d.wShift (lekiliMove1 d.s q)) ^ 2 / 4)) *
            d.uplus (d.wShift (lekiliMove1 d.s q), d.YFn q)
          = -((d.YFn q ^ 2 + d.c 1 (d.wShift (lekiliMove1 d.s q)) * d.YFn q +
              d.c 0 (d.wShift (lekiliMove1 d.s q))) *
              (-d.uplus (d.wShift (lekiliMove1 d.s q), d.YFn q))) := by ring
        _ = -(4 * d.s * d.C * (d.wShift (lekiliMove1 d.s q)) 1 / d.EFn (d.YFn q) +
              (d.wShift (lekiliMove1 d.s q)) 1 ^ 2 / d.EFn (d.YFn q) ^ 2 - d.YFn q ^ 2 -
              (d.wShift (lekiliMove1 d.s q)) 0) := by rw [hG]
        _ = d.Utilde q ^ 2 - d.Vtilde q ^ 2 := by rw [hdec]; ring
    have h2 :
        (d.YFn q + d.c 1 (d.wShift (lekiliMove1 d.s q)) / 2) ^ 2 +
            (d.c 0 (d.wShift (lekiliMove1 d.s q)) -
              d.c 1 (d.wShift (lekiliMove1 d.s q)) ^ 2 / 4) =
          (d.Utilde q ^ 2 - d.Vtilde q ^ 2) * d.invSqrtU q ^ 2 := by
      rw [hinv_sq, ← div_eq_mul_inv, eq_div_iff huplus_pos.ne']
      exact h1
    change d.c 0 (d.wShift (lekiliMove1 d.s q)) -
        d.c 1 (d.wShift (lekiliMove1 d.s q)) ^ 2 / 4 = _
    simp only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    linear_combination h2
  refine ext_vec2 ?_ rfl
  change d.c 0 (d.wShift (lekiliMove1 d.s q)) -
      d.c 1 (d.wShift (lekiliMove1 d.s q)) ^ 2 / 4 = _
  simp only [indefiniteFoldMap, Φ, vec4_zero, vec4_one, vec4_two]
  exact hψ0

end LekiliFoldData

/-- For `s > 0`, every non-cusp critical point `p` (`p₀³ - 3 p₀ p₁² ≠ s³`) of `lekiliMove1 s` is
locally modeled on `indefiniteFoldMap` (`IsIndefiniteFoldAt`). -/
private theorem isIndefiniteFoldAt_lekiliMove1_pos {s : ℝ} (hs : 0 < s)
    {p : EuclideanSpace ℝ (Fin 4)}
    (hp : p ∈ criticalPoints (𝓡 4) (𝓡 2) (lekiliMove1 s))
    (hnc : p 0 ^ 3 - 3 * p 0 * p 1 ^ 2 ≠ s ^ 3) :
    IsIndefiniteFoldAt (𝓡 4) (𝓡 2) (lekiliMove1 s) p := by
  rw [criticalPoints_lekiliMove1, Set.mem_ofPred_eq] at hp
  obtain ⟨h01, hp2, hp3⟩ := hp
  obtain ⟨α, β, C, S, hab1, hab_re, hab_im, hC_eq, hS_eq, _, hS_ne⟩ :=
    exists_half_angle_params hs h01 hnc
  obtain ⟨c, u, hc_an, hc0, hu_an, hu_val, heq_wp, hc0_fderiv⟩ :=
    lekiliMove1_fold_weierstrass hs hS_ne (C := C)
  obtain ⟨U_c, hU_c_sub, hU_c_open, h0_Uc⟩ := _root_.eventually_nhds_iff.mp
    ((hc_an 0).eventually_analyticAt.and (hc_an 1).eventually_analyticAt)
  obtain ⟨U_u, hU_u_sub, hU_u_open, h0_Uu⟩ := _root_.eventually_nhds_iff.mp
    hu_an.eventually_analyticAt
  let d : LekiliFoldData :=
    { s, hs, p, h01, hp2, hp3, α, β, C, S, hab1, hab_re, hab_im, hC_eq, hS_eq, hS_ne,
      c, u, hc_an, hc0, hu_an, hu_val, heq_wp, hc0_fderiv, U_c, hU_c_sub, hU_c_open, h0_Uc,
      U_u, hU_u_sub, hU_u_open, h0_Uu }
  exact isLocallyModeledOn_of_contDiff_maps d.hU_dom_open d.hp_dom d.hU_tgt_open d.hfp_tgt
    d.hΦ_diff d.hΨ_diff d.eΦ d.heΦ d.eΨ d.heΨ d.hΦ_p d.hΨ_fp d.heq_on_nhds
    (contDiff_lekiliMove1 s).continuous.continuousAt

/-- For every `s ≠ 0`, every non-cusp critical point `p` (`p₀³ - 3 p₀ p₁² ≠ s³`) of
`lekiliMove1 s` is locally modeled on `indefiniteFoldMap` (`IsIndefiniteFoldAt`). -/
-- tier: T2
theorem isIndefiniteFoldAt_lekiliMove1 {s : ℝ} (hs : s ≠ 0) {p : EuclideanSpace ℝ (Fin 4)}
    (hp : p ∈ criticalPoints (𝓡 4) (𝓡 2) (lekiliMove1 s))
    (hnc : p 0 ^ 3 - 3 * p 0 * p 1 ^ 2 ≠ s ^ 3) :
    IsIndefiniteFoldAt (𝓡 4) (𝓡 2) (lekiliMove1 s) p := by
  rcases lt_or_gt_of_ne hs with hneg | hpos
  · have ht : 0 < -s := neg_pos.mpr hneg
    have hcrit : flipSignDom p ∈ criticalPoints (𝓡 4) (𝓡 2) (lekiliMove1 (-s)) := by
      rw [criticalPoints_lekiliMove1, Set.mem_ofPred_eq] at hp ⊢
      simp only [flipSignDom_apply, vec4_zero, vec4_one, vec4_two, vec4_three]
      exact ⟨by linear_combination hp.1, hp.2.1, hp.2.2⟩
    have hnc' : (flipSignDom p) 0 ^ 3 - 3 * (flipSignDom p) 0 * (flipSignDom p) 1 ^ 2 ≠
        (-s) ^ 3 := by
      simp only [flipSignDom_apply, vec4_zero, vec4_one]
      intro heq
      exact hnc (by linear_combination -heq)
    have hbase : IsLocallyModeledOn (𝓡 4) (𝓡 2) (lekiliMove1 (-s)) (flipSignDom p)
        indefiniteFoldMap 0 :=
      isIndefiniteFoldAt_lekiliMove1_pos ht hcrit hnc'
    change IsLocallyModeledOn (𝓡 4) (𝓡 2) (lekiliMove1 s) p indefiniteFoldMap 0
    exact isLocallyModeledOn_comp_equiv flipSignDom (ContinuousLinearEquiv.refl ℝ EuclideanPlane)
      (fun q ↦ by rw [ContinuousLinearEquiv.refl_apply, lekiliMove1_flipSignDom, neg_neg]) hbase
  · exact isIndefiniteFoldAt_lekiliMove1_pos hpos hp hnc

/-- The opposite critical point `lekiliMove1CritCurve s Real.pi` (`(-s, 0, 0, 0)`) of
`lekiliMove1 s` is an indefinite quadratic fold for all `s ≠ 0` (Gate G5.2 witness). -/
-- tier: T2
theorem isIndefiniteFoldAt_lekiliMove1_pi {s : ℝ} (hs : s ≠ 0) :
    IsIndefiniteFoldAt (𝓡 4) (𝓡 2) (lekiliMove1 s) (lekiliMove1CritCurve s Real.pi) := by
  refine isIndefiniteFoldAt_lekiliMove1 hs (lekiliMove1CritCurve_mem_criticalPoints s Real.pi) ?_
  simp only [lekiliMove1CritCurve, Real.cos_pi, Real.sin_pi, vec4_zero, vec4_one, mul_neg, mul_one,
    mul_zero]
  intro heq
  have hs3 : s ^ 3 = 0 := by linear_combination -(1 / 2 : ℝ) * heq
  exact pow_ne_zero 3 hs hs3

/-- Complete singularity classification of `lekiliMove1 s` for `s ≠ 0`: every critical point is
either an indefinite quadratic fold (`IsIndefiniteFoldAt`) or one of the three wrinkled cusps
(`IsWrinkledCuspAt`). -/
-- tier: T2
theorem singularities_lekiliMove1 {s : ℝ} (hs : s ≠ 0) :
    ∀ p ∈ criticalPoints (𝓡 4) (𝓡 2) (lekiliMove1 s),
      IsIndefiniteFoldAt (𝓡 4) (𝓡 2) (lekiliMove1 s) p ∨
        IsWrinkledCuspAt (𝓡 4) (𝓡 2) (lekiliMove1 s) p := by
  intro p hp
  by_cases hcusp : p 0 ^ 3 - 3 * p 0 * p 1 ^ 2 = s ^ 3
  · exact Or.inr (isWrinkledCuspAt_lekiliMove1 hs hp hcusp)
  · exact Or.inl (isIndefiniteFoldAt_lekiliMove1 hs hp hcusp)

end Move1Singularities




/-! ## 3. Lekili Moves 2, 3, and 4 (Birth, Cusp-Merge, and Swallowtail Flip) -/

section Moves234

/-- **Lekili Move 2 (Birth / Death of a 2-Cusp Wrinkled Component)**:
`(t, x₁, x₂, x₃) ↦ (t, x₁³ + 3(t² - s) x₁ + x₂² - x₃²)`. Empty critical locus for `s < 0`,
single critical point `{0}` for `s = 0`, and circle `{p | p₀² + p₁² = s ∧ p₂ = p₃ = 0}` for
`s > 0` with two wrinkled cusps at `(±√s, 0, 0, 0)`. -/
-- tier: T2
noncomputable def lekiliMove2 (s : ℝ) (p : EuclideanSpace ℝ (Fin 4)) : EuclideanPlane :=
  vec2 (p 0) (p 1 ^ 3 + 3 * (p 0 ^ 2 - s) * p 1 + p 2 ^ 2 - p 3 ^ 2)

/-- Smoothness (`ContDiff ℝ ∞`) of `lekiliMove2 s`. -/
theorem contDiff_lekiliMove2 (s : ℝ) : ContDiff ℝ ∞ (lekiliMove2 s) := by
  have hp (i : Fin 4) : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 4) ↦ p i) :=
    (euclidProj i).contDiff
  exact contDiff_vec2 (hp 0)
    (((((hp 1).pow 3).add ((contDiff_const.mul (((hp 0).pow 2).sub contDiff_const)).mul (hp 1))).add
      ((hp 2).pow 2)).sub ((hp 3).pow 2))

/-- Manifold smoothness of `lekiliMove2 s`. -/
-- tier: T2
theorem contMDiff_lekiliMove2 (s : ℝ) : ContMDiff (𝓡 4) (𝓡 2) ∞ (lekiliMove2 s) :=
  (contDiff_lekiliMove2 s).contMDiff

/-- Continuous linear map representing `fderiv ℝ (lekiliMove2 s) p`. -/
noncomputable def lekiliMove2FDerivCLM (s : ℝ) (p : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanPlane :=
  clmVec2
    (euclidProj (0 : Fin 4))
    ((6 * p 0 * p 1) • euclidProj (0 : Fin 4) +
      (3 * (p 1 ^ 2 + p 0 ^ 2 - s)) • euclidProj (1 : Fin 4) +
      (2 * p 2) • euclidProj (2 : Fin 4) -
      (2 * p 3) • euclidProj (3 : Fin 4))

@[simp]
theorem lekiliMove2FDerivCLM_apply (s : ℝ) (p v : EuclideanSpace ℝ (Fin 4)) :
    lekiliMove2FDerivCLM s p v =
      vec2 (v 0) (6 * p 0 * p 1 * v 0 + 3 * (p 1 ^ 2 + p 0 ^ 2 - s) * v 1 +
        2 * p 2 * v 2 - 2 * p 3 * v 3) := by
  simp [lekiliMove2FDerivCLM, euclidProj]

/-- Exact Fréchet derivative of `lekiliMove2 s` at `p`. -/
theorem hasFDerivAt_lekiliMove2 (s : ℝ) (p : EuclideanSpace ℝ (Fin 4)) :
    HasFDerivAt (lekiliMove2 s) (lekiliMove2FDerivCLM s p) p := by
  have hp (i : Fin 4) : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ x i)
      (euclidProj i) p :=
    (euclidProj i).hasFDerivAt
  have hsq (i : Fin 4) : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ x i ^ 2)
      ((2 * p i) • euclidProj i) p := by
    convert (hp i).pow 2 using 1
    ext v
    simp [smul_apply, euclidProj, nsmul_eq_mul, smul_eq_mul]
  have hcube : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ x 1 ^ 3)
      ((3 * p 1 ^ 2) • euclidProj (1 : Fin 4)) p := by
    convert (hp 1).pow 3 using 1
    ext v
    simp [smul_apply, euclidProj, nsmul_eq_mul, smul_eq_mul]
  have hmid : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ 3 * (x 0 ^ 2 - s) * x 1)
      ((6 * p 0 * p 1) • euclidProj (0 : Fin 4) +
        (3 * (p 0 ^ 2 - s)) • euclidProj (1 : Fin 4)) p := by
    refine ((((hsq 0).sub (hasFDerivAt_const s p)).const_mul (3 : ℝ)).mul (hp 1)).congr_fderiv ?_
    ext v
    simp only [add_apply, sub_apply, Pi.sub_apply, zero_apply, smul_apply, euclidProj,
      EuclideanSpace.proj, smul_eq_mul]
    ring
  have h1 : HasFDerivAt
      (fun x : EuclideanSpace ℝ (Fin 4) ↦ x 1 ^ 3 + 3 * (x 0 ^ 2 - s) * x 1 + x 2 ^ 2 - x 3 ^ 2)
      ((6 * p 0 * p 1) • euclidProj (0 : Fin 4) +
        (3 * (p 1 ^ 2 + p 0 ^ 2 - s)) • euclidProj (1 : Fin 4) +
        (2 * p 2) • euclidProj (2 : Fin 4) -
        (2 * p 3) • euclidProj (3 : Fin 4)) p := by
    convert (((hcube.add hmid).add (hsq 2)).sub (hsq 3)) using 1
    ext v
    simp only [add_apply, sub_apply, smul_apply, euclidProj, EuclideanSpace.proj, smul_eq_mul]
    ring
  exact hasFDerivAt_vec2 (hp 0) h1

/-- `fderiv ℝ (lekiliMove2 s) p = lekiliMove2FDerivCLM s p`. -/
@[simp]
theorem fderiv_lekiliMove2 (s : ℝ) (p : EuclideanSpace ℝ (Fin 4)) :
    fderiv ℝ (lekiliMove2 s) p = lekiliMove2FDerivCLM s p :=
  (hasFDerivAt_lekiliMove2 s p).fderiv

/-- Surjectivity characterization of `fderiv ℝ (lekiliMove2 s) p`. -/
theorem surjective_fderiv_lekiliMove2_iff (s : ℝ) (p : EuclideanSpace ℝ (Fin 4)) :
    Function.Surjective (fderiv ℝ (lekiliMove2 s) p) ↔
      ¬ (p 0 ^ 2 + p 1 ^ 2 = s ∧ p 2 = 0 ∧ p 3 = 0) := by
  rw [fderiv_lekiliMove2]
  constructor
  · rintro hsurj ⟨h01, hp2, hp3⟩
    obtain ⟨v, hv⟩ := hsurj (vec2 0 1)
    have hv0 := congrArg (fun u : EuclideanPlane ↦ u 0) hv
    have hv1 := congrArg (fun u : EuclideanPlane ↦ u 1) hv
    simp only [lekiliMove2FDerivCLM_apply, vec2_zero, vec2_one, hp2, hp3, mul_zero] at hv0 hv1
    have hcoeff : p 1 ^ 2 + p 0 ^ 2 - s = 0 := by linarith
    rw [hv0, hcoeff] at hv1
    linarith
  · intro hnot w
    by_cases h1 : p 1 ^ 2 + p 0 ^ 2 - s ≠ 0
    · refine ⟨vec4 (w 0)
          ((w 1 - 6 * p 0 * p 1 * w 0) / (3 * (p 1 ^ 2 + p 0 ^ 2 - s))) 0 0, ext_vec2 ?_ ?_⟩
      · simp
      · simp only [lekiliMove2FDerivCLM_apply, vec2_one, vec4_zero, vec4_one, vec4_two, vec4_three]
        field_simp [h1]
        ring
    · by_cases h2 : p 2 ≠ 0
      · refine ⟨vec4 (w 0) 0 ((w 1 - 6 * p 0 * p 1 * w 0) / (2 * p 2)) 0, ext_vec2 ?_ ?_⟩
        · simp
        · simp only [lekiliMove2FDerivCLM_apply, vec2_one, vec4_zero, vec4_one, vec4_two,
            vec4_three]
          field_simp [h2]
          ring
      · push Not at h1 h2
        have hp3 : p 3 ≠ 0 := by
          intro h3
          exact hnot ⟨by linarith, h2, h3⟩
        refine ⟨vec4 (w 0) 0 0 (-(w 1 - 6 * p 0 * p 1 * w 0) / (2 * p 3)), ext_vec2 ?_ ?_⟩
        · simp
        · simp only [lekiliMove2FDerivCLM_apply, vec2_one, vec4_zero, vec4_one, vec4_two,
            vec4_three]
          field_simp [hp3]
          ring

/-- Critical locus of `lekiliMove2 s` is empty when `s < 0`. -/
theorem criticalPoints_lekiliMove2_neg {s : ℝ} (hs : s < 0) :
    criticalPoints (𝓡 4) (𝓡 2) (lekiliMove2 s) = ∅ := by
  rw [criticalPoints_euclidean_eq]
  ext p
  simp only [mem_euclideanCriticalPoints_iff, surjective_fderiv_lekiliMove2_iff, not_not,
    Set.mem_empty_iff_false, iff_false]
  rintro ⟨h01, -, -⟩
  nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]

/-- Critical locus of `lekiliMove2 s` for `0 ≤ s`: `{p | p₀² + p₁² = s ∧ p₂ = 0 ∧ p₃ = 0}`. -/
-- tier: T2
theorem criticalPoints_lekiliMove2_nonneg {s : ℝ} (_hs : 0 ≤ s) :
    criticalPoints (𝓡 4) (𝓡 2) (lekiliMove2 s) =
      {p : EuclideanSpace ℝ (Fin 4) | p 0 ^ 2 + p 1 ^ 2 = s ∧ p 2 = 0 ∧ p 3 = 0} := by
  rw [criticalPoints_euclidean_eq]
  ext p
  rw [mem_euclideanCriticalPoints_iff, surjective_fderiv_lekiliMove2_iff, not_not,
    Set.mem_ofPred_eq]

/-- Closed-form `IsWrinkledCuspAt` at `(σ * √s, 0, 0, 0)` (`σ = ±1`, `0 < s`) for `lekiliMove2 s`.
-/
-- tier: T2
theorem isWrinkledCuspAt_lekiliMove2 {s σ : ℝ} (hs : 0 < s) (hσ : σ = 1 ∨ σ = -1) :
    IsWrinkledCuspAt (𝓡 4) (𝓡 2) (lekiliMove2 s) (vec4 (σ * Real.sqrt s) 0 0 0) := by
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσ_ne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hsqrt_ne : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  let p_star := vec4 (σ * Real.sqrt s) 0 0 0
  let Φ : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4) :=
    fun p ↦ vec4 (s - p 0 ^ 2) (p 1) (p 2) (p 3)
  let Ψ : EuclideanPlane → EuclideanPlane := fun w ↦ vec2 (s - w 0 ^ 2) (w 1)
  have hΦ_diff : ContDiff ℝ ∞ Φ := by
    have hp (i : Fin 4) : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 4) ↦ p i) :=
      (euclidProj i).contDiff
    exact contDiff_vec4 (contDiff_const.sub ((hp 0).pow 2)) (hp 1) (hp 2) (hp 3)
  have hΨ_diff : ContDiff ℝ ∞ Ψ := by
    have hw (i : Fin 2) : ContDiff ℝ ∞ (fun w : EuclideanPlane ↦ w i) :=
      (euclidProj i).contDiff
    exact contDiff_vec2 (contDiff_const.sub ((hw 0).pow 2)) (hw 1)
  let c₀ : ℝ := -2 * σ * Real.sqrt s
  have hc₀ : c₀ ≠ 0 := by simp [c₀, hσ_ne, hsqrt_ne]
  let eΦ : EuclideanSpace ℝ (Fin 4) ≃L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    { toFun := fun v ↦ vec4 (c₀ * v 0) (v 1) (v 2) (v 3)
      invFun := fun v ↦ vec4 (v 0 / c₀) (v 1) (v 2) (v 3)
      map_add' := fun u v ↦ by refine ext_vec4 ?_ ?_ ?_ ?_ <;> simp; ring
      map_smul' := fun r v ↦ by refine ext_vec4 ?_ ?_ ?_ ?_ <;> simp; ring
      left_inv := fun v ↦ by
        refine ext_vec4 ?_ ?_ ?_ ?_ <;> simp only [vec4_zero, vec4_one, vec4_two, vec4_three]
        field_simp [hc₀]
      right_inv := fun v ↦ by
        refine ext_vec4 ?_ ?_ ?_ ?_ <;> simp only [vec4_zero, vec4_one, vec4_two, vec4_three]
        field_simp [hc₀]
      continuous_toFun := continuous_vec4
        (continuous_const.mul (euclidProj 0).continuous)
        (euclidProj 1).continuous (euclidProj 2).continuous (euclidProj 3).continuous
      continuous_invFun := continuous_vec4
        ((euclidProj 0).continuous.div_const c₀)
        (euclidProj 1).continuous (euclidProj 2).continuous (euclidProj 3).continuous }
  let eΨ : EuclideanPlane ≃L[ℝ] EuclideanPlane :=
    { toFun := fun v ↦ vec2 (c₀ * v 0) (v 1)
      invFun := fun v ↦ vec2 (v 0 / c₀) (v 1)
      map_add' := fun u v ↦ by refine ext_vec2 ?_ ?_ <;> simp; ring
      map_smul' := fun r v ↦ by refine ext_vec2 ?_ ?_ <;> simp; ring
      left_inv := fun v ↦ by
        refine ext_vec2 ?_ ?_ <;> simp only [vec2_zero, vec2_one]
        field_simp [hc₀]
      right_inv := fun v ↦ by
        refine ext_vec2 ?_ ?_ <;> simp only [vec2_zero, vec2_one]
        field_simp [hc₀]
      continuous_toFun := continuous_vec2
        (continuous_const.mul (euclidProj 0).continuous) (euclidProj 1).continuous
      continuous_invFun := continuous_vec2
        ((euclidProj 0).continuous.div_const c₀) (euclidProj 1).continuous }
  have heΦ : (eΦ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) =
      fderiv ℝ Φ p_star := by
    have hp (i : Fin 4) : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ x i)
        (euclidProj i) p_star := (euclidProj i).hasFDerivAt
    have h0 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ s - x 0 ^ 2)
        (c₀ • euclidProj (0 : Fin 4)) p_star := by
      refine (((hp 0).pow 2).const_sub s).congr_fderiv ?_
      ext v
      simp only [c₀, p_star, euclidProj, EuclideanSpace.proj, PiLp.proj_apply, vec4_zero,
        nsmul_eq_mul, smul_eq_mul, neg_apply, smul_apply]
      ring
    have hder := hasFDerivAt_vec4' h0 (hp 1) (hp 2) (hp 3)
    rw [hder.fderiv]
    ext v i
    fin_cases i <;> simp [eΦ, euclidProj, smul_eq_mul]
  have heΨ : (eΨ : EuclideanPlane →L[ℝ] EuclideanPlane) =
      fderiv ℝ Ψ (lekiliMove2 s p_star) := by
    have hw (i : Fin 2) : HasFDerivAt (fun x : EuclideanPlane ↦ x i)
        (euclidProj i) (lekiliMove2 s p_star) := (euclidProj i).hasFDerivAt
    have h0 : HasFDerivAt (fun x : EuclideanPlane ↦ s - x 0 ^ 2)
        (c₀ • euclidProj (0 : Fin 2)) (lekiliMove2 s p_star) := by
      refine (((hw 0).pow 2).const_sub s).congr_fderiv ?_
      ext v
      simp only [c₀, p_star, lekiliMove2, euclidProj, EuclideanSpace.proj, PiLp.proj_apply,
        vec4_zero, vec4_one, vec4_two, vec4_three, vec2_zero, nsmul_eq_mul, smul_eq_mul,
        neg_apply, smul_apply]
      ring
    have hder := hasFDerivAt_vec2 h0 (hw 1)
    rw [hder.fderiv]
    ext v i
    fin_cases i <;> simp [eΨ, euclidProj, smul_eq_mul]
  have hΦ_p : Φ p_star = 0 := by
    refine ext_vec4 ?_ rfl rfl rfl
    simp only [Φ, p_star, vec4_zero, mul_pow, hσ2, one_mul, Real.sq_sqrt hs.le, sub_self,
      PiLp.zero_apply]
  have hΨ_fp : Ψ (lekiliMove2 s p_star) = wrinkledCuspMap 0 := by
    refine ext_vec2 ?_ ?_
    · simp only [Ψ, lekiliMove2, p_star, vec4_zero, vec2_zero, mul_pow, hσ2, one_mul,
        Real.sq_sqrt hs.le, sub_self, wrinkledCuspMap_apply_zero, PiLp.zero_apply]
    · simp [Ψ, lekiliMove2, p_star, wrinkledCuspMap]
  refine isLocallyModeledOn_of_contDiff_maps isOpen_univ trivial isOpen_univ trivial
    hΦ_diff.contDiffOn hΨ_diff.contDiffOn eΦ heΦ eΨ heΨ hΦ_p hΨ_fp ?_
    (contDiff_lekiliMove2 s).continuous.continuousAt
  refine Eventually.of_forall fun p ↦ ⟨trivial, ?_⟩
  refine ext_vec2 rfl ?_
  simp only [Ψ, Φ, lekiliMove2, wrinkledCuspMap, vec2_zero, vec2_one, vec4_zero, vec4_one,
    vec4_two, vec4_three]
  ring

private theorem isWrinkledCuspAt_cubicMinusThreeG
    {g : ℝ → ℝ} (hg_diff : ContDiff ℝ ∞ g) {t₀ : ℝ}
    (hg0 : g t₀ = 0) (hg'_ne : deriv g t₀ ≠ 0) :
    IsWrinkledCuspAt (𝓡 4) (𝓡 2)
      (fun p ↦ vec2 (p 0) (p 1 ^ 3 - 3 * g (p 0) * p 1 + p 2 ^ 2 - p 3 ^ 2))
      (vec4 t₀ 0 0 0) := by
  let p_star := vec4 t₀ 0 0 0
  let F : EuclideanSpace ℝ (Fin 4) → EuclideanPlane :=
    fun p ↦ vec2 (p 0) (p 1 ^ 3 - 3 * g (p 0) * p 1 + p 2 ^ 2 - p 3 ^ 2)
  have hF_diff : ContDiff ℝ ∞ F := by
    have hp (i : Fin 4) : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 4) ↦ p i) :=
      (euclidProj i).contDiff
    have hg0_diff : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 4) ↦ g (p 0)) :=
      hg_diff.comp (hp 0)
    exact contDiff_vec2 (hp 0)
      (((((hp 1).pow 3).sub ((contDiff_const.mul hg0_diff).mul (hp 1))).add
        ((hp 2).pow 2)).sub ((hp 3).pow 2))
  let Φ : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4) :=
    fun p ↦ vec4 (g (p 0)) (p 1) (p 2) (p 3)
  let Ψ : EuclideanPlane → EuclideanPlane := fun w ↦ vec2 (g (w 0)) (w 1)
  have hΦ_diff : ContDiff ℝ ∞ Φ := by
    have hp (i : Fin 4) : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 4) ↦ p i) :=
      (euclidProj i).contDiff
    exact contDiff_vec4 (hg_diff.comp (hp 0)) (hp 1) (hp 2) (hp 3)
  have hΨ_diff : ContDiff ℝ ∞ Ψ := by
    have hw (i : Fin 2) : ContDiff ℝ ∞ (fun w : EuclideanPlane ↦ w i) :=
      (euclidProj i).contDiff
    exact contDiff_vec2 (hg_diff.comp (hw 0)) (hw 1)
  let c₀ : ℝ := deriv g t₀
  let eΦ : EuclideanSpace ℝ (Fin 4) ≃L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    { toFun := fun v ↦ vec4 (c₀ * v 0) (v 1) (v 2) (v 3)
      invFun := fun v ↦ vec4 (v 0 / c₀) (v 1) (v 2) (v 3)
      map_add' := fun u v ↦ by refine ext_vec4 ?_ ?_ ?_ ?_ <;> simp; ring
      map_smul' := fun r v ↦ by refine ext_vec4 ?_ ?_ ?_ ?_ <;> simp; ring
      left_inv := fun v ↦ by
        refine ext_vec4 ?_ ?_ ?_ ?_ <;> simp only [vec4_zero, vec4_one, vec4_two, vec4_three];
        field_simp [hg'_ne, c₀]
      right_inv := fun v ↦ by
        refine ext_vec4 ?_ ?_ ?_ ?_ <;> simp only [vec4_zero, vec4_one, vec4_two, vec4_three];
        field_simp [hg'_ne, c₀]
      continuous_toFun := continuous_vec4
        (continuous_const.mul (euclidProj 0).continuous)
        (euclidProj 1).continuous (euclidProj 2).continuous (euclidProj 3).continuous
      continuous_invFun := continuous_vec4
        ((euclidProj 0).continuous.div_const c₀)
        (euclidProj 1).continuous (euclidProj 2).continuous (euclidProj 3).continuous }
  let eΨ : EuclideanPlane ≃L[ℝ] EuclideanPlane :=
    { toFun := fun v ↦ vec2 (c₀ * v 0) (v 1)
      invFun := fun v ↦ vec2 (v 0 / c₀) (v 1)
      map_add' := fun u v ↦ by refine ext_vec2 ?_ ?_ <;> simp; ring
      map_smul' := fun r v ↦ by refine ext_vec2 ?_ ?_ <;> simp; ring
      left_inv := fun v ↦ by
        refine ext_vec2 ?_ ?_ <;> simp only [vec2_zero, vec2_one];
        field_simp [hg'_ne, c₀]
      right_inv := fun v ↦ by
        refine ext_vec2 ?_ ?_ <;> simp only [vec2_zero, vec2_one];
        field_simp [hg'_ne, c₀]
      continuous_toFun := continuous_vec2
        (continuous_const.mul (euclidProj 0).continuous) (euclidProj 1).continuous
      continuous_invFun := continuous_vec2
        ((euclidProj 0).continuous.div_const c₀) (euclidProj 1).continuous }
  have hg_der : HasFDerivAt (fun x : ℝ ↦ g x) (c₀ • ContinuousLinearMap.id ℝ ℝ) t₀ := by
    refine (hg_diff.contDiffAt.differentiableAt (by simp)).hasDerivAt.hasFDerivAt.congr_fderiv ?_
    apply ContinuousLinearMap.ext_ring
    simp [c₀]
  have heΦ : (eΦ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) =
      fderiv ℝ Φ p_star := by
    have hp (i : Fin 4) : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ x i)
        (euclidProj i) p_star := (euclidProj i).hasFDerivAt
    have h0 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ g (x 0))
        (c₀ • euclidProj (0 : Fin 4)) p_star := by
      refine (hg_der.comp p_star (hp 0)).congr_fderiv ?_
      ext v
      simp [smul_apply]
    rw [(hasFDerivAt_vec4' h0 (hp 1) (hp 2) (hp 3)).fderiv]
    ext v i
    fin_cases i <;> simp [eΦ, euclidProj, smul_eq_mul]
  have heΨ : (eΨ : EuclideanPlane →L[ℝ] EuclideanPlane) = fderiv ℝ Ψ (F p_star) := by
    have hw (i : Fin 2) : HasFDerivAt (fun x : EuclideanPlane ↦ x i)
        (euclidProj i) (F p_star) := (euclidProj i).hasFDerivAt
    have h0 : HasFDerivAt (fun x : EuclideanPlane ↦ g (x 0))
        (c₀ • euclidProj (0 : Fin 2)) (F p_star) := by
      have hF0 : (F p_star) 0 = t₀ := rfl
      refine ((hF0 ▸ hg_der).comp (F p_star) (hw 0)).congr_fderiv ?_
      ext v
      simp [smul_apply]
    rw [(hasFDerivAt_vec2 h0 (hw 1)).fderiv]
    ext v i
    fin_cases i <;> simp [eΨ, euclidProj, smul_eq_mul]
  have hΦ_p : Φ p_star = 0 := by
    refine ext_vec4 ?_ rfl rfl rfl
    simp [Φ, p_star, hg0]
  have hΨ_fp : Ψ (F p_star) = wrinkledCuspMap 0 := by
    refine ext_vec2 ?_ ?_ <;> simp [Ψ, F, p_star, wrinkledCuspMap, hg0]
  refine isLocallyModeledOn_of_contDiff_maps isOpen_univ trivial isOpen_univ trivial
    hΦ_diff.contDiffOn hΨ_diff.contDiffOn eΦ heΦ eΨ heΨ hΦ_p hΨ_fp ?_
    hF_diff.continuous.continuousAt
  refine Eventually.of_forall fun p ↦ ⟨trivial, ?_⟩
  refine ext_vec2 rfl ?_
  simp only [Ψ, Φ, wrinkledCuspMap, vec2_zero, vec2_one, vec4_zero, vec4_one,
    vec4_two, vec4_three]

private theorem isIndefiniteFoldAt_cubicMinusThreeG
    {g : ℝ → ℝ} (hg_diff : ContDiff ℝ ∞ g) {p : EuclideanSpace ℝ (Fin 4)}
    (hp1_sq : p 1 ^ 2 = g (p 0)) (hp1 : p 1 ≠ 0) (hp2 : p 2 = 0) (hp3 : p 3 = 0) :
    IsIndefiniteFoldAt (𝓡 4) (𝓡 2)
      (fun q ↦ vec2 (q 0) (q 1 ^ 3 - 3 * g (q 0) * q 1 + q 2 ^ 2 - q 3 ^ 2)) p := by
  let F : EuclideanSpace ℝ (Fin 4) → EuclideanPlane :=
    fun q ↦ vec2 (q 0) (q 1 ^ 3 - 3 * g (q 0) * q 1 + q 2 ^ 2 - q 3 ^ 2)
  have hF_diff : ContDiff ℝ ∞ F := by
    have hq (i : Fin 4) : ContDiff ℝ ∞ (fun q : EuclideanSpace ℝ (Fin 4) ↦ q i) :=
      (euclidProj i).contDiff
    have hg0_diff : ContDiff ℝ ∞ (fun q : EuclideanSpace ℝ (Fin 4) ↦ g (q 0)) :=
      hg_diff.comp (hq 0)
    exact contDiff_vec2 (hq 0)
      (((((hq 1).pow 3).sub ((contDiff_const.mul hg0_diff).mul (hq 1))).add
        ((hq 2).pow 2)).sub ((hq 3).pow 2))
  let ε : ℝ := if 0 < p 1 then 1 else -1
  have hε2 : ε ^ 2 = 1 := by by_cases h : 0 < p 1 <;> simp [ε, h]
  have hε_ne : ε ≠ 0 := by by_cases h : 0 < p 1 <;> simp [ε, h]
  have hε_p1 : 0 < ε * p 1 := by
    by_cases h : 0 < p 1
    · simp [ε, h]
    · have hneg : p 1 < 0 := lt_of_le_of_ne (not_lt.mp h) hp1
      simp only [ε, h, ↓reduceIte, neg_one_mul, Left.neg_pos_iff]
      exact hneg
  let r₀ : ℝ → ℝ := fun t ↦ ε * Real.sqrt (g t)
  have hgp_pos : 0 < g (p 0) := by rw [← hp1_sq]; exact sq_pos_iff.mpr hp1
  have hr₀_p : r₀ (p 0) = p 1 := by
    have hs_eq : Real.sqrt (g (p 0)) = ε * p 1 := by
      rw [← hp1_sq]
      by_cases h : 0 < p 1
      · simp [ε, h, Real.sqrt_sq h.le]
      · simp [ε, h, Real.sqrt_sq_eq_abs, abs_of_nonpos (not_lt.mp h)]
    calc
      r₀ (p 0) = ε * (ε * p 1) := by simp only [r₀, hs_eq]
      _ = ε ^ 2 * p 1 := by ring
      _ = p 1 := by rw [hε2, one_mul]
  let R : EuclideanSpace ℝ (Fin 4) → ℝ := fun q ↦ 2 * (ε * r₀ (q 0)) + ε * q 1
  have hRp : R p = 3 * (ε * p 1) := by simp only [R, hr₀_p]; ring
  have hRp_pos : 0 < R p := by rw [hRp]; positivity
  let U_dom : Set (EuclideanSpace ℝ (Fin 4)) := {q | 0 < g (q 0) ∧ 0 < R q}
  let U_tgt : Set EuclideanPlane := {w | 0 < g (w 0)}
  have hr₀_cont : Continuous r₀ :=
    continuous_const.mul (Real.continuous_sqrt.comp hg_diff.continuous)
  have hR_cont : Continuous R :=
    (continuous_const.mul (continuous_const.mul (hr₀_cont.comp (euclidProj 0).continuous))).add
      (continuous_const.mul (euclidProj 1).continuous)
  have hU_dom_open : IsOpen U_dom :=
    (isOpen_lt continuous_const (hg_diff.continuous.comp (euclidProj 0).continuous)).inter
      (isOpen_lt continuous_const hR_cont)
  have hU_tgt_open : IsOpen U_tgt :=
    isOpen_lt continuous_const (hg_diff.continuous.comp (euclidProj 0).continuous)
  have hp_dom : p ∈ U_dom := ⟨hgp_pos, hRp_pos⟩
  have hfp_tgt : F p ∈ U_tgt := by simpa [U_tgt, F] using hgp_pos
  have hr₀_contDiff : ContDiffOn ℝ ∞ r₀ {t | 0 < g t} :=
    contDiff_const.contDiffOn.mul (hg_diff.contDiffOn.sqrt fun t ht ↦ ne_of_gt ht)
  have hR_contDiff : ContDiffOn ℝ ∞ R U_dom := by
    have hq0 : ContDiff ℝ ∞ (fun q : EuclideanSpace ℝ (Fin 4) ↦ q 0) := (euclidProj 0).contDiff
    have hq1 : ContDiff ℝ ∞ (fun q : EuclideanSpace ℝ (Fin 4) ↦ q 1) := (euclidProj 1).contDiff
    have hr₀_comp : ContDiffOn ℝ ∞ (fun q : EuclideanSpace ℝ (Fin 4) ↦ r₀ (q 0)) U_dom :=
      hr₀_contDiff.comp hq0.contDiffOn fun _ hq ↦ hq.1
    exact (contDiff_const.contDiffOn.mul (contDiff_const.contDiffOn.mul hr₀_comp)).add
      (contDiff_const.contDiffOn.mul hq1.contDiffOn)
  let posCoord : EuclideanSpace ℝ (Fin 4) → ℝ := fun q ↦ if 0 < p 1 then q 3 else q 2
  let negCoord : EuclideanSpace ℝ (Fin 4) → ℝ := fun q ↦ if 0 < p 1 then q 2 else q 3
  let posProj : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ :=
    if 0 < p 1 then euclidProj (3 : Fin 4) else euclidProj (2 : Fin 4)
  let negProj : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ :=
    if 0 < p 1 then euclidProj (2 : Fin 4) else euclidProj (3 : Fin 4)
  have hpos_cont : ContDiff ℝ ∞ posCoord := by
    by_cases h : 0 < p 1
    · simpa [posCoord, h] using (euclidProj (3 : Fin 4)).contDiff
    · simpa [posCoord, h] using (euclidProj (2 : Fin 4)).contDiff
  have hneg_cont : ContDiff ℝ ∞ negCoord := by
    by_cases h : 0 < p 1
    · simpa [negCoord, h] using (euclidProj (2 : Fin 4)).contDiff
    · simpa [negCoord, h] using (euclidProj (3 : Fin 4)).contDiff
  let Φ : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4) := fun q ↦
    vec4 (posCoord q) (Real.sqrt 2 * (q 1 - r₀ (q 0)) * Real.sqrt (R q))
      (Real.sqrt 2 * negCoord q) (q 0 - p 0)
  let Ψ : EuclideanPlane → EuclideanPlane := fun w ↦
    vec2 (-ε * (w 1 + 2 * r₀ (w 0) ^ 3)) (w 0 - p 0)
  have hΦ_diff : ContDiffOn ℝ ∞ Φ U_dom := by
    have hq0 : ContDiff ℝ ∞ (fun q : EuclideanSpace ℝ (Fin 4) ↦ q 0) := (euclidProj 0).contDiff
    have hq1 : ContDiff ℝ ∞ (fun q : EuclideanSpace ℝ (Fin 4) ↦ q 1) := (euclidProj 1).contDiff
    have hr₀_comp : ContDiffOn ℝ ∞ (fun q : EuclideanSpace ℝ (Fin 4) ↦ r₀ (q 0)) U_dom :=
      hr₀_contDiff.comp hq0.contDiffOn fun _ hq ↦ hq.1
    have hR_sqrt : ContDiffOn ℝ ∞ (fun q ↦ Real.sqrt (R q)) U_dom :=
      hR_contDiff.sqrt fun _ hq ↦ hq.2.ne'
    have h1 : ContDiffOn ℝ ∞
        (fun q ↦ Real.sqrt 2 * (q 1 - r₀ (q 0)) * Real.sqrt (R q)) U_dom :=
      (contDiff_const.contDiffOn.mul (hq1.contDiffOn.sub hr₀_comp)).mul hR_sqrt
    have hpi : ContDiffOn ℝ ∞
        (fun q ↦ ![posCoord q, Real.sqrt 2 * (q 1 - r₀ (q 0)) * Real.sqrt (R q),
          Real.sqrt 2 * negCoord q, q 0 - p 0]) U_dom := by
      refine contDiffOn_pi.mpr fun i ↦ ?_
      fin_cases i
      · exact hpos_cont.contDiffOn
      · exact h1
      · exact (contDiff_const.mul hneg_cont).contDiffOn
      · exact (hq0.sub contDiff_const).contDiffOn
    exact ((EuclideanSpace.equiv (Fin 4) ℝ).symm.contDiff).contDiffOn.comp hpi
      (fun _ _ ↦ Set.mem_univ _)
  have hΨ_diff : ContDiffOn ℝ ∞ Ψ U_tgt := by
    have hw0 : ContDiff ℝ ∞ (fun w : EuclideanPlane ↦ w 0) := (euclidProj 0).contDiff
    have hw1 : ContDiff ℝ ∞ (fun w : EuclideanPlane ↦ w 1) := (euclidProj 1).contDiff
    have hr₀_w : ContDiffOn ℝ ∞ (fun w : EuclideanPlane ↦ r₀ (w 0)) U_tgt :=
      hr₀_contDiff.comp hw0.contDiffOn fun _ hw ↦ hw
    have h0 : ContDiffOn ℝ ∞ (fun w : EuclideanPlane ↦ -ε * (w 1 + 2 * r₀ (w 0) ^ 3)) U_tgt :=
      contDiff_const.contDiffOn.mul
        (hw1.contDiffOn.add (contDiff_const.contDiffOn.mul (hr₀_w.pow 3)))
    have hpi : ContDiffOn ℝ ∞
        (fun w : EuclideanPlane ↦ ![-ε * (w 1 + 2 * r₀ (w 0) ^ 3), w 0 - p 0]) U_tgt := by
      refine contDiffOn_pi.mpr fun i ↦ ?_
      fin_cases i
      · exact h0
      · exact (hw0.sub contDiff_const).contDiffOn
    exact ((EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff).contDiffOn.comp hpi
      (fun _ _ ↦ Set.mem_univ _)
  have hg_pos_open : IsOpen {t : ℝ | 0 < g t} := isOpen_lt continuous_const hg_diff.continuous
  have hr₀_diffAt : DifferentiableAt ℝ r₀ (p 0) :=
    (hr₀_contDiff.contDiffAt (hg_pos_open.mem_nhds hgp_pos)).differentiableAt (by simp)
  let dr₀ : ℝ := deriv r₀ (p 0)
  have hr₀_fderiv : HasFDerivAt r₀ (dr₀ • ContinuousLinearMap.id ℝ ℝ) (p 0) := by
    refine hr₀_diffAt.hasDerivAt.hasFDerivAt.congr_fderiv ?_
    apply ContinuousLinearMap.ext_ring
    simp [dr₀, smul_eq_mul]
  let k : ℝ := Real.sqrt 2 * Real.sqrt (R p)
  have hk_ne : k ≠ 0 := mul_ne_zero (Real.sqrt_pos.mpr (by norm_num)).ne'
    (Real.sqrt_pos.mpr hRp_pos).ne'
  have hrt2_ne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  let eΦ : EuclideanSpace ℝ (Fin 4) ≃L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    { toFun := fun v ↦
        vec4 (posProj v) (k * (v 1 - dr₀ * v 0)) (Real.sqrt 2 * negProj v) (v 0)
      invFun := fun u ↦ if 0 < p 1 then
          vec4 (u 3) (u 1 / k + dr₀ * u 3) (u 2 / Real.sqrt 2) (u 0)
        else
          vec4 (u 3) (u 1 / k + dr₀ * u 3) (u 0) (u 2 / Real.sqrt 2)
      map_add' := fun u v ↦ by
        refine ext_vec4 ?_ ?_ ?_ ?_ <;>
          simp only [vec4_zero, vec4_one, vec4_two, vec4_three, map_add, PiLp.add_apply] <;> ring
      map_smul' := fun r v ↦ by
        refine ext_vec4 ?_ ?_ ?_ ?_ <;>
          simp only [vec4_zero, vec4_one, vec4_two, vec4_three, map_smul, PiLp.smul_apply,
            smul_eq_mul, RingHom.id_apply] <;> ring
      left_inv := fun v ↦ by
        by_cases h : 0 < p 1
        · refine ext_vec4 ?_ ?_ ?_ ?_
          · simp [h, vec4_zero, posProj, euclidProj]
          · simp only [h, ↓reduceIte, vec4_zero, vec4_one, vec4_three]
            field_simp [hk_ne]
            ring
          · simp only [h, ↓reduceIte, vec4_two, negProj, euclidProj, EuclideanSpace.proj,
              PiLp.proj_apply]
            exact mul_div_cancel_left₀ _ hrt2_ne
          · simp [posProj, h, euclidProj]
        · refine ext_vec4 ?_ ?_ ?_ ?_
          · simp [h, vec4_zero, posProj, euclidProj]
          · simp only [h, ↓reduceIte, vec4_zero, vec4_one, vec4_three]
            field_simp [hk_ne]
            ring
          · simp [posProj, h, euclidProj]
          · simp only [h, ↓reduceIte, vec4_two, negProj, euclidProj, EuclideanSpace.proj,
              PiLp.proj_apply]
            exact mul_div_cancel_left₀ _ hrt2_ne
      right_inv := fun u ↦ by
        by_cases h : 0 < p 1
        · refine ext_vec4 ?_ ?_ ?_ ?_
          · simp [h, posProj, euclidProj]
          · simp only [h, ↓reduceIte, vec4_zero, vec4_one]
            field_simp [hk_ne]
            ring
          · simp only [h, ↓reduceIte, negProj, euclidProj, EuclideanSpace.proj,
              PiLp.proj_apply, vec4_two]
            exact mul_div_cancel₀ _ hrt2_ne
          · simp [h]
        · refine ext_vec4 ?_ ?_ ?_ ?_
          · simp [h, posProj, euclidProj]
          · simp only [h, ↓reduceIte, vec4_zero, vec4_one]
            field_simp [hk_ne]
            ring
          · simp only [h, ↓reduceIte, negProj, euclidProj, EuclideanSpace.proj,
              PiLp.proj_apply, vec4_three]
            exact mul_div_cancel₀ _ hrt2_ne
          · simp [h]
      continuous_toFun := continuous_vec4 posProj.continuous
        (continuous_const.mul ((euclidProj 1).continuous.sub
          (continuous_const.mul (euclidProj 0).continuous)))
        (continuous_const.mul negProj.continuous) (euclidProj 0).continuous
      continuous_invFun := by
        by_cases h : 0 < p 1
        · simp only [h, ↓reduceIte]
          exact continuous_vec4 (euclidProj 3).continuous
            (((euclidProj 1).continuous.div_const k).add
              (continuous_const.mul (euclidProj 3).continuous))
            ((euclidProj 2).continuous.div_const (Real.sqrt 2)) (euclidProj 0).continuous
        · simp only [h, ↓reduceIte]
          exact continuous_vec4 (euclidProj 3).continuous
            (((euclidProj 1).continuous.div_const k).add
              (continuous_const.mul (euclidProj 3).continuous))
            (euclidProj 0).continuous ((euclidProj 2).continuous.div_const (Real.sqrt 2)) }
  let r₃ : ℝ → ℝ := fun t ↦ 2 * r₀ t ^ 3
  have hr₃_diffAt : DifferentiableAt ℝ r₃ (p 0) :=
    ((hr₀_diffAt.pow 3).const_mul 2)
  let dr₃ : ℝ := deriv r₃ (p 0)
  have hr₃_fderiv : HasFDerivAt r₃ (dr₃ • ContinuousLinearMap.id ℝ ℝ) (p 0) := by
    refine hr₃_diffAt.hasDerivAt.hasFDerivAt.congr_fderiv ?_
    apply ContinuousLinearMap.ext_ring
    simp [dr₃, smul_eq_mul]
  let eΨ : EuclideanPlane ≃L[ℝ] EuclideanPlane :=
    { toFun := fun v ↦ vec2 (-ε * (v 1 + dr₃ * v 0)) (v 0)
      invFun := fun u ↦ vec2 (u 1) (-ε * u 0 - dr₃ * u 1)
      map_add' := fun u v ↦ by refine ext_vec2 ?_ ?_ <;> simp; ring
      map_smul' := fun r v ↦ by refine ext_vec2 ?_ ?_ <;> simp; ring
      left_inv := fun v ↦ by
        refine ext_vec2 ?_ ?_
        · rfl
        · simp only [vec2_zero, vec2_one]
          calc
            -ε * (-ε * (v 1 + dr₃ * v 0)) - dr₃ * v 0
              = ε ^ 2 * (v 1 + dr₃ * v 0) - dr₃ * v 0 := by ring
            _ = v 1 := by rw [hε2, one_mul]; ring
      right_inv := fun u ↦ by
        refine ext_vec2 ?_ ?_
        · simp only [vec2_zero, vec2_one]
          calc
            -ε * (-ε * u 0 - dr₃ * u 1 + dr₃ * u 1) = ε ^ 2 * u 0 := by ring
            _ = u 0 := by rw [hε2, one_mul]
        · rfl
      continuous_toFun := continuous_vec2
        (continuous_const.mul ((euclidProj 1).continuous.add
          (continuous_const.mul (euclidProj 0).continuous)))
        (euclidProj 0).continuous
      continuous_invFun := continuous_vec2 (euclidProj 1).continuous
        ((continuous_const.mul (euclidProj 0).continuous).sub
          (continuous_const.mul (euclidProj 1).continuous)) }
  have heΦ : (eΦ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) =
      fderiv ℝ Φ p := by
    have hq (i : Fin 4) : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ x i)
        (euclidProj i) p := (euclidProj i).hasFDerivAt
    have hpos_der : HasFDerivAt posCoord posProj p := by
      by_cases h : 0 < p 1 <;> simp only [posCoord, posProj, h, ↓reduceIte] <;> exact hq _
    have hneg_der : HasFDerivAt negCoord negProj p := by
      by_cases h : 0 < p 1 <;> simp only [negCoord, negProj, h, ↓reduceIte] <;> exact hq _
    have hdiff_diff : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 4) ↦ q 1 - r₀ (q 0))
        (euclidProj (1 : Fin 4) - dr₀ • euclidProj (0 : Fin 4)) p := by
      refine ((hq 1).sub (hr₀_fderiv.comp p (hq 0))).congr_fderiv ?_
      ext v
      simp [sub_apply, smul_apply]
    have hR_sqrt_diff : DifferentiableAt ℝ (fun q ↦ Real.sqrt (R q)) p := by
      have hRc := hR_contDiff.sqrt fun _ hqU ↦ hqU.2.ne'
      exact (hRc.contDiffAt (hU_dom_open.mem_nhds hp_dom)).differentiableAt (by simp)
    have h1_der : HasFDerivAt
        (fun q ↦ Real.sqrt 2 * (q 1 - r₀ (q 0)) * Real.sqrt (R q))
        (k • (euclidProj (1 : Fin 4) - dr₀ • euclidProj (0 : Fin 4))) p := by
      have hm := (hdiff_diff.const_mul (Real.sqrt 2)).mul hR_sqrt_diff.hasFDerivAt
      refine hm.congr_fderiv ?_
      ext v
      have hp_zero : p 1 - r₀ (p 0) = 0 := sub_eq_zero.mpr hr₀_p.symm
      simp only [add_apply, smul_apply, sub_apply, hp_zero, mul_zero, k]
      ring
    have h3_der : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 4) ↦ q 0 - p 0)
        (euclidProj (0 : Fin 4)) p :=
      (hq 0).sub_const (p 0)
    have hneg2_der : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 4) ↦ Real.sqrt 2 * negCoord q)
        ((Real.sqrt 2) • negProj) p :=
      hneg_der.const_mul (Real.sqrt 2)
    rw [(hasFDerivAt_vec4' hpos_der h1_der hneg2_der h3_der).fderiv]
    ext v i
    fin_cases i <;> simp [eΦ, euclidProj, smul_eq_mul, sub_eq_add_neg]; ring
  have heΨ : (eΨ : EuclideanPlane →L[ℝ] EuclideanPlane) = fderiv ℝ Ψ (F p) := by
    have hw (i : Fin 2) : HasFDerivAt (fun x : EuclideanPlane ↦ x i)
        (euclidProj i) (F p) := (euclidProj i).hasFDerivAt
    have hFp0 : (F p) 0 = p 0 := rfl
    have hr₃_comp : HasFDerivAt (fun w : EuclideanPlane ↦ r₃ (w 0))
        (dr₃ • euclidProj (0 : Fin 2)) (F p) := by
      have hderiv_r₃ : HasFDerivAt r₃ (dr₃ • ContinuousLinearMap.id ℝ ℝ) ((F p) 0) :=
        hFp0 ▸ hr₃_fderiv
      refine (hderiv_r₃.comp (F p) (hw 0)).congr_fderiv ?_
      ext v
      simp [smul_apply]
    have h0_der : HasFDerivAt (fun w : EuclideanPlane ↦ -ε * (w 1 + r₃ (w 0)))
        ((-ε) • (euclidProj (1 : Fin 2) + dr₃ • euclidProj (0 : Fin 2))) (F p) :=
      ((hw 1).add hr₃_comp).const_mul (-ε)
    have h1_der : HasFDerivAt (fun w : EuclideanPlane ↦ w 0 - p 0) (euclidProj (0 : Fin 2)) (F p) :=
      (hw 0).sub_const (p 0)
    rw [(hasFDerivAt_vec2 h0_der h1_der).fderiv]
    ext v i
    fin_cases i <;> simp [eΨ, euclidProj, smul_eq_mul]; ring
  have hΦ_p : Φ p = 0 := by
    refine ext_vec4 ?_ ?_ ?_ ?_
    · by_cases h : 0 < p 1 <;> simp [Φ, posCoord, h, hp2, hp3]
    · simp [Φ, hr₀_p]
    · by_cases h : 0 < p 1 <;> simp [Φ, negCoord, h, hp2, hp3]
    · simp [Φ]
  have hΨ_fp : Ψ (F p) = indefiniteFoldMap 0 := by
    refine ext_vec2 ?_ ?_
    · simp only [Ψ, F, indefiniteFoldMap, vec2_zero, vec2_one, PiLp.zero_apply, hr₀_p, hp2, hp3]
      rw [show p 1 ^ 3 = p 1 ^ 2 * p 1 by ring, hp1_sq]
      ring
    · simp [Ψ, F, indefiniteFoldMap]
  refine isLocallyModeledOn_of_contDiff_maps hU_dom_open hp_dom hU_tgt_open hfp_tgt
    hΦ_diff hΨ_diff eΦ heΦ eΨ heΨ hΦ_p hΨ_fp ?_ hF_diff.continuous.continuousAt
  filter_upwards [hU_dom_open.mem_nhds hp_dom] with q hq
  have hq_tgt : F q ∈ U_tgt := by simpa [U_tgt, F] using hq.1
  refine ⟨hq_tgt, ?_⟩
  have hr₀_sq : r₀ (q 0) ^ 2 = g (q 0) := by
    simp only [r₀, mul_pow, hε2, one_mul, Real.sq_sqrt hq.1.le]
  have hR_sq : Real.sqrt (R q) ^ 2 = R q := Real.sq_sqrt hq.2.le
  have hrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  refine ext_vec2 ?_ rfl
  simp only [Ψ, Φ, indefiniteFoldMap, vec2_zero, vec4_zero, vec4_one, vec4_two]
  have hnum :
      -ε * (q 1 ^ 3 - 3 * g (q 0) * q 1 + q 2 ^ 2 - q 3 ^ 2 + 2 * r₀ (q 0) ^ 3) =
        posCoord q ^ 2 - ((Real.sqrt 2 * (q 1 - r₀ (q 0)) * Real.sqrt (R q)) ^ 2 +
          (Real.sqrt 2 * negCoord q) ^ 2) / 2 := by
    rw [← hr₀_sq]
    have hsq_term : (Real.sqrt 2 * (q 1 - r₀ (q 0)) * Real.sqrt (R q)) ^ 2 =
        2 * (q 1 - r₀ (q 0)) ^ 2 * R q := by
      calc
        (Real.sqrt 2 * (q 1 - r₀ (q 0)) * Real.sqrt (R q)) ^ 2
          = Real.sqrt 2 ^ 2 * (q 1 - r₀ (q 0)) ^ 2 * Real.sqrt (R q) ^ 2 := by ring
        _ = 2 * (q 1 - r₀ (q 0)) ^ 2 * R q := by rw [hrt2_sq, hR_sq]
    have hneg_term : (Real.sqrt 2 * negCoord q) ^ 2 = 2 * negCoord q ^ 2 := by
      calc
        (Real.sqrt 2 * negCoord q) ^ 2 = Real.sqrt 2 ^ 2 * negCoord q ^ 2 := by ring
        _ = 2 * negCoord q ^ 2 := by rw [hrt2_sq]
    rw [hsq_term, hneg_term]
    by_cases h : 0 < p 1
    · simp only [ε, posCoord, negCoord, R, h, ↓reduceIte]
      ring
    · simp only [ε, posCoord, negCoord, R, h, ↓reduceIte]
      ring
  exact hnum

/-- Closed-form `IsIndefiniteFoldAt` on `{p ∈ criticalPoints (lekiliMove2 s) | p 1 ≠ 0}` (`0 < s`).
-/
-- tier: T2
theorem isIndefiniteFoldAt_lekiliMove2 {s : ℝ} (hs : 0 < s) {p : EuclideanSpace ℝ (Fin 4)}
    (hp : p ∈ criticalPoints (𝓡 4) (𝓡 2) (lekiliMove2 s)) (hp1 : p 1 ≠ 0) :
    IsIndefiniteFoldAt (𝓡 4) (𝓡 2) (lekiliMove2 s) p := by
  rw [criticalPoints_lekiliMove2_nonneg hs.le, Set.mem_ofPred_eq] at hp
  have hfun :
      lekiliMove2 s =
        fun q ↦ vec2 (q 0) (q 1 ^ 3 - 3 * (s - q 0 ^ 2) * q 1 + q 2 ^ 2 - q 3 ^ 2) := by
    funext q
    refine ext_vec2 rfl ?_
    simp only [lekiliMove2, vec2_one]
    ring
  rw [hfun]
  have hg_diff : ContDiff ℝ ∞ (fun t : ℝ ↦ s - t ^ 2) :=
    contDiff_const.sub (contDiff_id.pow 2)
  exact isIndefiniteFoldAt_cubicMinusThreeG hg_diff (by linarith [hp.1]) hp1 hp.2.1 hp.2.2

/-- **Lekili Move 3 (Merging Two Opposite Cusps into an Indefinite Fold)**:
`(t, x₁, x₂, x₃) ↦ (t, x₁³ - 3(t² - s) x₁ + x₂² - x₃²)`. For `s > 0`, the critical locus
consists of two opposite cusped hyperbola arcs with cusps at `(±√s, 0, 0, 0)`; for `s < 0`, the
two cusps merge into two disjoint regular arcs of indefinite folds. -/
-- tier: T2
noncomputable def lekiliMove3 (s : ℝ) (p : EuclideanSpace ℝ (Fin 4)) : EuclideanPlane :=
  vec2 (p 0) (p 1 ^ 3 - 3 * (p 0 ^ 2 - s) * p 1 + p 2 ^ 2 - p 3 ^ 2)

/-- Smoothness (`ContDiff ℝ ∞`) of `lekiliMove3 s`. -/
theorem contDiff_lekiliMove3 (s : ℝ) : ContDiff ℝ ∞ (lekiliMove3 s) := by
  have hp (i : Fin 4) : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 4) ↦ p i) :=
    (euclidProj i).contDiff
  exact contDiff_vec2 (hp 0)
    (((((hp 1).pow 3).sub ((contDiff_const.mul (((hp 0).pow 2).sub contDiff_const)).mul (hp 1))).add
      ((hp 2).pow 2)).sub ((hp 3).pow 2))

/-- Manifold smoothness of `lekiliMove3 s`. -/
-- tier: T2
theorem contMDiff_lekiliMove3 (s : ℝ) : ContMDiff (𝓡 4) (𝓡 2) ∞ (lekiliMove3 s) :=
  (contDiff_lekiliMove3 s).contMDiff

/-- Continuous linear map representing `fderiv ℝ (lekiliMove3 s) p`. -/
noncomputable def lekiliMove3FDerivCLM (s : ℝ) (p : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanPlane :=
  clmVec2
    (euclidProj (0 : Fin 4))
    ((-6 * p 0 * p 1) • euclidProj (0 : Fin 4) +
      (3 * (p 1 ^ 2 - p 0 ^ 2 + s)) • euclidProj (1 : Fin 4) +
      (2 * p 2) • euclidProj (2 : Fin 4) -
      (2 * p 3) • euclidProj (3 : Fin 4))

@[simp]
theorem lekiliMove3FDerivCLM_apply (s : ℝ) (p v : EuclideanSpace ℝ (Fin 4)) :
    lekiliMove3FDerivCLM s p v =
      vec2 (v 0) (-6 * p 0 * p 1 * v 0 + 3 * (p 1 ^ 2 - p 0 ^ 2 + s) * v 1 +
        2 * p 2 * v 2 - 2 * p 3 * v 3) := by
  simp [lekiliMove3FDerivCLM, euclidProj]

/-- Exact Fréchet derivative of `lekiliMove3 s` at `p`. -/
theorem hasFDerivAt_lekiliMove3 (s : ℝ) (p : EuclideanSpace ℝ (Fin 4)) :
    HasFDerivAt (lekiliMove3 s) (lekiliMove3FDerivCLM s p) p := by
  have hp (i : Fin 4) : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ x i)
      (euclidProj i) p := (euclidProj i).hasFDerivAt
  have hsq (i : Fin 4) : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ x i ^ 2)
      ((2 * p i) • euclidProj i) p := by
    convert (hp i).pow 2 using 1
    ext v; simp [smul_apply, euclidProj, nsmul_eq_mul, smul_eq_mul]
  have hcube : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ x 1 ^ 3)
      ((3 * p 1 ^ 2) • euclidProj (1 : Fin 4)) p := by
    convert (hp 1).pow 3 using 1
    ext v; simp [smul_apply, euclidProj, nsmul_eq_mul, smul_eq_mul]
  have hmid : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ 3 * (x 0 ^ 2 - s) * x 1)
      ((6 * p 0 * p 1) • euclidProj (0 : Fin 4) +
        (3 * (p 0 ^ 2 - s)) • euclidProj (1 : Fin 4)) p := by
    refine ((((hsq 0).sub (hasFDerivAt_const s p)).const_mul (3 : ℝ)).mul (hp 1)).congr_fderiv ?_
    ext v
    simp only [add_apply, sub_apply, Pi.sub_apply, zero_apply, smul_apply, euclidProj,
      EuclideanSpace.proj, smul_eq_mul]
    ring
  have h1 : HasFDerivAt
      (fun x : EuclideanSpace ℝ (Fin 4) ↦ x 1 ^ 3 - 3 * (x 0 ^ 2 - s) * x 1 + x 2 ^ 2 - x 3 ^ 2)
      ((-6 * p 0 * p 1) • euclidProj (0 : Fin 4) +
        (3 * (p 1 ^ 2 - p 0 ^ 2 + s)) • euclidProj (1 : Fin 4) +
        (2 * p 2) • euclidProj (2 : Fin 4) -
        (2 * p 3) • euclidProj (3 : Fin 4)) p := by
    convert (((hcube.sub hmid).add (hsq 2)).sub (hsq 3)) using 1
    ext v
    simp only [add_apply, sub_apply, smul_apply, euclidProj, EuclideanSpace.proj, smul_eq_mul]
    ring
  exact hasFDerivAt_vec2 (hp 0) h1

/-- `fderiv ℝ (lekiliMove3 s) p = lekiliMove3FDerivCLM s p`. -/
@[simp]
theorem fderiv_lekiliMove3 (s : ℝ) (p : EuclideanSpace ℝ (Fin 4)) :
    fderiv ℝ (lekiliMove3 s) p = lekiliMove3FDerivCLM s p :=
  (hasFDerivAt_lekiliMove3 s p).fderiv

/-- Surjectivity characterization of `fderiv ℝ (lekiliMove3 s) p`. -/
theorem surjective_fderiv_lekiliMove3_iff (s : ℝ) (p : EuclideanSpace ℝ (Fin 4)) :
    Function.Surjective (fderiv ℝ (lekiliMove3 s) p) ↔
      ¬ (p 1 ^ 2 = p 0 ^ 2 - s ∧ p 2 = 0 ∧ p 3 = 0) := by
  rw [fderiv_lekiliMove3]
  constructor
  · rintro hsurj ⟨h01, hp2, hp3⟩
    obtain ⟨v, hv⟩ := hsurj (vec2 0 1)
    have hv0 := congrArg (fun u : EuclideanPlane ↦ u 0) hv
    have hv1 := congrArg (fun u : EuclideanPlane ↦ u 1) hv
    simp only [lekiliMove3FDerivCLM_apply, vec2_zero, vec2_one, hp2, hp3, mul_zero] at hv0 hv1
    have hcoeff : p 1 ^ 2 - p 0 ^ 2 + s = 0 := by linarith
    rw [hv0, hcoeff] at hv1
    linarith
  · intro hnot w
    by_cases h1 : p 1 ^ 2 - p 0 ^ 2 + s ≠ 0
    · refine ⟨vec4 (w 0)
          ((w 1 + 6 * p 0 * p 1 * w 0) / (3 * (p 1 ^ 2 - p 0 ^ 2 + s))) 0 0, ext_vec2 ?_ ?_⟩
      · simp
      · simp only [lekiliMove3FDerivCLM_apply, vec2_one, vec4_zero, vec4_one, vec4_two, vec4_three]
        field_simp [h1]
        ring
    · by_cases h2 : p 2 ≠ 0
      · refine ⟨vec4 (w 0) 0 ((w 1 + 6 * p 0 * p 1 * w 0) / (2 * p 2)) 0, ext_vec2 ?_ ?_⟩
        · simp
        · simp only [lekiliMove3FDerivCLM_apply, vec2_one, vec4_zero, vec4_one, vec4_two,
            vec4_three]
          field_simp [h2]
          ring
      · push Not at h1 h2
        have hp3 : p 3 ≠ 0 := by
          intro h3
          exact hnot ⟨by linarith, h2, h3⟩
        refine ⟨vec4 (w 0) 0 0 (-(w 1 + 6 * p 0 * p 1 * w 0) / (2 * p 3)), ext_vec2 ?_ ?_⟩
        · simp
        · simp only [lekiliMove3FDerivCLM_apply, vec2_one, vec4_zero, vec4_one, vec4_two,
            vec4_three]
          field_simp [hp3]
          ring

/-- Critical locus of `lekiliMove3 s`: `{p | p₁² = p₀² - s ∧ p₂ = 0 ∧ p₃ = 0}`. -/
-- tier: T2
theorem criticalPoints_lekiliMove3 (s : ℝ) :
    criticalPoints (𝓡 4) (𝓡 2) (lekiliMove3 s) =
      {p : EuclideanSpace ℝ (Fin 4) | p 1 ^ 2 = p 0 ^ 2 - s ∧ p 2 = 0 ∧ p 3 = 0} := by
  rw [criticalPoints_euclidean_eq]
  ext p
  rw [mem_euclideanCriticalPoints_iff, surjective_fderiv_lekiliMove3_iff, not_not,
    Set.mem_ofPred_eq]

/-- Closed-form `IsWrinkledCuspAt` at `(σ * √s, 0, 0, 0)` (`σ = ±1`, `0 < s`) for `lekiliMove3 s`.
-/
-- tier: T2
theorem isWrinkledCuspAt_lekiliMove3 {s σ : ℝ} (hs : 0 < s) (hσ : σ = 1 ∨ σ = -1) :
    IsWrinkledCuspAt (𝓡 4) (𝓡 2) (lekiliMove3 s) (vec4 (σ * Real.sqrt s) 0 0 0) := by
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσ_ne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hsqrt_ne : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  let g : ℝ → ℝ := fun t ↦ t ^ 2 - s
  have hg_diff : ContDiff ℝ ∞ g := (contDiff_id.pow 2).sub contDiff_const
  have hg0 : g (σ * Real.sqrt s) = 0 := by
    simp [g, mul_pow, hσ2, Real.sq_sqrt hs.le]
  have hg'_ne : deriv g (σ * Real.sqrt s) ≠ 0 := by
    have hder : HasDerivAt g (2 * (σ * Real.sqrt s)) (σ * Real.sqrt s) := by
      have hid := hasDerivAt_id (σ * Real.sqrt s)
      refine ((hid.pow 2).sub (hasDerivAt_const _ s)).congr_deriv ?_
      dsimp only [id_eq]
      ring
    rw [hder.deriv]
    exact mul_ne_zero (by norm_num) (mul_ne_zero hσ_ne hsqrt_ne)
  exact isWrinkledCuspAt_cubicMinusThreeG hg_diff hg0 hg'_ne

/-- Closed-form `IsIndefiniteFoldAt` on `{p ∈ criticalPoints (lekiliMove3 s) | p 1 ≠ 0}`. -/
-- tier: T2
theorem isIndefiniteFoldAt_lekiliMove3 (s : ℝ) {p : EuclideanSpace ℝ (Fin 4)}
    (hp : p ∈ criticalPoints (𝓡 4) (𝓡 2) (lekiliMove3 s)) (hp1 : p 1 ≠ 0) :
    IsIndefiniteFoldAt (𝓡 4) (𝓡 2) (lekiliMove3 s) p := by
  rw [criticalPoints_lekiliMove3, Set.mem_ofPred_eq] at hp
  have hg_diff : ContDiff ℝ ∞ (fun t : ℝ ↦ t ^ 2 - s) :=
    (contDiff_id.pow 2).sub contDiff_const
  exact isIndefiniteFoldAt_cubicMinusThreeG hg_diff hp.1 hp1 hp.2.1 hp.2.2

/-- After Move 3 crosses to `s < 0`, every critical point of `lekiliMove3 s` is an indefinite fold.
-/
theorem isIndefiniteFoldAt_lekiliMove3_of_neg {s : ℝ} (hs : s < 0) {p : EuclideanSpace ℝ (Fin 4)}
    (hp : p ∈ criticalPoints (𝓡 4) (𝓡 2) (lekiliMove3 s)) :
    IsIndefiniteFoldAt (𝓡 4) (𝓡 2) (lekiliMove3 s) p := by
  have hp_mem := hp
  rw [criticalPoints_lekiliMove3, Set.mem_ofPred_eq] at hp_mem
  have hp1_pos : 0 < p 1 ^ 2 := by nlinarith [sq_nonneg (p 0), hp_mem.1]
  have hp1 : p 1 ≠ 0 := fun h ↦ by simp [h] at hp1_pos
  exact isIndefiniteFoldAt_lekiliMove3 s hp hp1

/-- **Lekili Move 4 (Swallowtail / Flip Move)**:
`(t, x₁, x₂, x₃) ↦ (t, x₁⁴/4 + s x₁²/2 - t x₁ + x₂² - x₃²)`. The critical locus is the smooth
curve `p₀ = p₁³ + s p₁, p₂ = p₃ = 0`; its image in `ℝ²` has `0` cusps for `s > 0`, one
swallowtail point at `s = 0`, and two cusps `x₁ = ±√(-s/3)` for `s < 0`. -/
-- tier: T2
noncomputable def lekiliMove4 (s : ℝ) (p : EuclideanSpace ℝ (Fin 4)) : EuclideanPlane :=
  vec2 (p 0) (p 1 ^ 4 / 4 + s * p 1 ^ 2 / 2 - p 0 * p 1 + p 2 ^ 2 - p 3 ^ 2)

/-- Smoothness (`ContDiff ℝ ∞`) of `lekiliMove4 s`. -/
theorem contDiff_lekiliMove4 (s : ℝ) : ContDiff ℝ ∞ (lekiliMove4 s) := by
  have hp (i : Fin 4) : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 4) ↦ p i) :=
    (euclidProj i).contDiff
  exact contDiff_vec2 (hp 0)
    (((((((hp 1).pow 4).div_const 4).add ((contDiff_const.mul ((hp 1).pow 2)).div_const 2)).sub
      ((hp 0).mul (hp 1))).add ((hp 2).pow 2)).sub ((hp 3).pow 2))

/-- Manifold smoothness of `lekiliMove4 s`. -/
-- tier: T2
theorem contMDiff_lekiliMove4 (s : ℝ) : ContMDiff (𝓡 4) (𝓡 2) ∞ (lekiliMove4 s) :=
  (contDiff_lekiliMove4 s).contMDiff

/-- Continuous linear map representing `fderiv ℝ (lekiliMove4 s) p`. -/
noncomputable def lekiliMove4FDerivCLM (s : ℝ) (p : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanPlane :=
  clmVec2
    (euclidProj (0 : Fin 4))
    ((-p 1) • euclidProj (0 : Fin 4) +
      (p 1 ^ 3 + s * p 1 - p 0) • euclidProj (1 : Fin 4) +
      (2 * p 2) • euclidProj (2 : Fin 4) -
      (2 * p 3) • euclidProj (3 : Fin 4))

@[simp]
theorem lekiliMove4FDerivCLM_apply (s : ℝ) (p v : EuclideanSpace ℝ (Fin 4)) :
    lekiliMove4FDerivCLM s p v =
      vec2 (v 0) (-p 1 * v 0 + (p 1 ^ 3 + s * p 1 - p 0) * v 1 +
        2 * p 2 * v 2 - 2 * p 3 * v 3) := by
  simp [lekiliMove4FDerivCLM, euclidProj]

/-- Exact Fréchet derivative of `lekiliMove4 s` at `p`. -/
theorem hasFDerivAt_lekiliMove4 (s : ℝ) (p : EuclideanSpace ℝ (Fin 4)) :
    HasFDerivAt (lekiliMove4 s) (lekiliMove4FDerivCLM s p) p := by
  have hp (i : Fin 4) : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ x i)
      (euclidProj i) p := (euclidProj i).hasFDerivAt
  have h4 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ x 1 ^ 4 / 4)
      ((p 1 ^ 3) • euclidProj (1 : Fin 4)) p := by
    have heq : (fun x : EuclideanSpace ℝ (Fin 4) ↦ x 1 ^ 4 / 4) =
        fun x ↦ x 1 ^ 4 * (1 / 4 : ℝ) := by funext x; ring
    rw [heq]
    refine (((hp 1).pow 4).mul_const (1 / 4 : ℝ)).congr_fderiv ?_
    ext v; simp [smul_apply, euclidProj, nsmul_eq_mul, smul_eq_mul]; ring
  have h2s : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ s * x 1 ^ 2 / 2)
      ((s * p 1) • euclidProj (1 : Fin 4)) p := by
    have heq : (fun x : EuclideanSpace ℝ (Fin 4) ↦ s * x 1 ^ 2 / 2) =
        fun x ↦ s * x 1 ^ 2 * (1 / 2 : ℝ) := by funext x; ring
    rw [heq]
    refine ((((hp 1).pow 2).const_mul s).mul_const (1 / 2 : ℝ)).congr_fderiv ?_
    ext v; simp [smul_apply, euclidProj, nsmul_eq_mul, smul_eq_mul]; ring
  have h01 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ x 0 * x 1)
      ((p 1) • euclidProj (0 : Fin 4) + (p 0) • euclidProj (1 : Fin 4)) p := by
    convert (hp 0).mul (hp 1) using 1
    ext v; simp [smul_apply, euclidProj, smul_eq_mul]; ring
  have hsq (i : Fin 4) : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 4) ↦ x i ^ 2)
      ((2 * p i) • euclidProj i) p := by
    convert (hp i).pow 2 using 1
    ext v; simp [smul_apply, euclidProj, nsmul_eq_mul, smul_eq_mul]
  have h1 : HasFDerivAt
      (fun x : EuclideanSpace ℝ (Fin 4) ↦
        x 1 ^ 4 / 4 + s * x 1 ^ 2 / 2 - x 0 * x 1 + x 2 ^ 2 - x 3 ^ 2)
      ((-p 1) • euclidProj (0 : Fin 4) +
        (p 1 ^ 3 + s * p 1 - p 0) • euclidProj (1 : Fin 4) +
        (2 * p 2) • euclidProj (2 : Fin 4) -
        (2 * p 3) • euclidProj (3 : Fin 4)) p := by
    convert ((((h4.add h2s).sub h01).add (hsq 2)).sub (hsq 3)) using 1
    ext v
    simp only [add_apply, sub_apply, smul_apply, euclidProj, EuclideanSpace.proj, smul_eq_mul]
    ring
  exact hasFDerivAt_vec2 (hp 0) h1

/-- `fderiv ℝ (lekiliMove4 s) p = lekiliMove4FDerivCLM s p`. -/
@[simp]
theorem fderiv_lekiliMove4 (s : ℝ) (p : EuclideanSpace ℝ (Fin 4)) :
    fderiv ℝ (lekiliMove4 s) p = lekiliMove4FDerivCLM s p :=
  (hasFDerivAt_lekiliMove4 s p).fderiv

/-- Surjectivity characterization of `fderiv ℝ (lekiliMove4 s) p`. -/
theorem surjective_fderiv_lekiliMove4_iff (s : ℝ) (p : EuclideanSpace ℝ (Fin 4)) :
    Function.Surjective (fderiv ℝ (lekiliMove4 s) p) ↔
      ¬ (p 0 = p 1 ^ 3 + s * p 1 ∧ p 2 = 0 ∧ p 3 = 0) := by
  rw [fderiv_lekiliMove4]
  constructor
  · rintro hsurj ⟨h01, hp2, hp3⟩
    obtain ⟨v, hv⟩ := hsurj (vec2 0 1)
    have hv0 := congrArg (fun u : EuclideanPlane ↦ u 0) hv
    have hv1 := congrArg (fun u : EuclideanPlane ↦ u 1) hv
    simp only [lekiliMove4FDerivCLM_apply, vec2_zero, vec2_one, hp2, hp3, mul_zero] at hv0 hv1
    have hcoeff : p 1 ^ 3 + s * p 1 - p 0 = 0 := by linarith
    rw [hv0, hcoeff] at hv1
    linarith
  · intro hnot w
    by_cases h1 : p 1 ^ 3 + s * p 1 - p 0 ≠ 0
    · refine ⟨vec4 (w 0)
          ((w 1 + p 1 * w 0) / (p 1 ^ 3 + s * p 1 - p 0)) 0 0, ext_vec2 ?_ ?_⟩
      · simp
      · simp only [lekiliMove4FDerivCLM_apply, vec2_one, vec4_zero, vec4_one, vec4_two,
          vec4_three, mul_zero, add_zero, sub_zero]
        rw [mul_div_cancel₀ _ h1]
        ring
    · by_cases h2 : p 2 ≠ 0
      · refine ⟨vec4 (w 0) 0 ((w 1 + p 1 * w 0) / (2 * p 2)) 0, ext_vec2 ?_ ?_⟩
        · simp
        · simp only [lekiliMove4FDerivCLM_apply, vec2_one, vec4_zero, vec4_one, vec4_two,
            vec4_three]
          field_simp [h2]
          ring
      · push Not at h1 h2
        have hp3 : p 3 ≠ 0 := by
          intro h3
          exact hnot ⟨by linarith, h2, h3⟩
        refine ⟨vec4 (w 0) 0 0 (-(w 1 + p 1 * w 0) / (2 * p 3)), ext_vec2 ?_ ?_⟩
        · simp
        · simp only [lekiliMove4FDerivCLM_apply, vec2_one, vec4_zero, vec4_one, vec4_two,
            vec4_three]
          field_simp [hp3]
          ring

/-- Critical locus of `lekiliMove4 s`: `{p | p₀ = p₁³ + s p₁ ∧ p₂ = 0 ∧ p₃ = 0}`. -/
-- tier: T2
theorem criticalPoints_lekiliMove4 (s : ℝ) :
    criticalPoints (𝓡 4) (𝓡 2) (lekiliMove4 s) =
      {p : EuclideanSpace ℝ (Fin 4) | p 0 = p 1 ^ 3 + s * p 1 ∧ p 2 = 0 ∧ p 3 = 0} := by
  rw [criticalPoints_euclidean_eq]
  ext p
  rw [mem_euclideanCriticalPoints_iff, surjective_fderiv_lekiliMove4_iff, not_not,
    Set.mem_ofPred_eq]

/-- Parametric critical curve `x ↦ (x³ + s x, x, 0, 0)` for `lekiliMove4 s`. -/
noncomputable def lekiliMove4CritCurve (s x : ℝ) : EuclideanSpace ℝ (Fin 4) :=
  vec4 (x ^ 3 + s * x) x 0 0

/-- Parametric critical-value curve `x ↦ lekiliMove4 s (lekiliMove4CritCurve s x)`. -/
noncomputable def lekiliMove4CritValue (s x : ℝ) : EuclideanPlane :=
  lekiliMove4 s (lekiliMove4CritCurve s x)

/-- Exact derivative `(3 x² + s) • (1, -x)` along the swallowtail critical-value curve: regular
when `s > 0`, and acquiring two cusps `x = ±√(-s/3)` when `s < 0`. -/
theorem hasDerivAt_lekiliMove4CritValue (s x : ℝ) :
    HasDerivAt (lekiliMove4CritValue s) (vec2 (3 * x ^ 2 + s) (-(3 * x ^ 2 + s) * x)) x := by
  have heq : lekiliMove4CritValue s =
      fun t ↦ vec2 (t ^ 3 + s * t) (-3 / 4 * t ^ 4 - s / 2 * t ^ 2) := by
    funext t
    refine ext_vec2 rfl ?_
    simp only [lekiliMove4CritValue, lekiliMove4CritCurve, lekiliMove4, vec4_zero, vec4_one,
      vec4_two, vec4_three, vec2_one]
    ring
  rw [heq]
  have hid := hasDerivAt_id x
  have h0 : HasDerivAt (fun t : ℝ ↦ t ^ 3 + s * t) (3 * x ^ 2 + s) x := by
    refine ((hid.pow 3).add (hid.const_mul s)).congr_deriv ?_
    dsimp only [id_eq]
    ring
  have h1 : HasDerivAt (fun t : ℝ ↦ -3 / 4 * t ^ 4 - s / 2 * t ^ 2)
      (-(3 * x ^ 2 + s) * x) x := by
    refine (((hid.pow 4).const_mul (-3 / 4 : ℝ)).sub ((hid.pow 2).const_mul (s / 2))).congr_deriv ?_
    dsimp only [id_eq]
    ring
  exact hasDerivAt_vec2 h0 h1

/-- Every point on `lekiliMove4CritCurve s` lies in `criticalPoints (𝓡 4) (𝓡 2) (lekiliMove4 s)`. -/
-- tier: T1
theorem lekiliMove4CritCurve_mem_criticalPoints (s x : ℝ) :
    lekiliMove4CritCurve s x ∈ criticalPoints (𝓡 4) (𝓡 2) (lekiliMove4 s) := by
  rw [criticalPoints_lekiliMove4]
  exact ⟨rfl, rfl, rfl⟩

/-- Closed-form `IsIndefiniteFoldAt` along `lekiliMove4CritCurve s x` whenever
`3 * x ^ 2 + s ≠ 0` (`Lekili 2009`, §3.2 Move 4). -/
-- tier: T2
theorem isIndefiniteFoldAt_lekiliMove4 (s x : ℝ) (hx : 3 * x ^ 2 + s ≠ 0) :
    IsIndefiniteFoldAt (𝓡 4) (𝓡 2) (lekiliMove4 s) (lekiliMove4CritCurve s x) := by
  let p_star := lekiliMove4CritCurve s x
  let t₀ : ℝ := x ^ 3 + s * x
  let a : ℝ := 3 * x ^ 2 + s
  have ha_ne : a ≠ 0 := hx
  let h : ℝ → ℝ := fun u ↦ u ^ 3 + s * u
  have hh_diff : ContDiffOn ℝ ∞ h Set.univ :=
    ((contDiff_id.pow 3).add (contDiff_const.mul contDiff_id)).contDiffOn
  let eh : ℝ ≃L[ℝ] ℝ :=
    { toFun v := a * v
      invFun v := v / a
      map_add' u v := by ring
      map_smul' r v := by simp only [smul_eq_mul, RingHom.id_apply]; ring
      left_inv v := by field_simp [ha_ne]
      right_inv v := by field_simp [ha_ne]
      continuous_toFun := continuous_const.mul continuous_id
      continuous_invFun := continuous_id.div_const a }
  have heh : (eh : ℝ →L[ℝ] ℝ) = fderiv ℝ h x := by
    have hder : HasDerivAt h a x := by
      have hid := hasDerivAt_id x
      refine ((hid.pow 3).add (hid.const_mul s)).congr_deriv ?_
      dsimp only [id_eq, a]; ring
    rw [hder.hasFDerivAt.fderiv]
    apply ContinuousLinearMap.ext_ring
    simp [eh]
  obtain ⟨Θ, hΘ_coe, hx_Θ, _, hΘ_symm⟩ :=
    TauCeti.ContDiffOn.exists_openPartialHomeomorph hh_diff isOpen_univ (Set.mem_univ x)
      (by simp) heh
  let r : ℝ → ℝ := Θ.symm
  let V₀ : Set ℝ := Θ.target
  have hV₀_open : IsOpen V₀ := Θ.open_target
  have ht₀_eq : Θ x = t₀ := by rw [hΘ_coe]
  have ht₀_V₀ : t₀ ∈ V₀ := ht₀_eq ▸ Θ.map_source hx_Θ
  have hr_t₀ : r t₀ = x := by rw [← ht₀_eq]; exact Θ.left_inv hx_Θ
  have hr_eq : ∀ t ∈ V₀, r t ^ 3 + s * r t = t := fun t ht ↦ by
    change h (Θ.symm t) = t
    rw [← hΘ_coe]
    exact Θ.right_inv ht
  have hr_contOn : ContinuousOn r V₀ := hΘ_symm.continuousOn
  let ε : ℝ := if 0 < a then 1 else -1
  have hε2 : ε ^ 2 = 1 := by by_cases hpos : 0 < a <;> simp [ε, hpos]
  have hε_a : 0 < ε * a := by
    by_cases hpos : 0 < a
    · simp [ε, hpos]
    · have hneg : a < 0 := lt_of_le_of_ne (not_lt.mp hpos) ha_ne
      simp only [ε, hpos, ↓reduceIte, neg_one_mul, Left.neg_pos_iff]
      exact hneg
  let R : EuclideanSpace ℝ (Fin 4) → ℝ :=
    fun q ↦ ε * ((q 1 ^ 2 + 2 * r (q 0) * q 1 + 3 * r (q 0) ^ 2 + 2 * s) / 2)
  have hRp : R p_star = ε * a := by
    have hp0 : p_star 0 = t₀ := rfl
    have hp1 : p_star 1 = x := rfl
    simp only [R, hp0, hp1, hr_t₀, a]
    ring
  have hRp_pos : 0 < R p_star := hRp ▸ hε_a
  let U_tgt : Set EuclideanPlane := {w | w 0 ∈ V₀}
  have hU_tgt_open : IsOpen U_tgt := hV₀_open.preimage (euclidProj 0).continuous
  have hfp_tgt : lekiliMove4 s p_star ∈ U_tgt := ht₀_V₀
  let preV₀ : Set (EuclideanSpace ℝ (Fin 4)) := {q | q 0 ∈ V₀}
  have hpreV₀_open : IsOpen preV₀ := hV₀_open.preimage (euclidProj 0).continuous
  have hR_contOn : ContinuousOn R preV₀ := by
    have hr_q : ContinuousOn (fun q : EuclideanSpace ℝ (Fin 4) ↦ r (q 0)) preV₀ :=
      hr_contOn.comp (euclidProj 0).continuous.continuousOn (fun _ hq ↦ hq)
    have hq1 : ContinuousOn (fun q : EuclideanSpace ℝ (Fin 4) ↦ q 1) preV₀ :=
      (euclidProj 1).continuous.continuousOn
    exact continuousOn_const.mul
      (((((hq1.pow 2).add ((continuousOn_const.mul hr_q).mul hq1)).add
        (continuousOn_const.mul (hr_q.pow 2))).add continuousOn_const).div_const 2)
  let U_dom : Set (EuclideanSpace ℝ (Fin 4)) := {q ∈ preV₀ | 0 < R q}
  have hU_dom_open : IsOpen U_dom := hR_contOn.isOpen_inter_preimage hpreV₀_open isOpen_Ioi
  have hp_dom : p_star ∈ U_dom := ⟨ht₀_V₀, hRp_pos⟩
  have hR_contDiff : ContDiffOn ℝ ∞ R U_dom := by
    have hq0 : ContDiffOn ℝ ∞ (fun q : EuclideanSpace ℝ (Fin 4) ↦ q 0) U_dom :=
      (euclidProj 0).contDiff.contDiffOn
    have hq1 : ContDiffOn ℝ ∞ (fun q : EuclideanSpace ℝ (Fin 4) ↦ q 1) U_dom :=
      (euclidProj 1).contDiff.contDiffOn
    have hr_q : ContDiffOn ℝ ∞ (fun q : EuclideanSpace ℝ (Fin 4) ↦ r (q 0)) U_dom :=
      hΘ_symm.comp hq0 (fun _ hq ↦ hq.1)
    exact contDiff_const.contDiffOn.mul
      (((((hq1.pow 2).add ((contDiff_const.contDiffOn.mul hr_q).mul hq1)).add
        (contDiff_const.contDiffOn.mul (hr_q.pow 2))).add
        contDiff_const.contDiffOn).div_const 2)
  let posCoord : EuclideanSpace ℝ (Fin 4) → ℝ := fun q ↦ if 0 < a then q 3 else q 2
  let negCoord : EuclideanSpace ℝ (Fin 4) → ℝ := fun q ↦ if 0 < a then q 2 else q 3
  let posProj : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ :=
    if 0 < a then euclidProj (3 : Fin 4) else euclidProj (2 : Fin 4)
  let negProj : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ :=
    if 0 < a then euclidProj (2 : Fin 4) else euclidProj (3 : Fin 4)
  have hpos_cont : ContDiff ℝ ∞ posCoord := by
    by_cases hpos : 0 < a <;> simpa [posCoord, hpos] using (euclidProj _).contDiff
  have hneg_cont : ContDiff ℝ ∞ negCoord := by
    by_cases hpos : 0 < a <;> simpa [negCoord, hpos] using (euclidProj _).contDiff
  let cCrit : ℝ → ℝ := fun t ↦ -3 / 4 * r t ^ 4 - s / 2 * r t ^ 2
  have hcCrit_diff : ContDiffOn ℝ ∞ cCrit V₀ :=
    ((contDiff_const.contDiffOn.mul (hΘ_symm.pow 4)).sub
      (contDiff_const.contDiffOn.mul (hΘ_symm.pow 2)))
  let Φ : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4) := fun q ↦
    vec4 (posCoord q) ((q 1 - r (q 0)) * Real.sqrt (R q))
      (Real.sqrt 2 * negCoord q) (q 0 - t₀)
  let Ψ : EuclideanPlane → EuclideanPlane := fun w ↦
    vec2 (-ε * (w 1 - cCrit (w 0))) (w 0 - t₀)
  have hΦ_diff : ContDiffOn ℝ ∞ Φ U_dom := by
    have hq0 : ContDiffOn ℝ ∞ (fun q : EuclideanSpace ℝ (Fin 4) ↦ q 0) U_dom :=
      (euclidProj 0).contDiff.contDiffOn
    have hq1 : ContDiffOn ℝ ∞ (fun q : EuclideanSpace ℝ (Fin 4) ↦ q 1) U_dom :=
      (euclidProj 1).contDiff.contDiffOn
    have hr_q : ContDiffOn ℝ ∞ (fun q : EuclideanSpace ℝ (Fin 4) ↦ r (q 0)) U_dom :=
      hΘ_symm.comp hq0 (fun _ hq ↦ hq.1)
    have hR_sqrt : ContDiffOn ℝ ∞ (fun q ↦ Real.sqrt (R q)) U_dom :=
      hR_contDiff.sqrt fun _ hq ↦ hq.2.ne'
    exact contDiffOn_vec4 hpos_cont.contDiffOn ((hq1.sub hr_q).mul hR_sqrt)
      (contDiff_const.mul hneg_cont).contDiffOn (hq0.sub contDiff_const.contDiffOn)
  have hΨ_diff : ContDiffOn ℝ ∞ Ψ U_tgt := by
    have hw0 : ContDiffOn ℝ ∞ (fun w : EuclideanPlane ↦ w 0) U_tgt :=
      (euclidProj 0).contDiff.contDiffOn
    have hw1 : ContDiffOn ℝ ∞ (fun w : EuclideanPlane ↦ w 1) U_tgt :=
      (euclidProj 1).contDiff.contDiffOn
    have hc_w : ContDiffOn ℝ ∞ (fun w : EuclideanPlane ↦ cCrit (w 0)) U_tgt :=
      hcCrit_diff.comp hw0 (fun _ hw ↦ hw)
    exact contDiffOn_vec2 (contDiff_const.contDiffOn.mul (hw1.sub hc_w))
      (hw0.sub contDiff_const.contDiffOn)
  have hr_diffAt : DifferentiableAt ℝ r t₀ :=
    (hΘ_symm.contDiffAt (hV₀_open.mem_nhds ht₀_V₀)).differentiableAt (by simp)
  let dr : ℝ := deriv r t₀
  have hr_fderiv : HasFDerivAt r (dr • ContinuousLinearMap.id ℝ ℝ) t₀ := by
    refine hr_diffAt.hasDerivAt.hasFDerivAt.congr_fderiv ?_
    apply ContinuousLinearMap.ext_ring
    simp [dr]
  have hcCrit_diffAt : DifferentiableAt ℝ cCrit t₀ :=
    (hcCrit_diff.contDiffAt (hV₀_open.mem_nhds ht₀_V₀)).differentiableAt (by simp)
  let dc : ℝ := deriv cCrit t₀
  have hcCrit_fderiv : HasFDerivAt cCrit (dc • ContinuousLinearMap.id ℝ ℝ) t₀ := by
    refine hcCrit_diffAt.hasDerivAt.hasFDerivAt.congr_fderiv ?_
    apply ContinuousLinearMap.ext_ring
    simp [dc]
  let k : ℝ := Real.sqrt (R p_star)
  have hk_ne : k ≠ 0 := (Real.sqrt_pos.mpr hRp_pos).ne'
  have hrt2_ne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  let eΦ : EuclideanSpace ℝ (Fin 4) ≃L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    { toFun v := vec4 (posProj v) (k * (v 1 - dr * v 0)) (Real.sqrt 2 * negProj v) (v 0)
      invFun u := if 0 < a then
          vec4 (u 3) (u 1 / k + dr * u 3) (u 2 / Real.sqrt 2) (u 0)
        else
          vec4 (u 3) (u 1 / k + dr * u 3) (u 0) (u 2 / Real.sqrt 2)
      map_add' u v := by
        refine ext_vec4 ?_ ?_ ?_ ?_ <;>
          simp only [vec4_zero, vec4_one, vec4_two, vec4_three, map_add, PiLp.add_apply] <;> ring
      map_smul' r0 v := by
        refine ext_vec4 ?_ ?_ ?_ ?_ <;>
          simp only [vec4_zero, vec4_one, vec4_two, vec4_three, map_smul, PiLp.smul_apply,
            smul_eq_mul, RingHom.id_apply] <;> ring
      left_inv v := by
        by_cases hpos : 0 < a
        · refine ext_vec4 ?_ ?_ ?_ ?_
          · simp [hpos, vec4_zero, posProj, euclidProj]
          · simp only [hpos, ↓reduceIte, vec4_zero, vec4_one, vec4_three]; field_simp [hk_ne]; ring
          · simp only [hpos, ↓reduceIte, vec4_two, negProj, euclidProj, EuclideanSpace.proj,
              PiLp.proj_apply]
            exact mul_div_cancel_left₀ _ hrt2_ne
          · simp [posProj, hpos, euclidProj]
        · refine ext_vec4 ?_ ?_ ?_ ?_
          · simp [hpos, vec4_zero, posProj, euclidProj]
          · simp only [hpos, ↓reduceIte, vec4_zero, vec4_one, vec4_three]; field_simp [hk_ne]; ring
          · simp [posProj, hpos, euclidProj]
          · simp only [hpos, ↓reduceIte, vec4_two, negProj, euclidProj, EuclideanSpace.proj,
              PiLp.proj_apply]
            exact mul_div_cancel_left₀ _ hrt2_ne
      right_inv u := by
        by_cases hpos : 0 < a
        · refine ext_vec4 ?_ ?_ ?_ ?_
          · simp [hpos, posProj, euclidProj]
          · simp only [hpos, ↓reduceIte, vec4_zero, vec4_one]; field_simp [hk_ne]; ring
          · simp only [hpos, ↓reduceIte, negProj, euclidProj, EuclideanSpace.proj,
              PiLp.proj_apply, vec4_two]
            exact mul_div_cancel₀ _ hrt2_ne
          · simp [hpos]
        · refine ext_vec4 ?_ ?_ ?_ ?_
          · simp [hpos, posProj, euclidProj]
          · simp only [hpos, ↓reduceIte, vec4_zero, vec4_one]; field_simp [hk_ne]; ring
          · simp only [hpos, ↓reduceIte, negProj, euclidProj, EuclideanSpace.proj,
              PiLp.proj_apply, vec4_three]
            exact mul_div_cancel₀ _ hrt2_ne
          · simp [hpos]
      continuous_toFun := continuous_vec4 posProj.continuous
        (continuous_const.mul ((euclidProj 1).continuous.sub
          (continuous_const.mul (euclidProj 0).continuous)))
        (continuous_const.mul negProj.continuous) (euclidProj 0).continuous
      continuous_invFun := by
        by_cases hpos : 0 < a
        · simp only [hpos, ↓reduceIte]
          exact continuous_vec4 (euclidProj 3).continuous
            (((euclidProj 1).continuous.div_const k).add
              (continuous_const.mul (euclidProj 3).continuous))
            ((euclidProj 2).continuous.div_const (Real.sqrt 2)) (euclidProj 0).continuous
        · simp only [hpos, ↓reduceIte]
          exact continuous_vec4 (euclidProj 3).continuous
            (((euclidProj 1).continuous.div_const k).add
              (continuous_const.mul (euclidProj 3).continuous))
            (euclidProj 0).continuous ((euclidProj 2).continuous.div_const (Real.sqrt 2)) }
  let eΨ : EuclideanPlane ≃L[ℝ] EuclideanPlane :=
    { toFun v := vec2 (-ε * (v 1 - dc * v 0)) (v 0)
      invFun u := vec2 (u 1) (-ε * u 0 + dc * u 1)
      map_add' u v := by
        refine ext_vec2 ?_ (by simp)
        simp only [vec2_zero, PiLp.add_apply]; ring
      map_smul' r0 v := by
        refine ext_vec2 ?_ (by simp)
        simp only [vec2_zero, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
      left_inv v := by
        refine ext_vec2 rfl ?_
        simp only [vec2_zero, vec2_one]
        calc
          -ε * (-ε * (v 1 - dc * v 0)) + dc * v 0
            = ε ^ 2 * (v 1 - dc * v 0) + dc * v 0 := by ring
          _ = v 1 := by rw [hε2, one_mul]; ring
      right_inv u := by
        refine ext_vec2 ?_ rfl
        simp only [vec2_zero, vec2_one]
        calc
          -ε * (-ε * u 0 + dc * u 1 - dc * u 1) = ε ^ 2 * u 0 := by ring
          _ = u 0 := by rw [hε2, one_mul]
      continuous_toFun := continuous_vec2
        (continuous_const.mul ((euclidProj 1).continuous.sub
          (continuous_const.mul (euclidProj 0).continuous)))
        (euclidProj 0).continuous
      continuous_invFun := continuous_vec2 (euclidProj 1).continuous
        ((continuous_const.mul (euclidProj 0).continuous).add
          (continuous_const.mul (euclidProj 1).continuous)) }
  have heΦ : (eΦ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) =
      fderiv ℝ Φ p_star := by
    have hq (i : Fin 4) : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 4) ↦ z i)
        (euclidProj i) p_star := (euclidProj i).hasFDerivAt
    have hpos_der : HasFDerivAt posCoord posProj p_star := by
      by_cases hpos : 0 < a <;> simp only [posCoord, posProj, hpos, ↓reduceIte] <;> exact hq _
    have hneg_der : HasFDerivAt negCoord negProj p_star := by
      by_cases hpos : 0 < a <;> simp only [negCoord, negProj, hpos, ↓reduceIte] <;> exact hq _
    have hp0_eq : p_star 0 = t₀ := rfl
    have hdiff_der : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 4) ↦ q 1 - r (q 0))
        (euclidProj (1 : Fin 4) - dr • euclidProj (0 : Fin 4)) p_star := by
      refine ((hq 1).sub ((hp0_eq ▸ hr_fderiv).comp p_star (hq 0))).congr_fderiv ?_
      ext v; simp [sub_apply, smul_apply]
    have hR_sqrt_diff : DifferentiableAt ℝ (fun q ↦ Real.sqrt (R q)) p_star :=
      ((hR_contDiff.sqrt fun _ hqU ↦ hqU.2.ne').contDiffAt
        (hU_dom_open.mem_nhds hp_dom)).differentiableAt (by simp)
    have h1_der : HasFDerivAt (fun q ↦ (q 1 - r (q 0)) * Real.sqrt (R q))
        (k • (euclidProj (1 : Fin 4) - dr • euclidProj (0 : Fin 4))) p_star := by
      have hm := hdiff_der.mul hR_sqrt_diff.hasFDerivAt
      refine hm.congr_fderiv ?_
      ext v
      have hp_zero : p_star 1 - r (p_star 0) = 0 := by
        simp [p_star, lekiliMove4CritCurve, hr_t₀, t₀]
      simp only [smul_apply, sub_apply, hp_zero, zero_smul, zero_add, k, smul_eq_mul]
    have h2_der : HasFDerivAt (fun q ↦ Real.sqrt 2 * negCoord q)
        ((Real.sqrt 2) • negProj) p_star := hneg_der.const_mul (Real.sqrt 2)
    have h3_der : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 4) ↦ q 0 - t₀)
        (euclidProj (0 : Fin 4)) p_star := (hq 0).sub_const t₀
    rw [(hasFDerivAt_vec4' hpos_der h1_der h2_der h3_der).fderiv]
    ext v i
    fin_cases i <;>
      simp only [eΦ, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_mk,
        LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, clmVec4_apply,
        smul_apply, sub_apply, euclidProj, EuclideanSpace.proj, PiLp.proj_apply, smul_eq_mul]
  have heΨ : (eΨ : EuclideanPlane →L[ℝ] EuclideanPlane) =
      fderiv ℝ Ψ (lekiliMove4 s p_star) := by
    have hw (i : Fin 2) : HasFDerivAt (fun z : EuclideanPlane ↦ z i)
        (euclidProj i) (lekiliMove4 s p_star) := (euclidProj i).hasFDerivAt
    have hc_der : HasFDerivAt (fun w : EuclideanPlane ↦ cCrit (w 0))
        (dc • euclidProj (0 : Fin 2)) (lekiliMove4 s p_star) := by
      refine (hcCrit_fderiv.comp (lekiliMove4 s p_star) (hw 0)).congr_fderiv ?_
      ext v; simp [smul_apply]
    have h0_der : HasFDerivAt (fun w : EuclideanPlane ↦ -ε * (w 1 - cCrit (w 0)))
        ((-ε) • (euclidProj (1 : Fin 2) - dc • euclidProj (0 : Fin 2)))
        (lekiliMove4 s p_star) :=
      ((hw 1).sub hc_der).const_mul (-ε)
    have h1_der : HasFDerivAt (fun w : EuclideanPlane ↦ w 0 - t₀)
        (euclidProj (0 : Fin 2)) (lekiliMove4 s p_star) := (hw 0).sub_const t₀
    rw [(hasFDerivAt_vec2 h0_der h1_der).fderiv]
    ext v i
    fin_cases i <;>
      simp only [eΨ, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_mk,
        LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, clmVec2_apply,
        smul_apply, sub_apply, euclidProj, EuclideanSpace.proj, PiLp.proj_apply, smul_eq_mul]
  have hΦ_p : Φ p_star = 0 := by
    refine ext_vec4 ?_ ?_ ?_ ?_
    · by_cases hpos : 0 < a <;> simp [Φ, posCoord, hpos, p_star, lekiliMove4CritCurve]
    · simp [Φ, p_star, lekiliMove4CritCurve, hr_t₀, t₀]
    · by_cases hpos : 0 < a <;> simp [Φ, negCoord, hpos, p_star, lekiliMove4CritCurve]
    · simp [Φ, p_star, lekiliMove4CritCurve, t₀]
  have hΨ_fp : Ψ (lekiliMove4 s p_star) = indefiniteFoldMap 0 := by
    refine ext_vec2 ?_ ?_
    · simp only [Ψ, lekiliMove4, p_star, lekiliMove4CritCurve, cCrit, indefiniteFoldMap,
        vec2_zero, vec2_one, vec4_zero, vec4_one, vec4_two, vec4_three, PiLp.zero_apply,
        t₀, hr_t₀]
      ring
    · simp [Ψ, lekiliMove4, p_star, lekiliMove4CritCurve, indefiniteFoldMap, t₀]
  refine isLocallyModeledOn_of_contDiff_maps hU_dom_open hp_dom hU_tgt_open hfp_tgt
    hΦ_diff hΨ_diff eΦ heΦ eΨ heΨ hΦ_p hΨ_fp ?_
    (contDiff_lekiliMove4 s).continuous.continuousAt
  filter_upwards [hU_dom_open.mem_nhds hp_dom] with q hq
  have hq_tgt : lekiliMove4 s q ∈ U_tgt := hq.1
  refine ⟨hq_tgt, ?_⟩
  have hq0_eq : q 0 = r (q 0) ^ 3 + s * r (q 0) := (hr_eq (q 0) hq.1).symm
  have hR_sq : Real.sqrt (R q) ^ 2 = R q := Real.sq_sqrt hq.2.le
  have hrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  refine ext_vec2 ?_ rfl
  simp only [Ψ, Φ, lekiliMove4, indefiniteFoldMap, cCrit, vec2_zero, vec2_one,
    vec4_zero, vec4_one, vec4_two]
  have hsq1 : ((q 1 - r (q 0)) * Real.sqrt (R q)) ^ 2 = (q 1 - r (q 0)) ^ 2 * R q := by
    rw [mul_pow, hR_sq]
  have hsq2 : (Real.sqrt 2 * negCoord q) ^ 2 = 2 * negCoord q ^ 2 := by
    rw [mul_pow, hrt2_sq]
  rw [hsq1, hsq2]
  dsimp only [cCrit, R]
  generalize r (q 0) = rq at hq0_eq ⊢
  rw [hq0_eq]
  by_cases hpos : 0 < a
  · simp only [ε, posCoord, negCoord, hpos, ↓reduceIte]
    ring
  · simp only [ε, posCoord, negCoord, hpos, ↓reduceIte]
    ring

/-- Every critical point `p ∈ criticalPoints (𝓡 4) (𝓡 2) (lekiliMove4 s)` with
`3 * p 1 ^ 2 + s ≠ 0` is an indefinite quadratic fold. -/
-- tier: T1
theorem isIndefiniteFoldAt_lekiliMove4_of_mem_criticalPoints (s : ℝ)
    {p : EuclideanSpace ℝ (Fin 4)}
    (hp : p ∈ criticalPoints (𝓡 4) (𝓡 2) (lekiliMove4 s)) (hx : 3 * p 1 ^ 2 + s ≠ 0) :
    IsIndefiniteFoldAt (𝓡 4) (𝓡 2) (lekiliMove4 s) p := by
  rw [criticalPoints_lekiliMove4, Set.mem_ofPred_eq] at hp
  have hp_eq : p = lekiliMove4CritCurve s (p 1) :=
    ext_vec4 hp.1 rfl hp.2.1 hp.2.2
  rw [hp_eq]
  exact isIndefiniteFoldAt_lekiliMove4 s (p 1) hx

private noncomputable def flipMove4Tgt : EuclideanPlane ≃L[ℝ] EuclideanPlane where
  toFun w := vec2 (-w 0) (w 1)
  invFun w := vec2 (-w 0) (w 1)
  map_add' u v := by refine ext_vec2 ?_ ?_ <;> simp [add_comm]
  map_smul' r v := by refine ext_vec2 ?_ ?_ <;> simp
  left_inv v := by refine ext_vec2 ?_ ?_ <;> simp
  right_inv v := by refine ext_vec2 ?_ ?_ <;> simp
  continuous_toFun := continuous_vec2 (euclidProj 0).continuous.neg (euclidProj 1).continuous
  continuous_invFun := continuous_vec2 (euclidProj 0).continuous.neg (euclidProj 1).continuous

private theorem flipMove4Tgt_lekiliMove4 (s : ℝ) (p : EuclideanSpace ℝ (Fin 4)) :
    flipMove4Tgt (lekiliMove4 s p) = lekiliMove4 s (flipSignDom p) := by
  refine ext_vec2 ?_ ?_
  · simp [flipMove4Tgt, flipSignDom_apply, lekiliMove4]
  · simp only [flipMove4Tgt, ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk,
      LinearMap.coe_mk, AddHom.coe_mk, flipSignDom_apply, lekiliMove4,
      vec2_one, vec4_zero, vec4_one, vec4_two, vec4_three]
    ring

/-- Positive-cusp normal form (`IsWrinkledCuspAt`) at `x = +√(-s/3)` (`s < 0`) for
`lekiliMove4 s` via real Weierstrass preparation factoring `x_* u³ + u⁴/4 = u³ (x_* + u/4)`. -/
-- tier: T2
theorem isWrinkledCuspAt_lekiliMove4_pos {s : ℝ} (hs : s < 0) :
    IsWrinkledCuspAt (𝓡 4) (𝓡 2) (lekiliMove4 s)
      (lekiliMove4CritCurve s (Real.sqrt (-s / 3))) := by
  let x_star : ℝ := Real.sqrt (-s / 3)
  have hx_arg_pos : 0 < -s / 3 := by linarith
  have hx_star_pos : 0 < x_star := Real.sqrt_pos.mpr hx_arg_pos
  have hx_star_ne : x_star ≠ 0 := hx_star_pos.ne'
  have hx_star_sq : x_star ^ 2 = -s / 3 := Real.sq_sqrt hx_arg_pos.le
  have hs_eq : s = -3 * x_star ^ 2 := by linarith
  let p_star := lekiliMove4CritCurve s x_star
  let t_star : ℝ := x_star ^ 3 + s * x_star
  have ht_star_eq : t_star = -2 * x_star ^ 3 := by
    dsimp only [t_star]; rw [hs_eq]; ring
  let G : (Fin 2 → ℝ) × ℝ → ℝ :=
    fun q ↦ x_star * q.2 ^ 3 + q.2 ^ 4 / 4 - q.1 0 * q.2 - q.1 1
  have hG_an : AnalyticAt ℝ G ((0 : Fin 2 → ℝ), (0 : ℝ)) := by
    have hq10 : AnalyticAt ℝ (fun q : (Fin 2 → ℝ) × ℝ ↦ q.1 0) (0, 0) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0).analyticAt _).comp
        analyticAt_fst
    have hq11 : AnalyticAt ℝ (fun q : (Fin 2 → ℝ) × ℝ ↦ q.1 1) (0, 0) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1).analyticAt _).comp
        analyticAt_fst
    have hq2 : AnalyticAt ℝ (fun q : (Fin 2 → ℝ) × ℝ ↦ q.2) (0, 0) := analyticAt_snd
    exact (((analyticAt_const.mul (hq2.pow 3)).add
      ((hq2.pow 4).div analyticAt_const (by norm_num))).sub (hq10.mul hq2)).sub hq11
  have hG_slice : (fun y : ℝ ↦ G (0, y)) =ᶠ[𝓝 0] fun y ↦ y ^ 3 * (x_star + y / 4) :=
    Eventually.of_forall fun y ↦ by dsimp only [G]; simp only [Pi.zero_apply]; ring
  have hord : analyticOrderAt (fun y : ℝ ↦ G (0, y)) 0 = (3 : ℕ) := by
    rw [analyticOrderAt_congr hG_slice]
    have hq_an : AnalyticAt ℝ (fun y : ℝ ↦ x_star + y / 4) 0 :=
      analyticAt_const.add (analyticAt_id.div analyticAt_const (by norm_num))
    have hq_ne : (x_star + (0 : ℝ) / 4) ≠ 0 := by simp [hx_star_ne]
    have hpow_an : AnalyticAt ℝ ((id : ℝ → ℝ) ^ 3) 0 := analyticAt_id.pow 3
    have hmul : analyticOrderAt (((id : ℝ → ℝ) ^ 3) * (fun y : ℝ ↦ x_star + y / 4)) 0 =
        analyticOrderAt ((id : ℝ → ℝ) ^ 3) 0 +
          analyticOrderAt (fun y : ℝ ↦ x_star + y / 4) 0 :=
      analyticOrderAt_mul hpow_an hq_an
    change analyticOrderAt (((id : ℝ → ℝ) ^ 3) * (fun y : ℝ ↦ x_star + y / 4)) 0 = (3 : ℕ)
    rw [hmul, analyticOrderAt_pow analyticAt_id 3, analyticOrderAt_id,
      (hq_an.analyticOrderAt_eq_zero).2 hq_ne]
    simp
  obtain ⟨c, u, hc_an, hc0, hu_an, _, heq_wp⟩ :=
    hG_an.exists_weierstrassPreparation_real hord
  have hu_val : u (0, 0) = x_star := by
    have hcomb : (fun y : ℝ ↦ y ^ 3 * u (0, y)) =ᶠ[𝓝 0] fun y ↦ y ^ 3 * (x_star + y / 4) := by
      have hslice_ev : (fun y : ℝ ↦ G (0, y)) =ᶠ[𝓝 0] fun y ↦ y ^ 3 * u (0, y) := by
        have ht : Tendsto (fun y : ℝ ↦ ((0 : Fin 2 → ℝ), y)) (𝓝 0) (𝓝 (0, 0)) :=
          ContinuousAt.tendsto (continuousAt_const.prodMk continuousAt_id)
        filter_upwards [ht.eventually heq_wp] with y hy
        rw [hy, TauCeti.Polynomial.eval_monicOfCoeff, Fin.sum_univ_three]
        simp [hc0, sub_zero]
      exact hslice_ev.symm.trans hG_slice
    have hu_eq : (fun y : ℝ ↦ u (0, y)) =ᶠ[𝓝[≠] 0] fun y ↦ x_star + y / 4 := by
      filter_upwards [nhdsWithin_le_nhds hcomb, self_mem_nhdsWithin] with y hy hy0
      exact mul_left_cancel₀ (pow_ne_zero 3 hy0) hy
    have ht1 : Tendsto (fun y : ℝ ↦ u (0, y)) (𝓝[≠] 0) (𝓝 (u (0, 0))) :=
      (hu_an.continuousAt.comp (continuousAt_const.prodMk continuousAt_id)).mono_left
        nhdsWithin_le_nhds
    have ht2 : Tendsto (fun y : ℝ ↦ x_star + y / 4) (𝓝[≠] 0) (𝓝 (x_star + (0 : ℝ) / 4)) :=
      ((continuousAt_const.add (continuousAt_id.div_const 4)).tendsto).mono_left nhdsWithin_le_nhds
    have hlim := tendsto_nhds_unique ht1 (ht2.congr' hu_eq.symm)
    simpa using hlim
  have hu_pos : 0 < u (0, 0) := hu_val ▸ hx_star_pos
  have hc0_fderiv : fderiv ℝ (c 0) 0 = (-x_star⁻¹) • ContinuousLinearMap.proj 1 := by
    have hprod_ev : (fun w : Fin 2 → ℝ ↦ c 0 w * u (w, 0)) =ᶠ[𝓝 0] fun w ↦ -w 1 := by
      have ht : Tendsto (fun w : Fin 2 → ℝ ↦ (w, (0 : ℝ))) (𝓝 0) (𝓝 (0, 0)) :=
        ContinuousAt.tendsto (continuousAt_id.prodMk continuousAt_const)
      filter_upwards [ht.eventually heq_wp] with w hw
      have hG0 : G (w, 0) = -w 1 := by simp [G]
      rw [← hG0, hw, TauCeti.Polynomial.eval_monicOfCoeff, Fin.sum_univ_three]
      simp
    have h1 : HasFDerivAt (fun w : Fin 2 → ℝ ↦ c 0 w * u (w, 0))
        (u (0, 0) • fderiv ℝ (c 0) 0) 0 := by
      have hc0d : HasFDerivAt (c 0) (fderiv ℝ (c 0) 0) 0 :=
        (hc_an 0).differentiableAt.hasFDerivAt
      have hud : HasFDerivAt (fun w : Fin 2 → ℝ ↦ u (w, (0 : ℝ)))
          (fderiv ℝ (fun w : Fin 2 → ℝ ↦ u (w, (0 : ℝ))) 0) 0 := by
        have hmap : AnalyticAt ℝ (fun w : Fin 2 → ℝ ↦ (w, (0 : ℝ))) 0 :=
          (analyticAt_id (𝕜 := ℝ) (E := Fin 2 → ℝ)).prod
            (analyticAt_const (𝕜 := ℝ) (v := (0 : ℝ)))
        exact (hu_an.comp_of_eq hmap rfl).differentiableAt.hasFDerivAt
      refine (hc0d.mul hud).congr_fderiv ?_
      ext v
      simp [smul_apply, hc0 0, zero_smul]
    have h2 : HasFDerivAt (fun w : Fin 2 → ℝ ↦ -w 1)
        (-(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1)) 0 :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1).hasFDerivAt).neg
    have hfeq := h1.unique (h2.congr_of_eventuallyEq hprod_ev)
    rw [hu_val] at hfeq
    ext v
    have hv := congrArg (fun F : (Fin 2 → ℝ) →L[ℝ] ℝ ↦ x_star⁻¹ * F v) hfeq
    simp only [smul_apply, neg_apply, ContinuousLinearMap.proj_apply, smul_eq_mul] at hv ⊢
    calc
      fderiv ℝ (c 0) 0 v = x_star⁻¹ * (x_star * fderiv ℝ (c 0) 0 v) := by
        field_simp [hx_star_ne]
      _ = x_star⁻¹ * -v 1 := hv
      _ = -x_star⁻¹ * v 1 := by ring
  let v₀ : Fin 2 → ℝ := ![1, 0]
  have hc1_v0 : (fderiv ℝ (c 1) 0) v₀ = -x_star⁻¹ := by
    have hG_t_eq : ∀ᶠ ty in 𝓝 ((0 : ℝ), (0 : ℝ)),
        G (ty.1 • v₀, ty.2) =
          (ty.2 ^ 3 + ∑ i : Fin 3, c i (ty.1 • v₀) * ty.2 ^ (i : ℕ)) * u (ty.1 • v₀, ty.2) ∧
          AnalyticAt ℝ u (ty.1 • v₀, ty.2) := by
      have ht1 : ContinuousAt (fun ty : ℝ × ℝ ↦ (ty.1 • v₀, ty.2)) (0, 0) :=
        (continuousAt_fst.smul continuousAt_const).prodMk continuousAt_snd
      have h00 : ((0 : ℝ) • v₀, (0 : ℝ)) = ((0 : Fin 2 → ℝ), (0 : ℝ)) := by simp
      filter_upwards [ht1.tendsto.eventually (h00 ▸ heq_wp),
        ht1.tendsto.eventually (h00 ▸ hu_an.eventually_analyticAt)] with ty hty1 hty2
      refine ⟨?_, hty2⟩
      rw [hty1, TauCeti.Polynomial.eval_monicOfCoeff, sub_zero]
    obtain ⟨r, hr_pos, hr_sub⟩ := Metric.eventually_nhds_iff.mp hG_t_eq
    have hc_deriv (i : Fin 3) :
        HasDerivAt (fun t : ℝ ↦ c i (t • v₀)) ((fderiv ℝ (c i) 0) v₀) 0 := by
      rw [hasDerivAt_iff_hasFDerivAt]
      have h0v : (0 : ℝ) • v₀ = 0 := zero_smul _ _
      have hf := (hc_an i).differentiableAt.hasFDerivAt
      rw [← h0v] at hf
      refine (hf.comp (0 : ℝ) ((hasFDerivAt_id (0 : ℝ)).smul_const v₀)).congr_fderiv ?_
      apply ContinuousLinearMap.ext_ring
      simp [one_smul]
    have hc0_v0 : (fderiv ℝ (c 0) 0) v₀ = 0 := by simp [hc0_fderiv, v₀]
    have hu_cont_t : ContinuousAt (fun y : ℝ ↦ (fderiv ℝ u (0, y)) (v₀, 0)) 0 := by
      have hudiff : ContinuousAt (fderiv ℝ u) (0, 0) :=
        ((hu_an.contDiffAt (n := ∞)).fderiv_right (m := 0) (by simp)).continuousAt
      have hev_eval : ContinuousAt
          (fun F : (Fin 2 → ℝ) × ℝ →L[ℝ] ℝ ↦ F (v₀, 0)) (fderiv ℝ u (0, 0)) :=
        (ContinuousLinearMap.apply ℝ ℝ (v₀, (0 : ℝ))).continuous.continuousAt
      exact hev_eval.tendsto.comp
        (hudiff.tendsto.comp (continuousAt_const.prodMk continuousAt_id).tendsto)
    have hderiv_eq : (fun _ : ℝ ↦ (-1 : ℝ)) =ᶠ[𝓝[≠] 0] fun y : ℝ ↦
        ((fderiv ℝ (c 2) 0) v₀ * y + (fderiv ℝ (c 1) 0) v₀) * u (0, y) +
          y ^ 2 * (fderiv ℝ u (0, y)) (v₀, 0) := by
      have hball : Metric.ball (0 : ℝ) (r / 2) ∈ 𝓝 (0 : ℝ) :=
        Metric.ball_mem_nhds 0 (half_pos hr_pos)
      filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with y hy hy0
      have hy_abs : |y| < r / 2 := by simpa [Metric.mem_ball, Real.dist_eq] using hy
      have h0y_ball : dist ((0 : ℝ), y) (0, 0) < r := by
        calc
          dist ((0 : ℝ), y) (0, 0) = |y| := by simp [Prod.dist_eq]
          _ < r / 2 := hy_abs
          _ < r := by linarith
      have hu_y_an : AnalyticAt ℝ u (0, y) := by simpa using (hr_sub h0y_ball).2
      have h_ty_eq : (fun t : ℝ ↦ G (t • v₀, y)) =ᶠ[𝓝 0] fun t : ℝ ↦
          (y ^ 3 + (c 0 (t • v₀) * 1 + c 1 (t • v₀) * y + c 2 (t • v₀) * y ^ 2)) *
            u (t • v₀, y) := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (half_pos hr_pos)] with t ht
        have ht_abs : |t| < r / 2 := by simpa [Metric.mem_ball, Real.dist_eq] using ht
        have hty_ball : dist (t, y) (0, 0) < r := by
          rw [Prod.dist_eq]
          exact max_lt (by simpa [Real.dist_eq] using ht_abs.trans (by linarith))
            (by simpa [Real.dist_eq] using hy_abs.trans (by linarith))
        have h1 := (hr_sub hty_ball).1
        rw [Fin.sum_univ_three] at h1
        simpa [pow_zero, pow_one] using h1
      have hL : HasDerivAt (fun t : ℝ ↦ G (t • v₀, y)) (-y) 0 := by
        have hg0 : (fun t : ℝ ↦ G (t • v₀, y)) =
            fun t : ℝ ↦ (x_star * y ^ 3 + y ^ 4 / 4) - t * y := by
          funext t; simp [G, v₀]
        rw [hg0]
        refine (((hasDerivAt_id (0 : ℝ)).mul_const y).const_sub _).congr_deriv ?_
        ring
      have hpoly : HasDerivAt
          (fun t : ℝ ↦ y ^ 3 + (c 0 (t • v₀) * 1 + c 1 (t • v₀) * y + c 2 (t • v₀) * y ^ 2))
          ((fderiv ℝ (c 1) 0) v₀ * y + (fderiv ℝ (c 2) 0) v₀ * y ^ 2) 0 := by
        have hp1 := ((hc_deriv 0).mul_const 1).add ((hc_deriv 1).mul_const y)
        have hp2 := (hp1.add ((hc_deriv 2).mul_const (y ^ 2))).const_add (y ^ 3)
        refine hp2.congr_deriv ?_
        rw [hc0_v0]; ring
      have hu_t : HasDerivAt (fun t : ℝ ↦ u (t • v₀, y)) ((fderiv ℝ u (0, y)) (v₀, 0)) 0 := by
        rw [hasDerivAt_iff_hasFDerivAt]
        have h0vy : ((0 : ℝ) • v₀, y) = ((0 : Fin 2 → ℝ), y) := by simp
        have hpath : HasFDerivAt (fun t : ℝ ↦ (t • v₀, y))
            (((ContinuousLinearMap.id ℝ ℝ).smulRight v₀).prod (0 : ℝ →L[ℝ] ℝ)) 0 :=
          ((hasFDerivAt_id (0 : ℝ)).smul_const v₀).prodMk (hasFDerivAt_const y (0 : ℝ))
        have hu_f := hu_y_an.differentiableAt.hasFDerivAt
        rw [← h0vy] at hu_f
        refine (hu_f.comp (0 : ℝ) hpath).congr_fderiv ?_
        apply ContinuousLinearMap.ext_ring; simp
      have hR := (hpoly.mul hu_t).congr_of_eventuallyEq h_ty_eq
      have heq_d := hL.unique hR
      simp only [zero_smul, hc0, zero_mul, add_zero] at heq_d
      apply mul_left_cancel₀ hy0
      linear_combination heq_d
    have ht_rhs : Tendsto
        (fun y : ℝ ↦
          ((fderiv ℝ (c 2) 0) v₀ * y + (fderiv ℝ (c 1) 0) v₀) * u (0, y) +
            y ^ 2 * (fderiv ℝ u (0, y)) (v₀, 0))
        (𝓝[≠] 0)
        (𝓝 (((fderiv ℝ (c 2) 0) v₀ * 0 + (fderiv ℝ (c 1) 0) v₀) * u (0, 0) +
          0 ^ 2 * (fderiv ℝ u (0, 0)) (v₀, 0))) := by
      have hcu : ContinuousAt (fun y : ℝ ↦ u (0, y)) 0 :=
        hu_an.continuousAt.comp (continuousAt_const.prodMk continuousAt_id)
      have hc_lin : ContinuousAt (fun y : ℝ ↦ (fderiv ℝ (c 2) 0) v₀ * y + (fderiv ℝ (c 1) 0) v₀)
          0 := by fun_prop
      have hc_sq : ContinuousAt (fun y : ℝ ↦ y ^ 2) 0 := by fun_prop
      exact ((hc_lin.mul hcu).add (hc_sq.mul hu_cont_t)).tendsto.mono_left nhdsWithin_le_nhds
    have hlim := tendsto_nhds_unique tendsto_const_nhds (ht_rhs.congr' hderiv_eq.symm)
    rw [hu_val] at hlim
    have hlim' : -1 = (fderiv ℝ (c 1) 0) v₀ * x_star := by simpa using hlim
    calc
      (fderiv ℝ (c 1) 0) v₀ = ((fderiv ℝ (c 1) 0) v₀ * x_star) * x_star⁻¹ := by
        field_simp [hx_star_ne]
      _ = (-1) * x_star⁻¹ := by rw [← hlim']
      _ = -x_star⁻¹ := by ring
  let dwShift : EuclideanPlane →L[ℝ] (Fin 2 → ℝ) :=
    ContinuousLinearMap.pi
      ![euclidProj (0 : Fin 2), euclidProj (1 : Fin 2) + x_star • euclidProj (0 : Fin 2)]
  have hdwShift_decomp (w : EuclideanPlane) :
      dwShift w = w 0 • v₀ + (w 1 + x_star * w 0) • ![0, 1] := by
    ext i; fin_cases i <;> simp [dwShift, v₀, euclidProj]
  let wShift : EuclideanPlane → (Fin 2 → ℝ) :=
    fun w ↦ ![w 0 - t_star, w 1 - (3 / 4 * x_star ^ 4 - x_star * (w 0 - t_star))]
  have hwShift_pstar : wShift (lekiliMove4 s p_star) = 0 := by
    ext i
    fin_cases i
    · dsimp only [wShift, p_star, lekiliMove4CritCurve, lekiliMove4, t_star]
      simp [vec2_zero, vec4_zero]
    · dsimp only [wShift, p_star, lekiliMove4CritCurve, lekiliMove4, t_star]
      simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply,
        vec2_zero, vec2_one, vec4_zero, vec4_one, vec4_two, vec4_three, hs_eq]
      ring
  have hwShift_diff : ContDiff ℝ ∞ wShift := by
    refine contDiff_pi.mpr fun i ↦ ?_
    fin_cases i
    · exact (euclidProj 0).contDiff.sub contDiff_const
    · exact (euclidProj 1).contDiff.sub
        (contDiff_const.sub (contDiff_const.mul ((euclidProj 0).contDiff.sub contDiff_const)))
  have hwShift_fderiv (w : EuclideanPlane) : HasFDerivAt wShift dwShift w := by
    refine hasFDerivAt_pi.mpr fun i ↦ ?_
    fin_cases i
    · simpa [dwShift] using ((euclidProj (0 : Fin 2)).hasFDerivAt (x := w)).sub_const t_star
    · have hw0 := ((euclidProj (0 : Fin 2)).hasFDerivAt (x := w)).sub_const t_star
      have hm := (hw0.const_mul x_star).const_sub (3 / 4 * x_star ^ 4)
      refine (((euclidProj (1 : Fin 2)).hasFDerivAt (x := w)).sub hm).congr_fderiv ?_
      ext v
      simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, sub_apply, neg_apply,
        add_apply, smul_apply, euclidProj, EuclideanSpace.proj, PiLp.proj_apply, smul_eq_mul]
      ring
  have hev_c : ∀ᶠ w : Fin 2 → ℝ in 𝓝 0,
      AnalyticAt ℝ (c 0) w ∧ AnalyticAt ℝ (c 1) w ∧ AnalyticAt ℝ (c 2) w :=
    (hc_an 0).eventually_analyticAt.and
      ((hc_an 1).eventually_analyticAt.and (hc_an 2).eventually_analyticAt)
  obtain ⟨U_c, hU_c_sub, hU_c_open, h0_Uc⟩ := _root_.eventually_nhds_iff.mp hev_c
  have hc_contDiff (i : Fin 3) : ContDiffOn ℝ ∞ (c i) U_c := fun w hw ↦ by
    have ha : AnalyticAt ℝ (c i) w := by
      fin_cases i
      · exact (hU_c_sub w hw).1
      · exact (hU_c_sub w hw).2.1
      · exact (hU_c_sub w hw).2.2
    exact ha.contDiffAt.contDiffWithinAt
  obtain ⟨U_u, hU_u_sub, hU_u_open, h0_Uu⟩ :=
    _root_.eventually_nhds_iff.mp hu_an.eventually_analyticAt
  have hu_contDiff : ContDiffOn ℝ ∞ u U_u := fun q hq ↦ (hU_u_sub q hq).contDiffAt.contDiffWithinAt
  let TFn : EuclideanPlane → ℝ := fun w ↦ c 2 (wShift w) ^ 2 / 9 - c 1 (wShift w) / 3
  let WFn : EuclideanPlane → ℝ := fun w ↦
    -(c 0 (wShift w) - c 1 (wShift w) * c 2 (wShift w) / 3 + 2 * c 2 (wShift w) ^ 3 / 27)
  let QFn : EuclideanSpace ℝ (Fin 4) → ℝ :=
    fun p ↦ (p 1 - x_star) + c 2 (wShift (lekiliMove4 s p)) / 3
  let invSqrtU : EuclideanSpace ℝ (Fin 4) → ℝ :=
    fun p ↦ (Real.sqrt (u (wShift (lekiliMove4 s p), p 1 - x_star)))⁻¹
  let Φ : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4) := fun p ↦
    vec4 (TFn (lekiliMove4 s p)) (QFn p) (p 2 * invSqrtU p) (p 3 * invSqrtU p)
  let Ψ : EuclideanPlane → EuclideanPlane := fun w ↦ vec2 (TFn w) (WFn w)
  let U_tgt : Set EuclideanPlane := wShift ⁻¹' U_c
  have hU_tgt_open : IsOpen U_tgt := hU_c_open.preimage hwShift_diff.continuous
  have hfp_tgt : lekiliMove4 s p_star ∈ U_tgt := by simpa [U_tgt, hwShift_pstar] using h0_Uc
  let pairFn : EuclideanSpace ℝ (Fin 4) → (Fin 2 → ℝ) × ℝ :=
    fun p ↦ (wShift (lekiliMove4 s p), p 1 - x_star)
  have hpair_diff : ContDiff ℝ ∞ pairFn :=
    (hwShift_diff.comp (contDiff_lekiliMove4 s)).prodMk ((euclidProj 1).contDiff.sub contDiff_const)
  let U_dom : Set (EuclideanSpace ℝ (Fin 4)) :=
    {p | lekiliMove4 s p ∈ U_tgt ∧ pairFn p ∈ U_u ∧ 0 < u (pairFn p)}
  have hU_dom_open : IsOpen U_dom := by
    have h1 : IsOpen (lekiliMove4 s ⁻¹' U_tgt) :=
      hU_tgt_open.preimage (contDiff_lekiliMove4 s).continuous
    have h2 : IsOpen (pairFn ⁻¹' U_u) := hU_u_open.preimage hpair_diff.continuous
    have hu_c : ContinuousOn (fun p ↦ u (pairFn p)) (pairFn ⁻¹' U_u) :=
      hu_contDiff.continuousOn.comp hpair_diff.continuous.continuousOn (fun _ hx ↦ hx)
    have h3 : IsOpen {p ∈ pairFn ⁻¹' U_u | 0 < u (pairFn p)} :=
      hu_c.isOpen_inter_preimage h2 isOpen_Ioi
    have heq : U_dom = (lekiliMove4 s ⁻¹' U_tgt) ∩ {p ∈ pairFn ⁻¹' U_u | 0 < u (pairFn p)} := by
      ext p; simp [U_dom]
    rw [heq]; exact h1.inter h3
  have hp_pair0 : pairFn p_star = (0, 0) :=
    Prod.ext hwShift_pstar (by simp [pairFn, p_star, lekiliMove4CritCurve])
  have hp_dom : p_star ∈ U_dom :=
    ⟨hfp_tgt, hp_pair0.symm ▸ h0_Uu, hp_pair0.symm ▸ hu_pos⟩
  have hc_comp_diff (i : Fin 3) : ContDiffOn ℝ ∞ (fun w ↦ c i (wShift w)) U_tgt :=
    (hc_contDiff i).comp hwShift_diff.contDiffOn (fun _ hw ↦ hw)
  have hΨ_diff : ContDiffOn ℝ ∞ Ψ U_tgt :=
    contDiffOn_vec2
      ((((hc_comp_diff 2).pow 2).div_const 9).sub ((hc_comp_diff 1).div_const 3))
      ((((hc_comp_diff 0).sub (((hc_comp_diff 1).mul (hc_comp_diff 2)).div_const 3)).add
        ((contDiff_const.contDiffOn.mul ((hc_comp_diff 2).pow 3)).div_const 27))).neg
  have hu_comp_cd : ContDiffOn ℝ ∞ (fun p ↦ u (pairFn p)) U_dom :=
    hu_contDiff.comp hpair_diff.contDiffOn (fun _ hp ↦ hp.2.1)
  have hinv_cd : ContDiffOn ℝ ∞ invSqrtU U_dom :=
    (hu_comp_cd.sqrt fun _ hp ↦ hp.2.2.ne').inv fun _ hp ↦ (Real.sqrt_pos.mpr hp.2.2).ne'
  have hΦ_diff : ContDiffOn ℝ ∞ Φ U_dom := by
    have hL_cd : ContDiffOn ℝ ∞ (lekiliMove4 s) U_dom := (contDiff_lekiliMove4 s).contDiffOn
    have hp_cd (i : Fin 4) : ContDiffOn ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 4) ↦ p i) U_dom :=
      (euclidProj i).contDiff.contDiffOn
    have hT_cd : ContDiffOn ℝ ∞ (fun p ↦ TFn (lekiliMove4 s p)) U_dom :=
      ((((hc_comp_diff 2).pow 2).div_const 9).sub ((hc_comp_diff 1).div_const 3)).comp
        hL_cd (fun _ hp ↦ hp.1)
    have hc2_cd : ContDiffOn ℝ ∞ (fun p ↦ c 2 (wShift (lekiliMove4 s p))) U_dom :=
      (hc_comp_diff 2).comp hL_cd (fun _ hp ↦ hp.1)
    exact contDiffOn_vec4 hT_cd
      (((hp_cd 1).sub contDiff_const.contDiffOn).add (hc2_cd.div_const 3))
      ((hp_cd 2).mul hinv_cd) ((hp_cd 3).mul hinv_cd)
  let k₁₁ : ℝ := (fderiv ℝ (c 1) 0) ![0, 1]
  let c₂₀ : ℝ := (fderiv ℝ (c 2) 0) v₀
  let rtu : ℝ := Real.sqrt (u (0, 0))
  have hrtu_ne : rtu ≠ 0 := (Real.sqrt_pos.mpr hu_pos).ne'
  let eΨ : EuclideanPlane ≃L[ℝ] EuclideanPlane :=
    { toFun v := vec2 (v 0 / (3 * x_star) - k₁₁ / 3 * (v 1 + x_star * v 0))
        ((v 1 + x_star * v 0) / x_star)
      invFun z :=
        let v0 := 3 * x_star * z 0 + k₁₁ * x_star ^ 2 * z 1
        vec2 v0 (x_star * z 1 - x_star * v0)
      map_add' u v := by
        refine ext_vec2 ?_ ?_ <;> (simp only [vec2_zero, vec2_one, PiLp.add_apply]; ring)
      map_smul' r0 v := by
        refine ext_vec2 ?_ ?_ <;>
          (simp only [vec2_zero, vec2_one, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring)
      left_inv v := by
        refine ext_vec2 ?_ ?_ <;>
          (simp only [vec2_zero, vec2_one]; field_simp [hx_star_ne]; ring)
      right_inv z := by
        refine ext_vec2 ?_ ?_ <;>
          (simp only [vec2_zero, vec2_one]; field_simp [hx_star_ne]; ring)
      continuous_toFun := continuous_vec2
        (((euclidProj 0).continuous.div_const (3 * x_star)).sub
          (continuous_const.mul ((euclidProj 1).continuous.add
            (continuous_const.mul (euclidProj 0).continuous))))
        (((euclidProj 1).continuous.add
          (continuous_const.mul (euclidProj 0).continuous)).div_const x_star)
      continuous_invFun := continuous_vec2
        ((continuous_const.mul (euclidProj 0).continuous).add
          (continuous_const.mul (euclidProj 1).continuous))
        ((continuous_const.mul (euclidProj 1).continuous).sub
          (continuous_const.mul ((continuous_const.mul (euclidProj 0).continuous).add
            (continuous_const.mul (euclidProj 1).continuous)))) }
  let eΦ : EuclideanSpace ℝ (Fin 4) ≃L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    { toFun v := vec4 (v 0 / (3 * x_star)) (v 1 + (c₂₀ / 3) * v 0) (v 2 / rtu) (v 3 / rtu)
      invFun a :=
        let v0 := 3 * x_star * a 0
        vec4 v0 (a 1 - (c₂₀ / 3) * v0) (rtu * a 2) (rtu * a 3)
      map_add' u v := by
        refine ext_vec4 ?_ ?_ ?_ ?_ <;>
          (simp only [vec4_zero, vec4_one, vec4_two, vec4_three, PiLp.add_apply]; ring)
      map_smul' r0 v := by
        refine ext_vec4 ?_ ?_ ?_ ?_ <;>
          (simp only [vec4_zero, vec4_one, vec4_two, vec4_three, PiLp.smul_apply,
             smul_eq_mul, RingHom.id_apply]; ring)
      left_inv v := by
        refine ext_vec4 ?_ ?_ ?_ ?_
        · simp only [vec4_zero]; field_simp [hx_star_ne]
        · simp only [vec4_zero, vec4_one]; field_simp [hx_star_ne]; ring
        · simp only [vec4_two]; field_simp [hrtu_ne]
        · simp only [vec4_three]; field_simp [hrtu_ne]
      right_inv a := by
        refine ext_vec4 ?_ ?_ ?_ ?_
        · simp only [vec4_zero]; field_simp [hx_star_ne]
        · simp only [vec4_zero, vec4_one]; field_simp [hx_star_ne]; ring
        · simp only [vec4_two]; field_simp [hrtu_ne]
        · simp only [vec4_three]; field_simp [hrtu_ne]
      continuous_toFun := continuous_vec4
        ((euclidProj 0).continuous.div_const (3 * x_star))
        ((euclidProj 1).continuous.add (continuous_const.mul (euclidProj 0).continuous))
        ((euclidProj 2).continuous.div_const rtu)
        ((euclidProj 3).continuous.div_const rtu)
      continuous_invFun := continuous_vec4
        (continuous_const.mul (euclidProj 0).continuous)
        ((euclidProj 1).continuous.sub
          (continuous_const.mul (continuous_const.mul (euclidProj 0).continuous)))
        (continuous_const.mul (euclidProj 2).continuous)
        (continuous_const.mul (euclidProj 3).continuous) }
  have hc_w_hasFDeriv (i : Fin 3) (w : EuclideanPlane) (hw : w ∈ U_tgt) :
      HasFDerivAt (fun z ↦ c i (wShift z))
        ((fderiv ℝ (c i) (wShift w)).comp dwShift) w := by
    have hci : AnalyticAt ℝ (c i) (wShift w) := by
      have hw' : wShift w ∈ U_c := hw
      fin_cases i
      · exact (hU_c_sub _ hw').1
      · exact (hU_c_sub _ hw').2.1
      · exact (hU_c_sub _ hw').2.2
    exact (hci.differentiableAt.hasFDerivAt).comp w (hwShift_fderiv w)
  have hT_hasFDeriv_wstar : HasFDerivAt TFn
      ((-1 / 3 : ℝ) • ((fderiv ℝ (c 1) 0).comp dwShift)) (lekiliMove4 s p_star) := by
    have h2 := hc_w_hasFDeriv 2 (lekiliMove4 s p_star) hfp_tgt
    have h1 := hc_w_hasFDeriv 1 (lekiliMove4 s p_star) hfp_tgt
    rw [hwShift_pstar] at h2 h1
    have h2_sq : HasFDerivAt (fun w : EuclideanPlane ↦ c 2 (wShift w) ^ 2 / 9)
        (0 : EuclideanPlane →L[ℝ] ℝ) (lekiliMove4 s p_star) := by
      have heq : (fun w ↦ c 2 (wShift w) ^ 2 / 9) = fun w ↦ c 2 (wShift w) ^ 2 * (1 / 9 : ℝ) := by
        funext w; ring
      rw [heq]
      refine ((h2.pow 2).mul_const (1 / 9 : ℝ)).congr_fderiv ?_
      ext v; simp [hwShift_pstar, hc0 2]
    have h1_div : HasFDerivAt (fun w ↦ c 1 (wShift w) / 3)
        ((1 / 3 : ℝ) • ((fderiv ℝ (c 1) 0).comp dwShift)) (lekiliMove4 s p_star) := by
      have heq : (fun w ↦ c 1 (wShift w) / 3) = fun w ↦ c 1 (wShift w) * (1 / 3 : ℝ) := by
        funext w; ring
      rw [heq]
      refine (h1.mul_const (1 / 3 : ℝ)).congr_fderiv ?_
      ext v; simp [smul_apply, smul_eq_mul]
    refine (h2_sq.sub h1_div).congr_fderiv ?_
    ext v; simp [smul_apply]; ring
  have hW_hasFDeriv_wstar : HasFDerivAt WFn
      (-((fderiv ℝ (c 0) 0).comp dwShift)) (lekiliMove4 s p_star) := by
    have h0 := hc_w_hasFDeriv 0 (lekiliMove4 s p_star) hfp_tgt
    have h1 := hc_w_hasFDeriv 1 (lekiliMove4 s p_star) hfp_tgt
    have h2 := hc_w_hasFDeriv 2 (lekiliMove4 s p_star) hfp_tgt
    rw [hwShift_pstar] at h0 h1 h2
    have h12 : HasFDerivAt (fun w : EuclideanPlane ↦ c 1 (wShift w) * c 2 (wShift w) / 3)
        (0 : EuclideanPlane →L[ℝ] ℝ) (lekiliMove4 s p_star) := by
      have heq : (fun w : EuclideanPlane ↦ c 1 (wShift w) * c 2 (wShift w) / 3) =
          fun w ↦ (c 1 (wShift w) * c 2 (wShift w)) * (1 / 3 : ℝ) := by funext w; ring
      rw [heq]
      refine ((h1.mul h2).mul_const (1 / 3 : ℝ)).congr_fderiv ?_
      ext v; simp [hwShift_pstar, hc0 1, hc0 2]
    have h2c : HasFDerivAt (fun w : EuclideanPlane ↦ 2 * c 2 (wShift w) ^ 3 / 27)
        (0 : EuclideanPlane →L[ℝ] ℝ) (lekiliMove4 s p_star) := by
      have heq : (fun w : EuclideanPlane ↦ 2 * c 2 (wShift w) ^ 3 / 27) =
          fun w ↦ (2 * c 2 (wShift w) ^ 3) * (1 / 27 : ℝ) := by funext w; ring
      rw [heq]
      refine (((h2.pow 3).const_mul 2).mul_const (1 / 27 : ℝ)).congr_fderiv ?_
      ext v; simp [hwShift_pstar, hc0 2]
    exact (((h0.sub h12).add h2c).neg).congr_fderiv (by ext v; simp)
  have heΨ : (eΨ : EuclideanPlane →L[ℝ] EuclideanPlane) =
      fderiv ℝ Ψ (lekiliMove4 s p_star) := by
    rw [(hasFDerivAt_vec2 hT_hasFDeriv_wstar hW_hasFDeriv_wstar).fderiv]
    refine ContinuousLinearMap.ext fun v ↦ ext_vec2 ?_ ?_
    · simp only [eΨ, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_mk,
        LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, clmVec2_apply, vec2_zero,
        smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
      rw [hdwShift_decomp v, map_add, map_smul, map_smul, hc1_v0]
      simp only [k₁₁, smul_eq_mul]
      field_simp [hx_star_ne]; ring
    · simp only [eΨ, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_mk,
        LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, clmVec2_apply, vec2_one,
        neg_apply, ContinuousLinearMap.comp_apply, hc0_fderiv, smul_apply,
        ContinuousLinearMap.proj_apply, dwShift, ContinuousLinearMap.pi_apply,
        Matrix.cons_val_one, Matrix.cons_val_zero, add_apply, euclidProj,
        EuclideanSpace.proj, PiLp.proj_apply, smul_eq_mul]
      field_simp [hx_star_ne]
  have heΦ : (eΦ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) =
      fderiv ℝ Φ p_star := by
    have hp (i : Fin 4) : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 4) ↦ q i)
        (euclidProj i) p_star := (euclidProj i).hasFDerivAt
    have hL_fderiv := hasFDerivAt_lekiliMove4 s p_star
    have hdw_L (v : EuclideanSpace ℝ (Fin 4)) :
        dwShift (lekiliMove4FDerivCLM s p_star v) = v 0 • v₀ := by
      ext j
      fin_cases j
      · simp [dwShift, lekiliMove4FDerivCLM_apply, v₀, euclidProj]
      · simp only [Fin.mk_one, dwShift, ContinuousLinearMap.pi_apply, Matrix.cons_val_one,
          Matrix.cons_val_zero, add_apply, smul_apply, euclidProj, EuclideanSpace.proj,
          PiLp.proj_apply, lekiliMove4FDerivCLM_apply, vec2_zero, vec2_one, p_star,
          lekiliMove4CritCurve, vec4_zero, vec4_one, vec4_two, vec4_three, v₀, Pi.smul_apply,
          smul_eq_mul]
        ring
    have hT_p_der : HasFDerivAt (fun q ↦ TFn (lekiliMove4 s q))
        ((1 / (3 * x_star)) • euclidProj (0 : Fin 4)) p_star := by
      refine (hT_hasFDeriv_wstar.comp p_star hL_fderiv).congr_fderiv ?_
      ext v
      simp only [smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul, hdw_L v,
        map_smul, hc1_v0, euclidProj, EuclideanSpace.proj, PiLp.proj_apply]
      field_simp [hx_star_ne]
    have hc2_p_der : HasFDerivAt (fun q ↦ c 2 (wShift (lekiliMove4 s q)))
        (c₂₀ • euclidProj (0 : Fin 4)) p_star := by
      have h2 := hc_w_hasFDeriv 2 (lekiliMove4 s p_star) hfp_tgt
      rw [hwShift_pstar] at h2
      refine (h2.comp p_star hL_fderiv).congr_fderiv ?_
      ext v
      simp only [smul_apply, ContinuousLinearMap.comp_apply, hdw_L v, map_smul, c₂₀,
        euclidProj, EuclideanSpace.proj, PiLp.proj_apply, smul_eq_mul]
      ring
    have hQ_p_der : HasFDerivAt QFn
        (euclidProj (1 : Fin 4) + (c₂₀ / 3) • euclidProj (0 : Fin 4)) p_star := by
      have heq_Q : QFn =
          fun q ↦ (q 1 - x_star) + c 2 (wShift (lekiliMove4 s q)) * (1 / 3 : ℝ) := by
        funext q; dsimp only [QFn]; ring
      rw [heq_Q]
      refine (((hp 1).sub_const x_star).add (hc2_p_der.mul_const (1 / 3 : ℝ))).congr_fderiv ?_
      ext v; simp [add_apply, smul_apply, smul_eq_mul]; ring
    have hinv_diffAt : DifferentiableAt ℝ invSqrtU p_star :=
      (hinv_cd.contDiffAt (hU_dom_open.mem_nhds hp_dom)).differentiableAt (by simp)
    have hinv_val : invSqrtU p_star = rtu⁻¹ := by
      change (Real.sqrt (u (pairFn p_star)))⁻¹ = rtu⁻¹
      rw [hp_pair0]
    have h2_der : HasFDerivAt (fun q ↦ q 2 * invSqrtU q)
        (rtu⁻¹ • euclidProj (2 : Fin 4)) p_star := by
      refine ((hp 2).mul hinv_diffAt.hasFDerivAt).congr_fderiv ?_
      ext v
      have hp20 : p_star 2 = 0 := rfl
      simp only [smul_apply, hp20, zero_smul, zero_add, hinv_val, smul_eq_mul]
    have h3_der : HasFDerivAt (fun q ↦ q 3 * invSqrtU q)
        (rtu⁻¹ • euclidProj (3 : Fin 4)) p_star := by
      refine ((hp 3).mul hinv_diffAt.hasFDerivAt).congr_fderiv ?_
      ext v
      have hp30 : p_star 3 = 0 := rfl
      simp only [smul_apply, hp30, zero_smul, zero_add, hinv_val, smul_eq_mul]
    rw [(hasFDerivAt_vec4' hT_p_der hQ_p_der h2_der h3_der).fderiv]
    refine ContinuousLinearMap.ext fun v ↦ ext_vec4 ?_ ?_ ?_ ?_
    · simp only [eΦ, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_mk,
        LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, clmVec4_apply, vec4_zero,
        smul_apply, euclidProj, EuclideanSpace.proj, PiLp.proj_apply, smul_eq_mul]
      ring
    · simp only [eΦ, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_mk,
        LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, clmVec4_apply, vec4_one,
        add_apply, smul_apply, euclidProj, EuclideanSpace.proj, PiLp.proj_apply, smul_eq_mul]
    · simp only [eΦ, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_mk,
        LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, clmVec4_apply, vec4_two,
        smul_apply, euclidProj, EuclideanSpace.proj, PiLp.proj_apply, smul_eq_mul]
      ring
    · simp only [eΦ, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_mk,
        LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, clmVec4_apply, vec4_three,
        smul_apply, euclidProj, EuclideanSpace.proj, PiLp.proj_apply, smul_eq_mul]
      ring
  have hΦ_p : Φ p_star = 0 := by
    refine ext_vec4 ?_ ?_ ?_ ?_
    · simp only [Φ, TFn, hwShift_pstar, hc0 1, hc0 2, vec4_zero, PiLp.zero_apply]; ring
    · dsimp only [Φ, QFn]
      rw [vec4_one, hwShift_pstar, hc0 2]
      simp [p_star, lekiliMove4CritCurve]
    · simp [Φ, p_star, lekiliMove4CritCurve]
    · simp [Φ, p_star, lekiliMove4CritCurve]
  have hΨ_fp : Ψ (lekiliMove4 s p_star) = wrinkledCuspMap 0 := by
    refine ext_vec2 ?_ ?_
    · simp only [Ψ, TFn, hwShift_pstar, hc0 1, hc0 2, wrinkledCuspMap, vec2_zero,
        PiLp.zero_apply]; ring
    · simp only [Ψ, WFn, hwShift_pstar, hc0 0, hc0 1, hc0 2, wrinkledCuspMap, vec2_one,
        PiLp.zero_apply]; ring
  refine isLocallyModeledOn_of_contDiff_maps hU_dom_open hp_dom hU_tgt_open hfp_tgt
    hΦ_diff hΨ_diff eΦ heΦ eΨ heΨ hΦ_p hΨ_fp ?_
    (contDiff_lekiliMove4 s).continuous.continuousAt
  have hG_at : ∀ᶠ q in 𝓝 p_star,
      G (pairFn q) =
        (QFn q ^ 3 - 3 * TFn (lekiliMove4 s q) * QFn q - WFn (lekiliMove4 s q)) *
          u (pairFn q) := by
    filter_upwards [hpair_diff.continuous.continuousAt.tendsto.eventually (hp_pair0 ▸ heq_wp)]
      with q hq
    rw [hq, TauCeti.Polynomial.eval_monicOfCoeff, Fin.sum_univ_three]
    dsimp only [pairFn, QFn, TFn, WFn]
    simp only [sub_zero, Fin.val_zero, pow_zero, mul_one, Fin.val_one, pow_one, Fin.val_two]
    ring
  filter_upwards [hU_dom_open.mem_nhds hp_dom, hG_at] with q hq hG
  refine ⟨hq.1, ?_⟩
  have hu_q_pos : 0 < u (pairFn q) := hq.2.2
  have hu_q_ne : u (pairFn q) ≠ 0 := hu_q_pos.ne'
  have hG_poly : G (pairFn q) = q 3 ^ 2 - q 2 ^ 2 := by
    dsimp only [G, pairFn, wShift, lekiliMove4]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, vec2_zero, vec2_one, ht_star_eq, hs_eq]
    ring
  have hinv_sq : invSqrtU q ^ 2 = (u (pairFn q))⁻¹ := by
    dsimp only [invSqrtU, pairFn]
    rw [inv_pow, Real.sq_sqrt hu_q_pos.le]
  have h2 : QFn q ^ 3 - 3 * TFn (lekiliMove4 s q) * QFn q - WFn (lekiliMove4 s q) =
      (q 3 ^ 2 - q 2 ^ 2) * invSqrtU q ^ 2 := by
    rw [hinv_sq, ← div_eq_mul_inv, eq_div_iff hu_q_ne, ← hG, hG_poly]
  refine ext_vec2 rfl ?_
  simp only [Ψ, Φ, wrinkledCuspMap, vec2_one, vec4_zero, vec4_one, vec4_two, vec4_three]
  rw [mul_pow, mul_pow]
  linear_combination -h2

/-- `IsWrinkledCuspAt` at both cusps `x = ±√(-s/3)` (`σ = ±1`, `s < 0`) of `lekiliMove4 s`
(`Lekili 2009`, §3.2 Move 4). -/
-- tier: T2
theorem isWrinkledCuspAt_lekiliMove4 {s σ : ℝ} (hs : s < 0) (hσ : σ = 1 ∨ σ = -1) :
    IsWrinkledCuspAt (𝓡 4) (𝓡 2) (lekiliMove4 s)
      (lekiliMove4CritCurve s (σ * Real.sqrt (-s / 3))) := by
  rcases hσ with rfl | rfl
  · simpa only [one_mul] using isWrinkledCuspAt_lekiliMove4_pos hs
  · have hpos := isWrinkledCuspAt_lekiliMove4_pos hs
    have hflip :
        flipSignDom (lekiliMove4CritCurve s ((-1) * Real.sqrt (-s / 3))) =
          lekiliMove4CritCurve s (Real.sqrt (-s / 3)) := by
      refine ext_vec4 ?_ ?_ ?_ ?_
      · simp only [flipSignDom_apply, lekiliMove4CritCurve, vec4_zero]; ring
      · simp only [flipSignDom_apply, lekiliMove4CritCurve, vec4_one]; ring
      · simp [flipSignDom_apply, lekiliMove4CritCurve]
      · simp [flipSignDom_apply, lekiliMove4CritCurve]
    exact isLocallyModeledOn_comp_equiv flipSignDom flipMove4Tgt
      (flipMove4Tgt_lekiliMove4 s) (hflip ▸ hpos)

/-- Negative-cusp normal form (`IsWrinkledCuspAt`) at `x = -√(-s/3)` (`s < 0`) for
`lekiliMove4 s`. -/
-- tier: T1
theorem isWrinkledCuspAt_lekiliMove4_neg {s : ℝ} (hs : s < 0) :
    IsWrinkledCuspAt (𝓡 4) (𝓡 2) (lekiliMove4 s)
      (lekiliMove4CritCurve s (-Real.sqrt (-s / 3))) := by
  simpa only [neg_one_mul] using isWrinkledCuspAt_lekiliMove4 hs (Or.inr rfl)

/-- For `0 < s`, every critical point of `lekiliMove4 s` is an indefinite quadratic fold
(`0` cusps). -/
-- tier: T1
theorem singularities_lekiliMove4_pos {s : ℝ} (hs : 0 < s) :
    ∀ p ∈ criticalPoints (𝓡 4) (𝓡 2) (lekiliMove4 s),
      IsIndefiniteFoldAt (𝓡 4) (𝓡 2) (lekiliMove4 s) p := by
  intro p hp
  refine isIndefiniteFoldAt_lekiliMove4_of_mem_criticalPoints s hp ?_
  nlinarith [sq_nonneg (p 1)]

/-- For `s < 0`, every critical point of `lekiliMove4 s` is either an indefinite quadratic fold
(`3 p₁² + s ≠ 0`) or one of the two wrinkled cusps (`p₁ = ±√(-s/3)`). -/
-- tier: T1
theorem singularities_lekiliMove4_neg {s : ℝ} (hs : s < 0) :
    ∀ p ∈ criticalPoints (𝓡 4) (𝓡 2) (lekiliMove4 s),
      IsIndefiniteFoldAt (𝓡 4) (𝓡 2) (lekiliMove4 s) p ∨
        IsWrinkledCuspAt (𝓡 4) (𝓡 2) (lekiliMove4 s) p := by
  intro p hp
  by_cases hx : 3 * p 1 ^ 2 + s ≠ 0
  · exact Or.inl (isIndefiniteFoldAt_lekiliMove4_of_mem_criticalPoints s hp hx)
  · push Not at hx
    right
    rw [criticalPoints_lekiliMove4, Set.mem_ofPred_eq] at hp
    have hp_eq : p = lekiliMove4CritCurve s (p 1) :=
      ext_vec4 hp.1 rfl hp.2.1 hp.2.2
    have hsq : p 1 ^ 2 = (Real.sqrt (-s / 3)) ^ 2 := by
      rw [Real.sq_sqrt (by linarith)]
      linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hp1 | hp1
    · rw [hp_eq, hp1]
      exact isWrinkledCuspAt_lekiliMove4_pos hs
    · rw [hp_eq, hp1]
      exact isWrinkledCuspAt_lekiliMove4_neg hs

end Moves234

/-! ## 4. Compactly Supported Lefschetz Wrinkling & `BrokenToWrinkled` -/

section BrokenToWrinkled

/-- Smooth bump function on `ℝ⁴` equal to `1` on `closedBall 0 1` and `0` outside `ball 0 2`. -/
noncomputable def lekiliWrinkleBump : ContDiffBump (0 : EuclideanSpace ℝ (Fin 4)) :=
  ⟨1, 2, zero_lt_one, one_lt_two⟩

/-- Compactly supported perturbation of `realLefschetzMap`: equals `lekiliMove1 s` inside
`ball 0 1` and coincides with `realLefschetzMap` outside `ball 0 2`. -/
-- tier: T2
noncomputable def compactLefschetzWrinkle (s : ℝ) (p : EuclideanSpace ℝ (Fin 4)) :
    EuclideanPlane :=
  realLefschetzMap p + lekiliWrinkleBump p • vec2 (2 * s * p 0) (-2 * s * p 1)

private noncomputable def lekiliBumpPerturb (p : EuclideanSpace ℝ (Fin 4)) : EuclideanPlane :=
  lekiliWrinkleBump p • vec2 (2 * p 0) (-2 * p 1)

private theorem compactLefschetzWrinkle_eq_add_smul (s : ℝ) (p : EuclideanSpace ℝ (Fin 4)) :
    compactLefschetzWrinkle s p = realLefschetzMap p + s • lekiliBumpPerturb p := by
  refine ext_vec2 ?_ ?_ <;>
    (simp only [compactLefschetzWrinkle, lekiliBumpPerturb, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, vec2_zero, vec2_one]; ring)

private theorem contDiff_lekiliBumpPerturb : ContDiff ℝ ∞ lekiliBumpPerturb := by
  have hp (i : Fin 4) : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 4) ↦ p i) :=
    (euclidProj i).contDiff
  exact lekiliWrinkleBump.contDiff.smul
    (contDiff_vec2 (contDiff_const.mul (hp 0)) (contDiff_const.mul (hp 1)))

/-- Joint smoothness (`ContDiff ℝ ∞`) of `(s, p) ↦ compactLefschetzWrinkle s p` on `ℝ × ℝ⁴`. -/
-- tier: T2
theorem contDiff_compactLefschetzWrinkle_uncurry :
    ContDiff ℝ ∞
      (fun q : ℝ × EuclideanSpace ℝ (Fin 4) ↦ compactLefschetzWrinkle q.1 q.2) := by
  have heq : (fun q : ℝ × EuclideanSpace ℝ (Fin 4) ↦ compactLefschetzWrinkle q.1 q.2) =
      fun q ↦ realLefschetzMap q.2 + q.1 • lekiliBumpPerturb q.2 := by
    funext q; exact compactLefschetzWrinkle_eq_add_smul q.1 q.2
  rw [heq]
  exact (contDiff_realLefschetzMap.comp contDiff_snd).add
    (contDiff_fst.smul (contDiff_lekiliBumpPerturb.comp contDiff_snd))

/-- Smoothness (`ContDiff ℝ ∞`) of `compactLefschetzWrinkle s`. -/
theorem contDiff_compactLefschetzWrinkle (s : ℝ) :
    ContDiff ℝ ∞ (compactLefschetzWrinkle s) := by
  have hp (i : Fin 4) : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 4) ↦ p i) :=
    (euclidProj i).contDiff
  have hlin : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 4) ↦ vec2 (2 * s * p 0) (-2 * s * p 1)) :=
    contDiff_vec2 (contDiff_const.mul (hp 0)) (contDiff_const.mul (hp 1))
  exact contDiff_realLefschetzMap.add (lekiliWrinkleBump.contDiff.smul hlin)

/-- Inside `Metric.ball 0 1`, `compactLefschetzWrinkle s` agrees identically with
`lekiliMove1 s` on an open neighborhood of each point. -/
theorem compactLefschetzWrinkle_eventuallyEq_lekiliMove1 (s : ℝ)
    {p : EuclideanSpace ℝ (Fin 4)} (hp : p ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    compactLefschetzWrinkle s =ᶠ[𝓝 p] lekiliMove1 s := by
  filter_upwards [lekiliWrinkleBump.eventuallyEq_one_of_mem_ball hp] with q hq
  change realLefschetzMap q + lekiliWrinkleBump q • vec2 (2 * s * q 0) (-2 * s * q 1) =
    realLefschetzMap q + vec2 (2 * s * q 0) (-2 * s * q 1)
  rw [hq, Pi.one_apply, one_smul]

/-- Outside `Metric.ball 0 2` (`2 ≤ ‖p‖`), `compactLefschetzWrinkle s p = realLefschetzMap p`. -/
theorem compactLefschetzWrinkle_eq_realLefschetzMap_of_two_le_norm (s : ℝ)
    {p : EuclideanSpace ℝ (Fin 4)} (hp : 2 ≤ ‖p‖) :
    compactLefschetzWrinkle s p = realLefschetzMap p := by
  have hdist : lekiliWrinkleBump.rOut ≤ dist p 0 := by
    simpa [lekiliWrinkleBump, dist_zero_right] using hp
  simp [compactLefschetzWrinkle, lekiliWrinkleBump.zero_of_le_dist hdist]

/-- Quantitative target bound: for `‖p‖ ≤ 2` and `|s| ≤ 1`,
`‖compactLefschetzWrinkle s p‖ ≤ 40`. -/
theorem norm_compactLefschetzWrinkle_le_forty {s : ℝ} (hs : |s| ≤ 1)
    {p : EuclideanSpace ℝ (Fin 4)} (hp : ‖p‖ ≤ 2) :
    ‖compactLefschetzWrinkle s p‖ ≤ 40 := by
  have hcoord (i : Fin 4) : |p i| ≤ 2 := by
    have hi : ‖p i‖ ≤ ‖p‖ := PiLp.norm_apply_le p i
    rw [Real.norm_eq_abs] at hi
    exact hi.trans hp
  have hs0 : -1 ≤ s ∧ s ≤ 1 := abs_le.mp hs
  have hb0 : 0 ≤ lekiliWrinkleBump p := lekiliWrinkleBump.nonneg
  have hb1 : lekiliWrinkleBump p ≤ 1 := lekiliWrinkleBump.le_one
  have hc0 : |compactLefschetzWrinkle s p 0| ≤ 24 := by
    simp only [compactLefschetzWrinkle, realLefschetzMap, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, vec2_zero]
    have h0' : p 0 ^ 2 ≤ 4 := by nlinarith [abs_le.mp (hcoord 0)]
    have h1' : p 1 ^ 2 ≤ 4 := by nlinarith [abs_le.mp (hcoord 1)]
    have h2' : p 2 ^ 2 ≤ 4 := by nlinarith [abs_le.mp (hcoord 2)]
    have h3' : p 3 ^ 2 ≤ 4 := by nlinarith [abs_le.mp (hcoord 3)]
    have hpert : |lekiliWrinkleBump p * (2 * s * p 0)| ≤ 4 := by
      rw [abs_mul, abs_of_nonneg hb0]
      have hsp0 : |2 * s * p 0| ≤ 4 := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        nlinarith [abs_nonneg s, hcoord 0]
      nlinarith
    calc
      |p 0 ^ 2 - p 1 ^ 2 + p 2 ^ 2 - p 3 ^ 2 + lekiliWrinkleBump p * (2 * s * p 0)|
        ≤ |p 0 ^ 2 - p 1 ^ 2 + p 2 ^ 2 - p 3 ^ 2| + |lekiliWrinkleBump p * (2 * s * p 0)| :=
          abs_add_le _ _
      _ ≤ (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2) + 4 := by
          gcongr
          rw [abs_le]
          constructor <;>
            linarith [sq_nonneg (p 0), sq_nonneg (p 1), sq_nonneg (p 2), sq_nonneg (p 3)]
      _ ≤ 24 := by linarith
  have hc1 : |compactLefschetzWrinkle s p 1| ≤ 24 := by
    simp only [compactLefschetzWrinkle, realLefschetzMap, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, vec2_one]
    have h01' : |2 * p 0 * p 1| ≤ 8 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [abs_nonneg (p 0), hcoord 0, hcoord 1]
    have h23' : |2 * p 2 * p 3| ≤ 8 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [abs_nonneg (p 2), hcoord 2, hcoord 3]
    have hpert : |lekiliWrinkleBump p * (-2 * s * p 1)| ≤ 4 := by
      rw [show -2 * s * p 1 = -(2 * s * p 1) by ring, abs_mul, abs_of_nonneg hb0, abs_neg]
      have hsp1 : |2 * s * p 1| ≤ 4 := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        nlinarith [abs_nonneg s, hcoord 1]
      nlinarith
    have _ := hs0
    calc
      |2 * p 0 * p 1 + 2 * p 2 * p 3 + lekiliWrinkleBump p * (-2 * s * p 1)|
        ≤ |2 * p 0 * p 1 + 2 * p 2 * p 3| + |lekiliWrinkleBump p * (-2 * s * p 1)| :=
          abs_add_le _ _
      _ ≤ (|2 * p 0 * p 1| + |2 * p 2 * p 3|) + 4 := by gcongr; exact abs_add_le _ _
      _ ≤ 24 := by linarith
  have hx0 : compactLefschetzWrinkle s p 0 ^ 2 ≤ 24 ^ 2 := by nlinarith [abs_le.mp hc0]
  have hx1 : compactLefschetzWrinkle s p 1 ^ 2 ≤ 24 ^ 2 := by nlinarith [abs_le.mp hc1]
  have hsq : ‖compactLefschetzWrinkle s p‖ ^ 2 ≤ 40 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    linarith
  exact (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp hsq

private noncomputable def clmVec4 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g₀ g₁ g₂ g₃ : E →L[ℝ] ℝ) : E →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![g₀, g₁, g₂, g₃])

private noncomputable def realLefschetzRightInvCLM (p : EuclideanSpace ℝ (Fin 4)) :
    EuclideanPlane →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  (2 * ‖p‖ ^ 2)⁻¹ •
    clmVec4
      (p 0 • euclidProj (0 : Fin 2) + p 1 • euclidProj (1 : Fin 2))
      ((-p 1) • euclidProj (0 : Fin 2) + p 0 • euclidProj (1 : Fin 2))
      (p 2 • euclidProj (0 : Fin 2) + p 3 • euclidProj (1 : Fin 2))
      ((-p 3) • euclidProj (0 : Fin 2) + p 2 • euclidProj (1 : Fin 2))

private theorem realLefschetzRightInvCLM_apply (p : EuclideanSpace ℝ (Fin 4))
    (w : EuclideanPlane) :
    realLefschetzRightInvCLM p w =
      (2 * ‖p‖ ^ 2)⁻¹ •
        vec4 (p 0 * w 0 + p 1 * w 1) (-p 1 * w 0 + p 0 * w 1)
          (p 2 * w 0 + p 3 * w 1) (-p 3 * w 0 + p 2 * w 1) := by
  simp only [realLefschetzRightInvCLM, clmVec4, smul_apply, clmVec4_apply,
    add_apply, euclidProj, EuclideanSpace.proj, PiLp.proj_apply, smul_eq_mul, neg_mul]

private theorem fderiv_realLefschetzMap_comp_rightInv {p : EuclideanSpace ℝ (Fin 4)}
    (hp : p ≠ 0) :
    (fderiv ℝ realLefschetzMap p).comp (realLefschetzRightInvCLM p) =
      ContinuousLinearMap.id ℝ EuclideanPlane := by
  have hnorm_ne : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
  have hden_ne : 2 * ‖p‖ ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hnorm_ne)
  have hsum : ‖p‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
  refine ContinuousLinearMap.ext fun w ↦ ?_
  rw [ContinuousLinearMap.comp_apply, fderiv_realLefschetzMap, realLefschetzRightInvCLM_apply,
    map_smul, realLefschetzFDerivCLM_apply, ContinuousLinearMap.id_apply]
  refine ext_vec2 ?_ ?_ <;>
    (simp only [PiLp.smul_apply, smul_eq_mul, vec2_zero, vec2_one, vec4_zero, vec4_one, vec4_two,
      vec4_three]; field_simp [hden_ne]; rw [hsum]; ring)

private theorem opNorm_realLefschetzRightInvCLM_le_one {p : EuclideanSpace ℝ (Fin 4)}
    (hp : 1 ≤ ‖p‖) :
    ‖realLefschetzRightInvCLM p‖ ≤ 1 := by
  have hp_pos : 0 < ‖p‖ := lt_of_lt_of_le zero_lt_one hp
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w ↦ ?_
  rw [one_mul, realLefschetzRightInvCLM_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (by positivity))]
  have hsum_p : ‖p‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
  have hsum_w : ‖w‖ ^ 2 = w 0 ^ 2 + w 1 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have hvec_sq :
      ‖vec4 (p 0 * w 0 + p 1 * w 1) (-p 1 * w 0 + p 0 * w 1)
          (p 2 * w 0 + p 3 * w 1) (-p 3 * w 0 + p 2 * w 1)‖ = ‖p‖ * ‖w‖ := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hp_pos.le (norm_nonneg w)), mul_pow,
      EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
    simp only [vec4_zero, vec4_one, vec4_two, vec4_three, hsum_p, hsum_w]
    ring
  rw [hvec_sq, inv_mul_le_iff₀ (by positivity)]
  have hp_sq : ‖p‖ ≤ ‖p‖ ^ 2 := by nlinarith
  nlinarith [norm_nonneg w]

/-- **Quantitative Collar Lemma for Compact Lefschetz Wrinkling**: there exists `s₀ ∈ (0, 1)` such
that for every `0 < s ≤ s₀`, the critical locus of `compactLefschetzWrinkle s` is contained inside
the inner disk `Metric.ball 0 1`, and every critical point is either an indefinite quadratic fold
(`IsIndefiniteFoldAt`) or one of the three wrinkled cusps (`IsWrinkledCuspAt`). -/
-- tier: T2
theorem exists_compactLefschetzWrinkle_collar :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ < 1 ∧
      ∀ s : ℝ, 0 < s → s ≤ s₀ →
        criticalPoints (𝓡 4) (𝓡 2) (compactLefschetzWrinkle s) ⊆
            Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) 1 ∧
          ∀ p ∈ criticalPoints (𝓡 4) (𝓡 2) (compactLefschetzWrinkle s),
            IsIndefiniteFoldAt (𝓡 4) (𝓡 2) (compactLefschetzWrinkle s) p ∨
              IsWrinkledCuspAt (𝓡 4) (𝓡 2) (compactLefschetzWrinkle s) p := by
  have hp_cd (i : Fin 4) : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 4) ↦ p i) :=
    (euclidProj i).contDiff
  have hP_cd : ContDiff ℝ ∞ lekiliBumpPerturb :=
    lekiliWrinkleBump.contDiff.smul
      (contDiff_vec2 (contDiff_const.mul (hp_cd 0)) (contDiff_const.mul (hp_cd 1)))
  have hnorm_cont :
      Continuous (fun p : EuclideanSpace ℝ (Fin 4) ↦ ‖fderiv ℝ lekiliBumpPerturb p‖) :=
    (hP_cd.continuous_fderiv (by simp)).norm
  have hball_ne : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) 2).Nonempty :=
    ⟨0, Metric.mem_closedBall_self (by norm_num)⟩
  obtain ⟨p_max, _, hp_max⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 4)) 2).exists_isMaxOn
      hball_ne hnorm_cont.continuousOn
  set M₁ := max ‖fderiv ℝ lekiliBumpPerturb p_max‖ 0
  set s₀ : ℝ := 1 / (M₁ + 2)
  have hM1_nn : 0 ≤ M₁ := le_max_right _ _
  have hs0_pos : 0 < s₀ := by positivity
  have hs0_lt_one : s₀ < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  refine ⟨s₀, hs0_pos, hs0_lt_one, fun s hs_pos hs_le ↦ ?_⟩
  have hcrit_sub : criticalPoints (𝓡 4) (𝓡 2) (compactLefschetzWrinkle s) ⊆
      Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) 1 := by
    intro p hp_crit
    by_contra hp_not
    rw [Metric.mem_ball, dist_zero_right, not_lt] at hp_not
    have hp_ne : p ≠ 0 := fun h0 ↦ by simp only [h0, norm_zero] at hp_not; norm_num at hp_not
    by_cases hp_le2 : ‖p‖ ≤ 2
    · have hsurj : Function.Surjective (fderiv ℝ (compactLefschetzWrinkle s) p) := by
        have hcomp_eq : compactLefschetzWrinkle s =
            fun q ↦ realLefschetzMap q + s • lekiliBumpPerturb q :=
          funext (compactLefschetzWrinkle_eq_add_smul s)
        have hfderiv_eq : fderiv ℝ (compactLefschetzWrinkle s) p =
            fderiv ℝ realLefschetzMap p + s • fderiv ℝ lekiliBumpPerturb p := by
          rw [hcomp_eq]
          have hd : HasFDerivAt (fun q ↦ realLefschetzMap q + s • lekiliBumpPerturb q)
              (realLefschetzFDerivCLM p + s • fderiv ℝ lekiliBumpPerturb p) p :=
            (hasFDerivAt_realLefschetzMap p).add
              ((hP_cd.contDiffAt.differentiableAt (by simp)).hasFDerivAt.const_smul s)
          rw [hd.fderiv, (hasFDerivAt_realLefschetzMap p).fderiv]
        set T := (fderiv ℝ (compactLefschetzWrinkle s) p).comp (realLefschetzRightInvCLM p)
        have hT_sub : T - ContinuousLinearMap.id ℝ EuclideanPlane =
            s • ((fderiv ℝ lekiliBumpPerturb p).comp (realLefschetzRightInvCLM p)) := by
          simp only [T, hfderiv_eq, ContinuousLinearMap.add_comp,
            fderiv_realLefschetzMap_comp_rightInv hp_ne, ContinuousLinearMap.smul_comp]
          abel
        have hP_le : ‖fderiv ℝ lekiliBumpPerturb p‖ ≤ M₁ :=
          (hp_max (Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using hp_le2))).trans
            (le_max_left _ _)
        have hT_norm : ‖T - ContinuousLinearMap.id ℝ EuclideanPlane‖ < 1 := by
          rw [hT_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hs_pos]
          calc
            s * ‖(fderiv ℝ lekiliBumpPerturb p).comp (realLefschetzRightInvCLM p)‖
              ≤ s * (‖fderiv ℝ lekiliBumpPerturb p‖ * ‖realLefschetzRightInvCLM p‖) :=
                mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) hs_pos.le
            _ ≤ s * (M₁ * 1) := by
                gcongr
                exact opNorm_realLefschetzRightInvCLM_le_one hp_not
            _ = s * M₁ := by rw [mul_one]
            _ ≤ s₀ * M₁ := mul_le_mul_of_nonneg_right hs_le hM1_nn
            _ = M₁ / (M₁ + 2) := by dsimp only [s₀]; ring
            _ < 1 := by rw [div_lt_one (by linarith)]; linarith
        have hT_surj : Function.Surjective
            ((fderiv ℝ (compactLefschetzWrinkle s) p).comp (realLefschetzRightInvCLM p)) :=
          surjective_of_norm_sub_id_lt_one hT_norm
        rw [ContinuousLinearMap.coe_comp] at hT_surj
        exact hT_surj.of_comp
      rw [criticalPoints_euclidean_eq, mem_euclideanCriticalPoints_iff] at hp_crit
      exact hp_crit hsurj
    · have hp_gt2 : 2 < ‖p‖ := lt_of_not_ge hp_le2
      have hev : compactLefschetzWrinkle s =ᶠ[𝓝 p] realLefschetzMap := by
        have hopen : IsOpen {q : EuclideanSpace ℝ (Fin 4) | 2 < ‖q‖} :=
          isOpen_Ioi.preimage continuous_norm
        filter_upwards [hopen.mem_nhds hp_gt2] with q hq
        exact compactLefschetzWrinkle_eq_realLefschetzMap_of_two_le_norm s hq.le
      have hsurj : Function.Surjective (fderiv ℝ (compactLefschetzWrinkle s) p) := by
        rw [hev.fderiv_eq]
        exact (surjective_fderiv_realLefschetzMap_iff p).mpr hp_ne
      rw [criticalPoints_euclidean_eq, mem_euclideanCriticalPoints_iff] at hp_crit
      exact hp_crit hsurj
  refine ⟨hcrit_sub, fun p hp_crit ↦ ?_⟩
  have hp_ball : p ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) 1 := hcrit_sub hp_crit
  have hev : compactLefschetzWrinkle s =ᶠ[𝓝 p] lekiliMove1 s :=
    compactLefschetzWrinkle_eventuallyEq_lekiliMove1 s hp_ball
  have hp_crit_L : p ∈ criticalPoints (𝓡 4) (𝓡 2) (lekiliMove1 s) := by
    rw [criticalPoints_euclidean_eq, mem_euclideanCriticalPoints_iff] at hp_crit ⊢
    rwa [← hev.fderiv_eq]
  rcases singularities_lekiliMove1 hs_pos.ne' p hp_crit_L with hfold | hcusp
  · exact Or.inl (isIndefiniteFoldAt_congr hev.symm hfold)
  · exact Or.inr (isWrinkledCuspAt_congr hev.symm hcusp)

private theorem surjective_mfderiv_congr_of_eventuallyEq
    {E H E' H' M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'}
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H' N]
    {f g : M → N} {x : M} (h : f =ᶠ[𝓝 x] g) :
    Function.Surjective (mfderiv I J f x) ↔ Function.Surjective (mfderiv I J g x) := by
  have heq : mfderiv I J f x =
      (tangentSpaceCast J (g x) (f x) :
        TangentSpace J (g x) →L[ℝ] TangentSpace J (f x)).comp (mfderiv I J g x) :=
    h.mfderiv_eq
  have hcoe : ⇑(mfderiv I J f x) =
      ⇑(tangentSpaceCast J (g x) (f x)) ∘ ⇑(mfderiv I J g x) := by
    rw [heq]; rfl
  rw [hcoe]
  exact ⟨fun hs y ↦ by
      obtain ⟨v, hv⟩ := hs (tangentSpaceCast J (g x) (f x) y)
      exact ⟨v, (tangentSpaceCast J (g x) (f x)).injective hv⟩,
    fun hs ↦ (tangentSpaceCast J (g x) (f x)).surjective.comp hs⟩

private theorem partialDiffeomorph_mfderiv_bijective
    {E H E' H' M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'}
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H' N]
    (Φ : PartialDiffeomorph I J M N ∞) {x : M} (hx : x ∈ Φ.source) :
    Function.Bijective (mfderiv I J Φ x) := by
  have hx_t : Φ x ∈ Φ.symm.source := Φ.symm_source ▸ Φ.map_source hx
  have hleft : Φ.symm (Φ x) = x := Φ.left_inv hx
  have hΦ_md : MDifferentiableAt I J (⇑Φ) x :=
    (Φ.contMDiffOn.contMDiffAt (Φ.open_source.mem_nhds hx)).mdifferentiableAt (by simp)
  have hsymm_md : MDifferentiableAt J I (⇑Φ.symm) (Φ x) :=
    (Φ.symm.contMDiffOn.contMDiffAt (Φ.symm.open_source.mem_nhds hx_t)).mdifferentiableAt
      (by simp)
  have hev_left : (⇑Φ.symm ∘ ⇑Φ) =ᶠ[𝓝 x] id :=
    _root_.eventually_nhds_iff.mpr ⟨Φ.source, fun q hq ↦ Φ.left_inv hq, Φ.open_source, hx⟩
  have hev_right : (⇑Φ ∘ ⇑Φ.symm) =ᶠ[𝓝 (Φ x)] id :=
    _root_.eventually_nhds_iff.mpr
      ⟨Φ.symm.source, fun y hy ↦ Φ.right_inv (Φ.symm_source ▸ hy), Φ.symm.open_source, hx_t⟩
  have hinj : Function.Injective (mfderiv I J Φ x) := by
    have hcm := mfderiv_comp (x := x) hsymm_md hΦ_md
    have heq : (mfderiv J I Φ.symm (Φ x)).comp (mfderiv I J Φ x) =
        (tangentSpaceCast I (id x) ((⇑Φ.symm ∘ ⇑Φ) x) :
          TangentSpace I (id x) →L[ℝ] TangentSpace I ((⇑Φ.symm ∘ ⇑Φ) x)).comp
          (ContinuousLinearMap.id ℝ (TangentSpace I x)) := by
      rw [← hcm, hev_left.mfderiv_eq, mfderiv_id]
    have hinj_comp : Function.Injective (⇑(mfderiv J I Φ.symm (Φ x)) ∘ ⇑(mfderiv I J Φ x)) := by
      have hcoe : ⇑((mfderiv J I Φ.symm (Φ x)).comp (mfderiv I J Φ x)) =
          ⇑(tangentSpaceCast I (id x) ((⇑Φ.symm ∘ ⇑Φ) x)) := by
        rw [heq]; rfl
      change Function.Injective ⇑((mfderiv J I Φ.symm (Φ x)).comp (mfderiv I J Φ x))
      rw [hcoe]
      exact (tangentSpaceCast I (id x) ((⇑Φ.symm ∘ ⇑Φ) x)).injective
    exact hinj_comp.of_comp
  have hsurj : Function.Surjective (mfderiv I J Φ x) := by
    have hΦ_at : MDifferentiableAt I J (⇑Φ) (Φ.symm (Φ x)) := hleft.symm ▸ hΦ_md
    have hcm := mfderiv_comp (x := Φ x) hΦ_at hsymm_md
    have heq : (mfderiv I J Φ (Φ.symm (Φ x))).comp (mfderiv J I Φ.symm (Φ x)) =
        (tangentSpaceCast J (id (Φ x)) ((⇑Φ ∘ ⇑Φ.symm) (Φ x)) :
          TangentSpace J (id (Φ x)) →L[ℝ] TangentSpace J ((⇑Φ ∘ ⇑Φ.symm) (Φ x))).comp
          (ContinuousLinearMap.id ℝ (TangentSpace J (Φ x))) := by
      rw [← hcm, hev_right.mfderiv_eq, mfderiv_id]
    have hsurj_comp : Function.Surjective
        (⇑(mfderiv I J Φ (Φ.symm (Φ x))) ∘ ⇑(mfderiv J I Φ.symm (Φ x))) := by
      have hcoe : ⇑((mfderiv I J Φ (Φ.symm (Φ x))).comp (mfderiv J I Φ.symm (Φ x))) =
          ⇑(tangentSpaceCast J (id (Φ x)) ((⇑Φ ∘ ⇑Φ.symm) (Φ x))) := by
        rw [heq]; rfl
      change Function.Surjective
        ⇑((mfderiv I J Φ (Φ.symm (Φ x))).comp (mfderiv J I Φ.symm (Φ x)))
      rw [hcoe]
      exact (tangentSpaceCast J (id (Φ x)) ((⇑Φ ∘ ⇑Φ.symm) (Φ x))).surjective
    have hs := hsurj_comp.of_comp
    rwa [hleft] at hs
  exact ⟨hinj, hsurj⟩

/-- Local chart conjugacy by `C^∞` partial diffeomorphisms `(φ, ψ)` transports critical points
of `f : M → Base` onto critical points of `g : ℝ⁴ → ℝ²`. -/
-- tier: T2
theorem mem_criticalPoints_iff_of_partialDiffeomorph_conj
    {E_M H_M E_B H_B M Base : Type*}
    [NormedAddCommGroup E_M] [NormedSpace ℝ E_M] [TopologicalSpace H_M]
    {I_M : ModelWithCorners ℝ E_M H_M}
    [NormedAddCommGroup E_B] [NormedSpace ℝ E_B] [TopologicalSpace H_B]
    {I_B : ModelWithCorners ℝ E_B H_B}
    [TopologicalSpace M] [ChartedSpace H_M M]
    [TopologicalSpace Base] [ChartedSpace H_B Base]
    {f : M → Base} {g : EuclideanSpace ℝ (Fin 4) → EuclideanPlane}
    (φ : PartialDiffeomorph I_M (𝓡 4) M (EuclideanSpace ℝ (Fin 4)) ∞)
    (ψ : PartialDiffeomorph I_B (𝓡 2) Base EuclideanPlane ∞)
    (hf : ContMDiffOn I_M I_B ∞ f φ.source) (hg : ContDiff ℝ ∞ g)
    (hconj : ∀ q ∈ φ.source, f q ∈ ψ.source ∧ ψ (f q) = g (φ q))
    {q : M} (hq : q ∈ φ.source) :
    q ∈ criticalPoints I_M I_B f ↔ φ q ∈ criticalPoints (𝓡 4) (𝓡 2) g := by
  have hev : (⇑ψ ∘ f) =ᶠ[𝓝 q] (g ∘ ⇑φ) :=
    _root_.eventually_nhds_iff.mpr
      ⟨φ.source, fun z hz ↦ (hconj z hz).2, φ.open_source, hq⟩
  have hφ_bij := partialDiffeomorph_mfderiv_bijective φ hq
  have hψ_bij := partialDiffeomorph_mfderiv_bijective ψ (hconj q hq).1
  have hψ_md : MDifferentiableAt I_B (𝓡 2) (⇑ψ) (f q) :=
    (ψ.contMDiffOn.contMDiffAt (ψ.open_source.mem_nhds (hconj q hq).1)).mdifferentiableAt
      (by simp)
  have hf_md : MDifferentiableAt I_M I_B f q :=
    (hf.contMDiffAt (φ.open_source.mem_nhds hq)).mdifferentiableAt (by simp)
  have hg_md : MDifferentiableAt (𝓡 4) (𝓡 2) g (φ q) :=
    hg.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hφ_md : MDifferentiableAt I_M (𝓡 4) (⇑φ) q :=
    (φ.contMDiffOn.contMDiffAt (φ.open_source.mem_nhds hq)).mdifferentiableAt (by simp)
  have h1 : Function.Surjective (mfderiv I_M I_B f q) ↔
      Function.Surjective (mfderiv I_M (𝓡 2) (⇑ψ ∘ f) q) := by
    rw [mfderiv_comp (x := q) hψ_md hf_md, ContinuousLinearMap.coe_comp]
    exact ⟨fun hs ↦ hψ_bij.2.comp hs, fun hs w ↦ by
      obtain ⟨x, hx⟩ := hs (mfderiv I_B (𝓡 2) ψ (f q) w)
      exact ⟨x, hψ_bij.1 hx⟩⟩
  have h2 : Function.Surjective (mfderiv I_M (𝓡 2) (g ∘ ⇑φ) q) ↔
      Function.Surjective (mfderiv (𝓡 4) (𝓡 2) g (φ q)) := by
    rw [mfderiv_comp (x := q) hg_md hφ_md, ContinuousLinearMap.coe_comp]
    exact ⟨fun hs y ↦ by obtain ⟨x, hx⟩ := hs y; exact ⟨mfderiv I_M (𝓡 4) φ q x, hx⟩,
      fun hs ↦ hs.comp hφ_bij.2⟩
  rw [mem_criticalPoints_iff, mem_criticalPoints_iff]
  exact not_congr (h1.trans ((surjective_mfderiv_congr_of_eventuallyEq hev).trans h2))

/-- Pulls back a local normal form `IsLocallyModeledOn` for `g` at `φ q` along a `C^∞` partial
diffeomorphism conjugacy `ψ (f z) = g (φ z)`. -/
-- tier: T2
theorem isLocallyModeledOn_of_partialDiffeomorph_conj
    {E_M H_M E_B H_B M Base : Type*}
    [NormedAddCommGroup E_M] [NormedSpace ℝ E_M] [TopologicalSpace H_M]
    {I_M : ModelWithCorners ℝ E_M H_M}
    [NormedAddCommGroup E_B] [NormedSpace ℝ E_B] [TopologicalSpace H_B]
    {I_B : ModelWithCorners ℝ E_B H_B}
    [TopologicalSpace M] [ChartedSpace H_M M]
    [TopologicalSpace Base] [ChartedSpace H_B Base]
    {f : M → Base} {g model : EuclideanSpace ℝ (Fin 4) → EuclideanPlane}
    {p_m : EuclideanSpace ℝ (Fin 4)}
    (φ : PartialDiffeomorph I_M (𝓡 4) M (EuclideanSpace ℝ (Fin 4)) ∞)
    (ψ : PartialDiffeomorph I_B (𝓡 2) Base EuclideanPlane ∞)
    (hconj : ∀ q ∈ φ.source, f q ∈ ψ.source ∧ ψ (f q) = g (φ q))
    {q : M} (hq : q ∈ φ.source)
    (hg_loc : IsLocallyModeledOn (𝓡 4) (𝓡 2) g (φ q) model p_m) :
    IsLocallyModeledOn I_M I_B f q model p_m := by
  obtain ⟨φg, ψg, hφg, hψg, hφgp, hψgp, hmod⟩ := hg_loc
  refine ⟨φ.trans φg, ψ.trans ψg, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hq, hφg⟩
  · rw [PartialDiffeomorph.trans_source]
    refine ⟨(hconj q hq).1, ?_⟩
    rw [Set.mem_preimage, (hconj q hq).2]
    exact hψg
  · exact hφgp
  · simp only [PartialDiffeomorph.coe_trans, Function.comp_apply, (hconj q hq).2, hψgp]
  · intro z hz
    rcases hz with ⟨hzφ, hzφg⟩
    refine ⟨?_, ?_⟩
    · rw [PartialDiffeomorph.trans_source]
      refine ⟨(hconj z hzφ).1, ?_⟩
      rw [Set.mem_preimage, (hconj z hzφ).2]
      exact (hmod (φ z) hzφg).1
    · simp only [PartialDiffeomorph.coe_trans, Function.comp_apply, (hconj z hzφ).2]
      exact (hmod (φ z) hzφg).2

/-- A real Lefschetz point `p₀` (`IsRealLefschetzAt`) is an isolated point of
`criticalPoints I_M I_B f`. -/
theorem isolated_criticalPoint_of_isRealLefschetzAt
    {E_M H_M E_B H_B M Base : Type*}
    [NormedAddCommGroup E_M] [NormedSpace ℝ E_M] [TopologicalSpace H_M]
    {I_M : ModelWithCorners ℝ E_M H_M}
    [NormedAddCommGroup E_B] [NormedSpace ℝ E_B] [TopologicalSpace H_B]
    {I_B : ModelWithCorners ℝ E_B H_B}
    [TopologicalSpace M] [ChartedSpace H_M M]
    [TopologicalSpace Base] [ChartedSpace H_B Base]
    {f : M → Base} (hf : ContMDiff I_M I_B ∞ f) {p₀ : M}
    (hp₀ : IsRealLefschetzAt I_M I_B f p₀) :
    ∃ U : Set M, IsOpen U ∧ p₀ ∈ U ∧ U ∩ criticalPoints I_M I_B f = {p₀} := by
  obtain ⟨φ, ψ, hpφ, _, hφ0, _, hmod⟩ := hp₀
  refine ⟨φ.source, φ.open_source, hpφ, ?_⟩
  ext q
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hqφ, hq_crit⟩
    have hφq_crit : φ q ∈ criticalPoints (𝓡 4) (𝓡 2) realLefschetzMap :=
      (mem_criticalPoints_iff_of_partialDiffeomorph_conj φ ψ hf.contMDiffOn
        contDiff_realLefschetzMap hmod hqφ).mp hq_crit
    rw [criticalPoints_realLefschetzMap, Set.mem_singleton_iff] at hφq_crit
    exact (φ.injOn hqφ hpφ (hφq_crit.trans hφ0.symm))
  · rintro rfl
    refine ⟨hpφ, ?_⟩
    rw [mem_criticalPoints_iff_of_partialDiffeomorph_conj φ ψ hf.contMDiffOn
      contDiff_realLefschetzMap hmod hpφ, hφ0, criticalPoints_realLefschetzMap]
    rfl

private noncomputable def scaleCLE4 {r : ℝ} (hr : r ≠ 0) :
    EuclideanSpace ℝ (Fin 4) ≃L[ℝ] EuclideanSpace ℝ (Fin 4) where
  toFun x := r • x
  invFun x := r⁻¹ • x
  map_add' x y := smul_add r x y
  map_smul' c x := smul_comm r c x
  left_inv x := by simp [smul_smul, inv_mul_cancel₀ hr]
  right_inv x := by simp [smul_smul, mul_inv_cancel₀ hr]
  continuous_toFun := continuous_id.const_smul r
  continuous_invFun := continuous_id.const_smul r⁻¹

private noncomputable def scaleCLE2 {c : ℝ} (hc : c ≠ 0) :
    EuclideanPlane ≃L[ℝ] EuclideanPlane where
  toFun y := c • y
  invFun y := c⁻¹ • y
  map_add' x y := smul_add c x y
  map_smul' a x := smul_comm c a x
  left_inv y := by simp [smul_smul, inv_mul_cancel₀ hc]
  right_inv y := by simp [smul_smul, mul_inv_cancel₀ hc]
  continuous_toFun := continuous_id.const_smul c
  continuous_invFun := continuous_id.const_smul c⁻¹

private noncomputable def cleToPartialDiffeomorph {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E ≃L[ℝ] F) : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞ where
  toPartialEquiv := A.toEquiv.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := A.contDiff.contMDiff.contMDiffOn
  contMDiffOn_invFun := A.symm.contDiff.contMDiff.contMDiffOn

private theorem realLefschetzMap_smul (r : ℝ) (x : EuclideanSpace ℝ (Fin 4)) :
    realLefschetzMap (r • x) = (r ^ 2) • realLefschetzMap x := by
  refine ext_vec2 ?_ ?_ <;>
    (simp only [realLefschetzMap, PiLp.smul_apply, smul_eq_mul, vec2_zero, vec2_one]; ring)

private theorem coe_restrOpen {E H E' H' M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'}
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H' N]
    (Φ : PartialDiffeomorph I J M N ∞) (s : Set M) (hs : IsOpen s) (x : M) :
    (Φ.restrOpen s hs) x = Φ x := by
  rw [PartialDiffeomorph.restrOpen_toPartialEquiv]
  rfl

private noncomputable def concatSmoothHomotopy {M Base : Type*}
    (H₁ H₂ : ℝ → M → Base) (t : ℝ) (x : M) : Base :=
  if t ≤ 1 / 2 then H₁ (Real.smoothTransition (3 * t)) x
  else H₂ (Real.smoothTransition (3 * t - 2)) x

private theorem concatSmoothHomotopy_zero {M Base : Type*}
    (H₁ H₂ : ℝ → M → Base) (x : M) :
    concatSmoothHomotopy H₁ H₂ 0 x = H₁ 0 x := by
  simp [concatSmoothHomotopy]

private theorem concatSmoothHomotopy_one {M Base : Type*}
    (H₁ H₂ : ℝ → M → Base) (x : M) :
    concatSmoothHomotopy H₁ H₂ 1 x = H₂ 1 x := by
  dsimp only [concatSmoothHomotopy]
  split_ifs with h
  · norm_num at h
  · rw [show (3 : ℝ) * 1 - 2 = 1 by norm_num, Real.smoothTransition.one]

private theorem concatSmoothHomotopy_stationary {M Base : Type*}
    {H₁ H₂ : ℝ → M → Base} {f₀ f₁ : M → Base} {K₁ K₂ : Set M}
    (h₁_stat : ∀ t : ℝ, ∀ x ∉ K₁, H₁ t x = f₀ x)
    (h₂_stat : ∀ t : ℝ, ∀ x ∉ K₂, H₂ t x = f₁ x)
    (hf₁_out : ∀ x ∉ K₁, f₁ x = f₀ x) (t : ℝ) {x : M} (hx : x ∉ K₁ ∪ K₂) :
    concatSmoothHomotopy H₁ H₂ t x = f₀ x := by
  have hx₁ : x ∉ K₁ := fun hm ↦ hx (Set.mem_union_left K₂ hm)
  have hx₂ : x ∉ K₂ := fun hm ↦ hx (Set.mem_union_right K₁ hm)
  dsimp only [concatSmoothHomotopy]
  split_ifs
  · exact h₁_stat _ x hx₁
  · exact (h₂_stat _ x hx₂).trans (hf₁_out x hx₁)

private theorem contMDiff_uncurry_concatSmoothHomotopy
    {E_M H_M E_B H_B M Base : Type*}
    [NormedAddCommGroup E_M] [NormedSpace ℝ E_M] [TopologicalSpace H_M]
    {I_M : ModelWithCorners ℝ E_M H_M}
    [TopologicalSpace M] [ChartedSpace H_M M]
    [NormedAddCommGroup E_B] [NormedSpace ℝ E_B] [TopologicalSpace H_B]
    {I_B : ModelWithCorners ℝ E_B H_B}
    [TopologicalSpace Base] [ChartedSpace H_B Base]
    {H₁ H₂ : ℝ → M → Base}
    (hH₁ : ContMDiff (𝓘(ℝ, ℝ).prod I_M) I_B ∞ (Function.uncurry H₁))
    (hH₂ : ContMDiff (𝓘(ℝ, ℝ).prod I_M) I_B ∞ (Function.uncurry H₂))
    (hjoin : ∀ x : M, H₁ 1 x = H₂ 0 x) :
    ContMDiff (𝓘(ℝ, ℝ).prod I_M) I_B ∞
      (Function.uncurry (concatSmoothHomotopy H₁ H₂)) := by
  have hst : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := ⊤)).contMDiff
  have hτ₁_md : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ ↦ Real.smoothTransition (3 * t)) :=
    hst.comp (contDiff_const.mul contDiff_id).contMDiff
  have hτ₂_md : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ ↦ Real.smoothTransition (3 * t - 2)) :=
    hst.comp ((contDiff_const.mul contDiff_id).sub contDiff_const).contMDiff
  let g₁ : ℝ × M → Base :=
    fun p ↦ Function.uncurry H₁ (Real.smoothTransition (3 * p.1), p.2)
  let g₂ : ℝ × M → Base :=
    fun p ↦ Function.uncurry H₂ (Real.smoothTransition (3 * p.1 - 2), p.2)
  have hg₁_md : ContMDiff (𝓘(ℝ, ℝ).prod I_M) I_B ∞ g₁ :=
    hH₁.comp ((hτ₁_md.comp contMDiff_fst).prodMk contMDiff_snd)
  have hg₂_md : ContMDiff (𝓘(ℝ, ℝ).prod I_M) I_B ∞ g₂ :=
    hH₂.comp ((hτ₂_md.comp contMDiff_fst).prodMk contMDiff_snd)
  refine contMDiffOn_univ.mp fun p _ ↦ ?_
  by_cases hp : p.1 < 2 / 3
  · let U₁ : Set (ℝ × M) := {q : ℝ × M | q.1 < 2 / 3}
    have hU₁_open : IsOpen U₁ := isOpen_Iio.preimage continuous_fst
    have heq₁ : ∀ q ∈ U₁, Function.uncurry (concatSmoothHomotopy H₁ H₂) q = g₁ q := by
      intro q hq
      have hq_lt : q.1 < 2 / 3 := hq
      dsimp only [Function.uncurry, concatSmoothHomotopy, g₁]
      split_ifs with hle
      · rfl
      · rw [Real.smoothTransition.zero_of_nonpos (by linarith),
          Real.smoothTransition.one_of_one_le (by linarith)]
        exact (hjoin q.2).symm
    have hev : Function.uncurry (concatSmoothHomotopy H₁ H₂) =ᶠ[𝓝 p] g₁ :=
      _root_.eventually_nhds_iff.mpr ⟨U₁, heq₁, hU₁_open, hp⟩
    exact (hg₁_md.contMDiffAt.congr_of_eventuallyEq hev).contMDiffWithinAt
  · have hp_gt : (1 / 3 : ℝ) < p.1 := by linarith
    let U₂ : Set (ℝ × M) := {q : ℝ × M | 1 / 3 < q.1}
    have hU₂_open : IsOpen U₂ := isOpen_Ioi.preimage continuous_fst
    have heq₂ : ∀ q ∈ U₂, Function.uncurry (concatSmoothHomotopy H₁ H₂) q = g₂ q := by
      intro q hq
      have hq_gt : (1 / 3 : ℝ) < q.1 := hq
      dsimp only [Function.uncurry, concatSmoothHomotopy, g₂]
      split_ifs with hle
      · rw [Real.smoothTransition.one_of_one_le (by linarith),
          Real.smoothTransition.zero_of_nonpos (by linarith)]
        exact hjoin q.2
      · rfl
    have hev : Function.uncurry (concatSmoothHomotopy H₁ H₂) =ᶠ[𝓝 p] g₂ :=
      _root_.eventually_nhds_iff.mpr ⟨U₂, heq₂, hU₂_open, hp_gt⟩
    exact (hg₂_md.contMDiffAt.congr_of_eventuallyEq hev).contMDiffWithinAt

private theorem wrinkledFibration_mem_closure_baseRegion
    {E_M H_M E_B H_B M Base Fiber : Type*}
    [NormedAddCommGroup E_M] [NormedSpace ℝ E_M] [TopologicalSpace H_M]
    {I_M : ModelWithCorners ℝ E_M H_M}
    [TopologicalSpace M] [ChartedSpace H_M M] [IsManifold I_M ∞ M]
    [NormedAddCommGroup E_B] [NormedSpace ℝ E_B] [TopologicalSpace H_B]
    {I_B : ModelWithCorners ℝ E_B H_B}
    [TopologicalSpace Base] [ChartedSpace H_B Base] [IsManifold I_B ∞ Base]
    [TopologicalSpace Fiber] [ChartedSpace EuclideanPlane Fiber]
    [IsManifold (𝓡 2) ∞ Fiber] [T2Space Fiber] [CompactSpace Fiber] [Nonempty Fiber]
    {W : WrinkledFibration I_M M I_B Base Fiber}
    [T2Space M] [DecidableEq M] {S : Finset M} {p₀ : M} (_hp₀_not : p₀ ∉ S)
    (hp₀_lef : IsRealLefschetzAt I_M I_B W.toFun p₀)
    (hp₀_out : W.toFun p₀ ∉ closure (W.baseRegion : Set Base))
    (hcrit : ∀ p ∈ criticalPoints I_M I_B W.toFun,
      IsIndefiniteFoldAt I_M I_B W.toFun p ∨ IsWrinkledCuspAt I_M I_B W.toFun p ∨
        (p ∈ insert p₀ S ∧ IsRealLefschetzAt I_M I_B W.toFun p ∧
          W.toFun p ∉ closure (W.baseRegion : Set Base))) :
    ∃ (W' : WrinkledFibration I_M M I_B Base Fiber)
      (K₂ : Set M) (H₀ : ℝ → M → Base),
      W'.baseRegion = W.baseRegion ∧
      W'.baseDiskRadius = W.baseDiskRadius ∧
      W'.toFun ⁻¹' closure (W.baseRegion : Set Base) =
        W.toFun ⁻¹' closure (W.baseRegion : Set Base) ∧
      IsCompact K₂ ∧
      Disjoint K₂ (W.toFun ⁻¹' closure (W.baseRegion : Set Base)) ∧
      (∀ p ∈ criticalPoints I_M I_B W.toFun, p ∈ K₂ → p = p₀) ∧
      (∀ x ∉ K₂, W'.toFun x = W.toFun x) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I_M) I_B ∞ (Function.uncurry H₀) ∧
      (∀ x, H₀ 0 x = W.toFun x) ∧
      (∀ x, H₀ 1 x = W'.toFun x) ∧
      (∀ (t : ℝ), ∀ x ∉ K₂, H₀ t x = W.toFun x) ∧
      ∀ p ∈ criticalPoints I_M I_B W'.toFun,
        IsIndefiniteFoldAt I_M I_B W'.toFun p ∨ IsWrinkledCuspAt I_M I_B W'.toFun p ∨
          (p ∈ S ∧ IsRealLefschetzAt I_M I_B W'.toFun p ∧
            W'.toFun p ∉ closure (W.baseRegion : Set Base)) := by
  classical
  obtain ⟨s₀, hs0_pos, hs0_lt_one, hs0_spec⟩ := exists_compactLefschetzWrinkle_collar
  obtain ⟨φ₀, ψ₀, hp₀φ, hfp₀ψ, hφ0, hψ0, hmod⟩ := hp₀_lef
  have hV0_open : IsOpen (ψ₀.source \ closure (W.baseRegion : Set Base)) :=
    ψ₀.open_source.sdiff isClosed_closure
  let ψ₁ := ψ₀.restrOpen (ψ₀.source \ closure (W.baseRegion : Set Base)) hV0_open
  have hψ1_src : ψ₁.source = ψ₀.source \ closure (W.baseRegion : Set Base) := by
    rw [PartialDiffeomorph.restrOpen_source]; exact Set.inter_eq_right.mpr Set.sdiff_subset
  have hU1_open : IsOpen (W.toFun ⁻¹' ψ₁.source) :=
    ψ₁.open_source.preimage W.contMDiff_toFun.continuous
  let φ₁ := φ₀.restrOpen (W.toFun ⁻¹' ψ₁.source) hU1_open
  have hp1_φ : p₀ ∈ φ₁.source := by
    rw [PartialDiffeomorph.restrOpen_source]
    exact ⟨hp₀φ, by rw [Set.mem_preimage, hψ1_src]; exact ⟨hfp₀ψ, hp₀_out⟩⟩
  have h0_φ1_tgt : (0 : EuclideanSpace ℝ (Fin 4)) ∈ φ₁.target := by
    have heq : φ₁ p₀ = 0 := by rw [coe_restrOpen]; exact hφ0
    exact heq ▸ φ₁.map_source hp1_φ
  have h0_ψ1_tgt : (0 : EuclideanPlane) ∈ ψ₁.target := by
    have hfp1 : W.toFun p₀ ∈ ψ₁.source := by rw [hψ1_src]; exact ⟨hfp₀ψ, hp₀_out⟩
    have heq : ψ₁ (W.toFun p₀) = 0 := by
      rw [coe_restrOpen, hψ0]
      exact ext_vec2 (by simp) (by simp)
    exact heq ▸ ψ₁.map_source hfp1
  obtain ⟨δ, hδ_pos, hδ_ball⟩ := Metric.isOpen_iff.mp φ₁.open_target 0 h0_φ1_tgt
  obtain ⟨η, hη_pos, hη_ball⟩ := Metric.isOpen_iff.mp ψ₁.open_target 0 h0_ψ1_tgt
  let R : ℝ := max (3 / δ) (Real.sqrt (41 / η) + 1)
  have hR_pos : 0 < R := lt_max_of_lt_left (by positivity)
  have hR_ne : R ≠ 0 := hR_pos.ne'
  have hR2_ne : R ^ 2 ≠ 0 := pow_ne_zero 2 hR_ne
  let φ := φ₁.trans (cleToPartialDiffeomorph (scaleCLE4 hR_ne))
  let ψ := ψ₁.trans (cleToPartialDiffeomorph (scaleCLE2 hR2_ne))
  have hφ_src' : φ.source = φ₁.source := by
    rw [PartialDiffeomorph.trans_source,
      show (cleToPartialDiffeomorph (scaleCLE4 hR_ne)).source = Set.univ from rfl,
      Set.preimage_univ, Set.inter_univ]
  have hψ_src' : ψ.source = ψ₁.source := by
    rw [PartialDiffeomorph.trans_source,
      show (cleToPartialDiffeomorph (scaleCLE2 hR2_ne)).source = Set.univ from rfl,
      Set.preimage_univ, Set.inter_univ]
  have hball2_sub : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) 2 ⊆ φ.target := by
    intro y hy
    rw [PartialDiffeomorph.trans_target,
      show (cleToPartialDiffeomorph (scaleCLE4 hR_ne)).target = Set.univ from rfl]
    refine ⟨Set.mem_univ _, ?_⟩
    have hy_norm : ‖y‖ ≤ 2 := by simpa [Metric.mem_closedBall, dist_zero_right] using hy
    change R⁻¹ • y ∈ φ₁.target
    apply hδ_ball
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hR_pos]
    have h3 : 3 / δ ≤ R := le_max_left _ _
    rw [← div_eq_inv_mul, div_lt_iff₀ hR_pos]
    nlinarith [(div_le_iff₀ hδ_pos).mp h3]
  have hball40_sub : Metric.closedBall (0 : EuclideanPlane) 40 ⊆ ψ.target := by
    intro z hz
    rw [PartialDiffeomorph.trans_target,
      show (cleToPartialDiffeomorph (scaleCLE2 hR2_ne)).target = Set.univ from rfl]
    refine ⟨Set.mem_univ _, ?_⟩
    have hz_norm : ‖z‖ ≤ 40 := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
    change (R ^ 2)⁻¹ • z ∈ ψ₁.target
    apply hη_ball
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos (sq_pos_of_pos hR_pos)]
    have h41 : Real.sqrt (41 / η) + 1 ≤ R := le_max_right _ _
    have hsq41 : 41 / η < R ^ 2 := by
      have hs41 : Real.sqrt (41 / η) < R := by linarith
      have hs_nn : 0 ≤ Real.sqrt (41 / η) := Real.sqrt_nonneg _
      have hsq : Real.sqrt (41 / η) ^ 2 < R ^ 2 := sq_lt_sq' (by linarith) hs41
      rwa [Real.sq_sqrt (by positivity)] at hsq
    rw [← div_eq_inv_mul, div_lt_iff₀ (sq_pos_of_pos hR_pos)]
    nlinarith [(div_lt_iff₀ hη_pos).mp hsq41]
  have hconj_old :
      ∀ q ∈ φ.source, W.toFun q ∈ ψ.source ∧ ψ (W.toFun q) = realLefschetzMap (φ q) := by
    intro q hq
    rw [hφ_src', PartialDiffeomorph.restrOpen_source] at hq
    refine ⟨hψ_src'.symm ▸ hq.2, ?_⟩
    simp only [φ, ψ, PartialDiffeomorph.coe_trans, Function.comp_apply]
    change R ^ 2 • ψ₁ (W.toFun q) = realLefschetzMap (R • φ₁ q)
    dsimp only [φ₁, ψ₁]
    rw [coe_restrOpen, coe_restrOpen, (hmod q hq.1).2, realLefschetzMap_smul]
  let f' : M → Base :=
    fun q ↦ if q ∈ φ.source then ψ.symm (compactLefschetzWrinkle s₀ (φ q)) else W.toFun q
  have hf'_pos {q : M} (hq : q ∈ φ.source) :
      f' q = ψ.symm (compactLefschetzWrinkle s₀ (φ q)) := by
    dsimp only [f']; split_ifs; rfl
  have hf'_neg {q : M} (hq : q ∉ φ.source) : f' q = W.toFun q := by
    dsimp only [f']; split_ifs; rfl
  let K₂ : Set M := φ.symm '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) 2
  have hK2_sub : K₂ ⊆ φ.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact φ.map_target (hball2_sub hy)
  have hφ_symm_src : φ.symm.source = φ.target := φ.symm_source
  have hK2_compact : IsCompact K₂ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 4)) 2).image_of_continuousOn
      ((φ.symm.contMDiffOn.continuousOn).mono (by rw [hφ_symm_src]; exact hball2_sub))
  have hK2_closed : IsClosed K₂ := hK2_compact.isClosed
  have hK2_disj : Disjoint K₂ (W.toFun ⁻¹' closure (W.baseRegion : Set Base)) := by
    rw [Set.disjoint_left]
    intro q hqK2 hq_cl
    have hmem := (hconj_old q (hK2_sub hqK2)).1
    rw [hψ_src', hψ1_src] at hmem
    exact hmem.2 hq_cl
  have hp0_φ : p₀ ∈ φ.source := hφ_src'.symm ▸ hp1_φ
  have hφ_p0 : φ p₀ = 0 := by
    simp only [φ, PartialDiffeomorph.coe_trans, Function.comp_apply]
    change R • φ₁ p₀ = 0
    rw [coe_restrOpen, hφ0, smul_zero]
  have hK2_crit : ∀ p ∈ criticalPoints I_M I_B W.toFun, p ∈ K₂ → p = p₀ := by
    intro p hp_crit hpK2
    have hpφ : p ∈ φ.source := hK2_sub hpK2
    have hφp_crit : φ p ∈ criticalPoints (𝓡 4) (𝓡 2) realLefschetzMap :=
      (mem_criticalPoints_iff_of_partialDiffeomorph_conj φ ψ W.contMDiff_toFun.contMDiffOn
        contDiff_realLefschetzMap hconj_old hpφ).mp hp_crit
    rw [criticalPoints_realLefschetzMap, Set.mem_singleton_iff] at hφp_crit
    exact φ.injOn hpφ hp0_φ (hφp_crit.trans hφ_p0.symm)
  have hf'_eq_out : ∀ q ∉ K₂, f' q = W.toFun q := by
    intro q hqK2
    by_cases hqφ : q ∈ φ.source
    · have hnotin : φ q ∉ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) 2 := by
        intro hmem
        exact hqK2 ⟨φ q, hmem, φ.left_inv hqφ⟩
      have hge : 2 ≤ ‖φ q‖ := by
        rw [Metric.mem_closedBall, dist_zero_right, not_le] at hnotin
        exact hnotin.le
      rw [hf'_pos hqφ, compactLefschetzWrinkle_eq_realLefschetzMap_of_two_le_norm s₀ hge,
        ← (hconj_old q hqφ).2]
      exact ψ.left_inv (hconj_old q hqφ).1
    · exact hf'_neg hqφ
  have hf'_tgt : ∀ q ∈ φ.source, compactLefschetzWrinkle s₀ (φ q) ∈ ψ.target := by
    intro q hq
    by_cases hnorm : ‖φ q‖ ≤ 2
    · exact hball40_sub (Metric.mem_closedBall.mpr (by
        rw [dist_zero_right]
        exact norm_compactLefschetzWrinkle_le_forty (abs_le.mpr ⟨by linarith, hs0_lt_one.le⟩)
          hnorm))
    · have hge : 2 ≤ ‖φ q‖ := (not_le.mp hnorm).le
      rw [compactLefschetzWrinkle_eq_realLefschetzMap_of_two_le_norm s₀ hge,
        ← (hconj_old q hq).2]
      exact ψ.map_source (hconj_old q hq).1
  have hψ_symm_src : ψ.symm.source = ψ.target := ψ.symm_source
  let H₀ : ℝ → M → Base := fun t q ↦
    if q ∈ φ.source then
      ψ.symm (compactLefschetzWrinkle (Real.smoothTransition t * s₀) (φ q))
    else
      W.toFun q
  have hH0_pos (t : ℝ) {q : M} (hq : q ∈ φ.source) :
      H₀ t q = ψ.symm (compactLefschetzWrinkle (Real.smoothTransition t * s₀) (φ q)) := by
    dsimp only [H₀]; split_ifs; rfl
  have hH0_neg (t : ℝ) {q : M} (hq : q ∉ φ.source) : H₀ t q = W.toFun q := by
    dsimp only [H₀]; split_ifs; rfl
  have hH0_tgt (t : ℝ) :
      ∀ q ∈ φ.source,
        compactLefschetzWrinkle (Real.smoothTransition t * s₀) (φ q) ∈ ψ.target := by
    intro q hq
    have ht0 : 0 ≤ Real.smoothTransition t := Real.smoothTransition.nonneg t
    have ht1 : Real.smoothTransition t ≤ 1 := Real.smoothTransition.le_one t
    have hts_abs : |Real.smoothTransition t * s₀| ≤ 1 :=
      abs_le.mpr ⟨by nlinarith, by nlinarith⟩
    by_cases hnorm : ‖φ q‖ ≤ 2
    · exact hball40_sub (Metric.mem_closedBall.mpr (by
        rw [dist_zero_right]
        exact norm_compactLefschetzWrinkle_le_forty hts_abs hnorm))
    · have hge : 2 ≤ ‖φ q‖ := (not_le.mp hnorm).le
      rw [compactLefschetzWrinkle_eq_realLefschetzMap_of_two_le_norm _ hge,
        ← (hconj_old q hq).2]
      exact ψ.map_source (hconj_old q hq).1
  have hH0_eq_out (t : ℝ) : ∀ q ∉ K₂, H₀ t q = W.toFun q := by
    intro q hqK2
    by_cases hqφ : q ∈ φ.source
    · have hnotin : φ q ∉ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) 2 := by
        intro hmem
        exact hqK2 ⟨φ q, hmem, φ.left_inv hqφ⟩
      have hge : 2 ≤ ‖φ q‖ := by
        rw [Metric.mem_closedBall, dist_zero_right, not_le] at hnotin
        exact hnotin.le
      rw [hH0_pos t hqφ, compactLefschetzWrinkle_eq_realLefschetzMap_of_two_le_norm _ hge,
        ← (hconj_old q hqφ).2]
      exact ψ.left_inv (hconj_old q hqφ).1
    · exact hH0_neg t hqφ
  have hH0_zero : ∀ q : M, H₀ 0 q = W.toFun q := by
    intro q
    by_cases hq : q ∈ φ.source
    · rw [hH0_pos 0 hq, Real.smoothTransition.zero, zero_mul,
        compactLefschetzWrinkle_eq_add_smul, zero_smul, add_zero, ← (hconj_old q hq).2]
      exact ψ.left_inv (hconj_old q hq).1
    · exact hH0_neg 0 hq
  have hH0_one : ∀ q : M, H₀ 1 q = f' q := by
    intro q
    by_cases hq : q ∈ φ.source
    · rw [hH0_pos 1 hq, Real.smoothTransition.one, one_mul, hf'_pos hq]
    · rw [hH0_neg 1 hq, hf'_neg hq]
  have hH0_md : ContMDiff (𝓘(ℝ, ℝ).prod I_M) I_B ∞ (Function.uncurry H₀) := by
    refine contMDiffOn_univ.mp fun p _ ↦ ?_
    by_cases hp : p.2 ∈ φ.source
    · have h_st : ContMDiffAt (𝓘(ℝ, ℝ).prod I_M) 𝓘(ℝ, ℝ) ∞
          (fun z : ℝ × M ↦ Real.smoothTransition z.1 * s₀) p :=
        (((Real.smoothTransition.contDiff (n := ⊤)).mul contDiff_const).contMDiff.comp
          contMDiff_fst).contMDiffAt
      have h_φ : ContMDiffAt (𝓘(ℝ, ℝ).prod I_M) (𝓡 4) ∞ (fun z : ℝ × M ↦ φ z.2) p :=
        (φ.contMDiffOn.contMDiffAt (φ.open_source.mem_nhds hp)).comp p
          contMDiff_snd.contMDiffAt
      have h_rl : ContMDiffAt (𝓘(ℝ, ℝ).prod I_M) (𝓡 2) ∞
          (fun z : ℝ × M ↦ realLefschetzMap (φ z.2)) p :=
        contDiff_realLefschetzMap.contMDiff.contMDiffAt.comp p h_φ
      have h_bp : ContMDiffAt (𝓘(ℝ, ℝ).prod I_M) (𝓡 2) ∞
          (fun z : ℝ × M ↦ lekiliBumpPerturb (φ z.2)) p :=
        contDiff_lekiliBumpPerturb.contMDiff.contMDiffAt.comp p h_φ
      have h_wr : ContMDiffAt (𝓘(ℝ, ℝ).prod I_M) (𝓡 2) ∞
          (fun z : ℝ × M ↦
            compactLefschetzWrinkle (Real.smoothTransition z.1 * s₀) (φ z.2)) p := by
        have heq_fn :
            (fun z : ℝ × M ↦
                compactLefschetzWrinkle (Real.smoothTransition z.1 * s₀) (φ z.2)) =
              fun z : ℝ × M ↦
                realLefschetzMap (φ z.2) +
                  (Real.smoothTransition z.1 * s₀) • lekiliBumpPerturb (φ z.2) := by
          funext z
          exact compactLefschetzWrinkle_eq_add_smul _ _
        rw [heq_fn]
        exact h_rl.add (h_st.smul h_bp)
      have h_ψ : ContMDiffAt (𝓡 2) I_B ∞ ψ.symm
          (compactLefschetzWrinkle (Real.smoothTransition p.1 * s₀) (φ p.2)) :=
        ψ.symm.contMDiffOn.contMDiffAt
          (ψ.symm.open_source.mem_nhds (by rw [hψ_symm_src]; exact hH0_tgt p.1 p.2 hp))
      have hcomp_at : ContMDiffAt (𝓘(ℝ, ℝ).prod I_M) I_B ∞
          (fun z : ℝ × M ↦
            ψ.symm (compactLefschetzWrinkle (Real.smoothTransition z.1 * s₀) (φ z.2))) p :=
        h_ψ.comp p h_wr
      have hev : Function.uncurry H₀ =ᶠ[𝓝 p]
          (fun z : ℝ × M ↦
            ψ.symm (compactLefschetzWrinkle (Real.smoothTransition z.1 * s₀) (φ z.2))) :=
        _root_.eventually_nhds_iff.mpr
          ⟨Set.univ ×ˢ φ.source, fun z hz ↦ hH0_pos z.1 hz.2,
            isOpen_univ.prod φ.open_source, ⟨trivial, hp⟩⟩
      exact (hcomp_at.congr_of_eventuallyEq hev).contMDiffWithinAt
    · have hpK2 : p.2 ∈ K₂ᶜ := fun hm ↦ hp (hK2_sub hm)
      have hev : Function.uncurry H₀ =ᶠ[𝓝 p] (fun z : ℝ × M ↦ W.toFun z.2) :=
        _root_.eventually_nhds_iff.mpr
          ⟨Set.univ ×ˢ K₂ᶜ, fun z hz ↦ hH0_eq_out z.1 z.2 hz.2,
            isOpen_univ.prod hK2_closed.isOpen_compl, ⟨trivial, hpK2⟩⟩
      exact (((W.contMDiff_toFun.comp contMDiff_snd).contMDiffAt).congr_of_eventuallyEq
        hev).contMDiffWithinAt
  have hf'_md : ContMDiff I_M I_B ∞ f' := by
    refine contMDiffOn_univ.mp fun q _ ↦ ?_
    by_cases hq : q ∈ φ.source
    · have hcomp_at : ContMDiffAt I_M I_B ∞
          (fun z ↦ ψ.symm (compactLefschetzWrinkle s₀ (φ z))) q := by
        have h1 : ContMDiffAt (𝓡 4) (𝓡 2) ∞ (compactLefschetzWrinkle s₀) (φ q) :=
          (contDiff_compactLefschetzWrinkle s₀).contMDiff.contMDiffAt
        have h2 : ContMDiffAt I_M (𝓡 4) ∞ φ q :=
          φ.contMDiffOn.contMDiffAt (φ.open_source.mem_nhds hq)
        have h3 : ContMDiffAt (𝓡 2) I_B ∞ ψ.symm (compactLefschetzWrinkle s₀ (φ q)) :=
          ψ.symm.contMDiffOn.contMDiffAt
            (ψ.symm.open_source.mem_nhds (by rw [hψ_symm_src]; exact hf'_tgt q hq))
        exact h3.comp q (h1.comp q h2)
      have hev : f' =ᶠ[𝓝 q] (fun z ↦ ψ.symm (compactLefschetzWrinkle s₀ (φ z))) :=
        _root_.eventually_nhds_iff.mpr
          ⟨φ.source, fun z hz ↦ hf'_pos hz, φ.open_source, hq⟩
      exact (hcomp_at.congr_of_eventuallyEq hev).contMDiffWithinAt
    · have hqK2 : q ∈ K₂ᶜ := fun hm ↦ hq (hK2_sub hm)
      have hev : f' =ᶠ[𝓝 q] W.toFun :=
        _root_.eventually_nhds_iff.mpr ⟨K₂ᶜ, hf'_eq_out, hK2_closed.isOpen_compl, hqK2⟩
      exact (W.contMDiff_toFun.contMDiffAt.congr_of_eventuallyEq hev).contMDiffWithinAt
  have hpre_clos_eq :
      f' ⁻¹' closure (W.baseRegion : Set Base) =
        W.toFun ⁻¹' closure (W.baseRegion : Set Base) := by
    ext q
    simp only [Set.mem_preimage]
    by_cases hq : q ∈ φ.source
    · have hfq1 : f' q ∉ closure (W.baseRegion : Set Base) := by
        rw [hf'_pos hq]
        have hmem_src : ψ.symm (compactLefschetzWrinkle s₀ (φ q)) ∈ ψ.source :=
          ψ.map_target (hf'_tgt q hq)
        rw [hψ_src', hψ1_src] at hmem_src
        exact hmem_src.2
      have hw1 : W.toFun q ∉ closure (W.baseRegion : Set Base) := by
        have hmem := (hconj_old q hq).1
        rw [hψ_src', hψ1_src] at hmem
        exact hmem.2
      exact ⟨fun hm ↦ absurd hm hfq1, fun hm ↦ absurd hm hw1⟩
    · rw [hf'_neg hq]
  have hpre_eq : f' ⁻¹' W.baseRegion.1 = W.toFun ⁻¹' W.baseRegion.1 := by
    ext q
    simp only [Set.mem_preimage]
    by_cases hq : q ∈ φ.source
    · have hfq1 : f' q ∉ closure (W.baseRegion : Set Base) := by
        rw [hf'_pos hq]
        have hmem_src : ψ.symm (compactLefschetzWrinkle s₀ (φ q)) ∈ ψ.source :=
          ψ.map_target (hf'_tgt q hq)
        rw [hψ_src', hψ1_src] at hmem_src
        exact hmem_src.2
      have hw1 : W.toFun q ∉ closure (W.baseRegion : Set Base) := by
        have hmem := (hconj_old q hq).1
        rw [hψ_src', hψ1_src] at hmem
        exact hmem.2
      exact ⟨fun hm ↦ absurd (subset_closure hm) hfq1, fun hm ↦ absurd (subset_closure hm) hw1⟩
    · rw [hf'_neg hq]
  have hpre_val : ∀ x ∈ f' ⁻¹' W.baseRegion.1, f' x = W.toFun x := by
    intro x hx
    rw [hpre_eq] at hx
    have hx_not : x ∉ φ.source := fun hxφ ↦ by
      have hmem := (hconj_old x hxφ).1
      rw [hψ_src', hψ1_src] at hmem
      exact hmem.2 (subset_closure hx)
    exact hf'_neg hx_not
  have hconj_new :
      ∀ q ∈ φ.source, f' q ∈ ψ.source ∧ ψ (f' q) = compactLefschetzWrinkle s₀ (φ q) := by
    intro q hq
    rw [hf'_pos hq]
    exact ⟨ψ.map_target (hf'_tgt q hq), ψ.right_inv (hf'_tgt q hq)⟩
  let preOpen' : TopologicalSpace.Opens M :=
    ⟨f' ⁻¹' W.baseRegion.1, W.baseRegion.2.preimage hf'_md.continuous⟩
  have hpre_mem {m : M} : m ∈ preOpen' ↔ m ∈ W.preimageOpen := by
    change m ∈ f' ⁻¹' W.baseRegion.1 ↔ m ∈ W.toFun ⁻¹' W.baseRegion.1
    rw [hpre_eq]
  let triv'To : preOpen' → W.baseRegion × Fiber :=
    fun m ↦ W.trivialization ⟨m.1, hpre_mem.mp m.2⟩
  let triv'Inv : W.baseRegion × Fiber → preOpen' :=
    fun bz ↦ ⟨(W.trivialization.symm bz).1, hpre_mem.mpr (W.trivialization.symm bz).2⟩
  let triv' : preOpen' ≃ₘ⟮I_M, I_B.prod (𝓡 2)⟯ (W.baseRegion × Fiber) :=
    { toFun := triv'To
      invFun := triv'Inv
      left_inv m := by
        apply Subtype.ext
        dsimp only [triv'To, triv'Inv]
        have h := congrArg Subtype.val (W.trivialization.symm_apply_apply ⟨m.1, hpre_mem.mp m.2⟩)
        exact h
      right_inv bz := by
        dsimp only [triv'To, triv'Inv]
        have hsub :
            (⟨(W.trivialization.symm bz).1, (W.trivialization.symm bz).2⟩ :
              W.preimageOpen) = W.trivialization.symm bz :=
          Subtype.ext rfl
        have hr := W.trivialization.apply_symm_apply bz
        convert hr
      contMDiff_toFun := by
        have hm_incl :
            ContMDiff I_M I_M ∞ (fun m : preOpen' ↦
              (⟨m.1, hpre_mem.mp m.2⟩ : W.preimageOpen)) :=
          (TauCeti.ContMDiff.subtypeVal_comp_iff W.preimageOpen _).mp contMDiff_subtype_val
        exact W.trivialization.contMDiff.comp hm_incl
      contMDiff_invFun := by
        refine (TauCeti.ContMDiff.subtypeVal_comp_iff preOpen' triv'Inv).mp ?_
        change ContMDiff (I_B.prod (𝓡 2)) I_M ∞ (Subtype.val ∘ ⇑W.trivialization.symm)
        exact contMDiff_subtype_val.comp W.trivialization.symm.contMDiff }
  have hreg_pre' : ∀ q ∈ f' ⁻¹' W.baseRegion.1, Function.Surjective (mfderiv I_M I_B f' q) := by
    intro q hq
    have hq_old : q ∈ W.toFun ⁻¹' W.baseRegion.1 := hpre_eq ▸ hq
    have hq_notK2 : q ∉ K₂ := fun hqK2 ↦ by
      have hqφ := hK2_sub hqK2
      have hmem := (hconj_old q hqφ).1
      rw [hψ_src', hψ1_src] at hmem
      exact hmem.2 (subset_closure hq_old)
    have hev : f' =ᶠ[𝓝 q] W.toFun :=
      _root_.eventually_nhds_iff.mpr ⟨K₂ᶜ, hf'_eq_out, hK2_closed.isOpen_compl, hq_notK2⟩
    exact (surjective_mfderiv_congr_of_eventuallyEq hev).mpr (W.regular_on_preimage q hq_old)
  let W' : WrinkledFibration I_M M I_B Base Fiber :=
    { toFun := f'
      contMDiff_toFun := hf'_md
      baseRegion := W.baseRegion
      baseRegion_nonempty := W.baseRegion_nonempty
      regular_on_preimage := hreg_pre'
      baseDiskRadius := W.baseDiskRadius
      baseDiskRadius_pos := W.baseDiskRadius_pos
      baseDisk := W.baseDisk
      trivialization := triv'
      trivialization_fst := fun p ↦ by
        have hfst := W.trivialization_fst ⟨p.1, hpre_mem.mp p.2⟩
        apply Subtype.ext
        have hval := congrArg Subtype.val hfst
        change (W.trivialization ⟨p.1, hpre_mem.mp p.2⟩).1.1 = f' p.1
        rw [hval, hpre_val p.1 p.2] }
  refine ⟨W', K₂, H₀, rfl, rfl, hpre_clos_eq, hK2_compact, hK2_disj, hK2_crit, hf'_eq_out,
    hH0_md, hH0_zero, hH0_one, hH0_eq_out, fun p hp_crit ↦ ?_⟩
  by_cases hpφ : p ∈ φ.source
  · have hφp_crit : φ p ∈ criticalPoints (𝓡 4) (𝓡 2) (compactLefschetzWrinkle s₀) :=
      (mem_criticalPoints_iff_of_partialDiffeomorph_conj φ ψ hf'_md.contMDiffOn
        (contDiff_compactLefschetzWrinkle s₀) hconj_new hpφ).mp hp_crit
    rcases (hs0_spec s₀ hs0_pos le_rfl).2 (φ p) hφp_crit with hfold | hcusp
    · exact Or.inl (isLocallyModeledOn_of_partialDiffeomorph_conj φ ψ hconj_new hpφ hfold)
    · exact Or.inr (Or.inl (isLocallyModeledOn_of_partialDiffeomorph_conj φ ψ hconj_new hpφ hcusp))
  · have hpK2 : p ∉ K₂ := fun hm ↦ hpφ (hK2_sub hm)
    have hev : f' =ᶠ[𝓝 p] W.toFun :=
      _root_.eventually_nhds_iff.mpr ⟨K₂ᶜ, hf'_eq_out, hK2_closed.isOpen_compl, hpK2⟩
    have hp_old : p ∈ criticalPoints I_M I_B W.toFun := by
      change ¬ Function.Surjective (mfderiv I_M I_B f' p) at hp_crit
      exact (surjective_mfderiv_congr_of_eventuallyEq hev).not.mp hp_crit
    rcases hcrit p hp_old with hfold | hcusp | ⟨hp_mem, hp_lef, hp_out⟩
    · exact Or.inl (isIndefiniteFoldAt_congr hev.symm hfold)
    · exact Or.inr (Or.inl (isWrinkledCuspAt_congr hev.symm hcusp))
    · have hp_ne : p ≠ p₀ := fun h ↦ hpφ (h ▸ (by rw [hφ_src']; exact hp1_φ))
      have hpS : p ∈ S := (Finset.mem_insert.mp hp_mem).resolve_left hp_ne
      refine Or.inr (Or.inr ⟨hpS, isLocallyModeledOn_congr hev.symm hp_lef, ?_⟩)
      change f' p ∉ closure (W.baseRegion : Set Base)
      rwa [hf'_eq_out p hpK2]

private theorem not_isolated_criticalPoint_indefiniteFoldMap
    {y : EuclideanSpace ℝ (Fin 4)}
    (hy : y ∈ criticalPoints (𝓡 4) (𝓡 2) indefiniteFoldMap) :
    ∀ U ∈ 𝓝 y, ∃ y' ∈ U, y' ≠ y ∧ y' ∈ criticalPoints (𝓡 4) (𝓡 2) indefiniteFoldMap := by
  intro U hU
  rw [criticalPoints_indefiniteFoldMap, Set.mem_ofPred_eq] at hy
  have hcont : Continuous (fun δ : ℝ ↦ y + vec4 0 0 0 δ) :=
    continuous_const.add (continuous_vec4 continuous_const continuous_const continuous_const
      continuous_id)
  have h0 : y + vec4 0 0 0 0 = y := by
    ext i; fin_cases i <;> simp [vec4_zero, vec4_one, vec4_two, vec4_three]
  have hev : ∀ᶠ δ in 𝓝 (0 : ℝ), y + vec4 0 0 0 δ ∈ U :=
    hcont.continuousAt.preimage_mem_nhds (by rw [h0]; exact hU)
  obtain ⟨δ₀, hδ0_pos, hδ0_sub⟩ := Metric.eventually_nhds_iff_ball.mp hev
  let δ := δ₀ / 2
  have hδ_pos : 0 < δ := half_pos hδ0_pos
  have hδ_mem : δ ∈ Metric.ball (0 : ℝ) δ₀ := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hδ_pos]
    dsimp only [δ]
    linarith
  refine ⟨y + vec4 0 0 0 δ, hδ0_sub δ hδ_mem, ?_, ?_⟩
  · intro heq
    have h3 := congrArg (fun v : EuclideanSpace ℝ (Fin 4) ↦ v 3) heq
    simp only [PiLp.add_apply, vec4_three] at h3
    linarith
  · rw [criticalPoints_indefiniteFoldMap, Set.mem_ofPred_eq]
    simp only [PiLp.add_apply, vec4_zero, vec4_one, vec4_two, hy.1, hy.2.1, hy.2.2, add_zero,
      and_self]

private theorem finite_realLefschetzPoints_of_brokenLefschetz
    {E_M H_M E_B H_B M Base Fiber : Type*}
    [NormedAddCommGroup E_M] [NormedSpace ℝ E_M] [TopologicalSpace H_M]
    {I_M : ModelWithCorners ℝ E_M H_M}
    [TopologicalSpace M] [ChartedSpace H_M M] [IsManifold I_M ∞ M] [CompactSpace M]
    [NormedAddCommGroup E_B] [NormedSpace ℝ E_B] [TopologicalSpace H_B]
    {I_B : ModelWithCorners ℝ E_B H_B}
    [TopologicalSpace Base] [ChartedSpace H_B Base] [IsManifold I_B ∞ Base]
    [TopologicalSpace Fiber] [ChartedSpace EuclideanPlane Fiber]
    [IsManifold (𝓡 2) ∞ Fiber] [T2Space Fiber] [CompactSpace Fiber] [Nonempty Fiber]
    (B : BrokenLefschetzFibration I_M M I_B Base Fiber) :
    {p ∈ criticalPoints I_M I_B B.toFun | IsRealLefschetzAt I_M I_B B.toFun p}.Finite := by
  have hfd_B : FiniteDimensional ℝ E_B := by
    let x₀ : B.baseDiskOpen := ⟨0, Metric.mem_ball_self B.baseDiskRadius_pos⟩
    let y₀ : B.baseRegion := B.baseDisk x₀
    have hL_md : MDifferentiableAt (𝓡 2) I_B (⇑B.baseDisk) (B.baseDisk.symm y₀) :=
      (B.baseDisk.contMDiff.contMDiffAt).mdifferentiableAt (by simp)
    have hR_md : MDifferentiableAt I_B (𝓡 2) (⇑B.baseDisk.symm) y₀ :=
      (B.baseDisk.symm.contMDiff.contMDiffAt).mdifferentiableAt (by simp)
    have hev : (⇑B.baseDisk ∘ ⇑B.baseDisk.symm) =ᶠ[𝓝 y₀] id :=
      Filter.Eventually.of_forall fun y ↦ B.baseDisk.apply_symm_apply y
    have hcm := mfderiv_comp (x := y₀) hL_md hR_md
    have heq : (mfderiv (𝓡 2) I_B B.baseDisk (B.baseDisk.symm y₀)).comp
        (mfderiv I_B (𝓡 2) B.baseDisk.symm y₀) =
        (tangentSpaceCast I_B (id y₀) ((⇑B.baseDisk ∘ ⇑B.baseDisk.symm) y₀) :
          TangentSpace I_B (id y₀) →L[ℝ]
            TangentSpace I_B ((⇑B.baseDisk ∘ ⇑B.baseDisk.symm) y₀)).comp
          (ContinuousLinearMap.id ℝ (TangentSpace I_B y₀)) := by
      rw [← hcm, hev.mfderiv_eq, mfderiv_id]
    have hsurj_comp : Function.Surjective
        (⇑(mfderiv (𝓡 2) I_B B.baseDisk (B.baseDisk.symm y₀)) ∘
          ⇑(mfderiv I_B (𝓡 2) B.baseDisk.symm y₀)) := by
      have hcoe : ⇑((mfderiv (𝓡 2) I_B B.baseDisk (B.baseDisk.symm y₀)).comp
          (mfderiv I_B (𝓡 2) B.baseDisk.symm y₀)) =
          ⇑(tangentSpaceCast I_B (id y₀) ((⇑B.baseDisk ∘ ⇑B.baseDisk.symm) y₀)) := by
        rw [heq]; rfl
      change Function.Surjective ⇑((mfderiv (𝓡 2) I_B B.baseDisk (B.baseDisk.symm y₀)).comp
        (mfderiv I_B (𝓡 2) B.baseDisk.symm y₀))
      rw [hcoe]
      exact (tangentSpaceCast I_B (id y₀) ((⇑B.baseDisk ∘ ⇑B.baseDisk.symm) y₀)).surjective
    have hsurj : Function.Surjective
        (mfderiv (𝓡 2) I_B B.baseDisk (B.baseDisk.symm y₀)).toLinearMap :=
      hsurj_comp.of_comp
    exact Module.Finite.of_surjective _ hsurj
  let L_real : Set M :=
    {p ∈ criticalPoints I_M I_B B.toFun | IsRealLefschetzAt I_M I_B B.toFun p}
  have hcov : ∀ p : M, ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ (U ∩ L_real).Subsingleton := by
    intro p
    by_cases hp : p ∈ criticalPoints I_M I_B B.toFun
    · rcases B.singularities_broken_lefschetz p hp with hp_lef | hp_fold
      · obtain ⟨U, hU_open, hpU, hU_eq⟩ :=
          isolated_criticalPoint_of_isRealLefschetzAt B.contMDiff_toFun hp_lef
        refine ⟨U, hU_open, hpU, fun x hx y hy ↦ ?_⟩
        have hx0 : x = p := by
          have : x ∈ U ∩ criticalPoints I_M I_B B.toFun := ⟨hx.1, hx.2.1⟩
          rwa [hU_eq, Set.mem_singleton_iff] at this
        have hy0 : y = p := by
          have : y ∈ U ∩ criticalPoints I_M I_B B.toFun := ⟨hy.1, hy.2.1⟩
          rwa [hU_eq, Set.mem_singleton_iff] at this
        exact hx0.trans hy0.symm
      · obtain ⟨φ, ψ, hpφ, _, _, _, hmod⟩ := hp_fold
        refine ⟨φ.source, φ.open_source, hpφ, fun q hq _ _ ↦ ?_⟩
        exfalso
        rcases hq with ⟨hqφ, hq_crit, hq_lef⟩
        obtain ⟨V, hV_open, hqV, hV_eq⟩ :=
          isolated_criticalPoint_of_isRealLefschetzAt B.contMDiff_toFun hq_lef
        have hφq_crit : φ q ∈ criticalPoints (𝓡 4) (𝓡 2) indefiniteFoldMap :=
          (mem_criticalPoints_iff_of_partialDiffeomorph_conj φ ψ B.contMDiff_toFun.contMDiffOn
            contDiff_indefiniteFoldMap hmod hqφ).mp hq_crit
        have hφ_symm_src : φ.symm.source = φ.target := φ.symm_source
        have hnbhd : φ.symm ⁻¹' (φ.source ∩ V) ∩ φ.target ∈ 𝓝 (φ q) := by
          have h1 : φ.source ∩ V ∈ 𝓝 q := (φ.open_source.inter hV_open).mem_nhds ⟨hqφ, hqV⟩
          have hpre : φ.symm ⁻¹' (φ.source ∩ V) ∈ 𝓝 (φ q) :=
            (φ.symm.contMDiffOn.continuousOn.continuousAt
              (φ.symm.open_source.mem_nhds
                (by rw [hφ_symm_src]; exact φ.map_source hqφ))).preimage_mem_nhds
              (by simpa [φ.left_inv hqφ] using h1)
          exact Filter.inter_mem hpre (φ.open_target.mem_nhds (φ.map_source hqφ))
        obtain ⟨y', ⟨hy'_pre, hy'_tgt⟩, hy'_ne, hy'_crit⟩ :=
          not_isolated_criticalPoint_indefiniteFoldMap hφq_crit _ hnbhd
        set q' := φ.symm y'
        have hq'_src : q' ∈ φ.source := hy'_pre.1
        have hq'_V : q' ∈ V := hy'_pre.2
        have hφq' : φ q' = y' := φ.right_inv hy'_tgt
        have hq'_crit : q' ∈ criticalPoints I_M I_B B.toFun :=
          (mem_criticalPoints_iff_of_partialDiffeomorph_conj φ ψ B.contMDiff_toFun.contMDiffOn
            contDiff_indefiniteFoldMap hmod hq'_src).mpr (by rwa [hφq'])
        have hq'_eq : q' = q := by
          have : q' ∈ V ∩ criticalPoints I_M I_B B.toFun := ⟨hq'_V, hq'_crit⟩
          rwa [hV_eq, Set.mem_singleton_iff] at this
        exact hy'_ne (hφq' ▸ congrArg φ hq'_eq)
    · have hreg_open : IsOpen {q : M | TauCeti.IsRegularPoint I_M I_B B.toFun q} :=
        TauCeti.isOpen_setOf_isRegularPoint B.contMDiff_toFun (by simp)
      have hp_reg : TauCeti.IsRegularPoint I_M I_B B.toFun p :=
        TauCeti.isRegularPoint_iff.mpr (notMem_criticalPoints_iff.mp hp)
      refine ⟨{q : M | TauCeti.IsRegularPoint I_M I_B B.toFun q}, hreg_open, hp_reg,
        fun x hx _ _ ↦ ?_⟩
      exact absurd (TauCeti.isRegularPoint_iff.mp hx.1) (mem_criticalPoints_iff.mp hx.2.1)
  choose U hU_open hU_mem hU_sub using hcov
  obtain ⟨t, ht_cov⟩ := isCompact_univ.elim_finite_subcover U hU_open fun p _ ↦
    Set.mem_iUnion.mpr ⟨p, hU_mem p⟩
  have hsub : L_real ⊆ ⋃ p ∈ t, (U p ∩ L_real) := fun x hx ↦ by
    obtain ⟨p, hp_t, hxU⟩ := Set.mem_iUnion₂.mp (ht_cov (Set.mem_univ x))
    exact Set.mem_iUnion₂.mpr ⟨p, hp_t, hxU, hx⟩
  exact (t.finite_toSet.biUnion fun p _ ↦ (hU_sub p).finite).subset hsub

/-- **Broken-to-Purely-Wrinkled Surgery on Compact 4-Manifolds (Disjoint Closure Case)**:
if every real Lefschetz critical point of a broken Lefschetz fibration `B` maps outside
`closure B.baseRegion.1`, repeated compactly supported Lekili Move 1 wrinkling (`Lekili 2009`,
§3.1 & §4 / Theorem 4) eliminates all real Lefschetz points via a smooth global homotopy
`H : ℝ → M → Base` (`H 0 = B.toFun`, `H 1 = P.toFun`) supported inside a compact set `K ⊆ M`
disjoint from `B.toFun ⁻¹' closure B.baseRegion.1` and from all non-Lefschetz critical points of
`B`, while preserving `baseRegion` and `baseDiskRadius`. -/
-- tier: T2
theorem BrokenLefschetzFibration.exists_purelyWrinkledFibration_of_disjoint_closure
    {E_M H_M E_B H_B M Base Fiber : Type*}
    [NormedAddCommGroup E_M] [NormedSpace ℝ E_M] [TopologicalSpace H_M]
    {I_M : ModelWithCorners ℝ E_M H_M}
    [TopologicalSpace M] [ChartedSpace H_M M] [IsManifold I_M ∞ M] [CompactSpace M] [T2Space M]
    [NormedAddCommGroup E_B] [NormedSpace ℝ E_B] [TopologicalSpace H_B]
    {I_B : ModelWithCorners ℝ E_B H_B}
    [TopologicalSpace Base] [ChartedSpace H_B Base] [IsManifold I_B ∞ Base]
    [TopologicalSpace Fiber] [ChartedSpace EuclideanPlane Fiber]
    [IsManifold (𝓡 2) ∞ Fiber] [T2Space Fiber] [CompactSpace Fiber] [Nonempty Fiber]
    (B : BrokenLefschetzFibration I_M M I_B Base Fiber)
    (hdisj : ∀ p ∈ criticalPoints I_M I_B B.toFun,
      IsRealLefschetzAt I_M I_B B.toFun p → B.toFun p ∉ closure (B.baseRegion : Set Base)) :
    ∃ (P : PurelyWrinkledFibration I_M M I_B Base Fiber)
      (K : Set M) (H : ℝ → M → Base),
      P.baseRegion = B.baseRegion ∧
      P.baseDiskRadius = B.baseDiskRadius ∧
      IsCompact K ∧
      Disjoint K (B.toFun ⁻¹' closure (B.baseRegion : Set Base)) ∧
      (∀ p ∈ criticalPoints I_M I_B B.toFun,
        ¬ IsRealLefschetzAt I_M I_B B.toFun p → p ∉ K) ∧
      (∀ x ∉ K, P.toFun x = B.toFun x) ∧
      (∀ x ∈ P.toFun ⁻¹' P.baseRegion.1, P.toFun x = B.toFun x) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I_M) I_B ∞ (Function.uncurry H) ∧
      (∀ x, H 0 x = B.toFun x) ∧
      (∀ x, H 1 x = P.toFun x) ∧
      ∀ (t : ℝ), ∀ x ∉ K, H t x = B.toFun x := by
  classical
  have hfin := finite_realLefschetzPoints_of_brokenLefschetz B
  have hstep :
      ∀ S : Finset M,
        ∀ W : WrinkledFibration I_M M I_B Base Fiber,
          (∀ p ∈ criticalPoints I_M I_B W.toFun,
            IsIndefiniteFoldAt I_M I_B W.toFun p ∨ IsWrinkledCuspAt I_M I_B W.toFun p ∨
              (p ∈ S ∧ IsRealLefschetzAt I_M I_B W.toFun p ∧
                W.toFun p ∉ closure (W.baseRegion : Set Base))) →
          ∃ (P : PurelyWrinkledFibration I_M M I_B Base Fiber)
            (K : Set M) (H : ℝ → M → Base),
            P.baseRegion = W.baseRegion ∧
            P.baseDiskRadius = W.baseDiskRadius ∧
            P.toFun ⁻¹' closure (W.baseRegion : Set Base) =
              W.toFun ⁻¹' closure (W.baseRegion : Set Base) ∧
            IsCompact K ∧
            Disjoint K (W.toFun ⁻¹' closure (W.baseRegion : Set Base)) ∧
            (∀ p ∈ criticalPoints I_M I_B W.toFun,
              ¬ IsRealLefschetzAt I_M I_B W.toFun p → p ∉ K) ∧
            (∀ x ∉ K, P.toFun x = W.toFun x) ∧
            ContMDiff (𝓘(ℝ, ℝ).prod I_M) I_B ∞ (Function.uncurry H) ∧
            (∀ x, H 0 x = W.toFun x) ∧
            (∀ x, H 1 x = P.toFun x) ∧
            ∀ (t : ℝ), ∀ x ∉ K, H t x = W.toFun x := by
    intro S
    induction S using Finset.induction with
    | empty =>
      intro W hcrit
      refine ⟨⟨W, fun p hp ↦ ?_⟩, ∅, fun _ x ↦ W.toFun x, rfl, rfl, rfl, isCompact_empty,
        by simp, fun _ _ _ hp ↦ hp, fun _ _ ↦ rfl,
        W.contMDiff_toFun.comp contMDiff_snd, fun _ ↦ rfl, fun _ ↦ rfl, fun _ _ _ ↦ rfl⟩
      rcases hcrit p hp with hfold | hcusp | ⟨hmem, _⟩
      · exact Or.inl hfold
      · exact Or.inr hcusp
      · exact absurd hmem (Finset.notMem_empty p)
    | @insert a S' ha ih =>
      intro W hcrit
      by_cases ha_cond : a ∈ criticalPoints I_M I_B W.toFun ∧
          IsRealLefschetzAt I_M I_B W.toFun a ∧
          W.toFun a ∉ closure (W.baseRegion : Set Base)
      · obtain ⟨W', K₁, H₁, hreg', hrad', hpre_clos', hK₁_comp, hK₁_disj, hK₁_crit, hW'_out,
            hH₁_md, hH₁_0, hH₁_1, hH₁_stat, hcrit'⟩ :=
          wrinkledFibration_mem_closure_baseRegion ha ha_cond.2.1 ha_cond.2.2 hcrit
        obtain ⟨P, K₂, H₂, hP_reg, hP_rad, hP_pre_clos, hK₂_comp, hK₂_disj, hK₂_crit, hP_out,
            hH₂_md, hH₂_0, hH₂_1, hH₂_stat⟩ :=
          ih W' (fun p hp ↦ by simpa only [hreg'] using hcrit' p hp)
        have hK₂_disj' : Disjoint K₂ (W.toFun ⁻¹' closure (W.baseRegion : Set Base)) := by
          rwa [hreg', hpre_clos'] at hK₂_disj
        refine ⟨P, K₁ ∪ K₂, concatSmoothHomotopy H₁ H₂,
          hP_reg.trans hreg', hP_rad.trans hrad', ?_,
          hK₁_comp.union hK₂_comp, hK₁_disj.union_left hK₂_disj', ?_, ?_,
          contMDiff_uncurry_concatSmoothHomotopy hH₁_md hH₂_md
            (fun x ↦ (hH₁_1 x).trans (hH₂_0 x).symm),
          fun x ↦ (concatSmoothHomotopy_zero H₁ H₂ x).trans (hH₁_0 x),
          fun x ↦ (concatSmoothHomotopy_one H₁ H₂ x).trans (hH₂_1 x),
          fun t x hx ↦ concatSmoothHomotopy_stationary hH₁_stat hH₂_stat hW'_out t hx⟩
        · calc
            P.toFun ⁻¹' closure (W.baseRegion : Set Base)
              = P.toFun ⁻¹' closure (W'.baseRegion : Set Base) := by rw [hreg']
            _ = W'.toFun ⁻¹' closure (W'.baseRegion : Set Base) := hP_pre_clos
            _ = W'.toFun ⁻¹' closure (W.baseRegion : Set Base) := by rw [hreg']
            _ = W.toFun ⁻¹' closure (W.baseRegion : Set Base) := hpre_clos'
        · intro p hp_crit hp_not_lef
          have hp_not_K₁ : p ∉ K₁ := fun hpK₁ ↦
            hp_not_lef (hK₁_crit p hp_crit hpK₁ ▸ ha_cond.2.1)
          have hev : W'.toFun =ᶠ[𝓝 p] W.toFun :=
            _root_.eventually_nhds_iff.mpr
              ⟨K₁ᶜ, hW'_out, hK₁_comp.isClosed.isOpen_compl, hp_not_K₁⟩
          have hp_crit' : p ∈ criticalPoints I_M I_B W'.toFun := by
            rw [mem_criticalPoints_iff] at hp_crit ⊢
            exact (surjective_mfderiv_congr_of_eventuallyEq hev).not.mpr hp_crit
          have hp_not_lef' : ¬ IsRealLefschetzAt I_M I_B W'.toFun p := fun hl ↦
            hp_not_lef (isLocallyModeledOn_congr hev hl)
          have hp_not_K₂ : p ∉ K₂ := hK₂_crit p hp_crit' hp_not_lef'
          exact fun hm ↦ hm.elim hp_not_K₁ hp_not_K₂
        · intro x hx
          have hx₁ : x ∉ K₁ := fun hm ↦ hx (Set.mem_union_left K₂ hm)
          have hx₂ : x ∉ K₂ := fun hm ↦ hx (Set.mem_union_right K₁ hm)
          exact (hP_out x hx₂).trans (hW'_out x hx₁)
      · refine ih W fun p hp ↦ ?_
        rcases hcrit p hp with hfold | hcusp | ⟨hp_mem, hp_lef, hp_out⟩
        · exact Or.inl hfold
        · exact Or.inr (Or.inl hcusp)
        · have hp_ne : p ≠ a := by
            rintro rfl
            exact ha_cond ⟨hp, hp_lef, hp_out⟩
          exact Or.inr (Or.inr ⟨(Finset.mem_insert.mp hp_mem).resolve_left hp_ne, hp_lef, hp_out⟩)
  obtain ⟨P, K, H, hP_reg, hP_rad, hP_pre_clos, hK_comp, hK_disj, hK_crit, hP_out,
      hH_md, hH_0, hH_1, hH_stat⟩ :=
    hstep hfin.toFinset B.toWrinkledFibration fun p hp ↦ by
      rcases B.singularities_broken_lefschetz p hp with hp_lef | hp_fold
      · exact Or.inr (Or.inr ⟨hfin.mem_toFinset.mpr ⟨hp, hp_lef⟩, hp_lef, hdisj p hp hp_lef⟩)
      · exact Or.inl hp_fold
  refine ⟨P, K, H, hP_reg, hP_rad, hK_comp, hK_disj, hK_crit, hP_out, ?_,
    hH_md, hH_0, hH_1, hH_stat⟩
  intro x hx
  have hx_cl : x ∈ P.toFun ⁻¹' closure (B.baseRegion : Set Base) :=
    subset_closure (by simpa [hP_reg] using hx)
  have hx_B_cl : x ∈ B.toFun ⁻¹' closure (B.baseRegion : Set Base) :=
    hP_pre_clos ▸ hx_cl
  have hx_not_K : x ∉ K := Set.disjoint_right.mp hK_disj hx_B_cl
  exact hP_out x hx_not_K

/-- Shrinks the regular base disk of a `WrinkledFibration` to half radius `W.baseDiskRadius / 2`,
ensuring `closure W'.baseRegion.1 ⊆ W.baseRegion.1` (disjoint from `W.toFun '' Crit(W)`). -/
-- tier: T2
noncomputable def WrinkledFibration.shrinkBaseHalf
    {E_M H_M E_B H_B M Base Fiber : Type*}
    [NormedAddCommGroup E_M] [NormedSpace ℝ E_M] [TopologicalSpace H_M]
    {I_M : ModelWithCorners ℝ E_M H_M}
    [TopologicalSpace M] [ChartedSpace H_M M] [IsManifold I_M ∞ M]
    [NormedAddCommGroup E_B] [NormedSpace ℝ E_B] [TopologicalSpace H_B]
    {I_B : ModelWithCorners ℝ E_B H_B}
    [TopologicalSpace Base] [ChartedSpace H_B Base] [IsManifold I_B ∞ Base] [T2Space Base]
    [TopologicalSpace Fiber] [ChartedSpace EuclideanPlane Fiber]
    [IsManifold (𝓡 2) ∞ Fiber] [T2Space Fiber] [CompactSpace Fiber] [Nonempty Fiber]
    (W : WrinkledFibration I_M M I_B Base Fiber) :
    {W' : WrinkledFibration I_M M I_B Base Fiber //
      W'.toFun = W.toFun ∧
      W'.baseDiskRadius = W.baseDiskRadius / 2 ∧
      W'.baseRegion.1 ⊆ W.baseRegion.1 ∧
      closure (W'.baseRegion : Set Base) ⊆ W.baseRegion.1} := by
  let rHalf := W.baseDiskRadius / 2
  have hrHalf_pos : 0 < rHalf := half_pos W.baseDiskRadius_pos
  have hrHalf_lt : rHalf < W.baseDiskRadius := by
    dsimp only [rHalf]; linarith [W.baseDiskRadius_pos]
  let BHalfSet : Set Base :=
    {b : Base | ∃ h : b ∈ W.baseRegion.1, (W.baseDisk.symm ⟨b, h⟩ : EuclideanPlane) ∈
      Metric.ball (0 : EuclideanPlane) rHalf}
  have hBHalf_open : IsOpen BHalfSet := by
    let U_disk : Set W.baseDiskOpen :=
      {x : W.baseDiskOpen | (x : EuclideanPlane) ∈ Metric.ball (0 : EuclideanPlane) rHalf}
    have hU_disk_open : IsOpen U_disk := Metric.isOpen_ball.preimage continuous_subtype_val
    have hU_reg_open : IsOpen ((W.baseDisk.symm : W.baseRegion → W.baseDiskOpen) ⁻¹' U_disk) :=
      hU_disk_open.preimage W.baseDisk.symm.continuous
    have heq : BHalfSet =
        (Subtype.val : W.baseRegion → Base) ''
          ((W.baseDisk.symm : W.baseRegion → W.baseDiskOpen) ⁻¹' U_disk) := by
      ext b
      simp only [BHalfSet, U_disk, Set.mem_ofPred_eq, Set.mem_image, Set.mem_preimage,
        Subtype.exists]
      constructor
      · rintro ⟨h, hm⟩; exact ⟨b, h, hm, rfl⟩
      · rintro ⟨_, h, hm, rfl⟩; exact ⟨h, hm⟩
    rw [heq]
    exact W.baseRegion.2.isOpenMap_subtype_val _ hU_reg_open
  let BHalf : TopologicalSpace.Opens Base := ⟨BHalfSet, hBHalf_open⟩
  have hBHalf_sub : BHalf.1 ⊆ W.baseRegion.1 := fun _ h ↦ h.1
  have hBHalf_ne : BHalf.1.Nonempty := by
    refine ⟨(W.baseDisk ⟨0, Metric.mem_ball_self W.baseDiskRadius_pos⟩).1,
      (W.baseDisk ⟨0, Metric.mem_ball_self W.baseDiskRadius_pos⟩).2, ?_⟩
    have hsymm : W.baseDisk.symm ⟨(W.baseDisk ⟨0, Metric.mem_ball_self W.baseDiskRadius_pos⟩).1,
        (W.baseDisk ⟨0, Metric.mem_ball_self W.baseDiskRadius_pos⟩).2⟩ =
        ⟨0, Metric.mem_ball_self W.baseDiskRadius_pos⟩ :=
      W.baseDisk.symm_apply_apply _
    rw [hsymm]
    exact Metric.mem_ball_self hrHalf_pos
  let KH : Set Base :=
    Set.range (fun x : Metric.closedBall (0 : EuclideanPlane) rHalf ↦
      (W.baseDisk ⟨x.1, Metric.closedBall_subset_ball hrHalf_lt x.2⟩ : Base))
  have hKH_compact : IsCompact KH := by
    have : CompactSpace (Metric.closedBall (0 : EuclideanPlane) rHalf) :=
      isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : EuclideanPlane) rHalf)
    have hcont : Continuous (fun x : Metric.closedBall (0 : EuclideanPlane) rHalf ↦
        (W.baseDisk ⟨x.1, Metric.closedBall_subset_ball hrHalf_lt x.2⟩ : Base)) :=
      continuous_subtype_val.comp (W.baseDisk.continuous.comp
        (continuous_subtype_val.subtype_mk _))
    exact isCompact_range hcont
  have hBHalf_sub_KH : BHalf.1 ⊆ KH := by
    intro b ⟨hb_reg, hb_ball⟩
    refine ⟨⟨(W.baseDisk.symm ⟨b, hb_reg⟩).1, Metric.ball_subset_closedBall hb_ball⟩, ?_⟩
    have hsub : (⟨(W.baseDisk.symm ⟨b, hb_reg⟩).1,
        Metric.closedBall_subset_ball hrHalf_lt (Metric.ball_subset_closedBall hb_ball)⟩ :
          W.baseDiskOpen) = W.baseDisk.symm ⟨b, hb_reg⟩ :=
      Subtype.ext rfl
    dsimp only
    rw [hsub]
    exact congrArg Subtype.val (W.baseDisk.apply_symm_apply ⟨b, hb_reg⟩)
  have hKH_sub_reg : KH ⊆ W.baseRegion.1 := by
    rintro _ ⟨x, rfl⟩
    exact (W.baseDisk ⟨x.1, Metric.closedBall_subset_ball hrHalf_lt x.2⟩).2
  have hclosure_sub : closure (BHalf : Set Base) ⊆ W.baseRegion.1 :=
    (closure_minimal hBHalf_sub_KH hKH_compact.isClosed).trans hKH_sub_reg
  let diskHalfOpen : TopologicalSpace.Opens EuclideanPlane :=
    ⟨Metric.ball (0 : EuclideanPlane) rHalf, Metric.isOpen_ball⟩
  let diskHalfTo : diskHalfOpen → BHalf := fun x ↦
    ⟨(W.baseDisk ⟨x.1, Metric.ball_subset_ball hrHalf_lt.le x.2⟩).1,
      (W.baseDisk ⟨x.1, Metric.ball_subset_ball hrHalf_lt.le x.2⟩).2, by
        have hsub : (⟨(W.baseDisk ⟨x.1, Metric.ball_subset_ball hrHalf_lt.le x.2⟩).1,
            (W.baseDisk ⟨x.1, Metric.ball_subset_ball hrHalf_lt.le x.2⟩).2⟩ : W.baseRegion) =
            W.baseDisk ⟨x.1, Metric.ball_subset_ball hrHalf_lt.le x.2⟩ :=
          Subtype.ext rfl
        rw [hsub, W.baseDisk.symm_apply_apply]
        exact x.2⟩
  let diskHalfInv : BHalf → diskHalfOpen := fun b ↦
    ⟨(W.baseDisk.symm ⟨b.1, b.2.1⟩).1, b.2.2⟩
  let baseDiskHalf : diskHalfOpen ≃ₘ⟮𝓡 2, I_B⟯ BHalf :=
    { toFun := diskHalfTo
      invFun := diskHalfInv
      left_inv x := by
        apply Subtype.ext
        have hsub : (⟨(W.baseDisk ⟨x.1, Metric.ball_subset_ball hrHalf_lt.le x.2⟩).1,
            (W.baseDisk ⟨x.1, Metric.ball_subset_ball hrHalf_lt.le x.2⟩).2⟩ : W.baseRegion) =
            W.baseDisk ⟨x.1, Metric.ball_subset_ball hrHalf_lt.le x.2⟩ :=
          Subtype.ext rfl
        change (W.baseDisk.symm ⟨_, _⟩).1 = x.1
        rw [hsub, W.baseDisk.symm_apply_apply]
      right_inv b := by
        apply Subtype.ext
        have hsub : (⟨(W.baseDisk.symm ⟨b.1, b.2.1⟩).1,
            Metric.ball_subset_ball hrHalf_lt.le b.2.2⟩ : W.baseDiskOpen) =
            W.baseDisk.symm ⟨b.1, b.2.1⟩ :=
          Subtype.ext rfl
        change (W.baseDisk ⟨_, _⟩).1 = b.1
        rw [hsub, W.baseDisk.apply_symm_apply]
      contMDiff_toFun := by
        refine (TauCeti.ContMDiff.subtypeVal_comp_iff BHalf diskHalfTo).mp ?_
        have hincl : ContMDiff (𝓡 2) (𝓡 2) ∞
            (fun x : diskHalfOpen ↦
              (⟨x.1, Metric.ball_subset_ball hrHalf_lt.le x.2⟩ : W.baseDiskOpen)) :=
          (TauCeti.ContMDiff.subtypeVal_comp_iff W.baseDiskOpen _).mp contMDiff_subtype_val
        change ContMDiff (𝓡 2) I_B ∞
          (Subtype.val ∘ W.baseDisk ∘ fun x : diskHalfOpen ↦
            (⟨x.1, Metric.ball_subset_ball hrHalf_lt.le x.2⟩ : W.baseDiskOpen))
        exact contMDiff_subtype_val.comp (W.baseDisk.contMDiff.comp hincl)
      contMDiff_invFun := by
        refine (TauCeti.ContMDiff.subtypeVal_comp_iff diskHalfOpen diskHalfInv).mp ?_
        have hincl : ContMDiff I_B I_B ∞
            (fun b : BHalf ↦ (⟨b.1, b.2.1⟩ : W.baseRegion)) :=
          (TauCeti.ContMDiff.subtypeVal_comp_iff W.baseRegion _).mp contMDiff_subtype_val
        change ContMDiff I_B (𝓡 2) ∞
          (Subtype.val ∘ W.baseDisk.symm ∘ fun b : BHalf ↦
            (⟨b.1, b.2.1⟩ : W.baseRegion))
        exact contMDiff_subtype_val.comp (W.baseDisk.symm.contMDiff.comp hincl) }
  let preHalfOpen : TopologicalSpace.Opens M :=
    ⟨W.toFun ⁻¹' BHalf.1, BHalf.2.preimage W.contMDiff_toFun.continuous⟩
  let trivHalfTo : preHalfOpen → BHalf × Fiber := fun m ↦
    let q := W.trivialization ⟨m.1, hBHalf_sub m.2⟩
    ⟨⟨q.1.1, by
      have hfst := congrArg Subtype.val (W.trivialization_fst ⟨m.1, hBHalf_sub m.2⟩)
      dsimp only [q] at hfst ⊢
      rw [hfst]
      exact m.2⟩, q.2⟩
  let trivHalfInv : BHalf × Fiber → preHalfOpen := fun bz ↦
    ⟨(W.trivialization.symm (⟨bz.1.1, bz.1.2.1⟩, bz.2)).1, by
      have hfst := congrArg Subtype.val
        (W.trivialization_fst (W.trivialization.symm (⟨bz.1.1, bz.1.2.1⟩, bz.2)))
      rw [W.trivialization.apply_symm_apply] at hfst
      dsimp only at hfst
      change W.toFun (W.trivialization.symm (⟨bz.1.1, bz.1.2.1⟩, bz.2)).1 ∈ BHalf.1
      rw [← hfst]
      exact bz.1.2⟩
  let trivHalf : preHalfOpen ≃ₘ⟮I_M, I_B.prod (𝓡 2)⟯ (BHalf × Fiber) :=
    { toFun := trivHalfTo
      invFun := trivHalfInv
      left_inv m := by
        apply Subtype.ext
        dsimp only [trivHalfTo, trivHalfInv]
        have hsub : ((⟨(W.trivialization ⟨m.1, hBHalf_sub m.2⟩).1.1,
            (W.trivialization ⟨m.1, hBHalf_sub m.2⟩).1.2⟩ : W.baseRegion),
            (W.trivialization ⟨m.1, hBHalf_sub m.2⟩).2) =
            W.trivialization ⟨m.1, hBHalf_sub m.2⟩ := rfl
        rw [hsub, W.trivialization.symm_apply_apply]
      right_inv bz := by
        dsimp only [trivHalfTo, trivHalfInv]
        set u := W.trivialization.symm (⟨bz.1.1, bz.1.2.1⟩, bz.2)
        have hu : (⟨u.1, hBHalf_sub (trivHalfInv bz).2⟩ : W.preimageOpen) = u := Subtype.ext rfl
        apply Prod.ext
        · apply Subtype.ext
          dsimp only
          rw [hu, W.trivialization.apply_symm_apply]
        · dsimp only
          rw [hu, W.trivialization.apply_symm_apply]
      contMDiff_toFun := by
        have hm_incl : ContMDiff I_M I_M ∞
            (fun m : preHalfOpen ↦ (⟨m.1, hBHalf_sub m.2⟩ : W.preimageOpen)) :=
          (TauCeti.ContMDiff.subtypeVal_comp_iff W.preimageOpen _).mp contMDiff_subtype_val
        have hcomp := W.trivialization.contMDiff.comp hm_incl
        refine ContMDiff.prodMk ?_ ?_
        · refine (TauCeti.ContMDiff.subtypeVal_comp_iff BHalf (fun m ↦ (trivHalfTo m).1)).mp ?_
          change ContMDiff I_M I_B ∞
            (Subtype.val ∘ Prod.fst ∘ (⇑W.trivialization ∘ fun m : preHalfOpen ↦
              (⟨m.1, hBHalf_sub m.2⟩ : W.preimageOpen)))
          exact contMDiff_subtype_val.comp (contMDiff_fst.comp hcomp)
        · change ContMDiff I_M (𝓡 2) ∞
            (Prod.snd ∘ (⇑W.trivialization ∘ fun m : preHalfOpen ↦
              (⟨m.1, hBHalf_sub m.2⟩ : W.preimageOpen)))
          exact contMDiff_snd.comp hcomp
      contMDiff_invFun := by
        refine (TauCeti.ContMDiff.subtypeVal_comp_iff preHalfOpen trivHalfInv).mp ?_
        have hbincl : ContMDiff (I_B.prod (𝓡 2)) I_B ∞
            (fun bz : BHalf × Fiber ↦ (⟨bz.1.1, bz.1.2.1⟩ : W.baseRegion)) := by
          refine (TauCeti.ContMDiff.subtypeVal_comp_iff W.baseRegion _).mp ?_
          change ContMDiff (I_B.prod (𝓡 2)) I_B ∞
            (Subtype.val ∘ (Prod.fst : BHalf × Fiber → BHalf))
          exact contMDiff_subtype_val.comp contMDiff_fst
        change ContMDiff (I_B.prod (𝓡 2)) I_M ∞
          (Subtype.val ∘ W.trivialization.symm ∘ fun bz : BHalf × Fiber ↦
            ((⟨bz.1.1, bz.1.2.1⟩ : W.baseRegion), bz.2))
        exact contMDiff_subtype_val.comp
          (W.trivialization.symm.contMDiff.comp (hbincl.prodMk contMDiff_snd)) }
  refine ⟨
    { toFun := W.toFun
      contMDiff_toFun := W.contMDiff_toFun
      baseRegion := BHalf
      baseRegion_nonempty := hBHalf_ne
      regular_on_preimage := fun q hq ↦ W.regular_on_preimage q (hBHalf_sub hq)
      baseDiskRadius := rHalf
      baseDiskRadius_pos := hrHalf_pos
      baseDisk := baseDiskHalf
      trivialization := trivHalf
      trivialization_fst := fun m ↦ by
        apply Subtype.ext
        have h := congrArg Subtype.val (W.trivialization_fst ⟨m.1, hBHalf_sub m.2⟩)
        exact h },
    rfl, rfl, hBHalf_sub, hclosure_sub⟩

/-- **Lekili's Wrinkling Surgery (`Lekili 2009`, *Geom. Topol.* 13, §3.1 & §4 / Theorem 4)**:
every broken Lefschetz fibration `B : M → Base` on a compact Hausdorff 4-manifold `M` over a
Hausdorff surface `Base` admits a smooth global homotopy `H : ℝ → M → Base` (`H 0 = B.toFun`,
`H 1 = P.toFun`) supported inside a compact subset `K ⊆ M` (disjoint from
`B.toFun ⁻¹' closure P.baseRegion.1` and from all non-Lefschetz critical points of `B`) to a
`PurelyWrinkledFibration` `P : M → Base` with `P.baseDiskRadius = B.baseDiskRadius / 2` and
`P.baseRegion.1 ⊆ B.baseRegion.1`, replacing each isolated real Lefschetz singularity by a
3-cusped wrinkle (`Lekili 2009`, §3.1 Move 1) while leaving `B.toFun` stationary outside `K`. -/
-- tier: T2
theorem BrokenLefschetzFibration.exists_purelyWrinkledFibration
    {E_M H_M E_B H_B M Base Fiber : Type*}
    [NormedAddCommGroup E_M] [NormedSpace ℝ E_M] [TopologicalSpace H_M]
    {I_M : ModelWithCorners ℝ E_M H_M}
    [TopologicalSpace M] [ChartedSpace H_M M] [IsManifold I_M ∞ M] [CompactSpace M] [T2Space M]
    [NormedAddCommGroup E_B] [NormedSpace ℝ E_B] [TopologicalSpace H_B]
    {I_B : ModelWithCorners ℝ E_B H_B}
    [TopologicalSpace Base] [ChartedSpace H_B Base] [IsManifold I_B ∞ Base] [T2Space Base]
    [TopologicalSpace Fiber] [ChartedSpace EuclideanPlane Fiber]
    [IsManifold (𝓡 2) ∞ Fiber] [T2Space Fiber] [CompactSpace Fiber] [Nonempty Fiber]
    (B : BrokenLefschetzFibration I_M M I_B Base Fiber) :
    ∃ (P : PurelyWrinkledFibration I_M M I_B Base Fiber)
      (K : Set M) (H : ℝ → M → Base),
      P.baseDiskRadius = B.baseDiskRadius / 2 ∧
      P.baseRegion.1 ⊆ B.baseRegion.1 ∧
      IsCompact K ∧
      Disjoint K (B.toFun ⁻¹' closure (P.baseRegion : Set Base)) ∧
      (∀ p ∈ criticalPoints I_M I_B B.toFun,
        ¬ IsRealLefschetzAt I_M I_B B.toFun p → p ∉ K) ∧
      (∀ x ∉ K, P.toFun x = B.toFun x) ∧
      (∀ x ∈ P.toFun ⁻¹' P.baseRegion.1, P.toFun x = B.toFun x) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I_M) I_B ∞ (Function.uncurry H) ∧
      (∀ x, H 0 x = B.toFun x) ∧
      (∀ x, H 1 x = P.toFun x) ∧
      ∀ (t : ℝ), ∀ x ∉ K, H t x = B.toFun x := by
  obtain ⟨W_half, hto, hrad, hsub, hclos⟩ := B.toWrinkledFibration.shrinkBaseHalf
  let B_half : BrokenLefschetzFibration I_M M I_B Base Fiber :=
    { toWrinkledFibration := W_half
      singularities_broken_lefschetz := fun p hp ↦ by
        rw [hto] at hp ⊢
        exact B.singularities_broken_lefschetz p hp }
  have hdisj : ∀ p ∈ criticalPoints I_M I_B B_half.toFun,
      IsRealLefschetzAt I_M I_B B_half.toFun p →
        B_half.toFun p ∉ closure (B_half.baseRegion : Set Base) := by
    intro p hp _ hcl
    have hcl' : B.toFun p ∈ closure (W_half.baseRegion : Set Base) := by
      change W_half.toFun p ∈ closure (W_half.baseRegion : Set Base) at hcl
      rwa [hto] at hcl
    have hreg : B.toFun p ∈ B.baseRegion.1 := hclos hcl'
    have hsurj : Function.Surjective (mfderiv I_M I_B B.toFun p) :=
      B.regular_on_preimage p hreg
    change ¬ Function.Surjective (mfderiv I_M I_B B_half.toFun p) at hp
    rw [show B_half.toFun = B.toFun from hto] at hp
    exact hp hsurj
  obtain ⟨P, K, H, hP_reg, hP_rad, hK_comp, hK_disj, hK_crit, hP_out, hP_val,
      hH_md, hH_0, hH_1, hH_stat⟩ :=
    B_half.exists_purelyWrinkledFibration_of_disjoint_closure hdisj
  refine ⟨P, K, H, hP_rad.trans hrad, ?_, hK_comp, ?_, ?_, ?_, ?_, hH_md, ?_, hH_1, ?_⟩
  · simpa [hP_reg] using hsub
  · simpa [hP_reg, B_half, hto] using hK_disj
  · simpa [B_half, hto] using hK_crit
  · simpa [B_half, hto] using hP_out
  · simpa [B_half, hto] using hP_val
  · simpa [B_half, hto] using hH_0
  · simpa [B_half, hto] using hH_stat

end BrokenToWrinkled

end S4TuringPoisson


