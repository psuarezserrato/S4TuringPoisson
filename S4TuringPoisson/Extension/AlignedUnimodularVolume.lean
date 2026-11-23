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

public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import S4TuringPoisson.Fibration.WrinkledGeneral4Manifold
public import S4TuringPoisson.Poisson.JacobianPoisson
public import TauCeti.Geometry.Manifold.DifferentialForm.Opens
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

/-!
# Aligned Unimodular Volume Form & Adapted Jacobian–Poisson Structure (Milestone M4.1)

This module implements Milestone M4.1 of `S4TuringPoisson` (`S4TCdiffeo-Aug-2026.tex`, §3–4 &
Equation (1)):

Given any smooth `4`-manifold `M` admitting a positively co-oriented wrinkled (or broken Lefschetz)
fibration `[A : AdmitsWrinkledOrBrokenLefschetzFibration M]` `f : M → Sphere2` (with an
**unconditional instance** for `Sphere4` supplied by `S4Fibration.lean` /
`WrinkledGeneral4Manifold.lean`):

1. **Concentric Base Radii & Smooth Pushed Cutoffs (`rCore`, `rMid`, `rInner`, `rOuter`,
   `baseDiskBump`, `alignedCutoff`)**:
   - Chooses concentric Euclidean radii `0 < rCore < rMid < rInner < rOuter < r_B` inside
     `A.fibration.baseDiskOpen` (`r_B = A.fibration.baseDiskRadius`).
   - Pushes `ContDiffBump` along `A.fibration.baseDisk : ball 0 r_B ≃ₘ baseRegion` to construct
     smooth `[0, 1]`-valued cutoffs on `Sphere2` supported strictly inside `baseRegion`, including
     `alignedCutoff` (`χ : Sphere2 → ℝ`, `χ ≡ 1` on `baseDisk '' closedBall 0 rInner`,
     `tsupport χ ⊆ baseRegion`).

2. **Global Aligned Nowhere-Vanishing 4-Form (`alignedVolumeForm`, `alignedPositiveVolume`)**:
   - Defines `alignedVolumeForm : TauCeti.SmoothForm (𝓡 4) M ℝ 4` extending the convex combination
     `(1 - χ ∘ f) • Ω₀ + (χ ∘ f) • Φ^* (p_F^* ω_F ∧ p_B^* μ_B)` smoothly by `Ω₀` outside
     `f ⁻¹' baseRegion`.
   - Uses `A.trivialization_pos_cooriented` to prove `alignedVolumeForm` is strictly positively
     co-oriented with `A.ambientVolume.Ω` and vanishes nowhere (`alignedVolumeForm_ne_zero`), and
     packages `alignedPositiveVolume : PositiveVolumeForm (𝓡 4) M` on `[CompactSpace M]`.

3. **Adapted Unimodular Jacobian–Poisson Structure & Equation (1) (`adaptedJacobianPoisson`)**:
   - Constructs `adaptedJacobianPoisson M : PoissonStructure (𝓡 4) M` from `alignedPositiveVolume`
     and `S2VolumeForm` along `A.fibration`.
   - Proves global unimodularity (`IsUnimodularWithVolume` and `IsUnimodularPoisson`), generic
     rank `2` outside `criticalPoints`, rank `0` at every critical point of `f`, Casimir invariance
     of `u ∘ f`, and **Equation (1)**: on `f ⁻¹' (baseDisk '' ball 0 rInner)` (and on the closed
     inner preimage), `alignedVolumeForm` equals `Φ^* (p_F^* ω_F ∧ p_B^* μ_B)`.
-/

@[expose] public section

open Bundle Filter Function MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace S4TuringPoisson

/-! ## 1. Rank Zero of Jacobian–Poisson Structures at Surface Critical Points -/

section CriticalRankZero

/-- At every critical point `x ∈ criticalSet I_M I_N f` of a smooth map `f : M → N` from a
`4`-manifold `M` to a `2`-manifold `N`, the pullback `f^* μ_N` vanishes at `x`, so
`jacobianAnchor` vanishes and `jacobianPoisson` has rank `0`. -/
theorem rankAt_jacobianPoisson_of_mem_criticalSet
    {E_M H_M M : Type*} [NormedAddCommGroup E_M] [NormedSpace ℝ E_M]
    [TopologicalSpace H_M] {I_M : ModelWithCorners ℝ E_M H_M}
    [TopologicalSpace M] [ChartedSpace H_M M] [IsManifold I_M ∞ M]
    [hdim_M : HasFinrank E_M 4] [FiniteDimensional ℝ E_M]
    {E_N H_N N : Type*} [NormedAddCommGroup E_N] [NormedSpace ℝ E_N]
    [TopologicalSpace H_N] {I_N : ModelWithCorners ℝ E_N H_N}
    [TopologicalSpace N] [ChartedSpace H_N N] [IsManifold I_N ∞ N]
    [hdim_N : HasFinrank E_N 2] [FiniteDimensional ℝ E_N]
    (Ω : TauCeti.SmoothForm I_M M ℝ 4) (hΩ : ∀ z : M, Ω.1 z ≠ 0)
    (μ_N : TauCeti.SmoothForm I_N N ℝ 2) (f : M → N) (hf : ContMDiff I_M I_N ∞ f)
    {x : M} (hcrit : x ∈ criticalSet I_M I_N f) :
    (jacobianPoisson Ω hΩ μ_N f hf).rankAt x = 0 := by
  let bN : Module.Basis (Fin 2) ℝ (TangentSpace I_N (f x)) :=
    (trivializationAt E_N (TangentSpace I_N) (f x)).basisAt
      (Module.finBasisOfFinrankEq ℝ E_N hdim_N.finrank_eq)
      (FiberBundle.mem_baseSet_trivializationAt' (f x))
  let L := mfderiv I_M I_N f x
  have hdet_zero (w₀ w₁ : TangentSpace I_M x) :
      bN.repr (L w₀) 0 * bN.repr (L w₁) 1 - bN.repr (L w₀) 1 * bN.repr (L w₁) 0 = 0 := by
    by_contra hdet
    apply hcrit
    intro u
    let a₀ := bN.repr (L w₀) 0
    let a₁ := bN.repr (L w₀) 1
    let c₀ := bN.repr (L w₁) 0
    let c₁ := bN.repr (L w₁) 1
    let p₀ := bN.repr u 0
    let p₁ := bN.repr u 1
    let d := a₀ * c₁ - a₁ * c₀
    have hd : d ≠ 0 := hdet
    let t₀ := (c₁ * p₀ - c₀ * p₁) / d
    let t₁ := (-a₁ * p₀ + a₀ * p₁) / d
    refine ⟨t₀ • w₀ + t₁ • w₁, ?_⟩
    have hw₀ : L w₀ = a₀ • bN 0 + a₁ • bN 1 := by
      conv_lhs => rw [← bN.sum_repr (L w₀), Fin.sum_univ_two]
    have hw₁ : L w₁ = c₀ • bN 0 + c₁ • bN 1 := by
      conv_lhs => rw [← bN.sum_repr (L w₁), Fin.sum_univ_two]
    have hu : u = p₀ • bN 0 + p₁ • bN 1 := by
      conv_lhs => rw [← bN.sum_repr u, Fin.sum_univ_two]
    rw [map_add, map_smul, map_smul, hw₀, hw₁, hu, smul_add, smul_add, smul_smul, smul_smul,
      smul_smul, smul_smul]
    have hcoeff0 : t₀ * a₀ + t₁ * c₀ = p₀ := by
      dsimp only [t₀, t₁]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hd]
      dsimp only [d]
      ring
    have hcoeff1 : t₀ * a₁ + t₁ * c₁ = p₁ := by
      dsimp only [t₀, t₁]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hd]
      dsimp only [d]
      ring
    rw [← hcoeff0, ← hcoeff1, add_smul, add_smul]
    abel
  have hpul0 : (TauCeti.SmoothForm.mpullback f hf μ_N).1 x = 0 := by
    ext w
    rw [TauCeti.SmoothForm.mpullback_apply,
      ContinuousAlternatingMap.apply_eq_det_mul (μ_N.1 (f x)) bN (fun i ↦ L (w i))]
    have hdet_eq :
        bN.det (fun i ↦ L (w i)) =
          bN.repr (L (w 0)) 0 * bN.repr (L (w 1)) 1 -
            bN.repr (L (w 0)) 1 * bN.repr (L (w 1)) 0 := by
      rw [Module.Basis.det_apply, Matrix.det_fin_two]
      simp only [Module.Basis.toMatrix_apply]
      ring
    rw [hdet_eq, hdet_zero (w 0) (w 1), zero_mul]
    rfl
  have hanch0 : (jacobianPoisson Ω hΩ μ_N f hf).anchor x = 0 := by
    ext α : 1
    change jacobianAnchor Ω μ_N f hf x α = 0
    rw [jacobianAnchor_eq_subTopDualVector, hpul0,
      ContinuousAlternatingMap.pairedWedge_zero_right, neg_zero]
    simp [subTopDualVector]
  simp [SmoothBivector.rankAt, hanch0]

end CriticalRankZero

/-! ## 2. Concentric Base Radii, Subdisks & Pushed `ContDiffBump` Cutoffs -/

section ConcentricBaseCutoffs

variable (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [A : AdmitsWrinkledOrBrokenLefschetzFibration M]

/-- Base Euclidean disk radius `r_B > 0` of `A.fibration`. -/
noncomputable def baseRadius : ℝ :=
  letI := A.instTopologicalSpaceFiber
  letI := A.instChartedSpaceFiber
  letI := A.instIsManifoldFiber
  letI := A.instT2SpaceFiber
  letI := A.instCompactSpaceFiber
  letI := A.instNonemptyFiber
  A.fibration.baseDiskRadius

theorem baseRadius_pos : 0 < baseRadius M := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  exact A.fibration.baseDiskRadius_pos

/-- Core base radius `r_core = r_B / 4` on which the leafwise bump `ρ` equals `1`. -/
noncomputable def rCore : ℝ :=
  baseRadius M / 4

/-- Intermediate support radius `r_mid = 3 * r_B / 8` bounding `tsupport ρ` strictly inside
`ball 0 r_inner`. -/
noncomputable def rMid : ℝ :=
  3 * baseRadius M / 8

/-- Inner alignment radius `r_inner = r_B / 2` on which `χ ≡ 1` and Equation (1) holds. -/
noncomputable def rInner : ℝ :=
  baseRadius M / 2

/-- Outer alignment cutoff radius `r_outer = 3 * r_B / 4 < r_B` bounding `tsupport χ`. -/
noncomputable def rOuter : ℝ :=
  3 * baseRadius M / 4

theorem rCore_pos : 0 < rCore M := by
  have h := baseRadius_pos M
  unfold rCore
  linarith

theorem rCore_lt_rMid : rCore M < rMid M := by
  have h := baseRadius_pos M
  unfold rCore rMid
  linarith

theorem rMid_lt_rInner : rMid M < rInner M := by
  have h := baseRadius_pos M
  unfold rMid rInner
  linarith

theorem rCore_lt_rInner : rCore M < rInner M :=
  (rCore_lt_rMid M).trans (rMid_lt_rInner M)

theorem rInner_lt_rOuter : rInner M < rOuter M := by
  have h := baseRadius_pos M
  unfold rInner rOuter
  linarith

theorem rOuter_lt_baseRadius : rOuter M < baseRadius M := by
  have h := baseRadius_pos M
  unfold rOuter
  linarith

theorem rMid_pos : 0 < rMid M :=
  (rCore_pos M).trans (rCore_lt_rMid M)

theorem rInner_pos : 0 < rInner M :=
  (rCore_pos M).trans (rCore_lt_rInner M)

theorem rOuter_pos : 0 < rOuter M :=
  (rInner_pos M).trans (rInner_lt_rOuter M)

theorem rInner_lt_baseRadius : rInner M < baseRadius M :=
  (rInner_lt_rOuter M).trans (rOuter_lt_baseRadius M)

theorem rMid_lt_baseRadius : rMid M < baseRadius M :=
  (rMid_lt_rInner M).trans (rInner_lt_baseRadius M)

theorem rCore_lt_baseRadius : rCore M < baseRadius M :=
  (rCore_lt_rInner M).trans (rInner_lt_baseRadius M)

/-- Concentric open subdisk `{b ∈ baseRegion | ‖baseDisk⁻¹(b)‖ < r}` inside `Sphere2`. -/
noncomputable def baseOpenSubdisk (r : ℝ) : Opens Sphere2 := by
  letI := A.instTopologicalSpaceFiber
  letI := A.instChartedSpaceFiber
  letI := A.instIsManifoldFiber
  letI := A.instT2SpaceFiber
  letI := A.instCompactSpaceFiber
  letI := A.instNonemptyFiber
  let U_reg : Set A.fibration.baseRegion :=
    {u | (A.fibration.baseDisk.symm u).1 ∈ Metric.ball (0 : EuclideanPlane) r}
  have hU_open : IsOpen U_reg :=
    Metric.isOpen_ball.preimage
      (continuous_subtype_val.comp A.fibration.baseDisk.symm.continuous)
  exact ⟨Subtype.val '' U_reg, A.fibration.baseRegion.2.isOpenMap_subtype_val U_reg hU_open⟩

theorem mem_baseOpenSubdisk_iff (r : ℝ) (b : Sphere2) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    b ∈ (baseOpenSubdisk M r).1 ↔
      ∃ hb : b ∈ A.fibration.baseRegion.1,
        (A.fibration.baseDisk.symm ⟨b, hb⟩).1 ∈ Metric.ball (0 : EuclideanPlane) r := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  constructor
  · rintro ⟨⟨b', hb'⟩, hmem, rfl⟩
    exact ⟨hb', hmem⟩
  · rintro ⟨hb, hmem⟩
    exact ⟨⟨b, hb⟩, hmem, rfl⟩

theorem baseOpenSubdisk_subset_baseRegion (r : ℝ) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    (baseOpenSubdisk M r).1 ⊆ A.fibration.baseRegion.1 := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  intro b hb
  obtain ⟨hb_reg, -⟩ := (mem_baseOpenSubdisk_iff M r b).mp hb
  exact hb_reg

/-- `(baseOpenSubdisk M r).1` equals the direct image of `{w ∈ baseDiskOpen | w.1 ∈ ball 0 r}`
under `Subtype.val ∘ A.fibration.baseDisk`. -/
theorem baseOpenSubdisk_eq_image_ball {r : ℝ} (hr : r ≤ baseRadius M) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    (baseOpenSubdisk M r).1 =
      (Subtype.val ∘ ⇑A.fibration.baseDisk) ''
        {w : A.fibration.baseDiskOpen | w.1 ∈ Metric.ball (0 : EuclideanPlane) r} := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  ext b
  rw [mem_baseOpenSubdisk_iff]
  constructor
  · rintro ⟨hb, hmem⟩
    refine ⟨A.fibration.baseDisk.symm ⟨b, hb⟩, hmem, ?_⟩
    simp only [Function.comp_apply, A.fibration.baseDisk.apply_symm_apply]
  · rintro ⟨w, hw, rfl⟩
    have _ := hr
    dsimp only [Function.comp_apply]
    refine ⟨(A.fibration.baseDisk w).2, ?_⟩
    have heq : (⟨(A.fibration.baseDisk w).1, (A.fibration.baseDisk w).2⟩ :
        A.fibration.baseRegion) = A.fibration.baseDisk w := Subtype.ext rfl
    rw [heq, A.fibration.baseDisk.symm_apply_apply]
    exact hw

/-- Concentric compact closed subdisk `baseDisk '' closedBall 0 r` inside `Sphere2` for
`r < baseRadius M`. -/
noncomputable def baseClosedSubdisk (r : ℝ) (hr : r < baseRadius M) : Set Sphere2 :=
  letI := A.instTopologicalSpaceFiber
  letI := A.instChartedSpaceFiber
  letI := A.instIsManifoldFiber
  letI := A.instT2SpaceFiber
  letI := A.instCompactSpaceFiber
  letI := A.instNonemptyFiber
  (fun x : Metric.closedBall (0 : EuclideanPlane) r ↦
    (A.fibration.baseDisk ⟨x.1, Metric.closedBall_subset_ball hr x.2⟩).1) '' Set.univ

theorem isCompact_baseClosedSubdisk (r : ℝ) (hr : r < baseRadius M) :
    IsCompact (baseClosedSubdisk M r hr) := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let K := Metric.closedBall (0 : EuclideanPlane) r
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 r)
  have hcont_incl : Continuous (fun x : K ↦
      (⟨x.1, Metric.closedBall_subset_ball hr x.2⟩ : A.fibration.baseDiskOpen)) :=
    continuous_subtype_val.subtype_mk _
  exact isCompact_univ.image
    (continuous_subtype_val.comp (A.fibration.baseDisk.continuous.comp hcont_incl))

theorem isClosed_baseClosedSubdisk (r : ℝ) (hr : r < baseRadius M) :
    IsClosed (baseClosedSubdisk M r hr) :=
  (isCompact_baseClosedSubdisk M r hr).isClosed

theorem mem_baseClosedSubdisk_iff (r : ℝ) (hr : r < baseRadius M) (b : Sphere2) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    b ∈ baseClosedSubdisk M r hr ↔
      ∃ hb : b ∈ A.fibration.baseRegion.1,
        (A.fibration.baseDisk.symm ⟨b, hb⟩).1 ∈ Metric.closedBall (0 : EuclideanPlane) r := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  constructor
  · rintro ⟨x, -, rfl⟩
    let w : A.fibration.baseDiskOpen := ⟨x.1, Metric.closedBall_subset_ball hr x.2⟩
    refine ⟨(A.fibration.baseDisk w).2, ?_⟩
    have heq : (⟨(A.fibration.baseDisk w).1, (A.fibration.baseDisk w).2⟩ :
        A.fibration.baseRegion) = A.fibration.baseDisk w := rfl
    rw [heq, A.fibration.baseDisk.symm_apply_apply]
    exact x.2
  · rintro ⟨hb, hmem⟩
    let w := A.fibration.baseDisk.symm ⟨b, hb⟩
    refine ⟨⟨w.1, hmem⟩, Set.mem_univ _, ?_⟩
    have hw : (⟨w.1, Metric.closedBall_subset_ball hr hmem⟩ : A.fibration.baseDiskOpen) = w :=
      Subtype.ext rfl
    change (A.fibration.baseDisk ⟨w.1, Metric.closedBall_subset_ball hr hmem⟩).1 = b
    rw [hw, A.fibration.baseDisk.apply_symm_apply]

theorem baseClosedSubdisk_subset_baseRegion (r : ℝ) (hr : r < baseRadius M) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    baseClosedSubdisk M r hr ⊆ A.fibration.baseRegion.1 := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  intro b hb
  exact ((mem_baseClosedSubdisk_iff M r hr b).mp hb).1

theorem baseOpenSubdisk_subset_baseClosedSubdisk (r : ℝ) (hr : r < baseRadius M) :
    (baseOpenSubdisk M r).1 ⊆ baseClosedSubdisk M r hr := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  intro b hb
  obtain ⟨hb_reg, hball⟩ := (mem_baseOpenSubdisk_iff M r b).mp hb
  exact (mem_baseClosedSubdisk_iff M r hr b).mpr ⟨hb_reg, Metric.ball_subset_closedBall hball⟩

theorem baseClosedSubdisk_subset_baseOpenSubdisk {r₁ r₂ : ℝ} (hr₁ : r₁ < baseRadius M)
    (hr₁₂ : r₁ < r₂) :
    baseClosedSubdisk M r₁ hr₁ ⊆ (baseOpenSubdisk M r₂).1 := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  intro b hb
  obtain ⟨hb_reg, hclosed⟩ := (mem_baseClosedSubdisk_iff M r₁ hr₁ b).mp hb
  exact (mem_baseOpenSubdisk_iff M r₂ b).mpr
    ⟨hb_reg, Metric.closedBall_subset_ball hr₁₂ hclosed⟩

/-- Core open base disk `B₀ = baseDisk '' ball 0 rCore` inside `Sphere2`. -/
noncomputable def baseCoreOpen : Opens Sphere2 :=
  baseOpenSubdisk M (rCore M)

/-- Inner open base disk `baseDisk '' ball 0 rInner` inside `Sphere2` on which `χ ≡ 1`. -/
noncomputable def baseInnerOpen : Opens Sphere2 :=
  baseOpenSubdisk M (rInner M)

theorem baseCenter_mem_baseCoreOpen :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    (A.fibration.baseCenter : Sphere2) ∈ (baseCoreOpen M).1 := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  rw [baseCoreOpen, mem_baseOpenSubdisk_iff]
  refine ⟨A.fibration.baseCenter.2, ?_⟩
  have heq : (⟨(A.fibration.baseCenter : Sphere2), A.fibration.baseCenter.2⟩ :
      A.fibration.baseRegion) = A.fibration.baseCenter := rfl
  rw [heq]
  unfold WrinkledFibration.baseCenter
  rw [A.fibration.baseDisk.symm_apply_apply]
  exact Metric.mem_ball_self (rCore_pos M)

theorem baseCoreOpen_nonempty : (baseCoreOpen M).1.Nonempty := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  exact ⟨A.fibration.baseCenter.1, baseCenter_mem_baseCoreOpen M⟩

/-- Smooth radial `ContDiffBump` on `EuclideanPlane` pushed forward along `A.fibration.baseDisk`
and extended by `0` outside `A.fibration.baseRegion` for `0 < r₁ < r₂ < baseRadius M`. -/
noncomputable def baseDiskBump {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) (b : Sphere2) : ℝ :=
  letI := A.instTopologicalSpaceFiber
  letI := A.instChartedSpaceFiber
  letI := A.instIsManifoldFiber
  letI := A.instT2SpaceFiber
  letI := A.instCompactSpaceFiber
  letI := A.instNonemptyFiber
  let B_plane : ContDiffBump (0 : EuclideanPlane) :=
    { rIn := r₁
      rOut := r₂
      rIn_pos := hr₁
      rIn_lt_rOut := hr₁₂ }
  letI := Classical.dec (b ∈ A.fibration.baseRegion.1)
  if hb : b ∈ A.fibration.baseRegion.1 then
    B_plane (A.fibration.baseDisk.symm ⟨b, hb⟩).1
  else
    0

theorem baseDiskBump_of_mem {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) {b : Sphere2}
    (hb :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      b ∈ A.fibration.baseRegion.1) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    baseDiskBump M hr₁ hr₁₂ b =
      ({ rIn := r₁, rOut := r₂, rIn_pos := hr₁, rIn_lt_rOut := hr₁₂ } :
          ContDiffBump (0 : EuclideanPlane))
        (A.fibration.baseDisk.symm ⟨b, hb⟩).1 := by
  simp only [baseDiskBump]
  exact dite_eq_left hb

theorem baseDiskBump_of_notMem {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) {b : Sphere2}
    (hb :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      b ∉ A.fibration.baseRegion.1) :
    baseDiskBump M hr₁ hr₁₂ b = 0 := by
  simp only [baseDiskBump]
  exact dite_eq_right hb

theorem baseDiskBump_nonneg {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) (b : Sphere2) :
    0 ≤ baseDiskBump M hr₁ hr₁₂ b := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  by_cases hb : b ∈ A.fibration.baseRegion.1
  · rw [baseDiskBump_of_mem M hr₁ hr₁₂ hb]
    exact ContDiffBump.nonneg _
  · rw [baseDiskBump_of_notMem M hr₁ hr₁₂ hb]

theorem baseDiskBump_le_one {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) (b : Sphere2) :
    baseDiskBump M hr₁ hr₁₂ b ≤ 1 := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  by_cases hb : b ∈ A.fibration.baseRegion.1
  · rw [baseDiskBump_of_mem M hr₁ hr₁₂ hb]
    exact ContDiffBump.le_one _
  · rw [baseDiskBump_of_notMem M hr₁ hr₁₂ hb]
    exact zero_le_one

theorem baseDiskBump_eq_one_of_mem_closedSubdisk {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂)
    (hr₂ : r₂ < baseRadius M) {b : Sphere2}
    (hb : b ∈ baseClosedSubdisk M r₁ (hr₁₂.trans hr₂)) :
    baseDiskBump M hr₁ hr₁₂ b = 1 := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  obtain ⟨hb_reg, hclosed⟩ := (mem_baseClosedSubdisk_iff M r₁ (hr₁₂.trans hr₂) b).mp hb
  rw [baseDiskBump_of_mem M hr₁ hr₁₂ hb_reg]
  exact ContDiffBump.one_of_mem_closedBall _ hclosed

theorem baseDiskBump_eq_one_of_mem_openSubdisk {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂)
    (hr₂ : r₂ < baseRadius M) {b : Sphere2} (hb : b ∈ (baseOpenSubdisk M r₁).1) :
    baseDiskBump M hr₁ hr₁₂ b = 1 :=
  baseDiskBump_eq_one_of_mem_closedSubdisk M hr₁ hr₁₂ hr₂
    (baseOpenSubdisk_subset_baseClosedSubdisk M r₁ (hr₁₂.trans hr₂) hb)

theorem baseDiskBump_eq_zero_of_notMem_closedSubdisk {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂)
    (hr₂ : r₂ < baseRadius M) {b : Sphere2} (hb : b ∉ baseClosedSubdisk M r₂ hr₂) :
    baseDiskBump M hr₁ hr₁₂ b = 0 := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  by_cases hb_reg : b ∈ A.fibration.baseRegion.1
  · rw [baseDiskBump_of_mem M hr₁ hr₁₂ hb_reg]
    let B_plane : ContDiffBump (0 : EuclideanPlane) :=
      { rIn := r₁, rOut := r₂, rIn_pos := hr₁, rIn_lt_rOut := hr₁₂ }
    have hnot_closed :
        (A.fibration.baseDisk.symm ⟨b, hb_reg⟩).1 ∉ Metric.closedBall (0 : EuclideanPlane) r₂ :=
      fun hmem ↦ hb ((mem_baseClosedSubdisk_iff M r₂ hr₂ b).mpr ⟨hb_reg, hmem⟩)
    have hnot_ball :
        (A.fibration.baseDisk.symm ⟨b, hb_reg⟩).1 ∉ Function.support ⇑B_plane := by
      rw [B_plane.support_eq]
      exact fun hball ↦ hnot_closed (Metric.ball_subset_closedBall hball)
    exact Function.notMem_support.mp hnot_ball
  · exact baseDiskBump_of_notMem M hr₁ hr₁₂ hb_reg

theorem tsupport_baseDiskBump_subset {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂)
    (hr₂ : r₂ < baseRadius M) :
    tsupport (baseDiskBump M hr₁ hr₁₂) ⊆ baseClosedSubdisk M r₂ hr₂ := by
  refine closure_minimal ?_ (isClosed_baseClosedSubdisk M r₂ hr₂)
  intro b hb
  by_contra hnot
  exact hb (baseDiskBump_eq_zero_of_notMem_closedSubdisk M hr₁ hr₁₂ hr₂ hnot)

/-- Global $C^\infty$ smoothness of `baseDiskBump` on `Sphere2` whenever `r₂ < baseRadius M`. -/
theorem contMDiff_baseDiskBump {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂)
    (hr₂ : r₂ < baseRadius M) :
    ContMDiff (𝓡 2) 𝓘(ℝ) ∞ (baseDiskBump M hr₁ hr₁₂) := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let B_plane : ContDiffBump (0 : EuclideanPlane) :=
    { rIn := r₁, rOut := r₂, rIn_pos := hr₁, rIn_lt_rOut := hr₁₂ }
  let g : A.fibration.baseRegion → ℝ := fun u ↦ B_plane (A.fibration.baseDisk.symm u).1
  have hg : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ g :=
    (B_plane.contDiff (n := ⊤)).contMDiff.comp
      (contMDiff_subtype_val.comp A.fibration.baseDisk.symm.contMDiff)
  have hcomp : baseDiskBump M hr₁ hr₁₂ ∘ (Subtype.val : A.fibration.baseRegion → Sphere2) = g :=
    funext fun u ↦ baseDiskBump_of_mem M hr₁ hr₁₂ u.2
  intro b₀
  by_cases hb₀ : b₀ ∈ A.fibration.baseRegion.1
  · refine ((TauCeti.isLocalDiffeomorph_subtype_val (I := 𝓡 2) (n := ∞)
        (⟨b₀, hb₀⟩ : A.fibration.baseRegion)).contMDiffAt_comp_iff le_rfl).mp ?_
    rw [hcomp]
    exact hg ⟨b₀, hb₀⟩
  · have hb₀_not : b₀ ∉ baseClosedSubdisk M r₂ hr₂ :=
      fun hmem ↦ hb₀ (baseClosedSubdisk_subset_baseRegion M r₂ hr₂ hmem)
    refine (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_baseClosedSubdisk M r₂ hr₂).isOpen_compl.mem_nhds hb₀_not]
      with b hb
    exact baseDiskBump_eq_zero_of_notMem_closedSubdisk M hr₁ hr₁₂ hr₂ hb

/-- Smooth alignment cutoff `χ : Sphere2 → ℝ` (`0 ≤ χ ≤ 1`, `χ ≡ 1` on
`baseClosedSubdisk M (rInner M)`, `tsupport χ ⊆ A.fibration.baseRegion.1`). -/
noncomputable def alignedCutoff : Sphere2 → ℝ :=
  baseDiskBump M (rInner_pos M) (rInner_lt_rOuter M)

theorem contMDiff_alignedCutoff : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ (alignedCutoff M) :=
  contMDiff_baseDiskBump M (rInner_pos M) (rInner_lt_rOuter M) (rOuter_lt_baseRadius M)

theorem alignedCutoff_nonneg (b : Sphere2) : 0 ≤ alignedCutoff M b :=
  baseDiskBump_nonneg M (rInner_pos M) (rInner_lt_rOuter M) b

theorem alignedCutoff_le_one (b : Sphere2) : alignedCutoff M b ≤ 1 :=
  baseDiskBump_le_one M (rInner_pos M) (rInner_lt_rOuter M) b

theorem alignedCutoff_eq_one_of_mem_closedInner {b : Sphere2}
    (hb : b ∈ baseClosedSubdisk M (rInner M) (rInner_lt_baseRadius M)) :
    alignedCutoff M b = 1 :=
  baseDiskBump_eq_one_of_mem_closedSubdisk M (rInner_pos M) (rInner_lt_rOuter M)
    (rOuter_lt_baseRadius M) hb

theorem alignedCutoff_eq_one_of_mem_baseInnerOpen {b : Sphere2} (hb : b ∈ (baseInnerOpen M).1) :
    alignedCutoff M b = 1 :=
  baseDiskBump_eq_one_of_mem_openSubdisk M (rInner_pos M) (rInner_lt_rOuter M)
    (rOuter_lt_baseRadius M) hb

theorem tsupport_alignedCutoff_subset_baseRegion :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    tsupport (alignedCutoff M) ⊆ A.fibration.baseRegion.1 := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  exact (tsupport_baseDiskBump_subset M (rInner_pos M) (rInner_lt_rOuter M)
    (rOuter_lt_baseRadius M)).trans
    (baseClosedSubdisk_subset_baseRegion M (rOuter M) (rOuter_lt_baseRadius M))

end ConcentricBaseCutoffs

/-! ## 3. Global Aligned Volume 4-Form & Equation (1) -/

section AlignedVolume

variable (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [A : AdmitsWrinkledOrBrokenLefschetzFibration M]

/-- Lift a rough 4-form on an open subset `U : Opens M` to a rough 4-form on `M` by `0` outside
`U`, aligning the fiber codomain `Bundle.Trivial M ℝ x`. -/
noncomputable def liftOpenRoughForm {U : Opens M} (η : TauCeti.RoughForm (𝓡 4) U ℝ 4) :
    TauCeti.RoughForm (𝓡 4) M ℝ 4 :=
  letI := Classical.decPred (· ∈ U.1)
  fun x ↦
    if hx : x ∈ U.1 then
      show TangentSpace (𝓡 4) x [⋀^Fin 4]→L[ℝ] Bundle.Trivial M ℝ x from η ⟨x, hx⟩
    else
      0

omit [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] A in
theorem liftOpenRoughForm_of_mem {U : Opens M} (η : TauCeti.RoughForm (𝓡 4) U ℝ 4) {x : M}
    (hx : x ∈ U.1) :
    liftOpenRoughForm M η x =
      show TangentSpace (𝓡 4) x [⋀^Fin 4]→L[ℝ] Bundle.Trivial M ℝ x from η ⟨x, hx⟩ := by
  simp only [liftOpenRoughForm]
  exact dite_eq_left hx

omit [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] A in
theorem liftOpenRoughForm_apply_of_mem {U : Opens M} (η : TauCeti.RoughForm (𝓡 4) U ℝ 4) {x : M}
    (hx : x ∈ U.1) (v : Fin 4 → TangentSpace (𝓡 4) x) :
    (show ℝ from liftOpenRoughForm M η x v) = (show ℝ from η ⟨x, hx⟩ v) :=
  DFunLike.congr_fun (liftOpenRoughForm_of_mem M η hx) v

/-- Product smooth 4-form `p_F^* ω_F ∧ p_B^* μ_B` on `A.fibration.baseRegion × A.Fiber`. -/
noncomputable def productTargetForm :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    TauCeti.SmoothForm ((𝓡 2).prod (𝓡 2)) (A.fibration.baseRegion × A.Fiber) ℝ 4 := by
  letI := A.instTopologicalSpaceFiber
  letI := A.instChartedSpaceFiber
  letI := A.instIsManifoldFiber
  letI := A.instT2SpaceFiber
  letI := A.instCompactSpaceFiber
  letI := A.instNonemptyFiber
  letI := A.instMeasurableSpaceFiber
  letI := A.instBorelSpaceFiber
  exact TauCeti.SmoothForm.wedge
    (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd A.fiberVolume.Ω)
    (TauCeti.SmoothForm.mpullback (Subtype.val ∘ Prod.fst)
      (contMDiff_subtype_val.comp contMDiff_fst) S2VolumeForm)

/-- Local product 4-form `Φ^* (p_F^* ω_F ∧ p_B^* μ_B)` on `A.fibration.preimageOpen`. -/
noncomputable def trivializedProductForm :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    TauCeti.SmoothForm (𝓡 4) A.fibration.preimageOpen ℝ 4 := by
  letI := A.instTopologicalSpaceFiber
  letI := A.instChartedSpaceFiber
  letI := A.instIsManifoldFiber
  letI := A.instT2SpaceFiber
  letI := A.instCompactSpaceFiber
  letI := A.instNonemptyFiber
  exact TauCeti.SmoothForm.mpullback A.fibration.trivialization
    A.fibration.trivialization.contMDiff (productTargetForm M)

/-- Underlying rough 4-form of `(1 - χ ∘ f) • Ω₀ + (χ ∘ f) • Φ^* (p_F^* ω_F ∧ p_B^* μ_B)`
extended by `Ω₀` outside `A.fibration.preimageOpen`. -/
noncomputable def alignedRoughForm : TauCeti.RoughForm (𝓡 4) M ℝ 4 := by
  letI := A.instTopologicalSpaceFiber
  letI := A.instChartedSpaceFiber
  letI := A.instIsManifoldFiber
  letI := A.instT2SpaceFiber
  letI := A.instCompactSpaceFiber
  letI := A.instNonemptyFiber
  exact fun x ↦
    (1 - alignedCutoff M (A.fibration x)) • A.ambientVolume.Ω.1 x +
      alignedCutoff M (A.fibration x) • liftOpenRoughForm M (trivializedProductForm M).1 x

theorem alignedRoughForm_of_mem {x : M}
    (hx :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      x ∈ A.fibration.preimageOpen.1) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    alignedRoughForm M x =
      (1 - alignedCutoff M (A.fibration x)) • A.ambientVolume.Ω.1 x +
        alignedCutoff M (A.fibration x) •
          (show TangentSpace (𝓡 4) x [⋀^Fin 4]→L[ℝ] Bundle.Trivial M ℝ x from
            (trivializedProductForm M).1 ⟨x, hx⟩) := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  change (1 - alignedCutoff M (A.fibration x)) • A.ambientVolume.Ω.1 x +
      alignedCutoff M (A.fibration x) • liftOpenRoughForm M (trivializedProductForm M).1 x = _
  rw [liftOpenRoughForm_of_mem M (trivializedProductForm M).1 hx]

theorem alignedRoughForm_apply_of_mem {x : M}
    (hx :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      x ∈ A.fibration.preimageOpen.1)
    (v : Fin 4 → TangentSpace (𝓡 4) x) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    (show ℝ from alignedRoughForm M x v) =
      (1 - alignedCutoff M (A.fibration x)) * (show ℝ from A.ambientVolume.Ω.1 x v) +
        alignedCutoff M (A.fibration x) *
          (show ℝ from (trivializedProductForm M).1 ⟨x, hx⟩ v) := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  have h := DFunLike.congr_fun (alignedRoughForm_of_mem M hx) v
  exact h.trans (by
    simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply]
    rfl)

theorem alignedRoughForm_of_alignedCutoff_eq_zero {x : M}
    (hχ :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      alignedCutoff M (A.fibration x) = 0) :
    alignedRoughForm M x = A.ambientVolume.Ω.1 x := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  change (1 - alignedCutoff M (A.fibration x)) • A.ambientVolume.Ω.1 x +
      alignedCutoff M (A.fibration x) • liftOpenRoughForm M (trivializedProductForm M).1 x =
    A.ambientVolume.Ω.1 x
  rw [hχ, sub_zero, one_smul, zero_smul, add_zero]

theorem alignedRoughForm_of_notMem {x : M}
    (hx :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      x ∉ A.fibration.preimageOpen.1) :
    alignedRoughForm M x = A.ambientVolume.Ω.1 x := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  have hnot_tsupp : A.fibration x ∉ tsupport (alignedCutoff M) :=
    fun hmem ↦ hx (tsupport_alignedCutoff_subset_baseRegion M hmem)
  exact alignedRoughForm_of_alignedCutoff_eq_zero M (image_eq_zero_of_notMem_tsupport hnot_tsupp)

/-- Global $C^\infty$ smoothness of `alignedRoughForm M` on `M`. -/
theorem isSmoothForm_alignedRoughForm :
    TauCeti.IsSmoothForm (𝓡 4) ∞ (alignedRoughForm M) := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  rw [TauCeti.isSmoothForm_def]
  intro x
  by_cases hx : x ∈ A.fibration.preimageOpen.1
  · let u₀ : A.fibration.preimageOpen := ⟨x, hx⟩
    have hχ_u : ContMDiff (𝓡 4) 𝓘(ℝ) ∞
        (fun u : A.fibration.preimageOpen ↦ alignedCutoff M (A.fibration u.1)) :=
      (contMDiff_alignedCutoff M).comp (A.fibration.contMDiff_toFun.comp contMDiff_subtype_val)
    have h1_u : ContMDiff (𝓡 4) 𝓘(ℝ) ∞
        (fun u : A.fibration.preimageOpen ↦ 1 - alignedCutoff M (A.fibration u.1)) :=
      contMDiff_const.sub hχ_u
    let Ω_sub := TauCeti.SmoothForm.mpullback
      (Subtype.val : A.fibration.preimageOpen → M) contMDiff_subtype_val A.ambientVolume.Ω
    have hloc_smooth : TauCeti.IsSmoothForm (𝓡 4) ∞
        (TauCeti.mpullback (𝓡 4) (𝓡 4) (Subtype.val : A.fibration.preimageOpen → M)
          (alignedRoughForm M)) := by
      have heq : TauCeti.mpullback (𝓡 4) (𝓡 4) (Subtype.val : A.fibration.preimageOpen → M)
          (alignedRoughForm M) =
          (fun u ↦ (1 - alignedCutoff M (A.fibration u.1)) • Ω_sub.1 u) +
            (fun u ↦ alignedCutoff M (A.fibration u.1) • (trivializedProductForm M).1 u) := by
        funext u
        ext v
        have hsub :
            (show ℝ from TauCeti.mpullback (𝓡 4) (𝓡 4)
              (Subtype.val : A.fibration.preimageOpen → M) (alignedRoughForm M) u v) =
            (show ℝ from alignedRoughForm M u.1 v) :=
          DFunLike.congr_fun (TauCeti.mpullback_subtype_val_apply (alignedRoughForm M) u) v
        have hmem := alignedRoughForm_apply_of_mem M u.2 v
        have hΩ : (show ℝ from Ω_sub.1 u v) = (show ℝ from A.ambientVolume.Ω.1 u.1 v) :=
          DFunLike.congr_fun
            (TauCeti.SmoothForm.coe_mpullback_subtype_val_apply A.ambientVolume.Ω u) v
        change (show ℝ from TauCeti.mpullback (𝓡 4) (𝓡 4)
            (Subtype.val : A.fibration.preimageOpen → M) (alignedRoughForm M) u v) =
          (1 - alignedCutoff M (A.fibration u.1)) * (show ℝ from Ω_sub.1 u v) +
            alignedCutoff M (A.fibration u.1) *
              (show ℝ from (trivializedProductForm M).1 u v)
        rw [hsub, hmem, hΩ]
      rw [heq]
      exact (Ω_sub.isSmoothForm.fun_smul h1_u).add
        ((trivializedProductForm M).isSmoothForm.fun_smul hχ_u)
    exact ((TauCeti.isLocalDiffeomorph_subtype_val (I := 𝓡 4) (n := ∞)
      u₀).contMDiffAt_mpullback_form_iff (by simp)).mp (hloc_smooth.contMDiff u₀)
  · let K : Set M := A.fibration ⁻¹' tsupport (alignedCutoff M)
    have hK_closed : IsClosed K :=
      (isClosed_tsupport (alignedCutoff M)).preimage A.fibration.contMDiff_toFun.continuous
    have hK_sub : K ⊆ A.fibration.preimageOpen.1 := fun y hy ↦
      tsupport_alignedCutoff_subset_baseRegion M hy
    have hx_notK : x ∉ K := fun hy ↦ hx (hK_sub hy)
    refine (A.ambientVolume.Ω.contMDiff x).congr_of_eventuallyEq ?_
    filter_upwards [hK_closed.isOpen_compl.mem_nhds hx_notK] with y hy
    have hχ0 : alignedCutoff M (A.fibration y) = 0 :=
      image_eq_zero_of_notMem_tsupport hy
    rw [alignedRoughForm_of_alignedCutoff_eq_zero M hχ0]

/-- **Global Aligned Smooth Volume 4-Form (`S4TCdiffeo-Aug-2026.tex`, §3–4)**:
Smooth 4-form `Ω` on `M` equal to `(1 - χ ∘ f) • Ω₀ + (χ ∘ f) • Φ^* (p_F^* ω_F ∧ p_B^* μ_B)` on
`f ⁻¹' baseRegion` and `Ω₀` outside `f ⁻¹' baseRegion`. -/
noncomputable def alignedVolumeForm : TauCeti.SmoothForm (𝓡 4) M ℝ 4 :=
  ⟨alignedRoughForm M, (isSmoothForm_alignedRoughForm M).mem_smoothBundleForms⟩

@[simp]
theorem coe_alignedVolumeForm : (alignedVolumeForm M).1 = alignedRoughForm M :=
  rfl

/-- Strict positive co-orientation of `alignedVolumeForm M` with `A.ambientVolume.Ω` at every
point `x : M`. -/
theorem alignedVolumeForm_pos_cooriented (x : M) :
    ∃ a : ℝ, 0 < a ∧ (alignedVolumeForm M).1 x = a • A.ambientVolume.Ω.1 x := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := A.instMeasurableSpaceFiber
  let _ := A.instBorelSpaceFiber
  by_cases hx : x ∈ A.fibration.preimageOpen.1
  · obtain ⟨c, hc_pos, hc_eq⟩ := A.trivialization_pos_cooriented ⟨x, hx⟩
    let χx := alignedCutoff M (A.fibration x)
    have hχ0 : 0 ≤ χx := alignedCutoff_nonneg M (A.fibration x)
    have hχ1 : χx ≤ 1 := alignedCutoff_le_one M (A.fibration x)
    have hpos : 0 < (1 - χx) + χx * c := by
      by_cases h0 : χx = 0
      · rw [h0]; linarith
      · have hχ_pos : 0 < χx := lt_of_le_of_ne' hχ0 h0
        have hmul : 0 < χx * c := mul_pos hχ_pos hc_pos
        linarith
    refine ⟨(1 - χx) + χx * c, hpos, ?_⟩
    ext v
    have hmem := alignedRoughForm_apply_of_mem M hx v
    have hc_v :
        (show ℝ from (trivializedProductForm M).1 ⟨x, hx⟩ v) =
          c * (show ℝ from A.ambientVolume.Ω.1 x v) := by
      have hv :
          (show ℝ from (trivializedProductForm M).1 ⟨x, hx⟩ v) =
            c * (show ℝ from (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val
              A.ambientVolume.Ω).1 ⟨x, hx⟩ v) :=
        DFunLike.congr_fun hc_eq v
      have hsub :
          (show ℝ from (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val
            A.ambientVolume.Ω).1 ⟨x, hx⟩ v) =
            (show ℝ from A.ambientVolume.Ω.1 x v) :=
        DFunLike.congr_fun
          (TauCeti.SmoothForm.coe_mpullback_subtype_val_apply A.ambientVolume.Ω ⟨x, hx⟩) v
      rw [hv, hsub]
    change (show ℝ from alignedRoughForm M x v) =
      ((1 - χx) + χx * c) * (show ℝ from A.ambientVolume.Ω.1 x v)
    rw [hmem, hc_v]
    ring
  · exact ⟨1, one_pos, by rw [coe_alignedVolumeForm, alignedRoughForm_of_notMem M hx, one_smul]⟩

/-- `alignedVolumeForm M` vanishes nowhere on `M`. -/
theorem alignedVolumeForm_ne_zero (x : M) : (alignedVolumeForm M).1 x ≠ 0 := by
  obtain ⟨a, ha_pos, ha_eq⟩ := alignedVolumeForm_pos_cooriented M x
  rw [ha_eq]
  exact smul_ne_zero ha_pos.ne' (A.ambientVolume.Ω_ne_zero x)

/-- Open preimage `f ⁻¹' (baseInnerOpen M)` inside `M` on which **Equation (1)** holds. -/
noncomputable def innerPreimageOpen : Opens M := by
  letI := A.instTopologicalSpaceFiber
  letI := A.instChartedSpaceFiber
  letI := A.instIsManifoldFiber
  letI := A.instT2SpaceFiber
  letI := A.instCompactSpaceFiber
  letI := A.instNonemptyFiber
  exact ⟨A.fibration ⁻¹' (baseInnerOpen M).1,
    (baseInnerOpen M).2.preimage A.fibration.contMDiff_toFun.continuous⟩

theorem innerPreimageOpen_le_preimageOpen :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    innerPreimageOpen M ≤ A.fibration.preimageOpen := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  intro x hx
  exact baseOpenSubdisk_subset_baseRegion M (rInner M) hx

/-- Pointwise **Equation (1)** on the closed inner preimage: whenever
`f x ∈ baseClosedSubdisk M (rInner M)`, `alignedVolumeForm M` equals
`Φ^* (p_F^* ω_F ∧ p_B^* μ_B)`. -/
theorem alignedVolumeForm_eq_trivializedProductForm_of_mem_closedInner {x : M}
    (hx_in :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      A.fibration x ∈ baseClosedSubdisk M (rInner M) (rInner_lt_baseRadius M)) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    (alignedVolumeForm M).1 x =
      show TangentSpace (𝓡 4) x [⋀^Fin 4]→L[ℝ] Bundle.Trivial M ℝ x from
        (trivializedProductForm M).1
          ⟨x, baseClosedSubdisk_subset_baseRegion M (rInner M) (rInner_lt_baseRadius M) hx_in⟩ := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  have hx_pre : x ∈ A.fibration.preimageOpen.1 :=
    baseClosedSubdisk_subset_baseRegion M (rInner M) (rInner_lt_baseRadius M) hx_in
  have hχ1 : alignedCutoff M (A.fibration x) = 1 :=
    alignedCutoff_eq_one_of_mem_closedInner M hx_in
  rw [coe_alignedVolumeForm, alignedRoughForm_of_mem M hx_pre, hχ1, sub_self, zero_smul, one_smul,
    zero_add]

/-- **Equation (1) (`S4TCdiffeo-Aug-2026.tex`, Eq. (1))**:
On the open neighborhood `innerPreimageOpen M` (`f ⁻¹' (baseDisk '' ball 0 rInner)`), the
restriction of `alignedVolumeForm M` equals `Φ^* (p_F^* ω_F ∧ p_B^* μ_B)`. -/
theorem mpullback_innerPreimageOpen_alignedVolumeForm :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    TauCeti.SmoothForm.mpullback (Subtype.val : innerPreimageOpen M → M) contMDiff_subtype_val
        (alignedVolumeForm M) =
      TauCeti.SmoothForm.mpullback (Opens.inclusion (innerPreimageOpen_le_preimageOpen M))
        (contMDiff_inclusion _) (trivializedProductForm M) := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  refine TauCeti.SmoothBundleForm.ext fun u v ↦ ?_
  have hl :
      (show ℝ from (TauCeti.SmoothForm.mpullback (Subtype.val : innerPreimageOpen M → M)
        contMDiff_subtype_val (alignedVolumeForm M)).1 u v) =
      (show ℝ from (alignedVolumeForm M).1 u.1 v) :=
    DFunLike.congr_fun
      (TauCeti.SmoothForm.coe_mpullback_subtype_val_apply (alignedVolumeForm M) u) v
  have hr :
      (show ℝ from (TauCeti.SmoothForm.mpullback
        (Opens.inclusion (innerPreimageOpen_le_preimageOpen M))
        (contMDiff_inclusion _) (trivializedProductForm M)).1 u v) =
      (show ℝ from (trivializedProductForm M).1
        (Opens.inclusion (innerPreimageOpen_le_preimageOpen M) u) v) := by
    rw [TauCeti.SmoothForm.coe_mpullback]
    exact DFunLike.congr_fun
      (TauCeti.mpullback_inclusion_apply (innerPreimageOpen_le_preimageOpen M)
        (trivializedProductForm M).1 u) v
  have heq :
      (show ℝ from (alignedVolumeForm M).1 u.1 v) =
      (show ℝ from (trivializedProductForm M).1
        (Opens.inclusion (innerPreimageOpen_le_preimageOpen M) u) v) :=
    DFunLike.congr_fun
      (alignedVolumeForm_eq_trivializedProductForm_of_mem_closedInner M
        (baseOpenSubdisk_subset_baseClosedSubdisk M (rInner M) (rInner_lt_baseRadius M) u.2)) v
  exact hl.trans (heq.trans hr.symm)

end AlignedVolume

/-! ## 4. `alignedPositiveVolume` & Adapted Unimodular Jacobian–Poisson Structure -/

section AdaptedPoisson

variable (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [A : AdmitsWrinkledOrBrokenLefschetzFibration M]

/-- Positive volume form package `(Ω, μ_Ω)` on compact `M` induced by `alignedVolumeForm M`. -/
noncomputable def alignedPositiveVolume : PositiveVolumeForm (𝓡 4) M :=
  PositiveVolumeForm.ofSmoothTopForm (alignedVolumeForm M) (alignedVolumeForm_ne_zero M)

@[simp]
theorem alignedPositiveVolume_Ω : (alignedPositiveVolume M).Ω = alignedVolumeForm M :=
  rfl

/-- **Adapted Generically Rank-2 Unimodular Jacobian–Poisson Structure `π_f`** on `M`
(`GSV15` Theorem 2.6, `BV21`, `S4TCdiffeo-Aug-2026.tex`, Proposition 1). -/
noncomputable def adaptedJacobianPoisson : PoissonStructure (𝓡 4) M := by
  letI := A.instTopologicalSpaceFiber
  letI := A.instChartedSpaceFiber
  letI := A.instIsManifoldFiber
  letI := A.instT2SpaceFiber
  letI := A.instCompactSpaceFiber
  letI := A.instNonemptyFiber
  exact jacobianPoissonOfPositiveVolume (alignedPositiveVolume M) S2VolumeForm
    A.fibration A.fibration.contMDiff_toFun

/-- `adaptedJacobianPoisson M` is globally unimodular with invariant volume
`(alignedPositiveVolume M).Ω` across all of `M` (including `Crit(f)`). -/
theorem isUnimodularWithVolume_adaptedJacobianPoisson :
    (adaptedJacobianPoisson M).IsUnimodularWithVolume (alignedPositiveVolume M).Ω := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  exact isUnimodularWithVolume_jacobianPoisson (alignedPositiveVolume M).Ω
    (alignedPositiveVolume M).Ω_ne_zero S2VolumeForm A.fibration A.fibration.contMDiff_toFun

/-- `(M, adaptedJacobianPoisson M)` is a unimodular Poisson manifold (`IsUnimodularPoisson`). -/
theorem isUnimodularPoisson_adaptedJacobianPoisson :
    (adaptedJacobianPoisson M).IsUnimodularPoisson := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  exact isUnimodularPoisson_jacobianPoissonOfPositiveVolume (alignedPositiveVolume M)
    S2VolumeForm A.fibration A.fibration.contMDiff_toFun

/-- At every regular point `x ∉ criticalPoints (𝓡 4) (𝓡 2) A.fibration`, `adaptedJacobianPoisson M`
has rank `2`. -/
theorem rankAt_adaptedJacobianPoisson_of_notMem_criticalPoints {x : M}
    (hreg :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      x ∉ criticalPoints (𝓡 4) (𝓡 2) A.fibration) :
    (adaptedJacobianPoisson M).rankAt x = 2 := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  exact rankAt_jacobianPoisson_of_notMem_criticalSet (alignedPositiveVolume M).Ω
    (alignedPositiveVolume M).Ω_ne_zero S2VolumeForm A.fibration A.fibration.contMDiff_toFun
    hreg (S2VolumeForm_ne_zero _)

/-- At every critical point `x ∈ criticalPoints (𝓡 4) (𝓡 2) A.fibration`, `adaptedJacobianPoisson M`
has rank `0`. -/
theorem rankAt_adaptedJacobianPoisson_of_mem_criticalPoints {x : M}
    (hcrit :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      x ∈ criticalPoints (𝓡 4) (𝓡 2) A.fibration) :
    (adaptedJacobianPoisson M).rankAt x = 0 := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  exact rankAt_jacobianPoisson_of_mem_criticalSet (alignedPositiveVolume M).Ω
    (alignedPositiveVolume M).Ω_ne_zero S2VolumeForm A.fibration A.fibration.contMDiff_toFun hcrit

/-- Every smooth function `u ∘ f` pulled back from `Sphere2` is a Casimir of
`adaptedJacobianPoisson M`. -/
theorem isCasimir_comp_adaptedJacobianPoisson (u : C^∞⟮𝓡 2, Sphere2; ℝ⟯) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    (adaptedJacobianPoisson M).IsCasimir (u.comp ⟨A.fibration, A.fibration.contMDiff_toFun⟩) := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  exact isCasimir_comp_jacobianPoisson (alignedPositiveVolume M).Ω
    (alignedPositiveVolume M).Ω_ne_zero S2VolumeForm A.fibration A.fibration.contMDiff_toFun u

end AdaptedPoisson

end S4TuringPoisson
