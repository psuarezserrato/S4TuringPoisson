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

public import S4TuringPoisson.Dynamics.UndecidabilityAndTransfer
public import S4TuringPoisson.Extension.AlignedUnimodularVolume
public import S4TuringPoisson.Smoothing.DiskSmoothing
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic

/-!
# Leafwise Bump Isotopy Lift & 4-Manifold Turing Completeness (Milestone M4.2)

This module implements Milestone M4.2 of `S4TuringPoisson` (`S4TCdiffeo-Aug-2026.tex`, §4):

Given any smooth `4`-manifold `M` admitting `[A : AdmitsWrinkledOrBrokenLefschetzFibration M]`
(with an unconditional instance on `Sphere4`):

1. **Concentric Base Bump `bumpProfile` (`ρ : Sphere2 → ℝ`)**:
   - Constructs `bumpProfile M : Sphere2 → ℝ` (`0 ≤ ρ ≤ 1`, $C^\infty$ smooth) via `baseDiskBump`
     with inner radius `rCore M` and outer radius `rMid M < rInner M`, so that:
     - `ρ ≡ 1` on `B₀ := baseCoreOpen M` (`baseDisk '' ball 0 rCore`), and
     - `tsupport ρ ⊆ baseInnerOpen M` (`baseDisk '' ball 0 rInner`), where `alignedCutoff` (`χ`) is
       identically `1` and **Equation (1)** holds.

2. **Global Leafwise Bump Diffeomorphism (`leafwiseBumpDiffeomorphOfIsotopy`,
   `leafwiseBumpDiffeomorph`)**:
   - Lifts any `AreaPreservingDiskIsotopy r₀` (and hence
     `[HasTuringCompleteAreaPreservingDiskIsotopy]`) along
     `fiberDiskChart M : SymplecticDiskChart A.Fiber A.fiberVolume.Ω` to `d_t^F : Fiber ≃ₘ Fiber`
     and extends `(b, y) ↦ (b, d_{ρ(b)}^F(y))` from `A.fibration.preimageOpen` by `id` outside
     `tsupport (ρ ∘ f)` to a global $C^\infty$ diffeomorphism `M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M`.

3. **Foliation Tangency, Leafwise Symplectomorphism, Global Volume & Poisson Invariance**:
   - Proves `f ∘ d_bar = f` globally across `M`, leafwise area-form preservation
     `(d_{ρ(b)}^F)^* ω_F = ω_F` over `baseRegion`, and `d_bar = id` outside `tsupport (ρ ∘ f)`.
   - Proves block-triangular wedge annihilation `(b, y) ↦ (b, d_{ρ(b)}^F(y))` on
     `p_F^* ω_F ∧ p_B^* μ_B` and deduces **global volume preservation**
     `mpullback d_bar _ alignedVolumeForm = alignedVolumeForm`,
     `MeasurePreserving ⇑d_bar alignedPositiveVolume.μ alignedPositiveVolume.μ`, and **global
     Poisson automorphism** (`IsPoissonMap` for `adaptedJacobianPoisson M`) on `[CompactSpace M]`.

4. **4-Manifold Turing Completeness & Undecidability (`isTuringComplete_leafwiseBumpDiffeomorph`)**:
   - Applies `IsTuringComplete.transfer` (`UndecidabilityAndTransfer.lean`) over `B₀ × diskOpen`
     (`ρ ≡ 1` on `B₀`) to establish `IsTuringComplete ⇑(leafwiseBumpDiffeomorph M)`, `≠ id`, and
     algorithmic undecidability of forward-orbit reachability.
-/

@[expose] public section

open Bundle Filter Function MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace S4TuringPoisson

/-! ## 1. Block-Triangular Wedge Pullback on Product 4-Manifolds `M₁ × M₂` -/

section BlockTriangularWedge

private theorem alternatingMap_eq_of_spanning_four {V F : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup F] [Module ℝ F]
    (E : Fin (2 + 2) → V)
    (hspan : ∀ u : V, ∃ c : Fin (2 + 2) → ℝ, u = ∑ j, c j • E j)
    (ω₁ ω₂ : AlternatingMap ℝ V F (Fin (2 + 2)))
    (heq : ω₁ E = ω₂ E)
    (v : Fin (2 + 2) → V) :
    ω₁ v = ω₂ v := by
  have h_idx (r : Fin (2 + 2) → Fin (2 + 2)) : ω₁ (E ∘ r) = ω₂ (E ∘ r) := by
    by_cases hr : Function.Injective r
    · let σ : Equiv.Perm (Fin (2 + 2)) :=
        Equiv.ofBijective r (Finite.injective_iff_bijective.mp hr)
      have hcomp : E ∘ r = E ∘ ⇑σ := rfl
      rw [hcomp, ω₁.map_perm E σ, ω₂.map_perm E σ, heq]
    · simp only [Function.Injective, not_forall] at hr
      obtain ⟨i, j, hij_eq, hij_ne⟩ := hr
      rw [ω₁.map_eq_zero_of_eq (E ∘ r) (by simp [hij_eq]) hij_ne,
        ω₂.map_eq_zero_of_eq (E ∘ r) (by simp [hij_eq]) hij_ne]
  choose c hc using fun i ↦ hspan (v i)
  have hv : v = fun i ↦ ∑ j : Fin (2 + 2), c i j • E j := funext hc
  rw [hv]
  change ω₁.toMultilinearMap (fun i ↦ ∑ j, c i j • E j) =
    ω₂.toMultilinearMap (fun i ↦ ∑ j, c i j • E j)
  rw [ω₁.toMultilinearMap.map_sum, ω₂.toMultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  change (ω₁.toMultilinearMap fun i ↦ c i (r i) • (E ∘ r) i) =
    ω₂.toMultilinearMap fun i ↦ c i (r i) • (E ∘ r) i
  rw [ω₁.toMultilinearMap.map_smul_univ (fun i ↦ c i (r i)) (E ∘ r),
    ω₂.toMultilinearMap.map_smul_univ (fun i ↦ c i (r i)) (E ∘ r)]
  exact congrArg _ (h_idx r)

private theorem tangentSpace_r2_decomp {M : Type*} [TopologicalSpace M]
    [ChartedSpace EuclideanPlane M] (x : M) (w : TangentSpace (𝓡 2) x) :
    let t₀ : TangentSpace (𝓡 2) x := (WithLp.toLp 2 ![1, (0 : ℝ)] : EuclideanPlane)
    let t₁ : TangentSpace (𝓡 2) x := (WithLp.toLp 2 ![0, (1 : ℝ)] : EuclideanPlane)
    ∃ c₀ c₁ : ℝ, w = c₀ • t₀ + c₁ • t₁ := by
  intro t₀ t₁
  let wE : EuclideanPlane := w
  refine ⟨WithLp.ofLp wE 0, WithLp.ofLp wE 1, ?_⟩
  change wE = (WithLp.ofLp wE 0) • (WithLp.toLp 2 ![1, (0 : ℝ)]) +
    (WithLp.ofLp wE 1) • (WithLp.toLp 2 ![0, (1 : ℝ)])
  ext i
  fin_cases i <;> simp

private theorem prodSurface_spanning {M₁ M₂ : Type*}
    [TopologicalSpace M₁] [ChartedSpace EuclideanPlane M₁]
    [TopologicalSpace M₂] [ChartedSpace EuclideanPlane M₂]
    (x : M₁) (y : M₂) :
    let t₀ : TangentSpace (𝓡 2) x := (WithLp.toLp 2 ![1, (0 : ℝ)] : EuclideanPlane)
    let t₁ : TangentSpace (𝓡 2) x := (WithLp.toLp 2 ![0, (1 : ℝ)] : EuclideanPlane)
    let s₀ : TangentSpace (𝓡 2) y := (WithLp.toLp 2 ![1, (0 : ℝ)] : EuclideanPlane)
    let s₁ : TangentSpace (𝓡 2) y := (WithLp.toLp 2 ![0, (1 : ℝ)] : EuclideanPlane)
    let e := TauCeti.Manifold.tangentSpaceProdEquiv (I := 𝓡 2) (J := 𝓡 2) (x, y)
    let E : Fin (2 + 2) → TangentSpace ((𝓡 2).prod (𝓡 2)) (x, y) :=
      ![e.symm (t₀, 0), e.symm (t₁, 0), e.symm (0, s₀), e.symm (0, s₁)]
    ∀ u : TangentSpace ((𝓡 2).prod (𝓡 2)) (x, y), ∃ c : Fin (2 + 2) → ℝ, u = ∑ j, c j • E j := by
  intro t₀ t₁ s₀ s₁ e E u
  obtain ⟨c₀, c₁, hc1⟩ := tangentSpace_r2_decomp x (e u).1
  obtain ⟨c₂, c₃, hc2⟩ := tangentSpace_r2_decomp y (e u).2
  refine ⟨![c₀, c₁, c₂, c₃], ?_⟩
  apply e.injective
  have h4 : (∑ j : Fin (2 + 2), (![c₀, c₁, c₂, c₃] : Fin 4 → ℝ) j • E j) =
      c₀ • E 0 + c₁ • E 1 + c₂ • E 2 + c₃ • E 3 := by
    rw [show (∑ j : Fin (2 + 2), (![c₀, c₁, c₂, c₃] : Fin 4 → ℝ) j • E j) =
      ∑ j : Fin 4, (![c₀, c₁, c₂, c₃] : Fin 4 → ℝ) j • E j from rfl, Fin.sum_univ_four]
    simp [add_assoc]
  rw [h4, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul]
  dsimp only [E, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  simp only [e.apply_symm_apply]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.smul_fst, smul_zero, add_zero]
    exact hc1
  · simp only [Prod.snd_add, Prod.smul_snd, smul_zero, zero_add]
    exact hc2

/-- **Block-Triangular `2 ∧ 2` Wedge Evaluation**:
Evaluating `p₁^* α ∧ p₂^* β` on `[ (a₀, c₀), (a₁, c₁), (0, b₀), (0, b₁) ]` annihilates the
off-diagonal vertical components `c₀, c₁` and yields `α(a₀, a₁) * β(b₀, b₁)`. -/
theorem wedge_mpullback_fst_snd_two_two_block
    {E₁ H₁ M₁ E₂ H₂ M₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ 1 M₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ 1 M₂]
    (α : TauCeti.SmoothForm I₁ M₁ ℝ 2) (β : TauCeti.SmoothForm I₂ M₂ ℝ 2)
    (p : M₁ × M₂) (a₀ a₁ : TangentSpace I₁ p.1) (c₀ c₁ b₀ b₁ : TangentSpace I₂ p.2) :
    let e := TauCeti.Manifold.tangentSpaceProdEquiv (I := I₁) (J := I₂) p
    (TauCeti.SmoothForm.wedge
        (TauCeti.SmoothForm.mpullback Prod.fst contMDiff_fst α)
        (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd β)).1 p
      ![e.symm (a₀, c₀), e.symm (a₁, c₁), e.symm (0, b₀), e.symm (0, b₁)] =
      α.1 p.1 ![a₀, a₁] * β.1 p.2 ![b₀, b₁] := by
  intro e
  let V : Fin (2 + 2) → TangentSpace (I₁.prod I₂) p :=
    ![e.symm (a₀, c₀), e.symm (a₁, c₁), e.symm (0, b₀), e.symm (0, b₁)]
  let f₁ : Fin (2 + 2) → TangentSpace I₁ p.1 := ![a₀, a₁, 0, 0]
  let f₂ : Fin (2 + 2) → TangentSpace I₂ p.2 := ![c₀, c₁, b₀, b₁]
  have hf₁ (k : Fin (2 + 2)) : (e (V k)).1 = f₁ k := by
    fin_cases k <;> simp [V, f₁]
  have hf₂ (k : Fin (2 + 2)) : (e (V k)).2 = f₂ k := by
    fin_cases k <;> simp [V, f₂]
  change (TauCeti.SmoothForm.wedge
      (TauCeti.SmoothForm.mpullback Prod.fst contMDiff_fst α)
      (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd β)).1 p V = _
  rw [TauCeti.SmoothForm.wedge_apply]
  simp_rw [TauCeti.SmoothForm.mpullback_fst_apply, TauCeti.SmoothForm.mpullback_snd_apply,
    show ∀ k, (TauCeti.Manifold.tangentSpaceProdEquiv p (V k)).1 = f₁ k from hf₁,
    show ∀ k, (TauCeti.Manifold.tangentSpaceProdEquiv p (V k)).2 = f₂ k from hf₂]
  let blockPerm (τ : Equiv.Perm (Fin 2) × Equiv.Perm (Fin 2)) : Equiv.Perm (Fin (2 + 2)) :=
    finSumFinEquiv.permCongr (Equiv.Perm.sumCongr τ.1 τ.2)
  have hblock_inj : Function.Injective blockPerm := by
    rintro ⟨τ₁, τ₂⟩ ⟨τ₁', τ₂'⟩ h
    have h' := finSumFinEquiv.permCongr.injective h
    exact Prod.ext
      (Equiv.ext fun i ↦ Sum.inl.inj (congrArg (fun σ ↦ σ (Sum.inl i)) h'))
      (Equiv.ext fun j ↦ Sum.inr.inj (congrArg (fun σ ↦ σ (Sum.inr j)) h'))
  let S : Finset (Equiv.Perm (Fin (2 + 2))) := Finset.univ.image blockPerm
  have hzero_outside : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin (2 + 2)))), σ ∉ S →
      Equiv.Perm.sign σ •
        (α.1 p.1 (fun i ↦ f₁ (σ (Fin.castAdd 2 i))) *
          β.1 p.2 (fun j ↦ f₂ (σ (Fin.natAdd 2 j)))) = 0 := by
    intro σ _ hnotS
    by_cases h01 : (σ 0).1 < 2 ∧ (σ 1).1 < 2
    · exfalso
      apply hnotS
      rw [Finset.mem_image]
      have hne01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
      have h2_ge : 2 ≤ (σ 2).1 := by
        by_contra! hlt2
        have hne02 : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
        have hne12 : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
        omega
      have h3_ge : 2 ≤ (σ 3).1 := by
        by_contra! hlt2
        have hne03 : σ 0 ≠ σ 3 := σ.injective.ne (by decide)
        have hne13 : σ 1 ≠ σ 3 := σ.injective.ne (by decide)
        omega
      let τ₁ : Equiv.Perm (Fin 2) := if (σ 0).1 = 0 then 1 else Equiv.swap 0 1
      let τ₂ : Equiv.Perm (Fin 2) := if (σ 2).1 = 2 then 1 else Equiv.swap 0 1
      refine ⟨(τ₁, τ₂), Finset.mem_univ _, Equiv.ext fun k ↦ ?_⟩
      have hne23 : σ 2 ≠ σ 3 := σ.injective.ne (by decide)
      have h0_lt : (σ 0).1 < 2 := h01.1
      have h1_lt : (σ 1).1 < 2 := h01.2
      have h2_lt : (σ 2).1 < 4 := (σ 2).2
      have h3_lt : (σ 3).1 < 4 := (σ 3).2
      have hne01_val : (σ 0).1 ≠ (σ 1).1 := Fin.val_ne_of_ne hne01
      have hne23_val : (σ 2).1 ≠ (σ 3).1 := Fin.val_ne_of_ne hne23
      fin_cases k
      · change finSumFinEquiv (Equiv.Perm.sumCongr τ₁ τ₂ (finSumFinEquiv.symm 0)) = σ 0
        have hs0 : finSumFinEquiv.symm (0 : Fin (2 + 2)) = Sum.inl 0 :=
          finSumFinEquiv.symm_apply_eq.mpr rfl
        rw [hs0, Equiv.Perm.sumCongr_apply, Sum.map_inl, finSumFinEquiv_apply_left]
        dsimp only [τ₁]
        split_ifs with h0
        · exact Fin.ext h0.symm
        · rw [Equiv.swap_apply_left]
          exact Fin.ext (show 1 = (σ 0).1 by omega)
      · change finSumFinEquiv (Equiv.Perm.sumCongr τ₁ τ₂ (finSumFinEquiv.symm 1)) = σ 1
        have hs1 : finSumFinEquiv.symm (1 : Fin (2 + 2)) = Sum.inl 1 :=
          finSumFinEquiv.symm_apply_eq.mpr rfl
        rw [hs1, Equiv.Perm.sumCongr_apply, Sum.map_inl, finSumFinEquiv_apply_left]
        dsimp only [τ₁]
        split_ifs with h0
        · exact Fin.ext (show 1 = (σ 1).1 by omega)
        · rw [Equiv.swap_apply_right]
          exact Fin.ext (show 0 = (σ 1).1 by omega)
      · change finSumFinEquiv (Equiv.Perm.sumCongr τ₁ τ₂ (finSumFinEquiv.symm 2)) = σ 2
        have hs2 : finSumFinEquiv.symm (2 : Fin (2 + 2)) = Sum.inr 0 :=
          finSumFinEquiv.symm_apply_eq.mpr rfl
        rw [hs2, Equiv.Perm.sumCongr_apply, Sum.map_inr, finSumFinEquiv_apply_right]
        dsimp only [τ₂]
        split_ifs with h2
        · exact Fin.ext h2.symm
        · rw [Equiv.swap_apply_left]
          exact Fin.ext (show 3 = (σ 2).1 by omega)
      · change finSumFinEquiv (Equiv.Perm.sumCongr τ₁ τ₂ (finSumFinEquiv.symm 3)) = σ 3
        have hs3 : finSumFinEquiv.symm (3 : Fin (2 + 2)) = Sum.inr 1 :=
          finSumFinEquiv.symm_apply_eq.mpr rfl
        rw [hs3, Equiv.Perm.sumCongr_apply, Sum.map_inr, finSumFinEquiv_apply_right]
        dsimp only [τ₂]
        split_ifs with h2
        · exact Fin.ext (show 3 = (σ 3).1 by omega)
        · rw [Equiv.swap_apply_right]
          exact Fin.ext (show 2 = (σ 3).1 by omega)
    · have hα_zero : α.1 p.1 (fun i ↦ f₁ (σ (Fin.castAdd 2 i))) = 0 := by
        by_cases h0 : (σ 0).1 < 2
        · have h1 : 2 ≤ (σ 1).1 := not_lt.mp fun h1 ↦ h01 ⟨h0, h1⟩
          have hf1_zero : f₁ (σ (Fin.castAdd 2 1)) = 0 := by
            change f₁ (σ 1) = 0
            rcases hσ1 : σ 1 with ⟨val, hlt⟩
            rw [hσ1] at h1
            interval_cases val <;> rfl
          exact (α.1 p.1).map_coord_zero 1 hf1_zero
        · have h0' : 2 ≤ (σ 0).1 := not_lt.mp h0
          have hf0_zero : f₁ (σ (Fin.castAdd 2 0)) = 0 := by
            change f₁ (σ 0) = 0
            rcases hσ0 : σ 0 with ⟨val, hlt⟩
            rw [hσ0] at h0'
            interval_cases val <;> rfl
          exact (α.1 p.1).map_coord_zero 0 hf0_zero
      rw [hα_zero, zero_mul, smul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ S) hzero_outside,
    Finset.sum_image fun _ _ _ _ h ↦ hblock_inj h]
  have hterm (τ : Equiv.Perm (Fin 2) × Equiv.Perm (Fin 2)) :
      Equiv.Perm.sign (blockPerm τ) •
        (α.1 p.1 (fun i ↦ f₁ (blockPerm τ (Fin.castAdd 2 i))) *
          β.1 p.2 (fun j ↦ f₂ (blockPerm τ (Fin.natAdd 2 j)))) =
        α.1 p.1 ![a₀, a₁] * β.1 p.2 ![b₀, b₁] := by
    have hsign : Equiv.Perm.sign (blockPerm τ) = Equiv.Perm.sign τ.1 * Equiv.Perm.sign τ.2 := by
      simp [blockPerm, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr]
    have hleft : (fun i ↦ f₁ (blockPerm τ (Fin.castAdd 2 i))) = (![a₀, a₁] : Fin 2 → _) ∘ ⇑τ.1 := by
      funext i
      have hc : blockPerm τ (Fin.castAdd 2 i) = Fin.castAdd 2 (τ.1 i) := by
        dsimp only [blockPerm, Equiv.permCongr_apply]
        rw [← finSumFinEquiv_apply_left, Equiv.symm_apply_apply, Equiv.Perm.sumCongr_apply,
          Sum.map_inl, finSumFinEquiv_apply_left]
      rw [hc]
      dsimp only [Function.comp_apply]
      rcases hv : τ.1 i with ⟨val, hlt⟩
      interval_cases val <;> rfl
    have hright :
        (fun j ↦ f₂ (blockPerm τ (Fin.natAdd 2 j))) = (![b₀, b₁] : Fin 2 → _) ∘ ⇑τ.2 := by
      funext j
      have hc : blockPerm τ (Fin.natAdd 2 j) = Fin.natAdd 2 (τ.2 j) := by
        dsimp only [blockPerm, Equiv.permCongr_apply]
        rw [← finSumFinEquiv_apply_right, Equiv.symm_apply_apply, Equiv.Perm.sumCongr_apply,
          Sum.map_inr, finSumFinEquiv_apply_right]
      rw [hc]
      dsimp only [Function.comp_apply]
      rcases hv : τ.2 j with ⟨val, hlt⟩
      interval_cases val <;> rfl
    have hp1 : α.1 p.1 ((![a₀, a₁] : Fin 2 → _) ∘ ⇑τ.1) =
        Equiv.Perm.sign τ.1 • α.1 p.1 ![a₀, a₁] :=
      (α.1 p.1).toAlternatingMap.map_perm ![a₀, a₁] τ.1
    have hp2 : β.1 p.2 ((![b₀, b₁] : Fin 2 → _) ∘ ⇑τ.2) =
        Equiv.Perm.sign τ.2 • β.1 p.2 ![b₀, b₁] :=
      (β.1 p.2).toAlternatingMap.map_perm ![b₀, b₁] τ.2
    rw [hleft, hright, hp1, hp2, hsign]
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ.1) with hs1 | hs1 <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ.2) with hs2 | hs2 <;>
    simp [hs1, hs2]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]
  simp only [Nat.factorial, Nat.mul_one, nsmul_eq_mul, smul_eq_mul]
  ring

/-- **Fiberwise Symplectomorphism Preserves Product 4-Form (`S4TCdiffeo-Aug-2026.tex`, §4)**:
For any smooth surfaces `M₁, M₂` modeled on `𝓡 2`, `2`-forms `α ∈ Ω²(M₁)` and `β ∈ Ω²(M₂)`, and
smooth fiberwise map `Ψ : (x, y) ↦ (x, G(x, y))` whose vertical slices `y ↦ G(x, y)` preserve `β`,
`Ψ` preserves `p₁^* α ∧ p₂^* β` globally on `M₁ × M₂`. -/
theorem mpullback_fiberwise_wedge_two_two {M₁ M₂ : Type*}
    [TopologicalSpace M₁] [ChartedSpace EuclideanPlane M₁] [IsManifold (𝓡 2) ∞ M₁]
    [TopologicalSpace M₂] [ChartedSpace EuclideanPlane M₂] [IsManifold (𝓡 2) ∞ M₂]
    (α : TauCeti.SmoothForm (𝓡 2) M₁ ℝ 2) (β : TauCeti.SmoothForm (𝓡 2) M₂ ℝ 2)
    {G : M₁ × M₂ → M₂} (hG : ContMDiff ((𝓡 2).prod (𝓡 2)) (𝓡 2) ∞ G)
    (hβ_slice : ∀ x : M₁,
      TauCeti.SmoothForm.mpullback (fun y ↦ G (x, y))
        (hG.comp (contMDiff_const.prodMk contMDiff_id)) β = β) :
    TauCeti.SmoothForm.mpullback (fun p : M₁ × M₂ ↦ (p.1, G p)) (contMDiff_fst.prodMk hG)
        (TauCeti.SmoothForm.wedge
          (TauCeti.SmoothForm.mpullback Prod.fst contMDiff_fst α)
          (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd β)) =
      TauCeti.SmoothForm.wedge
        (TauCeti.SmoothForm.mpullback Prod.fst contMDiff_fst α)
        (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd β) := by
  let Ψ : M₁ × M₂ → M₁ × M₂ := fun p ↦ (p.1, G p)
  have hΨ : ContMDiff ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) ∞ Ψ := contMDiff_fst.prodMk hG
  let W := TauCeti.SmoothForm.wedge
    (TauCeti.SmoothForm.mpullback Prod.fst contMDiff_fst α)
    (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd β)
  refine Subtype.ext (funext fun ⟨x, y⟩ ↦ ContinuousAlternatingMap.ext fun v ↦ ?_)
  let t₀ : TangentSpace (𝓡 2) x := (WithLp.toLp 2 ![1, (0 : ℝ)] : EuclideanPlane)
  let t₁ : TangentSpace (𝓡 2) x := (WithLp.toLp 2 ![0, (1 : ℝ)] : EuclideanPlane)
  let s₀ : TangentSpace (𝓡 2) y := (WithLp.toLp 2 ![1, (0 : ℝ)] : EuclideanPlane)
  let s₁ : TangentSpace (𝓡 2) y := (WithLp.toLp 2 ![0, (1 : ℝ)] : EuclideanPlane)
  let e := TauCeti.Manifold.tangentSpaceProdEquiv (I := 𝓡 2) (J := 𝓡 2) (x, y)
  let e' := TauCeti.Manifold.tangentSpaceProdEquiv (I := 𝓡 2) (J := 𝓡 2) (x, G (x, y))
  let Bxy : Fin (2 + 2) → TangentSpace ((𝓡 2).prod (𝓡 2)) (x, y) :=
    ![e.symm (t₀, 0), e.symm (t₁, 0), e.symm (0, s₀), e.symm (0, s₁)]
  refine alternatingMap_eq_of_spanning_four Bxy (prodSurface_spanning x y)
    ((TauCeti.SmoothForm.mpullback Ψ hΨ W).1 (x, y)).toAlternatingMap
    (W.1 (x, y)).toAlternatingMap ?_ v
  change (TauCeti.SmoothForm.mpullback Ψ hΨ W).1 (x, y) Bxy = W.1 (x, y) Bxy
  have hrhs : W.1 (x, y) Bxy = α.1 x ![t₀, t₁] * β.1 y ![s₀, s₁] :=
    wedge_mpullback_fst_snd_two_two_block α β (x, y) t₀ t₁ 0 0 s₀ s₁
  have hfst_dΨ (u : TangentSpace ((𝓡 2).prod (𝓡 2)) (x, y)) :
      (e' (mfderiv ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) Ψ (x, y) u)).1 = (e u).1 := by
    have hΨd : MDifferentiableAt ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) Ψ (x, y) :=
      (hΨ (x, y)).mdifferentiableAt (by simp)
    have hcomp := congrArg (· u) (mfderiv_comp (x, y) mdifferentiableAt_fst hΨd)
    have hfst_Ψ : (Prod.fst : M₁ × M₂ → M₁) ∘ Ψ = Prod.fst := rfl
    rw [hfst_Ψ, ContinuousLinearMap.comp_apply, mfderiv_fst, mfderiv_fst] at hcomp
    rw [show e' _ = _ from TauCeti.Manifold.tangentSpaceProdEquiv_apply (x, G (x, y)) _,
      show e u = u from TauCeti.Manifold.tangentSpaceProdEquiv_apply (x, y) u]
    exact hcomp.symm
  let ι : M₂ → M₁ × M₂ := fun z ↦ (x, z)
  have hι_mfderiv (w : TangentSpace (𝓡 2) y) :
      mfderiv (𝓡 2) ((𝓡 2).prod (𝓡 2)) ι y w = e.symm (0, w) := by
    have hd : mfderiv (𝓡 2) ((𝓡 2).prod (𝓡 2)) ι y =
        (mfderiv (𝓡 2) (𝓡 2) (fun _ : M₂ ↦ x) y).prod (mfderiv (𝓡 2) (𝓡 2) id y) :=
      mfderiv_prodMk mdifferentiableAt_const mdifferentiableAt_id
    rw [hd, mfderiv_const, mfderiv_id,
      show e.symm (0, w) = (0, w) from
        TauCeti.Manifold.tangentSpaceProdEquiv_symm_apply (x, y) (0, w)]
    rfl
  let Gx : M₂ → M₂ := fun z ↦ G (x, z)
  have hGx : ContMDiff (𝓡 2) (𝓡 2) ∞ Gx := hG.comp (contMDiff_const.prodMk contMDiff_id)
  have hsnd_vert (w : TangentSpace (𝓡 2) y) :
      (e' (mfderiv ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) Ψ (x, y) (e.symm (0, w)))).2 =
        mfderiv (𝓡 2) (𝓡 2) Gx y w := by
    rw [← hι_mfderiv w]
    have hιd : MDifferentiableAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) ι y :=
      mdifferentiableAt_const.prodMk mdifferentiableAt_id
    have hΨd : MDifferentiableAt ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) Ψ (ι y) :=
      (hΨ (x, y)).mdifferentiableAt (by simp)
    have h1 := congrArg (· (mfderiv (𝓡 2) ((𝓡 2).prod (𝓡 2)) ι y w))
      (mfderiv_comp (ι y) mdifferentiableAt_snd hΨd)
    have h2 := congrArg (· w) (mfderiv_comp y (mdifferentiableAt_snd.comp (ι y) hΨd) hιd)
    have hGx_eq : ((Prod.snd : M₁ × M₂ → M₂) ∘ Ψ) ∘ ι = Gx := rfl
    rw [hGx_eq, ContinuousLinearMap.comp_apply] at h2
    rw [ContinuousLinearMap.comp_apply, mfderiv_snd] at h1
    rw [show e' _ = _ from TauCeti.Manifold.tangentSpaceProdEquiv_apply (x, G (x, y)) _]
    exact (show (mfderiv ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) Ψ (x, y)
      (mfderiv (𝓡 2) ((𝓡 2).prod (𝓡 2)) ι y w)).2 = _ from h1.symm).trans h2.symm
  let c₀ := (e' (mfderiv ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) Ψ (x, y) (Bxy 0))).2
  let c₁ := (e' (mfderiv ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) Ψ (x, y) (Bxy 1))).2
  let d₀ := mfderiv (𝓡 2) (𝓡 2) Gx y s₀
  let d₁ := mfderiv (𝓡 2) (𝓡 2) Gx y s₁
  have hd0 :
      mfderiv ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) Ψ (x, y) (Bxy 0) =
        e'.symm (t₀, c₀) := by
    apply e'.injective
    rw [e'.apply_symm_apply]
    refine Prod.ext ?_ rfl
    rw [hfst_dΨ (Bxy 0), show Bxy 0 = e.symm (t₀, 0) from rfl, e.apply_symm_apply]
  have hd1 :
      mfderiv ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) Ψ (x, y) (Bxy 1) =
        e'.symm (t₁, c₁) := by
    apply e'.injective
    rw [e'.apply_symm_apply]
    refine Prod.ext ?_ rfl
    rw [hfst_dΨ (Bxy 1), show Bxy 1 = e.symm (t₁, 0) from rfl, e.apply_symm_apply]
  have hd2 :
      mfderiv ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) Ψ (x, y) (Bxy 2) =
        e'.symm (0, d₀) := by
    apply e'.injective
    rw [e'.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · rw [hfst_dΨ (Bxy 2), show Bxy 2 = e.symm (0, s₀) from rfl, e.apply_symm_apply]
    · rw [show Bxy 2 = e.symm (0, s₀) from rfl, hsnd_vert s₀]
  have hd3 :
      mfderiv ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) Ψ (x, y) (Bxy 3) =
        e'.symm (0, d₁) := by
    apply e'.injective
    rw [e'.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · rw [hfst_dΨ (Bxy 3), show Bxy 3 = e.symm (0, s₁) from rfl, e.apply_symm_apply]
    · rw [show Bxy 3 = e.symm (0, s₁) from rfl, hsnd_vert s₁]
  have hd_vec :
      (fun k : Fin (2 + 2) ↦ mfderiv ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) Ψ (x, y) (Bxy k)) =
        ![e'.symm (t₀, c₀), e'.symm (t₁, c₁), e'.symm (0, d₀), e'.symm (0, d₁)] := by
    funext k
    rcases k with ⟨val, hlt⟩
    interval_cases val
    · exact hd0
    · exact hd1
    · exact hd2
    · exact hd3
  rw [TauCeti.SmoothForm.mpullback_apply, hd_vec]
  have hlhs := wedge_mpullback_fst_snd_two_two_block α β (x, G (x, y)) t₀ t₁ c₀ c₁ d₀ d₁
  have hβ_pull : β.1 (Gx y) ![d₀, d₁] = β.1 y ![s₀, s₁] := by
    have hvec : (![d₀, d₁] : Fin 2 → TangentSpace (𝓡 2) (Gx y)) =
        fun i ↦ mfderiv (𝓡 2) (𝓡 2) Gx y (![s₀, s₁] i) := by
      funext i; fin_cases i <;> rfl
    rw [hvec, ← TauCeti.SmoothForm.mpullback_apply Gx hGx β y ![s₀, s₁], hβ_slice x]
  exact (hlhs.trans (congrArg (α.1 x ![t₀, t₁] * ·) hβ_pull)).trans hrhs.symm

end BlockTriangularWedge

/-! ## 2. Surface Isotopy Slice Lifting for Arbitrary `AreaPreservingDiskIsotopy` -/

section SurfaceIsotopyLift

set_option linter.concreteInstances false in
/-- View `[HasTuringCompleteAreaPreservingDiskIsotopy]` as an `AreaPreservingDiskIsotopy`. -/
noncomputable def AreaPreservingDiskIsotopy.ofTypeclass
    [H : HasTuringCompleteAreaPreservingDiskIsotopy] :
    AreaPreservingDiskIsotopy H.r₀ where
  r₀_mem_Ioo := H.r₀_mem_Ioo
  d := H.d
  dInv := H.dInv
  contDiff_d := H.contDiff_d
  contDiff_dInv := H.contDiff_dInv
  left_inv := H.left_inv
  right_inv := H.right_inv
  eq_self_of_notMem_ball := H.eq_self_of_notMem_ball
  time_zero := H.time_zero
  det_fderiv_eq_one := H.det_fderiv_eq_one

namespace SymplecticDiskChart

variable {F : Type*} [TopologicalSpace F] [ChartedSpace EuclideanPlane F]
  [IsManifold (𝓡 2) ∞ F] [T2Space F] {η : TauCeti.SmoothTwoForm (𝓡 2) F}

private theorem mpullback_congr_fun_two_ext {E₁ H₁ M₁ E₂ H₂ M₂ : Type*}
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

/-- Time-`t` slice of an `AreaPreservingDiskIsotopy r₀` lifted through `C : SymplecticDiskChart F η`
to a $C^\infty$ `Diffeomorph` of `F`. -/
noncomputable def liftIsotopyDiffeomorph (C : SymplecticDiskChart F η) {r₀ : ℝ}
    (I_disk : AreaPreservingDiskIsotopy r₀) (t : ℝ) :
    F ≃ₘ⟮𝓡 2, 𝓡 2⟯ F where
  toFun z := C.liftThroughChart I_disk.d (t, z)
  invFun z := C.liftThroughChart I_disk.dInv (t, z)
  left_inv z := C.liftThroughChart_comp_of_inv (fun s _ hw ↦ I_disk.mem_unitDisk2 s hw)
    I_disk.left_inv t z
  right_inv z := C.liftThroughChart_comp_of_inv (fun s _ hw ↦ I_disk.symm.mem_unitDisk2 s hw)
    I_disk.right_inv t z
  contMDiff_toFun :=
    (C.contMDiff_liftThroughChart I_disk.contDiff_d (fun s _ hw ↦ I_disk.mem_unitDisk2 s hw)
      I_disk.r₀_lt_one I_disk.eq_self_of_notMem_ball).comp (contMDiff_const.prodMk contMDiff_id)
  contMDiff_invFun :=
    (C.contMDiff_liftThroughChart I_disk.contDiff_dInv
      (fun s _ hw ↦ I_disk.symm.mem_unitDisk2 s hw)
      I_disk.r₀_lt_one (fun s _ hw ↦ I_disk.dInv_eq_self_of_notMem_ball s hw)).comp
      (contMDiff_const.prodMk contMDiff_id)

@[simp]
theorem liftIsotopyDiffeomorph_apply (C : SymplecticDiskChart F η) {r₀ : ℝ}
    (I_disk : AreaPreservingDiskIsotopy r₀) (t : ℝ) (z : F) :
    C.liftIsotopyDiffeomorph I_disk t z = C.liftThroughChart I_disk.d (t, z) :=
  rfl

@[simp]
theorem liftIsotopyDiffeomorph_symm_apply (C : SymplecticDiskChart F η) {r₀ : ℝ}
    (I_disk : AreaPreservingDiskIsotopy r₀) (t : ℝ) (z : F) :
    (C.liftIsotopyDiffeomorph I_disk t).symm z = C.liftThroughChart I_disk.dInv (t, z) :=
  rfl

@[simp]
theorem liftIsotopyDiffeomorph_zero (C : SymplecticDiskChart F η) {r₀ : ℝ}
    (I_disk : AreaPreservingDiskIsotopy r₀) :
    C.liftIsotopyDiffeomorph I_disk 0 = Diffeomorph.refl (𝓡 2) F ∞ := by
  ext z
  by_cases hz : z ∈ C.sourceOpen.1
  · obtain ⟨y, rfl⟩ := C.range_embed.symm.subset hz
    change C.liftThroughChart I_disk.d (0, C.embed y) = C.embed y
    rw [C.liftThroughChart_embed (fun s _ hw ↦ I_disk.mem_unitDisk2 s hw) 0 y]
    exact congrArg C.embed (Subtype.ext (I_disk.time_zero y.1))
  · exact C.liftThroughChart_of_notMem _ 0 hz

theorem liftIsotopyDiffeomorph_embed (C : SymplecticDiskChart F η) {r₀ : ℝ}
    (I_disk : AreaPreservingDiskIsotopy r₀) (t : ℝ) (y : diskOpen) :
    C.liftIsotopyDiffeomorph I_disk t (C.embed y) =
      C.embed ⟨I_disk.d (t, y.1), I_disk.mem_unitDisk2 t y.2⟩ :=
  C.liftThroughChart_embed (fun s _ hw ↦ I_disk.mem_unitDisk2 s hw) t y

/-- Every lifted slice `C.liftIsotopyDiffeomorph I_disk t` preserves `η` under smooth pullback. -/
theorem mpullback_liftIsotopyDiffeomorph_eq (C : SymplecticDiskChart F η) {r₀ : ℝ}
    (I_disk : AreaPreservingDiskIsotopy r₀) (t : ℝ) :
    TauCeti.SmoothForm.mpullback (C.liftIsotopyDiffeomorph I_disk t)
        (C.liftIsotopyDiffeomorph I_disk t).contMDiff η = η := by
  let Φ := C.liftIsotopyDiffeomorph I_disk t
  let δ : diskOpen → diskOpen := fun y ↦ ⟨I_disk.d (t, y.1), I_disk.mem_unitDisk2 t y.2⟩
  have hδ : ContMDiff (𝓡 2) (𝓡 2) ∞ δ :=
    (TauCeti.ContMDiff.subtypeVal_comp_iff diskOpen _).mp
      ((I_disk.contDiff_slice t).contMDiff.comp contMDiff_subtype_val)
  have hδ_area :
      TauCeti.SmoothForm.mpullback δ hδ
          (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val planeAreaForm) =
        TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val planeAreaForm := by
    have hval_δ : (Subtype.val : diskOpen → _) ∘ δ =
        (fun w ↦ I_disk.d (t, w)) ∘ Subtype.val := rfl
    calc
      TauCeti.SmoothForm.mpullback δ hδ
          (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val planeAreaForm)
        = TauCeti.SmoothForm.mpullback ((fun w ↦ I_disk.d (t, w)) ∘ Subtype.val)
            ((I_disk.contDiff_slice t).contMDiff.comp contMDiff_subtype_val) planeAreaForm := by
          rw [TauCeti.SmoothForm.mpullback_mpullback]
          exact mpullback_congr_fun_two_ext _ _ hval_δ planeAreaForm
      _ = TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val
            (TauCeti.SmoothForm.mpullback (fun w ↦ I_disk.d (t, w))
              (I_disk.contDiff_slice t).contMDiff planeAreaForm) := by
          rw [← TauCeti.SmoothForm.mpullback_mpullback (Subtype.val : diskOpen → EuclideanPlane)
            (fun w ↦ I_disk.d (t, w)) contMDiff_subtype_val (I_disk.contDiff_slice t).contMDiff
            planeAreaForm]
      _ = TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val planeAreaForm := by
          rw [I_disk.mpullback_planeAreaForm_eq t]
  have hpull_embed :
      TauCeti.SmoothForm.mpullback C.embed C.contMDiff_embed
          (TauCeti.SmoothForm.mpullback Φ Φ.contMDiff η) =
        TauCeti.SmoothForm.mpullback C.embed C.contMDiff_embed η := by
    have hcomm : ⇑Φ ∘ C.embed = C.embed ∘ δ :=
      funext fun y ↦ C.liftIsotopyDiffeomorph_embed I_disk t y
    calc
      TauCeti.SmoothForm.mpullback C.embed C.contMDiff_embed
          (TauCeti.SmoothForm.mpullback Φ Φ.contMDiff η)
        = TauCeti.SmoothForm.mpullback (C.embed ∘ δ) (C.contMDiff_embed.comp hδ) η := by
          rw [TauCeti.SmoothForm.mpullback_mpullback]
          exact mpullback_congr_fun_two_ext _ _ hcomm η
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
  · have hz_not_supp : z ∉ C.supportSet I_disk.r₀_lt_one :=
      fun hmem ↦ hz (C.supportSet_subset_sourceOpen I_disk.r₀_lt_one hmem)
    have hclosed : IsClosed (C.supportSet I_disk.r₀_lt_one) :=
      (C.isCompact_supportSet I_disk.r₀_lt_one).isClosed
    let V_compl : Opens F := ⟨(C.supportSet I_disk.r₀_lt_one)ᶜ, hclosed.isOpen_compl⟩
    let zV : V_compl := ⟨z, hz_not_supp⟩
    have hΦ_compl : ⇑Φ ∘ (Subtype.val : V_compl → F) = (Subtype.val : V_compl → F) :=
      funext fun w ↦ C.liftThroughChart_eq_self_of_notMem_supportSet
        I_disk.r₀_lt_one I_disk.eq_self_of_notMem_ball t w.2
    have hpull_compl :
        TauCeti.SmoothForm.mpullback (Subtype.val : V_compl → F) contMDiff_subtype_val
            (TauCeti.SmoothForm.mpullback Φ Φ.contMDiff η) =
          TauCeti.SmoothForm.mpullback (Subtype.val : V_compl → F) contMDiff_subtype_val η := by
      rw [TauCeti.SmoothForm.mpullback_mpullback]
      exact mpullback_congr_fun_two_ext _ _ hΦ_compl η
    have hsurj_compl :
        Function.Surjective (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : V_compl → F) zV) :=
      ((TauCeti.isLocalDiffeomorph_subtype_val (I := 𝓡 2) (n := ∞) zV).isInvertible_mfderiv
        (by simp)).surjective
    refine (TauCeti.mpullback_apply_eq_mpullback_apply_iff hsurj_compl).mp ?_
    simpa only [TauCeti.SmoothForm.coe_mpullback] using
      congrFun (congrArg Subtype.val hpull_compl) zV

end SymplecticDiskChart

end SurfaceIsotopyLift

/-! ## 3. Concentric Base Bump `bumpProfile` & Global Leafwise Bump Diffeomorphism -/

section BumpLiftGeneral

variable (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [A : AdmitsWrinkledOrBrokenLefschetzFibration M]

/-- Smooth base bump `ρ : Sphere2 → ℝ` (`0 ≤ ρ ≤ 1`, `ρ ≡ 1` on `baseCoreOpen M`,
`tsupport ρ ⊆ baseInnerOpen M`). -/
noncomputable def bumpProfile : Sphere2 → ℝ :=
  baseDiskBump M (rCore_pos M) (rCore_lt_rMid M)

theorem contMDiff_bumpProfile : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ (bumpProfile M) :=
  contMDiff_baseDiskBump M (rCore_pos M) (rCore_lt_rMid M) (rMid_lt_baseRadius M)

theorem bumpProfile_nonneg (b : Sphere2) : 0 ≤ bumpProfile M b :=
  baseDiskBump_nonneg M (rCore_pos M) (rCore_lt_rMid M) b

theorem bumpProfile_le_one (b : Sphere2) : bumpProfile M b ≤ 1 :=
  baseDiskBump_le_one M (rCore_pos M) (rCore_lt_rMid M) b

theorem bumpProfile_eq_one_of_mem_baseCoreOpen {b : Sphere2} (hb : b ∈ (baseCoreOpen M).1) :
    bumpProfile M b = 1 :=
  baseDiskBump_eq_one_of_mem_openSubdisk M (rCore_pos M) (rCore_lt_rMid M)
    (rMid_lt_baseRadius M) hb

theorem tsupport_bumpProfile_subset_baseInnerOpen :
    tsupport (bumpProfile M) ⊆ (baseInnerOpen M).1 :=
  (tsupport_baseDiskBump_subset M (rCore_pos M) (rCore_lt_rMid M)
    (rMid_lt_baseRadius M)).trans
    (baseClosedSubdisk_subset_baseOpenSubdisk M (rMid_lt_baseRadius M) (rMid_lt_rInner M))

theorem tsupport_bumpProfile_subset_baseRegion :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    tsupport (bumpProfile M) ⊆ A.fibration.baseRegion.1 := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  exact (tsupport_bumpProfile_subset_baseInnerOpen M).trans
    (baseOpenSubdisk_subset_baseRegion M (rInner M))

theorem tsupport_bumpProfile_comp_fibration_subset_innerPreimageOpen :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    tsupport (bumpProfile M ∘ A.fibration) ⊆ (innerPreimageOpen M).1 := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let K : Set M := A.fibration ⁻¹' tsupport (bumpProfile M)
  have hK_closed : IsClosed K :=
    (isClosed_tsupport (bumpProfile M)).preimage A.fibration.contMDiff_toFun.continuous
  have hsub_K : tsupport (bumpProfile M ∘ A.fibration) ⊆ K := by
    refine closure_minimal ?_ hK_closed
    intro x hx
    exact subset_tsupport (bumpProfile M) hx
  exact hsub_K.trans fun x hx ↦ tsupport_bumpProfile_subset_baseInnerOpen M hx

/-- Fiberwise bumped diffeomorphism `(b, y) ↦ (b, d_{ρ(b)}^F(y))` on
`A.fibration.baseRegion × A.Fiber` associated to any `AreaPreservingDiskIsotopy r₀`. -/
noncomputable def trivBumpDiffeomorphOfIsotopy {r₀ : ℝ}
    (I_disk : AreaPreservingDiskIsotopy r₀) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    (A.fibration.baseRegion × A.Fiber) ≃ₘ⟮(𝓡 2).prod (𝓡 2), (𝓡 2).prod (𝓡 2)⟯
      (A.fibration.baseRegion × A.Fiber) := by
  letI := A.instTopologicalSpaceFiber
  letI := A.instChartedSpaceFiber
  letI := A.instIsManifoldFiber
  letI := A.instT2SpaceFiber
  letI := A.instCompactSpaceFiber
  letI := A.instNonemptyFiber
  letI := A.instMeasurableSpaceFiber
  letI := A.instBorelSpaceFiber
  let C := AdmitsWrinkledOrBrokenLefschetzFibration.fiberDiskChart M
  let param : A.fibration.baseRegion × A.Fiber → ℝ × A.Fiber :=
    fun bz ↦ (bumpProfile M bz.1.1, bz.2)
  have hparam : ContMDiff ((𝓡 2).prod (𝓡 2)) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ param :=
    ((contMDiff_bumpProfile M).comp (contMDiff_subtype_val.comp contMDiff_fst)).prodMk contMDiff_snd
  have hd_smooth : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ (C.liftThroughChart I_disk.d) :=
    C.contMDiff_liftThroughChart I_disk.contDiff_d (fun s _ hw ↦ I_disk.mem_unitDisk2 s hw)
      I_disk.r₀_lt_one I_disk.eq_self_of_notMem_ball
  have hdInv_smooth : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ (C.liftThroughChart I_disk.dInv) :=
    C.contMDiff_liftThroughChart I_disk.contDiff_dInv
      (fun s _ hw ↦ I_disk.symm.mem_unitDisk2 s hw)
      I_disk.r₀_lt_one (fun s _ hw ↦ I_disk.dInv_eq_self_of_notMem_ball s hw)
  exact
    { toFun := fun bz ↦ (bz.1, C.liftThroughChart I_disk.d (param bz))
      invFun := fun bz ↦ (bz.1, C.liftThroughChart I_disk.dInv (param bz))
      left_inv := fun bz ↦ Prod.ext rfl
        (C.liftThroughChart_comp_of_inv (fun s _ hw ↦ I_disk.mem_unitDisk2 s hw)
          I_disk.left_inv (bumpProfile M bz.1.1) bz.2)
      right_inv := fun bz ↦ Prod.ext rfl
        (C.liftThroughChart_comp_of_inv (fun s _ hw ↦ I_disk.symm.mem_unitDisk2 s hw)
          I_disk.right_inv (bumpProfile M bz.1.1) bz.2)
      contMDiff_toFun := contMDiff_fst.prodMk (hd_smooth.comp hparam)
      contMDiff_invFun := contMDiff_fst.prodMk (hdInv_smooth.comp hparam) }

theorem coe_trivBumpDiffeomorphOfIsotopy {r₀ : ℝ}
    (I_disk : AreaPreservingDiskIsotopy r₀) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    letI := A.instMeasurableSpaceFiber
    letI := A.instBorelSpaceFiber
    ⇑(trivBumpDiffeomorphOfIsotopy M I_disk) =
      fun bz : A.fibration.baseRegion × A.Fiber ↦
        (bz.1, (AdmitsWrinkledOrBrokenLefschetzFibration.fiberDiskChart M).liftThroughChart
          I_disk.d (bumpProfile M bz.1.1, bz.2)) :=
  rfl

/-- Conjugated bumped diffeomorphism `Φ⁻¹ ∘ trivBumpDiffeomorph ∘ Φ` on
`A.fibration.preimageOpen`. -/
noncomputable def preimageBumpDiffeomorphOfIsotopy {r₀ : ℝ}
    (I_disk : AreaPreservingDiskIsotopy r₀) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    A.fibration.preimageOpen ≃ₘ⟮𝓡 4, 𝓡 4⟯ A.fibration.preimageOpen := by
  letI := A.instTopologicalSpaceFiber
  letI := A.instChartedSpaceFiber
  letI := A.instIsManifoldFiber
  letI := A.instT2SpaceFiber
  letI := A.instCompactSpaceFiber
  letI := A.instNonemptyFiber
  exact (A.fibration.trivialization.trans (trivBumpDiffeomorphOfIsotopy M I_disk)).trans
    A.fibration.trivialization.symm

theorem preimageBumpDiffeomorphOfIsotopy_eq_self_of_bump_zero {r₀ : ℝ}
    (I_disk : AreaPreservingDiskIsotopy r₀)
    (u :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      A.fibration.preimageOpen)
    (hρ :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      bumpProfile M (A.fibration u.1) = 0) :
    preimageBumpDiffeomorphOfIsotopy M I_disk u = u := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := A.instMeasurableSpaceFiber
  let _ := A.instBorelSpaceFiber
  let C := AdmitsWrinkledOrBrokenLefschetzFibration.fiberDiskChart M
  let bz := A.fibration.trivialization u
  have hb_eq : bz.1.1 = A.fibration u.1 :=
    congrArg Subtype.val (A.fibration.trivialization_fst u)
  have hρ_bz : bumpProfile M bz.1.1 = 0 := hb_eq ▸ hρ
  have hz0 : C.liftThroughChart I_disk.d (bumpProfile M bz.1.1, bz.2) = bz.2 := by
    rw [hρ_bz]
    change C.liftIsotopyDiffeomorph I_disk 0 bz.2 = bz.2
    rw [C.liftIsotopyDiffeomorph_zero I_disk]
    rfl
  change A.fibration.trivialization.symm
      (bz.1, C.liftThroughChart I_disk.d (bumpProfile M bz.1.1, bz.2)) = u
  rw [hz0, Prod.mk.eta]
  exact A.fibration.trivialization.symm_apply_apply u

theorem preimageBumpDiffeomorphOfIsotopy_symm_eq_self_of_bump_zero {r₀ : ℝ}
    (I_disk : AreaPreservingDiskIsotopy r₀)
    (u :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      A.fibration.preimageOpen)
    (hρ :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      bumpProfile M (A.fibration u.1) = 0) :
    (preimageBumpDiffeomorphOfIsotopy M I_disk).symm u = u :=
  preimageBumpDiffeomorphOfIsotopy_eq_self_of_bump_zero M I_disk.symm u hρ

/-- **Global Leafwise Bump Diffeomorphism (`S4TCdiffeo-Aug-2026.tex`, §4)**:
Extends `Φ⁻¹(b, d_{ρ(b)}^F(y))` smoothly by `id` outside `f ⁻¹' baseRegion` (and outside
`tsupport (ρ ∘ f)`). -/
noncomputable def leafwiseBumpDiffeomorphOfIsotopy {r₀ : ℝ}
    (I_disk : AreaPreservingDiskIsotopy r₀) :
    M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M := by
  letI := A.instTopologicalSpaceFiber
  letI := A.instChartedSpaceFiber
  letI := A.instIsManifoldFiber
  letI := A.instT2SpaceFiber
  letI := A.instCompactSpaceFiber
  letI := A.instNonemptyFiber
  let Λ := preimageBumpDiffeomorphOfIsotopy M I_disk
  let toF (x : M) : M :=
    letI := Classical.dec (x ∈ A.fibration.preimageOpen.1)
    if hx : x ∈ A.fibration.preimageOpen.1 then (Λ ⟨x, hx⟩).1 else x
  let invF (x : M) : M :=
    letI := Classical.dec (x ∈ A.fibration.preimageOpen.1)
    if hx : x ∈ A.fibration.preimageOpen.1 then (Λ.symm ⟨x, hx⟩).1 else x
  have hleft (x : M) : invF (toF x) = x := by
    by_cases hx : x ∈ A.fibration.preimageOpen.1
    · have hto : toF x = (Λ ⟨x, hx⟩).1 := dite_eq_left hx
      rw [hto]
      have hmem : (Λ ⟨x, hx⟩).1 ∈ A.fibration.preimageOpen.1 := (Λ ⟨x, hx⟩).2
      have hinv : invF (Λ ⟨x, hx⟩).1 = (Λ.symm (Λ ⟨x, hx⟩)).1 := dite_eq_left hmem
      rw [hinv, Λ.symm_apply_apply]
    · have hto : toF x = x := dite_eq_right hx
      rw [hto]
      exact dite_eq_right hx
  have hright (x : M) : toF (invF x) = x := by
    by_cases hx : x ∈ A.fibration.preimageOpen.1
    · have hinv : invF x = (Λ.symm ⟨x, hx⟩).1 := dite_eq_left hx
      rw [hinv]
      have hmem : (Λ.symm ⟨x, hx⟩).1 ∈ A.fibration.preimageOpen.1 := (Λ.symm ⟨x, hx⟩).2
      have hto : toF (Λ.symm ⟨x, hx⟩).1 = (Λ (Λ.symm ⟨x, hx⟩)).1 := dite_eq_left hmem
      rw [hto, Λ.apply_symm_apply]
    · have hinv : invF x = x := dite_eq_right hx
      rw [hinv]
      exact dite_eq_right hx
  let K : Set M := A.fibration ⁻¹' tsupport (bumpProfile M)
  have hK_closed : IsClosed K :=
    (isClosed_tsupport (bumpProfile M)).preimage A.fibration.contMDiff_toFun.continuous
  have hK_sub : K ⊆ A.fibration.preimageOpen.1 := fun y hy ↦
    tsupport_bumpProfile_subset_baseRegion M hy
  have hsmooth_to : ContMDiff (𝓡 4) (𝓡 4) ∞ toF := by
    intro x
    by_cases hx : x ∈ A.fibration.preimageOpen.1
    · have hcomp : toF ∘ (Subtype.val : A.fibration.preimageOpen → M) = Subtype.val ∘ ⇑Λ :=
        funext fun u ↦ dite_eq_left u.2
      refine ((TauCeti.isLocalDiffeomorph_subtype_val (I := 𝓡 4) (n := ∞)
        (⟨x, hx⟩ : A.fibration.preimageOpen)).contMDiffAt_comp_iff le_rfl).mp ?_
      rw [hcomp]
      exact (contMDiff_subtype_val.comp Λ.contMDiff) ⟨x, hx⟩
    · have hx_notK : x ∉ K := fun hy ↦ hx (hK_sub hy)
      refine contMDiffAt_id.congr_of_eventuallyEq ?_
      filter_upwards [hK_closed.isOpen_compl.mem_nhds hx_notK] with y hy
      have hρ0 : bumpProfile M (A.fibration y) = 0 := image_eq_zero_of_notMem_tsupport hy
      by_cases hy_pre : y ∈ A.fibration.preimageOpen.1
      · have hto : toF y = (Λ ⟨y, hy_pre⟩).1 := dite_eq_left hy_pre
        rw [hto, preimageBumpDiffeomorphOfIsotopy_eq_self_of_bump_zero M I_disk ⟨y, hy_pre⟩ hρ0]
        rfl
      · exact dite_eq_right hy_pre
  have hsmooth_inv : ContMDiff (𝓡 4) (𝓡 4) ∞ invF := by
    intro x
    by_cases hx : x ∈ A.fibration.preimageOpen.1
    · have hcomp : invF ∘ (Subtype.val : A.fibration.preimageOpen → M) = Subtype.val ∘ ⇑Λ.symm :=
        funext fun u ↦ dite_eq_left u.2
      refine ((TauCeti.isLocalDiffeomorph_subtype_val (I := 𝓡 4) (n := ∞)
        (⟨x, hx⟩ : A.fibration.preimageOpen)).contMDiffAt_comp_iff le_rfl).mp ?_
      rw [hcomp]
      exact (contMDiff_subtype_val.comp Λ.symm.contMDiff) ⟨x, hx⟩
    · have hx_notK : x ∉ K := fun hy ↦ hx (hK_sub hy)
      refine contMDiffAt_id.congr_of_eventuallyEq ?_
      filter_upwards [hK_closed.isOpen_compl.mem_nhds hx_notK] with y hy
      have hρ0 : bumpProfile M (A.fibration y) = 0 := image_eq_zero_of_notMem_tsupport hy
      by_cases hy_pre : y ∈ A.fibration.preimageOpen.1
      · have hinv : invF y = (Λ.symm ⟨y, hy_pre⟩).1 := dite_eq_left hy_pre
        rw [hinv, preimageBumpDiffeomorphOfIsotopy_symm_eq_self_of_bump_zero M I_disk
          ⟨y, hy_pre⟩ hρ0]
        rfl
      · exact dite_eq_right hy_pre
  exact
    { toFun := toF
      invFun := invF
      left_inv := hleft
      right_inv := hright
      contMDiff_toFun := hsmooth_to
      contMDiff_invFun := hsmooth_inv }

theorem leafwiseBumpDiffeomorphOfIsotopy_of_mem {r₀ : ℝ} (I_disk : AreaPreservingDiskIsotopy r₀)
    {x : M}
    (hx :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      x ∈ A.fibration.preimageOpen.1) :
    leafwiseBumpDiffeomorphOfIsotopy M I_disk x =
      (preimageBumpDiffeomorphOfIsotopy M I_disk ⟨x, hx⟩).1 := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := Classical.dec (x ∈ A.fibration.preimageOpen.1)
  change (if hx' : x ∈ A.fibration.preimageOpen.1 then
    (preimageBumpDiffeomorphOfIsotopy M I_disk ⟨x, hx'⟩).1 else x) = _
  exact dite_eq_left hx

theorem leafwiseBumpDiffeomorphOfIsotopy_of_notMem {r₀ : ℝ}
    (I_disk : AreaPreservingDiskIsotopy r₀) {x : M}
    (hx :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      x ∉ A.fibration.preimageOpen.1) :
    leafwiseBumpDiffeomorphOfIsotopy M I_disk x = x := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := Classical.dec (x ∈ A.fibration.preimageOpen.1)
  change (if hx' : x ∈ A.fibration.preimageOpen.1 then
    (preimageBumpDiffeomorphOfIsotopy M I_disk ⟨x, hx'⟩).1 else x) = x
  exact dite_eq_right hx

/-- `leafwiseBumpDiffeomorphOfIsotopy` equals `id` outside `tsupport (ρ ∘ f)`. -/
theorem leafwiseBumpDiffeomorphOfIsotopy_eq_self_of_notMem_tsupport {r₀ : ℝ}
    (I_disk : AreaPreservingDiskIsotopy r₀) {x : M}
    (hx :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      x ∉ tsupport (bumpProfile M ∘ A.fibration)) :
    leafwiseBumpDiffeomorphOfIsotopy M I_disk x = x := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  have hρ0 : bumpProfile M (A.fibration x) = 0 :=
    image_eq_zero_of_notMem_tsupport (f := bumpProfile M ∘ A.fibration) hx
  by_cases hx_pre : x ∈ A.fibration.preimageOpen.1
  · rw [leafwiseBumpDiffeomorphOfIsotopy_of_mem M I_disk hx_pre,
      preimageBumpDiffeomorphOfIsotopy_eq_self_of_bump_zero M I_disk ⟨x, hx_pre⟩ hρ0]
  · exact leafwiseBumpDiffeomorphOfIsotopy_of_notMem M I_disk hx_pre

/-- Action of `leafwiseBumpDiffeomorphOfIsotopy` on any regular fiber `A.fibration.embed (b, z)`
over `b : A.fibration.baseRegion`. -/
theorem leafwiseBumpDiffeomorphOfIsotopy_embed {r₀ : ℝ}
    (I_disk : AreaPreservingDiskIsotopy r₀)
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
    leafwiseBumpDiffeomorphOfIsotopy M I_disk (A.fibration.embed (b, z)) =
      A.fibration.embed
        (b, (AdmitsWrinkledOrBrokenLefschetzFibration.fiberDiskChart M).liftIsotopyDiffeomorph
          I_disk (bumpProfile M b.1) z) := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := A.instMeasurableSpaceFiber
  let _ := A.instBorelSpaceFiber
  let u := A.fibration.trivialization.symm (b, z)
  have hemb : A.fibration.embed (b, z) = u.1 := rfl
  rw [hemb, leafwiseBumpDiffeomorphOfIsotopy_of_mem M I_disk u.2]
  have hu_eq : (⟨u.1, u.2⟩ : A.fibration.preimageOpen) = u := rfl
  rw [hu_eq]
  change (A.fibration.trivialization.symm
      (trivBumpDiffeomorphOfIsotopy M I_disk (A.fibration.trivialization u))).1 = _
  rw [A.fibration.trivialization.apply_symm_apply]
  rfl

/-- **Foliation Preservation (`f ∘ d_bar = f`)**:
`leafwiseBumpDiffeomorphOfIsotopy` preserves every fiber of `A.fibration` across all of `M`. -/
@[simp]
theorem fibration_leafwiseBumpDiffeomorphOfIsotopy {r₀ : ℝ}
    (I_disk : AreaPreservingDiskIsotopy r₀) (x : M) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    A.fibration (leafwiseBumpDiffeomorphOfIsotopy M I_disk x) = A.fibration x := by
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
    let bz := A.fibration.trivialization u
    have hu_emb : x = A.fibration.embed (bz.1, bz.2) := by
      change u.1 = (A.fibration.trivialization.symm (bz.1, bz.2)).1
      rw [Prod.mk.eta, A.fibration.trivialization.symm_apply_apply]
    conv_lhs => rw [hu_emb]
    rw [leafwiseBumpDiffeomorphOfIsotopy_embed M I_disk bz.1 bz.2, A.fibration.apply_embed]
    exact congrArg Subtype.val (A.fibration.trivialization_fst u)
  · rw [leafwiseBumpDiffeomorphOfIsotopy_of_notMem M I_disk hx]

theorem fibration_comp_leafwiseBumpDiffeomorphOfIsotopy {r₀ : ℝ}
    (I_disk : AreaPreservingDiskIsotopy r₀) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    ⇑A.fibration ∘ ⇑(leafwiseBumpDiffeomorphOfIsotopy M I_disk) = ⇑A.fibration :=
  funext (fibration_leafwiseBumpDiffeomorphOfIsotopy M I_disk)

private theorem mpullback_congr_fun_four {E₁ H₁ M₁ E₂ H₂ M₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [IsManifold I₁ 1 M₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    [IsManifold I₂ 1 M₂] {f g : M₁ → M₂}
    (hf : ContMDiff I₁ I₂ ∞ f) (hg : ContMDiff I₁ I₂ ∞ g) (hfg : f = g)
    (α : TauCeti.SmoothForm I₂ M₂ ℝ 4) :
    TauCeti.SmoothForm.mpullback f hf α = TauCeti.SmoothForm.mpullback g hg α := by
  subst hfg
  rfl

private theorem mpullback_apply_congr_fun {E₁ H₁ M₁ E₂ H₂ M₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [IsManifold I₁ 1 M₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    [IsManifold I₂ 1 M₂] {f g : M₁ → M₂}
    (hf : ContMDiff I₁ I₂ ∞ f) (hfg : f = g)
    (α : TauCeti.SmoothForm I₂ M₂ ℝ 4) (p : M₁) (v : Fin 4 → TangentSpace I₁ p) :
    (show ℝ from (TauCeti.SmoothForm.mpullback f hf α).1 p v) =
      (show ℝ from α.1 (g p) (fun i ↦ mfderiv I₁ I₂ g p (v i))) := by
  subst hfg
  exact TauCeti.SmoothForm.mpullback_apply f hf α p v

private noncomputable def baseRegionAreaForm :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    TauCeti.SmoothForm (𝓡 2) A.fibration.baseRegion ℝ 2 := by
  letI := A.instTopologicalSpaceFiber
  letI := A.instChartedSpaceFiber
  letI := A.instIsManifoldFiber
  letI := A.instT2SpaceFiber
  letI := A.instCompactSpaceFiber
  letI := A.instNonemptyFiber
  exact TauCeti.SmoothForm.mpullback
    (Subtype.val : A.fibration.baseRegion → Sphere2) contMDiff_subtype_val S2VolumeForm

private noncomputable def swappedProductTargetForm :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    TauCeti.SmoothForm ((𝓡 2).prod (𝓡 2)) (A.fibration.baseRegion × A.Fiber) ℝ (2 + 2) := by
  letI := A.instTopologicalSpaceFiber
  letI := A.instChartedSpaceFiber
  letI := A.instIsManifoldFiber
  letI := A.instT2SpaceFiber
  letI := A.instCompactSpaceFiber
  letI := A.instNonemptyFiber
  letI := A.instMeasurableSpaceFiber
  letI := A.instBorelSpaceFiber
  exact TauCeti.SmoothForm.wedge
    (TauCeti.SmoothForm.mpullback Prod.fst contMDiff_fst (baseRegionAreaForm M))
    (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd A.fiberVolume.Ω)

private theorem productTargetForm_apply_eq_swapped
    (q :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      A.fibration.baseRegion × A.Fiber)
    (w :
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
    (show ℝ from (productTargetForm M).1 q w) =
      (show ℝ from (swappedProductTargetForm M).1 q w) := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := A.instMeasurableSpaceFiber
  let _ := A.instBorelSpaceFiber
  have hpull :
      TauCeti.SmoothForm.mpullback (I := (𝓡 2).prod (𝓡 2)) (I' := 𝓡 2)
          (Prod.fst : A.fibration.baseRegion × A.Fiber → A.fibration.baseRegion)
          contMDiff_fst (baseRegionAreaForm M) =
        TauCeti.SmoothForm.mpullback (Subtype.val ∘ Prod.fst)
          (contMDiff_subtype_val.comp contMDiff_fst) S2VolumeForm := by
    refine Subtype.ext (funext fun p ↦ ContinuousAlternatingMap.ext fun v ↦ ?_)
    change (TauCeti.SmoothForm.mpullback Prod.fst contMDiff_fst
        (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val S2VolumeForm)).1 p v = _
    rw [TauCeti.SmoothForm.mpullback_apply, TauCeti.SmoothForm.mpullback_apply,
      TauCeti.SmoothForm.mpullback_apply]
    congr 1
    funext i
    have hcomp := mfderiv_comp p
      ((contMDiff_subtype_val (I := 𝓡 2) (n := ∞)).mdifferentiableAt (by simp))
      (mdifferentiableAt_fst (I := 𝓡 2) (I' := 𝓡 2))
    exact (congrArg (· (v i)) hcomp).symm
  have hcomm := TauCeti.SmoothForm.wedge_comm_of_even (I := (𝓡 2).prod (𝓡 2))
    (M := A.fibration.baseRegion × A.Fiber) (k := 2) (by decide)
    (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd A.fiberVolume.Ω)
    (TauCeti.SmoothForm.mpullback (Subtype.val ∘ Prod.fst)
      (contMDiff_subtype_val.comp contMDiff_fst) S2VolumeForm)
  have heq : productTargetForm M = swappedProductTargetForm M :=
    hcomm.trans (congrArg
      (fun η ↦ TauCeti.SmoothForm.wedge η
        (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd A.fiberVolume.Ω))
      hpull.symm)
  exact DFunLike.congr_fun (congrFun (congrArg Subtype.val heq) q) w

private noncomputable def trivFiberMap {r₀ : ℝ}
    (I_disk : AreaPreservingDiskIsotopy r₀) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    A.fibration.baseRegion × A.Fiber → A.Fiber := by
  letI := A.instTopologicalSpaceFiber
  letI := A.instChartedSpaceFiber
  letI := A.instIsManifoldFiber
  letI := A.instT2SpaceFiber
  letI := A.instCompactSpaceFiber
  letI := A.instNonemptyFiber
  letI := A.instMeasurableSpaceFiber
  letI := A.instBorelSpaceFiber
  exact fun bz ↦
    (AdmitsWrinkledOrBrokenLefschetzFibration.fiberDiskChart M).liftThroughChart
      I_disk.d (bumpProfile M bz.1.1, bz.2)

private theorem contMDiff_trivFiberMap {r₀ : ℝ}
    (I_disk : AreaPreservingDiskIsotopy r₀) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    ContMDiff ((𝓡 2).prod (𝓡 2)) (𝓡 2) ∞ (trivFiberMap M I_disk) := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := A.instMeasurableSpaceFiber
  let _ := A.instBorelSpaceFiber
  exact ((AdmitsWrinkledOrBrokenLefschetzFibration.fiberDiskChart M).contMDiff_liftThroughChart
    I_disk.contDiff_d (fun s _ hw ↦ I_disk.mem_unitDisk2 s hw)
    I_disk.r₀_lt_one I_disk.eq_self_of_notMem_ball).comp
    (((contMDiff_bumpProfile M).comp (contMDiff_subtype_val.comp contMDiff_fst)).prodMk
      contMDiff_snd)

private theorem mpullback_trivFiberMap_slice {r₀ : ℝ}
    (I_disk : AreaPreservingDiskIsotopy r₀) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    letI := A.instMeasurableSpaceFiber
    letI := A.instBorelSpaceFiber
    ∀ b : A.fibration.baseRegion,
      TauCeti.SmoothForm.mpullback (fun y ↦ trivFiberMap M I_disk (b, y))
        ((contMDiff_trivFiberMap M I_disk).comp (contMDiff_const.prodMk contMDiff_id))
        A.fiberVolume.Ω = A.fiberVolume.Ω := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := A.instMeasurableSpaceFiber
  let _ := A.instBorelSpaceFiber
  intro b
  let C := AdmitsWrinkledOrBrokenLefschetzFibration.fiberDiskChart M
  have hfun :
      (fun y ↦ trivFiberMap M I_disk (b, y)) =
        ⇑(C.liftIsotopyDiffeomorph I_disk (bumpProfile M b.1)) := rfl
  exact (SymplecticDiskChart.mpullback_congr_fun_two_ext _
    (C.liftIsotopyDiffeomorph I_disk (bumpProfile M b.1)).contMDiff hfun A.fiberVolume.Ω).trans
    (C.mpullback_liftIsotopyDiffeomorph_eq I_disk (bumpProfile M b.1))

private theorem mpullback_swappedProductTargetForm_apply {r₀ : ℝ}
    (I_disk : AreaPreservingDiskIsotopy r₀)
    (p :
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
      Fin (2 + 2) → TangentSpace ((𝓡 2).prod (𝓡 2)) p) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    (show ℝ from (TauCeti.SmoothForm.mpullback
        (fun q : A.fibration.baseRegion × A.Fiber ↦ (q.1, trivFiberMap M I_disk q))
        (contMDiff_fst.prodMk (contMDiff_trivFiberMap M I_disk))
        (swappedProductTargetForm M)).1 p v) =
      (show ℝ from (swappedProductTargetForm M).1 p v) := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := A.instMeasurableSpaceFiber
  let _ := A.instBorelSpaceFiber
  have h := mpullback_fiberwise_wedge_two_two (baseRegionAreaForm M) A.fiberVolume.Ω
    (contMDiff_trivFiberMap M I_disk) (mpullback_trivFiberMap_slice M I_disk)
  exact DFunLike.congr_fun (congrFun (congrArg Subtype.val h) p) v

/-- Pullback preservation of `productTargetForm M` (`p_F^* ω_F ∧ p_B^* μ_B`) under
`trivBumpDiffeomorphOfIsotopy M I_disk`. -/
theorem mpullback_trivBumpDiffeomorphOfIsotopy_productTargetForm {r₀ : ℝ}
    (I_disk : AreaPreservingDiskIsotopy r₀) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    TauCeti.SmoothForm.mpullback (trivBumpDiffeomorphOfIsotopy M I_disk)
        (trivBumpDiffeomorphOfIsotopy M I_disk).contMDiff (productTargetForm M) =
      productTargetForm M := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := A.instMeasurableSpaceFiber
  let _ := A.instBorelSpaceFiber
  have htriv_coe :
      ⇑(trivBumpDiffeomorphOfIsotopy M I_disk) =
        fun q : A.fibration.baseRegion × A.Fiber ↦ (q.1, trivFiberMap M I_disk q) :=
    coe_trivBumpDiffeomorphOfIsotopy M I_disk
  refine Subtype.ext (funext fun p ↦ ContinuousAlternatingMap.ext fun v ↦ ?_)
  have h_lhs := mpullback_apply_congr_fun
    (trivBumpDiffeomorphOfIsotopy M I_disk).contMDiff htriv_coe (productTargetForm M) p v
  have h_p1 := productTargetForm_apply_eq_swapped M (p.1, trivFiberMap M I_disk p)
    (fun i ↦ mfderiv ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2))
      (fun q : A.fibration.baseRegion × A.Fiber ↦ (q.1, trivFiberMap M I_disk q)) p (v i))
  have h_w :
      (show ℝ from (swappedProductTargetForm M).1 (p.1, trivFiberMap M I_disk p)
        (fun i ↦ mfderiv ((𝓡 2).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2))
          (fun q : A.fibration.baseRegion × A.Fiber ↦ (q.1, trivFiberMap M I_disk q)) p (v i))) =
      (show ℝ from (TauCeti.SmoothForm.mpullback
        (fun q : A.fibration.baseRegion × A.Fiber ↦ (q.1, trivFiberMap M I_disk q))
        (contMDiff_fst.prodMk (contMDiff_trivFiberMap M I_disk))
        (swappedProductTargetForm M)).1 p v) :=
    (TauCeti.SmoothForm.mpullback_apply
      (fun q : A.fibration.baseRegion × A.Fiber ↦ (q.1, trivFiberMap M I_disk q))
      (contMDiff_fst.prodMk (contMDiff_trivFiberMap M I_disk))
      (swappedProductTargetForm M) p v).symm
  have h_3p := mpullback_swappedProductTargetForm_apply M I_disk p v
  have h_p2 := (productTargetForm_apply_eq_swapped M p v).symm
  exact h_lhs.trans (h_p1.trans (h_w.trans (h_3p.trans h_p2)))

/-- Pullback preservation of `trivializedProductForm M` (`Φ^* (p_F^* ω_F ∧ p_B^* μ_B)`) under
`preimageBumpDiffeomorphOfIsotopy M I_disk`. -/
theorem mpullback_preimageBumpDiffeomorphOfIsotopy_trivializedProductForm {r₀ : ℝ}
    (I_disk : AreaPreservingDiskIsotopy r₀) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    TauCeti.SmoothForm.mpullback (preimageBumpDiffeomorphOfIsotopy M I_disk)
        (preimageBumpDiffeomorphOfIsotopy M I_disk).contMDiff (trivializedProductForm M) =
      trivializedProductForm M := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  unfold preimageBumpDiffeomorphOfIsotopy trivializedProductForm
  rw [TauCeti.SmoothForm.mpullback_trans, TauCeti.SmoothForm.mpullback_trans,
    TauCeti.SmoothForm.mpullback_symm_mpullback,
    mpullback_trivBumpDiffeomorphOfIsotopy_productTargetForm M I_disk]

/-- **Global Volume-Form Preservation (`d_bar^* Ω = Ω`)**:
`leafwiseBumpDiffeomorphOfIsotopy M I_disk` preserves `alignedVolumeForm M` across **all** of
`M`. -/
theorem mpullback_leafwiseBumpDiffeomorphOfIsotopy_alignedVolumeForm {r₀ : ℝ}
    (I_disk : AreaPreservingDiskIsotopy r₀) :
    TauCeti.SmoothForm.mpullback (leafwiseBumpDiffeomorphOfIsotopy M I_disk)
        (leafwiseBumpDiffeomorphOfIsotopy M I_disk).contMDiff (alignedVolumeForm M) =
      alignedVolumeForm M := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let d_bar := leafwiseBumpDiffeomorphOfIsotopy M I_disk
  let Ω := alignedVolumeForm M
  let U_in := innerPreimageOpen M
  let j : U_in → A.fibration.preimageOpen := Opens.inclusion (innerPreimageOpen_le_preimageOpen M)
  have hj : ContMDiff (𝓡 4) (𝓡 4) ∞ j := contMDiff_inclusion _
  let d_in : U_in → U_in := fun u ↦
    ⟨d_bar u.1, by
      change A.fibration (d_bar u.1) ∈ (baseInnerOpen M).1
      rw [fibration_leafwiseBumpDiffeomorphOfIsotopy M I_disk u.1]
      exact u.2⟩
  have hd_in : ContMDiff (𝓡 4) (𝓡 4) ∞ d_in :=
    (TauCeti.ContMDiff.subtypeVal_comp_iff U_in d_in).mp
      (d_bar.contMDiff.comp contMDiff_subtype_val)
  have hcomm_M : (Subtype.val : U_in → M) ∘ d_in = ⇑d_bar ∘ Subtype.val := rfl
  have hcomm_pre : j ∘ d_in = ⇑(preimageBumpDiffeomorphOfIsotopy M I_disk) ∘ j :=
    funext fun u ↦ Subtype.ext
      (leafwiseBumpDiffeomorphOfIsotopy_of_mem M I_disk (innerPreimageOpen_le_preimageOpen M u.2))
  have hpull_in :
      TauCeti.SmoothForm.mpullback (Subtype.val : U_in → M) contMDiff_subtype_val
          (TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff Ω) =
        TauCeti.SmoothForm.mpullback (Subtype.val : U_in → M) contMDiff_subtype_val Ω := by
    calc
      TauCeti.SmoothForm.mpullback (Subtype.val : U_in → M) contMDiff_subtype_val
          (TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff Ω)
        = TauCeti.SmoothForm.mpullback (⇑d_bar ∘ (Subtype.val : U_in → M))
            (d_bar.contMDiff.comp contMDiff_subtype_val) Ω := by
          rw [TauCeti.SmoothForm.mpullback_mpullback]
      _ = TauCeti.SmoothForm.mpullback ((Subtype.val : U_in → M) ∘ d_in)
            (contMDiff_subtype_val.comp hd_in) Ω :=
          mpullback_congr_fun_four _ _ hcomm_M.symm Ω
      _ = TauCeti.SmoothForm.mpullback d_in hd_in
            (TauCeti.SmoothForm.mpullback (Subtype.val : U_in → M) contMDiff_subtype_val Ω) := by
          rw [← TauCeti.SmoothForm.mpullback_mpullback d_in (Subtype.val : U_in → M)
            hd_in contMDiff_subtype_val Ω]
      _ = TauCeti.SmoothForm.mpullback d_in hd_in
            (TauCeti.SmoothForm.mpullback j hj (trivializedProductForm M)) := by
          rw [mpullback_innerPreimageOpen_alignedVolumeForm M]
      _ = TauCeti.SmoothForm.mpullback (j ∘ d_in) (hj.comp hd_in) (trivializedProductForm M) := by
          rw [TauCeti.SmoothForm.mpullback_mpullback]
      _ = TauCeti.SmoothForm.mpullback (⇑(preimageBumpDiffeomorphOfIsotopy M I_disk) ∘ j)
            ((preimageBumpDiffeomorphOfIsotopy M I_disk).contMDiff.comp hj)
            (trivializedProductForm M) :=
          mpullback_congr_fun_four _ _ hcomm_pre (trivializedProductForm M)
      _ = TauCeti.SmoothForm.mpullback j hj
            (TauCeti.SmoothForm.mpullback (preimageBumpDiffeomorphOfIsotopy M I_disk)
              (preimageBumpDiffeomorphOfIsotopy M I_disk).contMDiff
              (trivializedProductForm M)) := by
          rw [← TauCeti.SmoothForm.mpullback_mpullback j
            (preimageBumpDiffeomorphOfIsotopy M I_disk) hj
            (preimageBumpDiffeomorphOfIsotopy M I_disk).contMDiff (trivializedProductForm M)]
      _ = TauCeti.SmoothForm.mpullback (Subtype.val : U_in → M) contMDiff_subtype_val Ω := by
          rw [mpullback_preimageBumpDiffeomorphOfIsotopy_trivializedProductForm M I_disk,
            mpullback_innerPreimageOpen_alignedVolumeForm M]
  let S : Set M := tsupport (bumpProfile M ∘ A.fibration)
  let V_ext : Opens M := ⟨Sᶜ, (isClosed_tsupport _).isOpen_compl⟩
  have hd_ext : ⇑d_bar ∘ (Subtype.val : V_ext → M) = Subtype.val :=
    funext fun w ↦ leafwiseBumpDiffeomorphOfIsotopy_eq_self_of_notMem_tsupport M I_disk w.2
  have hpull_ext :
      TauCeti.SmoothForm.mpullback (Subtype.val : V_ext → M) contMDiff_subtype_val
          (TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff Ω) =
        TauCeti.SmoothForm.mpullback (Subtype.val : V_ext → M) contMDiff_subtype_val Ω := by
    rw [TauCeti.SmoothForm.mpullback_mpullback]
    exact mpullback_congr_fun_four _ _ hd_ext Ω
  refine TauCeti.SmoothBundleForm.ext fun x v ↦ ?_
  by_cases hx_in : x ∈ U_in.1
  · let u : U_in := ⟨x, hx_in⟩
    have h1 := DFunLike.congr_fun (congrFun (congrArg Subtype.val hpull_in) u) v
    have hl := DFunLike.congr_fun
      (TauCeti.SmoothForm.coe_mpullback_subtype_val_apply
        (TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff Ω) u) v
    have hr := DFunLike.congr_fun (TauCeti.SmoothForm.coe_mpullback_subtype_val_apply Ω u) v
    exact hl.symm.trans (h1.trans hr)
  · have hx_notS : x ∉ S := fun hxS ↦
      hx_in (tsupport_bumpProfile_comp_fibration_subset_innerPreimageOpen M hxS)
    let w : V_ext := ⟨x, hx_notS⟩
    have h1 := DFunLike.congr_fun (congrFun (congrArg Subtype.val hpull_ext) w) v
    have hl := DFunLike.congr_fun
      (TauCeti.SmoothForm.coe_mpullback_subtype_val_apply
        (TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff Ω) w) v
    have hr := DFunLike.congr_fun (TauCeti.SmoothForm.coe_mpullback_subtype_val_apply Ω w) v
    exact hl.symm.trans (h1.trans hr)

end BumpLiftGeneral

/-! ## 4. Measure Preservation & Global Poisson Automorphism on Compact `M` -/

section CompactInvariance

variable (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [A : AdmitsWrinkledOrBrokenLefschetzFibration M]

/-- **Global Measure Preservation (`MeasurePreserving ⇑d_bar μ_Ω μ_Ω`)**:
On compact `M`, `leafwiseBumpDiffeomorphOfIsotopy M I_disk` preserves the induced positive finite
Borel volume measure `(alignedPositiveVolume M).μ`. -/
theorem measurePreserving_leafwiseBumpDiffeomorphOfIsotopy {r₀ : ℝ}
    (I_disk : AreaPreservingDiskIsotopy r₀) :
    MeasurePreserving ⇑(leafwiseBumpDiffeomorphOfIsotopy M I_disk)
      (alignedPositiveVolume M).μ (alignedPositiveVolume M).μ :=
  (alignedPositiveVolume M).measurePreserving_of_mpullback_eq
    (leafwiseBumpDiffeomorphOfIsotopy M I_disk)
    (mpullback_leafwiseBumpDiffeomorphOfIsotopy_alignedVolumeForm M I_disk)

/-- **Global Poisson Automorphism (`IsPoissonMap`)**:
Because `leafwiseBumpDiffeomorphOfIsotopy M I_disk` preserves both `A.fibration` and
`(alignedPositiveVolume M).Ω`, it preserves the Poisson bracket of `adaptedJacobianPoisson M`
globally across all of `M` (including `Crit(f)`). -/
theorem isPoissonMap_leafwiseBumpDiffeomorphOfIsotopy {r₀ : ℝ}
    (I_disk : AreaPreservingDiskIsotopy r₀) :
    SmoothBivector.IsPoissonMap
      (adaptedJacobianPoisson M).toSmoothBivector
      (adaptedJacobianPoisson M).toSmoothBivector
      (leafwiseBumpDiffeomorphOfIsotopy M I_disk)
      (leafwiseBumpDiffeomorphOfIsotopy M I_disk).contMDiff := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let Φ := leafwiseBumpDiffeomorphOfIsotopy M I_disk
  let ΦMap : C^∞⟮𝓡 4, M; 𝓡 4, M⟯ := ⟨Φ, Φ.contMDiff⟩
  let Ω := (alignedPositiveVolume M).Ω
  have hΩ : ∀ x : M, Ω.1 x ≠ 0 := (alignedPositiveVolume M).Ω_ne_zero
  have hΦ_Ω : TauCeti.SmoothForm.mpullback Φ Φ.contMDiff Ω = Ω :=
    mpullback_leafwiseBumpDiffeomorphOfIsotopy_alignedVolumeForm M I_disk
  have hdiff_pull (u : C^∞⟮𝓡 4, M; ℝ⟯) :
      TauCeti.SmoothForm.mpullback Φ Φ.contMDiff (SmoothBivector.diffOneForm u) =
        SmoothBivector.diffOneForm (u.comp ΦMap) := by
    refine TauCeti.SmoothBundleForm.ext fun x v ↦ ?_
    have hv : v = ![v 0] := funext fun i ↦ by fin_cases i; rfl
    rw [hv, TauCeti.SmoothForm.mpullback_apply_one, SmoothBivector.diffOneForm_apply,
      SmoothBivector.diffOneForm_apply]
    have hud : MDifferentiableAt (𝓡 4) 𝓘(ℝ) u (Φ x) := u.contMDiff.mdifferentiableAt (by simp)
    have hΦd : MDifferentiableAt (𝓡 4) (𝓡 4) Φ x := Φ.contMDiff.mdifferentiableAt (by simp)
    change mvfderiv (𝓡 4) u (Φ x) (mfderiv (𝓡 4) (𝓡 4) Φ x (v 0)) =
      mvfderiv (𝓡 4) (u ∘ Φ) x (v 0)
    rw [mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply]
    exact (congrArg (· (v 0)) (mfderiv_comp x hud hΦd)).symm
  have hbase_pull :
      TauCeti.SmoothForm.mpullback Φ Φ.contMDiff
          (TauCeti.SmoothForm.mpullback A.fibration A.fibration.contMDiff_toFun S2VolumeForm) =
        TauCeti.SmoothForm.mpullback A.fibration A.fibration.contMDiff_toFun S2VolumeForm := by
    rw [TauCeti.SmoothForm.mpullback_mpullback]
    have hcomp := fibration_comp_leafwiseBumpDiffeomorphOfIsotopy M I_disk
    exact SymplecticDiskChart.mpullback_congr_fun_two_ext _ _ hcomp S2VolumeForm
  intro g h
  ext x
  have h1 := funSMulₗ_bracket_jacobianPoisson Ω hΩ S2VolumeForm A.fibration
    A.fibration.contMDiff_toFun (g.comp ΦMap) (h.comp ΦMap)
  have h2 := congrArg (TauCeti.SmoothForm.mpullback Φ Φ.contMDiff)
    (funSMulₗ_bracket_jacobianPoisson Ω hΩ S2VolumeForm A.fibration
      A.fibration.contMDiff_toFun g h)
  have hw1 := TauCeti.SmoothForm.mpullback_wedge (k := 2) (l := 2) Φ Φ.contMDiff
    (TauCeti.SmoothForm.wedge (SmoothBivector.diffOneForm g) (SmoothBivector.diffOneForm h))
    (TauCeti.SmoothForm.mpullback A.fibration A.fibration.contMDiff_toFun S2VolumeForm)
  have hw2 := TauCeti.SmoothForm.mpullback_wedge (k := 1) (l := 1) Φ Φ.contMDiff
    (SmoothBivector.diffOneForm g) (SmoothBivector.diffOneForm h)
  rw [hw1, hw2, hdiff_pull g, hdiff_pull h, hbase_pull, ← h1] at h2
  have hlhs_x :
      (TauCeti.SmoothForm.mpullback Φ Φ.contMDiff
          (TauCeti.SmoothForm.funSMulₗ ((adaptedJacobianPoisson M).bracket g h) Ω)).1 x =
        ((adaptedJacobianPoisson M).bracket g h) (Φ x) • Ω.1 x := by
    ext v
    rw [TauCeti.SmoothForm.mpullback_apply, TauCeti.SmoothForm.coe_funSMulₗ,
      ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.smul_apply,
      ← TauCeti.SmoothForm.mpullback_apply Φ Φ.contMDiff Ω x v, hΦ_Ω]
  have hx_eq :
      ((adaptedJacobianPoisson M).bracket g h) (Φ x) • Ω.1 x =
        ((adaptedJacobianPoisson M).bracket (g.comp ΦMap) (h.comp ΦMap)) x • Ω.1 x := by
    calc
      ((adaptedJacobianPoisson M).bracket g h) (Φ x) • Ω.1 x
        = (TauCeti.SmoothForm.mpullback Φ Φ.contMDiff
            (TauCeti.SmoothForm.funSMulₗ ((adaptedJacobianPoisson M).bracket g h) Ω)).1 x :=
          hlhs_x.symm
      _ = (TauCeti.SmoothForm.funSMulₗ
            ((adaptedJacobianPoisson M).bracket (g.comp ΦMap) (h.comp ΦMap)) Ω).1 x :=
          congrFun (congrArg Subtype.val h2) x
      _ = ((adaptedJacobianPoisson M).bracket (g.comp ΦMap) (h.comp ΦMap)) x • Ω.1 x := by
          rw [TauCeti.SmoothForm.coe_funSMulₗ]
  exact (smul_left_injective ℝ (hΩ x) hx_eq).symm

end CompactInvariance

/-! ## 5. Specialization to `[HasTuringCompleteAreaPreservingDiskIsotopy]` & 4-Manifold Transfer -/

section TuringCompleteLift

set_option linter.concreteInstances false

variable (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [A : AdmitsWrinkledOrBrokenLefschetzFibration M]
  [H : HasTuringCompleteAreaPreservingDiskIsotopy]

/-- **Headline Leafwise Bump Diffeomorphism `d_bar : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M`** lifting
`[HasTuringCompleteAreaPreservingDiskIsotopy]` into `M`. -/
noncomputable def leafwiseBumpDiffeomorph : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ M :=
  leafwiseBumpDiffeomorphOfIsotopy M AreaPreservingDiskIsotopy.ofTypeclass

@[simp]
theorem fibration_leafwiseBumpDiffeomorph (x : M) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    A.fibration (leafwiseBumpDiffeomorph M x) = A.fibration x :=
  fibration_leafwiseBumpDiffeomorphOfIsotopy M AreaPreservingDiskIsotopy.ofTypeclass x

theorem fibration_comp_leafwiseBumpDiffeomorph :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    ⇑A.fibration ∘ ⇑(leafwiseBumpDiffeomorph M) = ⇑A.fibration :=
  fibration_comp_leafwiseBumpDiffeomorphOfIsotopy M AreaPreservingDiskIsotopy.ofTypeclass

theorem leafwiseBumpDiffeomorph_eq_self_of_notMem_tsupport {x : M}
    (hx :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      x ∉ tsupport (bumpProfile M ∘ A.fibration)) :
    leafwiseBumpDiffeomorph M x = x :=
  leafwiseBumpDiffeomorphOfIsotopy_eq_self_of_notMem_tsupport M
    AreaPreservingDiskIsotopy.ofTypeclass hx

/-- On every regular fiber over `b : A.fibration.baseRegion`, `leafwiseBumpDiffeomorph M` restricts
to `(fiberDiskChart M).liftSliceDiffeomorph (bumpProfile M b.1)`, which preserves
`A.fiberVolume.Ω`. -/
theorem leafwiseBumpDiffeomorph_embed
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
    leafwiseBumpDiffeomorph M (A.fibration.embed (b, z)) =
      A.fibration.embed
        (b, (AdmitsWrinkledOrBrokenLefschetzFibration.fiberDiskChart M).liftSliceDiffeomorph
          (bumpProfile M b.1) z) :=
  leafwiseBumpDiffeomorphOfIsotopy_embed M AreaPreservingDiskIsotopy.ofTypeclass b z

/-- Global volume-form invariance `(leafwiseBumpDiffeomorph M)^* alignedVolumeForm =
alignedVolumeForm`. -/
theorem mpullback_leafwiseBumpDiffeomorph_alignedVolumeForm :
    TauCeti.SmoothForm.mpullback (leafwiseBumpDiffeomorph M)
        (leafwiseBumpDiffeomorph M).contMDiff (alignedVolumeForm M) =
      alignedVolumeForm M :=
  mpullback_leafwiseBumpDiffeomorphOfIsotopy_alignedVolumeForm M
    AreaPreservingDiskIsotopy.ofTypeclass

/-- Global measure preservation on compact `M`. -/
theorem measurePreserving_leafwiseBumpDiffeomorph [CompactSpace M] :
    MeasurePreserving ⇑(leafwiseBumpDiffeomorph M)
      (alignedPositiveVolume M).μ (alignedPositiveVolume M).μ :=
  measurePreserving_leafwiseBumpDiffeomorphOfIsotopy M AreaPreservingDiskIsotopy.ofTypeclass

/-- Global Poisson automorphism (`IsPoissonMap`) of `leafwiseBumpDiffeomorph M` on compact `M`. -/
theorem isPoissonMap_leafwiseBumpDiffeomorph [CompactSpace M] :
    SmoothBivector.IsPoissonMap
      (adaptedJacobianPoisson M).toSmoothBivector
      (adaptedJacobianPoisson M).toSmoothBivector
      (leafwiseBumpDiffeomorph M)
      (leafwiseBumpDiffeomorph M).contMDiff :=
  isPoissonMap_leafwiseBumpDiffeomorphOfIsotopy M AreaPreservingDiskIsotopy.ofTypeclass

/-- Over the core open base disk `baseCoreOpen M` (`ρ ≡ 1`), `leafwiseBumpDiffeomorph M`
intertwines `baseDiskProductEmbed M` with `diskTimeOneMap`. -/
theorem leafwiseBumpDiffeomorph_baseDiskProductEmbed_of_mem_baseCoreOpen
    (b :
      letI := A.instTopologicalSpaceFiber
      letI := A.instChartedSpaceFiber
      letI := A.instIsManifoldFiber
      letI := A.instT2SpaceFiber
      letI := A.instCompactSpaceFiber
      letI := A.instNonemptyFiber
      A.fibration.baseRegion)
    (hb : b.1 ∈ (baseCoreOpen M).1) (y : diskOpen) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    leafwiseBumpDiffeomorph M (AdmitsWrinkledOrBrokenLefschetzFibration.baseDiskProductEmbed M
        (b, y)) =
      AdmitsWrinkledOrBrokenLefschetzFibration.baseDiskProductEmbed M
        (b, HasTuringCompleteAreaPreservingDiskIsotopy.diskTimeOneMap y) := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  let _ := A.instMeasurableSpaceFiber
  let _ := A.instBorelSpaceFiber
  let C := AdmitsWrinkledOrBrokenLefschetzFibration.fiberDiskChart M
  change leafwiseBumpDiffeomorph M (A.fibration.embed (b, C.embed y)) =
    A.fibration.embed (b, C.embed (HasTuringCompleteAreaPreservingDiskIsotopy.diskTimeOneMap y))
  rw [leafwiseBumpDiffeomorph_embed M b (C.embed y),
    bumpProfile_eq_one_of_mem_baseCoreOpen M hb, C.liftSliceDiffeomorph_embed 1 y]
  rfl

/-- **4-Manifold Turing Completeness (`S4TCdiffeo-Aug-2026.tex`, Theorem 1 & Corollary 2)**:
`leafwiseBumpDiffeomorph M` is Turing complete (`IsTuringComplete`) on `M`. -/
theorem isTuringComplete_leafwiseBumpDiffeomorph :
    IsTuringComplete ⇑(leafwiseBumpDiffeomorph M) := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  have hΨ : Topology.IsOpenEmbedding
      (AdmitsWrinkledOrBrokenLefschetzFibration.baseDiskProductEmbed M) :=
    (AdmitsWrinkledOrBrokenLefschetzFibration.isOpenEmbedding_baseDiskProductEmbed M).2.1
  let B₀_reg : Set A.fibration.baseRegion := Subtype.val ⁻¹' (baseCoreOpen M).1
  have hB₀_open : IsOpen B₀_reg := (baseCoreOpen M).2.preimage continuous_subtype_val
  have hc_mem : A.fibration.baseCenter ∈ B₀_reg := baseCenter_mem_baseCoreOpen M
  exact HasTuringCompleteAreaPreservingDiskIsotopy.isTuringComplete_diskTimeOneMap.transfer
    hΨ hB₀_open hc_mem fun b hb y ↦
      leafwiseBumpDiffeomorph_baseDiskProductEmbed_of_mem_baseCoreOpen M b hb y

/-- Anti-vacuity non-triviality: `⇑(leafwiseBumpDiffeomorph M) ≠ id`. -/
theorem leafwiseBumpDiffeomorph_ne_id :
    (⇑(leafwiseBumpDiffeomorph M) : M → M) ≠ id :=
  (isTuringComplete_leafwiseBumpDiffeomorph M).ne_id

/-- Algorithmic undecidability of forward-orbit reachability for `leafwiseBumpDiffeomorph M` on
`M`. -/
-- tier: T2
theorem undecidable_orbit_reachability_leafwiseBumpDiffeomorph :
    ∃ (U : Opens M) (Param : Type) (instTopParam : TopologicalSpace Param) (param₀ : Param)
      (openChart : Param × UnitDisk2 → M) (chart : UnitDisk2 → M)
      (coord : Nat.Partrec.Code → UnitDisk2)
      (approx : Nat.Partrec.Code × ℕ → RatFrac × RatFrac)
      (targetBoxes : ℕ → RatBox2),
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
      REPred (fun c : Nat.Partrec.Code ↦
        ∃ n : ℕ, (⇑(leafwiseBumpDiffeomorph M))^[n] (chart (coord c)) ∈ U) ∧
      ¬ ComputablePred (fun c : Nat.Partrec.Code ↦
          ∃ n : ℕ, (⇑(leafwiseBumpDiffeomorph M))^[n] (chart (coord c)) ∈ U) ∧
      ¬ ∃ dec : Nat.Partrec.Code → Bool,
          Computable dec ∧
          ∀ c : Nat.Partrec.Code,
            dec c = true ↔
              ∃ n : ℕ, (⇑(leafwiseBumpDiffeomorph M))^[n] (chart (coord c)) ∈ U :=
  (isTuringComplete_leafwiseBumpDiffeomorph M).undecidable_orbit_reachability

end TuringCompleteLift

end S4TuringPoisson
