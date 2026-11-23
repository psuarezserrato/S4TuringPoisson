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

public import S4TuringPoisson.Poisson.BivectorAndModular
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Assoc
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Jacobian–Poisson Structures and Global Unimodularity on Smooth 4-Manifolds (M1.2)

This module formalizes Milestone M1.2 of `S4TuringPoisson`, establishing the global Jacobian–Poisson
construction of García-Naranjo–Suárez-Serrato–Vera (`GSV15`, Theorem 2.6) and its global
unimodularity across singular loci (`BV21`; `S4TCdiffeo-Aug-2026.tex`, Eq. (1) & Proposition 1):

Given a smooth map `f : M → N` (`hf : ContMDiff I_M I_N ∞ f`) from a smooth `4`-manifold `M`
equipped with a nowhere-vanishing smooth `4`-form `Ω` (or `PositiveVolumeForm I_M M`) to a smooth
`2`-manifold `N` equipped with a smooth `2`-form `μ_N`:

1. **Sub-Top-Form Contraction Duality (`subTopDualVector`, `vectorFieldOfSubTopForm`)**:
   - On any `(m + 1)`-dimensional smooth manifold `M` with nowhere-vanishing volume form `Ω`, every
     smooth `m`-form `η ∈ Ωᵐ(M)` corresponds to a unique smooth vector field `X` satisfying
     `ι_X Ω = η`.

2. **Global Jacobian–Poisson Structure (`jacobianPoisson`, `jacobianPoissonOfPositiveVolume`)**:
   - Anchor `#_{π_f}` defined globally on `M` by `ι_{#_{π_f}(α)} Ω = -(α ∧ f^* μ_N)`, so that
     `ι_{X_h} Ω = dh ∧ f^* μ_N` and `{g, h}_{π_f} • Ω = dg ∧ dh ∧ f^* μ_N`
     (`S4TCdiffeo-Aug-2026.tex`, Equation (1)).
   - Smooth ℝ-bilinearity, skew-symmetry, Leibniz derivation, and the **Jacobi identity** proved
     coordinate-freely on **all** of `M` (including `Crit(f)`).
   - **Global Unimodularity**: `𝓛_{X_h} Ω = d(dh ∧ f^* μ_N) = 0` and `Y^Ω = 0` everywhere on `M`
     (including across `Crit(f)`), yielding `IsUnimodularWithVolume Ω` and `IsUnimodularPoisson`.
   - **Casimirs & Regular Symplectic Foliation**: pullbacks `u ∘ f` of all `u ∈ C^∞(N)` are Casimir
     functions; `Im(#_{π_f, x}) ≤ ker(mfderiv f x)` at every `x ∈ M`; and at regular points
     `x ∉ criticalSet f` where `μ_N (f x) ≠ 0`, `Im(#_{π_f, x}) = ker(mfderiv f x)` and
     `rankAt x = 2`.

3. **Euclidean Specialization `ℝ⁴ → ℝ²` (`euclideanJacobianPoisson`)**:
   - Canonical volume `4`-form `euclideanVolumeForm 4` (`dx₀ ∧ dx₁ ∧ dx₂ ∧ dx₃`) on
     `EuclideanSpace ℝ (Fin 4)` paired with `planeAreaForm` (`dy₀ ∧ dy₁`) on
     `EuclideanSpace ℝ (Fin 2)`.
   - Explicit determinant / Jacobian-minor formulas for `{g, h}_{π_f}` and coordinate brackets
     `{x_i, x_j}_{π_f}`, enabling direct verification of Gate 3 and Gate 4.
-/

@[expose] public section

noncomputable section

open Bundle Filter Function Module Set TauCeti TopologicalSpace
open scoped ContDiff Manifold Topology

namespace S4TuringPoisson

/-! ## 1. Wedge Evaluation Helpers in Degrees `1 ∧ 2` and `1 ∧ 3` -/

section WedgeEval

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- Explicit expansion of `(α ∧ ψ) ![u₀, u₁, u₂]` for a `1`-form `α` and `2`-form `ψ`. -/
theorem pairedWedge_one_two_apply (α : V [⋀^Fin 1]→L[ℝ] ℝ) (ψ : V [⋀^Fin 2]→L[ℝ] ℝ)
    (u₀ u₁ u₂ : V) :
    ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
        (ContinuousLinearMap.mul ℝ ℝ).continuous₂ α ψ ![u₀, u₁, u₂] =
      α ![u₀] * ψ ![u₁, u₂] - α ![u₁] * ψ ![u₀, u₂] + α ![u₂] * ψ ![u₀, u₁] := by
  have hcons : (![u₀, u₁, u₂] : Fin 3 → V) = Matrix.vecCons u₀ ![u₁, u₂] := rfl
  rw [hcons, ← ContinuousAlternatingMap.curryLeftTopological_apply_apply,
    ContinuousAlternatingMap.curryLeftTopological_pairedWedge (k := 0) (l := 1),
    ContinuousAlternatingMap.pairedWedge_apply_zero_left,
    ContinuousAlternatingMap.pairedWedge_apply_one_one]
  have hcast : ((![u₁, u₂] ∘ Fin.cast (show 0 + (1 + 1) = 0 + 1 + 1 by omega)) ∘
      Fin.cast (Nat.zero_add 2).symm : Fin 2 → V) = ![u₁, u₂] := by
    funext i; fin_cases i <;> rfl
  have hα0 : ContinuousAlternatingMap.curryLeftTopological α u₀ 0 = α ![u₀] := by
    rw [ContinuousAlternatingMap.curryLeftTopological_apply_apply]
    congr 1; funext i; fin_cases i; rfl
  have hψ1 : ContinuousAlternatingMap.curryLeftTopological ψ u₀ ![u₂] = ψ ![u₀, u₂] := by
    rw [ContinuousAlternatingMap.curryLeftTopological_apply_apply]
  have hψ2 : ContinuousAlternatingMap.curryLeftTopological ψ u₀ ![u₁] = ψ ![u₀, u₁] := by
    rw [ContinuousAlternatingMap.curryLeftTopological_apply_apply]
  rw [hcast, hα0, hψ1, hψ2]
  simp only [zero_add, pow_one, ContinuousLinearMap.mul_apply', neg_one_smul]
  ring

/-- Explicit expansion of `(α ∧ η) ![v₀, v₁, v₂, v₃]` for a `1`-form `α` and `3`-form `η`. -/
theorem pairedWedge_one_three_apply (α : V [⋀^Fin 1]→L[ℝ] ℝ) (η : V [⋀^Fin 3]→L[ℝ] ℝ)
    (v₀ v₁ v₂ v₃ : V) :
    ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
        (ContinuousLinearMap.mul ℝ ℝ).continuous₂ α η ![v₀, v₁, v₂, v₃] =
      α ![v₀] * η ![v₁, v₂, v₃] - α ![v₁] * η ![v₀, v₂, v₃] +
        α ![v₂] * η ![v₀, v₁, v₃] - α ![v₃] * η ![v₀, v₁, v₂] := by
  have hcons : (![v₀, v₁, v₂, v₃] : Fin 4 → V) = Matrix.vecCons v₀ ![v₁, v₂, v₃] := rfl
  rw [hcons, ← ContinuousAlternatingMap.curryLeftTopological_apply_apply,
    ContinuousAlternatingMap.curryLeftTopological_pairedWedge (k := 0) (l := 2),
    ContinuousAlternatingMap.pairedWedge_apply_zero_left]
  have hcast : ((![v₁, v₂, v₃] ∘ Fin.cast (show 0 + (2 + 1) = 0 + 1 + 2 by omega)) ∘
      Fin.cast (Nat.zero_add 3).symm : Fin 3 → V) = ![v₁, v₂, v₃] := by
    funext i; fin_cases i <;> rfl
  have hα0 : ContinuousAlternatingMap.curryLeftTopological α v₀ 0 = α ![v₀] := by
    rw [ContinuousAlternatingMap.curryLeftTopological_apply_apply]
    congr 1; funext i; fin_cases i; rfl
  rw [hcast, hα0, pairedWedge_one_two_apply]
  have hη1 : ContinuousAlternatingMap.curryLeftTopological η v₀ ![v₂, v₃] = η ![v₀, v₂, v₃] := by
    rw [ContinuousAlternatingMap.curryLeftTopological_apply_apply]
  have hη2 : ContinuousAlternatingMap.curryLeftTopological η v₀ ![v₁, v₃] = η ![v₀, v₁, v₃] := by
    rw [ContinuousAlternatingMap.curryLeftTopological_apply_apply]
  have hη3 : ContinuousAlternatingMap.curryLeftTopological η v₀ ![v₁, v₂] = η ![v₀, v₁, v₂] := by
    rw [ContinuousAlternatingMap.curryLeftTopological_apply_apply]
  rw [hη1, hη2, hη3]
  simp only [zero_add, pow_one, ContinuousLinearMap.mul_apply', neg_one_smul]
  ring

end WedgeEval

/-! ## 2. Sub-Top-Form Contraction Duality (`ι_X Ω = η`) -/

section SubTopDuality

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Evaluating an `(m + 1)`-alternating form on `vecCons (b i) (i₀.removeNth b)` yields
`(-1)^i₀ * vol b` when `i = i₀` and `0` otherwise. -/
theorem alternating_apply_vecCons_basis_removeNth {m : ℕ} (b : Module.Basis (Fin (m + 1)) ℝ V)
    (vol : V [⋀^Fin (m + 1)]→ₗ[ℝ] ℝ) (i i₀ : Fin (m + 1)) :
    vol (Matrix.vecCons (b i) (i₀.removeNth b)) =
      if i = i₀ then (-1 : ℝ) ^ (i₀ : ℕ) * vol b else 0 := by
  by_cases hi : i = i₀
  · subst hi
    rw [ite_eq_left rfl, ← vol.neg_one_pow_smul_map_insertNth i (b i) (i.removeNth b),
      Fin.insertNth_self_removeNth]
    simp
  · rw [ite_eq_right hi]
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hi
    exact vol.map_eq_zero_of_eq (Matrix.vecCons (b i) (i₀.removeNth b))
      (i := 0) (j := k.succ) (by simp [Fin.removeNth_apply, hk]) (Fin.succ_ne_zero k).symm

/-- Two `m`-alternating forms on an `(m + 1)`-dimensional space with basis `b` are equal whenever
they agree on all `(m + 1)` sub-tuples `i₀.removeNth b`. -/
theorem alternating_eq_of_forall_removeNth_eq {m : ℕ} (b : Module.Basis (Fin (m + 1)) ℝ V)
    {A B : V [⋀^Fin m]→ₗ[ℝ] ℝ}
    (h : ∀ i₀ : Fin (m + 1), A (i₀.removeNth b) = B (i₀.removeNth b)) :
    A = B := by
  refine b.ext_alternating fun s hs ↦ ?_
  have hcard : (Finset.univ.image s).card < (Finset.univ : Finset (Fin (m + 1))).card := by
    rw [Finset.card_image_of_injective _ hs, Finset.card_fin, Finset.card_fin]
    omega
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hs_ne (k : Fin m) : s k ≠ i₀ := fun heq ↦
    hi₀ (heq ▸ Finset.mem_image_of_mem s (Finset.mem_univ k))
  let g (k : Fin m) : Fin m := (Fin.exists_succAbove_eq (hs_ne k)).choose
  have hg (k : Fin m) : i₀.succAbove (g k) = s k :=
    (Fin.exists_succAbove_eq (hs_ne k)).choose_spec
  have hginj : Function.Injective g := fun k₁ k₂ hk ↦
    hs (by rw [← hg k₁, ← hg k₂, hk])
  let σ : Equiv.Perm (Fin m) := Equiv.ofBijective g (Finite.injective_iff_bijective.mp hginj)
  have hcomp : (fun k ↦ b (s k)) = (i₀.removeNth b) ∘ σ := by
    funext k
    simp [σ, Fin.removeNth_apply, hg k]
  rw [hcomp, A.map_perm, B.map_perm, h i₀]

/-- Explicit vector `u ∈ V` whose interior contraction with `vol` equals `η`. -/
def subTopDualVector {m : ℕ} [TopologicalSpace V] (b : Module.Basis (Fin (m + 1)) ℝ V)
    (vol : V [⋀^Fin (m + 1)]→L[ℝ] ℝ) (η : V [⋀^Fin m]→L[ℝ] ℝ) : V :=
  ∑ i : Fin (m + 1), ((-1 : ℝ) ^ (i : ℕ) * η (i.removeNth b) / vol b) • b i

theorem apply_vecCons_subTopDualVector {m : ℕ} [TopologicalSpace V]
    (b : Module.Basis (Fin (m + 1)) ℝ V) {vol : V [⋀^Fin (m + 1)]→L[ℝ] ℝ} (hvol : vol ≠ 0)
    (η : V [⋀^Fin m]→L[ℝ] ℝ) (w : Fin m → V) :
    vol (Matrix.vecCons (subTopDualVector b vol η) w) = η w := by
  have hvolb : vol b ≠ 0 := (vol.map_basis_ne_zero_iff b).mpr hvol
  suffices hA : vol.toAlternatingMap.curryLeft (subTopDualVector b vol η) = η.toAlternatingMap by
    exact DFunLike.congr_fun hA w
  refine alternating_eq_of_forall_removeNth_eq b fun i₀ ↦ ?_
  let evalAt : (V [⋀^Fin m]→ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun A ↦ A (i₀.removeNth b)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  change evalAt (vol.toAlternatingMap.curryLeft (subTopDualVector b vol η)) = η (i₀.removeNth b)
  rw [subTopDualVector, map_sum, map_sum]
  have hterm (i : Fin (m + 1)) :
      evalAt (vol.toAlternatingMap.curryLeft
        (((-1 : ℝ) ^ (i : ℕ) * η (i.removeNth b) / vol b) • b i)) =
        if i = i₀ then η (i₀.removeNth b) else 0 := by
    rw [map_smul, map_smul]
    change ((-1 : ℝ) ^ (i : ℕ) * η (i.removeNth b) / vol b) •
      vol.toAlternatingMap (Matrix.vecCons (b i) (i₀.removeNth b)) = _
    rw [alternating_apply_vecCons_basis_removeNth b vol.toAlternatingMap i i₀]
    split_ifs with hi
    · subst hi
      rw [ContinuousAlternatingMap.coe_toAlternatingMap, smul_eq_mul]
      have hpow : (-1 : ℝ) ^ (i : ℕ) * (-1 : ℝ) ^ (i : ℕ) = 1 := by
        rw [← mul_pow]
        norm_num
      calc
        (-1 : ℝ) ^ (i : ℕ) * η (i.removeNth b) / vol b * ((-1 : ℝ) ^ (i : ℕ) * vol b)
            = ((-1 : ℝ) ^ (i : ℕ) * (-1 : ℝ) ^ (i : ℕ)) * η (i.removeNth b) *
                (vol b / vol b) := by
              ring
        _ = η (i.removeNth b) := by rw [hpow, div_self hvolb, one_mul, mul_one]
    · simp
  rw [Finset.sum_congr rfl fun i _ ↦ hterm i]
  simp

theorem eq_subTopDualVector_of_forall_vecCons {m : ℕ} [TopologicalSpace V]
    (b : Module.Basis (Fin (m + 1)) ℝ V) {vol : V [⋀^Fin (m + 1)]→L[ℝ] ℝ} (hvol : vol ≠ 0)
    (η : V [⋀^Fin m]→L[ℝ] ℝ) {u : V}
    (hu : ∀ w : Fin m → V, vol (Matrix.vecCons u w) = η w) :
    u = subTopDualVector b vol η := by
  have hvolb : vol b ≠ 0 := (vol.map_basis_ne_zero_iff b).mpr hvol
  suffices hzero : u - subTopDualVector b vol η = 0 from sub_eq_zero.mp hzero
  let z := u - subTopDualVector b vol η
  have hz_eval (i₀ : Fin (m + 1)) : vol (Matrix.vecCons z (i₀.removeNth b)) = 0 := by
    have hexp : z = u + (-1 : ℝ) • subTopDualVector b vol η := by
      simp [z, sub_eq_add_neg]
    rw [hexp, map_vecCons_add_slot0, map_vecCons_smul_slot0, hu,
      apply_vecCons_subTopDualVector b hvol η]
    simp
  refine b.ext_elem fun i₀ ↦ ?_
  rw [map_zero, Finsupp.zero_apply]
  let evalAt : (V [⋀^Fin m]→ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun A ↦ A (i₀.removeNth b)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hrepr : z = ∑ i : Fin (m + 1), b.repr z i • b i := (b.sum_repr z).symm
  have hval : evalAt (vol.toAlternatingMap.curryLeft z) = 0 := hz_eval i₀
  rw [hrepr, map_sum, map_sum] at hval
  have hterm (i : Fin (m + 1)) :
      evalAt (vol.toAlternatingMap.curryLeft (b.repr z i • b i)) =
        if i = i₀ then b.repr z i₀ * ((-1 : ℝ) ^ (i₀ : ℕ) * vol b) else 0 := by
    rw [map_smul, map_smul]
    change b.repr z i • vol.toAlternatingMap (Matrix.vecCons (b i) (i₀.removeNth b)) = _
    rw [alternating_apply_vecCons_basis_removeNth, ContinuousAlternatingMap.coe_toAlternatingMap,
      smul_eq_mul]
    split_ifs with hi
    · subst hi; rfl
    · ring
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hval
  have hne : (-1 : ℝ) ^ (i₀ : ℕ) * vol b ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hvolb
  exact (mul_eq_zero.mp hval).resolve_right hne

end SubTopDuality

section SmoothSubTopDuality

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Smooth vector field `X` uniquely determined by `ι_X Ω = η` for a nowhere-vanishing smooth
`(m + 1)`-form `Ω` and any smooth `m`-form `η` on an `(m + 1)`-manifold `M`. -/
def vectorFieldOfSubTopForm {m : ℕ} [hdim : HasFinrank E (m + 1)] [FiniteDimensional ℝ E]
    (Ω : SmoothForm I M ℝ (m + 1)) (η : SmoothForm I M ℝ m) (x : M) : TangentSpace I x :=
  subTopDualVector
    ((trivializationAt E (TangentSpace I) x).basisAt
      (Module.finBasisOfFinrankEq ℝ E hdim.finrank_eq)
      (FiberBundle.mem_baseSet_trivializationAt' x))
    (Ω.1 x) (η.1 x)

@[simp]
theorem interior_vectorFieldOfSubTopForm {m : ℕ} [HasFinrank E (m + 1)] [FiniteDimensional ℝ E]
    (Ω : SmoothForm I M ℝ (m + 1)) (hΩ : ∀ x : M, Ω.1 x ≠ 0) (η : SmoothForm I M ℝ m) :
    RoughForm.interior (vectorFieldOfSubTopForm Ω η) Ω.1 = η.1 := by
  funext x
  ext w
  rw [RoughForm.interior_apply]
  exact apply_vecCons_subTopDualVector _ (hΩ x) (η.1 x) w

theorem eq_vectorFieldOfSubTopForm_iff {m : ℕ} [HasFinrank E (m + 1)] [FiniteDimensional ℝ E]
    (Ω : SmoothForm I M ℝ (m + 1)) (hΩ : ∀ x : M, Ω.1 x ≠ 0) (η : SmoothForm I M ℝ m)
    (V : (x : M) → TangentSpace I x) :
    V = vectorFieldOfSubTopForm Ω η ↔ RoughForm.interior V Ω.1 = η.1 := by
  constructor
  · rintro rfl
    exact interior_vectorFieldOfSubTopForm Ω hΩ η
  · intro h
    funext x
    refine eq_subTopDualVector_of_forall_vecCons _ (hΩ x) (η.1 x) fun w ↦ ?_
    simpa [RoughForm.interior_apply] using DFunLike.congr_fun (congrFun h x) w

theorem contMDiff_vectorFieldOfSubTopForm {m : ℕ} [hdim : HasFinrank E (m + 1)]
    [FiniteDimensional ℝ E] (Ω : SmoothForm I M ℝ (m + 1)) (hΩ : ∀ x : M, Ω.1 x ≠ 0)
    (η : SmoothForm I M ℝ m) :
    ContMDiff I I.tangent ∞
      (fun x ↦ (⟨x, vectorFieldOfSubTopForm Ω η x⟩ : TangentBundle I M)) := by
  intro x₀
  let bE : Module.Basis (Fin (m + 1)) ℝ E := Module.finBasisOfFinrankEq ℝ E hdim.finrank_eq
  let e := trivializationAt E (TangentSpace I) x₀
  let frame (y : M) : Fin (m + 1) → TangentSpace I y := fun i ↦ e.symmL ℝ y (bE i)
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  have hΩ_ne : Ω.1 x₀ (frame x₀) ≠ 0 := by
    have hfr : frame x₀ = ⇑(e.basisAt bE hx₀) :=
      funext fun i ↦ (TauCeti.Manifold.basisAt_apply bE hx₀ i).symm
    rw [hfr]
    exact ((Ω.1 x₀).map_basis_ne_zero_iff _).mpr (hΩ x₀)
  have hΩ_smooth : ContMDiffAt I 𝓘(ℝ) ∞ (fun y ↦ Ω.1 y (frame y)) x₀ :=
    (isSmoothForm_iff_forall_contMDiffAt_trivializationAt_apply.mp Ω.isSmoothForm) x₀ bE
  have hη_smooth (i : Fin (m + 1)) :
      ContMDiffAt I 𝓘(ℝ) ∞ (fun y ↦ η.1 y (i.removeNth (frame y))) x₀ := by
    have heq : (fun y ↦ η.1 y (i.removeNth (frame y))) =
        (fun y ↦ η.1 y (e.symmL ℝ y ∘ i.removeNth bE)) := by
      funext y; congr 1
    rw [heq]
    exact (isSmoothForm_iff_forall_contMDiffAt_trivializationAt_apply.mp η.isSmoothForm)
      x₀ (i.removeNth bE)
  have hcoeff (i : Fin (m + 1)) :
      ContMDiffAt I 𝓘(ℝ) ∞
        (fun y ↦ (-1 : ℝ) ^ (i : ℕ) * η.1 y (i.removeNth (frame y)) / Ω.1 y (frame y)) x₀ :=
    (contMDiffAt_const.mul (hη_smooth i)).div₀ hΩ_smooth hΩ_ne
  have hsec (i : Fin (m + 1)) :
      ContMDiffAt I I.tangent ∞ (fun y ↦ (⟨y, e.symm y (bE i)⟩ : TangentBundle I M)) x₀ :=
    (TauCeti.Manifold.contMDiffOn_symm_baseSet (e := e) (n := ∞) (bE i)).contMDiffAt
      (e.open_baseSet.mem_nhds hx₀)
  have hsum : ContMDiffAt I I.tangent ∞
      (fun y ↦ (⟨y, ∑ i : Fin (m + 1),
        ((-1 : ℝ) ^ (i : ℕ) * η.1 y (i.removeNth (frame y)) / Ω.1 y (frame y)) •
          e.symm y (bE i)⟩ : TangentBundle I M)) x₀ :=
    ContMDiffAt.sum_section (s := Finset.univ)
      fun i (_ : i ∈ Finset.univ) ↦ (hcoeff i).smul_section (hsec i)
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds hx₀] with y hy
  congr 1
  have hby : frame y = ⇑(e.basisAt bE hy) :=
    funext fun i ↦ (TauCeti.Manifold.basisAt_apply bE hy i).symm
  have hsymm (i : Fin (m + 1)) : e.symm y (bE i) = e.basisAt bE hy i := by
    rw [TauCeti.Manifold.basisAt_apply bE hy i, e.symmL_apply hy]
  have heq_dual : vectorFieldOfSubTopForm Ω η y =
      subTopDualVector (e.basisAt bE hy) (Ω.1 y) (η.1 y) := by
    refine eq_subTopDualVector_of_forall_vecCons (e.basisAt bE hy) (hΩ y) (η.1 y) fun w ↦ ?_
    simpa [RoughForm.interior_apply] using
      DFunLike.congr_fun (congrFun (interior_vectorFieldOfSubTopForm Ω hΩ η) y) w
  rw [heq_dual]
  simp only [subTopDualVector, hby, hsymm]

end SmoothSubTopDuality

/-! ## 3. Global Jacobian–Poisson Structure on 4-Manifolds (`GSV15` Thm 2.6, `BV21`) -/

section JacobianGeneral

variable {E_M H_M M : Type*} [NormedAddCommGroup E_M] [NormedSpace ℝ E_M]
  [TopologicalSpace H_M] {I_M : ModelWithCorners ℝ E_M H_M}
  [TopologicalSpace M] [ChartedSpace H_M M] [IsManifold I_M ∞ M]
  [hdim_M : HasFinrank E_M 4] [FiniteDimensional ℝ E_M]
  {E_N H_N N : Type*} [NormedAddCommGroup E_N] [NormedSpace ℝ E_N]
  [TopologicalSpace H_N] {I_N : ModelWithCorners ℝ E_N H_N}
  [TopologicalSpace N] [ChartedSpace H_N N] [IsManifold I_N ∞ N]
  [hdim_N : HasFinrank E_N 2] [FiniteDimensional ℝ E_N]

/-- Critical set `Crit(f) = {x ∈ M | ¬ Surjective (mfderiv f x)}` of a map `f : M → N`. -/
def criticalSet (I_M : ModelWithCorners ℝ E_M H_M) (I_N : ModelWithCorners ℝ E_N H_N)
    (f : M → N) : Set M :=
  {x : M | ¬ Function.Surjective (mfderiv I_M I_N f x)}

omit [IsManifold I_M ∞ M] hdim_M [FiniteDimensional ℝ E_M]
  [IsManifold I_N ∞ N] hdim_N [FiniteDimensional ℝ E_N] in
@[simp]
theorem mem_criticalSet_iff (f : M → N) (x : M) :
    x ∈ criticalSet I_M I_N f ↔ ¬ Function.Surjective (mfderiv I_M I_N f x) :=
  Iff.rfl

omit hdim_M [FiniteDimensional ℝ E_M] in
/-- Pullback `f^* μ_N` of any smooth `2`-form `μ_N` on a `2`-manifold `N` is globally closed
on `M`. -/
theorem isClosed_mpullback_surfaceForm (μ_N : SmoothForm I_N N ℝ 2) (f : M → N)
    (hf : ContMDiff I_M I_N ∞ f) :
    (SmoothForm.mpullback f hf μ_N).IsClosed :=
  (SmoothForm.isClosed_of_finrank_le hdim_N.finrank_eq.le μ_N).mpullback f hf

omit hdim_M [FiniteDimensional ℝ E_M] in
/-- For every smooth function `h ∈ C^∞(M)`, the `3`-form `dh ∧ f^* μ_N` is globally closed
on `M`. -/
theorem isClosed_diffOneForm_wedge_mpullback (μ_N : SmoothForm I_N N ℝ 2) (f : M → N)
    (hf : ContMDiff I_M I_N ∞ f) (h : C^∞⟮I_M, M; ℝ⟯) :
    (SmoothForm.wedge (SmoothBivector.diffOneForm h) (SmoothForm.mpullback f hf μ_N)).IsClosed := by
  rw [SmoothForm.isClosed_def]
  funext x
  ext v
  rw [SmoothForm.coe_wedge, SmoothForm.mextDeriv_wedge_apply,
    (SmoothForm.isClosed_def _).mp (SmoothBivector.isClosed_diffOneForm h),
    (SmoothForm.isClosed_def _).mp (isClosed_mpullback_surfaceForm μ_N f hf),
    RoughForm.wedge_zero_left, RoughForm.wedge_zero_right]
  simp

/-- Pointwise continuous linear anchor `#_{π_f, x} : T_x^* M →L[ℝ] T_x M` characterized by
`ι_{#_{π_f, x}(α)} Ω_x = -(α ∧ (f^* μ_N)_x)`. -/
def jacobianAnchor (Ω : SmoothForm I_M M ℝ 4) (μ_N : SmoothForm I_N N ℝ 2)
    (f : M → N) (hf : ContMDiff I_M I_N ∞ f) (x : M) :
    (TangentSpace I_M x →L[ℝ] ℝ) →L[ℝ] TangentSpace I_M x := by
  let b : Module.Basis (Fin 4) ℝ (TangentSpace I_M x) :=
    (trivializationAt E_M (TangentSpace I_M) x).basisAt
      (Module.finBasisOfFinrankEq ℝ E_M hdim_M.finrank_eq)
      (FiberBundle.mem_baseSet_trivializationAt' x)
  let ψ : TangentSpace I_M x [⋀^Fin 2]→L[ℝ] ℝ := (SmoothForm.mpullback f hf μ_N).1 x
  let evalAt (v : TangentSpace I_M x) : (TangentSpace I_M x →L[ℝ] ℝ) →L[ℝ] ℝ :=
    { toFun := fun α ↦ α v
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      cont := continuous_eval_const v }
  let wedge3 (w : Fin 3 → TangentSpace I_M x) : (TangentSpace I_M x →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ψ ![w 1, w 2] • evalAt (w 0) - ψ ![w 0, w 2] • evalAt (w 1) + ψ ![w 0, w 1] • evalAt (w 2)
  exact ∑ i : Fin 4,
    ((-(-1 : ℝ) ^ (i : ℕ) / Ω.1 x b) • (wedge3 (i.removeNth b)).smulRight (b i))

omit hdim_N [FiniteDimensional ℝ E_N] in
theorem jacobianAnchor_eq_subTopDualVector (Ω : SmoothForm I_M M ℝ 4)
    (μ_N : SmoothForm I_N N ℝ 2) (f : M → N) (hf : ContMDiff I_M I_N ∞ f)
    (x : M) (α : TangentSpace I_M x →L[ℝ] ℝ) :
    jacobianAnchor Ω μ_N f hf x α =
      subTopDualVector
        ((trivializationAt E_M (TangentSpace I_M) x).basisAt
          (Module.finBasisOfFinrankEq ℝ E_M hdim_M.finrank_eq)
          (FiberBundle.mem_baseSet_trivializationAt' x))
        (Ω.1 x)
        (-ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
          (ContinuousLinearMap.mul ℝ ℝ).continuous₂
          (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1) α)
          ((SmoothForm.mpullback f hf μ_N).1 x)) := by
  have hwedge (w : Fin 3 → TangentSpace I_M x) :
      ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
        (ContinuousLinearMap.mul ℝ ℝ).continuous₂
        (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1) α)
        ((SmoothForm.mpullback f hf μ_N).1 x) w =
      (SmoothForm.mpullback f hf μ_N).1 x ![w 1, w 2] * α (w 0) -
        (SmoothForm.mpullback f hf μ_N).1 x ![w 0, w 2] * α (w 1) +
        (SmoothForm.mpullback f hf μ_N).1 x ![w 0, w 1] * α (w 2) := by
    have hw : w = ![w 0, w 1, w 2] := by funext j; fin_cases j <;> rfl
    conv_lhs => rw [hw]
    rw [pairedWedge_one_two_apply]
    simp only [ContinuousAlternatingMap.ofSubsingleton_apply_apply, Matrix.cons_val_zero]
    ring
  simp only [jacobianAnchor, subTopDualVector, FunLike.coe_sum, Finset.sum_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousAlternatingMap.neg_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hwedge, smul_smul]
  congr 1
  simp only [sub_apply, add_apply, smul_apply, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk, smul_eq_mul]
  ring

omit hdim_N [FiniteDimensional ℝ E_N] in
theorem apply_vecCons_jacobianAnchor (Ω : SmoothForm I_M M ℝ 4) (hΩ : ∀ x : M, Ω.1 x ≠ 0)
    (μ_N : SmoothForm I_N N ℝ 2) (f : M → N) (hf : ContMDiff I_M I_N ∞ f)
    (x : M) (α : TangentSpace I_M x →L[ℝ] ℝ) (w : Fin 3 → TangentSpace I_M x) :
    Ω.1 x (Matrix.vecCons (jacobianAnchor Ω μ_N f hf x α) w) =
      -ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
        (ContinuousLinearMap.mul ℝ ℝ).continuous₂
        (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1) α)
        ((SmoothForm.mpullback f hf μ_N).1 x) w := by
  rw [jacobianAnchor_eq_subTopDualVector]
  exact apply_vecCons_subTopDualVector _ (hΩ x) _ w

omit hdim_N [FiniteDimensional ℝ E_N] in
/-- Fundamental covector-wedge identity for `jacobianAnchor`:
`β (#_{π_f, x} α) • Ω_x = α ∧ β ∧ (f^* μ_N)_x`. -/
theorem smul_topForm_jacobianAnchor (Ω : SmoothForm I_M M ℝ 4) (hΩ : ∀ x : M, Ω.1 x ≠ 0)
    (μ_N : SmoothForm I_N N ℝ 2) (f : M → N) (hf : ContMDiff I_M I_N ∞ f)
    (x : M) (α β : TangentSpace I_M x →L[ℝ] ℝ) (v : Fin 4 → TangentSpace I_M x) :
    β (jacobianAnchor Ω μ_N f hf x α) * Ω.1 x v =
      ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
        (ContinuousLinearMap.mul ℝ ℝ).continuous₂
        (ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
          (ContinuousLinearMap.mul ℝ ℝ).continuous₂
          (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1) α)
          (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1) β))
        ((SmoothForm.mpullback f hf μ_N).1 x) v := by
  classical
  let αR : RoughForm I_M M ℝ 1 := fun y ↦
    if hy : y = x then
      hy ▸ ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1) α
    else 0
  let βR : RoughForm I_M M ℝ 1 := fun y ↦
    if hy : y = x then
      hy ▸ ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1) β
    else 0
  let VR : (y : M) → TangentSpace I_M y := fun y ↦
    if hy : y = x then hy ▸ jacobianAnchor Ω μ_N f hf x α else 0
  have hαx : αR x =
      ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1) α := by
    simp only [αR, ↓reduceDIte]
  have hβx : βR x =
      ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1) β := by
    simp only [βR, ↓reduceDIte]
  have hVx : VR x = jacobianAnchor Ω μ_N f hf x α := by
    simp only [VR, ↓reduceDIte]
  have h1 := apply_smul_topForm_eq_wedge_interior (m := 3) VR βR Ω.1 x v
  have hβeval : βR x ![VR x] = β (jacobianAnchor Ω μ_N f hf x α) := by
    rw [hβx, hVx, ContinuousAlternatingMap.ofSubsingleton_apply_apply, Matrix.cons_val_zero]
  have hιx : RoughForm.interior VR Ω.1 x = -(αR.wedge (SmoothForm.mpullback f hf μ_N).1) x := by
    ext w
    rw [RoughForm.interior_apply, hVx, apply_vecCons_jacobianAnchor Ω hΩ μ_N f hf x α w,
      RoughForm.wedge_def, RoughForm.wedgeWith_apply', hαx,
      ContinuousAlternatingMap.neg_apply]
  have hcast4 : ∀ h : 4 = 4, (v ∘ Fin.cast h : Fin 4 → TangentSpace I_M x) = v :=
    fun _ ↦ funext fun _ ↦ rfl
  rw [hβeval] at h1
  rw [h1, hcast4, RoughForm.wedge_def, RoughForm.wedgeWith_apply', hιx, hβx]
  have hneg : ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
      (ContinuousLinearMap.mul ℝ ℝ).continuous₂
      (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1) β)
      (-(αR.wedge (SmoothForm.mpullback f hf μ_N).1) x) v =
      -ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
        (ContinuousLinearMap.mul ℝ ℝ).continuous₂
        (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1) β)
        ((αR.wedge (SmoothForm.mpullback f hf μ_N).1) x) v := by
    simpa using DFunLike.congr_fun
      (ContinuousAlternatingMap.pairedWedge_smul_right (ContinuousLinearMap.mul ℝ ℝ)
        (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (-1 : ℝ)
        (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1) β)
        ((αR.wedge (SmoothForm.mpullback f hf μ_N).1) x)) v
  rw [hneg]
  have hassoc := RoughForm.wedgeWith_assoc (I := I_M)
    (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
    (fun a b c ↦ mul_assoc a b c) βR αR (SmoothForm.mpullback f hf μ_N).1 x v
  rw [hcast4] at hassoc
  rw [← hβx, RoughForm.wedge_def, ← RoughForm.wedgeWith_apply', ← hassoc]
  have hcomm : (βR.wedgeWith (ContinuousLinearMap.mul ℝ ℝ) αR) x =
      -(αR.wedgeWith (ContinuousLinearMap.mul ℝ ℝ) βR) x := by
    ext u
    have hc := RoughForm.wedgeWith_comm (ContinuousLinearMap.mul ℝ ℝ)
      (fun a b ↦ mul_comm a b) βR αR x u
    have hcu : (u ∘ Fin.cast (Nat.add_comm 1 1)) = u := funext fun _ ↦ rfl
    rw [hcu] at hc
    simpa using hc
  have hleft : (βR.wedgeWith (ContinuousLinearMap.mul ℝ ℝ) αR).wedgeWith
      (ContinuousLinearMap.mul ℝ ℝ) (SmoothForm.mpullback f hf μ_N).1 x v =
      -((αR.wedgeWith (ContinuousLinearMap.mul ℝ ℝ) βR).wedgeWith
        (ContinuousLinearMap.mul ℝ ℝ) (SmoothForm.mpullback f hf μ_N).1 x v) := by
    rw [RoughForm.wedgeWith_apply', hcomm]
    conv_rhs => rw [RoughForm.wedgeWith_apply']
    simpa using DFunLike.congr_fun
      (ContinuousAlternatingMap.pairedWedge_smul_left (ContinuousLinearMap.mul ℝ ℝ)
        (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (-1 : ℝ)
        ((αR.wedgeWith (ContinuousLinearMap.mul ℝ ℝ) βR) x)
        ((SmoothForm.mpullback f hf μ_N).1 x)) v
  rw [hleft, neg_neg, RoughForm.wedgeWith_apply', RoughForm.wedgeWith_apply', hαx, hβx]

/-- Smooth bivector underlying the Jacobian–Poisson structure `π_f`. -/
def jacobianSmoothBivector (Ω : SmoothForm I_M M ℝ 4) (hΩ : ∀ x : M, Ω.1 x ≠ 0)
    (μ_N : SmoothForm I_N N ℝ 2) (f : M → N) (hf : ContMDiff I_M I_N ∞ f) :
    SmoothBivector I_M M where
  anchor := jacobianAnchor Ω μ_N f hf
  anchor_skew x α β := by
    let b : Module.Basis (Fin 4) ℝ (TangentSpace I_M x) :=
      (trivializationAt E_M (TangentSpace I_M) x).basisAt
        (Module.finBasisOfFinrankEq ℝ E_M hdim_M.finrank_eq)
        (FiberBundle.mem_baseSet_trivializationAt' x)
    have hωb : Ω.1 x b ≠ 0 := ((Ω.1 x).map_basis_ne_zero_iff b).mpr (hΩ x)
    have h1 := smul_topForm_jacobianAnchor Ω hΩ μ_N f hf x α β b
    have h2 := smul_topForm_jacobianAnchor Ω hΩ μ_N f hf x β α b
    have hanti :
        ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
          (ContinuousLinearMap.mul ℝ ℝ).continuous₂
          (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1) α)
          (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1) β) =
        -ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
          (ContinuousLinearMap.mul ℝ ℝ).continuous₂
          (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1) β)
          (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1) α) := by
      ext u
      have hc := ContinuousAlternatingMap.pairedWedge_comm
        (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (fun a b ↦ mul_comm a b)
        (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1) α)
        (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1) β) u
      have hcu : (u ∘ Fin.cast (Nat.add_comm 1 1)) = u := funext fun _ ↦ rfl
      rw [hcu] at hc
      simpa using hc
    have hsum : β (jacobianAnchor Ω μ_N f hf x α) * Ω.1 x b =
        -(α (jacobianAnchor Ω μ_N f hf x β) * Ω.1 x b) := by
      rw [h1, h2, hanti]
      simpa using DFunLike.congr_fun
        (ContinuousAlternatingMap.pairedWedge_smul_left (ContinuousLinearMap.mul ℝ ℝ)
          (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (-1 : ℝ) _
          ((SmoothForm.mpullback f hf μ_N).1 x)) ⇑b
    rw [← neg_mul] at hsum
    exact mul_right_cancel₀ hωb hsum
  contMDiff_anchor α := by
    have heq : (fun x ↦ jacobianAnchor Ω μ_N f hf x (SmoothForm.degreeOneEquiv α x)) =
        vectorFieldOfSubTopForm Ω (-SmoothForm.wedge α (SmoothForm.mpullback f hf μ_N)) := by
      funext x
      rw [jacobianAnchor_eq_subTopDualVector]
      congr 1
      ext w
      have hα : ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1)
          (SmoothForm.degreeOneEquiv α x) = α.1 x := by
        ext u
        have hu : u = ![u 0] := funext fun i ↦ by fin_cases i; rfl
        conv_rhs => rw [hu]
        rw [ContinuousAlternatingMap.ofSubsingleton_apply_apply,
          SmoothForm.degreeOneEquiv_apply_apply_vec]
      rw [SmoothForm.neg_toRoughForm, Pi.neg_apply, ContinuousAlternatingMap.neg_apply,
        SmoothForm.coe_wedge, RoughForm.wedge_def, RoughForm.wedgeWith_apply',
        ContinuousAlternatingMap.neg_apply, hα]
    have hsec : (fun x ↦ (⟨x, jacobianAnchor Ω μ_N f hf x (SmoothForm.degreeOneEquiv α x)⟩ :
        TangentBundle I_M M)) =
        (fun x ↦ ⟨x, vectorFieldOfSubTopForm Ω
          (-SmoothForm.wedge α (SmoothForm.mpullback f hf μ_N)) x⟩) :=
      funext fun x ↦ congrArg (TotalSpace.mk' E_M x) (congrFun heq x)
    rw [hsec]
    exact contMDiff_vectorFieldOfSubTopForm Ω hΩ _

omit hdim_N [FiniteDimensional ℝ E_N] in
/-- Interior product of `#_{π_f}(α)` with `Ω` equals `-(α ∧ f^* μ_N)`. -/
theorem interior_anchorVectorField_jacobianSmoothBivector (Ω : SmoothForm I_M M ℝ 4)
    (hΩ : ∀ x : M, Ω.1 x ≠ 0) (μ_N : SmoothForm I_N N ℝ 2) (f : M → N)
    (hf : ContMDiff I_M I_N ∞ f) (α : SmoothForm I_M M ℝ 1) :
    RoughForm.interior ((jacobianSmoothBivector Ω hΩ μ_N f hf).anchorVectorField α) Ω.1 =
      (-SmoothForm.wedge α (SmoothForm.mpullback f hf μ_N)).1 := by
  funext x
  ext w
  have hα : ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1)
      (SmoothForm.degreeOneEquiv α x) = α.1 x := by
    ext u
    have hu : u = ![u 0] := funext fun i ↦ by fin_cases i; rfl
    conv_rhs => rw [hu]
    rw [ContinuousAlternatingMap.ofSubsingleton_apply_apply,
      SmoothForm.degreeOneEquiv_apply_apply_vec]
  rw [RoughForm.interior_apply, SmoothBivector.anchorVectorField, SmoothForm.neg_toRoughForm,
    Pi.neg_apply, ContinuousAlternatingMap.neg_apply, SmoothForm.coe_wedge,
    RoughForm.wedge_def, RoughForm.wedgeWith_apply']
  change Ω.1 x (Matrix.vecCons (jacobianAnchor Ω μ_N f hf x (SmoothForm.degreeOneEquiv α x)) w) = _
  rw [apply_vecCons_jacobianAnchor Ω hΩ μ_N f hf, hα]

omit hdim_N [FiniteDimensional ℝ E_N] in
/-- Interior product of `X_h` with `Ω` equals `dh ∧ f^* μ_N` everywhere on `M`. -/
theorem interior_hamiltonianVectorField_jacobianSmoothBivector (Ω : SmoothForm I_M M ℝ 4)
    (hΩ : ∀ x : M, Ω.1 x ≠ 0) (μ_N : SmoothForm I_N N ℝ 2) (f : M → N)
    (hf : ContMDiff I_M I_N ∞ f) (h : C^∞⟮I_M, M; ℝ⟯) :
    RoughForm.interior ((jacobianSmoothBivector Ω hΩ μ_N f hf).hamiltonianVectorField h) Ω.1 =
      (SmoothForm.wedge (SmoothBivector.diffOneForm h) (SmoothForm.mpullback f hf μ_N)).1 := by
  rw [(jacobianSmoothBivector Ω hΩ μ_N f hf).hamiltonianVectorField_eq_neg_anchorVectorField]
  have hneg : RoughForm.interior
      (-(jacobianSmoothBivector Ω hΩ μ_N f hf).anchorVectorField (SmoothBivector.diffOneForm h))
      Ω.1 =
      -RoughForm.interior
        ((jacobianSmoothBivector Ω hΩ μ_N f hf).anchorVectorField (SmoothBivector.diffOneForm h))
        Ω.1 := by
    funext x
    ext w
    rw [Pi.neg_apply, ContinuousAlternatingMap.neg_apply,
      RoughForm.interior_apply, RoughForm.interior_apply, Pi.neg_apply,
      ← neg_one_smul ℝ
        ((jacobianSmoothBivector Ω hΩ μ_N f hf).anchorVectorField (SmoothBivector.diffOneForm h) x),
      map_vecCons_smul_slot0, neg_one_smul]
  rw [hneg, interior_anchorVectorField_jacobianSmoothBivector, SmoothForm.neg_toRoughForm, neg_neg]

omit hdim_N [FiniteDimensional ℝ E_N] in
/-- Defining top-form identity `{g, h}_{π_f} • Ω = dg ∧ dh ∧ f^* μ_N` (`S4TCdiffeo-Aug-2026.tex`,
Equation (1)). -/
theorem funSMulₗ_bracket_jacobianSmoothBivector (Ω : SmoothForm I_M M ℝ 4)
    (hΩ : ∀ x : M, Ω.1 x ≠ 0) (μ_N : SmoothForm I_N N ℝ 2) (f : M → N)
    (hf : ContMDiff I_M I_N ∞ f) (g h : C^∞⟮I_M, M; ℝ⟯) :
    SmoothForm.funSMulₗ ((jacobianSmoothBivector Ω hΩ μ_N f hf).bracket g h) Ω =
      SmoothForm.wedge (SmoothForm.wedge (SmoothBivector.diffOneForm g)
        (SmoothBivector.diffOneForm h)) (SmoothForm.mpullback f hf μ_N) := by
  apply Subtype.ext
  funext x
  ext v
  have hdg : ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1)
      (mvfderiv I_M g x) = (SmoothBivector.diffOneForm g).1 x := by
    ext u
    have hu : u = ![u 0] := funext fun i ↦ by fin_cases i; rfl
    conv_rhs => rw [hu]
    rw [ContinuousAlternatingMap.ofSubsingleton_apply_apply, SmoothBivector.diffOneForm_apply]
  have hdh : ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1)
      (mvfderiv I_M h x) = (SmoothBivector.diffOneForm h).1 x := by
    ext u
    have hu : u = ![u 0] := funext fun i ↦ by fin_cases i; rfl
    conv_rhs => rw [hu]
    rw [ContinuousAlternatingMap.ofSubsingleton_apply_apply, SmoothBivector.diffOneForm_apply]
  rw [SmoothForm.coe_funSMulₗ, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    SmoothBivector.bracket_apply, SmoothBivector.bivector_apply]
  change (mvfderiv I_M h x) (jacobianAnchor Ω μ_N f hf x (mvfderiv I_M g x)) * Ω.1 x v = _
  rw [smul_topForm_jacobianAnchor Ω hΩ μ_N f hf x (mvfderiv I_M g x) (mvfderiv I_M h x) v,
    SmoothForm.coe_wedge, SmoothForm.coe_wedge, RoughForm.wedge_def, RoughForm.wedge_def,
    RoughForm.wedgeWith_apply', RoughForm.wedgeWith_apply', hdg, hdh]

/-- Every vector in the image of `#_{π_f, x}` lies in `ker(mfderiv f x)` (globally on `M`, including
at critical points of `f`). -/
theorem mfderiv_jacobianAnchor_eq_zero (Ω : SmoothForm I_M M ℝ 4) (hΩ : ∀ x : M, Ω.1 x ≠ 0)
    (μ_N : SmoothForm I_N N ℝ 2) (f : M → N) (hf : ContMDiff I_M I_N ∞ f)
    (x : M) (α : TangentSpace I_M x →L[ℝ] ℝ) :
    mfderiv I_M I_N f x (jacobianAnchor Ω μ_N f hf x α) = 0 := by
  let bN : Module.Basis (Fin 2) ℝ (TangentSpace I_N (f x)) :=
    (trivializationAt E_N (TangentSpace I_N) (f x)).basisAt
      (Module.finBasisOfFinrankEq ℝ E_N hdim_N.finrank_eq)
      (FiberBundle.mem_baseSet_trivializationAt' (f x))
  let bM : Module.Basis (Fin 4) ℝ (TangentSpace I_M x) :=
    (trivializationAt E_M (TangentSpace I_M) x).basisAt
      (Module.finBasisOfFinrankEq ℝ E_M hdim_M.finrank_eq)
      (FiberBundle.mem_baseSet_trivializationAt' x)
  have hωb : Ω.1 x bM ≠ 0 := ((Ω.1 x).map_basis_ne_zero_iff bM).mpr (hΩ x)
  suffices hforall : ∀ γ : TangentSpace I_N (f x) →L[ℝ] ℝ,
      γ (mfderiv I_M I_N f x (jacobianAnchor Ω μ_N f hf x α)) = 0 by
    refine bN.ext_elem fun i ↦ ?_
    rw [map_zero, Finsupp.zero_apply]
    let eN := trivializationAt E_N (TangentSpace I_N) (f x)
    let bEN := Module.finBasisOfFinrankEq ℝ E_N hdim_N.finrank_eq
    let γi : TangentSpace I_N (f x) →L[ℝ] ℝ :=
      (bEN.coord i).toContinuousLinearMap.comp (eN.continuousLinearMapAt ℝ (f x))
    have hγ := hforall γi
    have hγb (j : Fin 2) : γi (bN j) = if j = i then 1 else 0 := by
      change (bEN.coord i) (eN.continuousLinearMapAt ℝ (f x) (bN j)) = _
      dsimp only [bN]
      rw [TauCeti.Manifold.basisAt_apply bEN (FiberBundle.mem_baseSet_trivializationAt' (f x)) j,
        eN.continuousLinearMapAt_symmL (FiberBundle.mem_baseSet_trivializationAt' (f x)),
        Module.Basis.coord_apply, bEN.repr_self, Finsupp.single_apply]
    have hrepr : ∀ u : TangentSpace I_N (f x), bN.repr u i = γi u := by
      intro u
      have hu : u = ∑ j : Fin 2, bN.repr u j • bN j := (bN.sum_repr u).symm
      conv_rhs => rw [hu]
      rw [map_sum]
      simp_rw [map_smul, hγb, smul_eq_mul, mul_ite, mul_one, mul_zero]
      simp
    rw [hrepr]
    exact hγ
  intro γ
  have hsmul := smul_topForm_jacobianAnchor Ω hΩ μ_N f hf x α
    (γ.comp (mfderiv I_M I_N f x)) bM
  rw [ContinuousLinearMap.comp_apply] at hsmul
  let γN : TangentSpace I_N (f x) [⋀^Fin 1]→L[ℝ] ℝ :=
    ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_N (f x)) ℝ (0 : Fin 1) γ
  have htopN : ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
      (ContinuousLinearMap.mul ℝ ℝ).continuous₂ γN (μ_N.1 (f x)) = 0 := by
    refine ContinuousAlternatingMap.eq_zero_of_finrank_lt _ ?_
    have : Module.Finite ℝ (TangentSpace I_N (f x)) := bN.finiteDimensional_of_finite
    have hfin : Module.finrank ℝ (TangentSpace I_N (f x)) = 2 := by
      rw [Module.finrank_eq_card_basis bN, Fintype.card_fin]
    rw [hfin, Fintype.card_fin]
    omega
  have hpul : ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
      (ContinuousLinearMap.mul ℝ ℝ).continuous₂
      (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1)
        (γ.comp (mfderiv I_M I_N f x)))
      ((SmoothForm.mpullback f hf μ_N).1 x) = 0 := by
    ext w
    have hpull_γ : ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1)
        (γ.comp (mfderiv I_M I_N f x)) =
        γN.compContinuousLinearMap (mfderiv I_M I_N f x) := by
      ext u
      have hu : u = ![u 0] := funext fun i ↦ by fin_cases i; rfl
      rw [hu, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
        ContinuousAlternatingMap.compContinuousLinearMap_apply]
      simp [γN]
    have hpull_μ : (SmoothForm.mpullback f hf μ_N).1 x =
        (μ_N.1 (f x)).compContinuousLinearMap (mfderiv I_M I_N f x) := by
      ext u
      rw [SmoothForm.mpullback_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply]
      rfl
    rw [hpull_γ, hpull_μ, ContinuousAlternatingMap.pairedWedge_apply]
    have hpull_w := DFunLike.congr_fun htopN (fun i ↦ mfderiv I_M I_N f x (w i))
    rw [ContinuousAlternatingMap.pairedWedge_apply] at hpull_w
    change _ = (0 : ℝ) at hpull_w
    simpa [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def] using hpull_w
  classical
  let αc : RoughForm I_M M ℝ 1 := fun y ↦
    if hy : y = x then
      hy ▸ ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1) α
    else 0
  let βc : RoughForm I_M M ℝ 1 := fun y ↦
    if hy : y = x then
      hy ▸ ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1)
        (γ.comp (mfderiv I_M I_N f x))
    else 0
  have hαcx : αc x =
      ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1) α := by
    simp only [αc, ↓reduceDIte]
  have hβcx : βc x =
      ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1)
        (γ.comp (mfderiv I_M I_N f x)) := by
    simp only [βc, ↓reduceDIte]
  have hassoc := RoughForm.wedgeWith_assoc (I := I_M)
    (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
    (fun a b c ↦ mul_assoc a b c) αc βc (SmoothForm.mpullback f hf μ_N).1 x bM
  have hcast : (⇑bM ∘ Fin.cast (Nat.add_assoc 1 1 2).symm) = ⇑bM := funext fun _ ↦ rfl
  rw [hcast] at hassoc
  simp only [RoughForm.wedgeWith_apply', hαcx, hβcx] at hassoc
  rw [hpul, ContinuousAlternatingMap.pairedWedge_zero_right] at hassoc
  change _ = (0 : ℝ) at hassoc
  rw [hassoc] at hsmul
  exact (mul_eq_zero.mp hsmul).resolve_right hωb

/-- Every Hamiltonian vector field `X_h` of `π_f` is tangent to the fibers of `f`:
`mfderiv f x (X_h x) = 0` at every `x ∈ M`. -/
theorem mfderiv_hamiltonianVectorField_jacobianSmoothBivector (Ω : SmoothForm I_M M ℝ 4)
    (hΩ : ∀ x : M, Ω.1 x ≠ 0) (μ_N : SmoothForm I_N N ℝ 2) (f : M → N)
    (hf : ContMDiff I_M I_N ∞ f) (h : C^∞⟮I_M, M; ℝ⟯) (x : M) :
    mfderiv I_M I_N f x
      ((jacobianSmoothBivector Ω hΩ μ_N f hf).hamiltonianVectorField h x) = 0 := by
  rw [SmoothBivector.hamiltonianVectorField, map_neg]
  dsimp only [jacobianSmoothBivector]
  rw [mfderiv_jacobianAnchor_eq_zero Ω hΩ μ_N f hf x, neg_zero]

/-- Interior contraction `ι_{X_u} (f^* μ_N) = 0` vanishes identically on `M`. -/
theorem interior_hamiltonian_mpullback_eq_zero (Ω : SmoothForm I_M M ℝ 4)
    (hΩ : ∀ x : M, Ω.1 x ≠ 0) (μ_N : SmoothForm I_N N ℝ 2) (f : M → N)
    (hf : ContMDiff I_M I_N ∞ f) (u : C^∞⟮I_M, M; ℝ⟯) :
    RoughForm.interior ((jacobianSmoothBivector Ω hΩ μ_N f hf).hamiltonianVectorField u)
      (SmoothForm.mpullback f hf μ_N).1 = 0 := by
  funext x
  ext w
  rw [RoughForm.interior_apply, SmoothForm.mpullback_apply]
  have h0 : (fun i : Fin 2 ↦
      mfderiv I_M I_N f x
        (Matrix.vecCons ((jacobianSmoothBivector Ω hΩ μ_N f hf).hamiltonianVectorField u x) w i)) =
      Matrix.vecCons 0 (fun j : Fin 1 ↦ mfderiv I_M I_N f x (w j)) := by
    funext i
    cases i using Fin.cases with
    | zero =>
      simpa using mfderiv_hamiltonianVectorField_jacobianSmoothBivector Ω hΩ μ_N f hf u x
    | succ j => rfl
  rw [h0]
  have hzero := map_vecCons_smul_slot0 (μ_N.1 (f x)) (0 : ℝ) 0
    (fun j : Fin 1 ↦ mfderiv I_M I_N f x (w j))
  simpa using hzero

/-- **GSV15 Theorem 2.6**: The Jacobian–Poisson structure `π_f` on a smooth `4`-manifold `M`
associated to `f : M → N`, nowhere-vanishing volume `4`-form `Ω`, and `2`-form `μ_N` satisfies the
cyclic Jacobi identity globally on all of `M` (including across `Crit(f)`). -/
def jacobianPoisson (Ω : SmoothForm I_M M ℝ 4) (hΩ : ∀ x : M, Ω.1 x ≠ 0)
    (μ_N : SmoothForm I_N N ℝ 2) (f : M → N) (hf : ContMDiff I_M I_N ∞ f) :
    PoissonStructure I_M M where
  toSmoothBivector := jacobianSmoothBivector Ω hΩ μ_N f hf
  jacobi g h u := by
    let B := jacobianSmoothBivector Ω hΩ μ_N f hf
    let ψ : SmoothForm I_M M ℝ 2 := SmoothForm.mpullback f hf μ_N
    let η (w : C^∞⟮I_M, M; ℝ⟯) : SmoothForm I_M M ℝ 3 :=
      SmoothForm.wedge (SmoothBivector.diffOneForm w) ψ
    have hι_η (k : C^∞⟮I_M, M; ℝ⟯) :
        RoughForm.interior (B.hamiltonianVectorField u) (η k).1 =
          (SmoothForm.funSMulₗ (B.bracket k u) ψ).1 := by
      funext x
      ext w
      rw [SmoothForm.coe_wedge, RoughForm.interior_wedge_apply (k := 0) (l := 1),
        interior_hamiltonian_mpullback_eq_zero Ω hΩ μ_N f hf u, RoughForm.wedge_zero_right]
      have hcast : (w ∘ Fin.cast (show 0 + (1 + 1) = 0 + 1 + 1 by omega)) =
          (w ∘ Fin.cast (zero_add 2)) := funext fun _ ↦ rfl
      have h0 : RoughForm.interior (B.hamiltonianVectorField u) (SmoothBivector.diffOneForm k).1 =
          RoughForm.ofFunction I_M (B.bracket k u) := by
        rw [RoughForm.eq_ofFunction
          (RoughForm.interior (B.hamiltonianVectorField u) (SmoothBivector.diffOneForm k).1)]
        congr 1
        funext y
        rw [RoughForm.interior_apply]
        have hv : (Matrix.vecCons (B.hamiltonianVectorField u y) 0 :
            Fin 1 → TangentSpace I_M y) = ![B.hamiltonianVectorField u y] := by
          funext i; fin_cases i; rfl
        rw [hv, SmoothBivector.diffOneForm_apply,
          ← B.bracket_apply_eq_mvfderiv_hamiltonianVectorField]
      rw [hcast, h0, RoughForm.ofFunction_wedge_apply, SmoothForm.coe_funSMulₗ,
        ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      change (B.bracket k u) x * ψ.1 x w + (-1 : ℝ) ^ (0 + 1) * 0 = (B.bracket k u) x * ψ.1 x w
      ring
    have htop_assoc : SmoothForm.funSMulₗ (B.bracket g h) Ω =
        SmoothForm.wedge (SmoothBivector.diffOneForm g) (η h) := by
      rw [funSMulₗ_bracket_jacobianSmoothBivector]
      apply Subtype.ext
      funext x
      ext v
      have ha := SmoothForm.wedge_assoc_apply (SmoothBivector.diffOneForm g)
        (SmoothBivector.diffOneForm h) ψ x v
      have hc : (v ∘ Fin.cast (Nat.add_assoc 1 1 2).symm) = v := funext fun _ ↦ rfl
      rw [hc] at ha
      exact ha
    have hcontract : SmoothForm.funSMulₗ (B.bracket g h) (η u) =
        SmoothForm.funSMulₗ (B.bracket g u) (η h) -
          SmoothForm.funSMulₗ (B.bracket h u) (η g) := by
      apply Subtype.ext
      have hlhs : (SmoothForm.funSMulₗ (B.bracket g h) (η u)).1 =
          RoughForm.interior (B.hamiltonianVectorField u)
            (SmoothForm.funSMulₗ (B.bracket g h) Ω).1 := by
        rw [SmoothForm.coe_funSMulₗ, SmoothForm.coe_funSMulₗ,
          ← interior_hamiltonianVectorField_jacobianSmoothBivector Ω hΩ μ_N f hf u]
        exact (RoughForm.interior_smul_pointwise (B.bracket g h)
          (B.hamiltonianVectorField u) Ω.1).symm
      rw [hlhs, htop_assoc]
      funext x
      ext w
      rw [SmoothForm.coe_wedge, RoughForm.interior_wedge_apply (k := 0) (l := 2), hι_η h]
      have hcast : (w ∘ Fin.cast (show 0 + (2 + 1) = 0 + 1 + 2 by omega)) =
          (w ∘ Fin.cast (zero_add 3)) := funext fun _ ↦ rfl
      have h0 : RoughForm.interior (B.hamiltonianVectorField u) (SmoothBivector.diffOneForm g).1 =
          RoughForm.ofFunction I_M (B.bracket g u) := by
        rw [RoughForm.eq_ofFunction
          (RoughForm.interior (B.hamiltonianVectorField u) (SmoothBivector.diffOneForm g).1)]
        congr 1
        funext y
        rw [RoughForm.interior_apply]
        have hv : (Matrix.vecCons (B.hamiltonianVectorField u y) 0 :
            Fin 1 → TangentSpace I_M y) = ![B.hamiltonianVectorField u y] := by
          funext i; fin_cases i; rfl
        rw [hv, SmoothBivector.diffOneForm_apply,
          ← B.bracket_apply_eq_mvfderiv_hamiltonianVectorField]
      have hsmul_wedge : RoughForm.wedge (SmoothBivector.diffOneForm g).1
          (SmoothForm.funSMulₗ (B.bracket h u) ψ).1 x w =
          (B.bracket h u) x * (η g).1 x w := by
        rw [SmoothForm.coe_funSMulₗ, RoughForm.wedge_def, RoughForm.wedgeWith_apply',
          ContinuousAlternatingMap.pairedWedge_smul_right,
          ContinuousAlternatingMap.smul_apply, smul_eq_mul,
          SmoothForm.coe_wedge, RoughForm.wedge_def, RoughForm.wedgeWith_apply']
      rw [hcast, h0, RoughForm.ofFunction_wedge_apply, hsmul_wedge,
        Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply,
        SmoothForm.coe_funSMulₗ, SmoothForm.coe_funSMulₗ,
        ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.smul_apply,
        smul_eq_mul, smul_eq_mul]
      simp only [zero_add, pow_one]
      change (B.bracket g u) x * (η h).1 x w + (-1 : ℝ) * ((B.bracket h u) x * (η g).1 x w) =
        (B.bracket g u) x * (η h).1 x w - (B.bracket h u) x * (η g).1 x w
      ring
    have hd_η (k : C^∞⟮I_M, M; ℝ⟯) : mextDerivₗ I_M 3 (η k) = 0 :=
      (SmoothForm.isClosed_iff_mextDerivₗ_eq_zero (η k)).mp
        (isClosed_diffOneForm_wedge_mpullback μ_N f hf k)
    have hd_smul (a b : C^∞⟮I_M, M; ℝ⟯) :
        mextDerivₗ I_M 3 (SmoothForm.funSMulₗ a (η b)) =
          SmoothForm.funSMulₗ (B.bracket a b) Ω := by
      apply Subtype.ext
      funext x
      ext v
      rw [SmoothForm.mextDerivₗ_funSMulₗ_apply, hd_η b]
      have hcast : (v ∘ Fin.cast (show 0 + 1 + 3 = 3 + 1 by omega)) = v := funext fun _ ↦ rfl
      have hstep : SmoothForm.funSMulₗ (B.bracket a b) Ω =
          SmoothForm.wedge (SmoothBivector.diffOneForm a) (η b) := by
        rw [funSMulₗ_bracket_jacobianSmoothBivector]
        apply Subtype.ext
        funext y
        ext u
        have ha := SmoothForm.wedge_assoc_apply (SmoothBivector.diffOneForm a)
          (SmoothBivector.diffOneForm b) ψ y u
        have hc : (u ∘ Fin.cast (Nat.add_assoc 1 1 2).symm) = u := funext fun _ ↦ rfl
        rw [hc] at ha
        exact ha
      have hval := DFunLike.congr_fun (congrFun (congrArg Subtype.val hstep) x) v
      rw [SmoothForm.coe_wedge, SmoothBivector.diffOneForm, mextDerivₗ_apply,
        SmoothForm.coe_ofFunction] at hval
      rw [hcast, ← hval]
      simp
    have hd_eq := congrArg (mextDerivₗ I_M 3) hcontract
    rw [map_sub, hd_smul, hd_smul, hd_smul] at hd_eq
    have hbr_eq : B.bracket (B.bracket g h) u =
        B.bracket (B.bracket g u) h - B.bracket (B.bracket h u) g := by
      ext x
      have hx := congrFun (congrArg Subtype.val hd_eq) x
      rw [Submodule.coe_sub, Pi.sub_apply, SmoothForm.coe_funSMulₗ,
        SmoothForm.coe_funSMulₗ, SmoothForm.coe_funSMulₗ, ← sub_smul] at hx
      exact smul_left_injective ℝ (hΩ x) hx
    ext x
    have hx := congrArg (fun w : C^∞⟮I_M, M; ℝ⟯ ↦ w x) hbr_eq
    have hs1 := congrArg (fun w : C^∞⟮I_M, M; ℝ⟯ ↦ w x) (B.bracket_skew (B.bracket g h) u)
    have hs2 := congrArg (fun w : C^∞⟮I_M, M; ℝ⟯ ↦ w x) (B.bracket_skew (B.bracket g u) h)
    have hs4 := congrArg (fun w : C^∞⟮I_M, M; ℝ⟯ ↦ w x) (B.bracket_skew (B.bracket h u) g)
    have hs2' : (B.bracket h (B.bracket g u)) x = -(B.bracket h (B.bracket u g)) x := by
      rw [B.bracket_skew g u, B.bracket_neg_right, ContMDiffMap.coe_neg, Pi.neg_apply]
    simp only [ContMDiffMap.coe_add, ContMDiffMap.coe_sub, ContMDiffMap.coe_neg,
      ContMDiffMap.coe_zero, Pi.add_apply, Pi.sub_apply, Pi.neg_apply,
      Pi.zero_apply] at hx hs1 hs2 hs4 ⊢
    linarith

/-- Convenience constructor taking a `PositiveVolumeForm I_M M` directly. -/
def jacobianPoissonOfPositiveVolume [MeasurableSpace M] [BorelSpace M]
    (V : PositiveVolumeForm I_M M) (μ_N : SmoothForm I_N N ℝ 2)
    (f : M → N) (hf : ContMDiff I_M I_N ∞ f) :
    PoissonStructure I_M M :=
  jacobianPoisson V.Ω V.Ω_ne_zero μ_N f hf

/-- Defining equation `{g, h}_{π_f} • Ω = dg ∧ dh ∧ f^* μ_N` on `jacobianPoisson`. -/
theorem funSMulₗ_bracket_jacobianPoisson (Ω : SmoothForm I_M M ℝ 4) (hΩ : ∀ x : M, Ω.1 x ≠ 0)
    (μ_N : SmoothForm I_N N ℝ 2) (f : M → N) (hf : ContMDiff I_M I_N ∞ f)
    (g h : C^∞⟮I_M, M; ℝ⟯) :
    SmoothForm.funSMulₗ ((jacobianPoisson Ω hΩ μ_N f hf).bracket g h) Ω =
      SmoothForm.wedge (SmoothForm.wedge (SmoothBivector.diffOneForm g)
        (SmoothBivector.diffOneForm h)) (SmoothForm.mpullback f hf μ_N) :=
  funSMulₗ_bracket_jacobianSmoothBivector Ω hΩ μ_N f hf g h

/-- Explicit quotient formula `{g, h}_{π_f} = divVolume Ω hΩ (dg ∧ dh ∧ f^* μ_N)`. -/
theorem bracket_jacobianPoisson_eq_divVolume (Ω : SmoothForm I_M M ℝ 4) (hΩ : ∀ x : M, Ω.1 x ≠ 0)
    (μ_N : SmoothForm I_N N ℝ 2) (f : M → N) (hf : ContMDiff I_M I_N ∞ f)
    (g h : C^∞⟮I_M, M; ℝ⟯) :
    (jacobianPoisson Ω hΩ μ_N f hf).bracket g h =
      divVolume Ω hΩ (SmoothForm.wedge (SmoothForm.wedge (SmoothBivector.diffOneForm g)
        (SmoothBivector.diffOneForm h)) (SmoothForm.mpullback f hf μ_N)) :=
  (eq_divVolume_iff Ω hΩ _ _).mpr (funSMulₗ_bracket_jacobianPoisson Ω hΩ μ_N f hf g h)

/-! ### Global Unimodularity across `Crit(f)` (`BV21`; `S4TCdiffeo-Aug-2026.tex`, Proposition 1) -/

/-- Every Hamiltonian vector field `X_h` of `jacobianPoisson` preserves `Ω` (`𝓛_{X_h} Ω = 0`)
globally on all of `M`, including across `Crit(f)`. -/
theorem lieDerivVolume_jacobianPoisson_eq_zero (Ω : SmoothForm I_M M ℝ 4)
    (hΩ : ∀ x : M, Ω.1 x ≠ 0) (μ_N : SmoothForm I_N N ℝ 2) (f : M → N)
    (hf : ContMDiff I_M I_N ∞ f) (h : C^∞⟮I_M, M; ℝ⟯) :
    (jacobianPoisson Ω hΩ μ_N f hf).lieDerivVolume Ω h = 0 := by
  apply Subtype.ext
  rw [PoissonStructure.coe_lieDerivVolume,
    (jacobianPoisson Ω hΩ μ_N f hf).lieDerivVolume_eq_mextDeriv_interior (m := 3) Ω
      hdim_M.finrank_eq.le h]
  change mextDeriv (RoughForm.interior
    ((jacobianSmoothBivector Ω hΩ μ_N f hf).hamiltonianVectorField h) Ω.1) = 0
  rw [interior_hamiltonianVectorField_jacobianSmoothBivector Ω hΩ μ_N f hf h]
  exact (SmoothForm.isClosed_def _).mp (isClosed_diffOneForm_wedge_mpullback μ_N f hf h)

/-- **Global Unimodularity with Volume `Ω`**: `jacobianPoisson Ω hΩ μ_N f hf` is unimodular with
respect to `Ω` across all of `M` (including `Crit(f)`). -/
theorem isUnimodularWithVolume_jacobianPoisson (Ω : SmoothForm I_M M ℝ 4)
    (hΩ : ∀ x : M, Ω.1 x ≠ 0) (μ_N : SmoothForm I_N N ℝ 2) (f : M → N)
    (hf : ContMDiff I_M I_N ∞ f) :
    (jacobianPoisson Ω hΩ μ_N f hf).IsUnimodularWithVolume Ω :=
  ⟨hΩ, lieDerivVolume_jacobianPoisson_eq_zero Ω hΩ μ_N f hf⟩

/-- Weinstein's modular derivation `Y^Ω` vanishes identically (`Y^Ω = 0`) on `jacobianPoisson`. -/
@[simp]
theorem modularDerivation_jacobianPoisson_eq_zero (Ω : SmoothForm I_M M ℝ 4)
    (hΩ : ∀ x : M, Ω.1 x ≠ 0) (μ_N : SmoothForm I_N N ℝ 2) (f : M → N)
    (hf : ContMDiff I_M I_N ∞ f) :
    (jacobianPoisson Ω hΩ μ_N f hf).modularDerivation Ω hΩ = 0 :=
  ((jacobianPoisson Ω hΩ μ_N f hf).isUnimodularWithVolume_iff_modularDerivation_eq_zero Ω hΩ).mp
    (isUnimodularWithVolume_jacobianPoisson Ω hΩ μ_N f hf)

/-- Every Jacobian–Poisson 4-manifold `(M, π_f)` satisfies `IsUnimodularPoisson`. -/
theorem isUnimodularPoisson_jacobianPoisson (Ω : SmoothForm I_M M ℝ 4)
    (hΩ : ∀ x : M, Ω.1 x ≠ 0) (μ_N : SmoothForm I_N N ℝ 2) (f : M → N)
    (hf : ContMDiff I_M I_N ∞ f) :
    (jacobianPoisson Ω hΩ μ_N f hf).IsUnimodularPoisson :=
  (isUnimodularWithVolume_jacobianPoisson Ω hΩ μ_N f hf).isUnimodularPoisson

theorem isUnimodularPoisson_jacobianPoissonOfPositiveVolume [MeasurableSpace M] [BorelSpace M]
    (V : PositiveVolumeForm I_M M) (μ_N : SmoothForm I_N N ℝ 2)
    (f : M → N) (hf : ContMDiff I_M I_N ∞ f) :
    (jacobianPoissonOfPositiveVolume V μ_N f hf).IsUnimodularPoisson :=
  isUnimodularPoisson_jacobianPoisson V.Ω V.Ω_ne_zero μ_N f hf

/-! ### Casimir Functions, Symplectic Distribution `Im(#_{π_f}) = ker(mfderiv f)`, and Rank `2` -/

/-- Pullbacks `u ∘ f` of smooth functions `u ∈ C^∞(N)` are Casimir functions of `π_f`. -/
theorem isCasimir_comp_jacobianPoisson (Ω : SmoothForm I_M M ℝ 4) (hΩ : ∀ x : M, Ω.1 x ≠ 0)
    (μ_N : SmoothForm I_N N ℝ 2) (f : M → N) (hf : ContMDiff I_M I_N ∞ f)
    (u : C^∞⟮I_N, N; ℝ⟯) :
    (jacobianPoisson Ω hΩ μ_N f hf).IsCasimir (u.comp ⟨f, hf⟩) := by
  intro h
  ext x
  rw [(jacobianPoisson Ω hΩ μ_N f hf).bracket_apply_eq_mvfderiv_hamiltonianVectorField]
  have hud : MDifferentiableAt I_N 𝓘(ℝ) u (f x) := u.contMDiff.mdifferentiableAt (by simp)
  have hfd : MDifferentiableAt I_M I_N f x := hf.mdifferentiableAt (by simp)
  have hchain : mvfderiv I_M (u ∘ f) x = (mvfderiv I_N u (f x)).comp (mfderiv I_M I_N f x) := by
    ext v
    simp only [mvfderiv_apply_eq_mfderiv_apply, ContinuousLinearMap.comp_apply]
    exact congrArg (· v) (mfderiv_comp x hud hfd)
  change mvfderiv I_M (u ∘ f) x
    ((jacobianSmoothBivector Ω hΩ μ_N f hf).hamiltonianVectorField h x) = 0
  rw [hchain, ContinuousLinearMap.comp_apply,
    mfderiv_hamiltonianVectorField_jacobianSmoothBivector Ω hΩ μ_N f hf h x, map_zero]

/-- At every point `x ∈ M` (including critical points), `Im(#_{π_f, x}) ≤ ker(mfderiv f x)`. -/
theorem range_anchor_le_ker_mfderiv (Ω : SmoothForm I_M M ℝ 4) (hΩ : ∀ x : M, Ω.1 x ≠ 0)
    (μ_N : SmoothForm I_N N ℝ 2) (f : M → N) (hf : ContMDiff I_M I_N ∞ f) (x : M) :
    LinearMap.range ((jacobianPoisson Ω hΩ μ_N f hf).anchor x).toLinearMap ≤
      LinearMap.ker (mfderiv I_M I_N f x).toLinearMap := by
  rintro _ ⟨α, rfl⟩
  rw [LinearMap.mem_ker]
  exact mfderiv_jacobianAnchor_eq_zero Ω hΩ μ_N f hf x α

/-- At any regular point `x ∉ criticalSet f` where `μ_N (f x) ≠ 0`, the characteristic distribution
equals the vertical tangent space of `f`: `Im(#_{π_f, x}) = ker(mfderiv f x)`. -/
theorem range_anchor_eq_ker_mfderiv_of_notMem_criticalSet (Ω : SmoothForm I_M M ℝ 4)
    (hΩ : ∀ x : M, Ω.1 x ≠ 0) (μ_N : SmoothForm I_N N ℝ 2) (f : M → N)
    (hf : ContMDiff I_M I_N ∞ f) {x : M}
    (hreg : x ∉ criticalSet I_M I_N f)
    (hμ : μ_N.1 (f x) ≠ 0) :
    LinearMap.range ((jacobianPoisson Ω hΩ μ_N f hf).anchor x).toLinearMap =
      LinearMap.ker (mfderiv I_M I_N f x).toLinearMap := by
  rw [mem_criticalSet_iff, not_not] at hreg
  let bM : Module.Basis (Fin 4) ℝ (TangentSpace I_M x) :=
    (trivializationAt E_M (TangentSpace I_M) x).basisAt
      (Module.finBasisOfFinrankEq ℝ E_M hdim_M.finrank_eq)
      (FiberBundle.mem_baseSet_trivializationAt' x)
  let bN : Module.Basis (Fin 2) ℝ (TangentSpace I_N (f x)) :=
    (trivializationAt E_N (TangentSpace I_N) (f x)).basisAt
      (Module.finBasisOfFinrankEq ℝ E_N hdim_N.finrank_eq)
      (FiberBundle.mem_baseSet_trivializationAt' (f x))
  have : FiniteDimensional ℝ (TangentSpace I_M x) := bM.finiteDimensional_of_finite
  let w (i : Fin 2) : TangentSpace I_M x := (hreg (bN i)).choose
  have hw (i : Fin 2) : mfderiv I_M I_N f x (w i) = bN i := (hreg (bN i)).choose_spec
  have hμw : (SmoothForm.mpullback f hf μ_N).1 x w ≠ 0 := by
    rw [SmoothForm.mpullback_apply]
    have hweq : (fun i ↦ mfderiv I_M I_N f x (w i)) = ⇑bN := funext hw
    rw [hweq]
    exact ((μ_N.1 (f x)).map_basis_ne_zero_iff bN).mpr hμ
  let dfL : TangentSpace I_M x →ₗ[ℝ] TangentSpace I_N (f x) := (mfderiv I_M I_N f x).toLinearMap
  have hdual : ∀ (β : Module.Dual ℝ (TangentSpace I_M x)),
      (∀ u ∈ LinearMap.range ((jacobianPoisson Ω hΩ μ_N f hf).anchor x).toLinearMap, β u = 0) →
      ∀ v ∈ LinearMap.ker dfL, β v = 0 := by
    intro β hβ v hv
    let eM := trivializationAt E_M (TangentSpace I_M) x
    let bEM := Module.finBasisOfFinrankEq ℝ E_M hdim_M.finrank_eq
    let α (j : Fin 4) : TangentSpace I_M x →L[ℝ] ℝ :=
      (bEM.coord j).toContinuousLinearMap.comp (eM.continuousLinearMapAt ℝ x)
    have hαb (j i : Fin 4) : α j (bM i) = if i = j then 1 else 0 := by
      change (bEM.coord j) (eM.continuousLinearMapAt ℝ x (bM i)) = _
      dsimp only [bM]
      rw [TauCeti.Manifold.basisAt_apply bEM (FiberBundle.mem_baseSet_trivializationAt' x) i,
        eM.continuousLinearMapAt_symmL (FiberBundle.mem_baseSet_trivializationAt' x),
        Module.Basis.coord_apply, bEM.repr_self, Finsupp.single_apply]
    have hrepr (j : Fin 4) (u : TangentSpace I_M x) : bM.repr u j = α j u := by
      have hu : u = ∑ i : Fin 4, bM.repr u i • bM i := (bM.sum_repr u).symm
      conv_rhs => rw [hu]
      rw [map_sum]
      simp_rw [map_smul, hαb, smul_eq_mul, mul_ite, mul_one, mul_zero]
      simp
    let βCLM : TangentSpace I_M x →L[ℝ] ℝ := ∑ j : Fin 4, β (bM j) • α j
    have hβ_eq (u : TangentSpace I_M x) : βCLM u = β u := by
      have hu : u = ∑ j : Fin 4, bM.repr u j • bM j := (bM.sum_repr u).symm
      conv_rhs => rw [hu]
      rw [map_sum]
      simp only [βCLM, FunLike.coe_sum, Finset.sum_apply, smul_apply, map_smul, smul_eq_mul,
        ← hrepr]
      exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
    have hanch_zero : jacobianAnchor Ω μ_N f hf x βCLM = 0 := by
      refine bM.ext_elem fun j ↦ ?_
      rw [map_zero, Finsupp.zero_apply, hrepr j]
      change α j ((jacobianSmoothBivector Ω hΩ μ_N f hf).anchor x βCLM) = 0
      rw [(jacobianSmoothBivector Ω hΩ μ_N f hf).anchor_skew x βCLM (α j), hβ_eq]
      have hβ0 : β ((jacobianSmoothBivector Ω hΩ μ_N f hf).anchor x (α j)) = 0 :=
        hβ _ ⟨α j, rfl⟩
      rw [hβ0, neg_zero]
    have hwedge0 : ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
        (ContinuousLinearMap.mul ℝ ℝ).continuous₂
        (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1) βCLM)
        ((SmoothForm.mpullback f hf μ_N).1 x) = 0 := by
      ext u
      change _ = (0 : ℝ)
      have h := apply_vecCons_jacobianAnchor Ω hΩ μ_N f hf x βCLM u
      rw [hanch_zero] at h
      have h0 : Ω.1 x (Matrix.vecCons 0 u) = 0 := by
        simpa using map_vecCons_smul_slot0 (Ω.1 x) (0 : ℝ) 0 u
      rw [h0] at h
      linarith
    by_contra hβv
    let w' (i : Fin 2) : TangentSpace I_M x := w i - (β (w i) / β v) • v
    have hw'_β (i : Fin 2) :
        (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1) βCLM)
          ![w' i] = 0 := by
      rw [ContinuousAlternatingMap.ofSubsingleton_apply_apply, Matrix.cons_val_zero, hβ_eq]
      simp only [w', map_sub, map_smul, smul_eq_mul]
      field_simp [hβv]
      ring
    have hw'_μ : (SmoothForm.mpullback f hf μ_N).1 x w' =
        (SmoothForm.mpullback f hf μ_N).1 x w := by
      rw [SmoothForm.mpullback_apply, SmoothForm.mpullback_apply]
      congr 1
      funext i
      have hv0 : mfderiv I_M I_N f x v = 0 := LinearMap.mem_ker.mp hv
      simp [w', hv0]
    have heval := ContinuousAlternatingMap.pairedWedge_apply_vecCons_of_forall
      (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
      (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I_M x) ℝ (0 : Fin 1) βCLM)
      ((SmoothForm.mpullback f hf μ_N).1 x) v w' hw'_β
    rw [hwedge0, ContinuousAlternatingMap.ofSubsingleton_apply_apply, Matrix.cons_val_zero,
      hβ_eq, ContinuousLinearMap.mul_apply', hw'_μ] at heval
    change (0 : ℝ) = β v * (SmoothForm.mpullback f hf μ_N).1 x w at heval
    exact mul_ne_zero hβv hμw heval.symm
  have hle := range_anchor_le_ker_mfderiv Ω hΩ μ_N f hf x
  refine le_antisymm hle fun v hv ↦ ?_
  by_contra hnot
  let R := LinearMap.range ((jacobianPoisson Ω hΩ μ_N f hf).anchor x).toLinearMap
  obtain ⟨φ, hφv, hφR⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hφ0 : ∀ u ∈ R, φ u = 0 := fun u hu ↦
    (Submodule.mem_bot ℝ).mp (hφR ▸ Submodule.mem_map_of_mem hu)
  exact hφv (hdual φ hφ0 v hv)

/-- At any regular point `x ∉ criticalSet f` where `μ_N (f x) ≠ 0`, the Jacobian–Poisson structure
has rank `2` (`rankAt x = 2`, `GSV15` Theorem 2.6). -/
theorem rankAt_jacobianPoisson_of_notMem_criticalSet (Ω : SmoothForm I_M M ℝ 4)
    (hΩ : ∀ x : M, Ω.1 x ≠ 0) (μ_N : SmoothForm I_N N ℝ 2) (f : M → N)
    (hf : ContMDiff I_M I_N ∞ f) {x : M}
    (hreg : x ∉ criticalSet I_M I_N f)
    (hμ : μ_N.1 (f x) ≠ 0) :
    (jacobianPoisson Ω hΩ μ_N f hf).rankAt x = 2 := by
  unfold SmoothBivector.rankAt
  rw [range_anchor_eq_ker_mfderiv_of_notMem_criticalSet Ω hΩ μ_N f hf hreg hμ]
  rw [mem_criticalSet_iff, not_not] at hreg
  let bM : Module.Basis (Fin 4) ℝ (TangentSpace I_M x) :=
    (trivializationAt E_M (TangentSpace I_M) x).basisAt
      (Module.finBasisOfFinrankEq ℝ E_M hdim_M.finrank_eq)
      (FiberBundle.mem_baseSet_trivializationAt' x)
  let bN : Module.Basis (Fin 2) ℝ (TangentSpace I_N (f x)) :=
    (trivializationAt E_N (TangentSpace I_N) (f x)).basisAt
      (Module.finBasisOfFinrankEq ℝ E_N hdim_N.finrank_eq)
      (FiberBundle.mem_baseSet_trivializationAt' (f x))
  have : FiniteDimensional ℝ (TangentSpace I_M x) := bM.finiteDimensional_of_finite
  have : FiniteDimensional ℝ (TangentSpace I_N (f x)) := bN.finiteDimensional_of_finite
  have hfinM : Module.finrank ℝ (TangentSpace I_M x) = 4 := by
    rw [Module.finrank_eq_card_basis bM, Fintype.card_fin]
  have hfinN : Module.finrank ℝ (TangentSpace I_N (f x)) = 2 := by
    rw [Module.finrank_eq_card_basis bN, Fintype.card_fin]
  let dfL : TangentSpace I_M x →ₗ[ℝ] TangentSpace I_N (f x) := (mfderiv I_M I_N f x).toLinearMap
  have hdf_range : Module.finrank ℝ (LinearMap.range dfL) = 2 := by
    rw [LinearMap.range_eq_top.mpr hreg, finrank_top, hfinN]
  have hrn := LinearMap.finrank_range_add_finrank_ker dfL
  rw [hdf_range, hfinM] at hrn
  change Module.finrank ℝ (LinearMap.ker dfL) = 2
  omega

end JacobianGeneral

/-! ## 4. Ergonomic Specialization to `ℝ⁴ → ℝ²` (`EuclideanSpace ℝ (Fin 4) → ℝ²`) -/

section Euclidean4

local instance instFactFinrankEuclideanFin (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- Standard oriented smooth top volume `n`-form `dx₀ ∧ ⋯ ∧ dx_{n-1}` on
`EuclideanSpace ℝ (Fin n)`. -/
def euclideanVolumeForm (n : ℕ) : SmoothForm (𝓡 n) (EuclideanSpace ℝ (Fin n)) ℝ n :=
  ⟨fun _ ↦ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.orientation.volumeFormL,
    (TauCeti.isSmoothForm_modelSpace_iff.2 contDiff_const).mem_smoothBundleForms⟩

@[simp]
theorem euclideanVolumeForm_apply_basisFun (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    (euclideanVolumeForm n).1 x
      (fun i ↦ (EuclideanSpace.basisFun (Fin n) ℝ i : TangentSpace (𝓡 n) x)) = 1 :=
  Orientation.volumeFormL_apply_orthonormal _ (EuclideanSpace.basisFun (Fin n) ℝ) rfl

theorem euclideanVolumeForm_ne_zero (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    (euclideanVolumeForm n).1 x ≠ 0 := by
  intro h
  have h1 := DFunLike.congr_fun h
    (fun i ↦ (EuclideanSpace.basisFun (Fin n) ℝ i : TangentSpace (𝓡 n) x))
  have h2 := euclideanVolumeForm_apply_basisFun n x
  exact one_ne_zero (h2.symm.trans h1)

/-- Standard volume `4`-form `dx₀ ∧ dx₁ ∧ dx₂ ∧ dx₃` on `ℝ⁴ = EuclideanSpace ℝ (Fin 4)`. -/
abbrev euclidean4VolumeForm : SmoothForm (𝓡 4) (EuclideanSpace ℝ (Fin 4)) ℝ 4 :=
  euclideanVolumeForm 4

theorem euclidean4VolumeForm_ne_zero (x : EuclideanSpace ℝ (Fin 4)) :
    euclidean4VolumeForm.1 x ≠ 0 :=
  euclideanVolumeForm_ne_zero 4 x

/-- Explicit determinant formula `volumeForm ![u, w] = u 0 * w 1 - u 1 * w 0` on `ℝ²`. -/
theorem euclideanPlaneVolumeForm_pair (u w : EuclideanSpace ℝ (Fin 2)) :
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation.volumeForm ![u, w] =
      u 0 * w 1 - u 1 * w 0 := by
  let b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  have hor : b.orientation = (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation := rfl
  rw [b.orientation.volumeForm_robust (EuclideanSpace.basisFun (Fin 2) ℝ) hor, b.det_apply,
    Matrix.det_fin_two]
  simp [b, Module.Basis.toMatrix_apply, EuclideanSpace.basisFun_repr]
  ring

/-- Smooth `i`-th coordinate function `x ↦ x i` on `EuclideanSpace ℝ (Fin n)`. -/
def euclideanCoord {n : ℕ} (i : Fin n) : C^∞⟮𝓡 n, EuclideanSpace ℝ (Fin n); ℝ⟯ :=
  ⟨EuclideanSpace.proj (𝕜 := ℝ) i, (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contMDiff⟩

@[simp]
theorem euclideanCoord_apply {n : ℕ} (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    (euclideanCoord i) x = x i :=
  rfl

@[simp]
theorem fderiv_euclideanCoord_apply {n : ℕ} (i : Fin n) (x v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (euclideanCoord i) x v = v i := by
  change fderiv ℝ (EuclideanSpace.proj (𝕜 := ℝ) i) x v = v i
  rw [(EuclideanSpace.proj (𝕜 := ℝ) i).fderiv]
  rfl

/-- Canonical Jacobian–Poisson structure on `ℝ⁴` induced by a `C^∞` map `f : ℝ⁴ → ℝ²` with respect
to `dx₀ ∧ dx₁ ∧ dx₂ ∧ dx₃` (`euclidean4VolumeForm`) and `dy₀ ∧ dy₁` (`planeAreaForm`). -/
def euclideanJacobianPoisson
    (f : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 2))
    (hf : ContDiff ℝ ∞ f) :
    PoissonStructure (𝓡 4) (EuclideanSpace ℝ (Fin 4)) :=
  jacobianPoisson euclidean4VolumeForm euclidean4VolumeForm_ne_zero planeAreaForm f hf.contMDiff

theorem isUnimodularWithVolume_euclideanJacobianPoisson
    (f : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 2)) (hf : ContDiff ℝ ∞ f) :
    (euclideanJacobianPoisson f hf).IsUnimodularWithVolume euclidean4VolumeForm :=
  isUnimodularWithVolume_jacobianPoisson euclidean4VolumeForm euclidean4VolumeForm_ne_zero
    planeAreaForm f hf.contMDiff

theorem isUnimodularPoisson_euclideanJacobianPoisson
    (f : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 2)) (hf : ContDiff ℝ ∞ f) :
    (euclideanJacobianPoisson f hf).IsUnimodularPoisson :=
  isUnimodularPoisson_jacobianPoisson euclidean4VolumeForm euclidean4VolumeForm_ne_zero
    planeAreaForm f hf.contMDiff

/-- Pointwise evaluation of `{g, h}_{π_f} x` on `ℝ⁴` as
`(dg ∧ dh ∧ f^* planeAreaForm)_x (e₀, e₁, e₂, e₃)`, expanded explicitly in directional derivatives
along the standard orthonormal basis `e_i` of `ℝ⁴`. -/
theorem euclideanJacobianPoisson_bracket_apply
    (f : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 2)) (hf : ContDiff ℝ ∞ f)
    (g h : C^∞⟮𝓡 4, EuclideanSpace ℝ (Fin 4); ℝ⟯) (x : EuclideanSpace ℝ (Fin 4)) :
    ((euclideanJacobianPoisson f hf).bracket g h) x =
      let dg := fun i : Fin 4 ↦ fderiv ℝ g x (EuclideanSpace.basisFun (Fin 4) ℝ i)
      let dh := fun i : Fin 4 ↦ fderiv ℝ h x (EuclideanSpace.basisFun (Fin 4) ℝ i)
      let J := fun i j : Fin 4 ↦
        (fderiv ℝ f x (EuclideanSpace.basisFun (Fin 4) ℝ i)) 0 *
          (fderiv ℝ f x (EuclideanSpace.basisFun (Fin 4) ℝ j)) 1 -
        (fderiv ℝ f x (EuclideanSpace.basisFun (Fin 4) ℝ i)) 1 *
          (fderiv ℝ f x (EuclideanSpace.basisFun (Fin 4) ℝ j)) 0
      (dg 0 * dh 1 - dg 1 * dh 0) * J 2 3 -
      (dg 0 * dh 2 - dg 2 * dh 0) * J 1 3 +
      (dg 0 * dh 3 - dg 3 * dh 0) * J 1 2 +
      (dg 1 * dh 2 - dg 2 * dh 1) * J 0 3 -
      (dg 1 * dh 3 - dg 3 * dh 1) * J 0 2 +
      (dg 2 * dh 3 - dg 3 * dh 2) * J 0 1 := by
  dsimp only
  let e : Fin 4 → TangentSpace (𝓡 4) x :=
    fun i ↦ (EuclideanSpace.basisFun (Fin 4) ℝ i : TangentSpace (𝓡 4) x)
  have htop := DFunLike.congr_fun (congrFun (congrArg Subtype.val
    (funSMulₗ_bracket_jacobianPoisson euclidean4VolumeForm euclidean4VolumeForm_ne_zero
      planeAreaForm f hf.contMDiff g h)) x) e
  rw [SmoothForm.coe_funSMulₗ, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    euclideanVolumeForm_apply_basisFun 4 x, mul_one] at htop
  have hassoc := SmoothForm.wedge_assoc_apply (SmoothBivector.diffOneForm g)
    (SmoothBivector.diffOneForm h) (SmoothForm.mpullback f hf.contMDiff planeAreaForm) x e
  have hce : (e ∘ Fin.cast (Nat.add_assoc 1 1 2).symm) = e := funext fun _ ↦ rfl
  rw [hce] at hassoc
  change ((jacobianPoisson euclidean4VolumeForm euclidean4VolumeForm_ne_zero
    planeAreaForm f hf.contMDiff).bracket g h) x = _
  rw [htop, hassoc]
  have he4 : e = ![e 0, e 1, e 2, e 3] := by funext i; fin_cases i <;> rfl
  rw [he4, SmoothForm.coe_wedge, RoughForm.wedge_def, RoughForm.wedgeWith_apply',
    pairedWedge_one_three_apply]
  simp only [SmoothForm.coe_wedge, RoughForm.wedge_def, RoughForm.wedgeWith_apply',
    pairedWedge_one_two_apply, SmoothBivector.diffOneForm_apply]
  have hmf_scalar (u : C^∞⟮𝓡 4, EuclideanSpace ℝ (Fin 4); ℝ⟯) (i : Fin 4) :
      mvfderiv (𝓡 4) u x (e i) = fderiv ℝ u x (EuclideanSpace.basisFun (Fin 4) ℝ i) := by
    rw [mvfderiv_apply_eq_mfderiv_apply, mfderiv_eq_fderiv]
    rfl
  have hmf (v : TangentSpace (𝓡 4) x) :
      (mfderiv (𝓡 4) (𝓡 2) f x v : EuclideanSpace ℝ (Fin 2)) = fderiv ℝ f x v := by
    rw [mfderiv_eq_fderiv]
    rfl
  have hpul (i j : Fin 4) :
      (SmoothForm.mpullback f hf.contMDiff planeAreaForm).1 x ![e i, e j] =
        (fderiv ℝ f x (EuclideanSpace.basisFun (Fin 4) ℝ i)) 0 *
          (fderiv ℝ f x (EuclideanSpace.basisFun (Fin 4) ℝ j)) 1 -
        (fderiv ℝ f x (EuclideanSpace.basisFun (Fin 4) ℝ i)) 1 *
          (fderiv ℝ f x (EuclideanSpace.basisFun (Fin 4) ℝ j)) 0 := by
    rw [SmoothForm.mpullback_apply, planeAreaForm_apply]
    simp_rw [hmf]
    have hpair : (fun k : Fin 2 ↦ fderiv ℝ f x (![e i, e j] k)) =
        ![fderiv ℝ f x (EuclideanSpace.basisFun (Fin 4) ℝ i),
          fderiv ℝ f x (EuclideanSpace.basisFun (Fin 4) ℝ j)] := by
      funext k; fin_cases k <;> rfl
    rw [hpair, euclideanPlaneVolumeForm_pair]
  simp only [hmf_scalar, hpul]
  ring

/-- Explicit coordinate bracket `{x₂, x₃}_{π_f} x = ∂_{x₀} f₀ * ∂_{x₁} f₁ - ∂_{x₁} f₀ * ∂_{x₀} f₁`
on `ℝ⁴` (0-indexed `Fin 4`, corresponding to `{x₃, x₄}_{π_f}` in 1-indexed coordinates). -/
theorem euclideanJacobianPoisson_bracket_coord_two_three
    (f : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 2)) (hf : ContDiff ℝ ∞ f)
    (x : EuclideanSpace ℝ (Fin 4)) :
    ((euclideanJacobianPoisson f hf).bracket (euclideanCoord 2) (euclideanCoord 3)) x =
      (fderiv ℝ f x (EuclideanSpace.basisFun (Fin 4) ℝ 0)) 0 *
        (fderiv ℝ f x (EuclideanSpace.basisFun (Fin 4) ℝ 1)) 1 -
      (fderiv ℝ f x (EuclideanSpace.basisFun (Fin 4) ℝ 1)) 0 *
        (fderiv ℝ f x (EuclideanSpace.basisFun (Fin 4) ℝ 0)) 1 := by
  rw [euclideanJacobianPoisson_bracket_apply]
  have hd (k i : Fin 4) :
      fderiv ℝ (euclideanCoord k) x (EuclideanSpace.basisFun (Fin 4) ℝ i) =
        if i = k then 1 else 0 := by
    rw [fderiv_euclideanCoord_apply]
    simp [EuclideanSpace.basisFun_apply, eq_comm]
  dsimp only
  simp only [hd]
  norm_num
  ring

/-- Explicit coordinate bracket `{x₁, x₂}_{π_f} x = ∂_{x₀} f₀ * ∂_{x₃} f₁ - ∂_{x₃} f₀ * ∂_{x₀} f₁`
on `ℝ⁴` (corresponding to `{y₂, y₃}_{π_f}` for `(y₁, y₂, y₃, t)` in Gate 4 / Eq. (2)). -/
theorem euclideanJacobianPoisson_bracket_coord_one_two
    (f : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 2)) (hf : ContDiff ℝ ∞ f)
    (x : EuclideanSpace ℝ (Fin 4)) :
    ((euclideanJacobianPoisson f hf).bracket (euclideanCoord 1) (euclideanCoord 2)) x =
      (fderiv ℝ f x (EuclideanSpace.basisFun (Fin 4) ℝ 0)) 0 *
        (fderiv ℝ f x (EuclideanSpace.basisFun (Fin 4) ℝ 3)) 1 -
      (fderiv ℝ f x (EuclideanSpace.basisFun (Fin 4) ℝ 3)) 0 *
        (fderiv ℝ f x (EuclideanSpace.basisFun (Fin 4) ℝ 0)) 1 := by
  rw [euclideanJacobianPoisson_bracket_apply]
  have hd (k i : Fin 4) :
      fderiv ℝ (euclideanCoord k) x (EuclideanSpace.basisFun (Fin 4) ℝ i) =
        if i = k then 1 else 0 := by
    rw [fderiv_euclideanCoord_apply]
    simp [EuclideanSpace.basisFun_apply, eq_comm]
  dsimp only
  simp only [hd]
  norm_num
  ring

/-- Explicit coordinate bracket `{x₀, x₁}_{π_f} x = ∂_{x₂} f₀ * ∂_{x₃} f₁ - ∂_{x₃} f₀ * ∂_{x₂} f₁`
on `ℝ⁴`. -/
theorem euclideanJacobianPoisson_bracket_coord_zero_one
    (f : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 2)) (hf : ContDiff ℝ ∞ f)
    (x : EuclideanSpace ℝ (Fin 4)) :
    ((euclideanJacobianPoisson f hf).bracket (euclideanCoord 0) (euclideanCoord 1)) x =
      (fderiv ℝ f x (EuclideanSpace.basisFun (Fin 4) ℝ 2)) 0 *
        (fderiv ℝ f x (EuclideanSpace.basisFun (Fin 4) ℝ 3)) 1 -
      (fderiv ℝ f x (EuclideanSpace.basisFun (Fin 4) ℝ 3)) 0 *
        (fderiv ℝ f x (EuclideanSpace.basisFun (Fin 4) ℝ 2)) 1 := by
  rw [euclideanJacobianPoisson_bracket_apply]
  have hd (k i : Fin 4) :
      fderiv ℝ (euclideanCoord k) x (EuclideanSpace.basisFun (Fin 4) ℝ i) =
        if i = k then 1 else 0 := by
    rw [fderiv_euclideanCoord_apply]
    simp [EuclideanSpace.basisFun_apply, eq_comm]
  dsimp only
  simp only [hd]
  norm_num
  ring

end Euclidean4

end S4TuringPoisson
