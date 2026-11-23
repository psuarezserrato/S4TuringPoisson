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
public import Mathlib.RingTheory.Derivation.Basic
public import TauCeti.Geometry.Manifold.ContMDiff.Log
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Covector
public import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Interior
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
public import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
public import TauCeti.Geometry.Manifold.VectorField.LieBracket
public import TauCeti.Geometry.Manifold.VectorField.Regularity
public import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# Smooth Poisson Bivectors, Koszul 1-Form Brackets, and Weinstein's Modular Class (M1.1)

This module formalizes Milestone M1.1 of `S4TuringPoisson`, developing the intrinsic Poisson
geometry and modular theory on smooth manifolds required for *"Hamiltonian and Turing complete
flows on smooth 4-manifolds"* (`S4TCdiffeo-Aug-2026.tex`, §"Notions from Poisson geometry" and
§"Unimodular Poisson structures"):

1. **Top-Form Division & Sub-Top-Form Contraction Duality**:
   - `divVolume`: smooth scalar ratio `Φ / Ω : C^∞⟮I, M; ℝ⟯` of any smooth top form `Φ` against a
     nowhere-vanishing smooth top form `Ω` (`Φ = SmoothForm.funSMulₗ (divVolume Ω hΩ Φ) Ω`).
   - `apply_smul_topForm_eq_wedge_interior`: on an `(m + 1)`-manifold, for every vector field `V`,
     `1`-form `α`, and `(m + 1)`-form `Ω`, `(α x ![V x]) * Ω x v = (α ∧ ι_V Ω) x (v ∘ ...)`.

2. **Smooth Bivectors & Poisson Brackets (`SmoothBivector`, `PoissonStructure`)**:
   - `SmoothBivector I M`: smooth skew-adjoint cotangent-to-tangent bundle anchor map
     `#_π : T^*M → TM` (`β (#_π α) = π(α, β)`), inducing Hamiltonian vector fields
     `X_h = - #_π(dh)` (`X_h(g) = {g, h}_π`) and smooth ℝ-bilinear skew-symmetric Leibniz brackets
     `{·, ·}_π` (`SmoothBivector.bracket`, bundled linearly as `SmoothBivector.bracketₗ`).
   - `PoissonStructure I M`: `SmoothBivector I M` satisfying the Jacobi identity, together with
     `[X_g, X_h] = -X_{{g, h}}`, Casimir functions, rank at a point, and smooth Poisson maps.

3. **Koszul 1-Form Bracket & Lichnerowicz 1-Cocycles**:
   - `SmoothBivector.koszulBracket`: `[α, β]_π = 𝓛_{#_π α} β - 𝓛_{#_π β} α - d(π(α, β))` on
     `SmoothForm I M ℝ 1`, proving skew-symmetry and `[df, dg]_π = d{f, g}_π`.
   - `PoissonStructure.IsLichnerowiczOneCocycle` and `CohomologousOneCocycle`: Poisson derivations
     of `C^∞(M)`, exactness of Hamiltonian derivations `X_u` (`d_π² = 0` in degree `0 → 1 → 2`),
     and equivalence relation defining the first Poisson cohomology class `[D] ∈ H¹(M, π)`.

4. **Weinstein's Modular Vector Field & Density Rescaling Invariance**:
   - `PoissonStructure.modularDerivation`: Weinstein's modular derivation `Y^Ω` defined by
     `𝓛_{X_h} Ω = (Y^Ω h) • Ω` (and `d(ι_{X_h} Ω) = (Y^Ω h) • Ω` via Cartan's magic formula on
     closed top forms), proved to be both a `Derivation ℝ C^∞(M) C^∞(M)` and a Lichnerowicz
     1-cocycle (`Y^Ω {g, h}_π = {Y^Ω g, h}_π + {g, Y^Ω h}_π`).
   - `PoissonStructure.modularDerivation_funSMul`: under positive smooth density rescaling
     `Ω ↦ a • Ω` (`a > 0`), `Y^{aΩ} = Y^Ω - X_{log a}`, establishing invariance of the modular
     cohomology class `[Y^Ω] ∈ H¹(M, π)`.
   - `PoissonStructure.IsUnimodularPoisson` and Weinstein's characterization: `[Y^Ω] = 0` iff
     there exists a positive rescaling `e^u • Ω` invariant under all Hamiltonian vector fields.
-/

@[expose] public section

noncomputable section

open Bundle Filter Function Module Set TauCeti TopologicalSpace VectorField
open scoped ContDiff Manifold Topology

namespace S4TuringPoisson

/-! ## 1. Top-Form Division and Sub-Top-Form Contraction Identities -/

theorem map_vecCons_add_slot0 {V F : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] {m : ℕ}
    (A : V [⋀^Fin (m + 1)]→L[ℝ] F) (u₁ u₂ : V) (w : Fin m → V) :
    A (Matrix.vecCons (u₁ + u₂) w) = A (Matrix.vecCons u₁ w) + A (Matrix.vecCons u₂ w) := by
  have h (z : V) : Matrix.vecCons z w = Function.update (Matrix.vecCons 0 w) 0 z := by
    funext j; cases j using Fin.cases <;> simp
  rw [h (u₁ + u₂), h u₁, h u₂]
  exact A.map_update_add (Matrix.vecCons 0 w) 0 u₁ u₂

theorem map_vecCons_smul_slot0 {V F : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] {m : ℕ}
    (A : V [⋀^Fin (m + 1)]→L[ℝ] F) (c : ℝ) (u : V) (w : Fin m → V) :
    A (Matrix.vecCons (c • u) w) = c • A (Matrix.vecCons u w) := by
  have h (z : V) : Matrix.vecCons z w = Function.update (Matrix.vecCons 0 w) 0 z := by
    funext j; cases j using Fin.cases <;> simp
  rw [h (c • u), h u]
  exact A.map_update_smul (Matrix.vecCons 0 w) 0 c u

section TopFormDivision

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Given a nowhere-vanishing smooth top form `Ω` on an `n`-manifold `M` and any smooth `n`-form
`Φ`, there is a unique smooth function `f : C^∞⟮I, M; ℝ⟯` such that `Φ = f • Ω`. -/
theorem existsUnique_contMDiffMap_funSMul_topForm {n : ℕ} [hdim : HasFinrank E n]
    [FiniteDimensional ℝ E] (Ω : SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0)
    (Φ : SmoothForm I M ℝ n) :
    ∃! f : C^∞⟮I, M; ℝ⟯, SmoothForm.funSMulₗ f Ω = Φ := by
  let bE : Module.Basis (Fin n) ℝ E := Module.finBasisOfFinrankEq ℝ E hdim.finrank_eq
  let frameAt (x₀ y : M) : Fin n → TangentSpace I y :=
    fun i ↦ (trivializationAt E (TangentSpace I) x₀).symmL ℝ y (bE i)
  let basisAt (x : M) : Module.Basis (Fin n) ℝ (TangentSpace I x) :=
    (trivializationAt E (TangentSpace I) x).basisAt bE
      (FiberBundle.mem_baseSet_trivializationAt' x)
  let rawRatio (x : M) : ℝ :=
    Φ.1 x (frameAt x x) / Ω.1 x (frameAt x x)
  have hframe_eq_basis (x : M) : frameAt x x = ⇑(basisAt x) :=
    funext fun i ↦
      (TauCeti.Manifold.basisAt_apply bE (FiberBundle.mem_baseSet_trivializationAt' x) i).symm
  have hΩ_ne (x : M) : Ω.1 x (frameAt x x) ≠ 0 := by
    rw [hframe_eq_basis x]
    exact ((Ω.1 x).map_basis_ne_zero_iff (basisAt x)).mpr (hΩ x)
  have hpoint (x : M) : rawRatio x • Ω.1 x = Φ.1 x := by
    ext v
    rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul,
      ContinuousAlternatingMap.apply_eq_det_mul (Ω.1 x) (basisAt x) v,
      ContinuousAlternatingMap.apply_eq_det_mul (Φ.1 x) (basisAt x) v]
    dsimp only [rawRatio]
    rw [hframe_eq_basis x]
    have hne : Ω.1 x (basisAt x) ≠ 0 := ((Ω.1 x).map_basis_ne_zero_iff (basisAt x)).mpr (hΩ x)
    field_simp [hne]
  have hsmooth : ContMDiff I 𝓘(ℝ) ∞ rawRatio := by
    intro x₀
    have hΦ_eval : ContMDiffAt I 𝓘(ℝ) ∞ (fun y ↦ Φ.1 y (frameAt x₀ y)) x₀ :=
      (isSmoothForm_iff_forall_contMDiffAt_trivializationAt_apply.mp Φ.isSmoothForm) x₀ bE
    have hΩ_eval : ContMDiffAt I 𝓘(ℝ) ∞ (fun y ↦ Ω.1 y (frameAt x₀ y)) x₀ :=
      (isSmoothForm_iff_forall_contMDiffAt_trivializationAt_apply.mp Ω.isSmoothForm) x₀ bE
    have hdiv : ContMDiffAt I 𝓘(ℝ) ∞
        (fun y ↦ Φ.1 y (frameAt x₀ y) / Ω.1 y (frameAt x₀ y)) x₀ :=
      hΦ_eval.div₀ hΩ_eval (hΩ_ne x₀)
    refine hdiv.congr_of_eventuallyEq ?_
    filter_upwards [hΩ_eval.continuousAt.eventually_ne (hΩ_ne x₀)] with y hy
    have heval := DFunLike.congr_fun (hpoint y) (frameAt x₀ y)
    simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul] at heval
    exact eq_div_of_mul_eq hy heval
  let ratioMap : C^∞⟮I, M; ℝ⟯ := ⟨rawRatio, hsmooth⟩
  refine ⟨ratioMap, ?_, ?_⟩
  · apply Subtype.ext
    rw [SmoothForm.coe_funSMulₗ]
    exact funext hpoint
  · intro g hg
    ext x
    have hgx : g x • Ω.1 x = rawRatio x • Ω.1 x := by
      have hg1 := congrFun (congrArg Subtype.val hg) x
      rw [SmoothForm.coe_funSMulₗ] at hg1
      exact hg1.trans (hpoint x).symm
    exact smul_left_injective ℝ (hΩ x) hgx

/-- Smooth scalar quotient `Φ / Ω : C^∞⟮I, M; ℝ⟯` of a smooth top form `Φ` by a nowhere-vanishing
smooth top form `Ω`. -/
def divVolume {n : ℕ} [HasFinrank E n] [FiniteDimensional ℝ E]
    (Ω : SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0) (Φ : SmoothForm I M ℝ n) :
    C^∞⟮I, M; ℝ⟯ :=
  (existsUnique_contMDiffMap_funSMul_topForm Ω hΩ Φ).choose

@[simp]
theorem funSMulₗ_divVolume {n : ℕ} [HasFinrank E n] [FiniteDimensional ℝ E]
    (Ω : SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0) (Φ : SmoothForm I M ℝ n) :
    SmoothForm.funSMulₗ (divVolume Ω hΩ Φ) Ω = Φ :=
  (existsUnique_contMDiffMap_funSMul_topForm Ω hΩ Φ).choose_spec.1

theorem divVolume_apply_smul {n : ℕ} [HasFinrank E n] [FiniteDimensional ℝ E]
    (Ω : SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0) (Φ : SmoothForm I M ℝ n) (x : M) :
    (divVolume Ω hΩ Φ) x • Ω.1 x = Φ.1 x := by
  have h := congrFun (congrArg Subtype.val (funSMulₗ_divVolume Ω hΩ Φ)) x
  rwa [SmoothForm.coe_funSMulₗ] at h

theorem eq_divVolume_iff {n : ℕ} [HasFinrank E n] [FiniteDimensional ℝ E]
    (Ω : SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0) (Φ : SmoothForm I M ℝ n)
    (g : C^∞⟮I, M; ℝ⟯) :
    g = divVolume Ω hΩ Φ ↔ SmoothForm.funSMulₗ g Ω = Φ :=
  ⟨fun h ↦ h ▸ funSMulₗ_divVolume Ω hΩ Φ,
    (existsUnique_contMDiffMap_funSMul_topForm Ω hΩ Φ).choose_spec.2 g⟩

theorem eq_divVolume_iff_forall {n : ℕ} [HasFinrank E n] [FiniteDimensional ℝ E]
    (Ω : SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0) (Φ : SmoothForm I M ℝ n)
    (g : C^∞⟮I, M; ℝ⟯) :
    g = divVolume Ω hΩ Φ ↔ ∀ x : M, g x • Ω.1 x = Φ.1 x := by
  rw [eq_divVolume_iff, Subtype.ext_iff, SmoothForm.coe_funSMulₗ, funext_iff]

@[simp]
theorem divVolume_zero {n : ℕ} [HasFinrank E n] [FiniteDimensional ℝ E]
    (Ω : SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0) :
    divVolume Ω hΩ 0 = 0 :=
  ((eq_divVolume_iff_forall Ω hΩ 0 0).mpr fun _ ↦ zero_smul ℝ _).symm

@[simp]
theorem divVolume_self {n : ℕ} [HasFinrank E n] [FiniteDimensional ℝ E]
    (Ω : SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0) :
    divVolume Ω hΩ Ω = 1 :=
  ((eq_divVolume_iff_forall Ω hΩ Ω 1).mpr fun _ ↦ one_smul ℝ _).symm

@[simp]
theorem divVolume_funSMulₗ {n : ℕ} [HasFinrank E n] [FiniteDimensional ℝ E]
    (Ω : SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0) (g : C^∞⟮I, M; ℝ⟯) :
    divVolume Ω hΩ (SmoothForm.funSMulₗ g Ω) = g :=
  ((eq_divVolume_iff Ω hΩ _ g).mpr rfl).symm

theorem divVolume_add {n : ℕ} [HasFinrank E n] [FiniteDimensional ℝ E]
    (Ω : SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0) (Φ Ψ : SmoothForm I M ℝ n) :
    divVolume Ω hΩ (Φ + Ψ) = divVolume Ω hΩ Φ + divVolume Ω hΩ Ψ := by
  symm
  rw [eq_divVolume_iff_forall]
  intro x
  rw [ContMDiffMap.coe_add, Pi.add_apply, add_smul, divVolume_apply_smul, divVolume_apply_smul,
    SmoothForm.add_toRoughForm, Pi.add_apply]

theorem divVolume_smul {n : ℕ} [HasFinrank E n] [FiniteDimensional ℝ E]
    (Ω : SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0) (c : ℝ) (Φ : SmoothForm I M ℝ n) :
    divVolume Ω hΩ (c • Φ) = c • divVolume Ω hΩ Φ := by
  symm
  rw [eq_divVolume_iff_forall]
  intro x
  rw [ContMDiffMap.coe_smul, Pi.smul_apply, smul_assoc, divVolume_apply_smul]
  rfl

theorem divVolume_neg {n : ℕ} [HasFinrank E n] [FiniteDimensional ℝ E]
    (Ω : SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0) (Φ : SmoothForm I M ℝ n) :
    divVolume Ω hΩ (-Φ) = -divVolume Ω hΩ Φ := by
  rw [← neg_one_smul ℝ Φ, divVolume_smul, neg_one_smul]

theorem divVolume_sub {n : ℕ} [HasFinrank E n] [FiniteDimensional ℝ E]
    (Ω : SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0) (Φ Ψ : SmoothForm I M ℝ n) :
    divVolume Ω hΩ (Φ - Ψ) = divVolume Ω hΩ Φ - divVolume Ω hΩ Ψ := by
  rw [sub_eq_add_neg, divVolume_add, divVolume_neg, ← sub_eq_add_neg]

theorem funSMulₗ_ne_zero {k : ℕ} {Ω : SmoothForm I M ℝ k} (hΩ : ∀ x : M, Ω.1 x ≠ 0)
    {a : C^∞⟮I, M; ℝ⟯} (ha : ∀ x : M, a x ≠ 0) (x : M) :
    (SmoothForm.funSMulₗ a Ω).1 x ≠ 0 := by
  rw [SmoothForm.coe_funSMulₗ]
  exact smul_ne_zero (ha x) (hΩ x)

omit [IsManifold I ∞ M] in
/-- Fundamental top-form contraction identity: on an `(m + 1)`-dimensional manifold, for any vector
field `V`, `1`-form `α`, and `(m + 1)`-form `Ω`, evaluating `α` on `V` scales `Ω` by the wedge
`α ∧ ι_V Ω` (`α ∧ Ω = 0` in degree `m + 2 > m + 1`). -/
theorem apply_smul_topForm_eq_wedge_interior {m : ℕ} [hdim : HasFinrank E (m + 1)]
    [FiniteDimensional ℝ E] (V : (x : M) → TangentSpace I x) (α : RoughForm I M ℝ 1)
    (Ω : RoughForm I M ℝ (m + 1)) (x : M) (v : Fin (m + 1) → TangentSpace I x) :
    α x ![V x] * Ω x v =
      (α.wedge (Ω.interior V)) x (v ∘ Fin.cast (Nat.add_comm 1 m)) := by
  have htop : (α.wedge Ω) x = 0 := by
    refine ContinuousAlternatingMap.eq_zero_of_finrank_lt ((α.wedge Ω) x) ?_
    change Module.finrank ℝ E < Fintype.card (Fin (1 + (m + 1)))
    rw [hdim.finrank_eq, Fintype.card_fin]
    omega
  have hint := RoughForm.interior_wedge_apply (k := 0) (l := m) V α Ω x
    (v ∘ Fin.cast (Nat.add_comm 1 m))
  have hzero : (α.wedge Ω).interior V x (v ∘ Fin.cast (Nat.add_comm 1 m)) = 0 := by
    rw [RoughForm.interior_apply, htop]
    rfl
  rw [hzero] at hint
  have hcast :
      ((v ∘ Fin.cast (Nat.add_comm 1 m)) ∘ Fin.cast (show 0 + (m + 1) = 0 + 1 + m by omega)) =
        (v ∘ Fin.cast (zero_add (m + 1))) := by
    funext i
    simp [Function.comp_apply]
  have hfirst : ((α.interior V).wedge Ω) x
      ((v ∘ Fin.cast (Nat.add_comm 1 m)) ∘ Fin.cast (show 0 + (m + 1) = 0 + 1 + m by omega)) =
      α x ![V x] * Ω x v := by
    rw [hcast]
    have h0 : α.interior V = RoughForm.ofFunction I (fun y ↦ α y ![V y]) := by
      rw [RoughForm.eq_ofFunction (α.interior V)]
      congr 1
      funext y
      rw [RoughForm.interior_apply]
      congr 1
      ext i
      fin_cases i
      rfl
    rw [h0, RoughForm.ofFunction_wedge_apply]
    simp
  have hpow : (-1 : ℝ) ^ (0 + 1) = -1 := by norm_num
  rw [hfirst, hpow, neg_one_smul] at hint
  linarith

end TopFormDivision

/-! ## 2. Smooth Bivectors, Anchor Map, Hamiltonian Vector Fields, and Poisson Brackets -/

/-- A **smooth bivector** `π ∈ 𝔛²(M)` on a smooth manifold `M`, represented intrinsically by its
smooth skew-adjoint cotangent-to-tangent bundle anchor map `#_π : T^*M → TM` satisfying
`β (#_π α) = π(α, β)` (`S4TCdiffeo-Aug-2026.tex`, line 355). -/
structure SmoothBivector {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] where
  /-- Fiberwise continuous linear anchor map `#_π : T_x^* M → T_x M`. -/
  anchor : (x : M) → (TangentSpace I x →L[ℝ] ℝ) →L[ℝ] TangentSpace I x
  /-- Skew-adjointness `β (#_π α) = - α (#_π β)`. -/
  anchor_skew :
    ∀ (x : M) (α β : TangentSpace I x →L[ℝ] ℝ), β (anchor x α) = -α (anchor x β)
  /-- Smoothness: `#_π` sends every smooth `1`-form to a smooth vector field on `M`. -/
  contMDiff_anchor :
    ∀ α : SmoothForm I M ℝ 1,
      ContMDiff I I.tangent ∞
        (fun x ↦ (⟨x, anchor x (SmoothForm.degreeOneEquiv α x)⟩ : TangentBundle I M))

namespace SmoothBivector

section General

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (B : SmoothBivector I M)

/-- Pointwise bivector pairing `π_x(α, β) := β (#_π α)` (`S4TCdiffeo-Aug-2026.tex`, line 355). -/
def bivector (x : M) (α β : TangentSpace I x →L[ℝ] ℝ) : ℝ :=
  β (B.anchor x α)

@[simp]
theorem bivector_apply (x : M) (α β : TangentSpace I x →L[ℝ] ℝ) :
    B.bivector x α β = β (B.anchor x α) :=
  rfl

theorem bivector_skew (x : M) (α β : TangentSpace I x →L[ℝ] ℝ) :
    B.bivector x α β = -B.bivector x β α :=
  B.anchor_skew x α β

@[simp]
theorem bivector_self (x : M) (α : TangentSpace I x →L[ℝ] ℝ) :
    B.bivector x α α = 0 := by
  linarith [B.bivector_skew x α α]

/-- Rank of the bivector `B` at a point `x : M`, defined as the dimension of `Im(#_{π, x})`. -/
def rankAt (x : M) : ℕ :=
  Module.finrank ℝ (LinearMap.range (B.anchor x).toLinearMap)

/-- Smooth vector field `#_π(α)` associated to a smooth `1`-form `α ∈ Ω¹(M)`. -/
def anchorVectorField (α : SmoothForm I M ℝ 1) (x : M) : TangentSpace I x :=
  B.anchor x (SmoothForm.degreeOneEquiv α x)

theorem contMDiff_anchorVectorField (α : SmoothForm I M ℝ 1) :
    ContMDiff I I.tangent ∞
      (fun x ↦ (⟨x, B.anchorVectorField α x⟩ : TangentBundle I M)) :=
  B.contMDiff_anchor α

theorem mdifferentiable_anchorVectorField (α : SmoothForm I M ℝ 1) :
    MDifferentiable I I.tangent
      (fun x ↦ (⟨x, B.anchorVectorField α x⟩ : TangentBundle I M)) :=
  (B.contMDiff_anchorVectorField α).mdifferentiable (by simp)

@[simp]
theorem anchorVectorField_zero :
    B.anchorVectorField (0 : SmoothForm I M ℝ 1) = 0 := by
  funext x
  simp [anchorVectorField]

theorem anchorVectorField_add (α β : SmoothForm I M ℝ 1) :
    B.anchorVectorField (α + β) = B.anchorVectorField α + B.anchorVectorField β := by
  funext x
  simp [anchorVectorField]

theorem anchorVectorField_neg (α : SmoothForm I M ℝ 1) :
    B.anchorVectorField (-α) = -B.anchorVectorField α := by
  funext x
  simp [anchorVectorField]

theorem anchorVectorField_smul (c : ℝ) (α : SmoothForm I M ℝ 1) :
    B.anchorVectorField (c • α) = c • B.anchorVectorField α := by
  funext x
  simp [anchorVectorField]

theorem anchorVectorField_funSMulₗ (f : C^∞⟮I, M; ℝ⟯) (α : SmoothForm I M ℝ 1) (x : M) :
    B.anchorVectorField (SmoothForm.funSMulₗ f α) x = f x • B.anchorVectorField α x := by
  have heq : SmoothForm.degreeOneEquiv (SmoothForm.funSMulₗ f α) x =
      f x • SmoothForm.degreeOneEquiv α x := by
    ext v
    rw [SmoothForm.degreeOneEquiv_apply_apply, SmoothForm.coe_funSMulₗ,
      ContinuousAlternatingMap.smul_apply, _root_.smul_apply,
      SmoothForm.degreeOneEquiv_apply_apply]
  simp [anchorVectorField, heq]

/-- Smooth scalar pairing `π(α, β) ∈ C^∞(M)` of two smooth `1`-forms `α, β ∈ Ω¹(M)`. -/
def pairOneForms (α β : SmoothForm I M ℝ 1) : C^∞⟮I, M; ℝ⟯ :=
  ⟨fun x ↦ B.bivector x (SmoothForm.degreeOneEquiv α x) (SmoothForm.degreeOneEquiv β x), by
    intro x
    have h := ((SmoothForm.degreeOneEquiv β).contMDiff x).clm_bundle_apply
      (B.contMDiff_anchorVectorField α x)
    rw [contMDiffAt_section_iff] at h
    simpa only [Trivial.eq_trivialization M ℝ, Trivial.trivialization_apply, bivector,
      anchorVectorField] using h⟩

@[simp]
theorem pairOneForms_apply (α β : SmoothForm I M ℝ 1) (x : M) :
    (B.pairOneForms α β) x =
      B.bivector x (SmoothForm.degreeOneEquiv α x) (SmoothForm.degreeOneEquiv β x) :=
  rfl

theorem pairOneForms_skew (α β : SmoothForm I M ℝ 1) :
    B.pairOneForms α β = -B.pairOneForms β α := by
  ext x
  exact B.bivector_skew x _ _

@[simp]
theorem pairOneForms_self (α : SmoothForm I M ℝ 1) :
    B.pairOneForms α α = 0 := by
  ext x
  exact B.bivector_self x _

/-- Exterior derivative `df ∈ Ω¹(M)` of a smooth scalar function `f : C^∞⟮I, M; ℝ⟯`. -/
def diffOneForm (f : C^∞⟮I, M; ℝ⟯) : SmoothForm I M ℝ 1 :=
  mextDerivₗ I 0 (SmoothForm.ofFunction f)

@[simp]
theorem degreeOneEquiv_diffOneForm (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    SmoothForm.degreeOneEquiv (diffOneForm f) x = mvfderiv I f x := by
  rw [diffOneForm, SmoothForm.degreeOneEquiv_mextDerivₗ, SmoothForm.ofFunction_apply_zero]

@[simp]
theorem diffOneForm_apply (f : C^∞⟮I, M; ℝ⟯) (x : M) (v : TangentSpace I x) :
    (diffOneForm f).1 x ![v] = mvfderiv I f x v := by
  rw [← SmoothForm.degreeOneEquiv_apply_apply_vec, degreeOneEquiv_diffOneForm]

theorem isClosed_diffOneForm (f : C^∞⟮I, M; ℝ⟯) : (diffOneForm f).IsClosed :=
  SmoothForm.isClosed_mextDerivₗ _

/-- **Hamiltonian vector field** `X_h := - #_π(dh)` of a smooth function `h ∈ C^∞(M)`, satisfying
`X_h(g) = dg(X_h) = π(dg, dh) = {g, h}_π` (`S4TCdiffeo-Aug-2026.tex`, line 349). -/
def hamiltonianVectorField (h : C^∞⟮I, M; ℝ⟯) (x : M) : TangentSpace I x :=
  -B.anchor x (mvfderiv I h x)

theorem hamiltonianVectorField_eq_neg_anchorVectorField (h : C^∞⟮I, M; ℝ⟯) :
    B.hamiltonianVectorField h = -B.anchorVectorField (diffOneForm h) := by
  funext x
  simp [hamiltonianVectorField, anchorVectorField]

theorem contMDiff_hamiltonianVectorField (h : C^∞⟮I, M; ℝ⟯) :
    ContMDiff I I.tangent ∞
      (fun x ↦ (⟨x, B.hamiltonianVectorField h x⟩ : TangentBundle I M)) := by
  have heq : B.hamiltonianVectorField h = B.anchorVectorField (-diffOneForm h) := by
    rw [anchorVectorField_neg, ← hamiltonianVectorField_eq_neg_anchorVectorField]
  rw [heq]
  exact B.contMDiff_anchorVectorField (-diffOneForm h)

theorem mdifferentiable_hamiltonianVectorField (h : C^∞⟮I, M; ℝ⟯) :
    MDifferentiable I I.tangent
      (fun x ↦ (⟨x, B.hamiltonianVectorField h x⟩ : TangentBundle I M)) :=
  (B.contMDiff_hamiltonianVectorField h).mdifferentiable (by simp)

@[simp]
theorem hamiltonianVectorField_zero :
    B.hamiltonianVectorField (0 : C^∞⟮I, M; ℝ⟯) = 0 := by
  funext x
  simp [hamiltonianVectorField]

@[simp]
theorem hamiltonianVectorField_const (c : ℝ) :
    B.hamiltonianVectorField (ContMDiffMap.C c : C^∞⟮I, M; ℝ⟯) = 0 := by
  funext x
  have hc : ⇑(ContMDiffMap.C c : C^∞⟮I, M; ℝ⟯) = (fun _ : M ↦ c) := rfl
  rw [hamiltonianVectorField, hc, mvfderiv_const, map_zero, neg_zero, Pi.zero_apply]

theorem hamiltonianVectorField_add (g h : C^∞⟮I, M; ℝ⟯) :
    B.hamiltonianVectorField (g + h) = B.hamiltonianVectorField g + B.hamiltonianVectorField h := by
  funext x
  have hg : MDifferentiableAt I 𝓘(ℝ) g x := g.contMDiff.mdifferentiableAt (by simp)
  have hh : MDifferentiableAt I 𝓘(ℝ) h x := h.contMDiff.mdifferentiableAt (by simp)
  simp only [hamiltonianVectorField, ContMDiffMap.coe_add, mvfderiv_add hg hh, map_add,
    Pi.add_apply]
  abel

theorem hamiltonianVectorField_neg (h : C^∞⟮I, M; ℝ⟯) :
    B.hamiltonianVectorField (-h) = -B.hamiltonianVectorField h := by
  funext x
  simp [hamiltonianVectorField, mvfderiv_neg]

theorem hamiltonianVectorField_sub (g h : C^∞⟮I, M; ℝ⟯) :
    B.hamiltonianVectorField (g - h) = B.hamiltonianVectorField g - B.hamiltonianVectorField h := by
  rw [sub_eq_add_neg, hamiltonianVectorField_add, hamiltonianVectorField_neg, ← sub_eq_add_neg]

theorem hamiltonianVectorField_smul (c : ℝ) (h : C^∞⟮I, M; ℝ⟯) :
    B.hamiltonianVectorField (c • h) = c • B.hamiltonianVectorField h := by
  funext x
  simp [hamiltonianVectorField, mvfderiv_const_smul_field]

theorem hamiltonianVectorField_mul (g h : C^∞⟮I, M; ℝ⟯) (x : M) :
    B.hamiltonianVectorField (g * h) x =
      g x • B.hamiltonianVectorField h x + h x • B.hamiltonianVectorField g x := by
  have hg : MDifferentiableAt I 𝓘(ℝ) g x := g.contMDiff.mdifferentiableAt (by simp)
  have hh : MDifferentiableAt I 𝓘(ℝ) h x := h.contMDiff.mdifferentiableAt (by simp)
  simp only [hamiltonianVectorField, ContMDiffMap.coe_mul, mvfderiv_mul hg hh, map_add, map_smul,
    smul_neg]
  abel

/-- Action `V(f) ∈ C^∞(M)` of a smooth vector field `V` on a smooth function `f`. -/
def actVectorField (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, V x⟩ : TangentBundle I M)))
    (f : C^∞⟮I, M; ℝ⟯) : C^∞⟮I, M; ℝ⟯ :=
  ⟨fun x ↦ mvfderiv I f x (V x), by
    rw [← contMDiffOn_univ]
    exact f.contMDiff.contMDiffOn.contMDiffOn_mvfderiv_apply isOpen_univ hV.contMDiffOn (by simp)⟩

@[simp]
theorem actVectorField_apply (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, V x⟩ : TangentBundle I M)))
    (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    (actVectorField V hV f) x = mvfderiv I f x (V x) :=
  rfl

/-- Smooth bracket `{g, h}_π ∈ C^∞(M)` induced by a smooth bivector `B`. -/
def bracket (g h : C^∞⟮I, M; ℝ⟯) : C^∞⟮I, M; ℝ⟯ :=
  B.pairOneForms (diffOneForm g) (diffOneForm h)

@[simp]
theorem bracket_apply (g h : C^∞⟮I, M; ℝ⟯) (x : M) :
    (B.bracket g h) x = B.bivector x (mvfderiv I g x) (mvfderiv I h x) := by
  rw [bracket, pairOneForms_apply, degreeOneEquiv_diffOneForm, degreeOneEquiv_diffOneForm]

theorem bracket_apply_eq_mvfderiv_hamiltonianVectorField (g h : C^∞⟮I, M; ℝ⟯) (x : M) :
    (B.bracket g h) x = mvfderiv I g x (B.hamiltonianVectorField h x) := by
  rw [bracket_apply, bivector_apply, B.anchor_skew, hamiltonianVectorField, map_neg]

theorem bracket_apply_eq_mvfderiv_anchorVectorField (g h : C^∞⟮I, M; ℝ⟯) (x : M) :
    (B.bracket g h) x = mvfderiv I h x (B.anchor x (mvfderiv I g x)) :=
  B.bracket_apply g h x

theorem bracket_add_left (g₁ g₂ h : C^∞⟮I, M; ℝ⟯) :
    B.bracket (g₁ + g₂) h = B.bracket g₁ h + B.bracket g₂ h := by
  ext x
  have hg₁ : MDifferentiableAt I 𝓘(ℝ) g₁ x := g₁.contMDiff.mdifferentiableAt (by simp)
  have hg₂ : MDifferentiableAt I 𝓘(ℝ) g₂ x := g₂.contMDiff.mdifferentiableAt (by simp)
  simp only [bracket_apply, bivector_apply, ContMDiffMap.coe_add, mvfderiv_add hg₁ hg₂, map_add,
    Pi.add_apply]

theorem bracket_add_right (g h₁ h₂ : C^∞⟮I, M; ℝ⟯) :
    B.bracket g (h₁ + h₂) = B.bracket g h₁ + B.bracket g h₂ := by
  ext x
  have hh₁ : MDifferentiableAt I 𝓘(ℝ) h₁ x := h₁.contMDiff.mdifferentiableAt (by simp)
  have hh₂ : MDifferentiableAt I 𝓘(ℝ) h₂ x := h₂.contMDiff.mdifferentiableAt (by simp)
  simp only [bracket_apply, bivector_apply, ContMDiffMap.coe_add, mvfderiv_add hh₁ hh₂,
    _root_.add_apply, Pi.add_apply]

theorem bracket_smul_left (c : ℝ) (g h : C^∞⟮I, M; ℝ⟯) :
    B.bracket (c • g) h = c • B.bracket g h := by
  ext x
  simp only [bracket_apply, bivector_apply, ContMDiffMap.coe_smul, mvfderiv_const_smul_field,
    map_smul, Pi.smul_apply]

theorem bracket_smul_right (c : ℝ) (g h : C^∞⟮I, M; ℝ⟯) :
    B.bracket g (c • h) = c • B.bracket g h := by
  ext x
  simp only [bracket_apply, bivector_apply, ContMDiffMap.coe_smul, mvfderiv_const_smul_field,
    _root_.smul_apply, Pi.smul_apply]

@[simp]
theorem bracket_zero_left (h : C^∞⟮I, M; ℝ⟯) :
    B.bracket 0 h = 0 := by
  simpa using B.bracket_smul_left 0 0 h

@[simp]
theorem bracket_zero_right (g : C^∞⟮I, M; ℝ⟯) :
    B.bracket g 0 = 0 := by
  simpa using B.bracket_smul_right 0 g 0

theorem bracket_neg_left (g h : C^∞⟮I, M; ℝ⟯) :
    B.bracket (-g) h = -B.bracket g h := by
  rw [← neg_one_smul ℝ g, B.bracket_smul_left, neg_one_smul]

theorem bracket_neg_right (g h : C^∞⟮I, M; ℝ⟯) :
    B.bracket g (-h) = -B.bracket g h := by
  rw [← neg_one_smul ℝ h, B.bracket_smul_right, neg_one_smul]

theorem bracket_sub_left (g₁ g₂ h : C^∞⟮I, M; ℝ⟯) :
    B.bracket (g₁ - g₂) h = B.bracket g₁ h - B.bracket g₂ h := by
  rw [sub_eq_add_neg, B.bracket_add_left, B.bracket_neg_left, ← sub_eq_add_neg]

theorem bracket_sub_right (g h₁ h₂ : C^∞⟮I, M; ℝ⟯) :
    B.bracket g (h₁ - h₂) = B.bracket g h₁ - B.bracket g h₂ := by
  rw [sub_eq_add_neg, B.bracket_add_right, B.bracket_neg_right, ← sub_eq_add_neg]

/-- Bundled ℝ-bilinear map `{·, ·}_π : C^∞(M) →ₗ[ℝ] C^∞(M) →ₗ[ℝ] C^∞(M)`. -/
def bracketₗ : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯ :=
  LinearMap.mk₂ ℝ B.bracket B.bracket_add_left B.bracket_smul_left
    B.bracket_add_right B.bracket_smul_right

@[simp]
theorem bracketₗ_apply (g h : C^∞⟮I, M; ℝ⟯) :
    (B.bracketₗ g) h = B.bracket g h :=
  rfl

/-- Skew-symmetry `{g, h}_π = -{h, g}_π` of the bracket. -/
theorem bracket_skew (g h : C^∞⟮I, M; ℝ⟯) :
    B.bracket g h = -B.bracket h g := by
  ext x
  exact B.bivector_skew x _ _

/-- Alternation `{g, g}_π = 0`. -/
@[simp]
theorem bracket_self (g : C^∞⟮I, M; ℝ⟯) :
    B.bracket g g = 0 := by
  ext x
  exact B.bivector_self x _

/-- Leibniz derivation law in the first argument: `{f * g, h}_π = f * {g, h}_π + g * {f, h}_π`. -/
theorem bracket_mul_left (f g h : C^∞⟮I, M; ℝ⟯) :
    B.bracket (f * g) h = f * B.bracket g h + g * B.bracket f h := by
  ext x
  have hf : MDifferentiableAt I 𝓘(ℝ) f x := f.contMDiff.mdifferentiableAt (by simp)
  have hg : MDifferentiableAt I 𝓘(ℝ) g x := g.contMDiff.mdifferentiableAt (by simp)
  rw [B.bracket_apply_eq_mvfderiv_hamiltonianVectorField, ContMDiffMap.coe_mul,
    mvfderiv_mul hf hg, _root_.add_apply, _root_.smul_apply, _root_.smul_apply, smul_eq_mul,
    smul_eq_mul, ContMDiffMap.coe_add, Pi.add_apply, ContMDiffMap.coe_mul, ContMDiffMap.coe_mul,
    Pi.mul_apply, Pi.mul_apply, B.bracket_apply_eq_mvfderiv_hamiltonianVectorField,
    B.bracket_apply_eq_mvfderiv_hamiltonianVectorField]

/-- Leibniz derivation law in the second argument: `{f, g * h}_π = g * {f, h}_π + h * {f, g}_π`. -/
theorem bracket_mul_right (f g h : C^∞⟮I, M; ℝ⟯) :
    B.bracket f (g * h) = g * B.bracket f h + h * B.bracket f g := by
  rw [B.bracket_skew f (g * h), B.bracket_mul_left g h f, B.bracket_skew h f, B.bracket_skew g f]
  ext x
  simp only [ContMDiffMap.coe_neg, ContMDiffMap.coe_add, ContMDiffMap.coe_mul,
    Pi.neg_apply, Pi.add_apply, Pi.mul_apply]
  ring

@[simp]
theorem bracket_const_left (c : ℝ) (h : C^∞⟮I, M; ℝ⟯) :
    B.bracket (ContMDiffMap.C c) h = 0 := by
  ext x
  have hc : ⇑(ContMDiffMap.C c : C^∞⟮I, M; ℝ⟯) = (fun _ : M ↦ c) := rfl
  rw [bracket_apply, bivector_apply, hc, mvfderiv_const, map_zero, map_zero,
    ContMDiffMap.coe_zero, Pi.zero_apply]

@[simp]
theorem bracket_const_right (g : C^∞⟮I, M; ℝ⟯) (c : ℝ) :
    B.bracket g (ContMDiffMap.C c) = 0 := by
  rw [B.bracket_skew, B.bracket_const_left, neg_zero]

@[simp]
theorem bracket_one_left (h : C^∞⟮I, M; ℝ⟯) :
    B.bracket 1 h = 0 :=
  B.bracket_const_left 1 h

@[simp]
theorem bracket_one_right (g : C^∞⟮I, M; ℝ⟯) :
    B.bracket g 1 = 0 :=
  B.bracket_const_right g 1

/-- Bundled ℝ-algebra derivation `X_h = {·, h}_π : Derivation ℝ C^∞(M) C^∞(M)`. -/
def hamiltonianDerivation (h : C^∞⟮I, M; ℝ⟯) :
    Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ where
  toLinearMap := B.bracketₗ.flip h
  map_one_eq_zero' := B.bracket_one_left h
  leibniz' f g := by
    change B.bracket (f * g) h = f • B.bracket g h + g • B.bracket f h
    rw [B.bracket_mul_left]
    ext x
    simp

@[simp]
theorem hamiltonianDerivation_apply (h g : C^∞⟮I, M; ℝ⟯) :
    (B.hamiltonianDerivation h) g = B.bracket g h :=
  rfl

theorem hamiltonianDerivation_neg (h : C^∞⟮I, M; ℝ⟯) :
    B.hamiltonianDerivation (-h) = -B.hamiltonianDerivation h := by
  ext g x
  simp [B.bracket_neg_right]

theorem hamiltonianDerivation_add (g h : C^∞⟮I, M; ℝ⟯) :
    B.hamiltonianDerivation (g + h) = B.hamiltonianDerivation g + B.hamiltonianDerivation h := by
  ext f x
  simp [B.bracket_add_right]

theorem hamiltonianDerivation_sub (g h : C^∞⟮I, M; ℝ⟯) :
    B.hamiltonianDerivation (g - h) = B.hamiltonianDerivation g - B.hamiltonianDerivation h := by
  ext f x
  simp [B.bracket_sub_right]

/-- Chain rule `{g, log a}_π = a⁻¹ * {g, a}_π` for a positive smooth function `a > 0`. -/
theorem bracket_log_right {a : C^∞⟮I, M; ℝ⟯} (ha : ∀ x, 0 < a x) (g : C^∞⟮I, M; ℝ⟯) (x : M) :
    (B.bracket g ⟨fun y ↦ Real.log (a y), a.contMDiff.log fun y ↦ (ha y).ne'⟩) x =
      (a x)⁻¹ * (B.bracket g a) x := by
  let loga : C^∞⟮I, M; ℝ⟯ := ⟨fun y ↦ Real.log (a y), a.contMDiff.log fun y ↦ (ha y).ne'⟩
  have hcoe : ⇑loga = Real.log ∘ a := rfl
  have hda : MDifferentiableAt I 𝓘(ℝ) a x := a.contMDiff.mdifferentiableAt (by simp)
  have hdlog : DifferentiableAt ℝ Real.log (a x) := Real.differentiableAt_log (ha x).ne'
  have hcomp : mvfderiv I (Real.log ∘ a) x = deriv Real.log (a x) • mvfderiv I a x :=
    mvfderiv_scalar_comp hda hdlog
  change (B.bracket g loga) x = _
  rw [bracket_apply, hcoe, hcomp, Real.deriv_log, bivector_apply, _root_.smul_apply, smul_eq_mul,
    bracket_apply, bivector_apply]

/-- A smooth function `c ∈ C^∞(M)` is a **Casimir function** of `B` if `{c, h}_π = 0` for all
`h ∈ C^∞(M)`. -/
def IsCasimir (c : C^∞⟮I, M; ℝ⟯) : Prop :=
  ∀ h : C^∞⟮I, M; ℝ⟯, B.bracket c h = 0

theorem IsCasimir.bracket_right {c : C^∞⟮I, M; ℝ⟯} (hc : B.IsCasimir c) (g : C^∞⟮I, M; ℝ⟯) :
    B.bracket g c = 0 := by
  rw [B.bracket_skew, hc g, neg_zero]

/-- A smooth map `φ : M → N` is a **Poisson map** between `(M, B₁)` and `(N, B₂)` if pullback
commutes with the brackets: `{g ∘ φ, h ∘ φ}_{B₁} = {g, h}_{B₂} ∘ φ` for all `g, h ∈ C^∞(N)`. -/
def IsPoissonMap {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N]
    [ChartedSpace H' N] [IsManifold I' ∞ N]
    (B₁ : SmoothBivector I M) (B₂ : SmoothBivector I' N) (φ : M → N)
    (hφ : ContMDiff I I' ∞ φ) : Prop :=
  ∀ g h : C^∞⟮I', N; ℝ⟯,
    B₁.bracket (g.comp ⟨φ, hφ⟩) (h.comp ⟨φ, hφ⟩) = (B₂.bracket g h).comp ⟨φ, hφ⟩

/-- Pointwise anchor pushforward criterion for `IsPoissonMap`: if
`dφ_x (#_{B₁}(dφ_x^* α)) = #_{B₂}(α)` for all `x` and `α`, then `φ` is a Poisson map. -/
theorem isPoissonMap_of_mfderiv_anchor {E' H' N : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
    {B₁ : SmoothBivector I M} {B₂ : SmoothBivector I' N} {φ : M → N}
    (hφ : ContMDiff I I' ∞ φ)
    (hpush : ∀ (x : M) (α : TangentSpace I' (φ x) →L[ℝ] ℝ),
      mfderiv I I' φ x (B₁.anchor x (α.comp (mfderiv I I' φ x))) = B₂.anchor (φ x) α) :
    IsPoissonMap B₁ B₂ φ hφ := by
  intro g h
  ext x
  have hφd : MDifferentiableAt I I' φ x := hφ.mdifferentiableAt (by simp)
  have hgd : MDifferentiableAt I' 𝓘(ℝ) g (φ x) := g.contMDiff.mdifferentiableAt (by simp)
  have hhd : MDifferentiableAt I' 𝓘(ℝ) h (φ x) := h.contMDiff.mdifferentiableAt (by simp)
  have hcg : mvfderiv I (g ∘ φ) x = (mvfderiv I' g (φ x)).comp (mfderiv I I' φ x) := by
    ext v
    simp only [mvfderiv_apply_eq_mfderiv_apply, ContinuousLinearMap.comp_apply]
    exact congrArg (· v) (mfderiv_comp x hgd hφd)
  have hch : mvfderiv I (h ∘ φ) x = (mvfderiv I' h (φ x)).comp (mfderiv I I' φ x) := by
    ext v
    simp only [mvfderiv_apply_eq_mfderiv_apply, ContinuousLinearMap.comp_apply]
    exact congrArg (· v) (mfderiv_comp x hhd hφd)
  let φMap : C^∞⟮I, M; I', N⟯ := ⟨φ, hφ⟩
  have hgcoe : ⇑(g.comp φMap) = g ∘ φ := rfl
  have hhcoe : ⇑(h.comp φMap) = h ∘ φ := rfl
  change (B₁.bracket (g.comp φMap) (h.comp φMap)) x = ((B₂.bracket g h).comp φMap) x
  rw [ContMDiffMap.comp_apply, bracket_apply, bracket_apply, hgcoe, hhcoe, hcg, hch,
    bivector_apply, ContinuousLinearMap.comp_apply]
  change (mvfderiv I' h (φ x))
      (mfderiv I I' φ x (B₁.anchor x ((mvfderiv I' g (φ x)).comp (mfderiv I I' φ x)))) = _
  rw [hpush, bivector_apply]
  rfl

/-! ### Koszul 1-Form Bracket (`S4TCdiffeo-Aug-2026.tex`, lines 359–363) -/

/-- Smooth Lie derivative `𝓛_V φ ∈ Ωᵏ(M)` of a smooth form `φ` along a smooth vector field `V`. -/
def smoothLieDerivForm {k : ℕ} (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, V x⟩ : TangentBundle I M)))
    (φ : SmoothForm I M ℝ k) : SmoothForm I M ℝ k :=
  ⟨mlieDerivForm V φ.1, SmoothForm.mlieDerivForm_mem_smoothBundleForms φ hV⟩

@[simp]
theorem coe_smoothLieDerivForm {k : ℕ} (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, V x⟩ : TangentBundle I M)))
    (φ : SmoothForm I M ℝ k) :
    (smoothLieDerivForm V hV φ).1 = mlieDerivForm V φ.1 :=
  rfl

/-- **Koszul 1-form bracket** `[α, β]_π = 𝓛_{#_π α} β - 𝓛_{#_π β} α - d(π(α, β))` on smooth
`1`-forms `Ω¹(M)` (`S4TCdiffeo-Aug-2026.tex`, line 360). -/
def koszulBracket (α β : SmoothForm I M ℝ 1) : SmoothForm I M ℝ 1 :=
  smoothLieDerivForm (B.anchorVectorField α) (B.contMDiff_anchorVectorField α) β -
    smoothLieDerivForm (B.anchorVectorField β) (B.contMDiff_anchorVectorField β) α -
    diffOneForm (B.pairOneForms α β)

/-- Skew-symmetry `[α, β]_π = -[β, α]_π` of the Koszul 1-form bracket. -/
theorem koszulBracket_skew (α β : SmoothForm I M ℝ 1) :
    B.koszulBracket α β = -B.koszulBracket β α := by
  have hd : diffOneForm (B.pairOneForms α β) = -diffOneForm (B.pairOneForms β α) := by
    rw [B.pairOneForms_skew α β]
    unfold diffOneForm
    have hneg : SmoothForm.ofFunction (-B.pairOneForms β α) =
        -SmoothForm.ofFunction (B.pairOneForms β α) := by
      ext x v
      simp [SmoothForm.coe_ofFunction]
    rw [hneg, map_neg]
  unfold koszulBracket
  rw [hd]
  abel

@[simp]
theorem koszulBracket_self (α : SmoothForm I M ℝ 1) :
    B.koszulBracket α α = 0 := by
  have h := B.koszulBracket_skew α α
  ext x v
  have hx := DFunLike.congr_fun (congrFun (congrArg Subtype.val h) x) v
  simp only [SmoothForm.neg_toRoughForm, Pi.neg_apply, ContinuousAlternatingMap.neg_apply] at hx
  change (B.koszulBracket α α).1 x v = 0
  linarith

/-- On exact `1`-forms, the Koszul bracket reproduces the differential of the scalar bracket:
`[df, dg]_π = d{f, g}_π`. -/
theorem koszulBracket_diffOneForm (f g : C^∞⟮I, M; ℝ⟯) :
    B.koszulBracket (diffOneForm f) (diffOneForm g) = diffOneForm (B.bracket f g) := by
  have hpair : B.pairOneForms (diffOneForm f) (diffOneForm g) = B.bracket f g := rfl
  have hL1 : smoothLieDerivForm (B.anchorVectorField (diffOneForm f))
      (B.contMDiff_anchorVectorField (diffOneForm f)) (diffOneForm g) =
      diffOneForm (B.bracket f g) := by
    apply Subtype.ext
    rw [coe_smoothLieDerivForm,
      SmoothForm.mlieDerivForm_eq_mextDeriv_interior
        (B.mdifferentiable_anchorVectorField (diffOneForm f)) (isClosed_diffOneForm g)]
    have hι : RoughForm.interior (B.anchorVectorField (diffOneForm f)) (diffOneForm g).1 =
        (SmoothForm.ofFunction (B.bracket f g)).1 := by
      rw [SmoothForm.coe_ofFunction,
        RoughForm.eq_ofFunction
          (RoughForm.interior (B.anchorVectorField (diffOneForm f)) (diffOneForm g).1)]
      congr 1
      funext x
      rw [RoughForm.interior_apply]
      have hv : (Matrix.vecCons (B.anchorVectorField (diffOneForm f) x) 0 :
          Fin 1 → TangentSpace I x) = ![B.anchorVectorField (diffOneForm f) x] := by
        funext i; fin_cases i; rfl
      rw [hv, diffOneForm_apply, anchorVectorField, degreeOneEquiv_diffOneForm, bracket_apply,
        bivector_apply]
    rw [hι, ← mextDerivₗ_apply I 0, ← diffOneForm]
  have hL2 : smoothLieDerivForm (B.anchorVectorField (diffOneForm g))
      (B.contMDiff_anchorVectorField (diffOneForm g)) (diffOneForm f) =
      -diffOneForm (B.bracket f g) := by
    have hneg : diffOneForm (-B.bracket f g) = -diffOneForm (B.bracket f g) := by
      unfold diffOneForm
      have h0 :
          SmoothForm.ofFunction (-B.bracket f g) = -SmoothForm.ofFunction (B.bracket f g) := by
        ext x v
        simp [SmoothForm.coe_ofFunction]
      rw [h0, map_neg]
    rw [← hneg, ← B.bracket_skew g f]
    apply Subtype.ext
    rw [coe_smoothLieDerivForm,
      SmoothForm.mlieDerivForm_eq_mextDeriv_interior
        (B.mdifferentiable_anchorVectorField (diffOneForm g)) (isClosed_diffOneForm f)]
    have hι : RoughForm.interior (B.anchorVectorField (diffOneForm g)) (diffOneForm f).1 =
        (SmoothForm.ofFunction (B.bracket g f)).1 := by
      rw [SmoothForm.coe_ofFunction,
        RoughForm.eq_ofFunction
          (RoughForm.interior (B.anchorVectorField (diffOneForm g)) (diffOneForm f).1)]
      congr 1
      funext x
      rw [RoughForm.interior_apply]
      have hv : (Matrix.vecCons (B.anchorVectorField (diffOneForm g) x) 0 :
          Fin 1 → TangentSpace I x) = ![B.anchorVectorField (diffOneForm g) x] := by
        funext i; fin_cases i; rfl
      rw [hv, diffOneForm_apply, anchorVectorField, degreeOneEquiv_diffOneForm, bracket_apply,
        bivector_apply]
    rw [hι, ← mextDerivₗ_apply I 0, ← diffOneForm]
  unfold koszulBracket
  rw [hL1, hL2, hpair]
  abel

end General

end SmoothBivector

/-! ## 3. Smooth Poisson Structures, Jacobi Identity, and Lie Bracket Homomorphism -/

/-- A **smooth Poisson structure** `(M, π)` on a smooth manifold `M`: a `SmoothBivector I M`
whose induced bracket `{·, ·}_π` on `C^∞(M)` satisfies the cyclic Jacobi identity. -/
structure PoissonStructure {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] extends SmoothBivector I M where
  /-- Cyclic Jacobi identity `{f, {g, h}} + {g, {h, f}} + {h, {f, g}} = 0`. -/
  jacobi :
    ∀ f g h : C^∞⟮I, M; ℝ⟯,
      toSmoothBivector.bracket f (toSmoothBivector.bracket g h) +
        toSmoothBivector.bracket g (toSmoothBivector.bracket h f) +
        toSmoothBivector.bracket h (toSmoothBivector.bracket f g) = 0

namespace PoissonStructure

section Basic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (P : PoissonStructure I M)

/-- Cyclic Jacobi identity in left-nested form `{f, {g, h}} + {g, {h, f}} + {h, {f, g}} = 0`. -/
theorem bracket_jacobi (f g h : C^∞⟮I, M; ℝ⟯) :
    P.bracket f (P.bracket g h) + P.bracket g (P.bracket h f) + P.bracket h (P.bracket f g) = 0 :=
  P.jacobi f g h

/-- Cyclic Jacobi identity in right-nested form `{{f, g}, h} + {{g, h}, f} + {{h, f}, g} = 0`. -/
theorem bracket_jacobi_right (f g h : C^∞⟮I, M; ℝ⟯) :
    P.bracket (P.bracket f g) h + P.bracket (P.bracket g h) f +
      P.bracket (P.bracket h f) g = 0 := by
  rw [P.bracket_skew (P.bracket f g) h, P.bracket_skew (P.bracket g h) f,
    P.bracket_skew (P.bracket h f) g]
  have hj := P.jacobi h f g
  ext x
  have hxj := congrArg (fun u : C^∞⟮I, M; ℝ⟯ ↦ u x) hj
  simp only [ContMDiffMap.coe_add, ContMDiffMap.coe_zero, Pi.add_apply, Pi.zero_apply] at hxj
  simp only [ContMDiffMap.coe_add, ContMDiffMap.coe_neg, ContMDiffMap.coe_zero,
    Pi.add_apply, Pi.neg_apply, Pi.zero_apply]
  linarith

/-- Adjoint Leibniz form of the Jacobi identity:
`{f, {g, h}}_π = {{f, g}_π, h}_π + {g, {f, h}_π}_π`. -/
theorem bracket_bracket_eq (f g h : C^∞⟮I, M; ℝ⟯) :
    P.bracket f (P.bracket g h) =
      P.bracket (P.bracket f g) h + P.bracket g (P.bracket f h) := by
  have hj := P.jacobi f g h
  rw [P.bracket_skew h f, P.bracket_neg_right, P.bracket_skew h (P.bracket f g)] at hj
  ext x
  have hxj := congrArg (fun u : C^∞⟮I, M; ℝ⟯ ↦ u x) hj
  simp only [ContMDiffMap.coe_add, ContMDiffMap.coe_neg, ContMDiffMap.coe_zero,
    Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at hxj ⊢
  linarith

/-- Right-acting Hamiltonian derivation identity:
`X_h({f, g}_π) = {X_h(f), g}_π + {f, X_h(g)}_π`. -/
theorem bracket_bracket_right (f g h : C^∞⟮I, M; ℝ⟯) :
    P.bracket (P.bracket f g) h =
      P.bracket (P.bracket f h) g + P.bracket f (P.bracket g h) := by
  have heq := P.bracket_bracket_eq h f g
  rw [P.bracket_skew h (P.bracket f g), P.bracket_skew h f, P.bracket_skew h g,
    P.bracket_neg_left, P.bracket_neg_right] at heq
  ext x
  have hx := congrArg (fun u : C^∞⟮I, M; ℝ⟯ ↦ u x) heq
  simp only [ContMDiffMap.coe_add, ContMDiffMap.coe_neg, Pi.add_apply, Pi.neg_apply] at hx ⊢
  linarith

/-- On a finite-dimensional Hausdorff smooth manifold, two tangent vectors at `x` are equal whenever
all smooth functions `f : C^∞⟮I, M; ℝ⟯` have the same directional derivative on them. -/
theorem eq_of_forall_mvfderiv_eq [FiniteDimensional ℝ E] [T2Space M] {x : M}
    {v w : TangentSpace I x}
    (h : ∀ f : C^∞⟮I, M; ℝ⟯, mvfderiv I f x v = mvfderiv I f x w) :
    v = w := by
  let β : SmoothBumpFunction I x := Classical.arbitrary (SmoothBumpFunction I x)
  let bE : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  have hcoord (i : Fin (Module.finrank ℝ E)) :
      (bE.coord i).toContinuousLinearMap v = (bE.coord i).toContinuousLinearMap w := by
    let ξ : E →L[ℝ] ℝ := (bE.coord i).toContinuousLinearMap
    have hf := h (β.bumpCovector (n := ⊤) ξ)
    rwa [β.mvfderiv_bumpCovector ξ] at hf
  exact bE.ext_elem fun i ↦ hcoord i

/-- Lie bracket of Hamiltonian vector fields:
`[X_f, X_g] = -X_{{f, g}_π}` (under `X_h = {·, h}_π`). -/
theorem mlieBracket_hamiltonianVectorField [CompleteSpace E] [FiniteDimensional ℝ E] [T2Space M]
    (f g : C^∞⟮I, M; ℝ⟯) :
    VectorField.mlieBracket I (P.hamiltonianVectorField f) (P.hamiltonianVectorField g) =
      -P.hamiltonianVectorField (P.bracket f g) := by
  funext x
  refine eq_of_forall_mvfderiv_eq fun h ↦ ?_
  have : IsManifold I (minSmoothness ℝ 2) M :=
    IsManifold.of_le (m := minSmoothness ℝ 2) (n := ∞) (by simp)
  rw [mvfderiv_mlieBracket (h.contMDiff x) (by simp)
    (P.mdifferentiable_hamiltonianVectorField f x)
    (P.mdifferentiable_hamiltonianVectorField g x)]
  have hgf : (fun y ↦ mvfderiv I h y (P.hamiltonianVectorField g y)) = ⇑(P.bracket h g) :=
    funext fun y ↦ (P.bracket_apply_eq_mvfderiv_hamiltonianVectorField h g y).symm
  have hfg : (fun y ↦ mvfderiv I h y (P.hamiltonianVectorField f y)) = ⇑(P.bracket h f) :=
    funext fun y ↦ (P.bracket_apply_eq_mvfderiv_hamiltonianVectorField h f y).symm
  rw [hgf, hfg, ← P.bracket_apply_eq_mvfderiv_hamiltonianVectorField (P.bracket h g) f x,
    ← P.bracket_apply_eq_mvfderiv_hamiltonianVectorField (P.bracket h f) g x,
    Pi.neg_apply, map_neg, ← P.bracket_apply_eq_mvfderiv_hamiltonianVectorField h (P.bracket f g) x]
  have hj := congrArg (fun u : C^∞⟮I, M; ℝ⟯ ↦ u x) (P.bracket_bracket_right h g f)
  simp only [ContMDiffMap.coe_add, Pi.add_apply] at hj
  rw [P.bracket_skew f g, P.bracket_neg_right, ContMDiffMap.coe_neg, Pi.neg_apply]
  linarith

/-- On exact `1`-forms, `#_π` is a Lie algebra homomorphism:
`[#_π(df), #_π(dg)] = #_π(d{f, g}_π) = #_π([df, dg]_π)`. -/
theorem mlieBracket_anchorVectorField_diffOneForm [CompleteSpace E] [FiniteDimensional ℝ E]
    [T2Space M] (f g : C^∞⟮I, M; ℝ⟯) :
    VectorField.mlieBracket I
        (P.anchorVectorField (SmoothBivector.diffOneForm f))
        (P.anchorVectorField (SmoothBivector.diffOneForm g)) =
      P.anchorVectorField (P.koszulBracket (SmoothBivector.diffOneForm f)
        (SmoothBivector.diffOneForm g)) := by
  have hf : P.anchorVectorField (SmoothBivector.diffOneForm f) = -P.hamiltonianVectorField f := by
    rw [P.hamiltonianVectorField_eq_neg_anchorVectorField, neg_neg]
  have hg : P.anchorVectorField (SmoothBivector.diffOneForm g) = -P.hamiltonianVectorField g := by
    rw [P.hamiltonianVectorField_eq_neg_anchorVectorField, neg_neg]
  rw [hf, hg, P.koszulBracket_diffOneForm]
  funext x
  rw [VectorField.mlieBracket_neg_left, VectorField.mlieBracket_neg_right, neg_neg,
    congrFun (P.mlieBracket_hamiltonianVectorField f g) x,
    P.hamiltonianVectorField_eq_neg_anchorVectorField, Pi.neg_apply, Pi.neg_apply, neg_neg]

/-! ## 4. Lichnerowicz 1-Cocycles and First Poisson Cohomology Class -/

/-- A derivation `D : Derivation ℝ C^∞(M) C^∞(M)` is a **Lichnerowicz 1-cocycle** (Poisson
derivation, `d_π D = 0`) if `D {g, h}_π = {D g, h}_π + {g, D h}_π` for all `g, h ∈ C^∞(M)`
(`S4TCdiffeo-Aug-2026.tex`, lines 370–374). -/
def IsLichnerowiczOneCocycle
    (D : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) : Prop :=
  ∀ g h : C^∞⟮I, M; ℝ⟯, D (P.bracket g h) = P.bracket (D g) h + P.bracket g (D h)

/-- Every Hamiltonian derivation `X_u = {·, u}_π` is a Lichnerowicz 1-cocycle (`d_π² = 0` from
degree `0` to degree `2`). -/
theorem isLichnerowiczOneCocycle_hamiltonianDerivation (u : C^∞⟮I, M; ℝ⟯) :
    P.IsLichnerowiczOneCocycle (P.hamiltonianDerivation u) := fun g h ↦
  P.bracket_bracket_right g h u

/-- Two derivations `D₁, D₂` are **cohomologous** in `H¹(M, π)` if their difference is a
Hamiltonian derivation `X_u` for some `u ∈ C^∞(M)`. -/
def CohomologousOneCocycle
    (D₁ D₂ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) : Prop :=
  ∃ u : C^∞⟮I, M; ℝ⟯, D₁ - D₂ = P.hamiltonianDerivation u

theorem CohomologousOneCocycle.refl
    (D : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) :
    P.CohomologousOneCocycle D D :=
  ⟨0, by ext g x; simp⟩

theorem CohomologousOneCocycle.symm
    {D₁ D₂ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯}
    (h : P.CohomologousOneCocycle D₁ D₂) :
    P.CohomologousOneCocycle D₂ D₁ := by
  obtain ⟨u, hu⟩ := h
  refine ⟨-u, ?_⟩
  rw [P.hamiltonianDerivation_neg, ← hu]
  abel

theorem CohomologousOneCocycle.trans
    {D₁ D₂ D₃ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯}
    (h₁₂ : P.CohomologousOneCocycle D₁ D₂)
    (h₂₃ : P.CohomologousOneCocycle D₂ D₃) :
    P.CohomologousOneCocycle D₁ D₃ := by
  obtain ⟨u₁, hu₁⟩ := h₁₂
  obtain ⟨u₂, hu₂⟩ := h₂₃
  refine ⟨u₁ + u₂, ?_⟩
  rw [P.hamiltonianDerivation_add, ← hu₁, ← hu₂]
  abel

theorem equivalence_cohomologousOneCocycle :
    Equivalence P.CohomologousOneCocycle :=
  ⟨CohomologousOneCocycle.refl P, fun h ↦ h.symm P, fun h₁ h₂ ↦ h₁.trans P h₂⟩

/-! ## 5. Weinstein's Modular Vector Field, Density Rescaling, and Unimodularity -/

section Modular

variable {n : ℕ} [hdim : HasFinrank E n] [FiniteDimensional ℝ E]

/-- Every smooth top form `Ω ∈ Ωⁿ(M)` on an `n`-manifold is automatically closed (`dΩ = 0`). -/
theorem isClosed_topForm (Ω : SmoothForm I M ℝ n) : Ω.IsClosed :=
  SmoothForm.isClosed_of_finrank_le hdim.finrank_eq.le Ω

/-- Smooth Lie derivative `𝓛_{X_h} Ω ∈ Ωⁿ(M)` of a smooth top form `Ω` along the Hamiltonian
vector field `X_h`. -/
def lieDerivVolume (Ω : SmoothForm I M ℝ n) (h : C^∞⟮I, M; ℝ⟯) : SmoothForm I M ℝ n :=
  SmoothBivector.smoothLieDerivForm (P.hamiltonianVectorField h)
    (P.contMDiff_hamiltonianVectorField h) Ω

omit hdim [FiniteDimensional ℝ E] in
@[simp]
theorem coe_lieDerivVolume (Ω : SmoothForm I M ℝ n) (h : C^∞⟮I, M; ℝ⟯) :
    (P.lieDerivVolume Ω h).1 = mlieDerivForm (P.hamiltonianVectorField h) Ω.1 :=
  rfl

omit hdim in
/-- By Cartan's magic formula on closed top forms (`dΩ = 0`), for `n = m + 1` the Lie derivative
`𝓛_{X_h} Ω` equals `d(ι_{X_h} Ω)`. -/
theorem lieDerivVolume_eq_mextDeriv_interior {m : ℕ} (Ω : SmoothForm I M ℝ (m + 1))
    (hfin : Module.finrank ℝ E ≤ m + 1) (h : C^∞⟮I, M; ℝ⟯) :
    mlieDerivForm (P.hamiltonianVectorField h) Ω.1 =
      mextDeriv (RoughForm.interior (P.hamiltonianVectorField h) Ω.1) :=
  SmoothForm.mlieDerivForm_eq_mextDeriv_interior (P.mdifferentiable_hamiltonianVectorField h)
    (SmoothForm.isClosed_of_finrank_le hfin Ω)

/-- Smooth interior contraction `ι_{X_h} Ω ∈ Ωᵐ(M)` of a smooth `(m + 1)`-form `Ω` by `X_h`. -/
def interiorHamiltonian {m : ℕ} (Ω : SmoothForm I M ℝ (m + 1)) (h : C^∞⟮I, M; ℝ⟯) :
    SmoothForm I M ℝ m :=
  ⟨RoughForm.interior (P.hamiltonianVectorField h) Ω.1,
    (Ω.isSmoothForm.interior (P.contMDiff_hamiltonianVectorField h)).mem_smoothBundleForms⟩

omit hdim [FiniteDimensional ℝ E] in
@[simp]
theorem coe_interiorHamiltonian {m : ℕ} (Ω : SmoothForm I M ℝ (m + 1)) (h : C^∞⟮I, M; ℝ⟯) :
    (P.interiorHamiltonian Ω h).1 = RoughForm.interior (P.hamiltonianVectorField h) Ω.1 :=
  rfl

omit hdim in
theorem mextDerivₗ_interiorHamiltonian_eq_lieDerivVolume {m : ℕ} [hdim' : HasFinrank E (m + 1)]
    (Ω : SmoothForm I M ℝ (m + 1)) (h : C^∞⟮I, M; ℝ⟯) :
    mextDerivₗ I m (P.interiorHamiltonian Ω h) = P.lieDerivVolume Ω h := by
  apply Subtype.ext
  rw [mextDerivₗ_apply, coe_interiorHamiltonian, coe_lieDerivVolume,
    P.lieDerivVolume_eq_mextDeriv_interior Ω hdim'.finrank_eq.le h]

/-- **Weinstein's modular operator** `Y^Ω h ∈ C^∞(M)` with respect to a nowhere-vanishing smooth
volume form `Ω`, uniquely defined by `𝓛_{X_h} Ω = (Y^Ω h) • Ω`
(`S4TCdiffeo-Aug-2026.tex`, line 378). -/
def modularApply (Ω : SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0) (h : C^∞⟮I, M; ℝ⟯) :
    C^∞⟮I, M; ℝ⟯ :=
  divVolume Ω hΩ (P.lieDerivVolume Ω h)

/-- Defining equation `𝓛_{X_h} Ω = (Y^Ω h) • Ω` of Weinstein's modular vector field. -/
@[simp]
theorem funSMulₗ_modularApply (Ω : SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0)
    (h : C^∞⟮I, M; ℝ⟯) :
    SmoothForm.funSMulₗ (P.modularApply Ω hΩ h) Ω = P.lieDerivVolume Ω h :=
  funSMulₗ_divVolume Ω hΩ (P.lieDerivVolume Ω h)

theorem mlieDerivForm_eq_modularApply_smul (Ω : SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0)
    (h : C^∞⟮I, M; ℝ⟯) (x : M) :
    mlieDerivForm (P.hamiltonianVectorField h) Ω.1 x = (P.modularApply Ω hΩ h) x • Ω.1 x :=
  (divVolume_apply_smul Ω hΩ (P.lieDerivVolume Ω h) x).symm

theorem eq_modularApply_iff (Ω : SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0)
    (h u : C^∞⟮I, M; ℝ⟯) :
    u = P.modularApply Ω hΩ h ↔ SmoothForm.funSMulₗ u Ω = P.lieDerivVolume Ω h :=
  eq_divVolume_iff Ω hΩ (P.lieDerivVolume Ω h) u

@[simp]
theorem modularApply_const (Ω : SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0) (c : ℝ) :
    P.modularApply Ω hΩ (ContMDiffMap.C c) = 0 := by
  symm
  rw [P.eq_modularApply_iff Ω hΩ (ContMDiffMap.C c) 0]
  apply Subtype.ext
  funext x
  simp only [SmoothForm.coe_funSMulₗ, ContMDiffMap.coe_zero, Pi.zero_apply, zero_smul,
    coe_lieDerivVolume, P.hamiltonianVectorField_const c]
  have hzero : mlieDerivForm (0 : (y : M) → TangentSpace I y) Ω.1 = 0 := by
    cases n with
    | zero =>
      rw [mlieDerivForm_eq_interior_mextDeriv, RoughForm.interior_zero_field]
    | succ m =>
      have h0 : MDifferentiable I I.tangent
          (fun y : M ↦ (⟨y, (0 : TangentSpace I y)⟩ : TangentBundle I M)) :=
        (contMDiff_zeroSection (n := ∞) ℝ (TangentSpace I : M → Type _)).mdifferentiable (by simp)
      change mlieDerivForm (fun y : M ↦ (0 : TangentSpace I y)) Ω.1 = 0
      rw [SmoothForm.mlieDerivForm_eq_mextDeriv_interior h0 (isClosed_topForm Ω)]
      change mextDeriv (RoughForm.interior (0 : (y : M) → TangentSpace I y) Ω.1) = 0
      rw [RoughForm.interior_zero_field, mextDeriv_zero]
  rw [hzero, Pi.zero_apply]

@[simp]
theorem modularApply_one (Ω : SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0) :
    P.modularApply Ω hΩ 1 = 0 :=
  P.modularApply_const Ω hΩ 1

theorem modularApply_add (Ω : SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0)
    (g h : C^∞⟮I, M; ℝ⟯) :
    P.modularApply Ω hΩ (g + h) = P.modularApply Ω hΩ g + P.modularApply Ω hΩ h := by
  have hadd : P.lieDerivVolume Ω (g + h) = P.lieDerivVolume Ω g + P.lieDerivVolume Ω h := by
    apply Subtype.ext
    funext x
    rw [coe_lieDerivVolume, SmoothForm.add_toRoughForm, Pi.add_apply, coe_lieDerivVolume,
      coe_lieDerivVolume, P.hamiltonianVectorField_add]
    exact mlieDerivForm_add_left Ω.1 (P.mdifferentiable_hamiltonianVectorField g x)
      (P.mdifferentiable_hamiltonianVectorField h x)
  unfold modularApply
  rw [hadd, divVolume_add]

theorem modularApply_smul (Ω : SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0)
    (c : ℝ) (h : C^∞⟮I, M; ℝ⟯) :
    P.modularApply Ω hΩ (c • h) = c • P.modularApply Ω hΩ h := by
  have hsmul : P.lieDerivVolume Ω (c • h) = c • P.lieDerivVolume Ω h := by
    apply Subtype.ext
    funext x
    cases n with
    | zero =>
      rw [coe_lieDerivVolume, SetLike.val_smul, Pi.smul_apply, coe_lieDerivVolume,
        mlieDerivForm_eq_interior_mextDeriv, mlieDerivForm_eq_interior_mextDeriv,
        P.hamiltonianVectorField_smul]
      ext v
      rw [RoughForm.interior_apply, ContinuousAlternatingMap.smul_apply, RoughForm.interior_apply,
        Pi.smul_apply, map_vecCons_smul_slot0]
    | succ m =>
      rw [coe_lieDerivVolume, SetLike.val_smul, Pi.smul_apply, coe_lieDerivVolume,
        SmoothForm.mlieDerivForm_eq_mextDeriv_interior
          (P.mdifferentiable_hamiltonianVectorField (c • h)) (isClosed_topForm Ω),
        SmoothForm.mlieDerivForm_eq_mextDeriv_interior
          (P.mdifferentiable_hamiltonianVectorField h) (isClosed_topForm Ω),
        P.hamiltonianVectorField_smul]
      have hsc : RoughForm.interior (c • P.hamiltonianVectorField h) Ω.1 =
          c • RoughForm.interior (P.hamiltonianVectorField h) Ω.1 :=
        RoughForm.interior_smul_field (fun _ ↦ c) (P.hamiltonianVectorField h) Ω.1
      rw [hsc, mextDeriv_smul, Pi.smul_apply]
  unfold modularApply
  rw [hsmul, divVolume_smul]

/-- **Weinstein's Derivation Theorem**: `h ↦ Y^Ω h` satisfies the Leibniz rule
`Y^Ω (g * h) = g * Y^Ω h + h * Y^Ω g`, and hence defines a derivation of `C^∞(M)`
(`S4TCdiffeo-Aug-2026.tex`, lines 376–378). -/
theorem modularApply_mul (Ω : SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0)
    (g h : C^∞⟮I, M; ℝ⟯) :
    P.modularApply Ω hΩ (g * h) = g * P.modularApply Ω hΩ h + h * P.modularApply Ω hΩ g := by
  symm
  rw [P.eq_modularApply_iff Ω hΩ (g * h)]
  cases n with
  | zero =>
    have hL0 (u : C^∞⟮I, M; ℝ⟯) : P.lieDerivVolume Ω u = 0 := by
      apply Subtype.ext
      rw [coe_lieDerivVolume, mlieDerivForm_eq_interior_mextDeriv]
      have hd0 : mextDeriv Ω.1 = 0 := (SmoothForm.isClosed_def Ω).mp (isClosed_topForm Ω)
      rw [hd0, RoughForm.interior_zero]
      rfl
    have hm0 (u : C^∞⟮I, M; ℝ⟯) : P.modularApply Ω hΩ u = 0 := by
      unfold modularApply
      rw [hL0 u, divVolume_zero]
    rw [hm0 g, hm0 h, hL0 (g * h), mul_zero, mul_zero, add_zero]
    apply Subtype.ext
    funext x
    simp [SmoothForm.coe_funSMulₗ]
  | succ m =>
    apply Subtype.ext
    funext x
    ext v
    have hι : P.interiorHamiltonian Ω (g * h) =
        SmoothForm.funSMulₗ g (P.interiorHamiltonian Ω h) +
          SmoothForm.funSMulₗ h (P.interiorHamiltonian Ω g) := by
      apply Subtype.ext
      funext y
      ext w
      rw [coe_interiorHamiltonian, SmoothForm.add_toRoughForm, Pi.add_apply,
        ContinuousAlternatingMap.add_apply, SmoothForm.coe_funSMulₗ, SmoothForm.coe_funSMulₗ,
        ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.smul_apply,
        coe_interiorHamiltonian, coe_interiorHamiltonian,
        RoughForm.interior_apply, RoughForm.interior_apply, RoughForm.interior_apply,
        P.hamiltonianVectorField_mul g h y, map_vecCons_add_slot0 (Ω.1 y),
        map_vecCons_smul_slot0 (Ω.1 y), map_vecCons_smul_slot0 (Ω.1 y)]
    have hd := congrArg (fun η : SmoothForm I M ℝ m ↦ (mextDerivₗ I m η).1 x v) hι
    rw [P.mextDerivₗ_interiorHamiltonian_eq_lieDerivVolume Ω (g * h), map_add,
      SmoothForm.add_toRoughForm, Pi.add_apply, ContinuousAlternatingMap.add_apply,
      SmoothForm.mextDerivₗ_funSMulₗ_apply, SmoothForm.mextDerivₗ_funSMulₗ_apply,
      P.mextDerivₗ_interiorHamiltonian_eq_lieDerivVolume Ω h,
      P.mextDerivₗ_interiorHamiltonian_eq_lieDerivVolume Ω g] at hd
    have hdg : (mextDeriv (RoughForm.ofFunction I g)).wedge (P.interiorHamiltonian Ω h).1 x
        (v ∘ Fin.cast (show 0 + 1 + m = m + 1 by omega)) =
        (P.bracket g h) x * Ω.1 x v := by
      have hcast : (v ∘ Fin.cast (show 0 + 1 + m = m + 1 by omega)) =
          (v ∘ Fin.cast (Nat.add_comm 1 m)) := by
        funext i; simp
      rw [hcast, coe_interiorHamiltonian, ← apply_smul_topForm_eq_wedge_interior]
      have hd1 : mextDeriv (RoughForm.ofFunction I g) x ![P.hamiltonianVectorField h x] =
          (P.bracket g h) x := by
        rw [mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
          Matrix.cons_val_zero, P.bracket_apply_eq_mvfderiv_hamiltonianVectorField]
      rw [hd1]
    have hdh : (mextDeriv (RoughForm.ofFunction I h)).wedge (P.interiorHamiltonian Ω g).1 x
        (v ∘ Fin.cast (show 0 + 1 + m = m + 1 by omega)) =
        (P.bracket h g) x * Ω.1 x v := by
      have hcast : (v ∘ Fin.cast (show 0 + 1 + m = m + 1 by omega)) =
          (v ∘ Fin.cast (Nat.add_comm 1 m)) := by
        funext i; simp
      rw [hcast, coe_interiorHamiltonian, ← apply_smul_topForm_eq_wedge_interior]
      have hd1 : mextDeriv (RoughForm.ofFunction I h) x ![P.hamiltonianVectorField g x] =
          (P.bracket h g) x := by
        rw [mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
          Matrix.cons_val_zero, P.bracket_apply_eq_mvfderiv_hamiltonianVectorField]
      rw [hd1]
    have hskew : (P.bracket h g) x = -(P.bracket g h) x := by
      simpa using congrArg (fun u : C^∞⟮I, M; ℝ⟯ ↦ u x) (P.bracket_skew h g)
    have hmod_h : (P.lieDerivVolume Ω h).1 x v = (P.modularApply Ω hΩ h) x * Ω.1 x v := by
      rw [coe_lieDerivVolume, P.mlieDerivForm_eq_modularApply_smul Ω hΩ h x,
        ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    have hmod_g : (P.lieDerivVolume Ω g).1 x v = (P.modularApply Ω hΩ g) x * Ω.1 x v := by
      rw [coe_lieDerivVolume, P.mlieDerivForm_eq_modularApply_smul Ω hΩ g x,
        ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    rw [hdg, hdh, hskew, hmod_h, hmod_g] at hd
    rw [SmoothForm.coe_funSMulₗ, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
      ContMDiffMap.coe_add, ContMDiffMap.coe_mul, ContMDiffMap.coe_mul, Pi.add_apply,
      Pi.mul_apply, Pi.mul_apply, hd]
    ring

/-- **Weinstein's modular derivation (modular vector field)** `Y^Ω : Derivation ℝ C^∞(M) C^∞(M)`
defined by `𝓛_{X_h} Ω = (Y^Ω h) • Ω` (`S4TCdiffeo-Aug-2026.tex`, line 378). -/
def modularDerivation (Ω : SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0) :
    Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ where
  toFun := P.modularApply Ω hΩ
  map_add' := P.modularApply_add Ω hΩ
  map_smul' := P.modularApply_smul Ω hΩ
  map_one_eq_zero' := P.modularApply_one Ω hΩ
  leibniz' g h := by
    change P.modularApply Ω hΩ (g * h) =
      g • P.modularApply Ω hΩ h + h • P.modularApply Ω hΩ g
    rw [P.modularApply_mul Ω hΩ g h]
    ext x
    simp

@[simp]
theorem modularDerivation_apply (Ω : SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0)
    (h : C^∞⟮I, M; ℝ⟯) :
    (P.modularDerivation Ω hΩ) h = P.modularApply Ω hΩ h :=
  rfl

/-- Negating the volume form `-Ω` leaves `Y^Ω` unchanged: `Y^{-Ω} = Y^Ω`. -/
theorem modularDerivation_neg (Ω : SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0) :
    P.modularDerivation (-Ω) (fun x ↦ neg_ne_zero.mpr (hΩ x)) = P.modularDerivation Ω hΩ := by
  ext h x
  have hL : (P.lieDerivVolume (-Ω) h).1 x = -(P.lieDerivVolume Ω h).1 x := by
    cases n with
    | zero =>
      rw [coe_lieDerivVolume, coe_lieDerivVolume, mlieDerivForm_eq_interior_mextDeriv,
        mlieDerivForm_eq_interior_mextDeriv, SmoothForm.neg_toRoughForm, mextDeriv_neg,
        RoughForm.interior_def, RoughForm.interior_def]
      ext v
      simp
    | succ m =>
      rw [coe_lieDerivVolume, coe_lieDerivVolume,
        SmoothForm.mlieDerivForm_eq_mextDeriv_interior
          (P.mdifferentiable_hamiltonianVectorField h) (isClosed_topForm (-Ω)),
        SmoothForm.mlieDerivForm_eq_mextDeriv_interior
          (P.mdifferentiable_hamiltonianVectorField h) (isClosed_topForm Ω),
        SmoothForm.neg_toRoughForm]
      have hneg : RoughForm.interior (P.hamiltonianVectorField h) (-Ω.1) =
          -RoughForm.interior (P.hamiltonianVectorField h) Ω.1 := by
        simpa only [neg_one_smul] using
          RoughForm.interior_smul (-1 : ℝ) (P.hamiltonianVectorField h) Ω.1
      rw [hneg, mextDeriv_neg, Pi.neg_apply]
  have h1 := P.mlieDerivForm_eq_modularApply_smul (-Ω) (fun y ↦ neg_ne_zero.mpr (hΩ y)) h x
  have h2 := P.mlieDerivForm_eq_modularApply_smul Ω hΩ h x
  change mlieDerivForm _ (-Ω).1 x = _ at h1
  rw [← coe_lieDerivVolume, hL, coe_lieDerivVolume, h2, SmoothForm.neg_toRoughForm, Pi.neg_apply,
    smul_neg, neg_inj] at h1
  exact smul_left_injective ℝ (hΩ x) h1.symm

/-- Smooth logarithm `log a ∈ C^∞(M)` of a positive smooth function `a > 0`. -/
def logSmooth (a : C^∞⟮I, M; ℝ⟯) (ha : ∀ x : M, 0 < a x) : C^∞⟮I, M; ℝ⟯ :=
  ⟨fun x ↦ Real.log (a x), a.contMDiff.log fun x ↦ (ha x).ne'⟩

omit [IsManifold I ∞ M] hdim [FiniteDimensional ℝ E] in
@[simp]
theorem logSmooth_apply (a : C^∞⟮I, M; ℝ⟯) (ha : ∀ x : M, 0 < a x) (x : M) :
    (logSmooth a ha) x = Real.log (a x) :=
  rfl

/-- Smooth exponential `exp u ∈ C^∞(M)` of any smooth function `u ∈ C^∞(M)`. -/
def expSmooth (u : C^∞⟮I, M; ℝ⟯) : C^∞⟮I, M; ℝ⟯ :=
  ⟨fun x ↦ Real.exp (u x), Real.contDiff_exp.comp_contMDiff u.contMDiff⟩

omit [IsManifold I ∞ M] hdim [FiniteDimensional ℝ E] in
@[simp]
theorem expSmooth_apply (u : C^∞⟮I, M; ℝ⟯) (x : M) :
    (expSmooth u) x = Real.exp (u x) :=
  rfl

omit [IsManifold I ∞ M] hdim [FiniteDimensional ℝ E] in
theorem expSmooth_pos (u : C^∞⟮I, M; ℝ⟯) (x : M) : 0 < (expSmooth u) x :=
  Real.exp_pos (u x)

omit [IsManifold I ∞ M] hdim [FiniteDimensional ℝ E] in
@[simp]
theorem logSmooth_expSmooth (u : C^∞⟮I, M; ℝ⟯) :
    logSmooth (expSmooth u) (expSmooth_pos u) = u := by
  ext x
  simp [Real.log_exp]

/-- **Positive Density Rescaling Law for Weinstein's Modular Vector Field**
(`S4TCdiffeo-Aug-2026.tex`, line 381; verified sign `Y^{aΩ} = Y^Ω - X_{log a}` under
`X_h = {·, h}_π`):
for every positive smooth function `a > 0`,
`Y^{a • Ω} h = Y^Ω h + {log a, h}_π = Y^Ω h - X_{log a}(h)`. -/
theorem modularDerivation_funSMul (Ω : SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0)
    (a : C^∞⟮I, M; ℝ⟯) (ha : ∀ x : M, 0 < a x) :
    P.modularDerivation (SmoothForm.funSMulₗ a Ω)
        (funSMulₗ_ne_zero hΩ fun x ↦ (ha x).ne') =
      P.modularDerivation Ω hΩ - P.hamiltonianDerivation (logSmooth a ha) := by
  ext h : 1
  symm
  rw [_root_.sub_apply, modularDerivation_apply, modularDerivation_apply,
    P.eq_modularApply_iff (SmoothForm.funSMulₗ a Ω)
      (funSMulₗ_ne_zero hΩ fun x ↦ (ha x).ne') h]
  cases n with
  | zero =>
    have hsub : Subsingleton E := Module.finrank_zero_iff.mp hdim.finrank_eq
    have hL0 (Φ : SmoothForm I M ℝ 0) : P.lieDerivVolume Φ h = 0 := by
      apply Subtype.ext
      rw [coe_lieDerivVolume, mlieDerivForm_eq_interior_mextDeriv,
        (SmoothForm.isClosed_def Φ).mp (isClosed_topForm Φ), RoughForm.interior_zero]
      rfl
    have hm0 : P.modularApply Ω hΩ h = 0 := by
      unfold modularApply
      rw [hL0 Ω, divVolume_zero]
    have hb0 : (P.hamiltonianDerivation (logSmooth a ha)) h = 0 := by
      ext x
      rw [SmoothBivector.hamiltonianDerivation_apply,
        P.bracket_apply_eq_mvfderiv_hamiltonianVectorField]
      have hv0 : P.hamiltonianVectorField (logSmooth a ha) x = 0 := by
        have : Subsingleton (TangentSpace I x) := hsub
        exact Subsingleton.elim _ _
      rw [hv0, map_zero, ContMDiffMap.coe_zero, Pi.zero_apply]
    rw [hm0, hb0, sub_zero, hL0]
    apply Subtype.ext
    funext x
    simp [SmoothForm.coe_funSMulₗ]
  | succ m =>
    apply Subtype.ext
    funext x
    ext v
    have hι : P.interiorHamiltonian (SmoothForm.funSMulₗ a Ω) h =
        SmoothForm.funSMulₗ a (P.interiorHamiltonian Ω h) := by
      apply Subtype.ext
      funext y
      simp only [coe_interiorHamiltonian, SmoothForm.coe_funSMulₗ]
      exact RoughForm.interior_smul_pointwise a (P.hamiltonianVectorField h) Ω.1 ▸ rfl
    have hd := congrArg (fun η : SmoothForm I M ℝ m ↦ (mextDerivₗ I m η).1 x v) hι
    rw [P.mextDerivₗ_interiorHamiltonian_eq_lieDerivVolume (SmoothForm.funSMulₗ a Ω) h,
      SmoothForm.mextDerivₗ_funSMulₗ_apply,
      P.mextDerivₗ_interiorHamiltonian_eq_lieDerivVolume Ω h] at hd
    have hda : (mextDeriv (RoughForm.ofFunction I a)).wedge (P.interiorHamiltonian Ω h).1 x
        (v ∘ Fin.cast (show 0 + 1 + m = m + 1 by omega)) =
        (P.bracket a h) x * Ω.1 x v := by
      have hcast : (v ∘ Fin.cast (show 0 + 1 + m = m + 1 by omega)) =
          (v ∘ Fin.cast (Nat.add_comm 1 m)) := by
        funext i; simp
      rw [hcast, coe_interiorHamiltonian, ← apply_smul_topForm_eq_wedge_interior]
      have hd1 : mextDeriv (RoughForm.ofFunction I a) x ![P.hamiltonianVectorField h x] =
          (P.bracket a h) x := by
        rw [mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
          Matrix.cons_val_zero, P.bracket_apply_eq_mvfderiv_hamiltonianVectorField]
      rw [hd1]
    have hlog : ((P.hamiltonianDerivation (logSmooth a ha)) h) x =
        -(a x)⁻¹ * (P.bracket a h) x := by
      rw [SmoothBivector.hamiltonianDerivation_apply]
      unfold logSmooth
      rw [P.bracket_log_right ha h x]
      have hs := congrArg (fun u : C^∞⟮I, M; ℝ⟯ ↦ u x) (P.bracket_skew h a)
      simp only [ContMDiffMap.coe_neg, Pi.neg_apply] at hs
      rw [hs]
      ring
    have hmod : (P.lieDerivVolume Ω h).1 x v = (P.modularApply Ω hΩ h) x * Ω.1 x v := by
      rw [coe_lieDerivVolume, P.mlieDerivForm_eq_modularApply_smul Ω hΩ h x,
        ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    rw [hda, hmod] at hd
    rw [SmoothForm.coe_funSMulₗ, SmoothForm.coe_funSMulₗ, ContinuousAlternatingMap.smul_apply,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul, smul_eq_mul,
      ContMDiffMap.coe_sub, Pi.sub_apply, hlog, hd]
    have hane : a x ≠ 0 := (ha x).ne'
    field_simp [hane]
    ring

/-- **Invariance of Weinstein's Modular Cohomology Class `[Y^Ω] ∈ H¹(M, π)`**:
rescaling `Ω ↦ a • Ω` by any positive smooth density `a > 0` leaves the modular class invariant. -/
theorem cohomologousOneCocycle_modularDerivation_funSMul
    (Ω : SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0)
    (a : C^∞⟮I, M; ℝ⟯) (ha : ∀ x : M, 0 < a x) :
    P.CohomologousOneCocycle
      (P.modularDerivation (SmoothForm.funSMulₗ a Ω)
        (funSMulₗ_ne_zero hΩ fun x ↦ (ha x).ne'))
      (P.modularDerivation Ω hΩ) := by
  refine ⟨-logSmooth a ha, ?_⟩
  rw [P.modularDerivation_funSMul Ω hΩ a ha, P.hamiltonianDerivation_neg]
  abel

/-- Any two co-oriented nowhere-vanishing smooth volume forms `Ω₁, Ω₂` (`Ω₂ / Ω₁ > 0` everywhere)
define the exact same modular cohomology class `[Y^{Ω₂}] = [Y^{Ω₁}] ∈ H¹(M, π)`. -/
theorem cohomologousOneCocycle_modularDerivation_of_pos_ratio
    (Ω₁ Ω₂ : SmoothForm I M ℝ n) (hΩ₁ : ∀ x : M, Ω₁.1 x ≠ 0) (hΩ₂ : ∀ x : M, Ω₂.1 x ≠ 0)
    (hpos : ∀ x : M, 0 < (divVolume Ω₁ hΩ₁ Ω₂) x) :
    P.CohomologousOneCocycle (P.modularDerivation Ω₂ hΩ₂) (P.modularDerivation Ω₁ hΩ₁) := by
  have heq : Ω₂ = SmoothForm.funSMulₗ (divVolume Ω₁ hΩ₁ Ω₂) Ω₁ :=
    (funSMulₗ_divVolume Ω₁ hΩ₁ Ω₂).symm
  have hmod : P.modularDerivation Ω₂ hΩ₂ =
      P.modularDerivation (SmoothForm.funSMulₗ (divVolume Ω₁ hΩ₁ Ω₂) Ω₁)
        (funSMulₗ_ne_zero hΩ₁ fun x ↦ (hpos x).ne') := by
    ext h : 1
    rw [modularDerivation_apply, modularDerivation_apply,
      P.eq_modularApply_iff, ← heq, P.funSMulₗ_modularApply]
  rw [hmod]
  exact P.cohomologousOneCocycle_modularDerivation_funSMul Ω₁ hΩ₁ _ hpos

omit hdim [FiniteDimensional ℝ E] in
/-- Cartan commutator identity `[𝓛_V, ι_W] φ = ι_{[V, W]} φ` for smooth forms and smooth vector
fields. -/
theorem mlieDerivForm_interior_sub {k : ℕ} (φ : SmoothForm I M ℝ (k + 1))
    {V W : (x : M) → TangentSpace I x}
    (hV : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, V x⟩ : TangentBundle I M)))
    (hW : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, W x⟩ : TangentBundle I M))) :
    mlieDerivForm V (RoughForm.interior W φ.1) -
        RoughForm.interior W (mlieDerivForm V φ.1) =
      RoughForm.interior (VectorField.mlieBracket I V W) φ.1 := by
  funext x
  ext v
  let X : Fin k → (y : M) → TangentSpace I y :=
    fun i ↦ FiberBundle.extend E (E := TangentSpace I) (v i)
  have hX (i : Fin k) : MDifferentiableAt I I.tangent
      (fun y ↦ (⟨y, X i y⟩ : TangentBundle I M)) x :=
    (FiberBundle.contMDiffAt_extend (k := ∞) I E (v i)).mdifferentiableAt (by simp)
  have hXself : (X · x) = v :=
    funext fun i ↦ FiberBundle.extend_apply_self (F := E) (E := TangentSpace I) (v := v i)
  have hVd : MDifferentiableAt I I.tangent (fun y ↦ (⟨y, V y⟩ : TangentBundle I M)) x :=
    (hV x).mdifferentiableAt (by simp)
  have hWd : MDifferentiableAt I I.tangent (fun y ↦ (⟨y, W y⟩ : TangentBundle I M)) x :=
    (hW x).mdifferentiableAt (by simp)
  let hφW : SmoothForm I M ℝ k :=
    ⟨RoughForm.interior W φ.1, (φ.isSmoothForm.interior hW).mem_smoothBundleForms⟩
  have h1 := mlieDerivForm_apply_vectorField (V := V) (φ := hφW.1) (X := X)
    (hφW.mdifferentiableAt x) hX
  let WX : Fin (k + 1) → (y : M) → TangentSpace I y :=
    fun j y ↦ Matrix.vecCons (W y) (X · y) j
  have hWX (j : Fin (k + 1)) : MDifferentiableAt I I.tangent
      (fun y ↦ (⟨y, WX j y⟩ : TangentBundle I M)) x := by
    cases j using Fin.cases with
    | zero => exact hWd
    | succ i => exact hX i
  have h2 := mlieDerivForm_apply_vectorField (V := V) (φ := φ.1) (X := WX)
    (φ.mdifferentiableAt x) hWX
  have hWX_x : (WX · x) = Matrix.vecCons (W x) v := by
    funext j
    cases j using Fin.cases with
    | zero => rfl
    | succ i => exact congrFun hXself i
  have hfun : (fun y ↦ hφW.1 y (X · y)) = (fun y ↦ φ.1 y (WX · y)) := by
    funext y
    rw [show hφW.1 = RoughForm.interior W φ.1 from rfl, RoughForm.interior_apply]
  rw [hXself, hfun] at h1
  rw [hWX_x, Fin.sum_univ_succ] at h2
  have hupd0 : Function.update (Matrix.vecCons (W x) v) 0 (mlieBracket I V (WX 0) x) =
      Matrix.vecCons (mlieBracket I V W x) v := by
    funext j
    cases j using Fin.cases <;> simp [WX]
  have hupds (i : Fin k) :
      Function.update (Matrix.vecCons (W x) v) i.succ (mlieBracket I V (WX i.succ) x) =
        Matrix.vecCons (W x) (Function.update v i (mlieBracket I V (X i) x)) := by
    funext j
    cases j using Fin.cases with
    | zero =>
      rw [Function.update_of_ne (Fin.succ_ne_zero i).symm]
      rfl
    | succ l =>
      by_cases hli : l = i
      · subst hli; simp [WX]
      · have hne : l.succ ≠ i.succ := fun h ↦ hli (Fin.succ_inj.mp h)
        rw [Function.update_of_ne hne, Matrix.cons_val_succ, Matrix.cons_val_succ,
          Function.update_of_ne hli]
  simp only [hupd0, hupds] at h2
  rw [Pi.sub_apply, ContinuousAlternatingMap.sub_apply, RoughForm.interior_apply,
    RoughForm.interior_apply, ← show hφW.1 = RoughForm.interior W φ.1 from rfl, h1, h2]
  simp only [show hφW.1 = RoughForm.interior W φ.1 from rfl, RoughForm.interior_apply]
  abel

/-- Commutator identity `[𝓛_V, 𝓛_W] Ω = 𝓛_{[V, W]} Ω` for smooth vector fields acting on any
smooth top form `Ω`. -/
theorem mlieDerivForm_comm_topForm (Ω : SmoothForm I M ℝ n)
    {V W : (x : M) → TangentSpace I x}
    (hV : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, V x⟩ : TangentBundle I M)))
    (hW : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, W x⟩ : TangentBundle I M)))
    (hVW : ContMDiff I I.tangent ∞
      (fun x ↦ (⟨x, VectorField.mlieBracket I V W x⟩ : TangentBundle I M))) :
    mlieDerivForm V (mlieDerivForm W Ω.1) - mlieDerivForm W (mlieDerivForm V Ω.1) =
      mlieDerivForm (VectorField.mlieBracket I V W) Ω.1 := by
  cases n with
  | zero =>
    have hd0 : mextDeriv Ω.1 = 0 := (SmoothForm.isClosed_def Ω).mp (isClosed_topForm Ω)
    simp [mlieDerivForm_eq_interior_mextDeriv, hd0]
  | succ m =>
    let LVΩ : SmoothForm I M ℝ (m + 1) := SmoothBivector.smoothLieDerivForm V hV Ω
    let LWΩ : SmoothForm I M ℝ (m + 1) := SmoothBivector.smoothLieDerivForm W hW Ω
    let ιWΩ : SmoothForm I M ℝ m :=
      ⟨RoughForm.interior W Ω.1, (Ω.isSmoothForm.interior hW).mem_smoothBundleForms⟩
    have hcomm := congrArg mextDeriv (mlieDerivForm_interior_sub Ω hV hW)
    have hm1 : IsSmoothForm I 1 (mlieDerivForm V ιWΩ.1) :=
      (SmoothForm.isSmoothForm ⟨_, SmoothForm.mlieDerivForm_mem_smoothBundleForms ιWΩ hV⟩).of_le
        (by simp)
    have hm2 : IsSmoothForm I 1 (RoughForm.interior W LVΩ.1) :=
      (LVΩ.isSmoothForm.interior hW).of_le (by simp)
    have hsub : mextDeriv (mlieDerivForm V ιWΩ.1 - RoughForm.interior W LVΩ.1) =
        mextDeriv (mlieDerivForm V ιWΩ.1) - mextDeriv (RoughForm.interior W LVΩ.1) := by
      funext x
      rw [sub_eq_add_neg, mextDeriv_add
        ((hm1.contDiffWithinAt_inChartAt_self x).differentiableWithinAt one_ne_zero)
        (((hm2.neg).contDiffWithinAt_inChartAt_self x).differentiableWithinAt one_ne_zero),
        mextDeriv_neg, Pi.neg_apply, Pi.sub_apply, sub_eq_add_neg]
    dsimp only [ιWΩ, LVΩ, SmoothBivector.smoothLieDerivForm] at hsub
    rw [hsub] at hcomm
    have hfirst : mextDeriv (mlieDerivForm V ιWΩ.1) = mlieDerivForm V LWΩ.1 := by
      cases m with
      | zero =>
        rw [mlieDerivForm_eq_interior_mextDeriv V ιWΩ.1]
        have hdι : mextDeriv ιWΩ.1 = LWΩ.1 :=
          (SmoothForm.mlieDerivForm_eq_mextDeriv_interior
            (hW.mdifferentiable (by simp)) (isClosed_topForm Ω)).symm
        rw [hdι, SmoothForm.mlieDerivForm_eq_mextDeriv_interior
          (hV.mdifferentiable (by simp)) (isClosed_topForm LWΩ)]
      | succ l =>
        rw [SmoothForm.mlieDerivForm_eq_interior_mextDeriv_add (φ := ιWΩ)
          (hV.mdifferentiable (by simp))]
        have hdι : mextDeriv ιWΩ.1 = LWΩ.1 :=
          (SmoothForm.mlieDerivForm_eq_mextDeriv_interior
            (hW.mdifferentiable (by simp)) (isClosed_topForm Ω)).symm
        rw [hdι]
        have ha1 : IsSmoothForm I 1 (RoughForm.interior V LWΩ.1) :=
          (LWΩ.isSmoothForm.interior hV).of_le (by simp)
        let hiV : SmoothForm I M ℝ l :=
          ⟨RoughForm.interior V ιWΩ.1, (ιWΩ.isSmoothForm.interior hV).mem_smoothBundleForms⟩
        have ha2 : IsSmoothForm I 1 (mextDeriv hiV.1) := by
          rw [← mextDerivₗ_apply I l hiV]
          exact (mextDerivₗ I l hiV).isSmoothForm.of_le (by simp)
        have hadd : mextDeriv (RoughForm.interior V LWΩ.1 + mextDeriv hiV.1) =
            mextDeriv (RoughForm.interior V LWΩ.1) + mextDeriv (mextDeriv hiV.1) := by
          funext x
          exact mextDeriv_add
            ((ha1.contDiffWithinAt_inChartAt_self x).differentiableWithinAt one_ne_zero)
            ((ha2.contDiffWithinAt_inChartAt_self x).differentiableWithinAt one_ne_zero)
        rw [hadd, SmoothForm.mextDeriv_mextDeriv hiV, add_zero,
          SmoothForm.mlieDerivForm_eq_mextDeriv_interior
            (hV.mdifferentiable (by simp)) (isClosed_topForm LWΩ)]
    have hsecond : mextDeriv (RoughForm.interior W LVΩ.1) = mlieDerivForm W LVΩ.1 :=
      (SmoothForm.mlieDerivForm_eq_mextDeriv_interior
        (hW.mdifferentiable (by simp)) (isClosed_topForm LVΩ)).symm
    have hrhs : mextDeriv (RoughForm.interior (VectorField.mlieBracket I V W) Ω.1) =
        mlieDerivForm (VectorField.mlieBracket I V W) Ω.1 :=
      (SmoothForm.mlieDerivForm_eq_mextDeriv_interior
        (hVW.mdifferentiable (by simp)) (isClosed_topForm Ω)).symm
    dsimp only [ιWΩ, LVΩ, LWΩ, SmoothBivector.smoothLieDerivForm] at hfirst hsecond
    rw [hfirst, hsecond, hrhs] at hcomm
    exact hcomm

/-- **Weinstein's Modular Cocycle Theorem**: `Y^Ω` is a Poisson derivation (Lichnerowicz
`1`-cocycle), i.e., `Y^Ω {g, h}_π = {Y^Ω g, h}_π + {g, Y^Ω h}_π`
(`S4TCdiffeo-Aug-2026.tex`, line 378). -/
theorem isLichnerowiczOneCocycle_modularDerivation [T2Space M]
    (Ω : SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0) :
    P.IsLichnerowiczOneCocycle (P.modularDerivation Ω hΩ) := by
  intro g h
  let _ : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  ext x
  have hstep (u v : C^∞⟮I, M; ℝ⟯) :
      mlieDerivForm (P.hamiltonianVectorField u)
          (mlieDerivForm (P.hamiltonianVectorField v) Ω.1) x =
        ((P.bracket (P.modularApply Ω hΩ v) u) x +
          (P.modularApply Ω hΩ v) x * (P.modularApply Ω hΩ u) x) • Ω.1 x := by
    have heq : mlieDerivForm (P.hamiltonianVectorField v) Ω.1 =
        (SmoothForm.funSMulₗ (P.modularApply Ω hΩ v) Ω).1 := by
      rw [SmoothForm.coe_funSMulₗ]
      funext y
      exact P.mlieDerivForm_eq_modularApply_smul Ω hΩ v y
    rw [heq]
    cases n with
    | zero =>
      have hsub : Subsingleton E := Module.finrank_zero_iff.mp hdim.finrank_eq
      have hd0 : mextDeriv (SmoothForm.funSMulₗ (P.modularApply Ω hΩ v) Ω).1 = 0 :=
        (SmoothForm.isClosed_def _).mp (isClosed_topForm _)
      rw [mlieDerivForm_eq_interior_mextDeriv, hd0, RoughForm.interior_zero, Pi.zero_apply]
      have hm0 (w : C^∞⟮I, M; ℝ⟯) : P.modularApply Ω hΩ w = 0 := by
        unfold modularApply
        have hL0 : P.lieDerivVolume Ω w = 0 := by
          apply Subtype.ext
          rw [coe_lieDerivVolume, mlieDerivForm_eq_interior_mextDeriv,
            (SmoothForm.isClosed_def Ω).mp (isClosed_topForm Ω), RoughForm.interior_zero]
          rfl
        rw [hL0, divVolume_zero]
      rw [hm0 v, P.bracket_apply_eq_mvfderiv_hamiltonianVectorField]
      have hv0 : P.hamiltonianVectorField u x = 0 := by
        have : Subsingleton (TangentSpace I x) := hsub
        exact Subsingleton.elim _ _
      simp [hv0]
    | succ m =>
      let φv := P.modularApply Ω hΩ v
      rw [SmoothForm.mlieDerivForm_eq_mextDeriv_interior
        (P.mdifferentiable_hamiltonianVectorField u)
        (isClosed_topForm (SmoothForm.funSMulₗ φv Ω))]
      have hι : RoughForm.interior (P.hamiltonianVectorField u)
          (SmoothForm.funSMulₗ φv Ω).1 =
          (SmoothForm.funSMulₗ φv (P.interiorHamiltonian Ω u)).1 := by
        rw [SmoothForm.coe_funSMulₗ, SmoothForm.coe_funSMulₗ, coe_interiorHamiltonian]
        exact RoughForm.interior_smul_pointwise φv (P.hamiltonianVectorField u) Ω.1
      rw [hι]
      ext w
      rw [← mextDerivₗ_apply I m (SmoothForm.funSMulₗ φv (P.interiorHamiltonian Ω u)),
        SmoothForm.mextDerivₗ_funSMulₗ_apply,
        P.mextDerivₗ_interiorHamiltonian_eq_lieDerivVolume Ω u]
      have hdφ : (mextDeriv (RoughForm.ofFunction I φv)).wedge (P.interiorHamiltonian Ω u).1 x
          (w ∘ Fin.cast (show 0 + 1 + m = m + 1 by omega)) =
          (P.bracket φv u) x * Ω.1 x w := by
        have hcast : (w ∘ Fin.cast (show 0 + 1 + m = m + 1 by omega)) =
            (w ∘ Fin.cast (Nat.add_comm 1 m)) := by
          funext i; simp
        rw [hcast, coe_interiorHamiltonian, ← apply_smul_topForm_eq_wedge_interior]
        have hd1 : mextDeriv (RoughForm.ofFunction I φv) x ![P.hamiltonianVectorField u x] =
            (P.bracket φv u) x := by
          rw [mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
            Matrix.cons_val_zero, P.bracket_apply_eq_mvfderiv_hamiltonianVectorField]
        rw [hd1]
      have hmod_u : (P.lieDerivVolume Ω u).1 x w = (P.modularApply Ω hΩ u) x * Ω.1 x w := by
        rw [coe_lieDerivVolume, P.mlieDerivForm_eq_modularApply_smul Ω hΩ u x,
          ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      rw [hdφ, hmod_u, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      ring
  have hVW := VectorField.contMDiff_mlieBracket (P.contMDiff_hamiltonianVectorField g)
    (P.contMDiff_hamiltonianVectorField h)
  have hcomm := congrFun (mlieDerivForm_comm_topForm Ω
    (P.contMDiff_hamiltonianVectorField g) (P.contMDiff_hamiltonianVectorField h) hVW) x
  rw [Pi.sub_apply, hstep g h, hstep h g, P.mlieBracket_hamiltonianVectorField g h,
    ← P.hamiltonianVectorField_neg, P.mlieDerivForm_eq_modularApply_smul Ω hΩ _ x] at hcomm
  have hmneg :
      (P.modularApply Ω hΩ (-P.bracket g h)) x = -(P.modularApply Ω hΩ (P.bracket g h)) x := by
    rw [← neg_one_smul ℝ (P.bracket g h), P.modularApply_smul Ω hΩ (-1)]
    simp
  rw [hmneg, ← sub_smul] at hcomm
  have hscalar := smul_left_injective ℝ (hΩ x) hcomm
  have hskew1 : (P.bracket (P.modularApply Ω hΩ h) g) x =
      -(P.bracket g (P.modularApply Ω hΩ h)) x := by
    simpa using congrArg (fun u : C^∞⟮I, M; ℝ⟯ ↦ u x) (P.bracket_skew (P.modularApply Ω hΩ h) g)
  simp only [modularDerivation_apply, ContMDiffMap.coe_add, Pi.add_apply]
  linarith

/-- A Poisson manifold `(M, P)` is **unimodular with respect to `Ω`** (`IsUnimodularWithVolume`)
when `Ω` is a nowhere-vanishing smooth volume form whose modular derivation `Y^Ω` vanishes
identically (equivalently `𝓛_{X_h} Ω = 0` for every `h ∈ C^∞(M)`). -/
def IsUnimodularWithVolume (Ω : SmoothForm I M ℝ n) : Prop :=
  (∀ x : M, Ω.1 x ≠ 0) ∧ ∀ h : C^∞⟮I, M; ℝ⟯, P.lieDerivVolume Ω h = 0

/-- A Poisson manifold `(M, P)` is **unimodular** (`IsUnimodularPoisson`, `S4TCdiffeo-Aug-2026.tex`,
lines 385–386) if it admits a nowhere-vanishing smooth volume form invariant under all Hamiltonian
vector fields. -/
def IsUnimodularPoisson {n : ℕ} [HasFinrank E n] : Prop :=
  ∃ Ω : SmoothForm I M ℝ n, P.IsUnimodularWithVolume Ω

theorem isUnimodularWithVolume_iff_modularDerivation_eq_zero
    (Ω : SmoothForm I M ℝ n) (hΩ : ∀ x : M, Ω.1 x ≠ 0) :
    P.IsUnimodularWithVolume Ω ↔ P.modularDerivation Ω hΩ = 0 := by
  constructor
  · rintro ⟨_, hzero⟩
    ext h : 1
    rw [modularDerivation_apply]
    unfold modularApply
    rw [hzero h, divVolume_zero]
    rfl
  · intro hmod
    refine ⟨hΩ, fun h ↦ ?_⟩
    rw [← P.funSMulₗ_modularApply Ω hΩ h]
    have hh : P.modularApply Ω hΩ h = 0 := by
      simpa using DFunLike.congr_fun hmod h
    rw [hh]
    apply Subtype.ext
    rw [SmoothForm.coe_funSMulₗ]
    funext x
    simp

omit [FiniteDimensional ℝ E] in
theorem IsUnimodularWithVolume.isUnimodularPoisson {Ω : SmoothForm I M ℝ n}
    (h : P.IsUnimodularWithVolume Ω) : P.IsUnimodularPoisson :=
  ⟨Ω, h⟩

/-- **Weinstein's Unimodularity Criterion** (`S4TCdiffeo-Aug-2026.tex`, lines 385–386):
given a reference nowhere-vanishing volume form `Ω₀`, the modular class `[Y^{Ω₀}] ∈ H¹(M, π)`
vanishes (`Y^{Ω₀} = X_u` for some `u ∈ C^∞(M)`) if and only if there exists a positive rescaling
`a • Ω₀` (`a > 0`) that is invariant under all Hamiltonian vector fields. -/
theorem exists_pos_funSMul_isUnimodularWithVolume_iff_exact
    (Ω₀ : SmoothForm I M ℝ n) (hΩ₀ : ∀ x : M, Ω₀.1 x ≠ 0) :
    (∃ a : C^∞⟮I, M; ℝ⟯, (∀ x : M, 0 < a x) ∧
      P.IsUnimodularWithVolume (SmoothForm.funSMulₗ a Ω₀)) ↔
      ∃ u : C^∞⟮I, M; ℝ⟯, P.modularDerivation Ω₀ hΩ₀ = P.hamiltonianDerivation u := by
  constructor
  · rintro ⟨a, ha, hunim⟩
    have hzero := (P.isUnimodularWithVolume_iff_modularDerivation_eq_zero
      (SmoothForm.funSMulₗ a Ω₀) (funSMulₗ_ne_zero hΩ₀ fun x ↦ (ha x).ne')).mp hunim
    rw [P.modularDerivation_funSMul Ω₀ hΩ₀ a ha, sub_eq_zero] at hzero
    exact ⟨logSmooth a ha, hzero⟩
  · rintro ⟨u, hu⟩
    refine ⟨expSmooth u, expSmooth_pos u, ?_⟩
    rw [P.isUnimodularWithVolume_iff_modularDerivation_eq_zero
      (SmoothForm.funSMulₗ (expSmooth u) Ω₀)
      (funSMulₗ_ne_zero hΩ₀ fun x ↦ (expSmooth_pos u x).ne'),
      P.modularDerivation_funSMul Ω₀ hΩ₀ (expSmooth u) (expSmooth_pos u),
      logSmooth_expSmooth, hu, sub_self]

theorem isUnimodularPoisson_of_modularDerivation_exact
    (Ω₀ : SmoothForm I M ℝ n) (hΩ₀ : ∀ x : M, Ω₀.1 x ≠ 0)
    (hexact : ∃ u : C^∞⟮I, M; ℝ⟯, P.modularDerivation Ω₀ hΩ₀ = P.hamiltonianDerivation u) :
    P.IsUnimodularPoisson := by
  obtain ⟨a, _, hunim⟩ := (P.exists_pos_funSMul_isUnimodularWithVolume_iff_exact Ω₀ hΩ₀).mpr hexact
  exact hunim.isUnimodularPoisson

end Modular

end Basic

end PoissonStructure

end S4TuringPoisson
