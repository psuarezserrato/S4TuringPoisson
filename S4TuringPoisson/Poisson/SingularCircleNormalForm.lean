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

public import S4TuringPoisson.Poisson.JacobianPoisson
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype
public import TauCeti.Geometry.Manifold.DifferentialForm.AddCircle

/-!
# Singular-Circle Normal Form, Free Involution, and Leaf Symplectic Forms (M1.3)

This module formalizes Milestone M1.3 of `S4TuringPoisson`, establishing Equations (3)–(5) of
`S4TCdiffeo-Aug-2026.tex` (García-Naranjo–Suárez-Serrato–Vera `GSV15`, Propositions 3.2 & 3.3) on
the tubular neighborhood `S¹ × B³` (`NormalBundleTube := AddCircle (2 * π) × OpenBall3`):

1. **Conformal Scalar Rescaling of Smooth Bivectors (`SmoothBivector.smulFunction`)**:
   - Extensionality for `SmoothBivector` and `PoissonStructure`, plus smooth conformal rescaling
     `k • π` (`(B.smulFunction k).bracket g h = k * B.bracket g h`).

2. **Equation (3) — Singular-Circle Poisson Normal Form (`singularCirclePoisson k`)**:
   - For every smooth function `k ∈ C^∞(S¹ × B³)` (without any non-vanishing restriction), defines
     `π_k = k(θ, x₁, x₂, x₃) (x₁ ∂_{x₂}∧∂_{x₃} + x₂ ∂_{x₁}∧∂_{x₃} - x₃ ∂_{x₁}∧∂_{x₂})` and proves
     the **Jacobi identity** globally on `S¹ × B³`.
   - Proves that smooth functions of `θ` (`u ∘ Prod.fst`) and the indefinite quadratic cone
     `casimirQuad(θ, x) = -x₁² + x₂² + x₃²` are Casimir functions of `π_k`, and that `π_k`
     vanishes along `singularCircleLocus = S¹ × {0}`.
   - Proves that whenever `k` is nowhere-vanishing (`∀ q, k q ≠ 0`), `π_k` coincides with the
     Jacobian–Poisson structure `jacobianPoisson` of `F(θ, x) = (θ, -x₁² + x₂² + x₃²)` with volume
     `(-2 / k) dθ ∧ dx₁ ∧ dx₂ ∧ dx₃` and cylinder area form `dθ ∧ dt`, and is globally unimodular
     with invariant volume `(1 / k) dθ ∧ dx₁ ∧ dx₂ ∧ dx₃` (`IsUnimodularWithVolume`,
     `IsUnimodularPoisson`).

3. **Equation (4) (`GSV15` Proposition 3.2) — Non-Orientable Bundle Involution**:
   - Defines `normalInvolution(θ, x₁, x₂, x₃) = (θ + π, -x₁, -x₂, x₃)`
     (`normalInvolutionDiffeomorph` on `S¹ × B³`), proving it is a smooth, **free** involution
     preserving `singularCircleLocus`, `casimirQuad`, and `dθ ∧ dx₁ ∧ dx₂ ∧ dx₃`, and is a
     **Poisson diffeomorphism** of `π_k` (preserving `(1 / k) dθ ∧ dx₁ ∧ dx₂ ∧ dx₃`) whenever
     `k ∘ normalInvolution = k`.

4. **Equation (5) (`GSV15` Proposition 3.3) — Regular-Leaf Symplectic Form**:
   - Proves that at every `q = (θ, x)` with `x ≠ 0` and `k q ≠ 0`, `rankAt q = 2`, the leaf tangent
     plane `Im(#_{π_k, q})` is `{v | v_θ = 0 ∧ ⟪leafUnitNormal q, v_x⟫ = 0}`, and the regular-leaf
     2-form `ω_{Σ_q} = (k(q) √(x₁² + x₂² + x₃²))⁻¹ ω_Area` is nondegenerate on `Im(#_{π_k, q})`
     and satisfies `ω_{Σ_q}(X_g(q), X_h(q)) = -{g, h}_{π_k}(q)`.
-/

@[expose] public section

noncomputable section

open Bundle Filter Function Metric Module Set TauCeti TopologicalSpace
open scoped ContDiff Manifold Real Topology

namespace S4TuringPoisson

/-! ## 1. Extensionality and Smooth Scalar Multiplication of Bivectors -/

section BivectorRescaling

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem SmoothBivector.ext {B₁ B₂ : SmoothBivector I M}
    (h : ∀ (x : M) (α : TangentSpace I x →L[ℝ] ℝ), B₁.anchor x α = B₂.anchor x α) :
    B₁ = B₂ := by
  cases B₁
  cases B₂
  congr
  funext x
  ext α
  exact h x α

theorem PoissonStructure.ext {P₁ P₂ : PoissonStructure I M}
    (h : P₁.toSmoothBivector = P₂.toSmoothBivector) :
    P₁ = P₂ := by
  cases P₁
  cases P₂
  congr

/-- Multiply a smooth bivector `B` pointwise by a smooth scalar function `k ∈ C^∞(M)`. -/
def SmoothBivector.smulFunction (B : SmoothBivector I M) (k : C^∞⟮I, M; ℝ⟯) :
    SmoothBivector I M where
  anchor x := k x • B.anchor x
  anchor_skew x α β := by
    simp only [smul_apply, map_smul, smul_eq_mul, B.anchor_skew x α β]
    ring
  contMDiff_anchor α := k.contMDiff.smul_section (B.contMDiff_anchor α)

@[simp]
theorem SmoothBivector.smulFunction_anchor_apply (B : SmoothBivector I M) (k : C^∞⟮I, M; ℝ⟯)
    (x : M) (α : TangentSpace I x →L[ℝ] ℝ) :
    (B.smulFunction k).anchor x α = k x • B.anchor x α :=
  rfl

@[simp]
theorem SmoothBivector.smulFunction_bivector_apply (B : SmoothBivector I M) (k : C^∞⟮I, M; ℝ⟯)
    (x : M) (α β : TangentSpace I x →L[ℝ] ℝ) :
    (B.smulFunction k).bivector x α β = k x * B.bivector x α β := by
  simp [SmoothBivector.bivector]

@[simp]
theorem SmoothBivector.smulFunction_hamiltonianVectorField (B : SmoothBivector I M)
    (k h : C^∞⟮I, M; ℝ⟯) (x : M) :
    (B.smulFunction k).hamiltonianVectorField h x = k x • B.hamiltonianVectorField h x := by
  simp [SmoothBivector.hamiltonianVectorField, smul_neg]

@[simp]
theorem SmoothBivector.smulFunction_bracket (B : SmoothBivector I M) (k g h : C^∞⟮I, M; ℝ⟯) :
    (B.smulFunction k).bracket g h = k * B.bracket g h := by
  ext x
  simp only [SmoothBivector.bracket_apply, SmoothBivector.smulFunction_bivector_apply,
    ContMDiffMap.coe_mul, Pi.mul_apply]

end BivectorRescaling

/-! ## 2. Tubular Neighborhood `S¹ × B³`, Coordinates, and Standard Volume `4`-Form -/

instance instFactTwoPiPos : Fact (0 < 2 * Real.pi) :=
  ⟨Real.two_pi_pos⟩

/-- The smooth circle `S¹ = ℝ ⧸ (2πℤ)` with canonical angular period `2π`. -/
abbrev CircleS1 : Type := AddCircle (2 * Real.pi)

/-- The open unit 3-ball `B³ = B(0, 1) ⊂ ℝ³` viewed as an open smooth submanifold of `ℝ³`. -/
def OpenBall3 : Opens (EuclideanSpace ℝ (Fin 3)) :=
  ⟨Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Metric.isOpen_ball⟩

/-- Trivial tubular neighborhood `S¹ × B³` of an embedded singular circle (`GSV15`, Section 3). -/
abbrev NormalBundleTube : Type := CircleS1 × OpenBall3

/-- Smooth model with corners `𝓘(ℝ) × 𝓡 3` of `NormalBundleTube = S¹ × B³`. -/
abbrev tubeModel := 𝓘(ℝ).prod (𝓡 3)

/-- Smooth model with corners `𝓘(ℝ) × 𝓘(ℝ)` of the Casimir cylinder `S¹ × ℝ`. -/
abbrev cylinderModel := 𝓘(ℝ).prod 𝓘(ℝ)

section Euclidean3Volume

local instance instFactFinrankEuclidean3 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- Explicit determinant formula for `euclideanVolumeForm 3` on any triple `![u, v, w]` in `ℝ³`. -/
theorem euclidean3VolumeForm_triple (x u v w : EuclideanSpace ℝ (Fin 3)) :
    (euclideanVolumeForm 3).1 x
      ![(u : TangentSpace (𝓡 3) x), (v : TangentSpace (𝓡 3) x), (w : TangentSpace (𝓡 3) x)] =
      u 0 * (v 1 * w 2 - v 2 * w 1) -
        u 1 * (v 0 * w 2 - v 2 * w 0) +
        u 2 * (v 0 * w 1 - v 1 * w 0) := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have hor : b.orientation = (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation := rfl
  change b.orientation.volumeFormL ![u, v, w] = _
  rw [Orientation.volumeFormL_apply,
    b.orientation.volumeForm_robust (EuclideanSpace.basisFun (Fin 3) ℝ) hor, b.det_apply,
    Matrix.det_fin_three]
  simp [b, Module.Basis.toMatrix_apply, EuclideanSpace.basisFun_repr]
  ring

end Euclidean3Volume

@[simp]
theorem basisFun_fin3_apply (i j : Fin 3) :
    (EuclideanSpace.basisFun (Fin 3) ℝ i) j = if j = i then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [EuclideanSpace.basisFun_apply]

/-- Canonical continuous linear identification `T_θ S¹ ≃L[ℝ] ℝ`. -/
def thetaTangentEquiv (θ : CircleS1) : TangentSpace 𝓘(ℝ) θ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.refl ℝ ℝ

@[simp]
theorem thetaTangentEquiv_apply (θ : CircleS1) (v : TangentSpace 𝓘(ℝ) θ) :
    thetaTangentEquiv θ v = v :=
  rfl

/-- Canonical continuous linear identification `T_x B³ ≃L[ℝ] ℝ³`. -/
def fiberTangentEquiv (x : OpenBall3) :
    TangentSpace (𝓡 3) x ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (TauCeti.Manifold.tangentSpaceOpenEquiv x).trans (NormedSpace.fromTangentSpace x.1)

/-- Canonical continuous linear identification `T_q (S¹ × B³) ≃L[ℝ] ℝ × ℝ³`. -/
def tubeTangentEquiv (q : NormalBundleTube) :
    TangentSpace tubeModel q ≃L[ℝ] ℝ × EuclideanSpace ℝ (Fin 3) :=
  (TauCeti.Manifold.tangentSpaceProdEquiv q).trans
    ((thetaTangentEquiv q.1).prodCongr (fiberTangentEquiv q.2))

/-- Canonical continuous linear identification `T_y (S¹ × ℝ) ≃L[ℝ] ℝ × ℝ`. -/
def cylinderTangentEquiv (y : CircleS1 × ℝ) :
    TangentSpace cylinderModel y ≃L[ℝ] ℝ × ℝ :=
  (TauCeti.Manifold.tangentSpaceProdEquiv y).trans
    ((thetaTangentEquiv y.1).prodCongr (NormedSpace.fromTangentSpace y.2))

/-- Ambient fiber projection `S¹ × B³ → ℝ³` sending `(θ, x)` to `(x : ℝ³)`. -/
def tubeFiberIncl (q : NormalBundleTube) : EuclideanSpace ℝ (Fin 3) :=
  q.2.1

theorem contMDiff_tubeFiberIncl : ContMDiff tubeModel (𝓡 3) ∞ tubeFiberIncl :=
  contMDiff_subtype_val.comp contMDiff_snd

/-- Smooth `i`-th fiber coordinate `x_i : C^∞(S¹ × B³)` (`i ∈ {0, 1, 2}` corresponding to
`(x₁, x₂, x₃)` in 1-indexed notation). -/
def tubeCoord (i : Fin 3) : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯ :=
  (euclideanCoord i).comp ⟨tubeFiberIncl, contMDiff_tubeFiberIncl⟩

@[simp]
theorem tubeCoord_apply (i : Fin 3) (q : NormalBundleTube) :
    tubeCoord i q = q.2.1 i :=
  rfl

/-- Unit angular tangent vector `∂_θ` at `q ∈ S¹ × B³`. -/
def tubeTangentTheta (q : NormalBundleTube) : TangentSpace tubeModel q :=
  (tubeTangentEquiv q).symm (1, 0)

/-- Fiber tangent vector `(0, v)` at `q ∈ S¹ × B³` associated to `v ∈ ℝ³`. -/
def tubeTangentFiber (q : NormalBundleTube) (v : EuclideanSpace ℝ (Fin 3)) :
    TangentSpace tubeModel q :=
  (tubeTangentEquiv q).symm (0, v)

@[simp]
theorem tubeTangentEquiv_theta (q : NormalBundleTube) :
    tubeTangentEquiv q (tubeTangentTheta q) = (1, 0) :=
  ContinuousLinearEquiv.apply_symm_apply _ _

@[simp]
theorem tubeTangentEquiv_fiber (q : NormalBundleTube) (v : EuclideanSpace ℝ (Fin 3)) :
    tubeTangentEquiv q (tubeTangentFiber q v) = (0, v) :=
  ContinuousLinearEquiv.apply_symm_apply _ _

@[simp]
theorem tubeTangentFiber_zero (q : NormalBundleTube) :
    tubeTangentFiber q 0 = 0 := by
  apply (tubeTangentEquiv q).injective
  simp

@[simp]
theorem tubeTangentFiber_smul (q : NormalBundleTube) (c : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    c • tubeTangentFiber q v = tubeTangentFiber q (c • v) := by
  apply (tubeTangentEquiv q).injective
  simp

@[simp]
theorem tubeTangentFiber_neg (q : NormalBundleTube) (v : EuclideanSpace ℝ (Fin 3)) :
    -tubeTangentFiber q v = tubeTangentFiber q (-v) := by
  apply (tubeTangentEquiv q).injective
  simp

theorem tubeTangent_decomp (q : NormalBundleTube) (v : TangentSpace tubeModel q) :
    v = (tubeTangentEquiv q v).1 • tubeTangentTheta q +
      tubeTangentFiber q (tubeTangentEquiv q v).2 := by
  apply (tubeTangentEquiv q).injective
  ext j <;> simp

/-- Standard 4-tuple `(∂_θ, ∂_{x₀}, ∂_{x₁}, ∂_{x₂})` at `q ∈ S¹ × B³`. -/
def tubeTangentFrame (q : NormalBundleTube) : Fin 4 → TangentSpace tubeModel q :=
  ![tubeTangentTheta q,
    tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 0),
    tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 1),
    tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 2)]

theorem mfderiv_fst_tube_apply (q : NormalBundleTube) (v : TangentSpace tubeModel q) :
    thetaTangentEquiv q.1 (mfderiv tubeModel 𝓘(ℝ) Prod.fst q v) = (tubeTangentEquiv q v).1 := by
  rw [mfderiv_fst]
  simp only [tubeTangentEquiv, thetaTangentEquiv, ContinuousLinearEquiv.trans_apply,
    TauCeti.Manifold.tangentSpaceProdEquiv_apply]
  rfl

@[simp]
theorem mfderiv_fst_tubeTangentTheta (q : NormalBundleTube) :
    thetaTangentEquiv q.1 (mfderiv tubeModel 𝓘(ℝ) Prod.fst q (tubeTangentTheta q)) = 1 := by
  rw [mfderiv_fst_tube_apply, tubeTangentEquiv_theta]

@[simp]
theorem mfderiv_fst_tubeTangentFiber (q : NormalBundleTube) (v : EuclideanSpace ℝ (Fin 3)) :
    thetaTangentEquiv q.1 (mfderiv tubeModel 𝓘(ℝ) Prod.fst q (tubeTangentFiber q v)) = 0 := by
  rw [mfderiv_fst_tube_apply, tubeTangentEquiv_fiber]

theorem mfderiv_tubeFiberIncl_apply (q : NormalBundleTube) (v : TangentSpace tubeModel q) :
    NormedSpace.fromTangentSpace (tubeFiberIncl q)
        (mfderiv tubeModel (𝓡 3) tubeFiberIncl q v) =
      (tubeTangentEquiv q v).2 := by
  have heq : tubeFiberIncl =
      (Subtype.val : OpenBall3 → EuclideanSpace ℝ (Fin 3)) ∘ Prod.snd := rfl
  have hsnd : MDifferentiableAt tubeModel (𝓡 3)
      (Prod.snd : NormalBundleTube → OpenBall3) q :=
    mdifferentiableAt_snd
  have hsub : MDifferentiableAt (𝓡 3) (𝓡 3)
      (Subtype.val : OpenBall3 → EuclideanSpace ℝ (Fin 3)) q.2 :=
    (contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)
  rw [heq, mfderiv_comp q hsub hsnd, ContinuousLinearMap.comp_apply,
    TauCeti.Manifold.mfderiv_subtype_val, mfderiv_snd]
  simp only [tubeTangentEquiv, fiberTangentEquiv, ContinuousLinearEquiv.trans_apply,
    TauCeti.Manifold.tangentSpaceProdEquiv_apply]
  rfl

@[simp]
theorem mfderiv_tubeFiberIncl_tubeTangentTheta (q : NormalBundleTube) :
    mfderiv tubeModel (𝓡 3) tubeFiberIncl q (tubeTangentTheta q) = 0 := by
  apply (NormedSpace.fromTangentSpace (tubeFiberIncl q)).injective
  rw [mfderiv_tubeFiberIncl_apply, tubeTangentEquiv_theta, map_zero]

@[simp]
theorem mfderiv_tubeFiberIncl_tubeTangentFiber (q : NormalBundleTube)
    (v : EuclideanSpace ℝ (Fin 3)) :
    mfderiv tubeModel (𝓡 3) tubeFiberIncl q (tubeTangentFiber q v) =
      (NormedSpace.fromTangentSpace (tubeFiberIncl q)).symm v := by
  apply (NormedSpace.fromTangentSpace (tubeFiberIncl q)).injective
  rw [mfderiv_tubeFiberIncl_apply, tubeTangentEquiv_fiber,
    ContinuousLinearEquiv.apply_symm_apply]

@[simp]
theorem mvfderiv_tubeCoord_tubeTangentTheta (i : Fin 3) (q : NormalBundleTube) :
    mvfderiv tubeModel (tubeCoord i) q (tubeTangentTheta q) = 0 := by
  have h1 : MDifferentiableAt (𝓡 3) 𝓘(ℝ) (euclideanCoord i) (tubeFiberIncl q) :=
    (euclideanCoord i).contMDiff.mdifferentiableAt (by simp)
  have h2 : MDifferentiableAt tubeModel (𝓡 3) tubeFiberIncl q :=
    contMDiff_tubeFiberIncl.mdifferentiableAt (by simp)
  have hc := mvfderiv_comp_apply q h1 h2 (tubeTangentTheta q)
  change mvfderiv tubeModel ((euclideanCoord i) ∘ tubeFiberIncl) q (tubeTangentTheta q) = 0
  rw [hc, mfderiv_tubeFiberIncl_tubeTangentTheta, map_zero]

@[simp]
theorem mvfderiv_tubeCoord_tubeTangentFiber (i : Fin 3) (q : NormalBundleTube)
    (v : EuclideanSpace ℝ (Fin 3)) :
    mvfderiv tubeModel (tubeCoord i) q (tubeTangentFiber q v) = v i := by
  have h1 : MDifferentiableAt (𝓡 3) 𝓘(ℝ) (euclideanCoord i) (tubeFiberIncl q) :=
    (euclideanCoord i).contMDiff.mdifferentiableAt (by simp)
  have h2 : MDifferentiableAt tubeModel (𝓡 3) tubeFiberIncl q :=
    contMDiff_tubeFiberIncl.mdifferentiableAt (by simp)
  have hc := mvfderiv_comp_apply q h1 h2 (tubeTangentFiber q v)
  change mvfderiv tubeModel ((euclideanCoord i) ∘ tubeFiberIncl) q (tubeTangentFiber q v) = v i
  rw [hc, mfderiv_tubeFiberIncl_tubeTangentFiber, mvfderiv_eq_fderiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, fderiv_euclideanCoord_apply]

/-- Pulled-back angular 1-form `dθ` on `NormalBundleTube = S¹ × B³`. -/
def tubeAngularForm : SmoothForm tubeModel NormalBundleTube ℝ 1 :=
  SmoothForm.mpullback Prod.fst contMDiff_fst (AddCircle.timeForm (2 * Real.pi))

/-- Pulled-back fiber 3-form `dx₀ ∧ dx₁ ∧ dx₂` on `NormalBundleTube = S¹ × B³`. -/
def tubeFiberVolumeForm : SmoothForm tubeModel NormalBundleTube ℝ 3 :=
  SmoothForm.mpullback tubeFiberIncl contMDiff_tubeFiberIncl (euclideanVolumeForm 3)

/-- Standard product volume `4`-form `dθ ∧ dx₀ ∧ dx₁ ∧ dx₂` on `S¹ × B³`. -/
def tubeVolumeForm : SmoothForm tubeModel NormalBundleTube ℝ 4 :=
  SmoothForm.wedge tubeAngularForm tubeFiberVolumeForm

@[simp]
theorem tubeAngularForm_apply_theta (q : NormalBundleTube) :
    tubeAngularForm.1 q ![tubeTangentTheta q] = 1 := by
  rw [tubeAngularForm, SmoothForm.mpullback_apply, AddCircle.timeForm_apply]
  exact mfderiv_fst_tubeTangentTheta q

@[simp]
theorem tubeAngularForm_apply_fiber (q : NormalBundleTube) (v : EuclideanSpace ℝ (Fin 3)) :
    tubeAngularForm.1 q ![tubeTangentFiber q v] = 0 := by
  rw [tubeAngularForm, SmoothForm.mpullback_apply, AddCircle.timeForm_apply]
  exact mfderiv_fst_tubeTangentFiber q v

@[simp]
theorem tubeVolumeForm_apply_frame (q : NormalBundleTube) :
    tubeVolumeForm.1 q (tubeTangentFrame q) = 1 := by
  dsimp only [tubeVolumeForm, tubeTangentFrame]
  rw [SmoothForm.coe_wedge, RoughForm.wedge_def, RoughForm.wedgeWith_apply',
    pairedWedge_one_three_apply, tubeAngularForm_apply_theta,
    tubeAngularForm_apply_fiber, tubeAngularForm_apply_fiber, tubeAngularForm_apply_fiber]
  have hfib : tubeFiberVolumeForm.1 q
      ![tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 0),
        tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 1),
        tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 2)] = 1 := by
    rw [tubeFiberVolumeForm, SmoothForm.mpullback_apply]
    have hvec : (fun i : Fin 3 ↦
        mfderiv tubeModel (𝓡 3) tubeFiberIncl q
          (![tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 0),
            tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 1),
            tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 2)] i)) =
        fun i : Fin 3 ↦
          (EuclideanSpace.basisFun (Fin 3) ℝ i : TangentSpace (𝓡 3) (tubeFiberIncl q)) := by
      funext i
      fin_cases i
      · change mfderiv tubeModel (𝓡 3) tubeFiberIncl q
          (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 0)) = _
        rw [mfderiv_tubeFiberIncl_tubeTangentFiber]
        exact NormedSpace.fromTangentSpace_symm_apply (𝕜 := ℝ) (tubeFiberIncl q) _
      · change mfderiv tubeModel (𝓡 3) tubeFiberIncl q
          (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 1)) = _
        rw [mfderiv_tubeFiberIncl_tubeTangentFiber]
        exact NormedSpace.fromTangentSpace_symm_apply (𝕜 := ℝ) (tubeFiberIncl q) _
      · change mfderiv tubeModel (𝓡 3) tubeFiberIncl q
          (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 2)) = _
        rw [mfderiv_tubeFiberIncl_tubeTangentFiber]
        exact NormedSpace.fromTangentSpace_symm_apply (𝕜 := ℝ) (tubeFiberIncl q) _
    rw [hvec, euclideanVolumeForm_apply_basisFun 3]
  rw [hfib]
  ring

theorem tubeVolumeForm_ne_zero (q : NormalBundleTube) : tubeVolumeForm.1 q ≠ 0 := by
  intro h
  have h1 := DFunLike.congr_fun h (tubeTangentFrame q)
  exact one_ne_zero ((tubeVolumeForm_apply_frame q).symm.trans h1)

/-! ## 3. Equation (3): Singular-Circle Poisson Structure, Casimirs, and Unimodularity -/

/-- Standard area `2`-form `dθ ∧ dt` on the Casimir cylinder `S¹ × ℝ`. -/
def cylinderAreaForm : SmoothForm cylinderModel (CircleS1 × ℝ) ℝ 2 :=
  SmoothForm.wedge
    (SmoothForm.mpullback Prod.fst contMDiff_fst (AddCircle.timeForm (2 * Real.pi)))
    (SmoothForm.mpullback Prod.snd contMDiff_snd SmoothForm.realLineCoordForm)

theorem cylinderAreaForm_pair (y : CircleS1 × ℝ) (v w : TangentSpace cylinderModel y) :
    cylinderAreaForm.1 y ![v, w] =
      (cylinderTangentEquiv y v).1 * (cylinderTangentEquiv y w).2 -
        (cylinderTangentEquiv y w).1 * (cylinderTangentEquiv y v).2 := by
  rw [← SmoothBundleForm.eval₂_apply, cylinderAreaForm,
    AddCircle.eval₂_wedge_timeForm_realLineCoordForm]
  simp only [cylinderTangentEquiv, thetaTangentEquiv, ContinuousLinearEquiv.trans_apply,
    TauCeti.Manifold.tangentSpaceProdEquiv_apply]
  rfl

theorem cylinderAreaForm_ne_zero (y : CircleS1 × ℝ) : cylinderAreaForm.1 y ≠ 0 := by
  intro h
  let e₀ : TangentSpace cylinderModel y := (cylinderTangentEquiv y).symm (1, 0)
  let e₁ : TangentSpace cylinderModel y := (cylinderTangentEquiv y).symm (0, 1)
  have h1 := DFunLike.congr_fun h ![e₀, e₁]
  have h2 := cylinderAreaForm_pair y e₀ e₁
  change cylinderAreaForm.1 y ![e₀, e₁] = (0 : ℝ) at h1
  rw [h1] at h2
  simp [e₀, e₁] at h2

/-- Indefinite quadratic Casimir `Q(θ, x₁, x₂, x₃) = -x₁² + x₂² + x₃²` on `S¹ × B³`. -/
def casimirQuad : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯ :=
  -(tubeCoord 0 * tubeCoord 0) + tubeCoord 1 * tubeCoord 1 + tubeCoord 2 * tubeCoord 2

@[simp]
theorem casimirQuad_apply (q : NormalBundleTube) :
    casimirQuad q = -(q.2.1 0) ^ 2 + (q.2.1 1) ^ 2 + (q.2.1 2) ^ 2 := by
  simp only [casimirQuad, ContMDiffMap.coe_add, ContMDiffMap.coe_neg, ContMDiffMap.coe_mul,
    Pi.add_apply, Pi.neg_apply, Pi.mul_apply, tubeCoord_apply]
  ring

theorem mvfderiv_casimirQuad_tubeTangentTheta (q : NormalBundleTube) :
    mvfderiv tubeModel casimirQuad q (tubeTangentTheta q) = 0 := by
  have hd (i : Fin 3) : MDifferentiableAt tubeModel 𝓘(ℝ) (tubeCoord i) q :=
    (tubeCoord i).contMDiff.mdifferentiableAt (by simp)
  have hd00 : MDifferentiableAt tubeModel 𝓘(ℝ) (tubeCoord 0 * tubeCoord 0) q :=
    (tubeCoord 0 * tubeCoord 0).contMDiff.mdifferentiableAt (by simp)
  have hd11 : MDifferentiableAt tubeModel 𝓘(ℝ) (tubeCoord 1 * tubeCoord 1) q :=
    (tubeCoord 1 * tubeCoord 1).contMDiff.mdifferentiableAt (by simp)
  have hd22 : MDifferentiableAt tubeModel 𝓘(ℝ) (tubeCoord 2 * tubeCoord 2) q :=
    (tubeCoord 2 * tubeCoord 2).contMDiff.mdifferentiableAt (by simp)
  have hcoe : ⇑casimirQuad =
      (-⇑(tubeCoord 0 * tubeCoord 0) + ⇑(tubeCoord 1 * tubeCoord 1)) +
        ⇑(tubeCoord 2 * tubeCoord 2) := rfl
  rw [hcoe, mvfderiv_add (hd00.neg.add hd11) hd22, add_apply,
    mvfderiv_add hd00.neg hd11, add_apply, mvfderiv_neg, neg_apply]
  have hm (i : Fin 3) :
      mvfderiv tubeModel (tubeCoord i * tubeCoord i) q (tubeTangentTheta q) = 0 := by
    rw [ContMDiffMap.coe_mul, mvfderiv_mul (hd i) (hd i), add_apply, smul_apply,
      mvfderiv_tubeCoord_tubeTangentTheta, smul_zero, add_zero]
  rw [hm 0, hm 1, hm 2]
  norm_num

theorem mvfderiv_casimirQuad_tubeTangentFiber (q : NormalBundleTube)
    (v : EuclideanSpace ℝ (Fin 3)) :
    mvfderiv tubeModel casimirQuad q (tubeTangentFiber q v) =
      -2 * q.2.1 0 * v 0 + 2 * q.2.1 1 * v 1 + 2 * q.2.1 2 * v 2 := by
  have hd (i : Fin 3) : MDifferentiableAt tubeModel 𝓘(ℝ) (tubeCoord i) q :=
    (tubeCoord i).contMDiff.mdifferentiableAt (by simp)
  have hd00 : MDifferentiableAt tubeModel 𝓘(ℝ) (tubeCoord 0 * tubeCoord 0) q :=
    (tubeCoord 0 * tubeCoord 0).contMDiff.mdifferentiableAt (by simp)
  have hd11 : MDifferentiableAt tubeModel 𝓘(ℝ) (tubeCoord 1 * tubeCoord 1) q :=
    (tubeCoord 1 * tubeCoord 1).contMDiff.mdifferentiableAt (by simp)
  have hd22 : MDifferentiableAt tubeModel 𝓘(ℝ) (tubeCoord 2 * tubeCoord 2) q :=
    (tubeCoord 2 * tubeCoord 2).contMDiff.mdifferentiableAt (by simp)
  have hcoe : ⇑casimirQuad =
      (-⇑(tubeCoord 0 * tubeCoord 0) + ⇑(tubeCoord 1 * tubeCoord 1)) +
        ⇑(tubeCoord 2 * tubeCoord 2) := rfl
  rw [hcoe, mvfderiv_add (hd00.neg.add hd11) hd22, add_apply,
    mvfderiv_add hd00.neg hd11, add_apply, mvfderiv_neg, neg_apply]
  have hm (i : Fin 3) :
      mvfderiv tubeModel (tubeCoord i * tubeCoord i) q (tubeTangentFiber q v) =
        2 * q.2.1 i * v i := by
    rw [ContMDiffMap.coe_mul, mvfderiv_mul (hd i) (hd i), add_apply, smul_apply, smul_eq_mul,
      tubeCoord_apply, mvfderiv_tubeCoord_tubeTangentFiber]
    ring
  rw [hm 0, hm 1, hm 2]
  ring

/-- Joint Casimir map `F(θ, x₁, x₂, x₃) = (θ, -x₁² + x₂² + x₃²) : S¹ × B³ → S¹ × ℝ`. -/
def singularCircleCasimirMap (q : NormalBundleTube) : CircleS1 × ℝ :=
  (q.1, casimirQuad q)

theorem contMDiff_singularCircleCasimirMap :
    ContMDiff tubeModel cylinderModel ∞ singularCircleCasimirMap :=
  contMDiff_fst.prodMk casimirQuad.contMDiff

theorem mfderiv_singularCircleCasimirMap_apply (q : NormalBundleTube)
    (v : TangentSpace tubeModel q) :
    cylinderTangentEquiv (singularCircleCasimirMap q)
        (mfderiv tubeModel cylinderModel singularCircleCasimirMap q v) =
      ((tubeTangentEquiv q v).1, mvfderiv tubeModel casimirQuad q v) := by
  have h1 : MDifferentiableAt tubeModel 𝓘(ℝ) Prod.fst q := mdifferentiableAt_fst
  have h2 : MDifferentiableAt tubeModel 𝓘(ℝ) casimirQuad q :=
    casimirQuad.contMDiff.mdifferentiableAt (by simp)
  have heq : singularCircleCasimirMap = fun p : NormalBundleTube ↦ (p.1, casimirQuad p) := rfl
  rw [cylinderTangentEquiv, ContinuousLinearEquiv.trans_apply,
    TauCeti.Manifold.tangentSpaceProdEquiv_apply,
    tubeTangentEquiv, ContinuousLinearEquiv.trans_apply,
    TauCeti.Manifold.tangentSpaceProdEquiv_apply,
    heq, mfderiv_prodMk h1 h2, mfderiv_fst, mvfderiv_apply_eq_mfderiv_apply]
  rfl

/-- Unit scaled volume `4`-form `(-2) • (dθ ∧ dx₀ ∧ dx₁ ∧ dx₂)` realizing `k ≡ 1`. -/
def unitScaledTubeVolumeForm : SmoothForm tubeModel NormalBundleTube ℝ 4 :=
  (-2 : ℝ) • tubeVolumeForm

@[simp]
theorem unitScaledTubeVolumeForm_apply (q : NormalBundleTube)
    (v : Fin 4 → TangentSpace tubeModel q) :
    unitScaledTubeVolumeForm.1 q v = (-2 : ℝ) * tubeVolumeForm.1 q v := by
  rw [unitScaledTubeVolumeForm, SmoothForm.smul_toRoughForm, Pi.smul_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]

@[simp]
theorem unitScaledTubeVolumeForm_apply_frame (q : NormalBundleTube) :
    unitScaledTubeVolumeForm.1 q (tubeTangentFrame q) = -2 := by
  rw [unitScaledTubeVolumeForm_apply, tubeVolumeForm_apply_frame, mul_one]

theorem unitScaledTubeVolumeForm_ne_zero (q : NormalBundleTube) :
    unitScaledTubeVolumeForm.1 q ≠ 0 := by
  intro h
  have h1 := DFunLike.congr_fun h (tubeTangentFrame q)
  rw [unitScaledTubeVolumeForm_apply_frame] at h1
  norm_num at h1

/-- Unit singular-circle Jacobian–Poisson structure (`k ≡ 1`). -/
def singularCircleUnitPoisson : PoissonStructure tubeModel NormalBundleTube :=
  jacobianPoisson unitScaledTubeVolumeForm unitScaledTubeVolumeForm_ne_zero cylinderAreaForm
    singularCircleCasimirMap contMDiff_singularCircleCasimirMap

/-- Directional derivative `∂_{x_i} g (q)` along the `i`-th fiber basis vector of `S¹ × B³`. -/
def fiberPartial (g : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯) (i : Fin 3) (q : NormalBundleTube) :
    ℝ :=
  mvfderiv tubeModel g q (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ i))

/-- Explicit coordinate formula for `singularCircleUnitPoisson` (`k ≡ 1`):
`{g, h}_{π_1} = x₁ (∂_{x₂} g ∂_{x₃} h - ∂_{x₃} g ∂_{x₂} h)
  + x₂ (∂_{x₁} g ∂_{x₃} h - ∂_{x₃} g ∂_{x₁} h)
  - x₃ (∂_{x₁} g ∂_{x₂} h - ∂_{x₂} g ∂_{x₁} h)`. -/
theorem singularCircleUnitPoisson_bracket_apply
    (g h : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯) (q : NormalBundleTube) :
    (singularCircleUnitPoisson.bracket g h) q =
      q.2.1 0 * (fiberPartial g 1 q * fiberPartial h 2 q -
          fiberPartial g 2 q * fiberPartial h 1 q) +
        q.2.1 1 * (fiberPartial g 0 q * fiberPartial h 2 q -
          fiberPartial g 2 q * fiberPartial h 0 q) -
        q.2.1 2 * (fiberPartial g 0 q * fiberPartial h 1 q -
          fiberPartial g 1 q * fiberPartial h 0 q) := by
  let e := tubeTangentFrame q
  have htop := DFunLike.congr_fun (congrFun (congrArg Subtype.val
    (funSMulₗ_bracket_jacobianPoisson unitScaledTubeVolumeForm unitScaledTubeVolumeForm_ne_zero
      cylinderAreaForm singularCircleCasimirMap contMDiff_singularCircleCasimirMap g h)) q) e
  simp only [SmoothForm.coe_funSMulₗ, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    e, unitScaledTubeVolumeForm_apply_frame] at htop
  have hassoc := SmoothForm.wedge_assoc_apply (SmoothBivector.diffOneForm g)
    (SmoothBivector.diffOneForm h)
    (SmoothForm.mpullback singularCircleCasimirMap contMDiff_singularCircleCasimirMap
      cylinderAreaForm) q e
  have hce : (e ∘ Fin.cast (Nat.add_assoc 1 1 2).symm) = e := funext fun _ ↦ rfl
  rw [hce] at hassoc
  have he4 : e = ![e 0, e 1, e 2, e 3] := by funext j; fin_cases j <;> rfl
  rw [hassoc, he4, SmoothForm.coe_wedge, RoughForm.wedge_def, RoughForm.wedgeWith_apply',
    pairedWedge_one_three_apply] at htop
  simp only [SmoothForm.coe_wedge, RoughForm.wedge_def, RoughForm.wedgeWith_apply',
    pairedWedge_one_two_apply, SmoothBivector.diffOneForm_apply] at htop
  have hpul_theta (i : Fin 3) :
      (SmoothForm.mpullback singularCircleCasimirMap contMDiff_singularCircleCasimirMap
        cylinderAreaForm).1 q
        ![tubeTangentTheta q, tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ i)] =
        mvfderiv tubeModel casimirQuad q
          (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ i)) := by
    rw [SmoothForm.mpullback_apply]
    have hpair : (fun j : Fin 2 ↦
        mfderiv tubeModel cylinderModel singularCircleCasimirMap q
          (![tubeTangentTheta q, tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ i)] j)) =
        ![mfderiv tubeModel cylinderModel singularCircleCasimirMap q (tubeTangentTheta q),
          mfderiv tubeModel cylinderModel singularCircleCasimirMap q
            (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ i))] := by
      funext j; fin_cases j <;> rfl
    rw [hpair, cylinderAreaForm_pair, mfderiv_singularCircleCasimirMap_apply,
      mfderiv_singularCircleCasimirMap_apply, mvfderiv_casimirQuad_tubeTangentTheta,
      tubeTangentEquiv_theta, tubeTangentEquiv_fiber]
    ring
  have hpul_fib (i j : Fin 3) :
      (SmoothForm.mpullback singularCircleCasimirMap contMDiff_singularCircleCasimirMap
        cylinderAreaForm).1 q
        ![tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ i),
          tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ j)] = 0 := by
    rw [SmoothForm.mpullback_apply]
    have hpair : (fun l : Fin 2 ↦
        mfderiv tubeModel cylinderModel singularCircleCasimirMap q
          (![tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ i),
            tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ j)] l)) =
        ![mfderiv tubeModel cylinderModel singularCircleCasimirMap q
            (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ i)),
          mfderiv tubeModel cylinderModel singularCircleCasimirMap q
            (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ j))] := by
      funext l; fin_cases l <;> rfl
    rw [hpair, cylinderAreaForm_pair, mfderiv_singularCircleCasimirMap_apply,
      mfderiv_singularCircleCasimirMap_apply, tubeTangentEquiv_fiber, tubeTangentEquiv_fiber]
    ring
  dsimp only [e, tubeTangentFrame, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three] at htop
  have hhead : Matrix.vecHead (Matrix.vecTail
      ![tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 0),
        tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 1),
        tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 2)]) =
      tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 1) := rfl
  have hlast : Matrix.vecHead (Matrix.vecTail (Matrix.vecTail
      ![tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 0),
        tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 1),
        tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 2)])) =
      tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 2) := rfl
  simp only [hhead, hlast] at htop
  rw [hpul_fib 0 1, hpul_fib 0 2, hpul_fib 1 2,
    hpul_theta 0, hpul_theta 1, hpul_theta 2,
    mvfderiv_casimirQuad_tubeTangentFiber, mvfderiv_casimirQuad_tubeTangentFiber,
    mvfderiv_casimirQuad_tubeTangentFiber] at htop
  simp only [basisFun_fin3_apply, ↓reduceIte, Fin.isValue,
    show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at htop
  dsimp only [singularCircleUnitPoisson, fiberPartial] at htop ⊢
  linarith

/-- Smooth bivector of Equation (3) on `S¹ × B³` for any smooth factor `k ∈ C^∞(S¹ × B³)`. -/
def singularCircleBivector (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯) :
    SmoothBivector tubeModel NormalBundleTube :=
  singularCircleUnitPoisson.toSmoothBivector.smulFunction k

/-- **Equation (3) (`GSV15`, Eq. 3.4)**: For **every** smooth function `k ∈ C^∞(S¹ × B³)` (even
with zeros), `π_k = k(θ, x₁, x₂, x₃)(x₁ ∂_{x₂}∧∂_{x₃} + x₂ ∂_{x₁}∧∂_{x₃} - x₃ ∂_{x₁}∧∂_{x₂})`
satisfies the Jacobi identity on all of `S¹ × B³`. -/
def singularCirclePoisson (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯) :
    PoissonStructure tubeModel NormalBundleTube where
  toSmoothBivector := singularCircleBivector k
  jacobi f g h := by
    let U := singularCircleUnitPoisson
    change (U.toSmoothBivector.smulFunction k).bracket f
        ((U.toSmoothBivector.smulFunction k).bracket g h) +
      (U.toSmoothBivector.smulFunction k).bracket g
        ((U.toSmoothBivector.smulFunction k).bracket h f) +
      (U.toSmoothBivector.smulFunction k).bracket h
        ((U.toSmoothBivector.smulFunction k).bracket f g) = 0
    simp only [SmoothBivector.smulFunction_bracket, U.bracket_mul_right]
    have hj := U.jacobi f g h
    ext q
    have hjq := congrArg (fun u : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯ ↦ u q) hj
    simp only [ContMDiffMap.coe_add, ContMDiffMap.coe_zero, Pi.add_apply, Pi.zero_apply] at hjq
    simp only [ContMDiffMap.coe_add, ContMDiffMap.coe_mul, ContMDiffMap.coe_zero,
      Pi.add_apply, Pi.mul_apply, Pi.zero_apply]
    have hwedge :
        (U.bracket f k) q * (U.bracket g h) q +
          (U.bracket g k) q * (U.bracket h f) q +
          (U.bracket h k) q * (U.bracket f g) q = 0 := by
      dsimp only [U]
      rw [singularCircleUnitPoisson_bracket_apply f k q,
        singularCircleUnitPoisson_bracket_apply g h q,
        singularCircleUnitPoisson_bracket_apply g k q,
        singularCircleUnitPoisson_bracket_apply h f q,
        singularCircleUnitPoisson_bracket_apply h k q,
        singularCircleUnitPoisson_bracket_apply f g q]
      ring
    calc
      k q * (k q * (U.bracket f (U.bracket g h)) q + (U.bracket g h) q * (U.bracket f k) q) +
          k q * (k q * (U.bracket g (U.bracket h f)) q + (U.bracket h f) q * (U.bracket g k) q) +
          k q * (k q * (U.bracket h (U.bracket f g)) q + (U.bracket f g) q * (U.bracket h k) q)
        = k q * k q *
            ((U.bracket f (U.bracket g h)) q +
              (U.bracket g (U.bracket h f)) q +
              (U.bracket h (U.bracket f g)) q) +
          k q *
            ((U.bracket f k) q * (U.bracket g h) q +
              (U.bracket g k) q * (U.bracket h f) q +
              (U.bracket h k) q * (U.bracket f g) q) := by
          ring
      _ = 0 := by rw [hjq, hwedge]; ring

/-- Explicit bracket formula for `singularCirclePoisson k` (Equation (3)). -/
theorem singularCirclePoisson_bracket_apply (k g h : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯)
    (q : NormalBundleTube) :
    ((singularCirclePoisson k).bracket g h) q =
      k q *
        (q.2.1 0 * (fiberPartial g 1 q * fiberPartial h 2 q -
            fiberPartial g 2 q * fiberPartial h 1 q) +
          q.2.1 1 * (fiberPartial g 0 q * fiberPartial h 2 q -
            fiberPartial g 2 q * fiberPartial h 0 q) -
          q.2.1 2 * (fiberPartial g 0 q * fiberPartial h 1 q -
            fiberPartial g 1 q * fiberPartial h 0 q)) := by
  change ((singularCircleUnitPoisson.toSmoothBivector.smulFunction k).bracket g h) q = _
  rw [SmoothBivector.smulFunction_bracket, ContMDiffMap.coe_mul, Pi.mul_apply,
    singularCircleUnitPoisson_bracket_apply]

@[simp]
theorem fiberPartial_tubeCoord (i j : Fin 3) (q : NormalBundleTube) :
    fiberPartial (tubeCoord i) j q = if j = i then 1 else 0 := by
  rw [fiberPartial, mvfderiv_tubeCoord_tubeTangentFiber, basisFun_fin3_apply]
  simp [eq_comm]

/-- Coordinate bracket `{x₁, x₂}_{π_k} = -k x₃`
(`{tubeCoord 0, tubeCoord 1} = -k * tubeCoord 2`). -/
theorem singularCirclePoisson_bracket_coord_zero_one
    (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯) (q : NormalBundleTube) :
    ((singularCirclePoisson k).bracket (tubeCoord 0) (tubeCoord 1)) q = -k q * q.2.1 2 := by
  rw [singularCirclePoisson_bracket_apply]
  simp only [fiberPartial_tubeCoord]
  norm_num

/-- Coordinate bracket `{x₁, x₃}_{π_k} = k x₂` (`{tubeCoord 0, tubeCoord 2} = k * tubeCoord 1`). -/
theorem singularCirclePoisson_bracket_coord_zero_two
    (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯) (q : NormalBundleTube) :
    ((singularCirclePoisson k).bracket (tubeCoord 0) (tubeCoord 2)) q = k q * q.2.1 1 := by
  rw [singularCirclePoisson_bracket_apply]
  simp only [fiberPartial_tubeCoord]
  norm_num

/-- Coordinate bracket `{x₂, x₃}_{π_k} = k x₁` (`{tubeCoord 1, tubeCoord 2} = k * tubeCoord 0`). -/
theorem singularCirclePoisson_bracket_coord_one_two
    (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯) (q : NormalBundleTube) :
    ((singularCirclePoisson k).bracket (tubeCoord 1) (tubeCoord 2)) q = k q * q.2.1 0 := by
  rw [singularCirclePoisson_bracket_apply]
  simp only [fiberPartial_tubeCoord]
  norm_num

/-- Smooth functions of the angular coordinate `θ ∈ S¹` are Casimirs of
`singularCirclePoisson k`. -/
theorem isCasimir_angular_singularCirclePoisson (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯)
    (u : C^∞⟮𝓘(ℝ), CircleS1; ℝ⟯) :
    (singularCirclePoisson k).IsCasimir (u.comp ⟨Prod.fst, contMDiff_fst⟩) := by
  intro h
  have hunit : singularCircleUnitPoisson.IsCasimir
      ((u.comp ⟨Prod.fst, contMDiff_fst⟩ : C^∞⟮cylinderModel, CircleS1 × ℝ; ℝ⟯).comp
        ⟨singularCircleCasimirMap, contMDiff_singularCircleCasimirMap⟩) :=
    isCasimir_comp_jacobianPoisson unitScaledTubeVolumeForm unitScaledTubeVolumeForm_ne_zero
      cylinderAreaForm singularCircleCasimirMap contMDiff_singularCircleCasimirMap
      (u.comp ⟨Prod.fst, contMDiff_fst⟩)
  have heq : ((u.comp ⟨Prod.fst, contMDiff_fst⟩ : C^∞⟮cylinderModel, CircleS1 × ℝ; ℝ⟯).comp
      ⟨singularCircleCasimirMap, contMDiff_singularCircleCasimirMap⟩) =
      u.comp ⟨Prod.fst, contMDiff_fst⟩ := by
    ext q; rfl
  rw [heq] at hunit
  change (singularCircleUnitPoisson.toSmoothBivector.smulFunction k).bracket
    (u.comp ⟨Prod.fst, contMDiff_fst⟩) h = 0
  rw [SmoothBivector.smulFunction_bracket, hunit h, mul_zero]

/-- The indefinite quadratic cone `casimirQuad(θ, x) = -x₁² + x₂² + x₃²` is a Casimir function of
`singularCirclePoisson k` for every smooth `k`. -/
theorem isCasimir_casimirQuad_singularCirclePoisson (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯) :
    (singularCirclePoisson k).IsCasimir casimirQuad := by
  intro h
  let sndMap : C^∞⟮cylinderModel, CircleS1 × ℝ; ℝ⟯ := ⟨Prod.snd, contMDiff_snd⟩
  have hunit : singularCircleUnitPoisson.IsCasimir
      (sndMap.comp ⟨singularCircleCasimirMap, contMDiff_singularCircleCasimirMap⟩) :=
    isCasimir_comp_jacobianPoisson unitScaledTubeVolumeForm unitScaledTubeVolumeForm_ne_zero
      cylinderAreaForm singularCircleCasimirMap contMDiff_singularCircleCasimirMap sndMap
  have heq : sndMap.comp ⟨singularCircleCasimirMap, contMDiff_singularCircleCasimirMap⟩ =
      casimirQuad := by
    ext q; rfl
  rw [heq] at hunit
  change (singularCircleUnitPoisson.toSmoothBivector.smulFunction k).bracket casimirQuad h = 0
  rw [SmoothBivector.smulFunction_bracket, hunit h, mul_zero]

/-- Singular circle `S¹ × {0} ⊂ S¹ × B³` where the rank of `π_k` drops to `0`. -/
def singularCircleLocus : Set NormalBundleTube :=
  {q : NormalBundleTube | (q.2 : EuclideanSpace ℝ (Fin 3)) = 0}

@[simp]
theorem mem_singularCircleLocus_iff (q : NormalBundleTube) :
    q ∈ singularCircleLocus ↔ (q.2 : EuclideanSpace ℝ (Fin 3)) = 0 :=
  Iff.rfl

/-- Explicit anchor action of `singularCirclePoisson k` in terms of `tubeTangentFiber`. -/
theorem singularCirclePoisson_anchor_apply (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯)
    (q : NormalBundleTube) (α : TangentSpace tubeModel q →L[ℝ] ℝ) :
    (singularCirclePoisson k).anchor q α =
      let αf := fun i : Fin 3 ↦ α (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ i))
      tubeTangentFiber q
        (k q • WithLp.toLp 2
          ![-q.2.1 1 * αf 2 + q.2.1 2 * αf 1,
            -q.2.1 0 * αf 2 - q.2.1 2 * αf 0,
             q.2.1 0 * αf 1 + q.2.1 1 * αf 0]) := by
  suffices hunit : singularCircleUnitPoisson.anchor q α =
      tubeTangentFiber q
        (WithLp.toLp 2
          ![-q.2.1 1 * α (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 2)) +
              q.2.1 2 * α (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 1)),
            -q.2.1 0 * α (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 2)) -
              q.2.1 2 * α (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 0)),
             q.2.1 0 * α (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 1)) +
              q.2.1 1 * α (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 0))]) by
    dsimp only
    change k q • singularCircleUnitPoisson.anchor q α = _
    rw [hunit, tubeTangentFiber_smul]
  let αf := fun i : Fin 3 ↦ α (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ i))
  let g : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯ :=
    αf 0 • tubeCoord 0 + αf 1 • tubeCoord 1 + αf 2 • tubeCoord 2
  have hfg (i : Fin 3) : fiberPartial g i q = αf i := by
    have hd (j : Fin 3) : MDifferentiableAt tubeModel 𝓘(ℝ) (tubeCoord j) q :=
      (tubeCoord j).contMDiff.mdifferentiableAt (by simp)
    have hs (j : Fin 3) : MDifferentiableAt tubeModel 𝓘(ℝ) (αf j • tubeCoord j) q :=
      (αf j • tubeCoord j).contMDiff.mdifferentiableAt (by simp)
    have hcoe : ⇑g = (⇑(αf 0 • tubeCoord 0) + ⇑(αf 1 • tubeCoord 1)) + ⇑(αf 2 • tubeCoord 2) := rfl
    dsimp only [fiberPartial]
    rw [hcoe, mvfderiv_add ((hs 0).add (hs 1)) (hs 2), add_apply,
      mvfderiv_add (hs 0) (hs 1), add_apply]
    have hm (j : Fin 3) :
        mvfderiv tubeModel (αf j • tubeCoord j) q
          (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ i)) =
          αf j * (EuclideanSpace.basisFun (Fin 3) ℝ i) j := by
      rw [ContMDiffMap.coe_smul, Pi.smul_def, mvfderiv_const_smul (hd j), smul_apply,
        smul_eq_mul, mvfderiv_tubeCoord_tubeTangentFiber]
    rw [hm 0, hm 1, hm 2]
    fin_cases i <;> simp
  have hu_theta (β : TangentSpace tubeModel q →L[ℝ] ℝ) :
      (tubeTangentEquiv q (singularCircleUnitPoisson.anchor q β)).1 = 0 := by
    have hm := mfderiv_singularCircleCasimirMap_apply q (singularCircleUnitPoisson.anchor q β)
    have hker : mfderiv tubeModel cylinderModel singularCircleCasimirMap q
        (singularCircleUnitPoisson.anchor q β) = 0 :=
      mfderiv_jacobianAnchor_eq_zero unitScaledTubeVolumeForm unitScaledTubeVolumeForm_ne_zero
        cylinderAreaForm singularCircleCasimirMap contMDiff_singularCircleCasimirMap q β
    rw [hker, map_zero] at hm
    exact (congrArg Prod.fst hm).symm
  have hα_split (v : TangentSpace tubeModel q) :
      (tubeTangentEquiv q v).1 = 0 → α v = mvfderiv tubeModel g q v := by
    intro hv1
    let vx := (tubeTangentEquiv q v).2
    have hv_eq : v =
        ∑ i : Fin 3, vx i • tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
      apply (tubeTangentEquiv q).injective
      ext j
      · rw [hv1, map_sum, Prod.fst_sum]
        simp
      · rw [map_sum, Prod.snd_sum]
        fin_cases j <;> simp [vx, Fin.sum_univ_three]
    rw [hv_eq, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    change vx i * αf i = vx i * fiberPartial g i q
    rw [hfg i]
  have hanch_eq : singularCircleUnitPoisson.anchor q α =
      singularCircleUnitPoisson.anchor q (mvfderiv tubeModel g q) := by
    apply (tubeTangentEquiv q).injective
    ext j
    · exact (hu_theta α).trans (hu_theta (mvfderiv tubeModel g q)).symm
    · let βj := mvfderiv tubeModel (tubeCoord j) q
      have hβj (w : TangentSpace tubeModel q) :
          (tubeTangentEquiv q w).1 = 0 → βj w = (tubeTangentEquiv q w).2 j := by
        intro hw1
        have hw := tubeTangent_decomp q w
        rw [hw1, zero_smul, zero_add] at hw
        conv_lhs => rw [hw]
        exact mvfderiv_tubeCoord_tubeTangentFiber j q _
      rw [← hβj _ (hu_theta α), ← hβj _ (hu_theta (mvfderiv tubeModel g q)),
        singularCircleUnitPoisson.anchor_skew q α βj,
        singularCircleUnitPoisson.anchor_skew q (mvfderiv tubeModel g q) βj,
        hα_split _ (hu_theta βj)]
  rw [hanch_eq]
  apply (tubeTangentEquiv q).injective
  ext j
  · rw [hu_theta (mvfderiv tubeModel g q), tubeTangentEquiv_fiber]
  · have hθg := hu_theta (mvfderiv tubeModel g q)
    have hw := tubeTangent_decomp q (singularCircleUnitPoisson.anchor q (mvfderiv tubeModel g q))
    rw [hθg, zero_smul, zero_add] at hw
    have heval : (singularCircleUnitPoisson.bracket g (tubeCoord j)) q =
        (tubeTangentEquiv q (singularCircleUnitPoisson.anchor q (mvfderiv tubeModel g q))).2 j := by
      rw [SmoothBivector.bracket_apply, SmoothBivector.bivector_apply]
      conv_lhs => rw [hw]
      exact mvfderiv_tubeCoord_tubeTangentFiber j q _
    rw [← heval, singularCircleUnitPoisson_bracket_apply g (tubeCoord j) q,
      hfg 0, hfg 1, hfg 2, tubeTangentEquiv_fiber]
    fin_cases j
    · dsimp only [αf]
      simp only [fiberPartial_tubeCoord]
      norm_num
    · dsimp only [αf]
      simp only [fiberPartial_tubeCoord]
      norm_num
    · dsimp only [αf]
      simp only [fiberPartial_tubeCoord]
      norm_num

/-- Explicit Hamiltonian vector field formula for `singularCirclePoisson k`. -/
theorem singularCirclePoisson_hamiltonianVectorField_apply
    (k h : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯) (q : NormalBundleTube) :
    (singularCirclePoisson k).hamiltonianVectorField h q =
      tubeTangentFiber q
        (k q • WithLp.toLp 2
          ![q.2.1 1 * fiberPartial h 2 q - q.2.1 2 * fiberPartial h 1 q,
            q.2.1 0 * fiberPartial h 2 q + q.2.1 2 * fiberPartial h 0 q,
            -q.2.1 0 * fiberPartial h 1 q - q.2.1 1 * fiberPartial h 0 q]) := by
  rw [SmoothBivector.hamiltonianVectorField, singularCirclePoisson_anchor_apply]
  dsimp only
  rw [tubeTangentFiber_neg]
  congr 1
  ext j
  fin_cases j
  · dsimp only
    simp only [PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
    change -(k q * (-q.2.1 1 * fiberPartial h 2 q + q.2.1 2 * fiberPartial h 1 q)) =
      k q * (q.2.1 1 * fiberPartial h 2 q - q.2.1 2 * fiberPartial h 1 q)
    ring
  · dsimp only
    simp only [PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
    change -(k q * (-q.2.1 0 * fiberPartial h 2 q - q.2.1 2 * fiberPartial h 0 q)) =
      k q * (q.2.1 0 * fiberPartial h 2 q + q.2.1 2 * fiberPartial h 0 q)
    ring
  · dsimp only
    simp only [PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
    change -(k q * (q.2.1 0 * fiberPartial h 1 q + q.2.1 1 * fiberPartial h 0 q)) =
      k q * (-q.2.1 0 * fiberPartial h 1 q - q.2.1 1 * fiberPartial h 0 q)
    ring

/-- Along `singularCircleLocus = S¹ × {0}`, the anchor of `singularCirclePoisson k` vanishes. -/
theorem anchor_eq_zero_of_mem_singularCircleLocus (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯)
    {q : NormalBundleTube} (hq : q ∈ singularCircleLocus) :
    (singularCirclePoisson k).anchor q = 0 := by
  ext α
  rw [singularCirclePoisson_anchor_apply]
  have hx0 : q.2.1 0 = 0 := by
    simpa [hq] using congrArg (fun x : EuclideanSpace ℝ (Fin 3) ↦ x 0) hq
  have hx1 : q.2.1 1 = 0 := by
    simpa [hq] using congrArg (fun x : EuclideanSpace ℝ (Fin 3) ↦ x 1) hq
  have hx2 : q.2.1 2 = 0 := by
    simpa [hq] using congrArg (fun x : EuclideanSpace ℝ (Fin 3) ↦ x 2) hq
  dsimp only
  have hz : (k q • WithLp.toLp 2
      ![-q.2.1 1 * α (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 2)) +
          q.2.1 2 * α (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 1)),
        -q.2.1 0 * α (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 2)) -
          q.2.1 2 * α (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 0)),
         q.2.1 0 * α (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 1)) +
          q.2.1 1 * α (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 0))]) = 0 := by
    ext j
    fin_cases j <;> simp [hx0, hx1, hx2]
  change tubeTangentFiber q _ = 0
  rw [hz, tubeTangentFiber_zero]

theorem rankAt_eq_zero_of_mem_singularCircleLocus (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯)
    {q : NormalBundleTube} (hq : q ∈ singularCircleLocus) :
    (singularCirclePoisson k).rankAt q = 0 := by
  simp [SmoothBivector.rankAt, anchor_eq_zero_of_mem_singularCircleLocus k hq]

/-- The critical set of `F(θ, x) = (θ, -x₁² + x₂² + x₃²)` is `singularCircleLocus = S¹ × {0}`. -/
theorem criticalSet_singularCircleCasimirMap :
    criticalSet tubeModel cylinderModel singularCircleCasimirMap = singularCircleLocus := by
  ext q
  rw [mem_criticalSet_iff, mem_singularCircleLocus_iff]
  constructor
  · intro hnot
    by_contra hx
    apply hnot
    intro w
    have hex : ∃ i : Fin 3, q.2.1 i ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hx
      ext i
      simpa using hall i
    obtain ⟨i, hi⟩ := hex
    let ei := EuclideanSpace.basisFun (Fin 3) ℝ i
    have hdi : mvfderiv tubeModel casimirQuad q (tubeTangentFiber q ei) ≠ 0 := by
      rw [mvfderiv_casimirQuad_tubeTangentFiber]
      fin_cases i <;>
        · dsimp only at hi
          dsimp only [ei]
          rw [basisFun_fin3_apply, basisFun_fin3_apply, basisFun_fin3_apply]
          intro h0
          norm_num at h0
          exact hi h0
    let w' := cylinderTangentEquiv (singularCircleCasimirMap q) w
    let v : TangentSpace tubeModel q :=
      w'.1 • tubeTangentTheta q +
        (w'.2 / mvfderiv tubeModel casimirQuad q (tubeTangentFiber q ei)) • tubeTangentFiber q ei
    refine ⟨v, ?_⟩
    apply (cylinderTangentEquiv (singularCircleCasimirMap q)).injective
    rw [mfderiv_singularCircleCasimirMap_apply]
    dsimp only [v]
    rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul,
      tubeTangentEquiv_theta, tubeTangentEquiv_fiber, mvfderiv_casimirQuad_tubeTangentTheta]
    ext
    · simp [w']
    · simp only [smul_eq_mul, mul_zero, zero_add]
      exact div_mul_cancel₀ w'.2 hdi
  · intro hx hsurj
    obtain ⟨v, hv⟩ := hsurj ((cylinderTangentEquiv (singularCircleCasimirMap q)).symm (0, 1))
    have hm := mfderiv_singularCircleCasimirMap_apply q v
    rw [hv, ContinuousLinearEquiv.apply_symm_apply] at hm
    have hcas : mvfderiv tubeModel casimirQuad q v = 1 := (congrArg Prod.snd hm).symm
    have hv_eq := tubeTangent_decomp q v
    rw [hv_eq, map_add, map_smul, mvfderiv_casimirQuad_tubeTangentTheta, smul_zero, zero_add,
      mvfderiv_casimirQuad_tubeTangentFiber] at hcas
    have hx0 : q.2.1 0 = 0 := by simp [hx]
    have hx1 : q.2.1 1 = 0 := by simp [hx]
    have hx2 : q.2.1 2 = 0 := by simp [hx]
    rw [hx0, hx1, hx2] at hcas
    norm_num at hcas

/-! ### Jacobian–Poisson Origin and Unimodularity for Nowhere-Vanishing `k` -/

/-- Nowhere-vanishing volume `4`-form `(-2 / k) dθ ∧ dx₁ ∧ dx₂ ∧ dx₃` realizing `π_k` directly as
the Jacobian–Poisson structure of `(θ, -x₁² + x₂² + x₃²)`. -/
def scaledTubeVolumeForm (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯) (hk : ∀ q, k q ≠ 0) :
    SmoothForm tubeModel NormalBundleTube ℝ 4 :=
  SmoothForm.funSMulₗ ⟨fun q ↦ -2 / k q, contMDiff_const.div₀ k.contMDiff hk⟩ tubeVolumeForm

@[simp]
theorem scaledTubeVolumeForm_apply (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯)
    (hk : ∀ q, k q ≠ 0) (q : NormalBundleTube) (v : Fin 4 → TangentSpace tubeModel q) :
    (scaledTubeVolumeForm k hk).1 q v = (-2 / k q) * tubeVolumeForm.1 q v := by
  let f : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯ :=
    ⟨fun p ↦ -2 / k p, contMDiff_const.div₀ k.contMDiff hk⟩
  have h := DFunLike.congr_fun (congrFun (SmoothForm.coe_funSMulₗ f tubeVolumeForm) q) v
  rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h
  exact h

theorem scaledTubeVolumeForm_ne_zero (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯)
    (hk : ∀ q, k q ≠ 0) (q : NormalBundleTube) :
    (scaledTubeVolumeForm k hk).1 q ≠ 0 :=
  funSMulₗ_ne_zero tubeVolumeForm_ne_zero (fun p ↦ div_ne_zero (by norm_num) (hk p)) q

/-- Invariant volume `4`-form `(1 / k) dθ ∧ dx₁ ∧ dx₂ ∧ dx₃` (`#9` & `S4TCdiffeo-Aug-2026.tex`). -/
def invKTubeVolumeForm (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯) (hk : ∀ q, k q ≠ 0) :
    SmoothForm tubeModel NormalBundleTube ℝ 4 :=
  SmoothForm.funSMulₗ ⟨fun q ↦ (k q)⁻¹, k.contMDiff.inv₀ hk⟩ tubeVolumeForm

@[simp]
theorem invKTubeVolumeForm_apply (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯)
    (hk : ∀ q, k q ≠ 0) (q : NormalBundleTube) (v : Fin 4 → TangentSpace tubeModel q) :
    (invKTubeVolumeForm k hk).1 q v = (k q)⁻¹ * tubeVolumeForm.1 q v := by
  let f : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯ := ⟨fun p ↦ (k p)⁻¹, k.contMDiff.inv₀ hk⟩
  have h := DFunLike.congr_fun (congrFun (SmoothForm.coe_funSMulₗ f tubeVolumeForm) q) v
  rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h
  exact h

theorem invKTubeVolumeForm_ne_zero (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯)
    (hk : ∀ q, k q ≠ 0) (q : NormalBundleTube) :
    (invKTubeVolumeForm k hk).1 q ≠ 0 :=
  funSMulₗ_ne_zero tubeVolumeForm_ne_zero (fun p ↦ inv_ne_zero (hk p)) q

/-- Whenever `k` is nowhere-vanishing on `S¹ × B³`, `singularCirclePoisson k` is **identical** to
the Jacobian–Poisson structure of `F(θ, x) = (θ, -x₁² + x₂² + x₃²)` with volume
`(-2 / k) dθ ∧ dx₁ ∧ dx₂ ∧ dx₃` and cylinder area form `dθ ∧ dt`. -/
theorem singularCirclePoisson_eq_jacobianPoisson (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯)
    (hk : ∀ q, k q ≠ 0) :
    singularCirclePoisson k =
      jacobianPoisson (scaledTubeVolumeForm k hk) (scaledTubeVolumeForm_ne_zero k hk)
        cylinderAreaForm singularCircleCasimirMap contMDiff_singularCircleCasimirMap := by
  apply PoissonStructure.ext
  apply SmoothBivector.ext
  intro q α
  let b : Module.Basis (Fin 4) ℝ (TangentSpace tubeModel q) :=
    (trivializationAt (ℝ × EuclideanSpace ℝ (Fin 3)) (TangentSpace tubeModel) q).basisAt
      (Module.finBasisOfFinrankEq ℝ (ℝ × EuclideanSpace ℝ (Fin 3)) HasFinrank.finrank_eq)
      (FiberBundle.mem_baseSet_trivializationAt' q)
  change k q • singularCircleUnitPoisson.anchor q α =
    jacobianAnchor (scaledTubeVolumeForm k hk) cylinderAreaForm singularCircleCasimirMap
      contMDiff_singularCircleCasimirMap q α
  rw [jacobianAnchor_eq_subTopDualVector]
  refine eq_subTopDualVector_of_forall_vecCons b (scaledTubeVolumeForm_ne_zero k hk q) _ fun w ↦ ?_
  rw [scaledTubeVolumeForm_apply, map_vecCons_smul_slot0, smul_eq_mul]
  have hunit := apply_vecCons_jacobianAnchor unitScaledTubeVolumeForm
    unitScaledTubeVolumeForm_ne_zero cylinderAreaForm singularCircleCasimirMap
    contMDiff_singularCircleCasimirMap q α w
  rw [unitScaledTubeVolumeForm_apply] at hunit
  dsimp only [singularCircleUnitPoisson, jacobianPoisson, jacobianSmoothBivector]
  have hkq : (-2 / k q) * (k q * (tubeVolumeForm.1 q)
      (Matrix.vecCons
        (jacobianAnchor unitScaledTubeVolumeForm cylinderAreaForm singularCircleCasimirMap
          contMDiff_singularCircleCasimirMap q α) w)) =
      (-2 : ℝ) * (tubeVolumeForm.1 q)
        (Matrix.vecCons
          (jacobianAnchor unitScaledTubeVolumeForm cylinderAreaForm singularCircleCasimirMap
            contMDiff_singularCircleCasimirMap q α) w) := by
    field_simp [hk q]
  rw [hkq, hunit, ContinuousAlternatingMap.neg_apply]

/-- Exact Jacobian–Poisson wedge identity with the `-2 / k` factor (`#9`):
`{g, h}_{π_k} • ((-2 / k) dθ ∧ dx₁ ∧ dx₂ ∧ dx₃) = dg ∧ dh ∧ F^*(dθ ∧ dt)`. -/
theorem funSMulₗ_bracket_singularCirclePoisson (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯)
    (hk : ∀ q, k q ≠ 0) (g h : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯) :
    SmoothForm.funSMulₗ ((singularCirclePoisson k).bracket g h) (scaledTubeVolumeForm k hk) =
      SmoothForm.wedge (SmoothForm.wedge (SmoothBivector.diffOneForm g)
        (SmoothBivector.diffOneForm h))
        (SmoothForm.mpullback singularCircleCasimirMap contMDiff_singularCircleCasimirMap
          cylinderAreaForm) := by
  rw [singularCirclePoisson_eq_jacobianPoisson k hk]
  exact funSMulₗ_bracket_jacobianPoisson (scaledTubeVolumeForm k hk)
    (scaledTubeVolumeForm_ne_zero k hk) cylinderAreaForm singularCircleCasimirMap
    contMDiff_singularCircleCasimirMap g h

/-- `singularCirclePoisson k` is globally unimodular with volume `(-2 / k) dθ ∧ dx₁ ∧ dx₂ ∧ dx₃`. -/
theorem isUnimodularWithVolume_scaledTubeVolumeForm (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯)
    (hk : ∀ q, k q ≠ 0) :
    (singularCirclePoisson k).IsUnimodularWithVolume (scaledTubeVolumeForm k hk) := by
  rw [singularCirclePoisson_eq_jacobianPoisson k hk]
  exact isUnimodularWithVolume_jacobianPoisson (scaledTubeVolumeForm k hk)
    (scaledTubeVolumeForm_ne_zero k hk) cylinderAreaForm singularCircleCasimirMap
    contMDiff_singularCircleCasimirMap

/-- `singularCirclePoisson k` is globally unimodular with volume `(1 / k) dθ ∧ dx₁ ∧ dx₂ ∧ dx₃`. -/
theorem isUnimodularWithVolume_invKTubeVolumeForm (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯)
    (hk : ∀ q, k q ≠ 0) :
    (singularCirclePoisson k).IsUnimodularWithVolume (invKTubeVolumeForm k hk) := by
  have hrel : invKTubeVolumeForm k hk = (-2⁻¹ : ℝ) • scaledTubeVolumeForm k hk := by
    apply Subtype.ext
    funext q
    ext v
    rw [SmoothForm.smul_toRoughForm, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, invKTubeVolumeForm_apply, scaledTubeVolumeForm_apply]
    field_simp [hk q]
  refine ⟨invKTubeVolumeForm_ne_zero k hk, fun h ↦ ?_⟩
  rw [hrel]
  have hzero := (isUnimodularWithVolume_scaledTubeVolumeForm k hk).2 h
  apply Subtype.ext
  rw [PoissonStructure.coe_lieDerivVolume,
    (singularCirclePoisson k).lieDerivVolume_eq_mextDeriv_interior (m := 3) _
      HasFinrank.finrank_eq.le h,
    SmoothForm.smul_toRoughForm]
  have hsmul : RoughForm.interior ((singularCirclePoisson k).hamiltonianVectorField h)
      ((-2⁻¹ : ℝ) • (scaledTubeVolumeForm k hk).1) =
      (-2⁻¹ : ℝ) • RoughForm.interior ((singularCirclePoisson k).hamiltonianVectorField h)
        (scaledTubeVolumeForm k hk).1 := by
    funext q
    ext w
    rw [RoughForm.interior_apply, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
      Pi.smul_apply, ContinuousAlternatingMap.smul_apply, RoughForm.interior_apply]
  have hisSmooth : IsSmoothForm tubeModel ∞
      (RoughForm.interior ((singularCirclePoisson k).hamiltonianVectorField h)
        (scaledTubeVolumeForm k hk).1) :=
    (scaledTubeVolumeForm k hk).isSmoothForm.interior
      ((singularCirclePoisson k).contMDiff_hamiltonianVectorField h)
  have hd0 : mextDeriv (RoughForm.interior ((singularCirclePoisson k).hamiltonianVectorField h)
      (scaledTubeVolumeForm k hk).1) = 0 := by
    rw [← (singularCirclePoisson k).lieDerivVolume_eq_mextDeriv_interior (m := 3) _
      HasFinrank.finrank_eq.le h, ← PoissonStructure.coe_lieDerivVolume, hzero]
    rfl
  rw [hsmul, RoughForm.smul_eq_mapCoeff,
    mextDeriv_mapCoeff _ (hisSmooth.of_le (by simp)), hd0, RoughForm.mapCoeff_zero]
  rfl

/-- Whenever `k` is nowhere-vanishing on `S¹ × B³`, `singularCirclePoisson k` is unimodular. -/
theorem isUnimodularPoisson_singularCirclePoisson (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯)
    (hk : ∀ q, k q ≠ 0) :
    (singularCirclePoisson k).IsUnimodularPoisson :=
  (isUnimodularWithVolume_invKTubeVolumeForm k hk).isUnimodularPoisson

/-! ## 4. Equation (4) (`GSV15` Proposition 3.2): Free Smooth Poisson Involution -/

/-- Ambient orthogonal reflection `(x₁, x₂, x₃) ↦ (-x₁, -x₂, x₃)` on `ℝ³`. -/
def fiberInvolutionLI : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun x := WithLp.toLp 2 ![-x 0, -x 1, x 2]
  map_add' x y := by
    ext i
    fin_cases i
    · simp; ring
    · simp; ring
    · simp
  map_smul' c x := by
    ext i
    fin_cases i <;> simp
  invFun x := WithLp.toLp 2 ![-x 0, -x 1, x 2]
  left_inv x := by
    ext i
    fin_cases i <;> simp
  right_inv x := by
    ext i
    fin_cases i <;> simp
  norm_map' x := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp [Fin.sum_univ_three]

/-- Restriction of `(x₁, x₂, x₃) ↦ (-x₁, -x₂, x₃)` to the open unit ball `B³ = OpenBall3`. -/
def ballFiberInvolution (x : OpenBall3) : OpenBall3 :=
  ⟨fiberInvolutionLI x.1, by
    have hx : ‖x.1‖ < 1 := by simpa [OpenBall3, Metric.mem_ball, dist_zero_right] using x.2
    simpa [OpenBall3, Metric.mem_ball, dist_zero_right, fiberInvolutionLI.norm_map] using hx⟩

theorem contMDiff_ballFiberInvolution : ContMDiff (𝓡 3) (𝓡 3) ∞ ballFiberInvolution :=
  (TauCeti.ContMDiff.subtypeVal_comp_iff OpenBall3 ballFiberInvolution).mp
    (fiberInvolutionLI.contDiff.contMDiff.comp contMDiff_subtype_val)

/-- Antipodal half-turn `θ ↦ θ + π` on `S¹ = AddCircle (2π)`. -/
def circleHalfTurn (θ : CircleS1) : CircleS1 :=
  θ + (Real.pi : CircleS1)

theorem contMDiff_circleHalfTurn : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ circleHalfTurn :=
  contMDiff_id.add contMDiff_const

/-- **Equation (4) (`GSV15`, Proposition 3.2)**: Non-orientable normal-bundle involution
`i(θ, x₁, x₂, x₃) = (θ + π, -x₁, -x₂, x₃)` on `S¹ × B³`. -/
def normalInvolution (q : NormalBundleTube) : NormalBundleTube :=
  (circleHalfTurn q.1, ballFiberInvolution q.2)

theorem contMDiff_normalInvolution : ContMDiff tubeModel tubeModel ∞ normalInvolution :=
  contMDiff_circleHalfTurn.prodMap contMDiff_ballFiberInvolution

/-- `normalInvolution` is a strict involution: `normalInvolution (normalInvolution q) = q`. -/
theorem involutive_normalInvolution : Function.Involutive normalInvolution := by
  intro q
  ext
  · dsimp only [normalInvolution, circleHalfTurn]
    rw [add_assoc, ← QuotientAddGroup.mk_add]
    have h2pi : Real.pi + Real.pi = 2 * Real.pi := by ring
    rw [h2pi, AddCircle.coe_period, add_zero]
  · have h := fiberInvolutionLI.left_inv q.2.1
    exact congrArg (fun y : EuclideanSpace ℝ (Fin 3) ↦ y _) h

@[simp]
theorem normalInvolution_normalInvolution (q : NormalBundleTube) :
    normalInvolution (normalInvolution q) = q :=
  involutive_normalInvolution q

/-- Smooth diffeomorphism packaging `normalInvolution : S¹ × B³ ≃ₘ S¹ × B³`. -/
def normalInvolutionDiffeomorph : NormalBundleTube ≃ₘ⟮tubeModel, tubeModel⟯ NormalBundleTube where
  toFun := normalInvolution
  invFun := normalInvolution
  left_inv := involutive_normalInvolution
  right_inv := involutive_normalInvolution
  contMDiff_toFun := contMDiff_normalInvolution
  contMDiff_invFun := contMDiff_normalInvolution

/-- `normalInvolution` acts freely on `S¹ × B³` (has no fixed points). -/
theorem normalInvolution_ne_self (q : NormalBundleTube) : normalInvolution q ≠ q := by
  intro h
  have h1 : q.1 + (Real.pi : CircleS1) = q.1 := congrArg Prod.fst h
  have hpi0 : (Real.pi : CircleS1) = 0 := by
    simpa using congrArg (fun x : CircleS1 ↦ -q.1 + x) h1
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (2 * Real.pi)).mp hpi0
  rw [zsmul_eq_mul] at hn
  have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
  have hn2 : (n : ℝ) * 2 = 1 := by
    apply mul_right_cancel₀ hpi_ne
    linarith
  rcases le_or_gt n 0 with hle | hgt
  · have hleR : (n : ℝ) ≤ 0 := Int.cast_nonpos.mpr hle
    linarith
  · have hge1 : (1 : ℤ) ≤ n := hgt
    have hgeR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hge1
    linarith

@[simp]
theorem casimirQuad_normalInvolution (q : NormalBundleTube) :
    casimirQuad (normalInvolution q) = casimirQuad q := by
  simp [casimirQuad_apply, normalInvolution, ballFiberInvolution, fiberInvolutionLI]

@[simp]
theorem normalInvolution_mem_singularCircleLocus_iff (q : NormalBundleTube) :
    normalInvolution q ∈ singularCircleLocus ↔ q ∈ singularCircleLocus := by
  simp only [mem_singularCircleLocus_iff, normalInvolution, ballFiberInvolution]
  exact ⟨fun h ↦ fiberInvolutionLI.injective (h.trans (map_zero fiberInvolutionLI).symm),
    fun h ↦ by rw [h, map_zero]⟩

theorem tubeTangentTheta_eq_prodEquiv_symm (p : NormalBundleTube) :
    tubeTangentTheta p =
      (TauCeti.Manifold.tangentSpaceProdEquiv p).symm ((thetaTangentEquiv p.1).symm 1, 0) := by
  apply (TauCeti.Manifold.tangentSpaceProdEquiv p).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply ((thetaTangentEquiv p.1).prodCongr (fiberTangentEquiv p.2)).injective
  rw [← ContinuousLinearEquiv.trans_apply, ← tubeTangentEquiv, tubeTangentEquiv_theta,
    ContinuousLinearEquiv.prodCongr_apply]
  dsimp only
  rw [ContinuousLinearEquiv.apply_symm_apply, map_zero]

theorem tubeTangentFiber_eq_prodEquiv_symm (p : NormalBundleTube)
    (v : EuclideanSpace ℝ (Fin 3)) :
    tubeTangentFiber p v =
      (TauCeti.Manifold.tangentSpaceProdEquiv p).symm (0, (fiberTangentEquiv p.2).symm v) := by
  apply (TauCeti.Manifold.tangentSpaceProdEquiv p).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply ((thetaTangentEquiv p.1).prodCongr (fiberTangentEquiv p.2)).injective
  rw [← ContinuousLinearEquiv.trans_apply, ← tubeTangentEquiv, tubeTangentEquiv_fiber,
    ContinuousLinearEquiv.prodCongr_apply]
  dsimp only
  rw [map_zero, ContinuousLinearEquiv.apply_symm_apply]

theorem mfderiv_normalInvolution_tubeTangentTheta (q : NormalBundleTube) :
    mfderiv tubeModel tubeModel normalInvolution q (tubeTangentTheta q) =
      tubeTangentTheta (normalInvolution q) := by
  have h1 : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ) circleHalfTurn q.1 :=
    contMDiff_circleHalfTurn.mdifferentiableAt (by simp)
  have h2 : MDifferentiableAt (𝓡 3) (𝓡 3) ballFiberInvolution q.2 :=
    contMDiff_ballFiberInvolution.mdifferentiableAt (by simp)
  have heq : normalInvolution = Prod.map circleHalfTurn ballFiberInvolution := rfl
  have hturn : mfderiv 𝓘(ℝ) 𝓘(ℝ) circleHalfTurn q.1 ((thetaTangentEquiv q.1).symm 1) =
      (thetaTangentEquiv (circleHalfTurn q.1)).symm 1 := by
    have hc : circleHalfTurn = fun θ : CircleS1 ↦ θ + (Real.pi : CircleS1) := rfl
    rw [hc, AddCircle.mfderiv_add_right]
    rfl
  rw [tubeTangentTheta_eq_prodEquiv_symm q,
    tubeTangentTheta_eq_prodEquiv_symm (normalInvolution q),
    heq, TauCeti.Manifold.mfderiv_prodMap_apply h1 h2, map_zero, hturn]
  rfl

theorem mfderiv_normalInvolution_tubeTangentFiber (q : NormalBundleTube)
    (v : EuclideanSpace ℝ (Fin 3)) :
    mfderiv tubeModel tubeModel normalInvolution q (tubeTangentFiber q v) =
      tubeTangentFiber (normalInvolution q) (fiberInvolutionLI v) := by
  have h1 : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ) circleHalfTurn q.1 :=
    contMDiff_circleHalfTurn.mdifferentiableAt (by simp)
  have h2 : MDifferentiableAt (𝓡 3) (𝓡 3) ballFiberInvolution q.2 :=
    contMDiff_ballFiberInvolution.mdifferentiableAt (by simp)
  have heq : normalInvolution = Prod.map circleHalfTurn ballFiberInvolution := rfl
  let u : TangentSpace (𝓡 3) q.2 := (fiberTangentEquiv q.2).symm v
  have hfv : TauCeti.Manifold.tangentSpaceOpenEquiv q.2 u =
      (NormedSpace.fromTangentSpace q.2.1).symm v := by
    apply (NormedSpace.fromTangentSpace q.2.1).injective
    rw [← ContinuousLinearEquiv.trans_apply, ← fiberTangentEquiv,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  have hball : mfderiv (𝓡 3) (𝓡 3) ballFiberInvolution q.2 u =
      (fiberTangentEquiv (ballFiberInvolution q.2)).symm (fiberInvolutionLI v) := by
    apply (fiberTangentEquiv (ballFiberInvolution q.2)).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    have hcomp : (Subtype.val : OpenBall3 → EuclideanSpace ℝ (Fin 3)) ∘ ballFiberInvolution =
        fiberInvolutionLI.toContinuousLinearMap ∘ Subtype.val := rfl
    have hsub := TauCeti.Manifold.tangentSpaceOpenEquiv_mfderiv_apply
      (I := 𝓡 3) (I' := 𝓡 3) (f := ballFiberInvolution)
      (A := fiberInvolutionLI.toContinuousLinearMap) hcomp u
    rw [fiberTangentEquiv, ContinuousLinearEquiv.trans_apply, hsub, hfv]
    change NormedSpace.fromTangentSpace (fiberInvolutionLI.toContinuousLinearMap q.2.1)
      (mfderiv (𝓡 3) (𝓡 3) fiberInvolutionLI.toContinuousLinearMap q.2.1
        ((NormedSpace.fromTangentSpace q.2.1).symm v)) = fiberInvolutionLI v
    rw [mfderiv_eq_fderiv, fiberInvolutionLI.toContinuousLinearMap.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply]
    rfl
  rw [tubeTangentFiber_eq_prodEquiv_symm q,
    tubeTangentFiber_eq_prodEquiv_symm (normalInvolution q),
    heq, TauCeti.Manifold.mfderiv_prodMap_apply h1 h2, map_zero]
  change (TauCeti.Manifold.tangentSpaceProdEquiv
      (circleHalfTurn q.1, ballFiberInvolution q.2)).symm
      (0, mfderiv (𝓡 3) (𝓡 3) ballFiberInvolution q.2 u) = _
  rw [hball]
  rfl

/-- `normalInvolution` is orientation-preserving on `S¹ × B³`:
`i^* tubeVolumeForm = tubeVolumeForm`. -/
theorem mpullback_normalInvolution_tubeVolumeForm :
    SmoothForm.mpullback normalInvolution contMDiff_normalInvolution tubeVolumeForm =
      tubeVolumeForm := by
  have hang : SmoothForm.mpullback normalInvolution contMDiff_normalInvolution tubeAngularForm =
      tubeAngularForm := by
    rw [tubeAngularForm, SmoothForm.mpullback_mpullback_of_comp_eq
      contMDiff_normalInvolution contMDiff_fst contMDiff_fst contMDiff_circleHalfTurn rfl]
    congr 1
    apply Subtype.ext
    rw [SmoothForm.coe_mpullback]
    unfold circleHalfTurn
    exact AddCircle.mpullback_add_right_timeForm (2 * Real.pi) (Real.pi : CircleS1)
  have hfib_vol : SmoothForm.mpullback fiberInvolutionLI fiberInvolutionLI.contDiff.contMDiff
      (euclideanVolumeForm 3) = euclideanVolumeForm 3 := by
    apply Subtype.ext
    funext x
    let b : Module.Basis (Fin 3) ℝ (TangentSpace (𝓡 3) x) :=
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map
        (NormedSpace.fromTangentSpace x).symm.toLinearEquiv
    ext w
    rw [ContinuousAlternatingMap.apply_eq_det_mul _ b w,
      ContinuousAlternatingMap.apply_eq_det_mul _ b w]
    congr 1
    have hvol_b : (euclideanVolumeForm 3).1 x b = 1 :=
      euclideanVolumeForm_apply_basisFun 3 x
    rw [hvol_b, SmoothForm.mpullback_apply]
    let y := fiberInvolutionLI x
    have hpush : (fun i : Fin 3 ↦ mfderiv (𝓡 3) (𝓡 3) fiberInvolutionLI x (b i)) =
        ![(NormedSpace.fromTangentSpace y).symm (-EuclideanSpace.basisFun (Fin 3) ℝ 0),
          (NormedSpace.fromTangentSpace y).symm (-EuclideanSpace.basisFun (Fin 3) ℝ 1),
          (NormedSpace.fromTangentSpace y).symm (EuclideanSpace.basisFun (Fin 3) ℝ 2)] := by
      funext i
      have hbi : b i =
          (NormedSpace.fromTangentSpace x).symm (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
        simp [b]
      rw [hbi]
      apply (NormedSpace.fromTangentSpace y).injective
      change NormedSpace.fromTangentSpace (fiberInvolutionLI.toContinuousLinearMap x)
        (mfderiv (𝓡 3) (𝓡 3) fiberInvolutionLI.toContinuousLinearMap x
          ((NormedSpace.fromTangentSpace x).symm (EuclideanSpace.basisFun (Fin 3) ℝ i))) = _
      rw [mfderiv_eq_fderiv, fiberInvolutionLI.toContinuousLinearMap.fderiv]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply]
      fin_cases i
      · change fiberInvolutionLI (EuclideanSpace.basisFun (Fin 3) ℝ 0) =
            -EuclideanSpace.basisFun (Fin 3) ℝ 0
        ext j; fin_cases j <;> simp [fiberInvolutionLI]
      · change fiberInvolutionLI (EuclideanSpace.basisFun (Fin 3) ℝ 1) =
            -EuclideanSpace.basisFun (Fin 3) ℝ 1
        ext j; fin_cases j <;> simp [fiberInvolutionLI]
      · change fiberInvolutionLI (EuclideanSpace.basisFun (Fin 3) ℝ 2) =
            EuclideanSpace.basisFun (Fin 3) ℝ 2
        ext j; fin_cases j <;> simp [fiberInvolutionLI]
    rw [hpush]
    have h3 := euclidean3VolumeForm_triple y
      (-EuclideanSpace.basisFun (Fin 3) ℝ 0)
      (-EuclideanSpace.basisFun (Fin 3) ℝ 1)
      (EuclideanSpace.basisFun (Fin 3) ℝ 2)
    refine h3.trans ?_
    simp
  have hfib : SmoothForm.mpullback normalInvolution contMDiff_normalInvolution
      tubeFiberVolumeForm = tubeFiberVolumeForm := by
    rw [tubeFiberVolumeForm, SmoothForm.mpullback_mpullback_of_comp_eq
      contMDiff_normalInvolution contMDiff_tubeFiberIncl
      contMDiff_tubeFiberIncl fiberInvolutionLI.contDiff.contMDiff rfl, hfib_vol]
  rw [tubeVolumeForm]
  exact (SmoothForm.mpullback_wedge normalInvolution contMDiff_normalInvolution
    tubeAngularForm tubeFiberVolumeForm).trans (by rw [hang, hfib])

/-- **GSV15 Proposition 3.2**: Whenever `k` is invariant under `normalInvolution`
(`∀ q, k (normalInvolution q) = k q`), `normalInvolution` is a smooth Poisson diffeomorphism of
`singularCirclePoisson k`. -/
theorem isPoissonMap_normalInvolution (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯)
    (hk_inv : ∀ q, k (normalInvolution q) = k q) :
    SmoothBivector.IsPoissonMap
      (singularCirclePoisson k).toSmoothBivector
      (singularCirclePoisson k).toSmoothBivector
      normalInvolution contMDiff_normalInvolution := by
  intro g h
  ext q
  let iMap : C^∞⟮tubeModel, NormalBundleTube; tubeModel, NormalBundleTube⟯ :=
    ⟨normalInvolution, contMDiff_normalInvolution⟩
  have hpartial (u : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯) :
      fiberPartial (u.comp iMap) 0 q = -fiberPartial u 0 (normalInvolution q) ∧
        fiberPartial (u.comp iMap) 1 q = -fiberPartial u 1 (normalInvolution q) ∧
        fiberPartial (u.comp iMap) 2 q = fiberPartial u 2 (normalInvolution q) := by
    have hu : MDifferentiableAt tubeModel 𝓘(ℝ) u (normalInvolution q) :=
      u.contMDiff.mdifferentiableAt (by simp)
    have hi : MDifferentiableAt tubeModel tubeModel normalInvolution q :=
      contMDiff_normalInvolution.mdifferentiableAt (by simp)
    have hcomp (j : Fin 3) :
        fiberPartial (u.comp iMap) j q =
          mvfderiv tubeModel u (normalInvolution q)
            (tubeTangentFiber (normalInvolution q)
              (fiberInvolutionLI (EuclideanSpace.basisFun (Fin 3) ℝ j))) := by
      dsimp only [fiberPartial]
      have hcoe : ⇑(u.comp iMap) = u ∘ normalInvolution := rfl
      rw [hcoe, mvfderiv_comp_apply q hu hi, mfderiv_normalInvolution_tubeTangentFiber]
    have he0 : fiberInvolutionLI (EuclideanSpace.basisFun (Fin 3) ℝ 0) =
        -EuclideanSpace.basisFun (Fin 3) ℝ 0 := by
      ext l; fin_cases l <;> simp [fiberInvolutionLI]
    have he1 : fiberInvolutionLI (EuclideanSpace.basisFun (Fin 3) ℝ 1) =
        -EuclideanSpace.basisFun (Fin 3) ℝ 1 := by
      ext l; fin_cases l <;> simp [fiberInvolutionLI]
    have he2 : fiberInvolutionLI (EuclideanSpace.basisFun (Fin 3) ℝ 2) =
        EuclideanSpace.basisFun (Fin 3) ℝ 2 := by
      ext l; fin_cases l <;> simp [fiberInvolutionLI]
    refine ⟨?_, ?_, ?_⟩
    · rw [hcomp 0, he0, ← tubeTangentFiber_neg, map_neg]; rfl
    · rw [hcomp 1, he1, ← tubeTangentFiber_neg, map_neg]; rfl
    · rw [hcomp 2, he2]; rfl
  obtain ⟨hg0, hg1, hg2⟩ := hpartial g
  obtain ⟨hh0, hh1, hh2⟩ := hpartial h
  change ((singularCirclePoisson k).bracket (g.comp iMap) (h.comp iMap)) q =
    ((singularCirclePoisson k).bracket g h) (normalInvolution q)
  rw [singularCirclePoisson_bracket_apply, singularCirclePoisson_bracket_apply,
    hg0, hg1, hg2, hh0, hh1, hh2, hk_inv q]
  have hv2 (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) 2 = c := rfl
  simp only [normalInvolution, ballFiberInvolution, fiberInvolutionLI,
    LinearIsometryEquiv.coe_mk, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one, hv2]
  ring

/-- Whenever `k ∘ normalInvolution = k` and `k` is nowhere-vanishing, `normalInvolution` preserves
the unimodular volume `4`-form `(1 / k) dθ ∧ dx₁ ∧ dx₂ ∧ dx₃`. -/
theorem mpullback_normalInvolution_invKTubeVolumeForm
    (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯) (hk : ∀ q, k q ≠ 0)
    (hk_inv : ∀ q, k (normalInvolution q) = k q) :
    SmoothForm.mpullback normalInvolution contMDiff_normalInvolution (invKTubeVolumeForm k hk) =
      invKTubeVolumeForm k hk := by
  have hvol := mpullback_normalInvolution_tubeVolumeForm
  apply Subtype.ext
  funext q
  ext v
  rw [SmoothForm.mpullback_apply, invKTubeVolumeForm_apply, invKTubeVolumeForm_apply, hk_inv q]
  congr 1
  have hq := DFunLike.congr_fun (congrFun (congrArg Subtype.val hvol) q) v
  rwa [SmoothForm.mpullback_apply] at hq

/-! ## 5. Equation (5) (`GSV15` Proposition 3.3): Symplectic Foliation and Leaf Symplectic Form -/

/-- Euclidean radial distance `R(q) = √(x₁² + x₂² + x₃²)` from the singular circle `S¹ × {0}`. -/
def fiberRadius (q : NormalBundleTube) : ℝ :=
  √((q.2.1 0) ^ 2 + (q.2.1 1) ^ 2 + (q.2.1 2) ^ 2)

theorem fiberRadius_eq_norm (q : NormalBundleTube) :
    fiberRadius q = ‖(q.2 : EuclideanSpace ℝ (Fin 3))‖ := by
  rw [fiberRadius, EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]

theorem fiberRadius_pos_of_notMem_singularCircleLocus {q : NormalBundleTube}
    (hq : q ∉ singularCircleLocus) :
    0 < fiberRadius q := by
  rw [fiberRadius_eq_norm]
  exact norm_pos_iff.mpr hq

/-- Unnormalized fiber normal `(-x₁, x₂, x₃) = (1/2) ∇_x Q` to the regular leaf `Σ_q ⊂ {θ} × B³`. -/
def casimirFiberGrad (q : NormalBundleTube) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![-q.2.1 0, q.2.1 1, q.2.1 2]

/-- Unit normal `n(q) = R(q)⁻¹ • (-x₁, x₂, x₃)` to the regular leaf `Σ_q ⊂ {θ} × B³`. -/
def leafUnitNormal (q : NormalBundleTube) : EuclideanSpace ℝ (Fin 3) :=
  (fiberRadius q)⁻¹ • casimirFiberGrad q

theorem norm_leafUnitNormal {q : NormalBundleTube} (hq : q ∉ singularCircleLocus) :
    ‖leafUnitNormal q‖ = 1 := by
  have hpos := fiberRadius_pos_of_notMem_singularCircleLocus hq
  have hgrad_norm : ‖casimirFiberGrad q‖ = fiberRadius q := by
    rw [EuclideanSpace.norm_eq, fiberRadius]
    congr 1
    simp [casimirFiberGrad, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  rw [leafUnitNormal, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le), hgrad_norm,
    inv_mul_cancel₀ hpos.ne']

theorem range_anchor_singularCirclePoisson_eq_unit
    (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯) {q : NormalBundleTube} (hkq : k q ≠ 0) :
    LinearMap.range ((singularCirclePoisson k).anchor q).toLinearMap =
      LinearMap.range (singularCircleUnitPoisson.anchor q).toLinearMap := by
  ext v
  constructor
  · rintro ⟨α, rfl⟩
    exact ⟨k q • α, by
      change (singularCircleUnitPoisson.anchor q) (k q • α) =
        k q • singularCircleUnitPoisson.anchor q α
      exact map_smul _ _ _⟩
  · rintro ⟨α, rfl⟩
    exact ⟨(k q)⁻¹ • α, by
      change k q • (singularCircleUnitPoisson.anchor q) ((k q)⁻¹ • α) =
        singularCircleUnitPoisson.anchor q α
      rw [map_smul, smul_smul, mul_inv_cancel₀ hkq, one_smul]⟩

/-- At every regular point `q ∉ singularCircleLocus` where `k q ≠ 0`, `singularCirclePoisson k`
has rank `2`. -/
theorem rankAt_singularCirclePoisson_of_notMem_singularCircleLocus
    (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯) {q : NormalBundleTube}
    (hq : q ∉ singularCircleLocus) (hkq : k q ≠ 0) :
    (singularCirclePoisson k).rankAt q = 2 := by
  have hreg : q ∉ criticalSet tubeModel cylinderModel singularCircleCasimirMap := by
    rwa [criticalSet_singularCircleCasimirMap]
  have hunit_rank : singularCircleUnitPoisson.rankAt q = 2 :=
    rankAt_jacobianPoisson_of_notMem_criticalSet unitScaledTubeVolumeForm
      unitScaledTubeVolumeForm_ne_zero cylinderAreaForm singularCircleCasimirMap
      contMDiff_singularCircleCasimirMap hreg (cylinderAreaForm_ne_zero _)
  unfold SmoothBivector.rankAt at hunit_rank ⊢
  rwa [range_anchor_singularCirclePoisson_eq_unit k hkq]

/-- At every regular point `q ∉ singularCircleLocus` where `k q ≠ 0`, the characteristic plane
`Im(#_{π_k, q})` consists of vertical fiber vectors orthogonal to `leafUnitNormal q`. -/
theorem mem_range_anchor_singularCirclePoisson_iff
    (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯) {q : NormalBundleTube}
    (hq : q ∉ singularCircleLocus) (hkq : k q ≠ 0) (v : TangentSpace tubeModel q) :
    v ∈ LinearMap.range ((singularCirclePoisson k).anchor q).toLinearMap ↔
      (tubeTangentEquiv q v).1 = 0 ∧ inner ℝ (leafUnitNormal q) (tubeTangentEquiv q v).2 = 0 := by
  have hreg : q ∉ criticalSet tubeModel cylinderModel singularCircleCasimirMap := by
    rwa [criticalSet_singularCircleCasimirMap]
  have hker := range_anchor_eq_ker_mfderiv_of_notMem_criticalSet unitScaledTubeVolumeForm
    unitScaledTubeVolumeForm_ne_zero cylinderAreaForm singularCircleCasimirMap
    contMDiff_singularCircleCasimirMap hreg (cylinderAreaForm_ne_zero _)
  rw [range_anchor_singularCirclePoisson_eq_unit k hkq]
  dsimp only [singularCircleUnitPoisson]
  rw [hker, LinearMap.mem_ker]
  change mfderiv tubeModel cylinderModel singularCircleCasimirMap q v = 0 ↔ _
  have hzero_iff : mfderiv tubeModel cylinderModel singularCircleCasimirMap q v = 0 ↔
      cylinderTangentEquiv (singularCircleCasimirMap q)
        (mfderiv tubeModel cylinderModel singularCircleCasimirMap q v) = 0 :=
    ⟨fun h ↦ by rw [h, map_zero],
      fun h ↦ (cylinderTangentEquiv (singularCircleCasimirMap q)).injective
        (h.trans (map_zero _).symm)⟩
  rw [hzero_iff, mfderiv_singularCircleCasimirMap_apply]
  have hv_eq := tubeTangent_decomp q v
  have hcas : mvfderiv tubeModel casimirQuad q v =
      2 * inner ℝ (casimirFiberGrad q) (tubeTangentEquiv q v).2 := by
    conv_lhs => rw [hv_eq]
    rw [map_add, map_smul, mvfderiv_casimirQuad_tubeTangentTheta, smul_zero, zero_add,
      mvfderiv_casimirQuad_tubeTangentFiber, EuclideanSpace.inner_eq_star_dotProduct]
    simp [casimirFiberGrad, dotProduct, Fin.sum_univ_three]
    ring
  have hrpos := fiberRadius_pos_of_notMem_singularCircleLocus hq
  rw [hcas, Prod.mk_eq_zero]
  refine and_congr Iff.rfl ?_
  rw [leafUnitNormal, inner_smul_left]
  simp only [conj_trivial, mul_eq_zero, OfNat.ofNat_ne_zero, inv_eq_zero, hrpos.ne', false_or]

/-- Induced Euclidean surface area bilinear form `ω_Area(v, w) = (ι_{n(q)} vol_{ℝ³})(v_x, w_x)` on
the fiber slice at `q ∈ S¹ × B³`. -/
def leafAreaForm (q : NormalBundleTube) (v w : TangentSpace tubeModel q) : ℝ :=
  let vx : EuclideanSpace ℝ (Fin 3) := (tubeTangentEquiv q v).2
  let wx : EuclideanSpace ℝ (Fin 3) := (tubeTangentEquiv q w).2
  (euclideanVolumeForm 3).1 q.2.1
    ![(leafUnitNormal q : TangentSpace (𝓡 3) q.2.1),
      (vx : TangentSpace (𝓡 3) q.2.1),
      (wx : TangentSpace (𝓡 3) q.2.1)]

/-- Explicit determinant formula for `leafAreaForm q v w`. -/
theorem leafAreaForm_apply (q : NormalBundleTube) (v w : TangentSpace tubeModel q) :
    leafAreaForm q v w =
      let vx := (tubeTangentEquiv q v).2
      let wx := (tubeTangentEquiv q w).2
      (fiberRadius q)⁻¹ *
        (-q.2.1 0 * (vx 1 * wx 2 - vx 2 * wx 1) -
          q.2.1 1 * (vx 0 * wx 2 - vx 2 * wx 0) +
          q.2.1 2 * (vx 0 * wx 1 - vx 1 * wx 0)) := by
  dsimp only [leafAreaForm]
  rw [euclidean3VolumeForm_triple]
  simp [leafUnitNormal, casimirFiberGrad]
  ring

/-- **Equation (5) (`GSV15`, Proposition 3.3)**: Regular-leaf symplectic bilinear form
`ω_{Σ_q} = (k(θ, x₁, x₂, x₃) * √(x₁² + x₂² + x₃²))⁻¹ * ω_Area`. -/
def leafSymplecticForm (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯) (q : NormalBundleTube)
    (v w : TangentSpace tubeModel q) : ℝ :=
  (1 / (k q * √((q.2.1 0) ^ 2 + (q.2.1 1) ^ 2 + (q.2.1 2) ^ 2))) * leafAreaForm q v w

theorem leafSymplecticForm_skew (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯) (q : NormalBundleTube)
    (v w : TangentSpace tubeModel q) :
    leafSymplecticForm k q v w = -leafSymplecticForm k q w v := by
  simp only [leafSymplecticForm, leafAreaForm_apply]
  ring

/-- **GSV15 Proposition 3.3 (Equation (5))**: At every regular point `q ∉ singularCircleLocus` with
`k q ≠ 0`, `leafSymplecticForm k q` pairs Hamiltonian vector fields to minus the Poisson bracket:
`ω_{Σ_q}(X_g(q), X_h(q)) = -{g, h}_{π_k}(q)`. -/
theorem leafSymplecticForm_hamiltonianVectorField
    (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯) {q : NormalBundleTube}
    (hq : q ∉ singularCircleLocus) (hkq : k q ≠ 0)
    (g h : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯) :
    leafSymplecticForm k q
        ((singularCirclePoisson k).hamiltonianVectorField g q)
        ((singularCirclePoisson k).hamiltonianVectorField h q) =
      -((singularCirclePoisson k).bracket g h) q := by
  have hrpos := fiberRadius_pos_of_notMem_singularCircleLocus hq
  have hr_ne : fiberRadius q ≠ 0 := hrpos.ne'
  have hr_sq : (fiberRadius q) ^ 2 = (q.2.1 0) ^ 2 + (q.2.1 1) ^ 2 + (q.2.1 2) ^ 2 :=
    Real.sq_sqrt (by positivity)
  rw [leafSymplecticForm, ← fiberRadius, leafAreaForm_apply,
    singularCirclePoisson_hamiltonianVectorField_apply,
    singularCirclePoisson_hamiltonianVectorField_apply,
    singularCirclePoisson_bracket_apply]
  dsimp only
  rw [tubeTangentEquiv_fiber, tubeTangentEquiv_fiber]
  simp only [PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hv2 (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) 2 = c := rfl
  simp only [hv2]
  have hpoly :
      -q.2.1 0 *
          ((k q * (q.2.1 0 * fiberPartial g 2 q + q.2.1 2 * fiberPartial g 0 q)) *
              (k q * (-q.2.1 0 * fiberPartial h 1 q - q.2.1 1 * fiberPartial h 0 q)) -
            (k q * (-q.2.1 0 * fiberPartial g 1 q - q.2.1 1 * fiberPartial g 0 q)) *
              (k q * (q.2.1 0 * fiberPartial h 2 q + q.2.1 2 * fiberPartial h 0 q))) -
        q.2.1 1 *
          ((k q * (q.2.1 1 * fiberPartial g 2 q - q.2.1 2 * fiberPartial g 1 q)) *
              (k q * (-q.2.1 0 * fiberPartial h 1 q - q.2.1 1 * fiberPartial h 0 q)) -
            (k q * (-q.2.1 0 * fiberPartial g 1 q - q.2.1 1 * fiberPartial g 0 q)) *
              (k q * (q.2.1 1 * fiberPartial h 2 q - q.2.1 2 * fiberPartial h 1 q))) +
        q.2.1 2 *
          ((k q * (q.2.1 1 * fiberPartial g 2 q - q.2.1 2 * fiberPartial g 1 q)) *
              (k q * (q.2.1 0 * fiberPartial h 2 q + q.2.1 2 * fiberPartial h 0 q)) -
            (k q * (q.2.1 0 * fiberPartial g 2 q + q.2.1 2 * fiberPartial g 0 q)) *
              (k q * (q.2.1 1 * fiberPartial h 2 q - q.2.1 2 * fiberPartial h 1 q))) =
        -(k q) ^ 2 * ((q.2.1 0) ^ 2 + (q.2.1 1) ^ 2 + (q.2.1 2) ^ 2) *
          (q.2.1 0 * (fiberPartial g 1 q * fiberPartial h 2 q -
              fiberPartial g 2 q * fiberPartial h 1 q) +
            q.2.1 1 * (fiberPartial g 0 q * fiberPartial h 2 q -
              fiberPartial g 2 q * fiberPartial h 0 q) -
            q.2.1 2 * (fiberPartial g 0 q * fiberPartial h 1 q -
              fiberPartial g 1 q * fiberPartial h 0 q)) := by
    ring
  rw [hpoly, ← hr_sq]
  field_simp [hkq, hr_ne]

/-- `leafSymplecticForm k q` is nondegenerate on the 2-dimensional symplectic leaf tangent space
`Im(#_{π_k, q})` at every regular point `q ∉ singularCircleLocus` where `k q ≠ 0`. -/
theorem leafSymplecticForm_nondegenerate_on_leaf
    (k : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯) {q : NormalBundleTube}
    (hq : q ∉ singularCircleLocus) (hkq : k q ≠ 0)
    {v : TangentSpace tubeModel q}
    (hv : v ∈ LinearMap.range ((singularCirclePoisson k).anchor q).toLinearMap)
    (horth : ∀ w ∈ LinearMap.range ((singularCirclePoisson k).anchor q).toLinearMap,
      leafSymplecticForm k q v w = 0) :
    v = 0 := by
  obtain ⟨α, rfl⟩ := hv
  let c := fun i : Fin 3 ↦ -α (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ i))
  let g : C^∞⟮tubeModel, NormalBundleTube; ℝ⟯ :=
    c 0 • tubeCoord 0 + c 1 • tubeCoord 1 + c 2 • tubeCoord 2
  have hfg (i : Fin 3) : fiberPartial g i q = c i := by
    have hd (j : Fin 3) : MDifferentiableAt tubeModel 𝓘(ℝ) (tubeCoord j) q :=
      (tubeCoord j).contMDiff.mdifferentiableAt (by simp)
    have hs (j : Fin 3) : MDifferentiableAt tubeModel 𝓘(ℝ) (c j • tubeCoord j) q :=
      (c j • tubeCoord j).contMDiff.mdifferentiableAt (by simp)
    have hcoe : ⇑g = (⇑(c 0 • tubeCoord 0) + ⇑(c 1 • tubeCoord 1)) + ⇑(c 2 • tubeCoord 2) := rfl
    dsimp only [fiberPartial]
    rw [hcoe, mvfderiv_add ((hs 0).add (hs 1)) (hs 2), add_apply,
      mvfderiv_add (hs 0) (hs 1), add_apply]
    have hm (j : Fin 3) :
        mvfderiv tubeModel (c j • tubeCoord j) q
          (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ i)) =
          c j * (EuclideanSpace.basisFun (Fin 3) ℝ i) j := by
      rw [ContMDiffMap.coe_smul, Pi.smul_def, mvfderiv_const_smul (hd j), smul_apply,
        smul_eq_mul, mvfderiv_tubeCoord_tubeTangentFiber]
    rw [hm 0, hm 1, hm 2]
    fin_cases i <;> simp
  have hv_ham : ((singularCirclePoisson k).anchor q).toLinearMap α =
      (singularCirclePoisson k).hamiltonianVectorField g q := by
    change (singularCirclePoisson k).anchor q α = _
    rw [singularCirclePoisson_anchor_apply, singularCirclePoisson_hamiltonianVectorField_apply,
      hfg 0, hfg 1, hfg 2]
    dsimp only [c]
    congr 1
    ext j
    fin_cases j
    · dsimp only
      simp only [PiLp.smul_apply, smul_eq_mul]
      change k q * (-q.2.1 1 * α (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 2)) +
          q.2.1 2 * α (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 1))) =
        k q * (q.2.1 1 * -α (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 2)) -
          q.2.1 2 * -α (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 1)))
      ring
    · dsimp only
      simp only [PiLp.smul_apply, smul_eq_mul]
      change k q * (-q.2.1 0 * α (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 2)) -
          q.2.1 2 * α (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 0))) =
        k q * (q.2.1 0 * -α (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 2)) +
          q.2.1 2 * -α (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 0)))
      ring
    · dsimp only
      simp only [PiLp.smul_apply, smul_eq_mul]
      change k q * (q.2.1 0 * α (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 1)) +
          q.2.1 1 * α (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 0))) =
        k q * (-q.2.1 0 * -α (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 1)) -
          q.2.1 1 * -α (tubeTangentFiber q (EuclideanSpace.basisFun (Fin 3) ℝ 0)))
      ring
  rw [hv_ham] at horth ⊢
  have hcoord (j : Fin 3) :
      ((singularCirclePoisson k).bracket g (tubeCoord j)) q = 0 := by
    have hw_mem : (singularCirclePoisson k).hamiltonianVectorField (tubeCoord j) q ∈
        LinearMap.range ((singularCirclePoisson k).anchor q).toLinearMap :=
      ⟨-mvfderiv tubeModel (tubeCoord j) q, by
        simp [SmoothBivector.hamiltonianVectorField]⟩
    have h0 := horth _ hw_mem
    rw [leafSymplecticForm_hamiltonianVectorField k hq hkq g (tubeCoord j)] at h0
    linarith
  rw [singularCirclePoisson_hamiltonianVectorField_apply]
  have hz : (k q • WithLp.toLp 2
      ![q.2.1 1 * fiberPartial g 2 q - q.2.1 2 * fiberPartial g 1 q,
        q.2.1 0 * fiberPartial g 2 q + q.2.1 2 * fiberPartial g 0 q,
        -q.2.1 0 * fiberPartial g 1 q - q.2.1 1 * fiberPartial g 0 q]) = 0 := by
    ext j
    have hj := hcoord j
    rw [singularCirclePoisson_bracket_apply] at hj
    fin_cases j
    · dsimp only at hj ⊢
      simp only [fiberPartial_tubeCoord] at hj
      norm_num at hj
      simp only [PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply]
      change k q * (q.2.1 1 * fiberPartial g 2 q - q.2.1 2 * fiberPartial g 1 q) = 0
      have hlin : q.2.1 1 * fiberPartial g 2 q - q.2.1 2 * fiberPartial g 1 q = 0 := by
        linarith [hj.resolve_left hkq]
      rw [hlin, mul_zero]
    · dsimp only at hj ⊢
      simp only [fiberPartial_tubeCoord] at hj
      norm_num at hj
      simp only [PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply]
      change k q * (q.2.1 0 * fiberPartial g 2 q + q.2.1 2 * fiberPartial g 0 q) = 0
      have hlin : q.2.1 0 * fiberPartial g 2 q + q.2.1 2 * fiberPartial g 0 q = 0 := by
        linarith [hj.resolve_left hkq]
      rw [hlin, mul_zero]
    · dsimp only at hj ⊢
      simp only [fiberPartial_tubeCoord] at hj
      norm_num at hj
      simp only [PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply]
      change k q * (-q.2.1 0 * fiberPartial g 1 q - q.2.1 1 * fiberPartial g 0 q) = 0
      have hlin : -q.2.1 0 * fiberPartial g 1 q - q.2.1 1 * fiberPartial g 0 q = 0 := by
        linarith [hj.resolve_left hkq]
      rw [hlin, mul_zero]
  rw [hz, tubeTangentFiber_zero]

end S4TuringPoisson
