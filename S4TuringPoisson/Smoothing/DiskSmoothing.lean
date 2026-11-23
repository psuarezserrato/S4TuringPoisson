/-
Copyright (c) 2026 Pablo Suárez-Serrato. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Suárez-Serrato
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import S4TuringPoisson.Dynamics.GeneralizedShift
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Flow.TimeDependent
public import TauCeti.Geometry.Manifold.Flow.TimeDependent
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
public import TauCeti.Geometry.Symplectic.Manifold.Surface

/-!
# Hamiltonian Disk-Isotopy Engine, CMPP21 Elementary Moves & Cantor Bridge (Milestone M3.3)

This module implements Stretch Track Milestone M3.3 of `S4TuringPoisson`, connecting `TauCeti`'s
symplectic Hamiltonian ODE engine on `EuclideanPlane` (`ℝ²`) to `AreaPreservingDiskIsotopy`,
the elementary area-preserving disk moves of Figures 1 and 2 of `S4TCdiffeo-Aug-2026.tex`, and the
`HasTuringCompleteAreaPreservingDiskIsotopy` interface of Milestone M0.3:

1. **Unconditional `TauCeti` Time-Dependent Hamiltonian Disk-Isotopy Engine**:
   - `CompactlySupportedPlanarHamiltonian r₀`: packages a jointly $C^\infty$ time-dependent
     Hamiltonian `H : ℝ × EuclideanPlane → ℝ` vanishing outside `Metric.ball 0 r₀` (`r₀ ∈ (0, 1)`).
   - `AreaPreservingDiskIsotopy r₀`: packages a jointly $C^\infty$ compactly supported isotopy
     `d, dInv : ℝ × EuclideanPlane → EuclideanPlane` starting at `id` at `t = 0` with unit Jacobian
     determinant `det (fderiv ℝ (d_t) y) = 1` everywhere.
   - `CompactlySupportedPlanarHamiltonian.toDiskIsotopy`: integrates any
     `CompactlySupportedPlanarHamiltonian r₀` via `TauCeti.timeDependentFlowOf` with respect to
     `planeAreaForm`, proving completeness on `Metric.closedBall 0 r₀`, vanishing of `X_{H_t}`
     outside `Metric.ball 0 r₀` by radial continuity, joint $C^\infty$ regularity of forward and
     backward flows, and `det (fderiv ℝ (d_t) y) = 1` via Cartan's magic formula
     (`TauCeti.mpullback_timeDependentFlowOf_of_mextDeriv_interior_eq_zero`, `d² = 0`, and
     `mpullback_planeAreaForm_eq_iff_det_fderiv_eq_one`).

2. **Composition Groupoid & Concrete `CMPP21` Elementary Moves (Figures 1 & 2)**:
   - `AreaPreservingDiskIsotopy.refl`, `.symm`, `.mono`, `.comp`, `.compSame`, `.listComp`: proves
     closure of `AreaPreservingDiskIsotopy` under identity, inverse, support-radius enlargement,
     pointwise isotopy composition `(t, y) ↦ d₂(t, d₁(t, y))`, and finite list products.
   - Constructively realizes via bumped autonomous `CompactlySupportedPlanarHamiltonian`s the
     elementary `CMPP21` / `S4TCdiffeo-Aug-2026.tex` Figures 1–2 building blocks (`bumpedRotation`,
     `sectorSwap`, and `bumpedHyperbolicStretch`) and proves their exact time-`1` action and
     non-triviality (`≠ id`) via ODE uniqueness (`TauCeti.timeDependentFlowOf_eq_of_hasMFDerivAt`).

3. **`CMPP21` Cantor-Circulation Bridge to `HasTuringCompleteAreaPreservingDiskIsotopy`**:
   - Proves unconditionally that any `AreaPreservingDiskIsotopy` conjugating a universal
     `ReversibleTM` generalized shift on `cantorDiskEmbed` yields a full anti-vacuous
     `TuringCompleteWitness` (including primitive-recursive `2⁻ᵐ` `RatFrac` approximations).
   - Packages the sharp `CMPP21` smooth Cantor-circulation hypothesis in
     `HasCMPPCantorCirculationHamiltonians` (stating purely that a finite list of
     `CompactlySupportedPlanarHamiltonian`s realizes the reversible Cantor-block shift at `t = 1`)
     and exports `instHasTuringCompleteAreaPreservingDiskIsotopyOfCMPP`.
-/

@[expose] public section

open Bundle Filter Function Metric Module Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace S4TuringPoisson

/-! ## 1. `AreaPreservingDiskIsotopy` & Composition Groupoid -/

/-- A jointly $C^\infty$, compactly supported, area-preserving planar isotopy supported inside
`Metric.ball 0 r₀` (`r₀ ∈ (0, 1)`), matching all geometric fields of
`HasTuringCompleteAreaPreservingDiskIsotopy`. -/
structure AreaPreservingDiskIsotopy (r₀ : ℝ) where
  /-- `0 < r₀` and `r₀ < 1`. -/
  r₀_mem_Ioo : r₀ ∈ Set.Ioo (0 : ℝ) 1
  /-- Forward time-dependent planar isotopy `(t, y) ↦ d(t, y)`. -/
  d : ℝ × EuclideanPlane → EuclideanPlane
  /-- Inverse time-dependent planar family `(t, y) ↦ d_t⁻¹(y)`. -/
  dInv : ℝ × EuclideanPlane → EuclideanPlane
  /-- Joint $C^\infty$ smoothness of `d` on `ℝ × ℝ²`. -/
  contDiff_d : ContDiff ℝ ∞ d
  /-- Joint $C^\infty$ smoothness of `dInv` on `ℝ × ℝ²`. -/
  contDiff_dInv : ContDiff ℝ ∞ dInv
  /-- `dInv (t, ·)` is a left inverse to `d (t, ·)` for every `t : ℝ`. -/
  left_inv : ∀ (t : ℝ) (y : EuclideanPlane), dInv (t, d (t, y)) = y
  /-- `dInv (t, ·)` is a right inverse to `d (t, ·)` for every `t : ℝ`. -/
  right_inv : ∀ (t : ℝ) (y : EuclideanPlane), d (t, dInv (t, y)) = y
  /-- Every slice `d (t, ·)` fixes all points outside `Metric.ball 0 r₀`. -/
  eq_self_of_notMem_ball :
    ∀ (t : ℝ) (y : EuclideanPlane), y ∉ Metric.ball (0 : EuclideanPlane) r₀ → d (t, y) = y
  /-- Isotopy starts at `id` at `t = 0`. -/
  time_zero : ∀ y : EuclideanPlane, d (0, y) = y
  /-- Unit Jacobian determinant `det (D_y d_t(y)) = 1` for all `(t, y)`. -/
  det_fderiv_eq_one :
    ∀ (t : ℝ) (y : EuclideanPlane),
      LinearMap.det (fderiv ℝ (fun z ↦ d (t, z)) y).toLinearMap = 1

namespace AreaPreservingDiskIsotopy

section Basic

/-- `0 < r₀`. -/
theorem r₀_pos {r₀ : ℝ} (I : AreaPreservingDiskIsotopy r₀) : 0 < r₀ :=
  I.r₀_mem_Ioo.1

/-- `r₀ < 1`. -/
theorem r₀_lt_one {r₀ : ℝ} (I : AreaPreservingDiskIsotopy r₀) : r₀ < 1 :=
  I.r₀_mem_Ioo.2

/-- Smoothness of the time-`t` slice `y ↦ I.d (t, y)`. -/
theorem contDiff_slice {r₀ : ℝ} (I : AreaPreservingDiskIsotopy r₀) (t : ℝ) :
    ContDiff ℝ ∞ (fun y ↦ I.d (t, y)) :=
  I.contDiff_d.comp (contDiff_const.prodMk contDiff_id)

/-- Smoothness of the inverse time-`t` slice `y ↦ I.dInv (t, y)`. -/
theorem contDiff_sliceInv {r₀ : ℝ} (I : AreaPreservingDiskIsotopy r₀) (t : ℝ) :
    ContDiff ℝ ∞ (fun y ↦ I.dInv (t, y)) :=
  I.contDiff_dInv.comp (contDiff_const.prodMk contDiff_id)

/-- Differentiability of the time-`t` slice at every point `y`. -/
theorem differentiableAt_slice {r₀ : ℝ} (I : AreaPreservingDiskIsotopy r₀) (t : ℝ)
    (y : EuclideanPlane) :
    DifferentiableAt ℝ (fun z ↦ I.d (t, z)) y :=
  (I.contDiff_slice t).differentiable (by simp) y

/-- Differentiability of the inverse time-`t` slice at every point `y`. -/
theorem differentiableAt_sliceInv {r₀ : ℝ} (I : AreaPreservingDiskIsotopy r₀) (t : ℝ)
    (y : EuclideanPlane) :
    DifferentiableAt ℝ (fun z ↦ I.dInv (t, z)) y :=
  (I.contDiff_sliceInv t).differentiable (by simp) y

/-- `I.dInv (t, ·)` also fixes all points outside `Metric.ball 0 r₀`. -/
theorem dInv_eq_self_of_notMem_ball {r₀ : ℝ} (I : AreaPreservingDiskIsotopy r₀) (t : ℝ)
    {y : EuclideanPlane} (hy : y ∉ Metric.ball (0 : EuclideanPlane) r₀) :
    I.dInv (t, y) = y := by
  calc
    I.dInv (t, y) = I.dInv (t, I.d (t, y)) := by rw [I.eq_self_of_notMem_ball t y hy]
    _ = y := I.left_inv t y

/-- `I.dInv (0, y) = y` for all `y`. -/
@[simp]
theorem dInv_time_zero {r₀ : ℝ} (I : AreaPreservingDiskIsotopy r₀) (y : EuclideanPlane) :
    I.dInv (0, y) = y := by
  calc
    I.dInv (0, y) = I.dInv (0, I.d (0, y)) := by rw [I.time_zero y]
    _ = y := I.left_inv 0 y

/-- Time-`t` slice packaged as a $C^\infty$ `Diffeomorph` of `EuclideanPlane`. -/
noncomputable def sliceDiffeomorph {r₀ : ℝ} (I : AreaPreservingDiskIsotopy r₀) (t : ℝ) :
    EuclideanPlane ≃ₘ⟮𝓡 2, 𝓡 2⟯ EuclideanPlane where
  toFun y := I.d (t, y)
  invFun y := I.dInv (t, y)
  left_inv := I.left_inv t
  right_inv := I.right_inv t
  contMDiff_toFun := (I.contDiff_slice t).contMDiff
  contMDiff_invFun := (I.contDiff_sliceInv t).contMDiff

@[simp]
theorem sliceDiffeomorph_apply {r₀ : ℝ} (I : AreaPreservingDiskIsotopy r₀) (t : ℝ)
    (y : EuclideanPlane) :
    I.sliceDiffeomorph t y = I.d (t, y) :=
  rfl

@[simp]
theorem sliceDiffeomorph_symm_apply {r₀ : ℝ} (I : AreaPreservingDiskIsotopy r₀) (t : ℝ)
    (y : EuclideanPlane) :
    (I.sliceDiffeomorph t).symm y = I.dInv (t, y) :=
  rfl

/-- Every slice `y ↦ I.d (t, y)` preserves `planeAreaForm` under smooth pullback. -/
theorem mpullback_planeAreaForm_eq {r₀ : ℝ} (I : AreaPreservingDiskIsotopy r₀) (t : ℝ) :
    TauCeti.SmoothForm.mpullback (fun y ↦ I.d (t, y)) (I.contDiff_slice t).contMDiff
        planeAreaForm = planeAreaForm :=
  (mpullback_planeAreaForm_eq_iff_det_fderiv_eq_one (I.contDiff_slice t)).mpr
    (I.det_fderiv_eq_one t)

/-- Every slice `I.d (t, ·)` maps `UnitDisk2` into `UnitDisk2`. -/
theorem mem_unitDisk2 {r₀ : ℝ} (I : AreaPreservingDiskIsotopy r₀) (t : ℝ)
    {y : EuclideanPlane} (hy : y ∈ UnitDisk2) :
    I.d (t, y) ∈ UnitDisk2 :=
  mem_unitDisk2_of_leftInverse_of_eq_self (f := fun z ↦ I.d (t, z))
    (g := fun z ↦ I.dInv (t, z)) I.r₀_lt_one (I.left_inv t) (I.eq_self_of_notMem_ball t) hy

/-- Restriction of the time-`1` slice `y ↦ I.d (1, y)` to `UnitDisk2`. -/
noncomputable def diskTimeOneMap {r₀ : ℝ} (I : AreaPreservingDiskIsotopy r₀)
    (y : UnitDisk2) : UnitDisk2 :=
  ⟨I.d (1, y.1), I.mem_unitDisk2 1 y.2⟩

@[simp]
theorem coe_diskTimeOneMap {r₀ : ℝ} (I : AreaPreservingDiskIsotopy r₀) (y : UnitDisk2) :
    (I.diskTimeOneMap y).1 = I.d (1, y.1) :=
  rfl

/-- Promote an `AreaPreservingDiskIsotopy` whose `diskTimeOneMap` is Turing complete to an
instance-ready `HasTuringCompleteAreaPreservingDiskIsotopy`. -/
@[instance_reducible]
def toHasTuringComplete {r₀ : ℝ} (I : AreaPreservingDiskIsotopy r₀)
    (htc : IsTuringComplete I.diskTimeOneMap) :
    HasTuringCompleteAreaPreservingDiskIsotopy where
  d := I.d
  dInv := I.dInv
  r₀ := r₀
  r₀_mem_Ioo := I.r₀_mem_Ioo
  contDiff_d := I.contDiff_d
  contDiff_dInv := I.contDiff_dInv
  left_inv := I.left_inv
  right_inv := I.right_inv
  eq_self_of_notMem_ball := I.eq_self_of_notMem_ball
  time_zero := I.time_zero
  det_fderiv_eq_one := I.det_fderiv_eq_one
  isTuringComplete_timeOne := htc

end Basic

/-! ### Groupoid Operations (`refl`, `symm`, `mono`, `comp`, `compSame`, `listComp`) -/

/-- Identity `AreaPreservingDiskIsotopy` at support radius `r₀ ∈ (0, 1)`. -/
def refl {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1) : AreaPreservingDiskIsotopy r₀ where
  r₀_mem_Ioo := hr₀
  d p := p.2
  dInv p := p.2
  contDiff_d := contDiff_snd
  contDiff_dInv := contDiff_snd
  left_inv _ _ := rfl
  right_inv _ _ := rfl
  eq_self_of_notMem_ball _ _ _ := rfl
  time_zero _ := rfl
  det_fderiv_eq_one _ y := by
    rw [fderiv_fun_id]
    exact LinearMap.det_id

@[simp]
theorem refl_diskTimeOneMap {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1) :
    (refl hr₀).diskTimeOneMap = id := by
  funext y
  exact Subtype.ext rfl

/-- Pointwise time-slice inverse `(t, y) ↦ I.dInv (t, y)` of an `AreaPreservingDiskIsotopy`. -/
def symm {r₀ : ℝ} (I : AreaPreservingDiskIsotopy r₀) : AreaPreservingDiskIsotopy r₀ where
  r₀_mem_Ioo := I.r₀_mem_Ioo
  d := I.dInv
  dInv := I.d
  contDiff_d := I.contDiff_dInv
  contDiff_dInv := I.contDiff_d
  left_inv := I.right_inv
  right_inv := I.left_inv
  eq_self_of_notMem_ball t _ hy := I.dInv_eq_self_of_notMem_ball t hy
  time_zero := I.dInv_time_zero
  det_fderiv_eq_one t y := by
    let f : EuclideanPlane → EuclideanPlane := fun z ↦ I.d (t, z)
    let g : EuclideanPlane → EuclideanPlane := fun z ↦ I.dInv (t, z)
    have hfg : f ∘ g = id := funext (I.right_inv t)
    have hcomp : (fderiv ℝ f (g y)).comp (fderiv ℝ g y) =
        ContinuousLinearMap.id ℝ EuclideanPlane := by
      rw [← fderiv_comp y (I.differentiableAt_slice t (g y)) (I.differentiableAt_sliceInv t y),
        hfg, fderiv_id]
    have hdet := congrArg (fun L : EuclideanPlane →L[ℝ] EuclideanPlane ↦
      LinearMap.det L.toLinearMap) hcomp
    change LinearMap.det ((fderiv ℝ f (g y)).toLinearMap.comp (fderiv ℝ g y).toLinearMap) =
      LinearMap.det (LinearMap.id : EuclideanPlane →ₗ[ℝ] EuclideanPlane) at hdet
    rw [LinearMap.det_comp, I.det_fderiv_eq_one t (g y), one_mul, LinearMap.det_id] at hdet
    exact hdet

/-- Enlarge the compact-support radius from `r₁` to `r₂` (`r₁ ≤ r₂ < 1`). -/
def mono {r₁ r₂ : ℝ} (I : AreaPreservingDiskIsotopy r₁) (hr : r₁ ≤ r₂) (hr₂ : r₂ < 1) :
    AreaPreservingDiskIsotopy r₂ where
  r₀_mem_Ioo := ⟨lt_of_lt_of_le I.r₀_pos hr, hr₂⟩
  d := I.d
  dInv := I.dInv
  contDiff_d := I.contDiff_d
  contDiff_dInv := I.contDiff_dInv
  left_inv := I.left_inv
  right_inv := I.right_inv
  eq_self_of_notMem_ball t y hy :=
    I.eq_self_of_notMem_ball t y fun hmem ↦ hy (Metric.ball_subset_ball hr hmem)
  time_zero := I.time_zero
  det_fderiv_eq_one := I.det_fderiv_eq_one

/-- Pointwise isotopy composition `(t, y) ↦ I₂.d (t, I₁.d (t, y))` with support inside
`Metric.ball 0 (max r₁ r₂)`. -/
def comp {r₁ r₂ : ℝ} (I₂ : AreaPreservingDiskIsotopy r₂) (I₁ : AreaPreservingDiskIsotopy r₁) :
    AreaPreservingDiskIsotopy (max r₁ r₂) where
  r₀_mem_Ioo := ⟨lt_of_lt_of_le I₁.r₀_pos (le_max_left r₁ r₂), max_lt I₁.r₀_lt_one I₂.r₀_lt_one⟩
  d p := I₂.d (p.1, I₁.d p)
  dInv p := I₁.dInv (p.1, I₂.dInv p)
  contDiff_d := I₂.contDiff_d.comp (contDiff_fst.prodMk I₁.contDiff_d)
  contDiff_dInv := I₁.contDiff_dInv.comp (contDiff_fst.prodMk I₂.contDiff_dInv)
  left_inv t y := by
    dsimp only
    rw [I₂.left_inv t (I₁.d (t, y)), I₁.left_inv t y]
  right_inv t y := by
    dsimp only
    rw [I₁.right_inv t (I₂.dInv (t, y)), I₂.right_inv t y]
  eq_self_of_notMem_ball t y hy := by
    have hy₁ : y ∉ Metric.ball (0 : EuclideanPlane) r₁ :=
      fun h ↦ hy (Metric.ball_subset_ball (le_max_left r₁ r₂) h)
    have hy₂ : y ∉ Metric.ball (0 : EuclideanPlane) r₂ :=
      fun h ↦ hy (Metric.ball_subset_ball (le_max_right r₁ r₂) h)
    dsimp only
    rw [I₁.eq_self_of_notMem_ball t y hy₁, I₂.eq_self_of_notMem_ball t y hy₂]
  time_zero y := by
    dsimp only
    rw [I₁.time_zero y, I₂.time_zero y]
  det_fderiv_eq_one t y := by
    let f₂ : EuclideanPlane → EuclideanPlane := fun z ↦ I₂.d (t, z)
    let f₁ : EuclideanPlane → EuclideanPlane := fun z ↦ I₁.d (t, z)
    change LinearMap.det (fderiv ℝ (f₂ ∘ f₁) y).toLinearMap = 1
    rw [fderiv_comp y (I₂.differentiableAt_slice t (f₁ y)) (I₁.differentiableAt_slice t y)]
    change LinearMap.det ((fderiv ℝ f₂ (f₁ y)).toLinearMap.comp (fderiv ℝ f₁ y).toLinearMap) = 1
    rw [LinearMap.det_comp, I₂.det_fderiv_eq_one t (f₁ y), I₁.det_fderiv_eq_one t y, mul_one]

/-- Fixed-radius composition `(t, y) ↦ I₂.d (t, I₁.d (t, y))` of two isotopies at radius `r₀`. -/
def compSame {r₀ : ℝ} (I₂ I₁ : AreaPreservingDiskIsotopy r₀) : AreaPreservingDiskIsotopy r₀ :=
  (I₂.comp I₁).mono (max_self r₀).le I₁.r₀_lt_one

@[simp]
theorem compSame_d {r₀ : ℝ} (I₂ I₁ : AreaPreservingDiskIsotopy r₀) (t : ℝ) (y : EuclideanPlane) :
    (I₂.compSame I₁).d (t, y) = I₂.d (t, I₁.d (t, y)) :=
  rfl

@[simp]
theorem compSame_diskTimeOneMap {r₀ : ℝ} (I₂ I₁ : AreaPreservingDiskIsotopy r₀) :
    (I₂.compSame I₁).diskTimeOneMap = I₂.diskTimeOneMap ∘ I₁.diskTimeOneMap := by
  funext y
  exact Subtype.ext rfl

/-- Finite right-fold composition of a list of `AreaPreservingDiskIsotopy r₀`s. -/
def listComp {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1) :
    List (AreaPreservingDiskIsotopy r₀) → AreaPreservingDiskIsotopy r₀
  | [] => refl hr₀
  | I :: Is => I.compSame (listComp hr₀ Is)

@[simp]
theorem listComp_nil {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1) :
    listComp hr₀ [] = refl hr₀ :=
  rfl

@[simp]
theorem listComp_cons {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    (I : AreaPreservingDiskIsotopy r₀) (Is : List (AreaPreservingDiskIsotopy r₀)) :
    listComp hr₀ (I :: Is) = I.compSame (listComp hr₀ Is) :=
  rfl

@[simp]
theorem listComp_diskTimeOneMap {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ Is : List (AreaPreservingDiskIsotopy r₀),
      (listComp hr₀ Is).diskTimeOneMap =
        Is.foldr (fun I acc ↦ I.diskTimeOneMap ∘ acc) id
  | [] => refl_diskTimeOneMap hr₀
  | I :: Is => by
    rw [listComp_cons, compSame_diskTimeOneMap, listComp_diskTimeOneMap hr₀ Is]
    rfl

end AreaPreservingDiskIsotopy

/-! ## 2. Unconditional `TauCeti` Time-Dependent Hamiltonian Disk-Isotopy Engine -/

section HamiltonianEngine

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

private theorem isSymplectic_planeAreaForm_aux :
    TauCeti.SmoothTwoForm.IsSymplectic planeAreaForm :=
  (TauCeti.SmoothTwoForm.isSymplectic_iff_forall_ne_zero_of_finrank_eq_two
    finrank_euclideanSpace_fin).mpr planeAreaForm_ne_zero

/-- A jointly $C^\infty$ time-dependent planar Hamiltonian `H : ℝ × EuclideanPlane → ℝ` supported
inside `Metric.ball 0 r₀` (`r₀ ∈ (0, 1)`). -/
structure CompactlySupportedPlanarHamiltonian (r₀ : ℝ) where
  /-- `0 < r₀` and `r₀ < 1`. -/
  r₀_mem_Ioo : r₀ ∈ Set.Ioo (0 : ℝ) 1
  /-- Time-dependent Hamiltonian function `(t, y) ↦ H(t, y)`. -/
  H : ℝ × EuclideanPlane → ℝ
  /-- Joint $C^\infty$ smoothness of `H` on `ℝ × ℝ²`. -/
  contDiff_H : ContDiff ℝ ∞ H
  /-- `H (t, ·)` vanishes outside `Metric.ball 0 r₀` at every time `t`. -/
  eq_zero_of_notMem_ball :
    ∀ (t : ℝ) (y : EuclideanPlane), y ∉ Metric.ball (0 : EuclideanPlane) r₀ → H (t, y) = 0

namespace CompactlySupportedPlanarHamiltonian

/-- Construct a `CompactlySupportedPlanarHamiltonian` from a time-independent $C^\infty$ function
`h : EuclideanPlane → ℝ` vanishing outside `Metric.ball 0 r₀`. -/
def ofAutonomous {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1) (h : EuclideanPlane → ℝ)
    (hh : ContDiff ℝ ∞ h)
    (hsupp : ∀ y : EuclideanPlane, y ∉ Metric.ball (0 : EuclideanPlane) r₀ → h y = 0) :
    CompactlySupportedPlanarHamiltonian r₀ where
  r₀_mem_Ioo := hr₀
  H p := h p.2
  contDiff_H := hh.comp contDiff_snd
  eq_zero_of_notMem_ball _ y hy := hsupp y hy

/-- Curried time-`t` Hamiltonian function `y ↦ P.H (t, y)`. -/
def slice {r₀ : ℝ} (P : CompactlySupportedPlanarHamiltonian r₀) (t : ℝ)
    (y : EuclideanPlane) : ℝ :=
  P.H (t, y)

theorem contDiff_slice {r₀ : ℝ} (P : CompactlySupportedPlanarHamiltonian r₀) (t : ℝ) :
    ContDiff ℝ ∞ (P.slice t) :=
  P.contDiff_H.comp (contDiff_const.prodMk contDiff_id)

/-- Time-dependent Hamiltonian vector field `X_t(y) = X_{P.slice t}(y)` on `EuclideanPlane` with
respect to `planeAreaForm`. -/
noncomputable def vectorField {r₀ : ℝ} (P : CompactlySupportedPlanarHamiltonian r₀)
    (t : ℝ) (y : EuclideanPlane) : TangentSpace (𝓡 2) y :=
  TauCeti.SmoothTwoForm.hamiltonianVectorField planeAreaForm (P.slice t) y

/-- Joint $C^\infty$ regularity of `P.vectorField` as a bundle map `ℝ × ℝ² → T ℝ²`. -/
theorem contMDiff_vectorField {r₀ : ℝ} (P : CompactlySupportedPlanarHamiltonian r₀) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2).tangent ∞
      (fun q : ℝ × EuclideanPlane ↦
        (⟨q.2, P.vectorField q.1 q.2⟩ : TangentBundle (𝓡 2) EuclideanPlane)) := by
  have hH_prod : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ) (∞ + 1) (Function.uncurry P.slice) := by
    have hH_top : ContMDiff 𝓘(ℝ, ℝ × EuclideanPlane) 𝓘(ℝ) ∞ P.H := P.contDiff_H.contMDiff
    have heq : (∞ + 1 : WithTop ℕ∞) = ∞ := rfl
    rw [heq]
    exact hH_top.comp (contMDiff_fst.prodMk_space contMDiff_snd)
  exact isSymplectic_planeAreaForm_aux.isNondegenerate.contMDiff_hamiltonianVectorField_uncurry
    le_rfl hH_prod

/-- `P.vectorField t` vanishes strictly outside `Metric.closedBall 0 r₀`. -/
theorem vectorField_eq_zero_of_notMem_closedBall {r₀ : ℝ}
    (P : CompactlySupportedPlanarHamiltonian r₀) (t : ℝ) {y : EuclideanPlane}
    (hy : y ∉ Metric.closedBall (0 : EuclideanPlane) r₀) :
    P.vectorField t y = 0 := by
  have hopen : (Metric.closedBall (0 : EuclideanPlane) r₀)ᶜ ∈ 𝓝 y :=
    Metric.isClosed_closedBall.isOpen_compl.mem_nhds hy
  have hev : P.slice t =ᶠ[𝓝 y] fun _ ↦ (0 : ℝ) := by
    filter_upwards [hopen] with z hz
    exact P.eq_zero_of_notMem_ball t z fun hball ↦ hz (Metric.ball_subset_closedBall hball)
  exact TauCeti.SmoothTwoForm.hamiltonianVectorField_eq_zero_of_eventuallyEq hev

/-- By continuity along outward rays `n ↦ (1 + 1/(n+1)) • y`, `P.vectorField t` vanishes at every
point outside `Metric.ball 0 r₀` (including the boundary sphere `‖y‖ = r₀`). -/
theorem vectorField_eq_zero_of_notMem_ball {r₀ : ℝ} (P : CompactlySupportedPlanarHamiltonian r₀)
    (t : ℝ) {y : EuclideanPlane} (hy : y ∉ Metric.ball (0 : EuclideanPlane) r₀) :
    P.vectorField t y = 0 := by
  have hr₀ : 0 < r₀ := P.r₀_mem_Ioo.1
  have hnorm : r₀ ≤ ‖y‖ := by
    simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hy
  have hhy0 : 0 < ‖y‖ := lt_of_lt_of_le hr₀ hnorm
  have hsec : ContMDiff (𝓡 2) (𝓡 2).tangent ∞
      (fun z : EuclideanPlane ↦ (⟨z, P.vectorField t z⟩ : TangentBundle (𝓡 2) EuclideanPlane)) :=
    P.contMDiff_vectorField.comp (contMDiff_const.prodMk contMDiff_id)
  let V : EuclideanPlane → EuclideanPlane := fun z ↦ P.vectorField t z
  have hV : ContDiff ℝ ∞ V := contMDiff_vectorSpace_iff_contDiff.mp hsec
  let ray : ℕ → EuclideanPlane := fun n ↦ (1 + 1 / ((n : ℝ) + 1)) • y
  have hray_tendsto : Tendsto ray atTop (𝓝 y) := by
    have h1 : Tendsto (fun n : ℕ ↦ (1 : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [add_zero, one_smul, ray] using h1.smul (tendsto_const_nhds (x := y))
  have hray_zero : ∀ n : ℕ, V (ray n) = 0 := by
    intro n
    have hnot : ray n ∉ Metric.closedBall (0 : EuclideanPlane) r₀ := by
      rw [Metric.mem_closedBall, dist_zero_right, not_le]
      have hpos_inv : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
      have hgt1 : 1 < 1 + 1 / ((n : ℝ) + 1) := by linarith
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      calc
        r₀ ≤ ‖y‖ := hnorm
        _ = 1 * ‖y‖ := (one_mul ‖y‖).symm
        _ < (1 + 1 / ((n : ℝ) + 1)) * ‖y‖ := mul_lt_mul_of_pos_right hgt1 hhy0
    exact P.vectorField_eq_zero_of_notMem_closedBall t hnot
  have htend0 : Tendsto (fun n : ℕ ↦ V (ray n)) atTop (𝓝 (0 : EuclideanPlane)) := by
    simpa only [hray_zero] using (tendsto_const_nhds (x := (0 : EuclideanPlane)))
  change V y = (0 : EuclideanPlane)
  exact tendsto_nhds_unique (hV.continuous.continuousAt.tendsto.comp hray_tendsto) htend0

/-- Completeness of the suspended autonomous vector field `(1, P.vectorField)` on `ℝ × ℝ²`. -/
theorem isComplete_suspension {r₀ : ℝ} (P : CompactlySupportedPlanarHamiltonian r₀) :
    TauCeti.IsCompleteVectorField (TauCeti.timeDependentSuspensionField P.vectorField) :=
  TauCeti.isCompleteVectorField_timeDependentSuspensionField
    (P.contMDiff_vectorField.of_le (by simp))
    (isCompact_closedBall (0 : EuclideanPlane) r₀)
    (fun u _ hy ↦ P.vectorField_eq_zero_of_notMem_closedBall u hy)

/-- Forward flow map `(t, y) ↦ timeDependentFlowOf P.vectorField 0 t y`. -/
noncomputable def flow {r₀ : ℝ} (P : CompactlySupportedPlanarHamiltonian r₀)
    (p : ℝ × EuclideanPlane) : EuclideanPlane :=
  TauCeti.timeDependentFlowOf P.vectorField 0 p.1 p.2

/-- Inverse flow map `(t, y) ↦ timeDependentFlowOf P.vectorField t 0 y`. -/
noncomputable def flowInv {r₀ : ℝ} (P : CompactlySupportedPlanarHamiltonian r₀)
    (p : ℝ × EuclideanPlane) : EuclideanPlane :=
  TauCeti.timeDependentFlowOf P.vectorField p.1 0 p.2

theorem contDiff_flow {r₀ : ℝ} (P : CompactlySupportedPlanarHamiltonian r₀) :
    ContDiff ℝ ∞ P.flow := by
  have hflow := TauCeti.contMDiff_timeDependentFlowOf P.isComplete_suspension (n := (⊤ : ℕ∞))
    le_top P.contMDiff_vectorField
  have harg : ContMDiff 𝓘(ℝ, ℝ × EuclideanPlane) ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 2)) ∞
      (fun q : ℝ × EuclideanPlane ↦ (((0 : ℝ), q.1), q.2)) :=
    ((contMDiff_const (c := (0 : ℝ))).prodMk contDiff_fst.contMDiff).prodMk contDiff_snd.contMDiff
  exact contMDiff_iff_contDiff.mp (hflow.comp harg)

theorem contDiff_flowInv {r₀ : ℝ} (P : CompactlySupportedPlanarHamiltonian r₀) :
    ContDiff ℝ ∞ P.flowInv := by
  have hflow := TauCeti.contMDiff_timeDependentFlowOf P.isComplete_suspension (n := (⊤ : ℕ∞))
    le_top P.contMDiff_vectorField
  have harg : ContMDiff 𝓘(ℝ, ℝ × EuclideanPlane) ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 2)) ∞
      (fun q : ℝ × EuclideanPlane ↦ ((q.1, (0 : ℝ)), q.2)) :=
    (contDiff_fst.contMDiff.prodMk (contMDiff_const (c := (0 : ℝ)))).prodMk contDiff_snd.contMDiff
  exact contMDiff_iff_contDiff.mp (hflow.comp harg)

/-- Every slice `y ↦ P.flow (t, y)` preserves `planeAreaForm` under pullback. -/
theorem mpullback_flow_planeAreaForm {r₀ : ℝ} (P : CompactlySupportedPlanarHamiltonian r₀)
    (t : ℝ) :
    TauCeti.mpullback (𝓡 2) (𝓡 2) (fun y ↦ P.flow (t, y)) planeAreaForm.1 = planeAreaForm.1 := by
  have hX2 : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2).tangent 2
      (fun p : ℝ × EuclideanPlane ↦
        (⟨p.2, P.vectorField p.1 p.2⟩ : TangentBundle (𝓡 2) EuclideanPlane)) :=
    P.contMDiff_vectorField.of_le (by simp)
  have hβ : MDifferentiable (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, EuclideanPlane [⋀^Fin 2]→L[ℝ] ℝ))
      (fun z ↦ TotalSpace.mk' (EuclideanPlane [⋀^Fin 2]→L[ℝ] ℝ) z (planeAreaForm.1 z)) := by
    simpa using planeAreaForm.toContMDiffSection.contMDiff.mdifferentiable (by simp)
  have hdβ : TauCeti.mextDeriv planeAreaForm.1 = 0 :=
    (TauCeti.SmoothForm.isClosed_def planeAreaForm).mp isSymplectic_planeAreaForm_aux.isClosed
  have hXβ : ∀ u : ℝ,
      TauCeti.mextDeriv (TauCeti.RoughForm.interior (P.vectorField u) planeAreaForm.1) = 0 := by
    intro u
    have hnd := isSymplectic_planeAreaForm_aux.isNondegenerate
    have hint : TauCeti.RoughForm.interior (P.vectorField u) planeAreaForm.1 =
        TauCeti.mextDeriv (TauCeti.RoughForm.ofFunction (𝓡 2) (P.slice u)) :=
      TauCeti.SmoothTwoForm.isHamiltonianVectorField_iff_interior_eq.mp
        (hnd.isHamiltonianVectorField_hamiltonianVectorField (P.slice u))
    rw [hint]
    exact TauCeti.mextDeriv_mextDeriv_ofFunction
      ((P.contDiff_slice u).contMDiff.of_le (by simp))
  exact TauCeti.mpullback_timeDependentFlowOf_of_mextDeriv_interior_eq_zero
    P.isComplete_suspension hX2 hβ hdβ hXβ 0 t

/-- **Unconditional `TauCeti` Hamiltonian Disk-Isotopy Engine**:
Every `CompactlySupportedPlanarHamiltonian r₀` integrates unconditionally to an
`AreaPreservingDiskIsotopy r₀`. -/
noncomputable def toDiskIsotopy {r₀ : ℝ} (P : CompactlySupportedPlanarHamiltonian r₀) :
    AreaPreservingDiskIsotopy r₀ where
  r₀_mem_Ioo := P.r₀_mem_Ioo
  d := P.flow
  dInv := P.flowInv
  contDiff_d := P.contDiff_flow
  contDiff_dInv := P.contDiff_flowInv
  left_inv t y := by
    dsimp only [flow, flowInv]
    rw [TauCeti.timeDependentFlowOf_trans P.isComplete_suspension
      (P.contMDiff_vectorField.of_le (by simp)), TauCeti.timeDependentFlowOf_self]
  right_inv t y := by
    dsimp only [flow, flowInv]
    rw [TauCeti.timeDependentFlowOf_trans P.isComplete_suspension
      (P.contMDiff_vectorField.of_le (by simp)), TauCeti.timeDependentFlowOf_self]
  eq_self_of_notMem_ball t y hy :=
    TauCeti.timeDependentFlowOf_eq_self_of_forall_eq_zero
      (P.contMDiff_vectorField.of_le (by simp))
      (fun u ↦ P.vectorField_eq_zero_of_notMem_ball u hy) 0 t
  time_zero y := TauCeti.timeDependentFlowOf_self P.vectorField 0 y
  det_fderiv_eq_one t := by
    have hslice : ContDiff ℝ ∞ (fun z ↦ P.flow (t, z)) :=
      P.contDiff_flow.comp (contDiff_const.prodMk contDiff_id)
    refine (mpullback_planeAreaForm_eq_iff_det_fderiv_eq_one hslice).mp ?_
    exact Subtype.ext ((TauCeti.SmoothForm.coe_mpullback (fun z ↦ P.flow (t, z))
      hslice.contMDiff planeAreaForm).trans (P.mpullback_flow_planeAreaForm t))

@[simp]
theorem toDiskIsotopy_d {r₀ : ℝ} (P : CompactlySupportedPlanarHamiltonian r₀)
    (t : ℝ) (y : EuclideanPlane) :
    P.toDiskIsotopy.d (t, y) = TauCeti.timeDependentFlowOf P.vectorField 0 t y :=
  rfl

/-- Compose the disk isotopies generated by a finite list of
`CompactlySupportedPlanarHamiltonian r₀`s. -/
noncomputable def listToDiskIsotopy {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    (Ps : List (CompactlySupportedPlanarHamiltonian r₀)) :
    AreaPreservingDiskIsotopy r₀ :=
  AreaPreservingDiskIsotopy.listComp hr₀ (Ps.map (·.toDiskIsotopy))

@[simp]
theorem listToDiskIsotopy_nil {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1) :
    listToDiskIsotopy hr₀ [] = AreaPreservingDiskIsotopy.refl hr₀ :=
  rfl

@[simp]
theorem listToDiskIsotopy_cons {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    (P : CompactlySupportedPlanarHamiltonian r₀)
    (Ps : List (CompactlySupportedPlanarHamiltonian r₀)) :
    listToDiskIsotopy hr₀ (P :: Ps) =
      P.toDiskIsotopy.compSame (listToDiskIsotopy hr₀ Ps) :=
  rfl

end CompactlySupportedPlanarHamiltonian

/-! ## 3. Concrete `CMPP21` Elementary Moves (Figures 1 & 2) -/

/-- Continuous linear coordinate projection `y ↦ y i` on `EuclideanPlane`. -/
noncomputable def planeCoordCLM (i : Fin 2) : EuclideanPlane →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).toContinuousLinearMap

@[simp]
theorem planeCoordCLM_apply (i : Fin 2) (y : EuclideanPlane) :
    planeCoordCLM i y = y i :=
  rfl

/-- Standard orthonormal basis vector `e₀ = ![1, 0]` of `EuclideanPlane`. -/
noncomputable def planeBasis0 : EuclideanPlane :=
  EuclideanSpace.basisFun (Fin 2) ℝ 0

/-- Standard orthonormal basis vector `e₁ = ![0, 1]` of `EuclideanPlane`. -/
noncomputable def planeBasis1 : EuclideanPlane :=
  EuclideanSpace.basisFun (Fin 2) ℝ 1

@[simp]
theorem planeBasis0_apply_zero : planeBasis0 0 = 1 := by
  simp [planeBasis0]

@[simp]
theorem planeBasis0_apply_one : planeBasis0 1 = 0 := by
  simp [planeBasis0]

@[simp]
theorem planeBasis1_apply_zero : planeBasis1 0 = 0 := by
  simp [planeBasis1]

@[simp]
theorem planeBasis1_apply_one : planeBasis1 1 = 1 := by
  simp [planeBasis1]

theorem euclideanPlane_eq_basis_sum (w : EuclideanPlane) :
    w = w 0 • planeBasis0 + w 1 • planeBasis1 := by
  ext i
  fin_cases i <;> simp

theorem toLp_two_eq_basis_sum (a b : ℝ) :
    (WithLp.toLp 2 ![a, b] : EuclideanPlane) = a • planeBasis0 + b • planeBasis1 := by
  ext i
  fin_cases i <;> simp

/-- Explicit symplectic determinant formula `u₀ v₁ - u₁ v₀` for `planeAreaForm.eval₂`. -/
theorem planeAreaForm_eval₂_eq (x u v : EuclideanPlane) :
    TauCeti.SmoothBundleForm.eval₂ planeAreaForm x
        (u : TangentSpace (𝓡 2) x) (v : TangentSpace (𝓡 2) x) =
      u 0 * v 1 - u 1 * v 0 := by
  let e₀ : TangentSpace (𝓡 2) x := planeBasis0
  let e₁ : TangentSpace (𝓡 2) x := planeBasis1
  have hu : (u : TangentSpace (𝓡 2) x) = u 0 • e₀ + u 1 • e₁ :=
    euclideanPlane_eq_basis_sum u
  have hv : (v : TangentSpace (𝓡 2) x) = v 0 • e₀ + v 1 • e₁ :=
    euclideanPlane_eq_basis_sum v
  have h01 : TauCeti.SmoothBundleForm.eval₂ planeAreaForm x e₀ e₁ = 1 := by
    rw [TauCeti.SmoothBundleForm.eval₂_apply]
    have hfun : (![e₀, e₁] : Fin 2 → TangentSpace (𝓡 2) x) =
        fun i ↦ (EuclideanSpace.basisFun (Fin 2) ℝ i : TangentSpace (𝓡 2) x) := by
      funext i
      fin_cases i <;> rfl
    rw [hfun]
    exact planeAreaForm_apply_basisFun x
  have h10 : TauCeti.SmoothBundleForm.eval₂ planeAreaForm x e₁ e₀ = -1 := by
    rw [TauCeti.SmoothBundleForm.eval₂_swap, h01]
  conv_lhs => rw [hu, hv]
  rw [TauCeti.SmoothBundleForm.eval₂_add_left,
    TauCeti.SmoothBundleForm.eval₂_add_right,
    TauCeti.SmoothBundleForm.eval₂_add_right,
    TauCeti.SmoothBundleForm.eval₂_smul_left,
    TauCeti.SmoothBundleForm.eval₂_smul_left,
    TauCeti.SmoothBundleForm.eval₂_smul_left,
    TauCeti.SmoothBundleForm.eval₂_smul_left,
    TauCeti.SmoothBundleForm.eval₂_smul_right,
    TauCeti.SmoothBundleForm.eval₂_smul_right,
    TauCeti.SmoothBundleForm.eval₂_smul_right,
    TauCeti.SmoothBundleForm.eval₂_smul_right,
    TauCeti.SmoothBundleForm.eval₂_self,
    TauCeti.SmoothBundleForm.eval₂_self,
    h01, h10]
  simp only [smul_eq_mul]
  ring

/-- Pointwise coordinate formula for `planeAreaForm.hamiltonianVectorField` from `HasFDerivAt`:
if `u₀ v₁ - u₁ v₀ = f' v` for all `v`, then `X_f(x) = u`. -/
theorem hamiltonianVectorField_planeAreaForm_eq_of_hasFDerivAt
    {f : EuclideanPlane → ℝ} {f' : EuclideanPlane →L[ℝ] ℝ} {x : EuclideanPlane}
    (hf : HasFDerivAt f f' x) (u : EuclideanPlane)
    (hu : ∀ v : EuclideanPlane, u 0 * v 1 - u 1 * v 0 = f' v) :
    TauCeti.SmoothTwoForm.hamiltonianVectorField planeAreaForm f x =
      (u : TangentSpace (𝓡 2) x) := by
  have hnd := isSymplectic_planeAreaForm_aux.isNondegenerate
  let uT : TangentSpace (𝓡 2) x := u
  change TauCeti.SmoothTwoForm.hamiltonianVectorField planeAreaForm f x = uT
  refine ((hnd.isInvertible_flat x).injective ?_).symm
  rw [hnd.flat_hamiltonianVectorField f x]
  ext v
  let vE : EuclideanPlane := v
  change TauCeti.SmoothTwoForm.flat planeAreaForm x uT (vE : TangentSpace (𝓡 2) x) =
    mvfderiv (𝓡 2) f x v
  rw [TauCeti.SmoothTwoForm.flat_apply, planeAreaForm_eval₂_eq x u vE, hu vE,
    TauCeti.mvfderiv_eq_fderiv_apply, hf.fderiv]

/-! ### B.1 Planar Rotations & Bumped Core Rotation (`bumpedRotationIsotopy`, Figure 1 `ρ`) -/

/-- Counterclockwise rotation by angle `α : ℝ` on `EuclideanPlane`. -/
noncomputable def planeRotate (α : ℝ) (v : EuclideanPlane) : EuclideanPlane :=
  WithLp.toLp 2 ![Real.cos α * v 0 - Real.sin α * v 1, Real.sin α * v 0 + Real.cos α * v 1]

@[simp]
theorem planeRotate_zero (v : EuclideanPlane) : planeRotate 0 v = v := by
  ext i
  fin_cases i <;> simp [planeRotate]

@[simp]
theorem planeRotate_neg_pi (v : EuclideanPlane) : planeRotate (-Real.pi) v = -v := by
  ext i
  fin_cases i <;> simp [planeRotate]

@[simp]
theorem planeRotate_pi (v : EuclideanPlane) : planeRotate Real.pi v = -v := by
  ext i
  fin_cases i <;> simp [planeRotate]

@[simp]
theorem norm_planeRotate (α : ℝ) (v : EuclideanPlane) : ‖planeRotate α v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [planeRotate, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Real.norm_eq_abs, sq_abs]
  congr 1
  calc
    (Real.cos α * v 0 - Real.sin α * v 1) ^ 2 + (Real.sin α * v 0 + Real.cos α * v 1) ^ 2
        = (Real.cos α ^ 2 + Real.sin α ^ 2) * (v 0 ^ 2 + v 1 ^ 2) := by ring
    _ = 1 * (v 0 ^ 2 + v 1 ^ 2) := by rw [Real.cos_sq_add_sin_sq]
    _ = v 0 ^ 2 + v 1 ^ 2 := one_mul _

/-- Quadratic generator `-(θ / 2) * ‖y - c‖²` of uniform angular-velocity `θ` rotation around
`c : EuclideanPlane`. -/
noncomputable def rotQuad (c : EuclideanPlane) (θ : ℝ) (y : EuclideanPlane) : ℝ :=
  -(θ / 2) * ((y 0 - c 0) ^ 2 + (y 1 - c 1) ^ 2)

theorem contDiff_rotQuad (c : EuclideanPlane) (θ : ℝ) : ContDiff ℝ ∞ (rotQuad c θ) := by
  unfold rotQuad
  have hy0 : ContDiff ℝ ∞ (fun y : EuclideanPlane ↦ y 0) := (planeCoordCLM 0).contDiff
  have hy1 : ContDiff ℝ ∞ (fun y : EuclideanPlane ↦ y 1) := (planeCoordCLM 1).contDiff
  exact contDiff_const.mul
    (((hy0.sub contDiff_const).pow 2).add ((hy1.sub contDiff_const).pow 2))

theorem hasFDerivAt_rotQuad (c : EuclideanPlane) (θ : ℝ) (x : EuclideanPlane) :
    HasFDerivAt (rotQuad c θ)
      ((-θ * (x 0 - c 0)) • planeCoordCLM 0 + (-θ * (x 1 - c 1)) • planeCoordCLM 1) x := by
  unfold rotQuad
  have h0 : HasFDerivAt (fun y : EuclideanPlane ↦ y 0 - c 0) (planeCoordCLM 0) x :=
    (planeCoordCLM 0).hasFDerivAt.sub_const (c 0)
  have h1 : HasFDerivAt (fun y : EuclideanPlane ↦ y 1 - c 1) (planeCoordCLM 1) x :=
    (planeCoordCLM 1).hasFDerivAt.sub_const (c 1)
  have hsq : HasFDerivAt (fun y : EuclideanPlane ↦ (y 0 - c 0) ^ 2 + (y 1 - c 1) ^ 2)
      (((2 : ℝ) * (x 0 - c 0)) • planeCoordCLM 0 +
        ((2 : ℝ) * (x 1 - c 1)) • planeCoordCLM 1) x := by
    convert (h0.pow 2).add (h1.pow 2) using 1
    ext v
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  convert hsq.const_mul (-(θ / 2)) using 1
  ext v
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Autonomous bumped rotational Hamiltonian around `c : EuclideanPlane` equal to `rotQuad c θ`
on `Metric.ball c ((r_in + r_out) / 2)` and vanishing outside `Metric.ball c r_out`. -/
noncomputable def bumpedCenterRotationHamiltonian {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    (c : EuclideanPlane) {r_in r_out : ℝ} (hr_in : 0 < r_in) (hr_lt : r_in < r_out)
    (hsub : Metric.ball c r_out ⊆ Metric.ball (0 : EuclideanPlane) r₀) (θ : ℝ) :
    CompactlySupportedPlanarHamiltonian r₀ :=
  let χ : ContDiffBump c := ⟨(r_in + r_out) / 2, r_out, by linarith, by linarith⟩
  CompactlySupportedPlanarHamiltonian.ofAutonomous hr₀
    (fun y ↦ χ y * rotQuad c θ y)
    ((χ.contDiff (n := ⊤)).mul (contDiff_rotQuad c θ))
    (fun y hy ↦ by
      have hnot : y ∉ Metric.ball c r_out := fun h ↦ hy (hsub h)
      have hdist : r_out ≤ dist y c := not_lt.mp (by simpa only [Metric.mem_ball] using hnot)
      rw [χ.zero_of_le_dist hdist, zero_mul])

/-- `AreaPreservingDiskIsotopy` generated by `bumpedCenterRotationHamiltonian`. -/
noncomputable def bumpedCenterRotationIsotopy {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    (c : EuclideanPlane) {r_in r_out : ℝ} (hr_in : 0 < r_in) (hr_lt : r_in < r_out)
    (hsub : Metric.ball c r_out ⊆ Metric.ball (0 : EuclideanPlane) r₀) (θ : ℝ) :
    AreaPreservingDiskIsotopy r₀ :=
  (bumpedCenterRotationHamiltonian hr₀ c hr_in hr_lt hsub θ).toDiskIsotopy

/-- `bumpedCenterRotationIsotopy` fixes every point outside `Metric.ball c r_out`. -/
theorem bumpedCenterRotationIsotopy_eq_self_of_notMem_ball {r₀ : ℝ}
    (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1) (c : EuclideanPlane) {r_in r_out : ℝ} (hr_in : 0 < r_in)
    (hr_lt : r_in < r_out) (hsub : Metric.ball c r_out ⊆ Metric.ball (0 : EuclideanPlane) r₀)
    (θ t : ℝ) {y : EuclideanPlane} (hy : y ∉ Metric.ball c r_out) :
    (bumpedCenterRotationIsotopy hr₀ c hr_in hr_lt hsub θ).d (t, y) = y := by
  let P := bumpedCenterRotationHamiltonian hr₀ c hr_in hr_lt hsub θ
  have hr_out : 0 < r_out := lt_trans hr_in hr_lt
  have hnorm : r_out ≤ ‖y - c‖ := by
    simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hy
  have hpos : 0 < ‖y - c‖ := lt_of_lt_of_le hr_out hnorm
  have hX_zero : ∀ u : ℝ, P.vectorField u y = 0 := by
    intro u
    have hsec : ContMDiff (𝓡 2) (𝓡 2).tangent ∞
        (fun z : EuclideanPlane ↦ (⟨z, P.vectorField u z⟩ : TangentBundle (𝓡 2) EuclideanPlane)) :=
      P.contMDiff_vectorField.comp (contMDiff_const.prodMk contMDiff_id)
    let V : EuclideanPlane → EuclideanPlane := fun z ↦ P.vectorField u z
    have hV : ContDiff ℝ ∞ V := contMDiff_vectorSpace_iff_contDiff.mp hsec
    let ray : ℕ → EuclideanPlane := fun n ↦ c + (1 + 1 / ((n : ℝ) + 1)) • (y - c)
    have hray_tendsto : Tendsto ray atTop (𝓝 y) := by
      have h1 : Tendsto (fun n : ℕ ↦ (1 : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 := (tendsto_const_nhds (x := c)).add (h1.smul (tendsto_const_nhds (x := y - c)))
      simpa only [add_zero, one_smul, add_sub_cancel, ray] using h2
    have hray_zero : ∀ n : ℕ, V (ray n) = 0 := by
      intro n
      have hnot_closed : ray n ∉ Metric.closedBall c r_out := by
        rw [Metric.mem_closedBall, dist_eq_norm, not_le]
        have hsub_ray : ray n - c = (1 + 1 / ((n : ℝ) + 1)) • (y - c) := add_sub_cancel_left _ _
        rw [hsub_ray, norm_smul, Real.norm_of_nonneg (by positivity)]
        have hgt1 : 1 < 1 + 1 / ((n : ℝ) + 1) := by
          have : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
          linarith
        calc
          r_out ≤ ‖y - c‖ := hnorm
          _ = 1 * ‖y - c‖ := (one_mul _).symm
          _ < (1 + 1 / ((n : ℝ) + 1)) * ‖y - c‖ := mul_lt_mul_of_pos_right hgt1 hpos
      have hopen : (Metric.closedBall c r_out)ᶜ ∈ 𝓝 (ray n) :=
        Metric.isClosed_closedBall.isOpen_compl.mem_nhds hnot_closed
      have hev : P.slice u =ᶠ[𝓝 (ray n)] fun _ ↦ (0 : ℝ) := by
        filter_upwards [hopen] with z hz
        have hdist : r_out ≤ dist z c :=
          (by simpa only [Set.mem_compl_iff, Metric.mem_closedBall, not_le] using hz :
            r_out < dist z c).le
        let χ : ContDiffBump c := ⟨(r_in + r_out) / 2, r_out, by linarith, by linarith⟩
        change χ z * rotQuad c θ z = 0
        rw [χ.zero_of_le_dist hdist, zero_mul]
      exact TauCeti.SmoothTwoForm.hamiltonianVectorField_eq_zero_of_eventuallyEq hev
    have htend0 : Tendsto (fun n : ℕ ↦ V (ray n)) atTop (𝓝 (0 : EuclideanPlane)) := by
      simpa only [hray_zero] using (tendsto_const_nhds (x := (0 : EuclideanPlane)))
    change V y = (0 : EuclideanPlane)
    exact tendsto_nhds_unique (hV.continuous.continuousAt.tendsto.comp hray_tendsto) htend0
  exact TauCeti.timeDependentFlowOf_eq_self_of_forall_eq_zero
    (P.contMDiff_vectorField.of_le (by simp)) hX_zero 0 t

/-- **Exact Inner-Core Rotation Formula**:
On `Metric.closedBall c r_in`, `bumpedCenterRotationIsotopy` acts at every time `t : ℝ` by exact
Euclidean rotation `y ↦ c + planeRotate (t * θ) (y - c)`. -/
theorem bumpedCenterRotationIsotopy_apply_of_mem_closedBall {r₀ : ℝ}
    (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1) (c : EuclideanPlane) {r_in r_out : ℝ} (hr_in : 0 < r_in)
    (hr_lt : r_in < r_out) (hsub : Metric.ball c r_out ⊆ Metric.ball (0 : EuclideanPlane) r₀)
    (θ t : ℝ) {y₀ : EuclideanPlane} (hy₀ : y₀ ∈ Metric.closedBall c r_in) :
    (bumpedCenterRotationIsotopy hr₀ c hr_in hr_lt hsub θ).d (t, y₀) =
      c + planeRotate (t * θ) (y₀ - c) := by
  let P := bumpedCenterRotationHamiltonian hr₀ c hr_in hr_lt hsub θ
  let χ : ContDiffBump c := ⟨(r_in + r_out) / 2, r_out, by linarith, by linarith⟩
  let v := y₀ - c
  let γ : ℝ → EuclideanPlane := fun u ↦ c + planeRotate (u * θ) v
  have hγ0 : γ 0 = y₀ := by
    simp [γ, v]
  have hγ_mem : ∀ u : ℝ, γ u ∈ Metric.ball c ((r_in + r_out) / 2) := by
    intro u
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_planeRotate]
    have hy₀_norm : ‖v‖ ≤ r_in := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, v] using hy₀
    linarith
  have hγ_deriv : ∀ u : ℝ,
      HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 2) γ u
        ((1 : ℝ →L[ℝ] ℝ).smulRight (P.vectorField u (γ u))) := by
    intro u
    have hev : P.slice u =ᶠ[𝓝 (γ u)] rotQuad c θ := by
      filter_upwards [χ.eventuallyEq_one_of_mem_ball (hγ_mem u)] with z hz
      change χ z * rotQuad c θ z = rotQuad c θ z
      rw [hz, Pi.one_apply, one_mul]
    let vel : EuclideanPlane :=
      (-θ * (γ u 1 - c 1)) • planeBasis0 + (θ * (γ u 0 - c 0)) • planeBasis1
    have hX_rot : TauCeti.SmoothTwoForm.hamiltonianVectorField planeAreaForm
        (rotQuad c θ) (γ u) = (vel : TangentSpace (𝓡 2) (γ u)) := by
      refine hamiltonianVectorField_planeAreaForm_eq_of_hasFDerivAt
        (hasFDerivAt_rotQuad c θ (γ u)) vel fun w ↦ ?_
      have hv0 : vel 0 = -θ * (γ u 1 - c 1) := by simp [vel]
      have hv1 : vel 1 = θ * (γ u 0 - c 0) := by simp [vel]
      rw [hv0, hv1]
      simp only [add_apply, smul_apply, planeCoordCLM_apply, smul_eq_mul]
      ring
    have hX : P.vectorField u (γ u) = (vel : TangentSpace (𝓡 2) (γ u)) :=
      (hev.hamiltonianVectorField_eq planeAreaForm).trans hX_rot
    rw [hX]
    have hlin : HasDerivAt (fun s : ℝ ↦ s * θ) θ u := by
      simpa only [one_mul] using (hasDerivAt_id' u).mul_const θ
    have hcos : HasDerivAt (fun s : ℝ ↦ Real.cos (s * θ)) (-Real.sin (u * θ) * θ) u := hlin.cos
    have hsin : HasDerivAt (fun s : ℝ ↦ Real.sin (s * θ)) (Real.cos (u * θ) * θ) u := hlin.sin
    have hf0 : HasDerivAt (fun s : ℝ ↦ c 0 + (Real.cos (s * θ) * v 0 - Real.sin (s * θ) * v 1))
        (((-Real.sin (u * θ) * θ) * v 0 - (Real.cos (u * θ) * θ) * v 1)) u :=
      ((hcos.mul_const (v 0)).sub (hsin.mul_const (v 1))).const_add (c 0)
    have hf1 : HasDerivAt (fun s : ℝ ↦ c 1 + (Real.sin (s * θ) * v 0 + Real.cos (s * θ) * v 1))
        (((Real.cos (u * θ) * θ) * v 0 + (-Real.sin (u * θ) * θ) * v 1)) u :=
      ((hsin.mul_const (v 0)).add (hcos.mul_const (v 1))).const_add (c 1)
    have hγ_eq : γ = fun s : ℝ ↦
        (c 0 + (Real.cos (s * θ) * v 0 - Real.sin (s * θ) * v 1)) • planeBasis0 +
        (c 1 + (Real.sin (s * θ) * v 0 + Real.cos (s * θ) * v 1)) • planeBasis1 := by
      funext s
      ext i
      fin_cases i <;> simp [γ, planeRotate]
    have hvel_eq :
        (((-Real.sin (u * θ) * θ) * v 0 - (Real.cos (u * θ) * θ) * v 1)) • planeBasis0 +
        (((Real.cos (u * θ) * θ) * v 0 + (-Real.sin (u * θ) * θ) * v 1)) • planeBasis1 = vel := by
      have hg0 : γ u 0 - c 0 = Real.cos (u * θ) * v 0 - Real.sin (u * θ) * v 1 := by
        simp [γ, planeRotate]
      have hg1 : γ u 1 - c 1 = Real.sin (u * θ) * v 0 + Real.cos (u * θ) * v 1 := by
        simp [γ, planeRotate]
      dsimp only [vel]
      rw [hg0, hg1]
      ext i
      fin_cases i <;> simp <;> ring
    have hd : HasDerivAt γ vel u := by
      rw [hγ_eq, ← hvel_eq]
      exact (hf0.smul_const planeBasis0).add (hf1.smul_const planeBasis1)
    exact hasMFDerivAt_iff_hasFDerivAt.mpr hd.hasFDerivAt
  have hflow := TauCeti.timeDependentFlowOf_eq_of_hasMFDerivAt
    (P.contMDiff_vectorField.of_le (by simp))
    (s := (0 : ℝ)) (t := t) (a := min 0 t - 1) (b := max 0 t + 1)
    (fun u _ ↦ hγ_deriv u)
    ⟨by linarith [min_le_left 0 t], by linarith [le_max_left 0 t]⟩
    ⟨by linarith [min_le_right 0 t], by linarith [le_max_right 0 t]⟩
  simpa only [bumpedCenterRotationIsotopy, CompactlySupportedPlanarHamiltonian.toDiskIsotopy_d,
    hγ0, γ, v] using hflow

/-- **Figure 1 Elementary Move (i) (`ρ` — Bumped Core Clockwise `π`-Rotation Hamiltonian)**:
Supported inside `Metric.ball 0 r₀` (`0 < r_in < r₀ < 1`), generating clockwise `π`-rotation on
`Metric.closedBall 0 r_in`. -/
noncomputable def bumpedRotationHamiltonian {r₀ r_in : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hr_in : r_in ∈ Set.Ioo (0 : ℝ) r₀) : CompactlySupportedPlanarHamiltonian r₀ :=
  bumpedCenterRotationHamiltonian hr₀ 0 hr_in.1 hr_in.2 Subset.rfl (-Real.pi)

/-- **Figure 1 Elementary Move (i) (`ρ` — Bumped Core Clockwise `π`-Rotation Isotopy)**:
`AreaPreservingDiskIsotopy r₀` rotating `Metric.closedBall 0 r_in` by `-π` (`y ↦ -y`) at `t = 1`. -/
noncomputable def bumpedRotationIsotopy {r₀ r_in : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hr_in : r_in ∈ Set.Ioo (0 : ℝ) r₀) : AreaPreservingDiskIsotopy r₀ :=
  (bumpedRotationHamiltonian hr₀ hr_in).toDiskIsotopy

/-- At `t = 1`, `bumpedRotationIsotopy` negates every point in the inner core
`Metric.closedBall 0 r_in`. -/
theorem bumpedRotationIsotopy_timeOne_eq_neg {r₀ r_in : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hr_in : r_in ∈ Set.Ioo (0 : ℝ) r₀) {y : EuclideanPlane}
    (hy : y ∈ Metric.closedBall (0 : EuclideanPlane) r_in) :
    (bumpedRotationIsotopy hr₀ hr_in).d (1, y) = -y := by
  have h := bumpedCenterRotationIsotopy_apply_of_mem_closedBall hr₀ 0 hr_in.1 hr_in.2 Subset.rfl
    (-Real.pi) 1 hy
  simpa only [bumpedRotationIsotopy, bumpedRotationHamiltonian, bumpedCenterRotationIsotopy,
    one_mul, sub_zero, zero_add, planeRotate_neg_pi] using h

/-- Non-vacuity witness: `bumpedRotationIsotopy`'s time-`1` disk diffeomorphism is nontrivial
(`≠ id`). -/
theorem bumpedRotationIsotopy_diskTimeOneMap_ne_id {r₀ r_in : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hr_in : r_in ∈ Set.Ioo (0 : ℝ) r₀) :
    (bumpedRotationIsotopy hr₀ hr_in).diskTimeOneMap ≠ id := by
  intro hid
  let p : EuclideanPlane := (r_in / 2) • planeBasis0
  have hp_norm : ‖p‖ = r_in / 2 := by
    have hpos : 0 < r_in / 2 := by linarith [hr_in.1]
    rw [norm_smul, Real.norm_of_nonneg hpos.le, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp
  have hp_closed : p ∈ Metric.closedBall (0 : EuclideanPlane) r_in := by
    rw [Metric.mem_closedBall, dist_zero_right, hp_norm]
    linarith [hr_in.1]
  have hp_disk : p ∈ UnitDisk2 := by
    rw [UnitDisk2, Metric.mem_ball, dist_zero_right, hp_norm]
    linarith [hr_in.2, hr₀.2]
  have heq := congrArg (fun u : UnitDisk2 ↦ u.1 0) (congrFun hid ⟨p, hp_disk⟩)
  change (bumpedRotationIsotopy hr₀ hr_in).d (1, p) 0 = p 0 at heq
  rw [bumpedRotationIsotopy_timeOne_eq_neg hr₀ hr_in hp_closed] at heq
  have hp0 : p 0 = r_in / 2 := by simp [p]
  have hnp0 : (-p) 0 = -(r_in / 2) := by simp [p]
  rw [hp0, hnp0] at heq
  linarith [hr_in.1]

/-! ### B.2 Disjoint Sub-Disk Sector Swap (`sectorSwapIsotopy`, Figure 1 `σ`) -/

/-- Disjointness of symmetric sub-balls `Metric.closedBall (-a) ρ` and `Metric.closedBall a ρ`
whenever `ρ < ‖a‖`. -/
theorem disjoint_symmetric_closedBalls {a : EuclideanPlane} {ρ : ℝ} (hρ : ρ < ‖a‖) :
    Disjoint (Metric.closedBall (-a) ρ) (Metric.closedBall a ρ) := by
  rw [Set.disjoint_iff]
  rintro y ⟨h1, h2⟩
  have hd1 : dist y (-a) ≤ ρ := Metric.mem_closedBall.mp h1
  have hd2 : dist a y ≤ ρ := by
    rw [dist_comm]
    exact Metric.mem_closedBall.mp h2
  have h2a : dist a (-a) = 2 * ‖a‖ := by
    rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ a, norm_smul, Real.norm_of_nonneg (by norm_num)]
  have htri : dist a (-a) ≤ dist a y + dist y (-a) := dist_triangle a y (-a)
  linarith

/-- Inclusion of symmetric sub-balls `Metric.closedBall (±a) ρ` in `Metric.ball 0 r₀` when
`‖a‖ + ρ < r₀`. -/
theorem symmetric_closedBall_subset_ball {a : EuclideanPlane} {ρ r₀ : ℝ} (hsum : ‖a‖ + ρ < r₀) :
    Metric.closedBall a ρ ⊆ Metric.ball (0 : EuclideanPlane) r₀ ∧
      Metric.closedBall (-a) ρ ⊆ Metric.ball (0 : EuclideanPlane) r₀ := by
  constructor
  · intro y hy
    rw [Metric.mem_ball, dist_zero_right]
    have hya : ‖y - a‖ ≤ ρ := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
    have htri := norm_le_insert' y a
    linarith
  · intro y hy
    rw [Metric.mem_ball, dist_zero_right]
    have hya : ‖y - (-a)‖ ≤ ρ := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
    have htri := norm_le_insert' y (-a)
    rw [norm_neg] at htri
    linarith

/-- **Figure 1 Elementary Move (ii) (`σ` — Disjoint Sub-Disk Exchange Isotopy)**:
Given `a : EuclideanPlane` and `0 < ρ < ‖a‖` with `‖a‖ + ρ < r₀ < 1`, composes three bumped
Hamiltonian rotations (`R_a ∘ R_{-a} ∘ R_0`) via `AreaPreservingDiskIsotopy.compSame` to exchange
the disjoint sub-balls `Metric.closedBall (-a) ρ` and `Metric.closedBall a ρ` inside
`Metric.ball 0 r₀` by pure rigid translation (`y ↦ y ± 2 • a`) at `t = 1`. -/
noncomputable def sectorSwapIsotopy {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    (a : EuclideanPlane) {ρ : ℝ} (hρ_pos : 0 < ρ) (hρ_lt : ρ < ‖a‖) (hsum : ‖a‖ + ρ < r₀) :
    AreaPreservingDiskIsotopy r₀ :=
  let R_in := ‖a‖ + ρ
  let R_out := (‖a‖ + ρ + r₀) / 2
  let ρ_out := min ((‖a‖ + ρ) / 2) ((r₀ - ‖a‖ + ρ) / 2)
  have hR_in_pos : 0 < R_in := by dsimp [R_in]; linarith [norm_nonneg a]
  have hR_lt : R_in < R_out := by dsimp [R_in, R_out]; linarith
  have hR_sub : Metric.ball (0 : EuclideanPlane) R_out ⊆ Metric.ball 0 r₀ :=
    Metric.ball_subset_ball (by dsimp [R_out]; linarith)
  have hρ_lt_out : ρ < ρ_out := lt_min (by linarith) (by linarith)
  have hρ_out_bound : ‖a‖ + ρ_out ≤ r₀ := by
    have hle : ρ_out ≤ (r₀ - ‖a‖ + ρ) / 2 := min_le_right _ _
    linarith
  have hsub_pos : Metric.ball a ρ_out ⊆ Metric.ball (0 : EuclideanPlane) r₀ := by
    intro y hy
    rw [Metric.mem_ball, dist_zero_right]
    have hya : ‖y - a‖ < ρ_out := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
    have htri := norm_le_insert' y a
    linarith
  have hsub_neg : Metric.ball (-a) ρ_out ⊆ Metric.ball (0 : EuclideanPlane) r₀ := by
    intro y hy
    rw [Metric.mem_ball, dist_zero_right]
    have hya : ‖y - (-a)‖ < ρ_out := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
    have htri := norm_le_insert' y (-a)
    rw [norm_neg] at htri
    linarith
  let rot0 := bumpedCenterRotationIsotopy hr₀ 0 hR_in_pos hR_lt hR_sub (-Real.pi)
  let rotNeg := bumpedCenterRotationIsotopy hr₀ (-a) hρ_pos hρ_lt_out hsub_neg (-Real.pi)
  let rotPos := bumpedCenterRotationIsotopy hr₀ a hρ_pos hρ_lt_out hsub_pos (-Real.pi)
  rotPos.compSame (rotNeg.compSame rot0)

/-- At `t = 1`, `sectorSwapIsotopy` translates every `y ∈ Metric.closedBall (-a) ρ` rigidly by
`+ 2 • a` into `Metric.closedBall a ρ`. -/
theorem sectorSwapIsotopy_timeOne_of_mem_neg {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    (a : EuclideanPlane) {ρ : ℝ} (hρ_pos : 0 < ρ) (hρ_lt : ρ < ‖a‖) (hsum : ‖a‖ + ρ < r₀)
    {y : EuclideanPlane} (hy : y ∈ Metric.closedBall (-a) ρ) :
    (sectorSwapIsotopy hr₀ a hρ_pos hρ_lt hsum).d (1, y) = y + (2 : ℝ) • a := by
  let R_in := ‖a‖ + ρ
  let ρ_out := min ((‖a‖ + ρ) / 2) ((r₀ - ‖a‖ + ρ) / 2)
  have hy_norm : ‖y + a‖ ≤ ρ := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_neg_eq_add] using hy
  have hy_R : y ∈ Metric.closedBall (0 : EuclideanPlane) R_in := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have htri := norm_le_insert' y (-a)
    rw [sub_neg_eq_add, norm_neg] at htri
    dsimp [R_in]
    linarith
  have hnegy_pos : -y ∈ Metric.closedBall a ρ := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have heq : -y - a = -(y + a) := by abel
    rw [heq, norm_neg]
    exact hy_norm
  have hnegy_not_neg : -y ∉ Metric.ball (-a) ρ_out := by
    intro hmem
    have h1 : dist (-y) (-a) < ρ_out := Metric.mem_ball.mp hmem
    have h2 : dist a (-y) ≤ ρ := by
      rw [dist_comm]
      exact Metric.mem_closedBall.mp hnegy_pos
    have h2a : dist a (-a) = 2 * ‖a‖ := by
      rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ a, norm_smul,
        Real.norm_of_nonneg (by norm_num)]
    have htri : dist a (-a) ≤ dist a (-y) + dist (-y) (-a) := dist_triangle a (-y) (-a)
    have hle : ρ_out ≤ (‖a‖ + ρ) / 2 := min_le_left _ _
    linarith
  unfold sectorSwapIsotopy
  simp only [AreaPreservingDiskIsotopy.compSame_d]
  rw [bumpedCenterRotationIsotopy_apply_of_mem_closedBall _ _ _ _ _ _ 1 hy_R]
  simp only [one_mul, sub_zero, zero_add, planeRotate_neg_pi]
  rw [bumpedCenterRotationIsotopy_eq_self_of_notMem_ball _ _ _ _ _ _ 1 hnegy_not_neg]
  rw [bumpedCenterRotationIsotopy_apply_of_mem_closedBall _ _ _ _ _ _ 1 hnegy_pos]
  simp only [one_mul, planeRotate_neg_pi]
  ext i
  simp only [PiLp.add_apply, PiLp.neg_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- At `t = 1`, `sectorSwapIsotopy` translates every `y ∈ Metric.closedBall a ρ` rigidly by
`- 2 • a` into `Metric.closedBall (-a) ρ`. -/
theorem sectorSwapIsotopy_timeOne_of_mem_pos {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    (a : EuclideanPlane) {ρ : ℝ} (hρ_pos : 0 < ρ) (hρ_lt : ρ < ‖a‖) (hsum : ‖a‖ + ρ < r₀)
    {y : EuclideanPlane} (hy : y ∈ Metric.closedBall a ρ) :
    (sectorSwapIsotopy hr₀ a hρ_pos hρ_lt hsum).d (1, y) = y - (2 : ℝ) • a := by
  let R_in := ‖a‖ + ρ
  let ρ_out := min ((‖a‖ + ρ) / 2) ((r₀ - ‖a‖ + ρ) / 2)
  have hy_norm : ‖y - a‖ ≤ ρ := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
  have hy_R : y ∈ Metric.closedBall (0 : EuclideanPlane) R_in := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have htri := norm_le_insert' y a
    dsimp [R_in]
    linarith
  have hnegy_neg : -y ∈ Metric.closedBall (-a) ρ := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_neg_eq_add]
    have heq : -y + a = -(y - a) := by abel
    rw [heq, norm_neg]
    exact hy_norm
  have hshifted_neg : y - (2 : ℝ) • a ∈ Metric.closedBall (-a) ρ := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_neg_eq_add]
    have heq : y - (2 : ℝ) • a + a = y - a := by
      ext i
      simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    exact hy_norm
  have hshifted_not_pos : y - (2 : ℝ) • a ∉ Metric.ball a ρ_out := by
    intro hmem
    have h1 : dist (y - (2 : ℝ) • a) a < ρ_out := Metric.mem_ball.mp hmem
    have h2 : dist (y - (2 : ℝ) • a) (-a) ≤ ρ := Metric.mem_closedBall.mp hshifted_neg
    have h2a : dist a (-a) = 2 * ‖a‖ := by
      rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ a, norm_smul,
        Real.norm_of_nonneg (by norm_num)]
    have htri : dist a (-a) ≤ dist a (y - (2 : ℝ) • a) + dist (y - (2 : ℝ) • a) (-a) :=
      dist_triangle a (y - (2 : ℝ) • a) (-a)
    rw [dist_comm a (y - (2 : ℝ) • a)] at htri
    have hle : ρ_out ≤ (‖a‖ + ρ) / 2 := min_le_left _ _
    linarith
  unfold sectorSwapIsotopy
  simp only [AreaPreservingDiskIsotopy.compSame_d]
  rw [bumpedCenterRotationIsotopy_apply_of_mem_closedBall _ _ _ _ _ _ 1 hy_R]
  simp only [one_mul, sub_zero, zero_add, planeRotate_neg_pi]
  rw [bumpedCenterRotationIsotopy_apply_of_mem_closedBall _ _ _ _ _ _ 1 hnegy_neg]
  simp only [one_mul, sub_neg_eq_add, planeRotate_neg_pi]
  have hmid : -a + -(-y + a) = y - (2 : ℝ) • a := by
    ext i
    simp only [PiLp.add_apply, PiLp.neg_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [hmid, bumpedCenterRotationIsotopy_eq_self_of_notMem_ball _ _ _ _ _ _ 1 hshifted_not_pos]

/-- `sectorSwapIsotopy` maps `Metric.closedBall (-a) ρ` onto `Metric.closedBall a ρ` and
`Metric.closedBall a ρ` onto `Metric.closedBall (-a) ρ` at `t = 1`. -/
theorem sectorSwapIsotopy_image_swap {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    (a : EuclideanPlane) {ρ : ℝ} (hρ_pos : 0 < ρ) (hρ_lt : ρ < ‖a‖) (hsum : ‖a‖ + ρ < r₀) :
    (fun y ↦ (sectorSwapIsotopy hr₀ a hρ_pos hρ_lt hsum).d (1, y)) ''
        Metric.closedBall (-a) ρ = Metric.closedBall a ρ ∧
      (fun y ↦ (sectorSwapIsotopy hr₀ a hρ_pos hρ_lt hsum).d (1, y)) ''
        Metric.closedBall a ρ = Metric.closedBall (-a) ρ := by
  have hsub_mem : ∀ {z : EuclideanPlane}, z ∈ Metric.closedBall a ρ →
      z - (2 : ℝ) • a ∈ Metric.closedBall (-a) ρ := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    have heq : z - (2 : ℝ) • a - (-a) = z - a := by
      ext i
      simp only [PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have hadd_mem : ∀ {z : EuclideanPlane}, z ∈ Metric.closedBall (-a) ρ →
      z + (2 : ℝ) • a ∈ Metric.closedBall a ρ := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    have heq : z + (2 : ℝ) • a - a = z - (-a) := by
      ext i
      simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  constructor
  · ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      dsimp only
      rw [sectorSwapIsotopy_timeOne_of_mem_neg hr₀ a hρ_pos hρ_lt hsum hy]
      exact hadd_mem hy
    · intro hz
      refine ⟨z - (2 : ℝ) • a, hsub_mem hz, ?_⟩
      dsimp only
      rw [sectorSwapIsotopy_timeOne_of_mem_neg hr₀ a hρ_pos hρ_lt hsum (hsub_mem hz)]
      abel
  · ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      dsimp only
      rw [sectorSwapIsotopy_timeOne_of_mem_pos hr₀ a hρ_pos hρ_lt hsum hy]
      exact hsub_mem hy
    · intro hz
      refine ⟨z + (2 : ℝ) • a, hadd_mem hz, ?_⟩
      dsimp only
      rw [sectorSwapIsotopy_timeOne_of_mem_pos hr₀ a hρ_pos hρ_lt hsum (hadd_mem hz)]
      abel

/-- Non-vacuity witness: `sectorSwapIsotopy`'s time-`1` disk diffeomorphism is nontrivial
(`≠ id`). -/
theorem sectorSwapIsotopy_diskTimeOneMap_ne_id {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    (a : EuclideanPlane) {ρ : ℝ} (hρ_pos : 0 < ρ) (hρ_lt : ρ < ‖a‖) (hsum : ‖a‖ + ρ < r₀) :
    (sectorSwapIsotopy hr₀ a hρ_pos hρ_lt hsum).diskTimeOneMap ≠ id := by
  intro hid
  have ha_mem : a ∈ Metric.closedBall a ρ := Metric.mem_closedBall_self hρ_pos.le
  have ha_ball : a ∈ Metric.ball (0 : EuclideanPlane) r₀ :=
    (symmetric_closedBall_subset_ball hsum).1 ha_mem
  have ha_disk : a ∈ UnitDisk2 := Metric.ball_subset_ball hr₀.2.le ha_ball
  have heq := congrArg Subtype.val (congrFun hid ⟨a, ha_disk⟩)
  change (sectorSwapIsotopy hr₀ a hρ_pos hρ_lt hsum).d (1, a) = a at heq
  rw [sectorSwapIsotopy_timeOne_of_mem_pos hr₀ a hρ_pos hρ_lt hsum ha_mem] at heq
  have ha_zero : a = 0 := by
    have h2 : (2 : ℝ) • a = 0 := by
      calc
        (2 : ℝ) • a = a - (a - (2 : ℝ) • a) := by abel
        _ = a - a := by rw [heq]
        _ = 0 := sub_self a
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  rw [ha_zero, norm_zero] at hρ_lt
  linarith

/-- Canonical sub-ball offset `(r₀ / 3) • e₀` inside `Metric.ball 0 r₀`. -/
noncomputable def canonicalSectorSwapCenter (r₀ : ℝ) : EuclideanPlane :=
  (r₀ / 3) • planeBasis0

theorem norm_canonicalSectorSwapCenter {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ‖canonicalSectorSwapCenter r₀‖ = r₀ / 3 := by
  have hpos : 0 < r₀ / 3 := by positivity
  rw [canonicalSectorSwapCenter, norm_smul, Real.norm_of_nonneg hpos.le,
    EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp

/-- Canonical parameter-free instantiation of `sectorSwapIsotopy` at offset `a = (r₀ / 3) • e₀`
and sub-ball radius `ρ = r₀ / 6`. -/
noncomputable def canonicalSectorSwapIsotopy {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1) :
    AreaPreservingDiskIsotopy r₀ :=
  sectorSwapIsotopy hr₀ (canonicalSectorSwapCenter r₀) (ρ := r₀ / 6)
    (by linarith [hr₀.1])
    (by rw [norm_canonicalSectorSwapCenter hr₀.1]; linarith [hr₀.1])
    (by rw [norm_canonicalSectorSwapCenter hr₀.1]; linarith [hr₀.1])

/-- Complete verification bundle for `canonicalSectorSwapIsotopy`: the two sub-balls of radius
`r₀ / 6` around `±(r₀ / 3) • e₀` are disjoint, lie inside `Metric.ball 0 r₀`, are exchanged onto
each other at `t = 1`, and witness `diskTimeOneMap ≠ id`. -/
theorem canonicalSectorSwapIsotopy_properties {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1) :
    let a := canonicalSectorSwapCenter r₀
    let ρ := r₀ / 6
    Disjoint (Metric.closedBall (-a) ρ) (Metric.closedBall a ρ) ∧
      Metric.closedBall a ρ ⊆ Metric.ball (0 : EuclideanPlane) r₀ ∧
      Metric.closedBall (-a) ρ ⊆ Metric.ball (0 : EuclideanPlane) r₀ ∧
      (fun y ↦ (canonicalSectorSwapIsotopy hr₀).d (1, y)) '' Metric.closedBall (-a) ρ =
        Metric.closedBall a ρ ∧
      (fun y ↦ (canonicalSectorSwapIsotopy hr₀).d (1, y)) '' Metric.closedBall a ρ =
        Metric.closedBall (-a) ρ ∧
      (canonicalSectorSwapIsotopy hr₀).diskTimeOneMap ≠ id := by
  intro a ρ
  have hρ_pos : 0 < ρ := by dsimp [ρ]; linarith [hr₀.1]
  have hρ_lt : ρ < ‖a‖ := by
    dsimp [a, ρ]
    rw [norm_canonicalSectorSwapCenter hr₀.1]
    linarith [hr₀.1]
  have hsum : ‖a‖ + ρ < r₀ := by
    dsimp [a, ρ]
    rw [norm_canonicalSectorSwapCenter hr₀.1]
    linarith [hr₀.1]
  obtain ⟨hsub1, hsub2⟩ := symmetric_closedBall_subset_ball hsum
  obtain ⟨him1, him2⟩ := sectorSwapIsotopy_image_swap hr₀ a hρ_pos hρ_lt hsum
  exact ⟨disjoint_symmetric_closedBalls hρ_lt, hsub1, hsub2, him1, him2,
    sectorSwapIsotopy_diskTimeOneMap_ne_id hr₀ a hρ_pos hρ_lt hsum⟩

/-! ### B.3 Bumped Hyperbolic Cantor-Block Stretch (`bumpedHyperbolicStretchIsotopy`, Figure 2) -/

/-- Hyperbolic squeeze quadratic `-μ * (y₀ - c₀) * (y₁ - c₁)` generating area-preserving scaling
`(e^{-t μ}, e^{t μ})` around `c : EuclideanPlane`. -/
noncomputable def stretchQuad (c : EuclideanPlane) (μ : ℝ) (y : EuclideanPlane) : ℝ :=
  -μ * ((y 0 - c 0) * (y 1 - c 1))

theorem contDiff_stretchQuad (c : EuclideanPlane) (μ : ℝ) : ContDiff ℝ ∞ (stretchQuad c μ) := by
  unfold stretchQuad
  have hy0 : ContDiff ℝ ∞ (fun y : EuclideanPlane ↦ y 0) := (planeCoordCLM 0).contDiff
  have hy1 : ContDiff ℝ ∞ (fun y : EuclideanPlane ↦ y 1) := (planeCoordCLM 1).contDiff
  exact contDiff_const.mul ((hy0.sub contDiff_const).mul (hy1.sub contDiff_const))

theorem hasFDerivAt_stretchQuad (c : EuclideanPlane) (μ : ℝ) (x : EuclideanPlane) :
    HasFDerivAt (stretchQuad c μ)
      ((-μ * (x 1 - c 1)) • planeCoordCLM 0 + (-μ * (x 0 - c 0)) • planeCoordCLM 1) x := by
  unfold stretchQuad
  have h0 : HasFDerivAt (fun y : EuclideanPlane ↦ y 0 - c 0) (planeCoordCLM 0) x :=
    (planeCoordCLM 0).hasFDerivAt.sub_const (c 0)
  have h1 : HasFDerivAt (fun y : EuclideanPlane ↦ y 1 - c 1) (planeCoordCLM 1) x :=
    (planeCoordCLM 1).hasFDerivAt.sub_const (c 1)
  convert (h0.mul h1).const_mul (-μ) using 1
  ext v
  simp only [add_apply, smul_apply, planeCoordCLM_apply, smul_eq_mul]
  ring

/-- **Figure 2 Elementary Move (`bumpedHyperbolicStretchHamiltonian`)**:
Autonomous bumped hyperbolic Hamiltonian supported inside `Metric.ball c r_out ⊆ Metric.ball 0 r₀`,
generating the Cantor-block squeeze `(e^{-μ}, e^μ)` around `c`. -/
noncomputable def bumpedHyperbolicStretchHamiltonian {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    (c : EuclideanPlane) {r_out : ℝ} (hr_out : 0 < r_out)
    (hsub : Metric.ball c r_out ⊆ Metric.ball (0 : EuclideanPlane) r₀) (μ : ℝ) :
    CompactlySupportedPlanarHamiltonian r₀ :=
  let χ : ContDiffBump c := ⟨r_out / 2, r_out, by linarith, by linarith⟩
  CompactlySupportedPlanarHamiltonian.ofAutonomous hr₀
    (fun y ↦ χ y * stretchQuad c μ y)
    ((χ.contDiff (n := ⊤)).mul (contDiff_stretchQuad c μ))
    (fun y hy ↦ by
      have hnot : y ∉ Metric.ball c r_out := fun h ↦ hy (hsub h)
      have hdist : r_out ≤ dist y c := not_lt.mp (by simpa only [Metric.mem_ball] using hnot)
      rw [χ.zero_of_le_dist hdist, zero_mul])

/-- **Figure 2 Elementary Move (`bumpedHyperbolicStretchIsotopy`)**:
`AreaPreservingDiskIsotopy r₀` generated by `bumpedHyperbolicStretchHamiltonian`. -/
noncomputable def bumpedHyperbolicStretchIsotopy {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    (c : EuclideanPlane) {r_out : ℝ} (hr_out : 0 < r_out)
    (hsub : Metric.ball c r_out ⊆ Metric.ball (0 : EuclideanPlane) r₀) (μ : ℝ) :
    AreaPreservingDiskIsotopy r₀ :=
  (bumpedHyperbolicStretchHamiltonian hr₀ c hr_out hsub μ).toDiskIsotopy

/-- **Exact Time-`1` Hyperbolic Stretch Action**:
For every point `y₀ ∈ Metric.closedBall c δ` with `Real.exp (2 * |μ|) * δ < r_out / 2`,
`bumpedHyperbolicStretchIsotopy` acts at `t = 1` by exact area-preserving diagonal scaling
`c + ![e^{-μ}(y₀₀ - c₀), e^μ(y₀₁ - c₁)]`. -/
theorem bumpedHyperbolicStretchIsotopy_timeOne_of_mem_closedBall {r₀ : ℝ}
    (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1) (c : EuclideanPlane) {r_out δ : ℝ} (hr_out : 0 < r_out)
    (hsub : Metric.ball c r_out ⊆ Metric.ball (0 : EuclideanPlane) r₀) (μ : ℝ)
    (hδ : Real.exp (2 * |μ|) * δ < r_out / 2)
    {y₀ : EuclideanPlane} (hy₀ : y₀ ∈ Metric.closedBall c δ) :
    (bumpedHyperbolicStretchIsotopy hr₀ c hr_out hsub μ).d (1, y₀) =
      c + WithLp.toLp 2 ![Real.exp (-μ) * (y₀ 0 - c 0), Real.exp μ * (y₀ 1 - c 1)] := by
  let P := bumpedHyperbolicStretchHamiltonian hr₀ c hr_out hsub μ
  let χ : ContDiffBump c := ⟨r_out / 2, r_out, by linarith, by linarith⟩
  let v := y₀ - c
  let γ : ℝ → EuclideanPlane := fun u ↦
    c + WithLp.toLp 2 ![Real.exp (-(u * μ)) * v 0, Real.exp (u * μ) * v 1]
  have hγ0 : γ 0 = y₀ := by
    ext i
    fin_cases i <;> simp [γ, v]
  have hv_norm : ‖v‖ ≤ δ := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, v] using hy₀
  have hγ_mem : ∀ u ∈ Set.Ioo (-2 : ℝ) 2, γ u ∈ Metric.ball c (r_out / 2) := by
    intro u hu
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, EuclideanSpace.norm_eq,
      Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Real.norm_eq_abs,
      sq_abs]
    have hu_abs : |u| ≤ 2 := abs_le.mpr ⟨hu.1.le, hu.2.le⟩
    have h1 : -(u * μ) ≤ 2 * |μ| := by
      have : -(u * μ) ≤ |u * μ| := neg_le_abs _
      rw [abs_mul] at this
      exact this.trans (mul_le_mul_of_nonneg_right hu_abs (abs_nonneg μ))
    have h2 : u * μ ≤ 2 * |μ| := by
      have : u * μ ≤ |u * μ| := le_abs_self _
      rw [abs_mul] at this
      exact this.trans (mul_le_mul_of_nonneg_right hu_abs (abs_nonneg μ))
    have he1 : Real.exp (-(u * μ)) ≤ Real.exp (2 * |μ|) := Real.exp_le_exp.mpr h1
    have he2 : Real.exp (u * μ) ≤ Real.exp (2 * |μ|) := Real.exp_le_exp.mpr h2
    have hsq1 : (Real.exp (-(u * μ)) * v 0) ^ 2 ≤ (Real.exp (2 * |μ|)) ^ 2 * v 0 ^ 2 := by
      have hsq_exp : (Real.exp (-(u * μ))) ^ 2 ≤ (Real.exp (2 * |μ|)) ^ 2 :=
        pow_le_pow_left₀ (Real.exp_nonneg _) he1 2
      nlinarith [sq_nonneg (v 0)]
    have hsq2 : (Real.exp (u * μ) * v 1) ^ 2 ≤ (Real.exp (2 * |μ|)) ^ 2 * v 1 ^ 2 := by
      have hsq_exp : (Real.exp (u * μ)) ^ 2 ≤ (Real.exp (2 * |μ|)) ^ 2 :=
        pow_le_pow_left₀ (Real.exp_nonneg _) he2 2
      nlinarith [sq_nonneg (v 1)]
    have hv_sq : v 0 ^ 2 + v 1 ^ 2 = ‖v‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sq_sqrt (by positivity)]
      simp [Real.norm_eq_abs, sq_abs]
    have hnorm_nonneg : 0 ≤ ‖v‖ := norm_nonneg v
    have hδ_nonneg : 0 ≤ δ := le_trans hnorm_nonneg hv_norm
    have hv_sq_le : v 0 ^ 2 + v 1 ^ 2 ≤ δ ^ 2 := by
      rw [hv_sq]
      exact pow_le_pow_left₀ hnorm_nonneg hv_norm 2
    have hsum_sq :
        (Real.exp (-(u * μ)) * v 0) ^ 2 + (Real.exp (u * μ) * v 1) ^ 2 ≤
          (Real.exp (2 * |μ|) * δ) ^ 2 := by
      calc
        (Real.exp (-(u * μ)) * v 0) ^ 2 + (Real.exp (u * μ) * v 1) ^ 2
            ≤ (Real.exp (2 * |μ|)) ^ 2 * (v 0 ^ 2 + v 1 ^ 2) := by linarith
        _ ≤ (Real.exp (2 * |μ|)) ^ 2 * δ ^ 2 :=
              mul_le_mul_of_nonneg_left hv_sq_le (sq_nonneg _)
        _ = (Real.exp (2 * |μ|) * δ) ^ 2 := by ring
    calc
      Real.sqrt ((Real.exp (-(u * μ)) * v 0) ^ 2 + (Real.exp (u * μ) * v 1) ^ 2)
          ≤ Real.sqrt ((Real.exp (2 * |μ|) * δ) ^ 2) := Real.sqrt_le_sqrt hsum_sq
      _ = Real.exp (2 * |μ|) * δ := Real.sqrt_sq (by positivity)
      _ < r_out / 2 := hδ
  have hγ_deriv : ∀ u ∈ Set.Ioo (-2 : ℝ) 2,
      HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 2) γ u
        ((1 : ℝ →L[ℝ] ℝ).smulRight (P.vectorField u (γ u))) := by
    intro u hu
    have hev : P.slice u =ᶠ[𝓝 (γ u)] stretchQuad c μ := by
      filter_upwards [χ.eventuallyEq_one_of_mem_ball (hγ_mem u hu)] with z hz
      change χ z * stretchQuad c μ z = stretchQuad c μ z
      rw [hz, Pi.one_apply, one_mul]
    let vel : EuclideanPlane :=
      (-μ * (γ u 0 - c 0)) • planeBasis0 + (μ * (γ u 1 - c 1)) • planeBasis1
    have hX_str : TauCeti.SmoothTwoForm.hamiltonianVectorField planeAreaForm
        (stretchQuad c μ) (γ u) = (vel : TangentSpace (𝓡 2) (γ u)) := by
      refine hamiltonianVectorField_planeAreaForm_eq_of_hasFDerivAt
        (hasFDerivAt_stretchQuad c μ (γ u)) vel fun w ↦ ?_
      have hv0 : vel 0 = -μ * (γ u 0 - c 0) := by simp [vel]
      have hv1 : vel 1 = μ * (γ u 1 - c 1) := by simp [vel]
      rw [hv0, hv1]
      simp only [add_apply, smul_apply, planeCoordCLM_apply, smul_eq_mul]
      ring
    have hX : P.vectorField u (γ u) = (vel : TangentSpace (𝓡 2) (γ u)) :=
      (hev.hamiltonianVectorField_eq planeAreaForm).trans hX_str
    rw [hX]
    have hlin_pos : HasDerivAt (fun s : ℝ ↦ s * μ) μ u := by
      simpa only [one_mul] using (hasDerivAt_id' u).mul_const μ
    have hlin_neg : HasDerivAt (fun s : ℝ ↦ -(s * μ)) (-μ) u := hlin_pos.neg
    have hexp0 : HasDerivAt (fun s : ℝ ↦ c 0 + Real.exp (-(s * μ)) * v 0)
        (Real.exp (-(u * μ)) * (-μ) * v 0) u :=
      (hlin_neg.exp.mul_const (v 0)).const_add (c 0)
    have hexp1 : HasDerivAt (fun s : ℝ ↦ c 1 + Real.exp (s * μ) * v 1)
        (Real.exp (u * μ) * μ * v 1) u :=
      (hlin_pos.exp.mul_const (v 1)).const_add (c 1)
    have hγ_eq : γ = fun s : ℝ ↦
        (c 0 + Real.exp (-(s * μ)) * v 0) • planeBasis0 +
        (c 1 + Real.exp (s * μ) * v 1) • planeBasis1 := by
      funext s
      ext i
      fin_cases i <;> simp [γ]
    have hvel_eq :
        (Real.exp (-(u * μ)) * (-μ) * v 0) • planeBasis0 +
        (Real.exp (u * μ) * μ * v 1) • planeBasis1 = vel := by
      have hg0 : γ u 0 - c 0 = Real.exp (-(u * μ)) * v 0 := by simp [γ]
      have hg1 : γ u 1 - c 1 = Real.exp (u * μ) * v 1 := by simp [γ]
      dsimp only [vel]
      rw [hg0, hg1]
      ext i
      fin_cases i <;> simp <;> ring
    have hd : HasDerivAt γ vel u := by
      rw [hγ_eq, ← hvel_eq]
      exact (hexp0.smul_const planeBasis0).add (hexp1.smul_const planeBasis1)
    exact hasMFDerivAt_iff_hasFDerivAt.mpr hd.hasFDerivAt
  have hflow := TauCeti.timeDependentFlowOf_eq_of_hasMFDerivAt
    (P.contMDiff_vectorField.of_le (by simp))
    (s := (0 : ℝ)) (t := (1 : ℝ)) (a := (-2 : ℝ)) (b := (2 : ℝ))
    hγ_deriv ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
  rw [hγ0] at hflow
  simpa only [bumpedHyperbolicStretchIsotopy, CompactlySupportedPlanarHamiltonian.toDiskIsotopy_d,
    γ, v, one_mul, PiLp.sub_apply] using hflow

/-- Specialization of `bumpedHyperbolicStretchIsotopy` to `μ = Real.log (cantorBase N)`, realizing
the exact `((cantorBase N)⁻¹, cantorBase N)` Cantor-square hyperbolic scaling of `CMPP21` Figure 2
on `Metric.closedBall c δ`. -/
theorem bumpedHyperbolicStretchIsotopy_cantorBase_timeOne {r₀ : ℝ}
    (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1) (c : EuclideanPlane) {r_out δ : ℝ} (hr_out : 0 < r_out)
    (hsub : Metric.ball c r_out ⊆ Metric.ball (0 : EuclideanPlane) r₀) (N : ℕ)
    (hδ : Real.exp (2 * |Real.log (cantorBase N : ℝ)|) * δ < r_out / 2)
    {y₀ : EuclideanPlane} (hy₀ : y₀ ∈ Metric.closedBall c δ) :
    (bumpedHyperbolicStretchIsotopy hr₀ c hr_out hsub (Real.log (cantorBase N : ℝ))).d (1, y₀) =
      c + WithLp.toLp 2
        ![(cantorBase N : ℝ)⁻¹ * (y₀ 0 - c 0), (cantorBase N : ℝ) * (y₀ 1 - c 1)] := by
  have hB : 0 < (cantorBase N : ℝ) := by exact_mod_cast cantorBase_pos N
  rw [bumpedHyperbolicStretchIsotopy_timeOne_of_mem_closedBall hr₀ c hr_out hsub
    (Real.log (cantorBase N : ℝ)) hδ hy₀, Real.exp_neg, Real.exp_log hB]

end HamiltonianEngine

/-! ## 4. `CMPP21` Cantor-Circulation Bridge to `HasTuringCompleteAreaPreservingDiskIsotopy` -/

section CantorCirculationBridge

/-- General `2⁻ᵐ` Euclidean error bound in `UnitDisk2` for `approxCantorList` applied to the
first `m + 1` digits of any sequence `s : ℤ → A` under `enc : A ≃ Fin N`. -/
theorem norm_approxCantorList_pair_sub_cantorDiskEmbed_le {A : Type*} {N : ℕ}
    (enc : A ≃ Fin N) (s : ℤ → A) (m : ℕ) :
    let B := cantorBase N
    let q₀ := approxCantorList B ((List.range (m + 1)).map fun j ↦ (enc (negHalf s j)).1)
    let q₁ := approxCantorList B ((List.range (m + 1)).map fun j ↦ (enc (nonnegHalf s j)).1)
    ‖ratFracPairToEuclidean2 (q₀, q₁) - (cantorDiskEmbed enc s).1‖ ≤ (1 / 2 : ℝ) ^ m := by
  intro B q₀ q₁
  have herr0 :
      |q₀.toReal - scaledCantorCoord (fun j ↦ enc (negHalf s j))| ≤
        1 / (4 * (B : ℝ) ^ (m + 1)) :=
    abs_approxCantorList_sub_scaledCantorCoord (fun j ↦ enc (negHalf s j)) m
  have herr1 :
      |q₁.toReal - scaledCantorCoord (fun j ↦ enc (nonnegHalf s j))| ≤
        1 / (4 * (B : ℝ) ^ (m + 1)) :=
    abs_approxCantorList_sub_scaledCantorCoord (fun j ↦ enc (nonnegHalf s j)) m
  set e₀ : ℝ := q₀.toReal - scaledCantorCoord (fun j ↦ enc (negHalf s j))
  set e₁ : ℝ := q₁.toReal - scaledCantorCoord (fun j ↦ enc (nonnegHalf s j))
  have hnorm :
      ‖ratFracPairToEuclidean2 (q₀, q₁) - (cantorDiskEmbed enc s).1‖ =
        Real.sqrt (e₀ ^ 2 + e₁ ^ 2) := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp only [ratFracPairToEuclidean2, cantorDiskEmbed, PiLp.sub_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs, e₀, e₁]
  rw [hnorm]
  have h2pos : 0 < (2 : ℝ) ^ (m + 1) := by positivity
  have hB2 : (2 : ℝ) ^ (m + 1) ≤ (B : ℝ) ^ (m + 1) := by
    refine pow_le_pow_left₀ (by positivity) ?_ (m + 1)
    exact_mod_cast le_trans (by decide : 2 ≤ 3) (three_le_cantorBase N)
  have hbound : 1 / (4 * (B : ℝ) ^ (m + 1)) ≤ (1 / 2 : ℝ) ^ (m + 1) := by
    rw [one_div_pow]
    have h4 : (2 : ℝ) ^ (m + 1) ≤ 4 * (B : ℝ) ^ (m + 1) := by linarith
    exact one_div_le_one_div_of_le h2pos h4
  have he0 : |e₀| ≤ (1 / 2 : ℝ) ^ (m + 1) := herr0.trans hbound
  have he1 : |e₁| ≤ (1 / 2 : ℝ) ^ (m + 1) := herr1.trans hbound
  have hsq0 : e₀ ^ 2 ≤ ((1 / 2 : ℝ) ^ (m + 1)) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) he0 2
  have hsq1 : e₁ ^ 2 ≤ ((1 / 2 : ℝ) ^ (m + 1)) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) he1 2
  have hsum_sq : e₀ ^ 2 + e₁ ^ 2 ≤ ((1 / 2 : ℝ) ^ m) ^ 2 := by
    have hhalf : ((1 / 2 : ℝ) ^ (m + 1)) ^ 2 + ((1 / 2 : ℝ) ^ (m + 1)) ^ 2 =
        (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ m) ^ 2 := by
      rw [pow_succ]
      ring
    have hpos_m : 0 ≤ ((1 / 2 : ℝ) ^ m) ^ 2 := sq_nonneg _
    linarith
  calc
    Real.sqrt (e₀ ^ 2 + e₁ ^ 2) ≤ Real.sqrt (((1 / 2 : ℝ) ^ m) ^ 2) :=
      Real.sqrt_le_sqrt hsum_sq
    _ = (1 / 2 : ℝ) ^ m := Real.sqrt_sq (by positivity)

/-- `listToDiskIsotopy` maps list concatenation to time-`1` composition on `UnitDisk2`. -/
theorem listToDiskIsotopy_append_diskTimeOneMap {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    (Ps₂ Ps₁ : List (CompactlySupportedPlanarHamiltonian r₀)) :
    (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy hr₀ (Ps₂ ++ Ps₁)).diskTimeOneMap =
      (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy hr₀ Ps₂).diskTimeOneMap ∘
        (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy hr₀ Ps₁).diskTimeOneMap := by
  induction Ps₂ with
  | nil =>
    simp only [List.nil_append, CompactlySupportedPlanarHamiltonian.listToDiskIsotopy_nil,
      AreaPreservingDiskIsotopy.refl_diskTimeOneMap, Function.id_comp]
  | cons P Ps₂ ih =>
    simp only [List.cons_append, CompactlySupportedPlanarHamiltonian.listToDiskIsotopy_cons,
      AreaPreservingDiskIsotopy.compSame_diskTimeOneMap, ih, Function.comp_assoc]

/-- Predicate asserting that a finite list of `CompactlySupportedPlanarHamiltonian r₀`s realizes a
generalized shift `Φ : GeneralizedShift A` on the middle-Cantor square `cantorDiskEmbed enc` at
time `t = 1` (`CMPP21` Proposition 5.1 & Theorem 5.2). -/
def RealizesGeneralizedShiftByHamiltonians {A : Type*} {N : ℕ} (enc : A ≃ Fin N)
    (Φ : GeneralizedShift A) {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    (Ps : List (CompactlySupportedPlanarHamiltonian r₀)) : Prop :=
  ∀ s : ℤ → A,
    (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy hr₀ Ps).diskTimeOneMap
        (cantorDiskEmbed enc s) =
      cantorDiskEmbed enc (Φ.eval s)

/-- Concatenating two lists of `CompactlySupportedPlanarHamiltonian r₀`s realizes the composed
generalized shifts at `t = 1` on `cantorDiskEmbed enc`. -/
theorem RealizesGeneralizedShiftByHamiltonians.append {A : Type*} {N : ℕ} (enc : A ≃ Fin N)
    {Φ₂ Φ₁ : GeneralizedShift A} {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    {Ps₂ Ps₁ : List (CompactlySupportedPlanarHamiltonian r₀)}
    (h₂ : RealizesGeneralizedShiftByHamiltonians enc Φ₂ hr₀ Ps₂)
    (h₁ : RealizesGeneralizedShiftByHamiltonians enc Φ₁ hr₀ Ps₁) :
    ∀ s : ℤ → A,
      (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy hr₀ (Ps₂ ++ Ps₁)).diskTimeOneMap
          (cantorDiskEmbed enc s) =
        cantorDiskEmbed enc (Φ₂.eval (Φ₁.eval s)) := by
  intro s
  rw [listToDiskIsotopy_append_diskTimeOneMap, Function.comp_apply, h₁ s, h₂ (Φ₁.eval s)]

/-- A finite unidirectional **universal reversible Turing simulator** (`Bennett 1973`, `CMPP21`
Theorem 2.2 & Lemma 4.3) simulating arbitrary `FinTM0` machines on bi-infinite sequences
`ℤ → R.ShiftAlphabet` with primitive-recursive initial digit enumerators for `Tape.mk₂ L R`. -/
structure UniversalReversibleSimulator : Type 1 where
  /-- Underlying unidirectional reversible Turing machine (`Γ, Q : Type`). -/
  R : ReversibleTM.{0, 0}
  /-- Cardinality `N` of `R.ShiftAlphabet`. -/
  shiftCard : ℕ
  /-- Explicit numbering `R.ShiftAlphabet ≃ Fin shiftCard`. -/
  encShift : R.ShiftAlphabet ≃ Fin shiftCard
  /-- Initial reversible configuration encoding `(M, t)` (independent of `(k, w)`). -/
  initRevCfg : (M : FinTM0) → FinSupportedTape M → R.Cfg
  /-- Nonempty family of variable-radius accepting cylinder blocks (independent of `t`). -/
  acceptBlocks :
    (M : FinTM0) → (k : ℕ) → Window M k →
      Set (Σ K : ℕ, Set.Icc (-(K : ℤ)) (K : ℤ) → R.ShiftAlphabet)
  /-- Non-emptiness of `acceptBlocks M k w` for every `(M, k, w)`. -/
  acceptBlocks_nonempty :
    ∀ (M : FinTM0) (k : ℕ) (w : Window M k), (acceptBlocks M k w).Nonempty
  /-- Forward reversible orbit enters an accepting cylinder block iff `HaltsWithWindow M t k w`. -/
  orbit_mem_acceptBlocks_iff :
    ∀ (M : FinTM0) (t : FinSupportedTape M) (k : ℕ) (w : Window M k),
      (∃ n : ℕ, ∃ b ∈ acceptBlocks M k w,
        R.encodeCfg (R.step^[n] (initRevCfg M t)) ∈ cylinderIcc b.1 b.2) ↔
      HaltsWithWindow M t k w
  /-- Non-terminal `TM0` initial configurations lie outside all accepting blocks at `n = 0`. -/
  encodeCfg_init_notMem_of_step_ne_none :
    ∀ (M : FinTM0) (t : FinSupportedTape M) (k : ℕ) (w : Window M k),
      Turing.TM0.step M.machine (M.initCfg t) ≠ none →
      ∀ b ∈ acceptBlocks M k w,
        R.encodeCfg (initRevCfg M t) ∉ cylinderIcc b.1 b.2
  /-- Primitive-recursive digit enumerators for the negative and non-negative Cantor halves of
  `R.encodeCfg (initRevCfg M (Turing.Tape.mk₂ L R_tape))`. -/
  primrec_initDigits :
    ∀ M : FinTM0,
      ∃ (encΓ : M.Γ ≃ Fin (Fintype.card M.Γ))
        (negDig posDig :
          List (Fin (Fintype.card M.Γ)) × List (Fin (Fintype.card M.Γ)) × ℕ → ℕ),
        Primrec negDig ∧
        Primrec posDig ∧
        ∀ (L R_tape : List M.Γ) (j : ℕ),
          negDig (L.map encΓ, R_tape.map encΓ, j) =
            (encShift (negHalf (R.encodeCfg (initRevCfg M (Turing.Tape.mk₂ L R_tape))) j)).1 ∧
          posDig (L.map encΓ, R_tape.map encΓ, j) =
            (encShift (nonnegHalf (R.encodeCfg (initRevCfg M (Turing.Tape.mk₂ L R_tape))) j)).1

/-- Nonempty open union of Cantor cylinder rectangles in `UnitDisk2` corresponding to
`S.acceptBlocks M k w`. -/
noncomputable def UniversalReversibleSimulator.targetOpen (S : UniversalReversibleSimulator)
    (M : FinTM0) (k : ℕ) (w : Window M k) : Opens UnitDisk2 :=
  ⟨⋃ b ∈ S.acceptBlocks M k w, (cantorCylinderRect S.encShift b.1 b.2).1,
    isOpen_biUnion fun b _ ↦ (cantorCylinderRect S.encShift b.1 b.2).2⟩

theorem UniversalReversibleSimulator.targetOpen_nonempty (S : UniversalReversibleSimulator)
    (M : FinTM0) (k : ℕ) (w : Window M k) :
    (S.targetOpen M k w).1.Nonempty := by
  obtain ⟨b₀, hb₀⟩ := S.acceptBlocks_nonempty M k w
  obtain ⟨y, hy⟩ := cantorCylinderRect_nonempty S.encShift b₀.1 b₀.2
  exact ⟨y, Set.mem_biUnion hb₀ hy⟩

/-- **Unconditional Cantor-Shift-to-`TuringCompleteWitness` Theorem**:
Any self-map `φ : UnitDisk2 → UnitDisk2` conjugating `S.R.toGeneralizedShift.eval` on
`cantorDiskEmbed S.encShift` for a `UniversalReversibleSimulator` `S` admits a full anti-vacuous
`TuringCompleteWitness φ` (including `Computable` `2⁻ᵐ` `RatFrac` approximations). -/
noncomputable def UniversalReversibleSimulator.turingCompleteWitness
    (S : UniversalReversibleSimulator) {φ : UnitDisk2 → UnitDisk2}
    (hconj : ∀ s : ℤ → S.R.ShiftAlphabet,
      φ (cantorDiskEmbed S.encShift s) =
        cantorDiskEmbed S.encShift (S.R.toGeneralizedShift.eval s)) :
    TuringCompleteWitness φ where
  encodePoint M t := cantorDiskEmbed S.encShift (S.R.encodeCfg (S.initRevCfg M t))
  encodeOpen M k w := S.targetOpen M k w
  encodeOpen_nonempty := S.targetOpen_nonempty
  orbit_mem_encodeOpen_iff M t k w := by
    have hiter : ∀ (n : ℕ) (s : ℤ → S.R.ShiftAlphabet),
        φ^[n] (cantorDiskEmbed S.encShift s) =
          cantorDiskEmbed S.encShift (S.R.toGeneralizedShift.eval^[n] s) := by
      intro n s
      induction n generalizing s with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply, hconj, ih, Function.iterate_succ_apply]
    refine (exists_congr fun n ↦ ?_).trans (S.orbit_mem_acceptBlocks_iff M t k w)
    rw [hiter n (S.R.encodeCfg (S.initRevCfg M t)), S.R.iterate_eval_encodeCfg]
    change cantorDiskEmbed S.encShift (S.R.encodeCfg (S.R.step^[n] (S.initRevCfg M t))) ∈
      ⋃ b ∈ S.acceptBlocks M k w, (cantorCylinderRect S.encShift b.1 b.2).1 ↔ _
    simp only [Set.mem_iUnion, exists_prop]
    refine exists_congr fun b ↦ and_congr_right fun _ ↦ ?_
    exact cantorDiskEmbed_mem_cantorCylinderRect_iff S.encShift _ b.1 b.2
  notMem_encodeOpen_of_step_ne_none M t k w hstep hmem := by
    change cantorDiskEmbed S.encShift (S.R.encodeCfg (S.initRevCfg M t)) ∈
      ⋃ b ∈ S.acceptBlocks M k w, (cantorCylinderRect S.encShift b.1 b.2).1 at hmem
    rw [Set.mem_iUnion₂] at hmem
    obtain ⟨b, hb, hrect⟩ := hmem
    have hcyl := (cantorDiskEmbed_mem_cantorCylinderRect_iff S.encShift _ b.1 b.2).mp hrect
    exact S.encodeCfg_init_notMem_of_step_ne_none M t k w hstep b hb hcyl
  chart := id
  chart_continuous := continuous_id
  chart_injective := Function.injective_id
  coordPoint M t := cantorDiskEmbed S.encShift (S.R.encodeCfg (S.initRevCfg M t))
  encodePoint_eq_chart _ _ := rfl
  computable_approx M := by
    obtain ⟨encΓ, negDig, posDig, hnegP, hposP, hdig_eq⟩ := S.primrec_initDigits M
    let B := cantorBase S.shiftCard
    let Arg := List (Fin (Fintype.card M.Γ)) × List (Fin (Fintype.card M.Γ)) × ℕ
    let negList : Arg → List ℕ :=
      fun p ↦ (List.range (p.2.2 + 1)).map fun j ↦ negDig (p.1, p.2.1, j)
    let posList : Arg → List ℕ :=
      fun p ↦ (List.range (p.2.2 + 1)).map fun j ↦ posDig (p.1, p.2.1, j)
    let approx : Arg → RatFrac × RatFrac :=
      fun p ↦ (approxCantorList B (negList p), approxCantorList B (posList p))
    refine ⟨encΓ, approx, ?_, ?_⟩
    · apply Primrec.to_comp
      have hL : Primrec (fun p : Arg ↦ p.1) := Primrec.fst
      have hR : Primrec (fun p : Arg ↦ p.2.1) := Primrec.fst.comp Primrec.snd
      have hm : Primrec (fun p : Arg ↦ p.2.2) := Primrec.snd.comp Primrec.snd
      have hrange : Primrec (fun p : Arg ↦ List.range (p.2.2 + 1)) :=
        Primrec.list_range.comp (Primrec.succ.comp hm)
      have htuple : Primrec (fun q : Arg × ℕ ↦ (q.1.1, q.1.2.1, q.2)) :=
        Primrec.pair (hL.comp Primrec.fst) (Primrec.pair (hR.comp Primrec.fst) Primrec.snd)
      have hnegList : Primrec negList :=
        Primrec.list_map hrange (hnegP.comp htuple).to₂
      have hposList : Primrec posList :=
        Primrec.list_map hrange (hposP.comp htuple).to₂
      exact Primrec.pair ((primrec_approxCantorList B).comp hnegList)
        ((primrec_approxCantorList B).comp hposList)
    · intro L R_tape m
      let s := S.R.encodeCfg (S.initRevCfg M (Turing.Tape.mk₂ L R_tape))
      have hneg_eq :
          negList (L.map encΓ, R_tape.map encΓ, m) =
            (List.range (m + 1)).map fun j ↦ (S.encShift (negHalf s j)).1 :=
        List.map_congr_left fun j _ ↦ (hdig_eq L R_tape j).1
      have hpos_eq :
          posList (L.map encΓ, R_tape.map encΓ, m) =
            (List.range (m + 1)).map fun j ↦ (S.encShift (nonnegHalf s j)).1 :=
        List.map_congr_left fun j _ ↦ (hdig_eq L R_tape j).2
      dsimp only [approx]
      rw [hneg_eq, hpos_eq]
      exact norm_approxCantorList_pair_sub_cantorDiskEmbed_le S.encShift s m

/-- **`CMPP21` Smooth Cantor-Circulation Hypothesis (`CMPP21` Section 5, Theorem 5.2)**:
Packages a universal unidirectional reversible simulator `sim : UniversalReversibleSimulator`
together with `r₀ ∈ (0, 1)` and a **finite list** of compactly supported planar Hamiltonians
`generators : List (CompactlySupportedPlanarHamiltonian r₀)` realizing the finite Cantor-rectangle
permutation/stretch `sim.R.toGeneralizedShift` on `cantorDiskEmbed sim.encShift` at `t = 1`. -/
class HasCMPPCantorCirculationHamiltonians : Type 1 where
  /-- Universal reversible Turing simulator on `shiftDom3 = {-1, 0, 1}`. -/
  sim : UniversalReversibleSimulator
  /-- Compact-support radius `r₀ ∈ (0, 1)`. -/
  r₀ : ℝ
  /-- `0 < r₀` and `r₀ < 1`. -/
  r₀_mem_Ioo : r₀ ∈ Set.Ioo (0 : ℝ) 1
  /-- Finite list of compactly supported planar Hamiltonians generating the Cantor circulation. -/
  generators : List (CompactlySupportedPlanarHamiltonian r₀)
  /-- At `t = 1`, the composed Hamiltonian disk isotopy realizes `sim.R.toGeneralizedShift` on
  `cantorDiskEmbed sim.encShift`. -/
  realizes_shift :
    RealizesGeneralizedShiftByHamiltonians sim.encShift sim.R.toGeneralizedShift
      r₀_mem_Ioo generators

section InstanceBridge

set_option linter.concreteInstances false

/-- Composed `AreaPreservingDiskIsotopy` generated via `TauCeti`'s Hamiltonian ODE engine from
`HasCMPPCantorCirculationHamiltonians.generators`. -/
noncomputable def cmppDiskIsotopy [C : HasCMPPCantorCirculationHamiltonians] :
    AreaPreservingDiskIsotopy C.r₀ :=
  CompactlySupportedPlanarHamiltonian.listToDiskIsotopy C.r₀_mem_Ioo C.generators

/-- `cmppDiskIsotopy.diskTimeOneMap` is Turing complete. -/
theorem isTuringComplete_cmppDiskIsotopy [C : HasCMPPCantorCirculationHamiltonians] :
    IsTuringComplete cmppDiskIsotopy.diskTimeOneMap :=
  ⟨C.sim.turingCompleteWitness C.realizes_shift⟩

/-- **Milestone M3.3 Bridge Instance**:
Constructs `HasTuringCompleteAreaPreservingDiskIsotopy` with zero `sorry` from
`[HasCMPPCantorCirculationHamiltonians]` using the `TauCeti` Hamiltonian disk-isotopy engine and
composition groupoid. -/
noncomputable instance instHasTuringCompleteAreaPreservingDiskIsotopyOfCMPP
    [C : HasCMPPCantorCirculationHamiltonians] :
    HasTuringCompleteAreaPreservingDiskIsotopy :=
  cmppDiskIsotopy.toHasTuringComplete isTuringComplete_cmppDiskIsotopy

end InstanceBridge

end CantorCirculationBridge

end S4TuringPoisson
