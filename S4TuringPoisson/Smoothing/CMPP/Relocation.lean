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

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Finset.Sum
public import S4TuringPoisson.Smoothing.CMPP.Primitives

/-!
# 1D Horizontal Sliding Lemma & Relocation Theorem RT (CMPP Milestone A3)

This module formalizes Milestone A3 (`S4TuringPoisson/Smoothing/CMPP/Relocation.lean`) of the
`CMPP21` Hamiltonian realization pipeline (`MISSION_DIRECTIVE_CMPP.md` §4.2, §7, §10 and
`docs/cmpp/geometry_spec.md` §3.2):

1. **Composition Order Helpers & Canonical Rational Geometry (`cmppR0 = 17 / 20`)**:
   - Pointwise composition identities (`listToDiskIsotopy_nil_d`, `listToDiskIsotopy_singleton_d`,
     `listToDiskIsotopy_cons_d`, `listToDiskIsotopy_append_d`) and autonomy preservation under list
     concatenation (`listToDiskIsotopy_autonomous_append`).
   - Canonical rational support radius `cmppR0 = 17 / 20`, workbench ball `B((0, -7/20), 3/10)`,
     global convex workspace `workBox = [-3/5, 11/20] × [-19/40, 1/4]`, and target parking square
     `parkBox = [-3/5, -7/20] × [0, 1/4]`.

2. **Disjoint `AxisRect` Open-Expansion & Obstacle-Avoiding L1 Translation**:
   - Exact coordinate separation characterization `AxisRect.disjoint_iff` and uniform `ε`-expansion
     clearance `exists_pos_openExpand_disjoint_finset` avoiding any `Finset` of obstacle rectangles
     inside `Metric.ball 0 cmppR0` (`exists_axisRect_translate_avoiding_finset`).

3. **1D Horizontal Sliding Lemmas (`exists_slide_right_hamiltonians`, `..._left_...`)**:
   - Proves by induction on `active.card` (selecting extremal `xMin` via `Finset.exists_max_image` /
     `Finset.exists_min_image`) that any pairwise-disjoint family of axis-parallel rectangles can be
     translated horizontally by `±(dx, 0)` via autonomous Hamiltonians without mutual or static
     obstacle collisions.

4. **Single-Piece Workbench Pipeline, Part-the-Sea & Relocation Theorem RT**:
   - Executes Pipeline A (`exists_single_piece_relocate_to_park`: right extraction, workbench drop
     and centering, L2 hyperbolic stretch, Part-the-Sea, upward parking insertion, Un-part-the-Sea)
     and proves **Relocation Theorem RT** (`exists_relocation_hamiltonians`) together with Gate G5
     anti-vacuity witness `cmppRelocation_sanity`.
-/

@[expose] public section

open Bundle Filter Function Metric Module Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace S4TuringPoisson.CMPP

/-! ## 0. Composition Order Helpers & Canonical Rational Geometry (`cmppR0 = 17 / 20`) -/

/-- Canonical planar Hamiltonian support radius `17 / 20 = 0.85 ∈ (0, 1)` for the CMPP relocation
pipeline (`docs/cmpp/geometry_spec.md` §3.2). -/
noncomputable def cmppR0 : ℝ := 17 / 20

/-- Canonical workbench center `(0, -7 / 20) = (0, -0.35)` (`docs/cmpp/geometry_spec.md` §3.2). -/
noncomputable def workbenchCenter : EuclideanPlane :=
  WithLp.toLp 2 ![0, -7 / 20]

/-- Canonical workbench outer cutoff radius `3 / 10 = 0.30` (`r_in = 3 / 20 = 0.15`). -/
noncomputable def workbenchRadius : ℝ := 3 / 10

/-- Convex planar workspace `[-3/5, 11/20] × [-19/40, 1/4]` enclosing `quarterSquare`, the right
extraction corridor, the workbench region, the staging box, and `parkBox`. -/
noncomputable def workBox : AxisRect :=
  { xMin := -3 / 5
    xMax := 11 / 20
    yMin := -19 / 40
    yMax := 1 / 4
    hx := by norm_num
    hy := by norm_num }

/-- Target parking square `[-3/5, -7/20] × [0, 1/4]` obtained by translating `quarterSquare` by
`(-3/5, 0)` (`docs/cmpp/geometry_spec.md` §3.1–§3.2). -/
noncomputable def parkBox : AxisRect :=
  quarterSquare.translate (-3 / 5) 0

/-- Pointwise evaluation of `listToDiskIsotopy` on the empty Hamiltonian list is the identity. -/
-- tier: T0
theorem listToDiskIsotopy_nil_d {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    (t : ℝ) (y : EuclideanPlane) :
    (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy hr₀ []).d (t, y) = y :=
  rfl

/-- Pointwise evaluation of `listToDiskIsotopy` on a singleton list `[P]`. -/
-- tier: T0
theorem listToDiskIsotopy_singleton_d {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    (P : CompactlySupportedPlanarHamiltonian r₀) (t : ℝ) (y : EuclideanPlane) :
    (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy hr₀ [P]).d (t, y) =
      P.toDiskIsotopy.d (t, y) :=
  rfl

/-- Pointwise evaluation of `listToDiskIsotopy` on `P :: Ps` applies `Ps` first and `P` second. -/
-- tier: T0
theorem listToDiskIsotopy_cons_d {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    (P : CompactlySupportedPlanarHamiltonian r₀)
    (Ps : List (CompactlySupportedPlanarHamiltonian r₀)) (t : ℝ) (y : EuclideanPlane) :
    (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy hr₀ (P :: Ps)).d (t, y) =
      P.toDiskIsotopy.d (t,
        (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy hr₀ Ps).d (t, y)) :=
  rfl

/-- Positivity `0 < cmppR0` of the canonical support radius `17 / 20`. -/
-- tier: T0
theorem cmppR0_pos : 0 < cmppR0 := by
  unfold cmppR0
  norm_cast
  linarith

/-- Upper bound `cmppR0 < 1` of the canonical support radius `17 / 20`. -/
-- tier: T0
theorem cmppR0_lt_one : cmppR0 < 1 := by
  unfold cmppR0
  norm_num

/-- Membership `cmppR0 ∈ (0, 1)` of the canonical support radius `17 / 20`. -/
-- tier: T0
theorem cmppR0_mem_Ioo : cmppR0 ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨cmppR0_pos, cmppR0_lt_one⟩

/-- First coordinate `0` of `workbenchCenter`. -/
-- tier: T0
@[simp]
theorem workbenchCenter_zero : workbenchCenter 0 = 0 :=
  rfl

/-- Second coordinate `-7 / 20` of `workbenchCenter`. -/
-- tier: T0
@[simp]
theorem workbenchCenter_one : workbenchCenter 1 = -7 / 20 :=
  rfl

/-- Positivity `0 < workbenchRadius` of `3 / 10`. -/
-- tier: T0
theorem workbenchRadius_pos : 0 < workbenchRadius := by
  unfold workbenchRadius
  norm_num

/-- Left `x`-endpoint `-3 / 5` of `workBox`. -/
-- tier: T0
@[simp]
theorem workBox_xMin : workBox.xMin = -3 / 5 := by
  rfl

/-- Right `x`-endpoint `11 / 20` of `workBox`. -/
-- tier: T0
@[simp]
theorem workBox_xMax : workBox.xMax = 11 / 20 := by
  unfold workBox
  norm_num

/-- Lower `y`-endpoint `-19 / 40` of `workBox`. -/
-- tier: T0
@[simp]
theorem workBox_yMin : workBox.yMin = -19 / 40 := by
  unfold workBox
  norm_num

/-- Upper `y`-endpoint `1 / 4` of `workBox`. -/
-- tier: T0
@[simp]
theorem workBox_yMax : workBox.yMax = 1 / 4 := by
  unfold workBox
  norm_num

/-- Left `x`-endpoint `-3 / 5` of `parkBox`. -/
-- tier: T0
@[simp]
theorem parkBox_xMin : parkBox.xMin = -3 / 5 := by
  simp [parkBox]

/-- Right `x`-endpoint `-7 / 20` of `parkBox`. -/
-- tier: T0
@[simp]
theorem parkBox_xMax : parkBox.xMax = -7 / 20 := by
  simp [parkBox]
  norm_num

/-- Lower `y`-endpoint `0` of `parkBox`. -/
-- tier: T0
@[simp]
theorem parkBox_yMin : parkBox.yMin = 0 := by
  simp [parkBox]

/-- Upper `y`-endpoint `1 / 4` of `parkBox`. -/
-- tier: T0
@[simp]
theorem parkBox_yMax : parkBox.yMax = 1 / 4 := by
  simp [parkBox]

/-- `quarterSquare = [0, 1/4]²` is contained in `workBox`. -/
-- tier: T0
theorem quarterSquare_subset_workBox : quarterSquare.toSet ⊆ workBox.toSet :=
  AxisRect.toSet_mono (by simp; norm_num) (by simp; norm_num)
    (by simp; norm_num) (by simp)

/-- Pointwise evaluation of `listToDiskIsotopy hr₀ (Ps₂ ++ Ps₁)` applies `Ps₁` first and `Ps₂`
second (`docs/cmpp/geometry_spec.md` §3.2). -/
-- tier: T1
theorem listToDiskIsotopy_append_d {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    (Ps₂ Ps₁ : List (CompactlySupportedPlanarHamiltonian r₀))
    (t : ℝ) (y : EuclideanPlane) :
    (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy hr₀ (Ps₂ ++ Ps₁)).d (t, y) =
      (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy hr₀ Ps₂).d (t,
        (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy hr₀ Ps₁).d (t, y)) := by
  induction Ps₂ with
  | nil =>
    rw [List.nil_append, listToDiskIsotopy_nil_d]
  | cons P Ps₂ ih =>
    rw [List.cons_append, listToDiskIsotopy_cons_d, listToDiskIsotopy_cons_d, ih]

/-- Concatenation of two lists of autonomous planar Hamiltonians remains autonomous. -/
-- tier: T1
theorem listToDiskIsotopy_autonomous_append {r₀ : ℝ}
    {Ps₂ Ps₁ : List (CompactlySupportedPlanarHamiltonian r₀)}
    (h₂ : ∀ H ∈ Ps₂, H.IsAutonomous) (h₁ : ∀ H ∈ Ps₁, H.IsAutonomous) :
    ∀ H ∈ Ps₂ ++ Ps₁, H.IsAutonomous :=
  List.forall_mem_append.mpr ⟨h₂, h₁⟩

/-- The canonical workbench support ball `B((0, -7/20), 3/10)` lies strictly inside
`Metric.ball 0 cmppR0` (`7/20 + 3/10 = 13/20 ≤ 17/20`). -/
-- tier: T1
theorem workbenchBall_subset_cmppBall :
    Metric.ball workbenchCenter workbenchRadius ⊆ Metric.ball (0 : EuclideanPlane) cmppR0 := by
  refine ball_subset_ball_zero_of_norm_add_le ?_
  have hnorm : ‖workbenchCenter‖ = 7 / 20 := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp only [Fin.isValue, workbenchCenter_zero, workbenchCenter_one, Real.norm_eq_abs, sq_abs]
    rw [show (0 : ℝ) ^ 2 + (-7 / 20) ^ 2 = (7 / 20) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [hnorm, workbenchRadius, cmppR0]
  norm_num

/-- Every point `z` in the upper half-plane `z 1 ≥ 0` lies strictly outside
`Metric.ball workbenchCenter workbenchRadius`. -/
-- tier: T1
theorem notMem_workbenchBall_of_nonneg_y {z : EuclideanPlane} (hz : 0 ≤ z 1) :
    z ∉ Metric.ball workbenchCenter workbenchRadius := by
  rw [Metric.mem_ball, dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp only [Fin.isValue, PiLp.sub_apply, workbenchCenter_zero, workbenchCenter_one, sub_zero,
    Real.norm_eq_abs, sq_abs, workbenchRadius, not_lt]
  have h1 : (7 / 20 : ℝ) ≤ z 1 - (-7 / 20) := by linarith
  have hsq : (3 / 10 : ℝ) ^ 2 ≤ (z 0) ^ 2 + (z 1 - (-7 / 20)) ^ 2 := by
    nlinarith [sq_nonneg (z 0)]
  calc
    (3 / 10 : ℝ) = Real.sqrt ((3 / 10 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt ((z 0) ^ 2 + (z 1 - (-7 / 20)) ^ 2) := Real.sqrt_le_sqrt hsq

/-- `parkBox` is contained in `workBox`. -/
-- tier: T1
theorem parkBox_subset_workBox : parkBox.toSet ⊆ workBox.toSet :=
  AxisRect.toSet_mono (by simp) (by simp; norm_num) (by simp; norm_num) (by simp)

/-- Translating `parkBox` by `(+3/5, 0)` recovers `quarterSquare`. -/
-- tier: T1
theorem parkBox_translate_return : parkBox.translate (3 / 5) 0 = quarterSquare := by
  ext <;> simp <;> norm_num

/-- For `ε ≤ 1 / 40`, the open expansion `workBox.openExpand ε` lies inside
`Metric.ball 0 cmppR0` (`(5/8)² + (1/2)² = 41/64 < 289/400`). -/
-- tier: T1
theorem workBox_openExpand_subset_cmppBall {ε : ℝ} (hε : ε ≤ 1 / 40) :
    workBox.openExpand ε ⊆ Metric.ball (0 : EuclideanPlane) cmppR0 := by
  intro p hp
  rw [AxisRect.mem_openExpand_iff, workBox_xMin, workBox_xMax, workBox_yMin, workBox_yMax] at hp
  rw [Metric.mem_ball, dist_zero_right, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp only [Fin.isValue, Real.norm_eq_abs, sq_abs, cmppR0]
  have hx_lo : (-5 / 8 : ℝ) < p 0 := by linarith [hp.1.1]
  have hx_hi : p 0 < 5 / 8 := by linarith [hp.1.2]
  have hy_lo : (-1 / 2 : ℝ) < p 1 := by linarith [hp.2.1]
  have hy_hi : p 1 < 1 / 2 := by linarith [hp.2.2]
  refine (Real.sqrt_lt' (by norm_num)).mpr ?_
  nlinarith

/-- Endpoint characterization of `A.toSet ⊆ B.toSet` for nonempty `AxisRect`s. -/
-- tier: T1
theorem AxisRect.toSet_subset_toSet_iff (A B : AxisRect) :
    A.toSet ⊆ B.toSet ↔
      B.xMin ≤ A.xMin ∧ A.xMax ≤ B.xMax ∧ B.yMin ≤ A.yMin ∧ A.yMax ≤ B.yMax := by
  constructor
  · intro h
    have hp_min : (WithLp.toLp 2 ![A.xMin, A.yMin] : EuclideanPlane) ∈ A.toSet := by
      rw [AxisRect.mem_toSet_iff]
      exact ⟨⟨le_rfl, A.hx⟩, ⟨le_rfl, A.hy⟩⟩
    have hp_max : (WithLp.toLp 2 ![A.xMax, A.yMax] : EuclideanPlane) ∈ A.toSet := by
      rw [AxisRect.mem_toSet_iff]
      exact ⟨⟨A.hx, le_rfl⟩, ⟨A.hy, le_rfl⟩⟩
    have hmin := (AxisRect.mem_toSet_iff B _).mp (h hp_min)
    have hmax := (AxisRect.mem_toSet_iff B _).mp (h hp_max)
    exact ⟨hmin.1.1, hmax.1.2, hmin.2.1, hmax.2.2⟩
  · rintro ⟨hx₁, hx₂, hy₁, hy₂⟩
    exact AxisRect.toSet_mono hx₁ hx₂ hy₁ hy₂

/-- Two `AxisRect`s with equal underlying sets are equal. -/
-- tier: T1
theorem AxisRect.toSet_injective {A B : AxisRect} (h : A.toSet = B.toSet) : A = B := by
  obtain ⟨hx₁, hx₂, hy₁, hy₂⟩ := (AxisRect.toSet_subset_toSet_iff A B).mp h.le
  obtain ⟨hx₁', hx₂', hy₁', hy₂'⟩ := (AxisRect.toSet_subset_toSet_iff B A).mp h.ge
  exact AxisRect.ext (le_antisymm hx₁' hx₁) (le_antisymm hx₂ hx₂')
    (le_antisymm hy₁' hy₁) (le_antisymm hy₂ hy₂')

/-- Convexity of `AxisRect`: if both `R` and `R.translate dx dy` lie in `B`, then
`R.tubeRect dx dy` also lies in `B`. -/
-- tier: T1
theorem AxisRect.tubeRect_subset_of_subset {R B : AxisRect} {dx dy : ℝ}
    (hR : R.toSet ⊆ B.toSet) (hT : (R.translate dx dy).toSet ⊆ B.toSet) :
    (R.tubeRect dx dy).toSet ⊆ B.toSet := by
  obtain ⟨hx₁, hx₂, hy₁, hy₂⟩ := (AxisRect.toSet_subset_toSet_iff R B).mp hR
  obtain ⟨htx₁, htx₂, hty₁, hty₂⟩ := (AxisRect.toSet_subset_toSet_iff _ B).mp hT
  simp only [AxisRect.translate_xMin, AxisRect.translate_xMax, AxisRect.translate_yMin,
    AxisRect.translate_yMax] at htx₁ htx₂ hty₁ hty₂
  exact AxisRect.toSet_mono (le_min hx₁ htx₁) (max_le hx₂ htx₂)
    (le_min hy₁ hty₁) (max_le hy₂ hty₂)

/-- If `R.toSet ⊆ workBox.toSet` and `ε ≤ 1 / 40`, then `R.openExpand ε` lies inside
`Metric.ball 0 cmppR0`. -/
-- tier: T1
theorem openExpand_subset_cmppBall_of_subset_workBox {R : AxisRect}
    (hR : R.toSet ⊆ workBox.toSet) {ε : ℝ} (hε : ε ≤ 1 / 40) :
    R.openExpand ε ⊆ Metric.ball (0 : EuclideanPlane) cmppR0 := by
  obtain ⟨hx₁, hx₂, hy₁, hy₂⟩ := (AxisRect.toSet_subset_toSet_iff R workBox).mp hR
  refine Subset.trans (fun p hp ↦ ?_) (workBox_openExpand_subset_cmppBall hε)
  rw [AxisRect.mem_openExpand_iff] at hp ⊢
  exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩,
    ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩

/-! ## 1. Disjoint `AxisRect` Open-Expansion & Obstacle-Avoiding L1 Translation -/

/-- Exact coordinate separation characterization of `Disjoint A.toSet B.toSet` for closed
axis-parallel rectangles (`docs/cmpp/geometry_spec.md` §3.2). -/
-- tier: T1
theorem AxisRect.disjoint_iff (A B : AxisRect) :
    Disjoint A.toSet B.toSet ↔
      A.xMax < B.xMin ∨ B.xMax < A.xMin ∨ A.yMax < B.yMin ∨ B.yMax < A.yMin := by
  constructor
  · intro hdisj
    by_contra! h
    obtain ⟨hx₁, hx₂, hy₁, hy₂⟩ := h
    let p : EuclideanPlane := WithLp.toLp 2 ![max A.xMin B.xMin, max A.yMin B.yMin]
    have hpA : p ∈ A.toSet := by
      rw [AxisRect.mem_toSet_iff]
      exact ⟨⟨le_max_left _ _, max_le A.hx hx₁⟩, ⟨le_max_left _ _, max_le A.hy hy₁⟩⟩
    have hpB : p ∈ B.toSet := by
      rw [AxisRect.mem_toSet_iff]
      exact ⟨⟨le_max_right _ _, max_le hx₂ B.hx⟩, ⟨le_max_right _ _, max_le hy₂ B.hy⟩⟩
    exact Set.disjoint_left.mp hdisj hpA hpB
  · rintro (hx₁ | hx₂ | hy₁ | hy₂)
    · rw [Set.disjoint_left]
      intro p hpA hpB
      rw [AxisRect.mem_toSet_iff] at hpA hpB
      linarith [hpA.1.2, hpB.1.1]
    · rw [Set.disjoint_left]
      intro p hpA hpB
      rw [AxisRect.mem_toSet_iff] at hpA hpB
      linarith [hpA.1.1, hpB.1.2]
    · rw [Set.disjoint_left]
      intro p hpA hpB
      rw [AxisRect.mem_toSet_iff] at hpA hpB
      linarith [hpA.2.2, hpB.2.1]
    · rw [Set.disjoint_left]
      intro p hpA hpB
      rw [AxisRect.mem_toSet_iff] at hpA hpB
      linarith [hpA.2.1, hpB.2.2]

/-- Rigid translation by `(dx, dy)` preserves disjointness of `AxisRect`s. -/
-- tier: T1
theorem AxisRect.disjoint_translate_iff (A B : AxisRect) (dx dy : ℝ) :
    Disjoint (A.translate dx dy).toSet (B.translate dx dy).toSet ↔ Disjoint A.toSet B.toSet := by
  simp only [AxisRect.disjoint_iff, AxisRect.translate_xMin, AxisRect.translate_xMax,
    AxisRect.translate_yMin, AxisRect.translate_yMax, add_lt_add_iff_right]

/-- Monotonicity of `AxisRect.openExpand` in the margin `ε`. -/
-- tier: T1
theorem AxisRect.openExpand_mono (R : AxisRect) {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
    R.openExpand ε₁ ⊆ R.openExpand ε₂ := by
  intro p hp
  rw [AxisRect.mem_openExpand_iff] at hp ⊢
  exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩,
    ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩

/-- Disjoint closed `AxisRect`s admit a positive `ε`-expansion `A.openExpand ε` remaining disjoint
from `B.toSet`. -/
-- tier: T1
theorem exists_pos_disjoint_openExpand_of_disjoint {A B : AxisRect}
    (h : Disjoint A.toSet B.toSet) :
    ∃ ε : ℝ, 0 < ε ∧ Disjoint (A.openExpand ε) B.toSet := by
  rcases (AxisRect.disjoint_iff A B).mp h with hx₁ | hx₂ | hy₁ | hy₂
  · refine ⟨(B.xMin - A.xMax) / 2, by linarith, ?_⟩
    exact (AxisRect.disjoint_toSet_openExpand_of_le_xMin (by linarith)).symm
  · refine ⟨(A.xMin - B.xMax) / 2, by linarith, ?_⟩
    exact (AxisRect.disjoint_toSet_openExpand_of_xMax_le (by linarith)).symm
  · refine ⟨(B.yMin - A.yMax) / 2, by linarith, ?_⟩
    exact (AxisRect.disjoint_toSet_openExpand_of_le_yMin (by linarith)).symm
  · refine ⟨(A.yMin - B.yMax) / 2, by linarith, ?_⟩
    exact (AxisRect.disjoint_toSet_openExpand_of_yMax_le (by linarith)).symm

/-- Any `AxisRect` `A` disjoint from a finite family `(Q k)` (`k ∈ obs`) admits a uniform
`ε ∈ (0, 1/40]` such that `A.openExpand ε` avoids every `(Q k).toSet`. -/
-- tier: T1
theorem exists_pos_openExpand_disjoint_finset {ι : Type*}
    (A : AxisRect) (obs : Finset ι) (Q : ι → AxisRect)
    (hdisj : ∀ k ∈ obs, Disjoint A.toSet (Q k).toSet) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 40 ∧ ∀ k ∈ obs, Disjoint (A.openExpand ε) (Q k).toSet := by
  classical
  induction obs using Finset.induction_on with
  | empty =>
    exact ⟨1 / 40, by norm_num, le_rfl, fun _ hk ↦ absurd hk (Finset.notMem_empty _)⟩
  | @insert a s _ ih =>
    obtain ⟨ε₁, hε₁_pos, hε₁_le, hε₁_disj⟩ :=
      ih (fun k hk ↦ hdisj k (Finset.mem_insert_of_mem hk))
    obtain ⟨ε₂, hε₂_pos, hε₂_disj⟩ :=
      exists_pos_disjoint_openExpand_of_disjoint (hdisj a (Finset.mem_insert_self a s))
    refine ⟨min ε₁ ε₂, lt_min hε₁_pos hε₂_pos, (min_le_left _ _).trans hε₁_le, ?_⟩
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hks
    · exact hε₂_disj.mono_left (A.openExpand_mono (min_le_right _ _))
    · exact (hε₁_disj k hks).mono_left (A.openExpand_mono (min_le_left _ _))

/-- Single-move autonomous L1 translation of an `AxisRect` `R` by `(dx, dy)` inside `workBox`
avoiding any `Finset` of obstacle rectangles `(Q k)` (`k ∈ obs`). -/
-- tier: T1
theorem exists_axisRect_translate_avoiding_finset {ι : Type*}
    (R : AxisRect) (dx dy : ℝ) (obs : Finset ι) (Q : ι → AxisRect)
    (htube_wb : (R.tubeRect dx dy).toSet ⊆ workBox.toSet)
    (hdisj : ∀ k ∈ obs, Disjoint (R.tubeRect dx dy).toSet (Q k).toSet) :
    ∃ P : CompactlySupportedPlanarHamiltonian cmppR0,
      P.IsAutonomous ∧
      (∀ y ∈ R.toSet, P.toDiskIsotopy.d (1, y) = y + WithLp.toLp 2 ![dx, dy]) ∧
      (fun y ↦ P.toDiskIsotopy.d (1, y)) '' R.toSet = (R.translate dx dy).toSet ∧
      (∀ k ∈ obs, ∀ y ∈ (Q k).toSet, P.toDiskIsotopy.d (1, y) = y) := by
  obtain ⟨ε, hε_pos, hε_le, hε_disj⟩ :=
    exists_pos_openExpand_disjoint_finset (R.tubeRect dx dy) obs Q hdisj
  have hball := openExpand_subset_cmppBall_of_subset_workBox htube_wb hε_le
  obtain ⟨P, hauto, htrans, himg, hfix⟩ :=
    exists_axisRect_translation_hamiltonian cmppR0_mem_Ioo R dx dy hε_pos hball
  refine ⟨P, hauto, htrans, himg, fun k hk y hy ↦ hfix y ?_⟩
  exact fun hmem ↦ Set.disjoint_left.mp (hε_disj k hk) hmem hy

/-! ## 2. 1D Horizontal Sliding Lemmas -/

/-- General rightward tube-separation lemma: if `A` and `B` are disjoint, `B.xMin ≤ A.xMax`, and
`0 ≤ dx`, then `(A.tubeRect dx 0).toSet` remains disjoint from `B.toSet` (covers both unmoved
leftward pieces and newly inserted target rectangles in Part-the-Sea / Un-part-the-Sea). -/
-- tier: T1
theorem disjoint_tubeRect_right_of_xMin_le_xMax {A B : AxisRect}
    (hdisj : Disjoint A.toSet B.toSet) (hle : B.xMin ≤ A.xMax) {dx : ℝ} (hdx : 0 ≤ dx) :
    Disjoint (A.tubeRect dx 0).toSet B.toSet := by
  rw [AxisRect.disjoint_iff] at hdisj ⊢
  simp only [AxisRect.tubeRect_xMin, AxisRect.tubeRect_xMax, AxisRect.tubeRect_yMin,
    AxisRect.tubeRect_yMax, add_zero, min_self, max_self]
  rw [min_eq_left (by linarith), max_eq_right (by linarith)]
  rcases hdisj with hx₁ | hx₂ | hy₁ | hy₂
  · linarith
  · exact Or.inr (Or.inl hx₂)
  · exact Or.inr (Or.inr (Or.inl hy₁))
  · exact Or.inr (Or.inr (Or.inr hy₂))

/-- Rightward tube-separation for a maximal-`xMin` active piece `A` against an unmoved piece `B`
with `B.xMin ≤ A.xMin`. -/
-- tier: T1
theorem disjoint_tubeRect_right_of_xMin_le {A B : AxisRect}
    (hdisj : Disjoint A.toSet B.toSet) (hle : B.xMin ≤ A.xMin) {dx : ℝ} (hdx : 0 ≤ dx) :
    Disjoint (A.tubeRect dx 0).toSet B.toSet :=
  disjoint_tubeRect_right_of_xMin_le_xMax hdisj (hle.trans A.hx) hdx

/-- Rightward tube-separation against a previously shifted piece `B.translate dx 0` when
`A.xMin ≤ B.xMin` and `0 ≤ dx`. -/
-- tier: T1
theorem disjoint_tubeRect_right_translate_of_xMin_le {A B : AxisRect}
    (hdisj : Disjoint A.toSet B.toSet) (hle : A.xMin ≤ B.xMin) {dx : ℝ} (hdx : 0 ≤ dx) :
    Disjoint (A.tubeRect dx 0).toSet (B.translate dx 0).toSet := by
  rw [AxisRect.disjoint_iff] at hdisj ⊢
  simp only [AxisRect.tubeRect_xMin, AxisRect.tubeRect_xMax, AxisRect.tubeRect_yMin,
    AxisRect.tubeRect_yMax, AxisRect.translate_xMin, AxisRect.translate_xMax,
    AxisRect.translate_yMin, AxisRect.translate_yMax, add_zero, min_self, max_self]
  rw [min_eq_left (by linarith), max_eq_right (by linarith)]
  rcases hdisj with hx₁ | hx₂ | hy₁ | hy₂
  · exact Or.inl (by linarith)
  · linarith [B.hx]
  · exact Or.inr (Or.inr (Or.inl hy₁))
  · exact Or.inr (Or.inr (Or.inr hy₂))

/-- Leftward tube-separation for a minimal-`xMin` active piece `A` against an unmoved piece `B`
with `A.xMin ≤ B.xMin`. -/
-- tier: T1
theorem disjoint_tubeRect_left_of_xMin_le {A B : AxisRect}
    (hdisj : Disjoint A.toSet B.toSet) (hle : A.xMin ≤ B.xMin) {dx : ℝ} (hdx : 0 ≤ dx) :
    Disjoint (A.tubeRect (-dx) 0).toSet B.toSet := by
  rw [AxisRect.disjoint_iff] at hdisj ⊢
  simp only [AxisRect.tubeRect_xMin, AxisRect.tubeRect_xMax, AxisRect.tubeRect_yMin,
    AxisRect.tubeRect_yMax, add_zero, min_self, max_self]
  rw [min_eq_right (by linarith), max_eq_left (by linarith)]
  rcases hdisj with hx₁ | hx₂ | hy₁ | hy₂
  · exact Or.inl hx₁
  · linarith [B.hx]
  · exact Or.inr (Or.inr (Or.inl hy₁))
  · exact Or.inr (Or.inr (Or.inr hy₂))

/-- Leftward tube-separation against a previously shifted piece `B.translate (-dx) 0` when
`B.xMin ≤ A.xMin` and `0 ≤ dx`. -/
-- tier: T1
theorem disjoint_tubeRect_left_translate_of_xMin_le {A B : AxisRect}
    (hdisj : Disjoint A.toSet B.toSet) (hle : B.xMin ≤ A.xMin) {dx : ℝ} (hdx : 0 ≤ dx) :
    Disjoint (A.tubeRect (-dx) 0).toSet (B.translate (-dx) 0).toSet := by
  rw [AxisRect.disjoint_iff] at hdisj ⊢
  simp only [AxisRect.tubeRect_xMin, AxisRect.tubeRect_xMax, AxisRect.tubeRect_yMin,
    AxisRect.tubeRect_yMax, AxisRect.translate_xMin, AxisRect.translate_xMax,
    AxisRect.translate_yMin, AxisRect.translate_yMax, add_zero, min_self, max_self]
  rw [min_eq_right (by linarith), max_eq_left (by linarith)]
  rcases hdisj with hx₁ | hx₂ | hy₁ | hy₂
  · linarith [A.hx]
  · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (Or.inl hy₁))
  · exact Or.inr (Or.inr (Or.inr hy₂))

/-- Symmetry of horizontal translation tubes: translating `R.translate dx 0` back by `(-dx, 0)`
sweeps out the exact same bounding rectangle `R.tubeRect dx 0`. -/
-- tier: T1
theorem tubeRect_translate_neg_x (R : AxisRect) (dx : ℝ) :
    (R.translate dx 0).tubeRect (-dx) 0 = R.tubeRect dx 0 := by
  ext
  · simp [min_comm]
  · simp [max_comm]
  · simp
  · simp

/-- **1D Rightward Horizontal Sliding Lemma**
(`MISSION_DIRECTIVE_CMPP.md` §4.2, `docs/cmpp/geometry_spec.md` §3.2):
Any finite pairwise-disjoint family `(R i)` (`i ∈ active`) of `AxisRect`s whose rightward
translation tubes `(R i).tubeRect dx 0` (`0 ≤ dx`) lie inside `workBox` and avoid a finite family
of static obstacles `(Q k)` (`k ∈ static`) can be rigidly translated by `+(dx, 0)` via a finite
list of autonomous planar Hamiltonians while fixing all `(Q k)` pointwise. -/
-- tier: T2
theorem exists_slide_right_hamiltonians.{u, v} {ι : Type u} :
    ∀ {κ : Type v} (active : Finset ι) (R : ι → AxisRect) {dx : ℝ} (_hdx : 0 ≤ dx)
      (static : Finset κ) (Q : κ → AxisRect),
      (active : Set ι).Pairwise (fun i j ↦ Disjoint (R i).toSet (R j).toSet) →
      (∀ i ∈ active, ((R i).tubeRect dx 0).toSet ⊆ workBox.toSet) →
      (∀ i ∈ active, ∀ k ∈ static, Disjoint ((R i).tubeRect dx 0).toSet (Q k).toSet) →
      ∃ Ps : List (CompactlySupportedPlanarHamiltonian cmppR0),
        (∀ H ∈ Ps, H.IsAutonomous) ∧
        (∀ i ∈ active, ∀ y ∈ (R i).toSet,
          (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).d (1, y) =
            y + WithLp.toLp 2 ![dx, 0]) ∧
        (∀ k ∈ static, ∀ y ∈ (Q k).toSet,
          (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).d (1, y) =
            y) := by
  classical
  suffices hmain :
      ∀ (n : ℕ) {κ : Type v} (active : Finset ι) (R : ι → AxisRect) {dx : ℝ} (_hdx : 0 ≤ dx)
        (static : Finset κ) (Q : κ → AxisRect),
        active.card = n →
        (active : Set ι).Pairwise (fun i j ↦ Disjoint (R i).toSet (R j).toSet) →
        (∀ i ∈ active, ((R i).tubeRect dx 0).toSet ⊆ workBox.toSet) →
        (∀ i ∈ active, ∀ k ∈ static, Disjoint ((R i).tubeRect dx 0).toSet (Q k).toSet) →
        ∃ Ps : List (CompactlySupportedPlanarHamiltonian cmppR0),
          (∀ H ∈ Ps, H.IsAutonomous) ∧
          (∀ i ∈ active, ∀ y ∈ (R i).toSet,
            (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).d (1, y) =
              y + WithLp.toLp 2 ![dx, 0]) ∧
          (∀ k ∈ static, ∀ y ∈ (Q k).toSet,
            (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).d (1, y) =
              y) by
    intro κ active R dx hdx static Q hpw hwb hst
    exact @hmain active.card κ active R dx hdx static Q rfl hpw hwb hst
  intro n
  induction n with
  | zero =>
    intro κ active R dx _ static Q hcard _ _ _
    rw [Finset.card_eq_zero.mp hcard]
    refine ⟨[], fun _ h ↦ absurd h List.not_mem_nil,
      fun _ hi ↦ absurd hi (Finset.notMem_empty _), fun _ _ y _ ↦ ?_⟩
    rw [listToDiskIsotopy_nil_d]
  | succ n ih =>
    intro κ active R dx hdx static Q hcard hpw hwb hst
    have hne : active.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image active (fun i ↦ (R i).xMin) hne
    let active' : Finset ι := active.erase i₀
    have hcard' : active'.card = n := by
      change (active.erase i₀).card = n
      rw [Finset.card_erase_of_mem hi₀, hcard]
      rfl
    let obs₁ : Finset (ι ⊕ κ) := active'.disjSum static
    let Q₁ : ι ⊕ κ → AxisRect := Sum.elim R Q
    have hdisj₁ : ∀ s ∈ obs₁, Disjoint ((R i₀).tubeRect dx 0).toSet (Q₁ s).toSet := by
      intro s hs
      rcases s with j | k
      · have hj : j ∈ active' := Finset.inl_mem_disjSum.mp hs
        have hj_act : j ∈ active := Finset.mem_of_mem_erase hj
        have hj_ne : i₀ ≠ j := (Finset.ne_of_mem_erase hj).symm
        exact disjoint_tubeRect_right_of_xMin_le (hpw hi₀ hj_act hj_ne) (hmax j hj_act) hdx
      · have hk : k ∈ static := Finset.inr_mem_disjSum.mp hs
        exact hst i₀ hi₀ k hk
    obtain ⟨P₀, hP₀_auto, hP₀_trans, _, hP₀_fix⟩ :=
      exists_axisRect_translate_avoiding_finset (R i₀) dx 0 obs₁ Q₁ (hwb i₀ hi₀) hdisj₁
    let static' : Finset (Option κ) := insert none (static.map Function.Embedding.some)
    let Q' : Option κ → AxisRect := fun o ↦
      match o with
      | none => (R i₀).translate dx 0
      | some k => Q k
    have hpw' : (active' : Set ι).Pairwise (fun i j ↦ Disjoint (R i).toSet (R j).toSet) :=
      hpw.mono (by intro x hx; exact Finset.mem_of_mem_erase hx)
    have hwb' : ∀ i ∈ active', ((R i).tubeRect dx 0).toSet ⊆ workBox.toSet :=
      fun i hi ↦ hwb i (Finset.mem_of_mem_erase hi)
    have hst' :
        ∀ i ∈ active', ∀ o ∈ static', Disjoint ((R i).tubeRect dx 0).toSet (Q' o).toSet := by
      intro i hi o ho
      have hi_act : i ∈ active := Finset.mem_of_mem_erase hi
      have hi_ne : i ≠ i₀ := Finset.ne_of_mem_erase hi
      rcases Finset.mem_insert.mp ho with rfl | hmap
      · exact disjoint_tubeRect_right_translate_of_xMin_le
          (hpw hi_act hi₀ hi_ne) (hmax i hi_act) hdx
      · rcases Finset.mem_map.mp hmap with ⟨k, hk, rfl⟩
        exact hst i hi_act k hk
    obtain ⟨Ps', hPs'_auto, hPs'_trans, hPs'_fix⟩ :=
      ih active' R hdx static' Q' hcard' hpw' hwb' hst'
    refine ⟨Ps' ++ [P₀],
      listToDiskIsotopy_autonomous_append hPs'_auto (List.forall_mem_singleton.mpr hP₀_auto),
      ?_, ?_⟩
    · intro i hi y hy
      rw [listToDiskIsotopy_append_d, listToDiskIsotopy_singleton_d]
      by_cases heq : i = i₀
      · subst heq
        rw [hP₀_trans y hy]
        have hmem_tr : y + WithLp.toLp 2 ![dx, 0] ∈ ((R i).translate dx 0).toSet := by
          rw [← (R i).image_add_toSet dx 0]
          exact ⟨y, hy, rfl⟩
        exact hPs'_fix none (Finset.mem_insert_self _ _) _ hmem_tr
      · have hi' : i ∈ active' := Finset.mem_erase.mpr ⟨heq, hi⟩
        have hfix₀ : P₀.toDiskIsotopy.d (1, y) = y :=
          hP₀_fix (Sum.inl i) (Finset.inl_mem_disjSum.mpr hi') y hy
        rw [hfix₀]
        exact hPs'_trans i hi' y hy
    · intro k hk y hy
      rw [listToDiskIsotopy_append_d, listToDiskIsotopy_singleton_d]
      have hfix₀ : P₀.toDiskIsotopy.d (1, y) = y :=
        hP₀_fix (Sum.inr k) (Finset.inr_mem_disjSum.mpr hk) y hy
      rw [hfix₀]
      have hk' : some k ∈ static' :=
        Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨k, hk, rfl⟩)
      exact hPs'_fix (some k) hk' y hy

/-- **1D Leftward Horizontal Sliding Lemma (`docs/cmpp/geometry_spec.md` §3.2)**:
Any finite pairwise-disjoint family `(R i)` (`i ∈ active`) of `AxisRect`s whose leftward
translation tubes `(R i).tubeRect (-dx) 0` (`0 ≤ dx`) lie inside `workBox` and avoid a finite
family of static obstacles `(Q k)` (`k ∈ static`) can be rigidly translated by `(-dx, 0)` via a
finite list of autonomous planar Hamiltonians while fixing all `(Q k)` pointwise. -/
-- tier: T2
theorem exists_slide_left_hamiltonians.{u, v} {ι : Type u} :
    ∀ {κ : Type v} (active : Finset ι) (R : ι → AxisRect) {dx : ℝ} (_hdx : 0 ≤ dx)
      (static : Finset κ) (Q : κ → AxisRect),
      (active : Set ι).Pairwise (fun i j ↦ Disjoint (R i).toSet (R j).toSet) →
      (∀ i ∈ active, ((R i).tubeRect (-dx) 0).toSet ⊆ workBox.toSet) →
      (∀ i ∈ active, ∀ k ∈ static, Disjoint ((R i).tubeRect (-dx) 0).toSet (Q k).toSet) →
      ∃ Ps : List (CompactlySupportedPlanarHamiltonian cmppR0),
        (∀ H ∈ Ps, H.IsAutonomous) ∧
        (∀ i ∈ active, ∀ y ∈ (R i).toSet,
          (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).d (1, y) =
            y + WithLp.toLp 2 ![-dx, 0]) ∧
        (∀ k ∈ static, ∀ y ∈ (Q k).toSet,
          (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).d (1, y) =
            y) := by
  classical
  suffices hmain :
      ∀ (n : ℕ) {κ : Type v} (active : Finset ι) (R : ι → AxisRect) {dx : ℝ} (_hdx : 0 ≤ dx)
        (static : Finset κ) (Q : κ → AxisRect),
        active.card = n →
        (active : Set ι).Pairwise (fun i j ↦ Disjoint (R i).toSet (R j).toSet) →
        (∀ i ∈ active, ((R i).tubeRect (-dx) 0).toSet ⊆ workBox.toSet) →
        (∀ i ∈ active, ∀ k ∈ static, Disjoint ((R i).tubeRect (-dx) 0).toSet (Q k).toSet) →
        ∃ Ps : List (CompactlySupportedPlanarHamiltonian cmppR0),
          (∀ H ∈ Ps, H.IsAutonomous) ∧
          (∀ i ∈ active, ∀ y ∈ (R i).toSet,
            (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).d (1, y) =
              y + WithLp.toLp 2 ![-dx, 0]) ∧
          (∀ k ∈ static, ∀ y ∈ (Q k).toSet,
            (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).d (1, y) =
              y) by
    intro κ active R dx hdx static Q hpw hwb hst
    exact @hmain active.card κ active R dx hdx static Q rfl hpw hwb hst
  intro n
  induction n with
  | zero =>
    intro κ active R dx _ static Q hcard _ _ _
    rw [Finset.card_eq_zero.mp hcard]
    refine ⟨[], fun _ h ↦ absurd h List.not_mem_nil,
      fun _ hi ↦ absurd hi (Finset.notMem_empty _), fun _ _ y _ ↦ ?_⟩
    rw [listToDiskIsotopy_nil_d]
  | succ n ih =>
    intro κ active R dx hdx static Q hcard hpw hwb hst
    have hne : active.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image active (fun i ↦ (R i).xMin) hne
    let active' : Finset ι := active.erase i₀
    have hcard' : active'.card = n := by
      change (active.erase i₀).card = n
      rw [Finset.card_erase_of_mem hi₀, hcard]
      rfl
    let obs₁ : Finset (ι ⊕ κ) := active'.disjSum static
    let Q₁ : ι ⊕ κ → AxisRect := Sum.elim R Q
    have hdisj₁ : ∀ s ∈ obs₁, Disjoint ((R i₀).tubeRect (-dx) 0).toSet (Q₁ s).toSet := by
      intro s hs
      rcases s with j | k
      · have hj : j ∈ active' := Finset.inl_mem_disjSum.mp hs
        have hj_act : j ∈ active := Finset.mem_of_mem_erase hj
        have hj_ne : i₀ ≠ j := (Finset.ne_of_mem_erase hj).symm
        exact disjoint_tubeRect_left_of_xMin_le (hpw hi₀ hj_act hj_ne) (hmin j hj_act) hdx
      · have hk : k ∈ static := Finset.inr_mem_disjSum.mp hs
        exact hst i₀ hi₀ k hk
    obtain ⟨P₀, hP₀_auto, hP₀_trans, _, hP₀_fix⟩ :=
      exists_axisRect_translate_avoiding_finset (R i₀) (-dx) 0 obs₁ Q₁ (hwb i₀ hi₀) hdisj₁
    let static' : Finset (Option κ) := insert none (static.map Function.Embedding.some)
    let Q' : Option κ → AxisRect := fun o ↦
      match o with
      | none => (R i₀).translate (-dx) 0
      | some k => Q k
    have hpw' : (active' : Set ι).Pairwise (fun i j ↦ Disjoint (R i).toSet (R j).toSet) :=
      hpw.mono (by intro x hx; exact Finset.mem_of_mem_erase hx)
    have hwb' : ∀ i ∈ active', ((R i).tubeRect (-dx) 0).toSet ⊆ workBox.toSet :=
      fun i hi ↦ hwb i (Finset.mem_of_mem_erase hi)
    have hst' :
        ∀ i ∈ active', ∀ o ∈ static', Disjoint ((R i).tubeRect (-dx) 0).toSet (Q' o).toSet := by
      intro i hi o ho
      have hi_act : i ∈ active := Finset.mem_of_mem_erase hi
      have hi_ne : i ≠ i₀ := Finset.ne_of_mem_erase hi
      rcases Finset.mem_insert.mp ho with rfl | hmap
      · exact disjoint_tubeRect_left_translate_of_xMin_le
          (hpw hi_act hi₀ hi_ne) (hmin i hi_act) hdx
      · rcases Finset.mem_map.mp hmap with ⟨k, hk, rfl⟩
        exact hst i hi_act k hk
    obtain ⟨Ps', hPs'_auto, hPs'_trans, hPs'_fix⟩ :=
      ih active' R hdx static' Q' hcard' hpw' hwb' hst'
    refine ⟨Ps' ++ [P₀],
      listToDiskIsotopy_autonomous_append hPs'_auto (List.forall_mem_singleton.mpr hP₀_auto),
      ?_, ?_⟩
    · intro i hi y hy
      rw [listToDiskIsotopy_append_d, listToDiskIsotopy_singleton_d]
      by_cases heq : i = i₀
      · subst heq
        rw [hP₀_trans y hy]
        have hmem_tr : y + WithLp.toLp 2 ![-dx, 0] ∈ ((R i).translate (-dx) 0).toSet := by
          rw [← (R i).image_add_toSet (-dx) 0]
          exact ⟨y, hy, rfl⟩
        exact hPs'_fix none (Finset.mem_insert_self _ _) _ hmem_tr
      · have hi' : i ∈ active' := Finset.mem_erase.mpr ⟨heq, hi⟩
        have hfix₀ : P₀.toDiskIsotopy.d (1, y) = y :=
          hP₀_fix (Sum.inl i) (Finset.inl_mem_disjSum.mpr hi') y hy
        rw [hfix₀]
        exact hPs'_trans i hi' y hy
    · intro k hk y hy
      rw [listToDiskIsotopy_append_d, listToDiskIsotopy_singleton_d]
      have hfix₀ : P₀.toDiskIsotopy.d (1, y) = y :=
        hP₀_fix (Sum.inr k) (Finset.inr_mem_disjSum.mpr hk) y hy
      rw [hfix₀]
      have hk' : some k ∈ static' :=
        Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨k, hk, rfl⟩)
      exact hPs'_fix (some k) hk' y hy

/-! ## 3. Single-Piece Step & Relocation Theorem RT (`exists_relocation_hamiltonians`) -/

/-- Area-preserving diagonal-stretch-and-translate affine map sending `P.center` to `P'.center`
with horizontal scaling `exp (-μ)` and vertical scaling `exp μ`. -/
noncomputable def rectAffineMap (P P' : AxisRect) (μ : ℝ) (y : EuclideanPlane) :
    EuclideanPlane :=
  P'.center + WithLp.toLp 2
    ![Real.exp (-μ) * (y 0 - P.center 0), Real.exp μ * (y 1 - P.center 1)]

/-- First coordinate of `rectAffineMap P P' μ y`. -/
-- tier: T0
@[simp]
theorem rectAffineMap_zero (P P' : AxisRect) (μ : ℝ) (y : EuclideanPlane) :
    rectAffineMap P P' μ y 0 = P'.center 0 + Real.exp (-μ) * (y 0 - P.center 0) := by
  simp [rectAffineMap]

/-- Second coordinate of `rectAffineMap P P' μ y`. -/
-- tier: T0
@[simp]
theorem rectAffineMap_one (P P' : AxisRect) (μ : ℝ) (y : EuclideanPlane) :
    rectAffineMap P P' μ y 1 = P'.center 1 + Real.exp μ * (y 1 - P.center 1) := by
  rw [rectAffineMap]
  simp

/-- Center of `R.translate dx dy` equals `R.center + ![dx, dy]`. -/
-- tier: T1
theorem AxisRect.translate_center (R : AxisRect) (dx dy : ℝ) :
    (R.translate dx dy).center = R.center + WithLp.toLp 2 ![dx, dy] := by
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, AxisRect.center_zero, AxisRect.translate_xMin,
      AxisRect.translate_xMax, PiLp.add_apply, Matrix.cons_val_zero]
    ring
  · simp only [Fin.mk_one, AxisRect.center_one, AxisRect.translate_yMin,
      AxisRect.translate_yMax, PiLp.add_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring

/-- Coordinate and width/height bounds for any `AxisRect` contained in
`quarterSquare = [0, 1/4]²`. -/
-- tier: T1
theorem AxisRect.bounds_of_subset_quarterSquare {R : AxisRect}
    (hR : R.toSet ⊆ quarterSquare.toSet) :
    0 ≤ R.xMin ∧ R.xMax ≤ 1 / 4 ∧ 0 ≤ R.yMin ∧ R.yMax ≤ 1 / 4 ∧
      R.width ≤ 1 / 4 ∧ R.height ≤ 1 / 4 := by
  obtain ⟨hx₁, hx₂, hy₁, hy₂⟩ := (AxisRect.toSet_subset_toSet_iff R quarterSquare).mp hR
  simp only [quarterSquare_xMin, quarterSquare_xMax, quarterSquare_yMin,
    quarterSquare_yMax] at hx₁ hx₂ hy₁ hy₂
  exact ⟨hx₁, hx₂, hy₁, hy₂, by unfold AxisRect.width; linarith,
    by unfold AxisRect.height; linarith⟩

/-- `rectAffineMap P P' μ` sends `P.center` to `P'.center`. -/
-- tier: T1
@[simp]
theorem rectAffineMap_center (P P' : AxisRect) (μ : ℝ) :
    rectAffineMap P P' μ P.center = P'.center := by
  ext i
  fin_cases i <;> simp

/-- Under matching scaled width and height (`P'.width = exp (-μ) * P.width`,
`P'.height = exp μ * P.height`), `rectAffineMap P P' μ` maps `P.toSet` into `P'.toSet`. -/
-- tier: T1
theorem rectAffineMap_mem_toSet {P P' : AxisRect} {μ : ℝ}
    (hw : P'.width = Real.exp (-μ) * P.width)
    (hh : P'.height = Real.exp μ * P.height)
    {y : EuclideanPlane} (hy : y ∈ P.toSet) :
    rectAffineMap P P' μ y ∈ P'.toSet := by
  obtain ⟨hx, hy_c⟩ := P.abs_sub_center_le_half_of_mem hy
  have hdx : |Real.exp (-μ) * (y 0 - P.center 0)| ≤ P'.width / 2 := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _), hw]
    calc
      Real.exp (-μ) * |y 0 - P.center 0| ≤ Real.exp (-μ) * (P.width / 2) :=
        mul_le_mul_of_nonneg_left hx (Real.exp_nonneg _)
      _ = Real.exp (-μ) * P.width / 2 := by ring
  have hdy : |Real.exp μ * (y 1 - P.center 1)| ≤ P'.height / 2 := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _), hh]
    calc
      Real.exp μ * |y 1 - P.center 1| ≤ Real.exp μ * (P.height / 2) :=
        mul_le_mul_of_nonneg_left hy_c (Real.exp_nonneg _)
      _ = Real.exp μ * P.height / 2 := by ring
  rw [abs_le] at hdx hdy
  rw [AxisRect.mem_toSet_iff]
  simp only [Fin.isValue, rectAffineMap_zero, rectAffineMap_one, P'.center_zero,
    P'.center_one, Set.mem_Icc]
  unfold AxisRect.width at hdx
  unfold AxisRect.height at hdy
  exact ⟨⟨by linarith [hdx.1], by linarith [hdx.2]⟩, ⟨by linarith [hdy.1], by linarith [hdy.2]⟩⟩

/-- Translating `rectAffineMap P (P'.translate dx dy) μ y` by `(-dx, -dy)` yields
`rectAffineMap P P' μ y`. -/
-- tier: T1
theorem rectAffineMap_translate_target_add (P P' : AxisRect) (dx dy μ : ℝ)
    (y : EuclideanPlane) :
    rectAffineMap P (P'.translate dx dy) μ y + WithLp.toLp 2 ![-dx, -dy] =
      rectAffineMap P P' μ y := by
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, PiLp.add_apply, rectAffineMap_zero, AxisRect.center_zero,
      AxisRect.translate_xMin, AxisRect.translate_xMax, Matrix.cons_val_zero]
    ring
  · simp only [Fin.mk_one, PiLp.add_apply, rectAffineMap_one, AxisRect.center_one,
      AxisRect.translate_yMin, AxisRect.translate_yMax, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    ring

/-- Bridge from affine image equality `(exp (-μ) * x + ax, exp μ * y + ay) '' P.toSet = P'.toSet`
to `P'.width = exp (-μ) * P.width`, `P'.height = exp μ * P.height`, and pointwise equality with
`rectAffineMap P P' μ` (used by Milestone A4 `Realize.lean` and Gate G5). -/
-- tier: T1
theorem eq_rectAffineMap_of_image_eq {P P' : AxisRect} {μ ax ay : ℝ}
    (himg : (fun p : EuclideanPlane ↦
      WithLp.toLp 2 ![Real.exp (-μ) * p 0 + ax, Real.exp μ * p 1 + ay]) '' P.toSet = P'.toSet) :
    P'.width = Real.exp (-μ) * P.width ∧
    P'.height = Real.exp μ * P.height ∧
    ∀ y : EuclideanPlane,
      WithLp.toLp 2 ![Real.exp (-μ) * y 0 + ax, Real.exp μ * y 1 + ay] =
        rectAffineMap P P' μ y := by
  have hsx : 0 < Real.exp (-μ) := Real.exp_pos _
  have hsy : 0 < Real.exp μ := Real.exp_pos _
  let R_im : AxisRect :=
    { xMin := Real.exp (-μ) * P.xMin + ax
      xMax := Real.exp (-μ) * P.xMax + ax
      yMin := Real.exp μ * P.yMin + ay
      yMax := Real.exp μ * P.yMax + ay
      hx := by nlinarith [P.hx]
      hy := by nlinarith [P.hy] }
  have him_eq : R_im.toSet = P'.toSet := by
    rw [← himg, P.image_posScaleTranslate hsx hsy ax ay]
    rfl
  have hR_eq : R_im = P' := AxisRect.toSet_injective him_eq
  have hxMin : P'.xMin = Real.exp (-μ) * P.xMin + ax := by rw [← hR_eq]
  have hxMax : P'.xMax = Real.exp (-μ) * P.xMax + ax := by rw [← hR_eq]
  have hyMin : P'.yMin = Real.exp μ * P.yMin + ay := by rw [← hR_eq]
  have hyMax : P'.yMax = Real.exp μ * P.yMax + ay := by rw [← hR_eq]
  refine ⟨?_, ?_, fun y ↦ ?_⟩
  · unfold AxisRect.width
    rw [hxMax, hxMin]
    ring
  · unfold AxisRect.height
    rw [hyMax, hyMin]
    ring
  · ext i
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, rectAffineMap_zero, AxisRect.center_zero,
        hxMin, hxMax]
      ring
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, rectAffineMap_one,
        AxisRect.center_one, hyMin, hyMax]
      ring

/-- **Single-Piece Pipeline A (`docs/cmpp/geometry_spec.md` §3.2)**:
Given a maximal-`xMin` remaining source piece `i₀ ∈ rem` (`Disjoint done rem`), constructs a
finite list `Ps` of autonomous planar Hamiltonians that maps `P i₀` via
`rectAffineMap (P i₀) ((P' i₀).translate (-3/5) 0) (μ i₀)` onto its parked target slot while
fixing every already-parked `(P' j).translate (-3/5) 0` (`j ∈ done`) and every remaining source
`P k` (`k ∈ rem.erase i₀`) pointwise. -/
-- tier: T2
theorem exists_single_piece_relocate_to_park {ι : Type*}
    (P P' : ι → AxisRect) (μ : ι → ℝ)
    (hP_sub : ∀ i : ι, (P i).toSet ⊆ quarterSquare.toSet)
    (hP'_sub : ∀ i : ι, (P' i).toSet ⊆ quarterSquare.toSet)
    (hP_disj : Pairwise (Disjoint on fun i : ι ↦ (P i).toSet))
    (hP'_disj : Pairwise (Disjoint on fun i : ι ↦ (P' i).toSet))
    (hw : ∀ i : ι, (P' i).width = Real.exp (-μ i) * (P i).width)
    (hh : ∀ i : ι, (P' i).height = Real.exp (μ i) * (P i).height)
    (hwb : ∀ i : ι,
      (max ((P i).width / 2) (Real.exp (-μ i) * ((P i).width / 2))) ^ 2 +
        (max ((P i).height / 2) (Real.exp (μ i) * ((P i).height / 2))) ^ 2 <
        (3 / 20 : ℝ) ^ 2)
    (done rem : Finset ι) (hdisj_dr : Disjoint done rem)
    {i₀ : ι} (hi₀ : i₀ ∈ rem) (hmax_x : ∀ k ∈ rem, (P k).xMin ≤ (P i₀).xMin) :
    let S' : ι → AxisRect := fun i ↦ (P' i).translate (-3 / 5) 0
    ∃ Ps : List (CompactlySupportedPlanarHamiltonian cmppR0),
      (∀ H ∈ Ps, H.IsAutonomous) ∧
      (∀ y ∈ (P i₀).toSet,
        (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).d (1, y) =
          rectAffineMap (P i₀) (S' i₀) (μ i₀) y) ∧
      (∀ j ∈ done, ∀ y ∈ (S' j).toSet,
        (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).d (1, y) = y) ∧
      (∀ k ∈ rem, k ≠ i₀ → ∀ y ∈ (P k).toSet,
        (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).d (1, y) =
          y) := by
  classical
  intro S'
  let rem' : Finset ι := rem.erase i₀
  have hS'_disj : Pairwise (Disjoint on fun i : ι ↦ (S' i).toSet) := by
    intro a b hab
    exact (AxisRect.disjoint_translate_iff (P' a) (P' b) (-3 / 5) 0).mpr (hP'_disj hab)
  have hS'_sub_park : ∀ i : ι, (S' i).toSet ⊆ parkBox.toSet := by
    intro i
    obtain ⟨hx₁, hx₂, hy₁, hy₂⟩ := AxisRect.bounds_of_subset_quarterSquare (hP'_sub i)
    exact AxisRect.toSet_mono (by simp [S']; linarith) (by simp [S']; linarith)
      (by simp [S']; linarith) (by simp [S']; linarith)
  have hS'_sub_wb : ∀ i : ι, (S' i).toSet ⊆ workBox.toSet :=
    fun i ↦ (hS'_sub_park i).trans parkBox_subset_workBox
  obtain ⟨hx₀_lo, hx₀_hi, hy₀_lo, hy₀_hi, hw₀_hi, hh₀_hi⟩ :=
    AxisRect.bounds_of_subset_quarterSquare (hP_sub i₀)
  have hw₀_nn : 0 ≤ (P i₀).width := (P i₀).width_nonneg
  have hh₀_nn : 0 ≤ (P i₀).height := (P i₀).height_nonneg
  obtain ⟨hx'₀_lo, hx'₀_hi, hy'₀_lo, hy'₀_hi, hw'₀_hi, hh'₀_hi⟩ :=
    AxisRect.bounds_of_subset_quarterSquare (hP'_sub i₀)
  have hw'₀_nn : 0 ≤ (P' i₀).width := (P' i₀).width_nonneg
  have hh'₀_nn : 0 ≤ (P' i₀).height := (P' i₀).height_nonneg
  -- Intermediate rectangles along Pipeline A:
  let R₀ : AxisRect := P i₀
  let R₁ : AxisRect := R₀.translate (3 / 10) 0
  let dy₂a : ℝ := -7 / 20 - R₁.center 1
  let R₂a : AxisRect := R₁.translate 0 dy₂a
  let dx₂b : ℝ := -R₂a.center 0
  let R₂b : AxisRect := R₂a.translate dx₂b 0
  let R₃ : AxisRect :=
    AxisRect.ofCenter workbenchCenter (by positivity : 0 ≤ (P' i₀).width / 2)
      (by positivity : 0 ≤ (P' i₀).height / 2)
  let dx₅a : ℝ := (S' i₀).center 0
  let R₅a : AxisRect := R₃.translate dx₅a 0
  let dy₅b : ℝ := (S' i₀).center 1 + 7 / 20
  -- Workspace inclusions for R₀, R₁, R₂a, R₂b, R₃, R₅a:
  have hR₀_wb : R₀.toSet ⊆ workBox.toSet := (hP_sub i₀).trans quarterSquare_subset_workBox
  have hR₁_wb : R₁.toSet ⊆ workBox.toSet :=
    AxisRect.toSet_mono (by simp [R₁, R₀]; linarith) (by simp [R₁, R₀]; linarith)
      (by simp [R₁, R₀]; linarith) (by simp [R₁, R₀]; linarith)
  have hR₂a_yMin : -19 / 40 ≤ R₂a.yMin := by
    simp only [R₂a, dy₂a, R₁, R₀, AxisRect.translate_yMin, AxisRect.center_one,
      AxisRect.translate_yMax, add_zero]
    unfold AxisRect.height at hh₀_hi
    linarith
  have hR₂a_yMax : R₂a.yMax ≤ -9 / 40 := by
    simp only [R₂a, dy₂a, R₁, R₀, AxisRect.translate_yMax, AxisRect.center_one,
      AxisRect.translate_yMin, add_zero]
    unfold AxisRect.height at hh₀_nn
    linarith [R₀.hy]
  have hR₂a_wb : R₂a.toSet ⊆ workBox.toSet :=
    AxisRect.toSet_mono (by simp [R₂a, R₁, R₀]; linarith) (by simp [R₂a, R₁, R₀]; linarith)
      (by simp; linarith) (by simp; linarith)
  have hR₂b_center : R₂b.center = workbenchCenter := by
    ext c
    fin_cases c
    · simp only [Fin.zero_eta, workbenchCenter_zero, R₂b, dx₂b, AxisRect.center_zero,
        AxisRect.translate_xMin, AxisRect.translate_xMax]
      ring
    · simp only [Fin.mk_one, workbenchCenter_one, R₂b, R₂a, dy₂a, AxisRect.center_one,
        AxisRect.translate_yMin, AxisRect.translate_yMax, add_zero]
      ring
  have hR₂b_wb : R₂b.toSet ⊆ workBox.toSet := by
    have hxMin_b : -1 / 8 ≤ R₂b.xMin := by
      simp only [R₂b, dx₂b, R₂a, R₁, R₀, AxisRect.translate_xMin, AxisRect.center_zero,
        AxisRect.translate_xMax, add_zero]
      unfold AxisRect.width at hw₀_hi
      linarith
    have hxMax_b : R₂b.xMax ≤ 1 / 8 := by
      simp only [R₂b, dx₂b, R₂a, R₁, R₀, AxisRect.translate_xMax, AxisRect.center_zero,
        AxisRect.translate_xMin, add_zero]
      unfold AxisRect.width at hw₀_hi
      linarith
    exact AxisRect.toSet_mono (by simp; linarith) (by simp; linarith)
      (by simp [R₂b]; linarith) (by simp [R₂b]; linarith)
  have hR₃_yMin : -19 / 40 ≤ R₃.yMin := by
    simp only [R₃, AxisRect.ofCenter_yMin, workbenchCenter_one]
    linarith
  have hR₃_yMax : R₃.yMax ≤ -9 / 40 := by
    simp only [R₃, AxisRect.ofCenter_yMax, workbenchCenter_one]
    linarith
  have hR₃_wb : R₃.toSet ⊆ workBox.toSet := by
    refine AxisRect.toSet_mono ?_ ?_ (by simp; linarith) (by simp; linarith)
    · simp only [workBox_xMin, R₃, AxisRect.ofCenter_xMin, workbenchCenter_zero]
      linarith
    · simp only [workBox_xMax, R₃, AxisRect.ofCenter_xMax, workbenchCenter_zero]
      linarith
  have hR₅a_xMin : R₅a.xMin = (S' i₀).xMin := by
    simp only [R₅a, dx₅a, R₃, S', AxisRect.translate_xMin, AxisRect.ofCenter_xMin,
      workbenchCenter_zero, AxisRect.center_zero, AxisRect.translate_xMax, AxisRect.width]
    ring
  have hR₅a_xMax : R₅a.xMax = (S' i₀).xMax := by
    simp only [R₅a, dx₅a, R₃, S', AxisRect.translate_xMax, AxisRect.ofCenter_xMax,
      workbenchCenter_zero, AxisRect.center_zero, AxisRect.translate_xMin, AxisRect.width]
    ring
  have hR₅a_wb : R₅a.toSet ⊆ workBox.toSet := by
    refine AxisRect.toSet_mono ?_ ?_ (by simp [R₅a]; linarith) (by simp [R₅a]; linarith)
    · rw [workBox_xMin, hR₅a_xMin]
      simp only [S', AxisRect.translate_xMin]
      linarith
    · rw [workBox_xMax, hR₅a_xMax]
      simp only [S', AxisRect.translate_xMax]
      linarith
  have hR₅b_eq : R₅a.translate 0 dy₅b = S' i₀ := by
    ext
    · simp [hR₅a_xMin]
    · simp [hR₅a_xMax]
    · simp only [AxisRect.translate_yMin, R₅a, dy₅b, R₃, S', AxisRect.ofCenter_yMin,
        workbenchCenter_one, AxisRect.center_one, AxisRect.translate_yMax, AxisRect.height,
        add_zero]
      ring
    · simp only [AxisRect.translate_yMax, R₅a, dy₅b, R₃, S', AxisRect.ofCenter_yMax,
        workbenchCenter_one, AxisRect.center_one, AxisRect.translate_yMin, AxisRect.height,
        add_zero]
      ring
  -- Obstacle bundle `done ⊕ rem'` for Moves 1, 2a, 2b:
  let obs_dr : Finset (ι ⊕ ι) := done.disjSum rem'
  let Q_dr : ι ⊕ ι → AxisRect := Sum.elim S' P
  -- Move 1: extract R₀ right by (+3/10, 0) into R₁
  have hdisj₁ : ∀ s ∈ obs_dr, Disjoint (R₀.tubeRect (3 / 10) 0).toSet (Q_dr s).toSet := by
    intro s hs
    rcases s with j | k
    · have hj : j ∈ done := Finset.inl_mem_disjSum.mp hs
      obtain ⟨_, hxj_hi, _, _, _, _⟩ := AxisRect.bounds_of_subset_quarterSquare (hP'_sub j)
      rw [AxisRect.disjoint_iff]
      refine Or.inr (Or.inl ?_)
      simp only [Q_dr, Sum.elim_inl, S', AxisRect.translate_xMax, R₀, AxisRect.tubeRect_xMin]
      rw [min_eq_left (by linarith)]
      linarith
    · have hk : k ∈ rem' := Finset.inr_mem_disjSum.mp hs
      have hk_rem : k ∈ rem := Finset.mem_of_mem_erase hk
      have hk_ne : i₀ ≠ k := (Finset.ne_of_mem_erase hk).symm
      exact disjoint_tubeRect_right_of_xMin_le (hP_disj hk_ne) (hmax_x k hk_rem) (by norm_num)
  obtain ⟨P₁, hP₁_auto, hP₁_trans, _, hP₁_fix⟩ :=
    exists_axisRect_translate_avoiding_finset R₀ (3 / 10) 0 obs_dr Q_dr
      (AxisRect.tubeRect_subset_of_subset hR₀_wb hR₁_wb) hdisj₁
  -- Move 2a: drop R₁ vertically by (0, dy₂a) into R₂a
  have hdisj₂a : ∀ s ∈ obs_dr, Disjoint (R₁.tubeRect 0 dy₂a).toSet (Q_dr s).toSet := by
    intro s hs
    rw [AxisRect.disjoint_iff]
    refine Or.inr (Or.inl ?_)
    have htube_xMin : (R₁.tubeRect 0 dy₂a).xMin = (P i₀).xMin + 3 / 10 := by
      simp [R₁, R₀]
    rw [htube_xMin]
    rcases s with j | k
    · obtain ⟨_, hxj_hi, _, _, _, _⟩ := AxisRect.bounds_of_subset_quarterSquare (hP'_sub j)
      simp only [Q_dr, Sum.elim_inl, S', AxisRect.translate_xMax]
      linarith
    · obtain ⟨_, hxk_hi, _, _, _, _⟩ := AxisRect.bounds_of_subset_quarterSquare (hP_sub k)
      simp only [Q_dr, Sum.elim_inr]
      linarith
  obtain ⟨P₂a, hP₂a_auto, hP₂a_trans, _, hP₂a_fix⟩ :=
    exists_axisRect_translate_avoiding_finset R₁ 0 dy₂a obs_dr Q_dr
      (AxisRect.tubeRect_subset_of_subset hR₁_wb hR₂a_wb) hdisj₂a
  -- Move 2b: center R₂a horizontally by (dx₂b, 0) into R₂b at workbenchCenter
  have hdisj₂b : ∀ s ∈ obs_dr, Disjoint (R₂a.tubeRect dx₂b 0).toSet (Q_dr s).toSet := by
    intro s hs
    rw [AxisRect.disjoint_iff]
    refine Or.inr (Or.inr (Or.inl ?_))
    have htube_yMax : (R₂a.tubeRect dx₂b 0).yMax = R₂a.yMax := by simp
    rw [htube_yMax]
    rcases s with j | k
    · obtain ⟨_, _, hyj_lo, _, _, _⟩ := AxisRect.bounds_of_subset_quarterSquare (hP'_sub j)
      simp only [Q_dr, Sum.elim_inl, S', AxisRect.translate_yMin, add_zero]
      linarith
    · obtain ⟨_, _, hyk_lo, _, _, _⟩ := AxisRect.bounds_of_subset_quarterSquare (hP_sub k)
      simp only [Q_dr, Sum.elim_inr]
      linarith
  obtain ⟨P₂b, hP₂b_auto, hP₂b_trans, _, hP₂b_fix⟩ :=
    exists_axisRect_translate_avoiding_finset R₂a dx₂b 0 obs_dr Q_dr
      (AxisRect.tubeRect_subset_of_subset hR₂a_wb hR₂b_wb) hdisj₂b
  -- Move 3: L2 hyperbolic stretch at workbenchCenter with parameter μ i₀
  let P₃ := bumpedHyperbolicStretchHamiltonian cmppR0_mem_Ioo workbenchCenter
    workbenchRadius_pos workbenchBall_subset_cmppBall (μ i₀)
  have hP₃_auto : P₃.IsAutonomous :=
    bumpedHyperbolicStretchHamiltonian_isAutonomous cmppR0_mem_Ioo workbenchCenter
      workbenchRadius_pos workbenchBall_subset_cmppBall (μ i₀)
  -- Move 4: Part-the-Sea right by (+3/10, 0) on J_right
  let J_right : Finset ι := done.filter fun j ↦ (P' i₀).xMin ≤ (P' j).xMax
  let J_left : Finset ι := done.filter fun j ↦ ¬ (P' i₀).xMin ≤ (P' j).xMax
  let obs₄ : Finset (Option (ι ⊕ ι)) :=
    insert none ((J_left.disjSum rem').map Function.Embedding.some)
  let Q₄ : Option (ι ⊕ ι) → AxisRect := fun o ↦
    match o with
    | none => R₃
    | some (Sum.inl k) => S' k
    | some (Sum.inr k) => P k
  have hJ_pw : (J_right : Set ι).Pairwise (fun i j ↦ Disjoint (S' i).toSet (S' j).toSet) :=
    fun a _ b _ hab ↦ hS'_disj hab
  have hJ_tube_wb : ∀ j ∈ J_right, ((S' j).tubeRect (3 / 10) 0).toSet ⊆ workBox.toSet := by
    intro j _
    obtain ⟨hxj_lo, hxj_hi, hyj_lo, hyj_hi, _, _⟩ :=
      AxisRect.bounds_of_subset_quarterSquare (hP'_sub j)
    refine AxisRect.tubeRect_subset_of_subset (hS'_sub_wb j) ?_
    exact AxisRect.toSet_mono (by simp [S']; linarith) (by simp [S']; linarith)
      (by simp [S']; linarith) (by simp [S']; linarith)
  have hJ_st₄ :
      ∀ j ∈ J_right, ∀ o ∈ obs₄, Disjoint ((S' j).tubeRect (3 / 10) 0).toSet (Q₄ o).toSet := by
    intro j hj o ho
    have hj_done : j ∈ done := (Finset.mem_filter.mp hj).1
    have hj_ge : (P' i₀).xMin ≤ (P' j).xMax := (Finset.mem_filter.mp hj).2
    rcases Finset.mem_insert.mp ho with rfl | hmap
    · rw [AxisRect.disjoint_iff]
      refine Or.inr (Or.inr (Or.inr ?_))
      obtain ⟨_, _, hyj_lo, _, _, _⟩ := AxisRect.bounds_of_subset_quarterSquare (hP'_sub j)
      simp only [Q₄, AxisRect.tubeRect_yMin, S', AxisRect.translate_yMin, add_zero, min_self]
      linarith
    · rcases Finset.mem_map.mp hmap with ⟨s, hs, rfl⟩
      rcases s with k | k
      · have hk : k ∈ J_left := Finset.inl_mem_disjSum.mp hs
        have hk_lt : (P' k).xMax < (P' i₀).xMin := not_le.mp (Finset.mem_filter.mp hk).2
        have hjk_ne : j ≠ k := fun heq ↦ by subst heq; linarith
        refine disjoint_tubeRect_right_of_xMin_le_xMax (hS'_disj hjk_ne) ?_ (by norm_num)
        simp only [S', AxisRect.translate_xMin, AxisRect.translate_xMax]
        linarith [(P' k).hx]
      · obtain ⟨hxk_lo, _, _, _, _, _⟩ := AxisRect.bounds_of_subset_quarterSquare (hP_sub k)
        obtain ⟨_, hxj_hi, _, _, _, _⟩ := AxisRect.bounds_of_subset_quarterSquare (hP'_sub j)
        change Disjoint ((S' j).tubeRect (3 / 10) 0).toSet (P k).toSet
        rw [AxisRect.disjoint_iff]
        refine Or.inl ?_
        simp only [AxisRect.tubeRect_xMax, S', AxisRect.translate_xMax]
        rw [max_eq_right (by linarith)]
        linarith
  obtain ⟨Ps₄, hPs₄_auto, hPs₄_trans, hPs₄_fix⟩ :=
    exists_slide_right_hamiltonians J_right S' (by norm_num : (0 : ℝ) ≤ 3 / 10) obs₄ Q₄
      hJ_pw hJ_tube_wb hJ_st₄
  -- Obstacle bundle for Moves 5a and 5b (`J_left` at `S'`, `J_right` staged, `rem'` at `P`):
  let S'_stage : ι → AxisRect := fun j ↦ (S' j).translate (3 / 10) 0
  let obs₅ : Finset ((ι ⊕ ι) ⊕ ι) := (J_left.disjSum J_right).disjSum rem'
  let Q₅ : (ι ⊕ ι) ⊕ ι → AxisRect :=
    Sum.elim (Sum.elim S' S'_stage) P
  -- Move 5a: horizontal align R₃ by (dx₅a, 0) into R₅a
  have hdisj₅a : ∀ s ∈ obs₅, Disjoint (R₃.tubeRect dx₅a 0).toSet (Q₅ s).toSet := by
    intro s _
    rw [AxisRect.disjoint_iff]
    refine Or.inr (Or.inr (Or.inl ?_))
    have htube_yMax : (R₃.tubeRect dx₅a 0).yMax = R₃.yMax := by simp
    rw [htube_yMax]
    rcases s with (k | j) | k
    · obtain ⟨_, _, hyk_lo, _, _, _⟩ := AxisRect.bounds_of_subset_quarterSquare (hP'_sub k)
      simp only [Q₅, Sum.elim_inl, S', AxisRect.translate_yMin, add_zero]
      linarith
    · obtain ⟨_, _, hyj_lo, _, _, _⟩ := AxisRect.bounds_of_subset_quarterSquare (hP'_sub j)
      simp only [Q₅, Sum.elim_inl, Sum.elim_inr, S'_stage, S', AxisRect.translate_yMin, add_zero]
      linarith
    · obtain ⟨_, _, hyk_lo, _, _, _⟩ := AxisRect.bounds_of_subset_quarterSquare (hP_sub k)
      simp only [Q₅, Sum.elim_inr]
      linarith
  obtain ⟨P₅a, hP₅a_auto, hP₅a_trans, _, hP₅a_fix⟩ :=
    exists_axisRect_translate_avoiding_finset R₃ dx₅a 0 obs₅ Q₅
      (AxisRect.tubeRect_subset_of_subset hR₃_wb hR₅a_wb) hdisj₅a
  -- Move 5b: vertical insert R₅a UP by (0, dy₅b) into R₅a.translate 0 dy₅b = S' i₀
  have hR₅b_wb : (R₅a.translate 0 dy₅b).toSet ⊆ workBox.toSet := by
    rw [hR₅b_eq]
    exact hS'_sub_wb i₀
  have hdisj₅b : ∀ s ∈ obs₅, Disjoint (R₅a.tubeRect 0 dy₅b).toSet (Q₅ s).toSet := by
    intro s hs
    have htxMin : (R₅a.tubeRect 0 dy₅b).xMin = (S' i₀).xMin := by simp [hR₅a_xMin]
    have htxMax : (R₅a.tubeRect 0 dy₅b).xMax = (S' i₀).xMax := by simp [hR₅a_xMax]
    rcases s with (k | j) | k
    · have hk_in : Sum.inl k ∈ J_left.disjSum J_right := Finset.inl_mem_disjSum.mp hs
      have hk : k ∈ J_left := Finset.inl_mem_disjSum.mp hk_in
      have hk_lt : (P' k).xMax < (P' i₀).xMin := not_le.mp (Finset.mem_filter.mp hk).2
      rw [AxisRect.disjoint_iff, htxMin]
      refine Or.inr (Or.inl ?_)
      simp only [Q₅, Sum.elim_inl, S', AxisRect.translate_xMin, AxisRect.translate_xMax]
      linarith
    · obtain ⟨hxj_lo, _, _, _, _, _⟩ := AxisRect.bounds_of_subset_quarterSquare (hP'_sub j)
      rw [AxisRect.disjoint_iff, htxMax]
      refine Or.inl ?_
      simp only [Q₅, Sum.elim_inl, Sum.elim_inr, S'_stage, S', AxisRect.translate_xMin,
        AxisRect.translate_xMax]
      linarith
    · obtain ⟨hxk_lo, _, _, _, _, _⟩ := AxisRect.bounds_of_subset_quarterSquare (hP_sub k)
      rw [AxisRect.disjoint_iff, htxMax]
      refine Or.inl ?_
      simp only [Q₅, Sum.elim_inr, S', AxisRect.translate_xMax]
      linarith
  obtain ⟨P₅b, hP₅b_auto, hP₅b_trans, _, hP₅b_fix⟩ :=
    exists_axisRect_translate_avoiding_finset R₅a 0 dy₅b obs₅ Q₅
      (AxisRect.tubeRect_subset_of_subset hR₅a_wb hR₅b_wb) hdisj₅b
  -- Move 6: Un-part-the-Sea left by (-3/10, 0) on J_right from S'_stage back to S'
  let obs₆ : Finset (Option (ι ⊕ ι)) :=
    insert none ((J_left.disjSum rem').map Function.Embedding.some)
  let Q₆ : Option (ι ⊕ ι) → AxisRect := fun o ↦
    match o with
    | none => S' i₀
    | some (Sum.inl k) => S' k
    | some (Sum.inr k) => P k
  have hJ_stage_pw :
      (J_right : Set ι).Pairwise (fun i j ↦ Disjoint (S'_stage i).toSet (S'_stage j).toSet) := by
    intro a _ b _ hab
    exact (AxisRect.disjoint_translate_iff (S' a) (S' b) (3 / 10) 0).mpr (hS'_disj hab)
  have hJ_stage_wb :
      ∀ j ∈ J_right, ((S'_stage j).tubeRect (-(3 / 10)) 0).toSet ⊆ workBox.toSet := by
    intro j hj
    rw [tubeRect_translate_neg_x (S' j) (3 / 10)]
    exact hJ_tube_wb j hj
  have hJ_st₆ :
      ∀ j ∈ J_right, ∀ o ∈ obs₆,
        Disjoint ((S'_stage j).tubeRect (-(3 / 10)) 0).toSet (Q₆ o).toSet := by
    intro j hj o ho
    rw [tubeRect_translate_neg_x (S' j) (3 / 10)]
    have hj_done : j ∈ done := (Finset.mem_filter.mp hj).1
    have hj_ge : (P' i₀).xMin ≤ (P' j).xMax := (Finset.mem_filter.mp hj).2
    rcases Finset.mem_insert.mp ho with rfl | hmap
    · have hji₀_ne : j ≠ i₀ := fun heq ↦ by
        subst heq
        exact Finset.disjoint_left.mp hdisj_dr hj_done hi₀
      refine disjoint_tubeRect_right_of_xMin_le_xMax (hS'_disj hji₀_ne) ?_ (by norm_num)
      simp only [S', AxisRect.translate_xMin, AxisRect.translate_xMax]
      linarith
    · rcases Finset.mem_map.mp hmap with ⟨s, hs, rfl⟩
      have hs_obs₄ : some s ∈ obs₄ :=
        Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨s, hs, rfl⟩)
      rcases s with k | k
      · exact hJ_st₄ j hj (some (Sum.inl k)) hs_obs₄
      · exact hJ_st₄ j hj (some (Sum.inr k)) hs_obs₄
  obtain ⟨Ps₆, hPs₆_auto, hPs₆_trans, hPs₆_fix⟩ :=
    exists_slide_left_hamiltonians J_right S'_stage (by norm_num : (0 : ℝ) ≤ 3 / 10) obs₆ Q₆
      hJ_stage_pw hJ_stage_wb hJ_st₆
  -- Assemble full single-piece Hamiltonian list:
  let Ps_early : List (CompactlySupportedPlanarHamiltonian cmppR0) := [P₃, P₂b, P₂a, P₁]
  let Ps_mid : List (CompactlySupportedPlanarHamiltonian cmppR0) := [P₅b, P₅a]
  let Ps : List (CompactlySupportedPlanarHamiltonian cmppR0) :=
    Ps₆ ++ Ps_mid ++ Ps₄ ++ Ps_early
  have hPs_early_auto : ∀ H ∈ Ps_early, H.IsAutonomous := by
    intro H hH
    simp only [Ps_early, List.mem_cons, List.not_mem_nil, or_false] at hH
    rcases hH with rfl | rfl | rfl | rfl
    · exact hP₃_auto
    · exact hP₂b_auto
    · exact hP₂a_auto
    · exact hP₁_auto
  have hPs_mid_auto : ∀ H ∈ Ps_mid, H.IsAutonomous := by
    intro H hH
    simp only [Ps_mid, List.mem_cons, List.not_mem_nil, or_false] at hH
    rcases hH with rfl | rfl
    · exact hP₅b_auto
    · exact hP₅a_auto
  refine ⟨Ps,
    listToDiskIsotopy_autonomous_append
      (listToDiskIsotopy_autonomous_append
        (listToDiskIsotopy_autonomous_append hPs₆_auto hPs_mid_auto) hPs₄_auto)
      hPs_early_auto,
    ?_, ?_, ?_⟩
  -- 1. Action on y ∈ (P i₀).toSet:
  · intro y hy
    dsimp only [Ps]
    rw [listToDiskIsotopy_append_d, listToDiskIsotopy_append_d, listToDiskIsotopy_append_d]
    have hy₁_mem : y + WithLp.toLp 2 ![3 / 10, 0] ∈ R₁.toSet := by
      rw [← R₀.image_add_toSet (3 / 10) 0]
      exact ⟨y, hy, rfl⟩
    let y₁ := y + WithLp.toLp 2 ![3 / 10, 0]
    have hy₂a_mem : y₁ + WithLp.toLp 2 ![0, dy₂a] ∈ R₂a.toSet := by
      rw [← R₁.image_add_toSet 0 dy₂a]
      exact ⟨y₁, hy₁_mem, rfl⟩
    let y₂a := y₁ + WithLp.toLp 2 ![0, dy₂a]
    have hy₂b_mem : y₂a + WithLp.toLp 2 ![dx₂b, 0] ∈ R₂b.toSet := by
      rw [← R₂a.image_add_toSet dx₂b 0]
      exact ⟨y₂a, hy₂a_mem, rfl⟩
    let y₂b := y₂a + WithLp.toLp 2 ![dx₂b, 0]
    have hearly_eq :
        (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps_early).d (1, y) =
          P₃.toDiskIsotopy.d (1, y₂b) := by
      dsimp only [Ps_early]
      rw [listToDiskIsotopy_cons_d, listToDiskIsotopy_cons_d, listToDiskIsotopy_cons_d,
        listToDiskIsotopy_singleton_d, hP₁_trans y hy, hP₂a_trans y₁ hy₁_mem,
        hP₂b_trans y₂a hy₂a_mem]
    rw [hearly_eq]
    have hR₂b_w : R₂b.width / 2 ≤ (P i₀).width / 2 := by
      simp [R₂b, R₂a, R₁, R₀]
    have hR₂b_h : R₂b.height / 2 ≤ (P i₀).height / 2 := by
      simp [R₂b, R₂a, R₁, R₀]
    have hwb_i₀ :
        (max ((P i₀).width / 2) (Real.exp (-μ i₀) * ((P i₀).width / 2))) ^ 2 +
          (max ((P i₀).height / 2) (Real.exp (μ i₀) * ((P i₀).height / 2))) ^ 2 <
          (workbenchRadius / 2) ^ 2 := by
      rw [show workbenchRadius / 2 = 3 / 20 by unfold workbenchRadius; norm_num]
      exact hwb i₀
    have hstr :
        P₃.toDiskIsotopy.d (1, y₂b) =
          workbenchCenter + WithLp.toLp 2
            ![Real.exp (-μ i₀) * (y₂b 0 - workbenchCenter 0),
              Real.exp (μ i₀) * (y₂b 1 - workbenchCenter 1)] :=
      bumpedHyperbolicStretchIsotopy_timeOne_of_mem_axisRect cmppR0_mem_Ioo hR₂b_center
        workbenchRadius_pos workbenchBall_subset_cmppBall (μ i₀) hR₂b_w hR₂b_h hwb_i₀ hy₂b_mem
    let y₃ := P₃.toDiskIsotopy.d (1, y₂b)
    have hy₂b_diff0 : y₂b 0 - workbenchCenter 0 = y 0 - (P i₀).center 0 := by
      simp only [Fin.isValue, y₂b, y₂a, y₁, dx₂b, R₂a, R₁, R₀, workbenchCenter_zero,
        PiLp.add_apply, Matrix.cons_val_zero, AxisRect.center_zero, AxisRect.translate_xMin,
        AxisRect.translate_xMax, add_zero]
      ring
    have hy₂b_diff1 : y₂b 1 - workbenchCenter 1 = y 1 - (P i₀).center 1 := by
      simp only [Fin.isValue, y₂b, y₂a, y₁, dy₂a, R₁, R₀, workbenchCenter_one, PiLp.add_apply,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, AxisRect.center_one,
        AxisRect.translate_yMin, AxisRect.translate_yMax, add_zero]
      ring
    have hy₃_mem : y₃ ∈ R₃.toSet := by
      rw [AxisRect.mem_ofCenter_iff]
      obtain ⟨hx_c, hy_c⟩ := (P i₀).abs_sub_center_le_half_of_mem hy
      have hy₃_0 : y₃ 0 - workbenchCenter 0 = Real.exp (-μ i₀) * (y 0 - (P i₀).center 0) := by
        dsimp only [y₃]
        rw [hstr, ← hy₂b_diff0]
        simp
      have hy₃_1 : y₃ 1 - workbenchCenter 1 = Real.exp (μ i₀) * (y 1 - (P i₀).center 1) := by
        dsimp only [y₃]
        rw [hstr, ← hy₂b_diff1]
        simp
      rw [hy₃_0, hy₃_1, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _),
        hw i₀, hh i₀]
      exact ⟨by
        calc
          Real.exp (-μ i₀) * |y 0 - (P i₀).center 0| ≤ Real.exp (-μ i₀) * ((P i₀).width / 2) :=
            mul_le_mul_of_nonneg_left hx_c (Real.exp_nonneg _)
          _ = Real.exp (-μ i₀) * (P i₀).width / 2 := by ring,
        by
        calc
          Real.exp (μ i₀) * |y 1 - (P i₀).center 1| ≤ Real.exp (μ i₀) * ((P i₀).height / 2) :=
            mul_le_mul_of_nonneg_left hy_c (Real.exp_nonneg _)
          _ = Real.exp (μ i₀) * (P i₀).height / 2 := by ring⟩
    change (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps₆).d
      (1, (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps_mid).d
        (1, (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps₄).d
          (1, y₃))) = rectAffineMap (P i₀) (S' i₀) (μ i₀) y
    rw [hPs₄_fix none (Finset.mem_insert_self _ _) y₃ hy₃_mem]
    have hy₅a_mem : y₃ + WithLp.toLp 2 ![dx₅a, 0] ∈ R₅a.toSet := by
      rw [← R₃.image_add_toSet dx₅a 0]
      exact ⟨y₃, hy₃_mem, rfl⟩
    let y₅a := y₃ + WithLp.toLp 2 ![dx₅a, 0]
    have hy₅b_mem : y₅a + WithLp.toLp 2 ![0, dy₅b] ∈ (S' i₀).toSet := by
      rw [← hR₅b_eq, ← R₅a.image_add_toSet 0 dy₅b]
      exact ⟨y₅a, hy₅a_mem, rfl⟩
    have hmid_eq :
        (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps_mid).d (1, y₃) =
          y₅a + WithLp.toLp 2 ![0, dy₅b] := by
      dsimp only [Ps_mid]
      rw [listToDiskIsotopy_cons_d, listToDiskIsotopy_singleton_d, hP₅a_trans y₃ hy₃_mem,
        hP₅b_trans y₅a hy₅a_mem]
    rw [hmid_eq, hPs₆_fix none (Finset.mem_insert_self _ _) _ hy₅b_mem]
    dsimp only [y₅a, y₃]
    rw [hstr, hy₂b_diff0, hy₂b_diff1]
    ext c
    fin_cases c
    · simp only [Fin.zero_eta, PiLp.add_apply, workbenchCenter_zero, Matrix.cons_val_zero,
        dx₅a, rectAffineMap_zero]
      ring
    · simp only [Fin.mk_one, PiLp.add_apply, workbenchCenter_one, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, dy₅b, rectAffineMap_one]
      ring
  -- 2. Pointwise fixity on already-parked (S' j).toSet (j ∈ done):
  · intro j hj y hy
    dsimp only [Ps]
    rw [listToDiskIsotopy_append_d, listToDiskIsotopy_append_d, listToDiskIsotopy_append_d]
    have hj_dr : Sum.inl j ∈ obs_dr := Finset.inl_mem_disjSum.mpr hj
    obtain ⟨_, _, hyj_lo, _, _, _⟩ := AxisRect.bounds_of_subset_quarterSquare (hP'_sub j)
    have hy_nonneg : 0 ≤ y 1 := by
      have hy_s := (AxisRect.mem_toSet_iff (S' j) y).mp hy
      simp only [S', AxisRect.translate_yMin, add_zero] at hy_s
      linarith [hy_s.2.1]
    have hP₃_fix_y : P₃.toDiskIsotopy.d (1, y) = y :=
      bumpedHyperbolicStretchIsotopy_eq_self_of_notMem_ball cmppR0_mem_Ioo workbenchCenter
        workbenchRadius_pos workbenchBall_subset_cmppBall (μ i₀) 1
        (notMem_workbenchBall_of_nonneg_y hy_nonneg)
    have hearly_fix :
        (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps_early).d (1, y) =
          y := by
      dsimp only [Ps_early]
      rw [listToDiskIsotopy_cons_d, listToDiskIsotopy_cons_d, listToDiskIsotopy_cons_d,
        listToDiskIsotopy_singleton_d, hP₁_fix _ hj_dr y hy, hP₂a_fix _ hj_dr y hy,
        hP₂b_fix _ hj_dr y hy, hP₃_fix_y]
    rw [hearly_fix]
    by_cases hj_ge : (P' i₀).xMin ≤ (P' j).xMax
    · have hj_R : j ∈ J_right := Finset.mem_filter.mpr ⟨hj, hj_ge⟩
      rw [hPs₄_trans j hj_R y hy]
      let y_st := y + WithLp.toLp 2 ![3 / 10, 0]
      have hy_st_mem : y_st ∈ (S'_stage j).toSet := by
        rw [← (S' j).image_add_toSet (3 / 10) 0]
        exact ⟨y, hy, rfl⟩
      have hj_obs₅ : Sum.inl (Sum.inr j) ∈ obs₅ :=
        Finset.inl_mem_disjSum.mpr (Finset.inr_mem_disjSum.mpr hj_R)
      have hmid_fix :
          (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps_mid).d
              (1, y_st) = y_st := by
        dsimp only [Ps_mid]
        rw [listToDiskIsotopy_cons_d, listToDiskIsotopy_singleton_d,
          hP₅a_fix _ hj_obs₅ y_st hy_st_mem, hP₅b_fix _ hj_obs₅ y_st hy_st_mem]
      change (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps₆).d
        (1, (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps_mid).d
          (1, y_st)) = y
      rw [hmid_fix, hPs₆_trans j hj_R y_st hy_st_mem]
      ext c
      fin_cases c <;> simp [y_st]
    · have hj_L : j ∈ J_left := Finset.mem_filter.mpr ⟨hj, hj_ge⟩
      have hj_obs₄ : some (Sum.inl j) ∈ obs₄ :=
        Finset.mem_insert_of_mem
          (Finset.mem_map.mpr ⟨Sum.inl j, Finset.inl_mem_disjSum.mpr hj_L, rfl⟩)
      have hj_obs₅ : Sum.inl (Sum.inl j) ∈ obs₅ :=
        Finset.inl_mem_disjSum.mpr (Finset.inl_mem_disjSum.mpr hj_L)
      have hj_obs₆ : some (Sum.inl j) ∈ obs₆ :=
        Finset.mem_insert_of_mem
          (Finset.mem_map.mpr ⟨Sum.inl j, Finset.inl_mem_disjSum.mpr hj_L, rfl⟩)
      rw [hPs₄_fix _ hj_obs₄ y hy]
      have hmid_fix :
          (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps_mid).d (1, y) =
            y := by
        dsimp only [Ps_mid]
        rw [listToDiskIsotopy_cons_d, listToDiskIsotopy_singleton_d,
          hP₅a_fix _ hj_obs₅ y hy, hP₅b_fix _ hj_obs₅ y hy]
      rw [hmid_fix, hPs₆_fix _ hj_obs₆ y hy]
  -- 3. Pointwise fixity on remaining sources (P k).toSet (k ∈ rem, k ≠ i₀):
  · intro k hk hne y hy
    dsimp only [Ps]
    rw [listToDiskIsotopy_append_d, listToDiskIsotopy_append_d, listToDiskIsotopy_append_d]
    have hk' : k ∈ rem' := Finset.mem_erase.mpr ⟨hne, hk⟩
    have hk_dr : Sum.inr k ∈ obs_dr := Finset.inr_mem_disjSum.mpr hk'
    obtain ⟨_, _, hyk_lo, _, _, _⟩ := AxisRect.bounds_of_subset_quarterSquare (hP_sub k)
    have hy_nonneg : 0 ≤ y 1 := by
      have hy_p := (AxisRect.mem_toSet_iff (P k) y).mp hy
      linarith [hy_p.2.1]
    have hP₃_fix_y : P₃.toDiskIsotopy.d (1, y) = y :=
      bumpedHyperbolicStretchIsotopy_eq_self_of_notMem_ball cmppR0_mem_Ioo workbenchCenter
        workbenchRadius_pos workbenchBall_subset_cmppBall (μ i₀) 1
        (notMem_workbenchBall_of_nonneg_y hy_nonneg)
    have hearly_fix :
        (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps_early).d (1, y) =
          y := by
      dsimp only [Ps_early]
      rw [listToDiskIsotopy_cons_d, listToDiskIsotopy_cons_d, listToDiskIsotopy_cons_d,
        listToDiskIsotopy_singleton_d, hP₁_fix _ hk_dr y hy, hP₂a_fix _ hk_dr y hy,
        hP₂b_fix _ hk_dr y hy, hP₃_fix_y]
    have hk_obs₄ : some (Sum.inr k) ∈ obs₄ :=
      Finset.mem_insert_of_mem
        (Finset.mem_map.mpr ⟨Sum.inr k, Finset.inr_mem_disjSum.mpr hk', rfl⟩)
    have hk_obs₅ : Sum.inr k ∈ obs₅ := Finset.inr_mem_disjSum.mpr hk'
    have hk_obs₆ : some (Sum.inr k) ∈ obs₆ :=
      Finset.mem_insert_of_mem
        (Finset.mem_map.mpr ⟨Sum.inr k, Finset.inr_mem_disjSum.mpr hk', rfl⟩)
    rw [hearly_fix, hPs₄_fix _ hk_obs₄ y hy]
    have hmid_fix :
        (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps_mid).d (1, y) =
          y := by
      dsimp only [Ps_mid]
      rw [listToDiskIsotopy_cons_d, listToDiskIsotopy_singleton_d,
        hP₅a_fix _ hk_obs₅ y hy, hP₅b_fix _ hk_obs₅ y hy]
    rw [hmid_fix, hPs₆_fix _ hk_obs₆ y hy]

/-- Inductive multi-piece parking lemma: relocates every remaining piece `k ∈ rem`
(`Disjoint done rem`) onto its parked target slot `(P' k).translate (-3/5) 0` via `rectAffineMap`
while fixing all already-parked pieces `j ∈ done` pointwise. -/
-- tier: T2
theorem exists_relocate_all_to_park {ι : Type*}
    (P P' : ι → AxisRect) (μ : ι → ℝ)
    (hP_sub : ∀ i : ι, (P i).toSet ⊆ quarterSquare.toSet)
    (hP'_sub : ∀ i : ι, (P' i).toSet ⊆ quarterSquare.toSet)
    (hP_disj : Pairwise (Disjoint on fun i : ι ↦ (P i).toSet))
    (hP'_disj : Pairwise (Disjoint on fun i : ι ↦ (P' i).toSet))
    (hw : ∀ i : ι, (P' i).width = Real.exp (-μ i) * (P i).width)
    (hh : ∀ i : ι, (P' i).height = Real.exp (μ i) * (P i).height)
    (hwb : ∀ i : ι,
      (max ((P i).width / 2) (Real.exp (-μ i) * ((P i).width / 2))) ^ 2 +
        (max ((P i).height / 2) (Real.exp (μ i) * ((P i).height / 2))) ^ 2 <
        (3 / 20 : ℝ) ^ 2) :
    ∀ (done rem : Finset ι), Disjoint done rem →
      let S' : ι → AxisRect := fun i ↦ (P' i).translate (-3 / 5) 0
      ∃ Ps : List (CompactlySupportedPlanarHamiltonian cmppR0),
        (∀ H ∈ Ps, H.IsAutonomous) ∧
        (∀ i ∈ rem, ∀ y ∈ (P i).toSet,
          (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).d (1, y) =
            rectAffineMap (P i) (S' i) (μ i) y) ∧
        (∀ j ∈ done, ∀ y ∈ (S' j).toSet,
          (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).d (1, y) =
            y) := by
  classical
  let S' : ι → AxisRect := fun i ↦ (P' i).translate (-3 / 5) 0
  suffices hmain :
      ∀ (n : ℕ) (done rem : Finset ι), rem.card = n → Disjoint done rem →
        ∃ Ps : List (CompactlySupportedPlanarHamiltonian cmppR0),
          (∀ H ∈ Ps, H.IsAutonomous) ∧
          (∀ i ∈ rem, ∀ y ∈ (P i).toSet,
            (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).d (1, y) =
              rectAffineMap (P i) (S' i) (μ i) y) ∧
          (∀ j ∈ done, ∀ y ∈ (S' j).toSet,
            (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).d (1, y) =
              y) by
    intro done rem hdr
    exact hmain rem.card done rem rfl hdr
  intro n
  induction n with
  | zero =>
    intro done rem hcard _
    rw [Finset.card_eq_zero.mp hcard]
    refine ⟨[], fun _ h ↦ absurd h List.not_mem_nil,
      fun _ hi ↦ absurd hi (Finset.notMem_empty _), fun _ _ y _ ↦ ?_⟩
    rw [listToDiskIsotopy_nil_d]
  | succ n ih =>
    intro done rem hcard hdr
    have hne : rem.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image rem (fun i ↦ (P i).xMin) hne
    obtain ⟨Ps_step, hstep_auto, hstep_i₀, hstep_done, hstep_rem⟩ :=
      exists_single_piece_relocate_to_park P P' μ hP_sub hP'_sub hP_disj hP'_disj hw hh hwb
        done rem hdr hi₀ hmax
    let done' : Finset ι := insert i₀ done
    let rem' : Finset ι := rem.erase i₀
    have hcard' : rem'.card = n := by
      change (rem.erase i₀).card = n
      rw [Finset.card_erase_of_mem hi₀, hcard]
      rfl
    have hdr' : Disjoint done' rem' := by
      rw [Finset.disjoint_left]
      intro x hx_d hx_r
      rcases Finset.mem_insert.mp hx_d with rfl | hx_done
      · exact (Finset.ne_of_mem_erase hx_r) rfl
      · exact Finset.disjoint_left.mp hdr hx_done (Finset.mem_of_mem_erase hx_r)
    obtain ⟨Ps_rest, hrest_auto, hrest_rem, hrest_done⟩ := ih done' rem' hcard' hdr'
    refine ⟨Ps_rest ++ Ps_step, listToDiskIsotopy_autonomous_append hrest_auto hstep_auto, ?_, ?_⟩
    · intro i hi y hy
      rw [listToDiskIsotopy_append_d]
      by_cases heq : i = i₀
      · subst heq
        rw [hstep_i₀ y hy]
        have hw_s : (S' i).width = Real.exp (-μ i) * (P i).width := by
          simpa [S'] using hw i
        have hh_s : (S' i).height = Real.exp (μ i) * (P i).height := by
          simpa [S'] using hh i
        have hmem_s : rectAffineMap (P i) (S' i) (μ i) y ∈ (S' i).toSet :=
          rectAffineMap_mem_toSet hw_s hh_s hy
        exact hrest_done i (Finset.mem_insert_self i done) _ hmem_s
      · rw [hstep_rem i hi heq y hy]
        exact hrest_rem i (Finset.mem_erase.mpr ⟨heq, hi⟩) y hy
    · intro j hj y hy
      rw [listToDiskIsotopy_append_d, hstep_done j hj y hy]
      exact hrest_done j (Finset.mem_insert_of_mem hj) y hy

/-- **Relocation Theorem RT (`MISSION_DIRECTIVE_CMPP.md` §4.2 & §10, `geometry_spec.md` §3.2)**:
Given any finite family `(P i)` (`i : ι`, `[Fintype ι]`) of pairwise-disjoint closed axis-parallel
rectangles in `quarterSquare = [0, 1/4]²`, pairwise-disjoint target rectangles `(P' i)` in
`quarterSquare`, and stretch parameters `μ i : ℝ` satisfying matching scaled dimensions and the
canonical workbench trajectory bound, there exists a finite list `Ps` of **autonomous** planar
Hamiltonians supported in `Metric.ball 0 cmppR0` (`cmppR0 = 17 / 20 ∈ (0, 1)`) whose time-`1`
composed flow equals `rectAffineMap (P i) (P' i) (μ i)` on `(P i).toSet` for every `i : ι`. -/
-- tier: T2
theorem exists_relocation_hamiltonians {ι : Type*} [Fintype ι]
    (P P' : ι → AxisRect) (μ : ι → ℝ)
    (hP_sub : ∀ i : ι, (P i).toSet ⊆ quarterSquare.toSet)
    (hP'_sub : ∀ i : ι, (P' i).toSet ⊆ quarterSquare.toSet)
    (hP_disj : Pairwise (Disjoint on fun i : ι ↦ (P i).toSet))
    (hP'_disj : Pairwise (Disjoint on fun i : ι ↦ (P' i).toSet))
    (hw : ∀ i : ι, (P' i).width = Real.exp (-μ i) * (P i).width)
    (hh : ∀ i : ι, (P' i).height = Real.exp (μ i) * (P i).height)
    (hwb : ∀ i : ι,
      (max ((P i).width / 2) (Real.exp (-μ i) * ((P i).width / 2))) ^ 2 +
        (max ((P i).height / 2) (Real.exp (μ i) * ((P i).height / 2))) ^ 2 <
        (3 / 20 : ℝ) ^ 2) :
    ∃ Ps : List (CompactlySupportedPlanarHamiltonian cmppR0),
      (∀ H ∈ Ps, H.IsAutonomous) ∧
      (∀ (i : ι) (y : EuclideanPlane), y ∈ (P i).toSet →
        (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).d (1, y) =
          rectAffineMap (P i) (P' i) (μ i) y) := by
  classical
  obtain ⟨Ps_park, hpark_auto, hpark_act, _⟩ :=
    exists_relocate_all_to_park P P' μ hP_sub hP'_sub hP_disj hP'_disj hw hh hwb
      ∅ Finset.univ (Finset.disjoint_empty_left _)
  have hret_wb : (parkBox.tubeRect (3 / 5) 0).toSet ⊆ workBox.toSet := by
    refine AxisRect.tubeRect_subset_of_subset parkBox_subset_workBox ?_
    rw [parkBox_translate_return]
    exact quarterSquare_subset_workBox
  obtain ⟨P_ret, hret_auto, hret_trans, _, _⟩ :=
    exists_axisRect_translate_avoiding_finset parkBox (3 / 5) 0 (∅ : Finset Empty) Empty.elim
      hret_wb (fun _ hk ↦ absurd hk (Finset.notMem_empty _))
  refine ⟨P_ret :: Ps_park, List.forall_mem_cons.mpr ⟨hret_auto, hpark_auto⟩, ?_⟩
  intro i y hy
  rw [listToDiskIsotopy_cons_d, hpark_act i (Finset.mem_univ i) y hy]
  let S'_i : AxisRect := (P' i).translate (-3 / 5) 0
  have hw_s : S'_i.width = Real.exp (-μ i) * (P i).width := by
    simpa [S'_i] using hw i
  have hh_s : S'_i.height = Real.exp (μ i) * (P i).height := by
    simpa [S'_i] using hh i
  have hmem_s : rectAffineMap (P i) S'_i (μ i) y ∈ S'_i.toSet :=
    rectAffineMap_mem_toSet hw_s hh_s hy
  have hsub_park : S'_i.toSet ⊆ parkBox.toSet := by
    obtain ⟨hx₁, hx₂, hy₁, hy₂, _, _⟩ := AxisRect.bounds_of_subset_quarterSquare (hP'_sub i)
    exact AxisRect.toSet_mono (by simp [S'_i]; linarith) (by simp [S'_i]; linarith)
      (by simp [S'_i]; linarith) (by simp [S'_i]; linarith)
  rw [hret_trans _ (hsub_park hmem_s)]
  have hadd := rectAffineMap_translate_target_add (P i) (P' i) (-3 / 5) 0 (μ i) y
  have hv :
      (WithLp.toLp 2 ![-(-3 / 5 : ℝ), -(0 : ℝ)] : EuclideanPlane) =
        WithLp.toLp 2 ![3 / 5, 0] := by
    ext c
    fin_cases c
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      norm_num
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, neg_zero]
  rw [hv] at hadd
  exact hadd

/-- `UnitDisk2` `diskTimeOneMap` wrapper for `exists_relocation_hamiltonians`. -/
-- tier: T1
theorem exists_relocation_hamiltonians_diskTimeOneMap {ι : Type*} [Fintype ι]
    (P P' : ι → AxisRect) (μ : ι → ℝ)
    (hP_sub : ∀ i : ι, (P i).toSet ⊆ quarterSquare.toSet)
    (hP'_sub : ∀ i : ι, (P' i).toSet ⊆ quarterSquare.toSet)
    (hP_disj : Pairwise (Disjoint on fun i : ι ↦ (P i).toSet))
    (hP'_disj : Pairwise (Disjoint on fun i : ι ↦ (P' i).toSet))
    (hw : ∀ i : ι, (P' i).width = Real.exp (-μ i) * (P i).width)
    (hh : ∀ i : ι, (P' i).height = Real.exp (μ i) * (P i).height)
    (hwb : ∀ i : ι,
      (max ((P i).width / 2) (Real.exp (-μ i) * ((P i).width / 2))) ^ 2 +
        (max ((P i).height / 2) (Real.exp (μ i) * ((P i).height / 2))) ^ 2 <
        (3 / 20 : ℝ) ^ 2) :
    ∃ Ps : List (CompactlySupportedPlanarHamiltonian cmppR0),
      (∀ H ∈ Ps, H.IsAutonomous) ∧
      (∀ (i : ι) (y : UnitDisk2), y.1 ∈ (P i).toSet →
        ((CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).diskTimeOneMap
          y).1 = rectAffineMap (P i) (P' i) (μ i) y.1) := by
  obtain ⟨Ps, hauto, hact⟩ :=
    exists_relocation_hamiltonians P P' μ hP_sub hP'_sub hP_disj hP'_disj hw hh hwb
  exact ⟨Ps, hauto, fun i y hy ↦ hact i y.1 hy⟩

/-! ## 4. Gate G5 Anti-Vacuity Sanity Check (`cmppRelocation_sanity`) -/

/-- **Gate G5 Anti-Vacuity Witness for Milestone A3 (`cmppRelocation_sanity`)**:
Swaps and stretches two concrete disjoint axis-parallel rectangles inside
`quarterSquare = [0, 1/4]²` with overlapping target `x`-intervals (genuinely invoking
Part-the-Sea & Un-part-the-Sea):
- `R₀ = [0, 1/12] × [0, 1/36]` mapped to `R'₀ = [0, 1/4] × [1/9, 13/108]` (`μ₀ = -Real.log 3`),
  sending `(0, 0) ↦ (0, 1/9)` and `R₀.center ↦ R'₀.center = (1/8, 25/216)`;
- `R₁ = [0, 1/12] × [1/9, 5/36]` mapped to `R'₁ = [0, 1/36] × [0, 1/12]` (`μ₁ = Real.log 3`),
  sending `(0, 1/9) ↦ (0, 0)` and `R₁.center ↦ R'₁.center = (1/72, 1/24)`,
witnessed by a non-empty autonomous Hamiltonian list `Ps` with `diskTimeOneMap ≠ id`. -/
-- tier: T2
theorem cmppRelocation_sanity :
    let R₀ : AxisRect :=
      { xMin := 0, xMax := 1 / 12, yMin := 0, yMax := 1 / 36,
        hx := by norm_num, hy := by norm_num }
    let R₁ : AxisRect :=
      { xMin := 0, xMax := 1 / 12, yMin := 1 / 9, yMax := 5 / 36,
        hx := by norm_num, hy := by norm_num }
    let R'₀ : AxisRect :=
      { xMin := 0, xMax := 1 / 4, yMin := 1 / 9, yMax := 13 / 108,
        hx := by norm_num, hy := by norm_num }
    let R'₁ : AxisRect :=
      { xMin := 0, xMax := 1 / 36, yMin := 0, yMax := 1 / 12,
        hx := by norm_num, hy := by norm_num }
    ∃ Ps : List (CompactlySupportedPlanarHamiltonian cmppR0),
      Ps ≠ [] ∧
      (∀ H ∈ Ps, H.IsAutonomous) ∧
      (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).d
        (1, 0) = WithLp.toLp 2 ![0, 1 / 9] ∧
      (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).d
        (1, WithLp.toLp 2 ![0, 1 / 9]) = 0 ∧
      (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).d
        (1, R₀.center) = R'₀.center ∧
      (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).d
        (1, R₁.center) = R'₁.center ∧
      (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).diskTimeOneMap ≠
        id := by
  intro R₀ R₁ R'₀ R'₁
  let P : Fin 2 → AxisRect := ![R₀, R₁]
  let P' : Fin 2 → AxisRect := ![R'₀, R'₁]
  let μ : Fin 2 → ℝ := ![-Real.log 3, Real.log 3]
  have hexp_pos3 : Real.exp (Real.log 3) = 3 := Real.exp_log (by norm_num)
  have hexp_neg3 : Real.exp (-Real.log 3) = 1 / 3 := by
    rw [Real.exp_neg, hexp_pos3, one_div]
  have hP_sub : ∀ i : Fin 2, (P i).toSet ⊆ quarterSquare.toSet := by
    intro i
    fin_cases i
    · exact AxisRect.toSet_mono (by simp [P, R₀])
        (by simp only [Fin.zero_eta, P, Matrix.cons_val_zero, R₀, quarterSquare_xMax]; norm_num)
        (by simp [P, R₀])
        (by simp only [Fin.zero_eta, P, Matrix.cons_val_zero, R₀, quarterSquare_yMax]; norm_num)
    · exact AxisRect.toSet_mono (by simp [P, R₁])
        (by simp only [Fin.mk_one, P, Matrix.cons_val_one, Matrix.cons_val_fin_one, R₁,
          quarterSquare_xMax]; norm_num)
        (by simp only [Fin.mk_one, P, Matrix.cons_val_one, Matrix.cons_val_fin_one, R₁,
          quarterSquare_yMin]; norm_num)
        (by simp only [Fin.mk_one, P, Matrix.cons_val_one, Matrix.cons_val_fin_one, R₁,
          quarterSquare_yMax]; norm_num)
  have hP'_sub : ∀ i : Fin 2, (P' i).toSet ⊆ quarterSquare.toSet := by
    intro i
    fin_cases i
    · exact AxisRect.toSet_mono (by simp [P', R'₀]) (by simp [P', R'₀])
        (by simp only [Fin.zero_eta, P', Matrix.cons_val_zero, R'₀, quarterSquare_yMin]; norm_num)
        (by simp only [Fin.zero_eta, P', Matrix.cons_val_zero, R'₀, quarterSquare_yMax]; norm_num)
    · exact AxisRect.toSet_mono (by simp [P', R'₁])
        (by simp only [Fin.mk_one, P', Matrix.cons_val_one, Matrix.cons_val_fin_one, R'₁,
          quarterSquare_xMax]; norm_num)
        (by simp [P', R'₁])
        (by simp only [Fin.mk_one, P', Matrix.cons_val_one, Matrix.cons_val_fin_one, R'₁,
          quarterSquare_yMax]; norm_num)
  have hP_disj : Pairwise (Disjoint on fun i : Fin 2 ↦ (P i).toSet) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · rw [Function.onFun, AxisRect.disjoint_iff]
      exact Or.inr (Or.inr (Or.inl (by simp [P, R₀, R₁]; norm_num)))
    · rw [Function.onFun, AxisRect.disjoint_iff]
      exact Or.inr (Or.inr (Or.inr (by simp [P, R₀, R₁]; norm_num)))
    · exact absurd rfl hij
  have hP'_disj : Pairwise (Disjoint on fun i : Fin 2 ↦ (P' i).toSet) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · rw [Function.onFun, AxisRect.disjoint_iff]
      exact Or.inr (Or.inr (Or.inr (by simp [P', R'₀, R'₁]; norm_num)))
    · rw [Function.onFun, AxisRect.disjoint_iff]
      exact Or.inr (Or.inr (Or.inl (by simp [P', R'₀, R'₁]; norm_num)))
    · exact absurd rfl hij
  have hw : ∀ i : Fin 2, (P' i).width = Real.exp (-μ i) * (P i).width := by
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, P', P, μ, Matrix.cons_val_zero, neg_neg, hexp_pos3, AxisRect.width,
        R'₀, R₀]
      norm_num
    · simp only [Fin.mk_one, P', P, μ, Matrix.cons_val_one, Matrix.cons_val_fin_one, hexp_neg3,
        AxisRect.width, R'₁, R₁]
      norm_num
  have hh : ∀ i : Fin 2, (P' i).height = Real.exp (μ i) * (P i).height := by
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, P', P, μ, Matrix.cons_val_zero, hexp_neg3, AxisRect.height, R'₀, R₀]
      norm_num
    · simp only [Fin.mk_one, P', P, μ, Matrix.cons_val_one, Matrix.cons_val_fin_one, hexp_pos3,
        AxisRect.height, R'₁, R₁]
      norm_num
  have hwb : ∀ i : Fin 2,
      (max ((P i).width / 2) (Real.exp (-μ i) * ((P i).width / 2))) ^ 2 +
        (max ((P i).height / 2) (Real.exp (μ i) * ((P i).height / 2))) ^ 2 <
        (3 / 20 : ℝ) ^ 2 := by
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, P, μ, Matrix.cons_val_zero, neg_neg, hexp_pos3, hexp_neg3,
        AxisRect.width, AxisRect.height, R₀]
      norm_num
    · simp only [Fin.mk_one, P, μ, Matrix.cons_val_one, Matrix.cons_val_fin_one, hexp_neg3,
        hexp_pos3, AxisRect.width, AxisRect.height, R₁]
      norm_num
  obtain ⟨Ps, hauto, hact⟩ :=
    exists_relocation_hamiltonians P P' μ hP_sub hP'_sub hP_disj hP'_disj hw hh hwb
  have h0_mem : (0 : EuclideanPlane) ∈ R₀.toSet := by
    rw [AxisRect.mem_toSet_iff]
    simp only [Fin.isValue, PiLp.zero_apply, R₀, Set.mem_Icc]
    norm_num
  have hp₁_mem : (WithLp.toLp 2 ![0, 1 / 9] : EuclideanPlane) ∈ R₁.toSet := by
    rw [AxisRect.mem_toSet_iff]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      R₁, Set.mem_Icc]
    norm_num
  have hd_zero :
      (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).d (1, 0) =
        WithLp.toLp 2 ![0, 1 / 9] := by
    rw [hact 0 0 h0_mem]
    ext c
    fin_cases c <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, P, P', μ, R₀, R'₀, rectAffineMap_zero,
        rectAffineMap_one, AxisRect.center_zero, AxisRect.center_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, PiLp.zero_apply, neg_neg, hexp_pos3,
        hexp_neg3] <;>
      norm_num
  have hd_p₁ :
      (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).d
        (1, WithLp.toLp 2 ![0, 1 / 9]) = 0 := by
    rw [hact 1 _ hp₁_mem]
    ext c
    fin_cases c <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, P, P', μ, R₁, R'₁, rectAffineMap_zero,
        rectAffineMap_one, AxisRect.center_zero, AxisRect.center_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, PiLp.zero_apply, hexp_pos3, hexp_neg3] <;>
      norm_num
  have hd_c₀ :
      (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).d
        (1, R₀.center) = R'₀.center := by
    rw [hact 0 R₀.center R₀.center_mem_toSet]
    simp [P, P']
  have hd_c₁ :
      (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).d
        (1, R₁.center) = R'₁.center := by
    rw [hact 1 R₁.center R₁.center_mem_toSet]
    simp [P, P']
  have hne_id :
      (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).diskTimeOneMap ≠
        id := by
    intro hid
    have h0_disk : (0 : EuclideanPlane) ∈ UnitDisk2 := by
      rw [UnitDisk2, Metric.mem_ball, dist_self]
      norm_num
    have heq := congrArg (fun q : UnitDisk2 ↦ q.1 1) (congrFun hid ⟨0, h0_disk⟩)
    change (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).d
      (1, 0) 1 = (0 : EuclideanPlane) 1 at heq
    rw [hd_zero] at heq
    norm_num at heq
  have hPs_ne : Ps ≠ [] := by
    rintro rfl
    exact hne_id (AreaPreservingDiskIsotopy.refl_diskTimeOneMap cmppR0_mem_Ioo)
  exact ⟨Ps, hPs_ne, hauto, hd_zero, hd_p₁, hd_c₀, hd_c₁, hne_id⟩

end S4TuringPoisson.CMPP
