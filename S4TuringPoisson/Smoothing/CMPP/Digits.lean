/-
Copyright (c) 2026 Pablo Suárez-Serrato. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Suárez-Serrato
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import S4TuringPoisson.Dynamics.GeneralizedShift

/-!
# Digit Algebra, Cylinder Rectangles, Block Affine Maps & Lemma G0 (CMPP Milestone A1)

This module formalizes Milestone A1 (`S4TuringPoisson/Smoothing/CMPP/Digits.lean`) of the `CMPP21`
Hamiltonian realization pipeline (`MISSION_DIRECTIVE_CMPP.md` §4.1, §7 and
`docs/cmpp/geometry_spec.md` §§1–2):

1. **Axis-Parallel Rectangles (`AxisRect`)**:
   - Compact nonempty axis-parallel planar rectangles `[xMin, xMax] × [yMin, yMax] ⊂ ℝ²` with
     width, height, center, rigid translation `translate`, unit-quarter bounding box
     `quarterSquare = [0, 1/4]²`, and axis-aligned translation bounding tube `tubeRect`.

2. **Closed Cantor Prefix Intervals & Prefix Compatibility**:
   - Closed rescaled middle-Cantor intervals
     `cantorClosedInterval p = [K / (4 B^m), (K + 1) / (4 B^m)]` inside `[0, 1/4]`, prefix
     antitonicity `cantorClosedInterval_antitone_prefix`, same-length disjointness
     `disjoint_cantorClosedInterval_of_ne` via `two_le_abs_cantorPrefixCode_sub`, and
     prefix-incompatibility disjointness `disjoint_cantorClosedInterval_of_not_prefix`.

3. **One-Digit & Multi-Digit Shift / Tail Identities for `scaledCantorCoord`**:
   - Exact `prefix + tail` decompositions of `scaledCantorCoord` for general length `m` and lengths
     `1`, `2`, and `3`, matching `docs/cmpp/geometry_spec.md` §1.1.

4. **`shiftDom3` Source/Image Rectangles, Block Affine Maps `A_w`, and Lemma G0**:
   - Source rectangles `sourceRect`, target rectangles `imageRect`, hyperbolic stretch parameter
     `blockStretchMu`, and affine block maps `blockAffineMap` (`A_w(R_w) = R'_w`,
     `A_w(cantorDiskEmbed s) = cantorDiskEmbed (Φ.eval s)` on `cyl(w)`).
   - **Lemma G0 (`imageRect_pairwise_disjoint`)**: injectivity of `Φ.eval` implies pairwise
     disjointness of all `N³` target rectangles `R'_w`, specialized to any `ReversibleTM` via
     `R.bijective_eval.injective`.
-/

@[expose] public section

open Function Set TopologicalSpace

namespace S4TuringPoisson.CMPP

/-! ## 1. Axis-Parallel Planar Rectangles (`AxisRect`) -/

/-- Closed axis-parallel planar rectangle `[xMin, xMax] × [yMin, yMax] ⊂ ℝ²`. -/
structure AxisRect where
  /-- Left `x`-coordinate bound. -/
  xMin : ℝ
  /-- Right `x`-coordinate bound. -/
  xMax : ℝ
  /-- Lower `y`-coordinate bound. -/
  yMin : ℝ
  /-- Upper `y`-coordinate bound. -/
  yMax : ℝ
  /-- Horizontal non-degeneracy `xMin ≤ xMax`. -/
  hx : xMin ≤ xMax
  /-- Vertical non-degeneracy `yMin ≤ yMax`. -/
  hy : yMin ≤ yMax

namespace AxisRect

/-- Underlying subset `{ p ∈ ℝ² | p 0 ∈ [xMin, xMax] ∧ p 1 ∈ [yMin, yMax] }` of `EuclideanPlane`. -/
def toSet (R : AxisRect) : Set EuclideanPlane :=
  { p : EuclideanPlane | p 0 ∈ Set.Icc R.xMin R.xMax ∧ p 1 ∈ Set.Icc R.yMin R.yMax }

/-- Horizontal width `xMax - xMin` of an `AxisRect`. -/
def width (R : AxisRect) : ℝ := R.xMax - R.xMin

/-- Vertical height `yMax - yMin` of an `AxisRect`. -/
def height (R : AxisRect) : ℝ := R.yMax - R.yMin

/-- Geometric center `((xMin + xMax) / 2, (yMin + yMax) / 2)` of an `AxisRect`. -/
noncomputable def center (R : AxisRect) : EuclideanPlane :=
  WithLp.toLp 2 ![(R.xMin + R.xMax) / 2, (R.yMin + R.yMax) / 2]

/-- Rigid translation of an `AxisRect` by `(dx, dy)`. -/
def translate (R : AxisRect) (dx dy : ℝ) : AxisRect :=
  { xMin := R.xMin + dx
    xMax := R.xMax + dx
    yMin := R.yMin + dy
    yMax := R.yMax + dy
    hx := by linarith [R.hx]
    hy := by linarith [R.hy] }

/-- Smallest axis-parallel bounding rectangle containing `R` and `R.translate dx dy` (swept tube for
axis-aligned translations). -/
def tubeRect (R : AxisRect) (dx dy : ℝ) : AxisRect :=
  { xMin := min R.xMin (R.xMin + dx)
    xMax := max R.xMax (R.xMax + dx)
    yMin := min R.yMin (R.yMin + dy)
    yMax := max R.yMax (R.yMax + dy)
    hx := le_trans (min_le_left _ _) (le_trans R.hx (le_max_left _ _))
    hy := le_trans (min_le_left _ _) (le_trans R.hy (le_max_left _ _)) }

/-- Extensionality for `AxisRect` via its four endpoint coordinates. -/
-- tier: T0
@[ext]
theorem ext {R₁ R₂ : AxisRect} (hxMin : R₁.xMin = R₂.xMin) (hxMax : R₁.xMax = R₂.xMax)
    (hyMin : R₁.yMin = R₂.yMin) (hyMax : R₁.yMax = R₂.yMax) : R₁ = R₂ := by
  rcases R₁ with ⟨_, _, _, _, _, _⟩
  rcases R₂ with ⟨_, _, _, _, _, _⟩
  simp_all

/-- Pointwise membership characterization for `AxisRect.toSet`. -/
-- tier: T0
@[simp]
theorem mem_toSet_iff (R : AxisRect) (p : EuclideanPlane) :
    p ∈ R.toSet ↔ p 0 ∈ Set.Icc R.xMin R.xMax ∧ p 1 ∈ Set.Icc R.yMin R.yMax := by
  rw [AxisRect.toSet]
  simp

/-- Width of any `AxisRect` is non-negative. -/
-- tier: T0
theorem width_nonneg (R : AxisRect) : 0 ≤ R.width := by
  unfold width
  linarith [R.hx]

/-- Height of any `AxisRect` is non-negative. -/
-- tier: T0
theorem height_nonneg (R : AxisRect) : 0 ≤ R.height := by
  unfold height
  linarith [R.hy]

/-- First coordinate of `R.center`. -/
-- tier: T0
@[simp]
theorem center_zero (R : AxisRect) : R.center 0 = (R.xMin + R.xMax) / 2 := by
  simp [center]

/-- Second coordinate of `R.center`. -/
-- tier: T0
@[simp]
theorem center_one (R : AxisRect) : R.center 1 = (R.yMin + R.yMax) / 2 := by
  simp [center]

/-- Left `x`-endpoint of `R.translate dx dy`. -/
-- tier: T0
@[simp]
theorem translate_xMin (R : AxisRect) (dx dy : ℝ) :
    (R.translate dx dy).xMin = R.xMin + dx := by
  unfold translate
  simp

/-- Right `x`-endpoint of `R.translate dx dy`. -/
-- tier: T0
@[simp]
theorem translate_xMax (R : AxisRect) (dx dy : ℝ) :
    (R.translate dx dy).xMax = R.xMax + dx := by
  unfold translate
  simp

/-- Lower `y`-endpoint of `R.translate dx dy`. -/
-- tier: T0
@[simp]
theorem translate_yMin (R : AxisRect) (dx dy : ℝ) :
    (R.translate dx dy).yMin = R.yMin + dy := by
  unfold translate
  simp

/-- Upper `y`-endpoint of `R.translate dx dy`. -/
-- tier: T0
@[simp]
theorem translate_yMax (R : AxisRect) (dx dy : ℝ) :
    (R.translate dx dy).yMax = R.yMax + dy := by
  unfold translate
  simp

/-- Rigid translation preserves `AxisRect.width`. -/
-- tier: T0
@[simp]
theorem translate_width (R : AxisRect) (dx dy : ℝ) :
    (R.translate dx dy).width = R.width := by
  unfold width
  unfold translate
  field_simp
  linarith

/-- Rigid translation preserves `AxisRect.height`. -/
-- tier: T0
@[simp]
theorem translate_height (R : AxisRect) (dx dy : ℝ) :
    (R.translate dx dy).height = R.height := by
  unfold height
  simp only [translate]
  linarith

/-- Left `x`-endpoint of `R.tubeRect dx dy`. -/
-- tier: T0
@[simp]
theorem tubeRect_xMin (R : AxisRect) (dx dy : ℝ) :
    (R.tubeRect dx dy).xMin = min R.xMin (R.xMin + dx) := by
  rfl

/-- Right `x`-endpoint of `R.tubeRect dx dy`. -/
-- tier: T0
@[simp]
theorem tubeRect_xMax (R : AxisRect) (dx dy : ℝ) :
    (R.tubeRect dx dy).xMax = max R.xMax (R.xMax + dx) := by
  rfl

/-- Lower `y`-endpoint of `R.tubeRect dx dy`. -/
-- tier: T0
@[simp]
theorem tubeRect_yMin (R : AxisRect) (dx dy : ℝ) :
    (R.tubeRect dx dy).yMin = min R.yMin (R.yMin + dy) := by
  rfl

/-- Upper `y`-endpoint of `R.tubeRect dx dy`. -/
-- tier: T0
@[simp]
theorem tubeRect_yMax (R : AxisRect) (dx dy : ℝ) :
    (R.tubeRect dx dy).yMax = max R.yMax (R.yMax + dy) := by
  rfl

/-- `R.center` belongs to `R.toSet`. -/
-- tier: T1
theorem center_mem_toSet (R : AxisRect) : R.center ∈ R.toSet := by
  rw [mem_toSet_iff, center_zero, center_one]
  exact ⟨⟨by linarith [R.hx], by linarith [R.hx]⟩, ⟨by linarith [R.hy], by linarith [R.hy]⟩⟩

/-- Every `AxisRect.toSet` is nonempty (witnessed by `R.center`). -/
-- tier: T1
theorem nonempty_toSet (R : AxisRect) : R.toSet.Nonempty :=
  ⟨R.center, R.center_mem_toSet⟩

/-- Every `AxisRect.toSet` is closed in `EuclideanPlane`. -/
-- tier: T1
theorem isClosed_toSet (R : AxisRect) : IsClosed R.toSet := by
  have h0 : Continuous fun p : EuclideanPlane ↦ p 0 :=
    PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0
  have h1 : Continuous fun p : EuclideanPlane ↦ p 1 :=
    PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1
  exact (isClosed_Icc.preimage h0).inter (isClosed_Icc.preimage h1)

/-- Every `AxisRect.toSet` is compact in `EuclideanPlane`. -/
-- tier: T1
theorem isCompact_toSet (R : AxisRect) : IsCompact R.toSet := by
  let φ : ℝ × ℝ → EuclideanPlane := fun q ↦ WithLp.toLp 2 ![q.1, q.2]
  have hcont : Continuous φ := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦ ?_)
    fin_cases i
    · simpa using continuous_fst
    · simpa using continuous_snd
  have heq : φ '' (Set.Icc R.xMin R.xMax ×ˢ Set.Icc R.yMin R.yMax) = R.toSet := by
    ext p
    simp only [Set.mem_image, Set.mem_prod, mem_toSet_iff, Prod.exists]
    constructor
    · rintro ⟨x, y, ⟨hx, hy⟩, rfl⟩
      simpa [φ] using And.intro hx hy
    · intro ⟨hx, hy⟩
      refine ⟨p 0, p 1, ⟨hx, hy⟩, ?_⟩
      ext i
      fin_cases i <;> simp [φ]
  rw [← heq]
  exact (isCompact_Icc.prod isCompact_Icc).image hcont

/-- Translating by `(0, 0)` is the identity on `AxisRect`. -/
-- tier: T1
@[simp]
theorem translate_zero (R : AxisRect) : R.translate 0 0 = R := by
  ext <;> simp

/-- Composition of rigid translations on `AxisRect` adds displacements. -/
-- tier: T1
theorem translate_translate (R : AxisRect) (dx₁ dy₁ dx₂ dy₂ : ℝ) :
    (R.translate dx₁ dy₁).translate dx₂ dy₂ = R.translate (dx₁ + dx₂) (dy₁ + dy₂) := by
  ext <;> simp [add_assoc]

/-- Image of `R.toSet` under planar vector addition by `(dx, dy)` equals
`(R.translate dx dy).toSet`. -/
-- tier: T1
theorem image_add_toSet (R : AxisRect) (dx dy : ℝ) :
    (fun p : EuclideanPlane ↦ p + WithLp.toLp 2 ![dx, dy]) '' R.toSet =
      (R.translate dx dy).toSet := by
  ext q
  simp only [Set.mem_image, mem_toSet_iff, translate_xMin, translate_xMax, translate_yMin,
    translate_yMax]
  constructor
  · rintro ⟨p, ⟨hx, hy⟩, rfl⟩
    simp only [PiLp.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, ⟨by linarith [hy.1], by linarith [hy.2]⟩⟩
  · rintro ⟨hx, hy⟩
    refine ⟨q - WithLp.toLp 2 ![dx, dy], ?_, sub_add_cancel _ _⟩
    simp only [PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, ⟨by linarith [hy.1], by linarith [hy.2]⟩⟩

/-- Monotonicity of `AxisRect.toSet` with respect to endpoint inclusion. -/
-- tier: T1
theorem toSet_mono {R₁ R₂ : AxisRect} (hxMin : R₂.xMin ≤ R₁.xMin) (hxMax : R₁.xMax ≤ R₂.xMax)
    (hyMin : R₂.yMin ≤ R₁.yMin) (hyMax : R₁.yMax ≤ R₂.yMax) :
    R₁.toSet ⊆ R₂.toSet := by
  intro p hp
  rw [mem_toSet_iff] at hp ⊢
  exact ⟨⟨le_trans hxMin hp.1.1, le_trans hp.1.2 hxMax⟩,
    ⟨le_trans hyMin hp.2.1, le_trans hp.2.2 hyMax⟩⟩

/-- `R.toSet` is contained in `(R.tubeRect dx dy).toSet`. -/
-- tier: T1
theorem subset_tubeRect_self (R : AxisRect) (dx dy : ℝ) :
    R.toSet ⊆ (R.tubeRect dx dy).toSet :=
  toSet_mono (min_le_left _ _) (le_max_left _ _) (min_le_left _ _) (le_max_left _ _)

/-- `(R.translate dx dy).toSet` is contained in `(R.tubeRect dx dy).toSet`. -/
-- tier: T1
theorem translate_subset_tubeRect (R : AxisRect) (dx dy : ℝ) :
    (R.translate dx dy).toSet ⊆ (R.tubeRect dx dy).toSet :=
  toSet_mono (min_le_right _ _) (le_max_right _ _) (min_le_right _ _) (le_max_right _ _)

/-- Every point along the linear segment `p + t • (dx, dy)` (`p ∈ R.toSet`, `t ∈ [0, 1]`) lies
inside `(R.tubeRect dx dy).toSet`. -/
-- tier: T1
theorem mem_tubeRect_of_mem_Icc {R : AxisRect} {p : EuclideanPlane} (hp : p ∈ R.toSet)
    (dx dy : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    p + t • WithLp.toLp 2 ![dx, dy] ∈ (R.tubeRect dx dy).toSet := by
  rw [mem_toSet_iff] at hp ⊢
  simp only [tubeRect_xMin, tubeRect_xMax, tubeRect_yMin, tubeRect_yMax, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Set.mem_Icc]
  have hx_lo : min R.xMin (R.xMin + dx) ≤ p 0 + t * dx := by
    rcases le_or_gt 0 dx with hdx | hdx
    · rw [min_eq_left (by linarith)]
      nlinarith [hp.1.1, ht.1]
    · rw [min_eq_right (by linarith)]
      nlinarith [hp.1.1, ht.2]
  have hx_hi : p 0 + t * dx ≤ max R.xMax (R.xMax + dx) := by
    rcases le_or_gt 0 dx with hdx | hdx
    · rw [max_eq_right (by linarith)]
      nlinarith [hp.1.2, ht.2]
    · rw [max_eq_left (by linarith)]
      nlinarith [hp.1.2, ht.1]
  have hy_lo : min R.yMin (R.yMin + dy) ≤ p 1 + t * dy := by
    rcases le_or_gt 0 dy with hdy | hdy
    · rw [min_eq_left (by linarith)]
      nlinarith [hp.2.1, ht.1]
    · rw [min_eq_right (by linarith)]
      nlinarith [hp.2.1, ht.2]
  have hy_hi : p 1 + t * dy ≤ max R.yMax (R.yMax + dy) := by
    rcases le_or_gt 0 dy with hdy | hdy
    · rw [max_eq_right (by linarith)]
      nlinarith [hp.2.2, ht.2]
    · rw [max_eq_left (by linarith)]
      nlinarith [hp.2.2, ht.1]
  exact ⟨⟨hx_lo, hx_hi⟩, ⟨hy_lo, hy_hi⟩⟩

/-- Disjointness of `x`-intervals implies disjointness of `AxisRect.toSet`. -/
-- tier: T1
theorem disjoint_toSet_of_disjoint_x {R₁ R₂ : AxisRect}
    (hx : Disjoint (Set.Icc R₁.xMin R₁.xMax) (Set.Icc R₂.xMin R₂.xMax)) :
    Disjoint R₁.toSet R₂.toSet :=
  Set.disjoint_left.mpr fun _ h₁ h₂ ↦ Set.disjoint_left.mp hx h₁.1 h₂.1

/-- Disjointness of `y`-intervals implies disjointness of `AxisRect.toSet`. -/
-- tier: T1
theorem disjoint_toSet_of_disjoint_y {R₁ R₂ : AxisRect}
    (hy : Disjoint (Set.Icc R₁.yMin R₁.yMax) (Set.Icc R₂.yMin R₂.yMax)) :
    Disjoint R₁.toSet R₂.toSet :=
  Set.disjoint_left.mpr fun _ h₁ h₂ ↦ Set.disjoint_left.mp hy h₁.2 h₂.2

/-- Image of `R.toSet` under any positive diagonal scaling and translation
`(sx * x + dx, sy * y + dy)` (`sx > 0`, `sy > 0`). -/
-- tier: T1
theorem image_posScaleTranslate (R : AxisRect) {sx sy : ℝ} (hsx : 0 < sx) (hsy : 0 < sy)
    (dx dy : ℝ) :
    (fun p : EuclideanPlane ↦ WithLp.toLp 2 ![sx * p 0 + dx, sy * p 1 + dy]) '' R.toSet =
      { q : EuclideanPlane |
        q 0 ∈ Set.Icc (sx * R.xMin + dx) (sx * R.xMax + dx) ∧
        q 1 ∈ Set.Icc (sy * R.yMin + dy) (sy * R.yMax + dy) } := by
  ext q
  simp only [Set.mem_image, mem_toSet_iff, Set.mem_ofPred_eq, Set.mem_Icc]
  constructor
  · rintro ⟨p, ⟨⟨hx₁, hx₂⟩, ⟨hy₁, hy₂⟩⟩, rfl⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩
  · rintro ⟨⟨hqx₁, hqx₂⟩, ⟨hqy₁, hqy₂⟩⟩
    refine ⟨WithLp.toLp 2 ![(q 0 - dx) / sx, (q 1 - dy) / sy], ?_, ?_⟩
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      refine ⟨⟨(le_div_iff₀ hsx).mpr (by linarith), (div_le_iff₀ hsx).mpr (by linarith)⟩,
        ⟨(le_div_iff₀ hsy).mpr (by linarith), (div_le_iff₀ hsy).mpr (by linarith)⟩⟩
    · ext i
      fin_cases i
      · simp only [Fin.zero_eta, Matrix.cons_val_zero]
        field_simp [hsx.ne']
        ring
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        field_simp [hsy.ne']
        ring

end AxisRect

/-- Canonical quarter-square `[0, 1/4] × [0, 1/4]` containing the rescaled square Cantor set. -/
noncomputable def quarterSquare : AxisRect :=
  { xMin := 0
    xMax := 1 / 4
    yMin := 0
    yMax := 1 / 4
    hx := by norm_num
    hy := by norm_num }

/-- Left `x`-endpoint of `quarterSquare`. -/
-- tier: T0
@[simp]
theorem quarterSquare_xMin : quarterSquare.xMin = 0 := by
  simp [quarterSquare]

/-- Right `x`-endpoint of `quarterSquare`. -/
-- tier: T0
@[simp]
theorem quarterSquare_xMax : quarterSquare.xMax = 1 / 4 := by
  unfold quarterSquare
  simp

/-- Lower `y`-endpoint of `quarterSquare`. -/
-- tier: T0
@[simp]
theorem quarterSquare_yMin : quarterSquare.yMin = 0 := by
  simp [quarterSquare]

/-- Upper `y`-endpoint of `quarterSquare`. -/
-- tier: T0
@[simp]
theorem quarterSquare_yMax : quarterSquare.yMax = 1 / 4 := by
  simp [quarterSquare]

/-- `quarterSquare.toSet` lies strictly inside the open unit disk `UnitDisk2`. -/
-- tier: T1
theorem quarterSquare_subset_unitDisk2 : quarterSquare.toSet ⊆ UnitDisk2 := by
  intro p hp
  rw [AxisRect.mem_toSet_iff, quarterSquare_xMin, quarterSquare_xMax, quarterSquare_yMin,
    quarterSquare_yMax] at hp
  have hp_eq : WithLp.toLp 2 ![p 0, p 1] = p := by
    ext i
    fin_cases i <;> simp
  rw [← hp_eq]
  exact toLp_mem_unitDisk2_of_mem_Ioo
    ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
    ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩

/-! ## 2. Closed Cantor Prefix Intervals & Prefix Compatibility -/

/-- Closed rescaled middle-Cantor interval `[K / (4 B^m), (K + 1) / (4 B^m)] ⊆ [0, 1/4]`
associated to a finite digit prefix `p : Fin m → Fin N`. -/
noncomputable def cantorClosedInterval {N m : ℕ} (p : Fin m → Fin N) : Set ℝ :=
  let B : ℝ := (cantorBase N : ℝ)
  let K : ℝ := (cantorPrefixCode (cantorBase N) (fun j ↦ (p j).1) : ℝ)
  Set.Icc (K / (4 * B ^ m)) ((K + 1) / (4 * B ^ m))

/-- Every even digit `2 * d.1` for `d : Fin N` satisfies `2 * d.1 + 1 ≤ cantorBase N`. -/
-- tier: T0
theorem two_mul_fin_add_one_le_cantorBase {N : ℕ} (d : Fin N) :
    2 * d.1 + 1 ≤ cantorBase N := by
  have := d.2
  unfold cantorBase
  omega

/-- `cantorPrefixCode` of an empty (`Fin 0`) prefix is `0`. -/
-- tier: T0
@[simp]
theorem cantorPrefixCode_zero (B : ℕ) (p : Fin 0 → ℕ) :
    cantorPrefixCode B p = 0 := by
  simp [cantorPrefixCode]

/-- `cantorPrefixCode` of a 1-digit (`Fin 1`) prefix `p` is `2 * p 0`. -/
-- tier: T0
@[simp]
theorem cantorPrefixCode_one (B : ℕ) (p : Fin 1 → ℕ) :
    cantorPrefixCode B p = 2 * p 0 := by
  simp [cantorPrefixCode]

/-- `cantorPrefixCode` of a 2-digit (`Fin 2`) prefix `p` is `2 * p 0 * B + 2 * p 1`. -/
-- tier: T1
theorem cantorPrefixCode_two (B : ℕ) (p : Fin 2 → ℕ) :
    cantorPrefixCode B p = 2 * p 0 * B + 2 * p 1 := by
  simp only [cantorPrefixCode, Fin.last]
  have h0 : (⟨0, by decide⟩ : Fin 1).castSucc = (0 : Fin 2) := rfl
  have h1 : (⟨1, by decide⟩ : Fin 2) = 1 := rfl
  rw [h0, h1]
  ring

/-- `cantorPrefixCode` of a 3-digit (`Fin 3`) prefix `p` is
`2 * p 0 * B ^ 2 + 2 * p 1 * B + 2 * p 2`. -/
-- tier: T1
theorem cantorPrefixCode_three (B : ℕ) (p : Fin 3 → ℕ) :
    cantorPrefixCode B p = 2 * p 0 * B ^ 2 + 2 * p 1 * B + 2 * p 2 := by
  rw [cantorPrefixCode, cantorPrefixCode_two]
  have h0 : (Fin.castSucc (0 : Fin 2)) = (0 : Fin 3) := rfl
  have h1 : (Fin.castSucc (1 : Fin 2)) = (1 : Fin 3) := rfl
  have h2 : (Fin.last 2) = (2 : Fin 3) := rfl
  rw [h0, h1, h2]
  ring

/-- `cantorClosedInterval p` is closed. -/
-- tier: T1
theorem isClosed_cantorClosedInterval {N m : ℕ} (p : Fin m → Fin N) :
    IsClosed (cantorClosedInterval p) :=
  isClosed_Icc

/-- `cantorClosedInterval p` is compact. -/
-- tier: T1
theorem isCompact_cantorClosedInterval {N m : ℕ} (p : Fin m → Fin N) :
    IsCompact (cantorClosedInterval p) :=
  isCompact_Icc

/-- `cantorClosedInterval p` is nonempty. -/
-- tier: T1
theorem cantorClosedInterval_nonempty {N m : ℕ} (p : Fin m → Fin N) :
    (cantorClosedInterval p).Nonempty := by
  unfold cantorClosedInterval
  refine Set.nonempty_Icc.mpr ?_
  have hden : 0 ≤ (4 : ℝ) * (cantorBase N : ℝ) ^ m := by
    have := cantorBase_pos N
    positivity
  exact div_le_div_of_nonneg_right (by linarith) hden

/-- `cantorClosedInterval p` is contained in `cantorOpenInterval p`. -/
-- tier: T1
theorem cantorClosedInterval_subset_cantorOpenInterval {N m : ℕ} (p : Fin m → Fin N) :
    cantorClosedInterval p ⊆ cantorOpenInterval p := by
  intro x hx
  unfold cantorClosedInterval at hx
  unfold cantorOpenInterval
  have hden : 0 < (4 : ℝ) * (cantorBase N : ℝ) ^ m := by
    have := cantorBase_pos N
    positivity
  exact ⟨lt_of_lt_of_le (div_lt_div_of_pos_right (by linarith) hden) hx.1,
    lt_of_le_of_lt hx.2 (div_lt_div_of_pos_right (by linarith) hden)⟩

/-- If `α : ℕ → Fin N` agrees with `p : Fin m → Fin N` on `{0, …, m - 1}`, then
`scaledCantorCoord α ∈ cantorClosedInterval p`. -/
-- tier: T2
theorem scaledCantorCoord_mem_cantorClosedInterval {N m : ℕ} (α : ℕ → Fin N)
    (p : Fin m → Fin N) (hp : ∀ j : Fin m, α j.1 = p j) :
    scaledCantorCoord α ∈ cantorClosedInterval p := by
  have heq : (fun j : Fin m ↦ (α j.1).1) = fun j : Fin m ↦ (p j).1 := by
    funext j
    rw [hp j]
  unfold cantorClosedInterval scaledCantorCoord
  rw [← heq]
  have hB : 0 < (cantorBase N : ℝ) ^ m := by
    have := cantorBase_pos N
    positivity
  have hden : 0 < (4 : ℝ) * (cantorBase N : ℝ) ^ m := by positivity
  have hlo := (div_le_iff₀ hB).mp (prefix_div_le_cantorCoord α m)
  have hhi := (le_div_iff₀ hB).mp (cantorCoord_le_prefix_add_one_div α m)
  exact ⟨(div_le_iff₀ hden).mpr (by linarith), (le_div_iff₀ hden).mpr (by linarith)⟩

/-- Every `cantorClosedInterval p` lies inside `[0, 1/4]`. -/
-- tier: T2
theorem cantorClosedInterval_subset_Icc_quarter {N m : ℕ} (p : Fin m → Fin N) :
    cantorClosedInterval p ⊆ Set.Icc (0 : ℝ) (1 / 4) := by
  intro x hx
  unfold cantorClosedInterval at hx
  have hB3 : 3 ≤ cantorBase N := three_le_cantorBase N
  have hden : 0 < (4 : ℝ) * (cantorBase N : ℝ) ^ m := by
    have := cantorBase_pos N
    positivity
  have hK_nat := cantorPrefixCode_add_one_le_pow (cantorBase N) (by omega)
    (fun j : Fin m ↦ (p j).1) (fun j ↦ by have := two_mul_fin_add_one_le_cantorBase (p j); omega)
  have hK_real : (cantorPrefixCode (cantorBase N) (fun j ↦ (p j).1) : ℝ) + 1 ≤
      (cantorBase N : ℝ) ^ m := by
    exact_mod_cast hK_nat
  constructor
  · exact le_trans (div_nonneg (Nat.cast_nonneg _) hden.le) hx.1
  · refine le_trans hx.2 ?_
    rw [div_le_iff₀ hden]
    linarith

/-- Extending a prefix `p : Fin (m + 1) → Fin N` shrinks `cantorClosedInterval` inside the
interval of its length-`m` truncation `j ↦ p j.castSucc`. -/
-- tier: T2
theorem cantorClosedInterval_castSucc_subset {N m : ℕ} (p : Fin (m + 1) → Fin N) :
    cantorClosedInterval p ⊆ cantorClosedInterval (fun j : Fin m ↦ p j.castSucc) := by
  intro x hx
  unfold cantorClosedInterval at hx ⊢
  have hB_pos_raw : 0 < (cantorBase N : ℝ) := by exact_mod_cast cantorBase_pos N
  have hd_le_raw : 2 * ((p (Fin.last m)).1 : ℝ) + 1 ≤ (cantorBase N : ℝ) := by
    exact_mod_cast two_mul_fin_add_one_le_cantorBase (p (Fin.last m))
  set B : ℝ := (cantorBase N : ℝ)
  have hB_pos : 0 < B := hB_pos_raw
  have hd_le : 2 * ((p (Fin.last m)).1 : ℝ) + 1 ≤ B := hd_le_raw
  have hden_m : 0 < 4 * B ^ m := by positivity
  have hden_succ : 0 < 4 * B ^ (m + 1) := by positivity
  let p' : Fin m → ℕ := fun j ↦ (p j.castSucc).1
  set Km : ℝ := (cantorPrefixCode (cantorBase N) p' : ℝ)
  have hcode :
      (cantorPrefixCode (cantorBase N) (fun j : Fin (m + 1) ↦ (p j).1) : ℝ) =
        B * Km + 2 * ((p (Fin.last m)).1 : ℝ) := by
    simp [cantorPrefixCode, B, Km, p']
  have hd_nonneg : (0 : ℝ) ≤ ((p (Fin.last m)).1 : ℝ) := Nat.cast_nonneg _
  constructor
  · refine le_trans ?_ hx.1
    rw [hcode, div_le_div_iff₀ hden_m hden_succ, pow_succ]
    nlinarith
  · refine le_trans hx.2 ?_
    rw [hcode, div_le_div_iff₀ hden_succ hden_m, pow_succ]
    nlinarith

/-- Prefix antitonicity of `cantorClosedInterval`: if `m₁ ≤ m₂` and `p₁` agrees with the first
`m₁` digits of `p₂`, then `cantorClosedInterval p₂ ⊆ cantorClosedInterval p₁`. -/
-- tier: T2
theorem cantorClosedInterval_antitone_prefix {N m₁ m₂ : ℕ} (hm : m₁ ≤ m₂)
    {p₁ : Fin m₁ → Fin N} {p₂ : Fin m₂ → Fin N}
    (hpref : ∀ j : Fin m₁, p₁ j = p₂ (Fin.castLE hm j)) :
    cantorClosedInterval p₂ ⊆ cantorClosedInterval p₁ := by
  induction m₂ with
  | zero =>
    have hm0 : m₁ = 0 := Nat.eq_zero_of_le_zero hm
    subst hm0
    have hp : p₁ = p₂ := Subsingleton.elim p₁ p₂
    rw [hp]
  | succ m ih =>
    rcases Nat.of_le_succ hm with hle | rfl
    · refine Subset.trans (cantorClosedInterval_castSucc_subset p₂) (ih hle fun j ↦ ?_)
      simpa using hpref j
    · have hp : p₁ = p₂ := funext fun j ↦ by simpa using hpref j
      rw [hp]

/-- Distinct prefixes `p₁ ≠ p₂` of the same length `m` have disjoint closed middle-Cantor intervals
(proved directly from `two_le_abs_cantorPrefixCode_sub`). -/
-- tier: T2
theorem disjoint_cantorClosedInterval_of_ne {N m : ℕ} {p₁ p₂ : Fin m → Fin N} (hne : p₁ ≠ p₂) :
    Disjoint (cantorClosedInterval p₁) (cantorClosedInterval p₂) := by
  rw [Set.disjoint_iff]
  rintro x ⟨hx₁, hx₂⟩
  unfold cantorClosedInterval at hx₁ hx₂
  have hden : 0 < (4 : ℝ) * (cantorBase N : ℝ) ^ m := by
    have := cantorBase_pos N
    positivity
  have hfn_ne : (fun j : Fin m ↦ (p₁ j).1) ≠ (fun j : Fin m ↦ (p₂ j).1) := by
    intro heq
    apply hne
    funext j
    exact Fin.ext (congrFun heq j)
  have hsep := two_le_abs_cantorPrefixCode_sub (three_le_cantorBase N) hfn_ne
    (fun j ↦ by have := two_mul_fin_add_one_le_cantorBase (p₁ j); omega)
    (fun j ↦ by have := two_mul_fin_add_one_le_cantorBase (p₂ j); omega)
  let c₁ : ℕ := cantorPrefixCode (cantorBase N) (fun j ↦ (p₁ j).1)
  let c₂ : ℕ := cantorPrefixCode (cantorBase N) (fun j ↦ (p₂ j).1)
  change (2 : ℤ) ≤ |(c₁ : ℤ) - (c₂ : ℤ)| at hsep
  have h₁l := (div_le_iff₀ hden).mp hx₁.1
  have h₁r := (le_div_iff₀ hden).mp hx₁.2
  have h₂l := (div_le_iff₀ hden).mp hx₂.1
  have h₂r := (le_div_iff₀ hden).mp hx₂.2
  rcases le_or_gt c₂ c₁ with hle | hlt
  · have hc : c₂ + 2 ≤ c₁ := by
      rw [abs_of_nonneg (by omega)] at hsep
      omega
    have hcR : (c₂ : ℝ) + 2 ≤ (c₁ : ℝ) := by exact_mod_cast hc
    linarith
  · have hc : c₁ + 2 ≤ c₂ := by
      rw [abs_of_neg (by omega)] at hsep
      omega
    have hcR : (c₁ : ℝ) + 2 ≤ (c₂ : ℝ) := by exact_mod_cast hc
    linarith

/-- If `m₁ ≤ m₂` and `p₁` differs from `p₂` at some position `j < m₁`, then
`cantorClosedInterval p₁` and `cantorClosedInterval p₂` are disjoint (`geometry_spec.md` §2.1). -/
-- tier: T2
theorem disjoint_cantorClosedInterval_of_not_prefix {N m₁ m₂ : ℕ} (hm : m₁ ≤ m₂)
    {p₁ : Fin m₁ → Fin N} {p₂ : Fin m₂ → Fin N}
    (hmis : ∃ j : Fin m₁, p₁ j ≠ p₂ (Fin.castLE hm j)) :
    Disjoint (cantorClosedInterval p₁) (cantorClosedInterval p₂) := by
  obtain ⟨j, hj⟩ := hmis
  let p₂' : Fin m₁ → Fin N := fun i ↦ p₂ (Fin.castLE hm i)
  have hne : p₁ ≠ p₂' := fun heq ↦ hj (congrFun heq j)
  exact (disjoint_cantorClosedInterval_of_ne hne).mono_right
    (cantorClosedInterval_antitone_prefix hm fun _ ↦ rfl)

/-- Symmetric prefix compatibility: whenever two closed middle-Cantor intervals intersect, their
prefixes agree at every common index `j < min m₁ m₂`. -/
-- tier: T2
theorem eq_of_cantorClosedInterval_inter_nonempty {N m₁ m₂ : ℕ}
    {p₁ : Fin m₁ → Fin N} {p₂ : Fin m₂ → Fin N}
    (hinter : (cantorClosedInterval p₁ ∩ cantorClosedInterval p₂).Nonempty)
    (j : ℕ) (hj₁ : j < m₁) (hj₂ : j < m₂) :
    p₁ ⟨j, hj₁⟩ = p₂ ⟨j, hj₂⟩ := by
  by_contra hne
  obtain ⟨x, hx₁, hx₂⟩ := hinter
  rcases le_total m₁ m₂ with hm | hm
  · have hd := disjoint_cantorClosedInterval_of_not_prefix hm (p₁ := p₁) (p₂ := p₂)
      ⟨⟨j, hj₁⟩, hne⟩
    exact Set.disjoint_left.mp hd hx₁ hx₂
  · have hd := disjoint_cantorClosedInterval_of_not_prefix hm (p₁ := p₂) (p₂ := p₁)
      ⟨⟨j, hj₂⟩, Ne.symm hne⟩
    exact Set.disjoint_left.mp hd hx₂ hx₁

/-! ## 3. One-Digit & Multi-Digit Shift / Tail Identities for `scaledCantorCoord` -/

/-- General `m`-digit `prefix + scaledTail` identity for `scaledCantorCoord`. -/
-- tier: T2
theorem scaledCantorCoord_eq_prefix_add_scaledTail {N : ℕ} (α : ℕ → Fin N) (m : ℕ) :
    scaledCantorCoord α =
      (cantorPrefixCode (cantorBase N) (fun j : Fin m ↦ (α j.1).1) : ℝ) /
        (4 * (cantorBase N : ℝ) ^ m) +
      ((cantorBase N : ℝ) ^ m)⁻¹ * scaledCantorCoord (fun j ↦ α (j + m)) := by
  unfold scaledCantorCoord
  rw [cantorCoord_eq_prefix_add_tail α m]
  ring

/-- General `m`-digit `(prefix + cantorCoord tail) / (4 B^m)` identity (`geometry_spec.md` §1.1). -/
-- tier: T2
theorem scaledCantorCoord_eq_prefix_add_tail {N : ℕ} (α : ℕ → Fin N) (m : ℕ) :
    scaledCantorCoord α =
      ((cantorPrefixCode (cantorBase N) (fun j : Fin m ↦ (α j.1).1) : ℝ) +
        cantorCoord (fun j ↦ α (j + m))) /
        (4 * (cantorBase N : ℝ) ^ m) := by
  have hB0 : ((cantorBase N : ℝ) ^ m) ≠ 0 := by
    have := cantorBase_pos N
    positivity
  unfold scaledCantorCoord
  rw [cantorCoord_eq_prefix_add_tail α m]
  field_simp [hB0]

/-- 1-digit head-and-tail identity relating `scaledCantorCoord α` to `α 0` and
`scaledCantorCoord (fun j ↦ α (j + 1))`. -/
-- tier: T2
theorem scaledCantorCoord_eq_head_add_tail {N : ℕ} (α : ℕ → Fin N) :
    scaledCantorCoord α =
      ((α 0).1 : ℝ) / (2 * (cantorBase N : ℝ)) +
        (cantorBase N : ℝ)⁻¹ * scaledCantorCoord (fun j ↦ α (j + 1)) := by
  have h := scaledCantorCoord_eq_prefix_add_scaledTail α 1
  rw [cantorPrefixCode_one] at h
  simp only [Fin.val_zero, pow_one, Nat.cast_mul, Nat.cast_ofNat] at h
  rw [h]
  have hB0 : (cantorBase N : ℝ) ≠ 0 := by exact_mod_cast (cantorBase_pos N).ne'
  field_simp [hB0]
  ring

/-- Inverse 1-digit shift formula expressing `scaledCantorCoord (fun j ↦ α (j + 1))` in terms of
`scaledCantorCoord α` and `α 0`. -/
-- tier: T2
theorem scaledCantorCoord_shift_one {N : ℕ} (α : ℕ → Fin N) :
    scaledCantorCoord (fun j ↦ α (j + 1)) =
      (cantorBase N : ℝ) * scaledCantorCoord α - ((α 0).1 : ℝ) / 2 := by
  have hB0 : (cantorBase N : ℝ) ≠ 0 := by exact_mod_cast (cantorBase_pos N).ne'
  rw [scaledCantorCoord_eq_head_add_tail α]
  field_simp [hB0]
  ring

/-- 1-digit `(2 d₀ + tail) / (4 B)` form of `scaledCantorCoord` (`geometry_spec.md` §1.1). -/
-- tier: T2
theorem scaledCantorCoord_eq_one_digit_add_tail {N : ℕ} (α : ℕ → Fin N) :
    scaledCantorCoord α =
      (2 * ((α 0).1 : ℝ) + cantorCoord (fun j ↦ α (j + 1))) / (4 * (cantorBase N : ℝ)) := by
  have h := scaledCantorCoord_eq_prefix_add_tail α 1
  rw [cantorPrefixCode_one] at h
  simpa [pow_one] using h

/-- 2-digit `(2 d₀ B + 2 d₁) / (4 B²) + B⁻² * scaledTail` form of `scaledCantorCoord`. -/
-- tier: T2
theorem scaledCantorCoord_eq_two_digits_add_scaledTail {N : ℕ} (α : ℕ → Fin N) :
    scaledCantorCoord α =
      (2 * ((α 0).1 : ℝ) * (cantorBase N : ℝ) + 2 * ((α 1).1 : ℝ)) /
        (4 * (cantorBase N : ℝ) ^ 2) +
      ((cantorBase N : ℝ) ^ 2)⁻¹ * scaledCantorCoord (fun j ↦ α (j + 2)) := by
  have h := scaledCantorCoord_eq_prefix_add_scaledTail α 2
  rw [cantorPrefixCode_two] at h
  simpa using h

/-- 2-digit `(2 d₀ B + 2 d₁ + tail) / (4 B²)` form of `scaledCantorCoord`
(`geometry_spec.md` §1.1). -/
-- tier: T2
theorem scaledCantorCoord_eq_two_digits_add_tail {N : ℕ} (α : ℕ → Fin N) :
    scaledCantorCoord α =
      (2 * ((α 0).1 : ℝ) * (cantorBase N : ℝ) + 2 * ((α 1).1 : ℝ) +
        cantorCoord (fun j ↦ α (j + 2))) /
        (4 * (cantorBase N : ℝ) ^ 2) := by
  have h := scaledCantorCoord_eq_prefix_add_tail α 2
  rw [cantorPrefixCode_two] at h
  simpa using h

/-- 3-digit `(2 d₀ B² + 2 d₁ B + 2 d₂) / (4 B³) + B⁻³ * scaledTail` form of `scaledCantorCoord`. -/
-- tier: T2
theorem scaledCantorCoord_eq_three_digits_add_scaledTail {N : ℕ} (α : ℕ → Fin N) :
    scaledCantorCoord α =
      (2 * ((α 0).1 : ℝ) * (cantorBase N : ℝ) ^ 2 +
        2 * ((α 1).1 : ℝ) * (cantorBase N : ℝ) + 2 * ((α 2).1 : ℝ)) /
        (4 * (cantorBase N : ℝ) ^ 3) +
      ((cantorBase N : ℝ) ^ 3)⁻¹ * scaledCantorCoord (fun j ↦ α (j + 3)) := by
  have h := scaledCantorCoord_eq_prefix_add_scaledTail α 3
  rw [cantorPrefixCode_three] at h
  have h2 : ((2 : Fin 3) : ℕ) = 2 := rfl
  simpa [h2] using h

/-- 3-digit `(2 d₀ B² + 2 d₁ B + 2 d₂ + tail) / (4 B³)` form of `scaledCantorCoord`
(`geometry_spec.md` §1.3). -/
-- tier: T2
theorem scaledCantorCoord_eq_three_digits_add_tail {N : ℕ} (α : ℕ → Fin N) :
    scaledCantorCoord α =
      (2 * ((α 0).1 : ℝ) * (cantorBase N : ℝ) ^ 2 +
        2 * ((α 1).1 : ℝ) * (cantorBase N : ℝ) + 2 * ((α 2).1 : ℝ) +
        cantorCoord (fun j ↦ α (j + 3))) /
        (4 * (cantorBase N : ℝ) ^ 3) := by
  have h := scaledCantorCoord_eq_prefix_add_tail α 3
  rw [cantorPrefixCode_three] at h
  have h2 : ((2 : Fin 3) : ℕ) = 2 := rfl
  simpa [h2] using h

/-! ## 4. `shiftDom3` Source/Image Rectangles, Block Affine Maps `A_w` & Lemma G0 -/

/-- Transport a local block `w : D → A` along `hD : D = shiftDom3` to `shiftDom3 → A`. -/
def restrictToDom3 {A : Type*} {D : Finset ℤ} (hD : D = shiftDom3) (w : D → A) :
    shiftDom3 → A :=
  fun i ↦ w ⟨i.1, hD.symm ▸ i.2⟩

/-- Source Cantor cylinder rectangle `R_w ⊆ [0, 1/4]²` of width `1 / (4 B)` and height
`1 / (4 B²)` associated to a 3-cell block `w : shiftDom3 → A` (`geometry_spec.md` §1.3). -/
noncomputable def sourceRect {A : Type*} {N : ℕ} (enc : A ≃ Fin N)
    (w : shiftDom3 → A) : AxisRect :=
  { xMin := (2 * ((enc (w dom3NegOne)).1 : ℝ)) / (4 * (cantorBase N : ℝ))
    xMax := (2 * ((enc (w dom3NegOne)).1 : ℝ) + 1) / (4 * (cantorBase N : ℝ))
    yMin :=
      (2 * ((enc (w dom3Zero)).1 : ℝ) * (cantorBase N : ℝ) +
        2 * ((enc (w dom3One)).1 : ℝ)) / (4 * (cantorBase N : ℝ) ^ 2)
    yMax :=
      (2 * ((enc (w dom3Zero)).1 : ℝ) * (cantorBase N : ℝ) +
        2 * ((enc (w dom3One)).1 : ℝ) + 1) / (4 * (cantorBase N : ℝ) ^ 2)
    hx := div_le_div_of_nonneg_right (by linarith) (by positivity)
    hy := div_le_div_of_nonneg_right (by linarith) (by positivity) }

/-- Left `x`-endpoint of `sourceRect enc w`. -/
-- tier: T0
@[simp]
theorem sourceRect_xMin {A : Type*} {N : ℕ} (enc : A ≃ Fin N) (w : shiftDom3 → A) :
    (sourceRect enc w).xMin = (2 * ((enc (w dom3NegOne)).1 : ℝ)) / (4 * (cantorBase N : ℝ)) := by
  unfold sourceRect
  unfold AxisRect.xMin
  simp [dom3NegOne]

/-- Right `x`-endpoint of `sourceRect enc w`. -/
-- tier: T0
@[simp]
theorem sourceRect_xMax {A : Type*} {N : ℕ} (enc : A ≃ Fin N) (w : shiftDom3 → A) :
    (sourceRect enc w).xMax =
      (2 * ((enc (w dom3NegOne)).1 : ℝ) + 1) / (4 * (cantorBase N : ℝ)) := by
  rfl

/-- Lower `y`-endpoint of `sourceRect enc w`. -/
-- tier: T0
@[simp]
theorem sourceRect_yMin {A : Type*} {N : ℕ} (enc : A ≃ Fin N) (w : shiftDom3 → A) :
    (sourceRect enc w).yMin =
      (2 * ((enc (w dom3Zero)).1 : ℝ) * (cantorBase N : ℝ) +
        2 * ((enc (w dom3One)).1 : ℝ)) / (4 * (cantorBase N : ℝ) ^ 2) := by
  rfl

/-- Upper `y`-endpoint of `sourceRect enc w`. -/
-- tier: T0
@[simp]
theorem sourceRect_yMax {A : Type*} {N : ℕ} (enc : A ≃ Fin N) (w : shiftDom3 → A) :
    (sourceRect enc w).yMax =
      (2 * ((enc (w dom3Zero)).1 : ℝ) * (cantorBase N : ℝ) +
        2 * ((enc (w dom3One)).1 : ℝ) + 1) / (4 * (cantorBase N : ℝ) ^ 2) := by
  rfl

/-- Horizontal affine translation offset `a_w` for `blockAffineMap` (`geometry_spec.md` §1.2). -/
noncomputable def blockOffsetX {A : Type*} {N : ℕ} (enc : A ≃ Fin N)
    (Φ : GeneralizedShift A) (hD : Φ.D = shiftDom3) (w : Φ.D → A) : ℝ :=
  let B : ℝ := (cantorBase N : ℝ)
  let wNeg : ℝ := ((enc (restrictToDom3 hD w dom3NegOne)).1 : ℝ)
  let u := restrictToDom3 hD (Φ.G w)
  let uNeg : ℝ := ((enc (u dom3NegOne)).1 : ℝ)
  let uZero : ℝ := ((enc (u dom3Zero)).1 : ℝ)
  if Φ.F w = 1 then
    (uZero * B + uNeg - wNeg) / (2 * B ^ 2)
  else if Φ.F w = -1 then
    -wNeg / 2
  else
    (uNeg - wNeg) / (2 * B)

/-- Vertical affine translation offset `b_w` for `blockAffineMap` (`geometry_spec.md` §1.2). -/
noncomputable def blockOffsetY {A : Type*} {N : ℕ} (enc : A ≃ Fin N)
    (Φ : GeneralizedShift A) (hD : Φ.D = shiftDom3) (w : Φ.D → A) : ℝ :=
  let B : ℝ := (cantorBase N : ℝ)
  let w₀ := restrictToDom3 hD w
  let wZero : ℝ := ((enc (w₀ dom3Zero)).1 : ℝ)
  let wOne : ℝ := ((enc (w₀ dom3One)).1 : ℝ)
  let u := restrictToDom3 hD (Φ.G w)
  let uNeg : ℝ := ((enc (u dom3NegOne)).1 : ℝ)
  let uZero : ℝ := ((enc (u dom3Zero)).1 : ℝ)
  let uOne : ℝ := ((enc (u dom3One)).1 : ℝ)
  if Φ.F w = 1 then
    (uOne - wZero * B - wOne) / (2 * B)
  else if Φ.F w = -1 then
    (uNeg * B ^ 2 + (uZero - wZero) * B + (uOne - wOne)) / (2 * B ^ 3)
  else
    ((uZero - wZero) * B + (uOne - wOne)) / (2 * B ^ 2)

/-- Hyperbolic stretch parameter `μ_w = F(w) * log B` (`geometry_spec.md` §1.2), matching the
`(exp (-μ_w), exp μ_w) = (B^{-F(w)}, B^{F(w)})` convention of `DiskSmoothing.lean`. -/
noncomputable def blockStretchMu {A : Type*} {N : ℕ} (_enc : A ≃ Fin N)
    (Φ : GeneralizedShift A) (_hD : Φ.D = shiftDom3) (w : Φ.D → A) : ℝ :=
  (Φ.F w : ℝ) * Real.log (cantorBase N : ℝ)

/-- Block affine map `A_w(x, y) = (B^{-F(w)} x + a_w, B^{F(w)} y + b_w)` realizing `Φ.eval`
on the source cylinder rectangle `sourceRect` (`geometry_spec.md` §1.2). -/
noncomputable def blockAffineMap {A : Type*} {N : ℕ} (enc : A ≃ Fin N)
    (Φ : GeneralizedShift A) (hD : Φ.D = shiftDom3) (w : Φ.D → A)
    (p : EuclideanPlane) : EuclideanPlane :=
  WithLp.toLp 2
    ![(cantorBase N : ℝ) ^ (-Φ.F w) * p 0 + blockOffsetX enc Φ hD w,
      (cantorBase N : ℝ) ^ (Φ.F w) * p 1 + blockOffsetY enc Φ hD w]

/-- Target Cantor cylinder rectangle `R'_w = A_w(R_w) ⊆ [0, 1/4]²` associated to `w : Φ.D → A`
(`geometry_spec.md` §1.3). -/
noncomputable def imageRect {A : Type*} {N : ℕ} (enc : A ≃ Fin N)
    (Φ : GeneralizedShift A) (hD : Φ.D = shiftDom3) (w : Φ.D → A) : AxisRect :=
  let B : ℝ := (cantorBase N : ℝ)
  let u := restrictToDom3 hD (Φ.G w)
  let uNeg : ℝ := ((enc (u dom3NegOne)).1 : ℝ)
  let uZero : ℝ := ((enc (u dom3Zero)).1 : ℝ)
  let uOne : ℝ := ((enc (u dom3One)).1 : ℝ)
  if Φ.F w = 1 then
    { xMin := (2 * uZero * B + 2 * uNeg) / (4 * B ^ 2)
      xMax := (2 * uZero * B + 2 * uNeg + 1) / (4 * B ^ 2)
      yMin := (2 * uOne) / (4 * B)
      yMax := (2 * uOne + 1) / (4 * B)
      hx := div_le_div_of_nonneg_right (by linarith) (by positivity)
      hy := div_le_div_of_nonneg_right (by linarith) (by positivity) }
  else if Φ.F w = -1 then
    { xMin := 0
      xMax := 1 / 4
      yMin := (2 * uNeg * B ^ 2 + 2 * uZero * B + 2 * uOne) / (4 * B ^ 3)
      yMax := (2 * uNeg * B ^ 2 + 2 * uZero * B + 2 * uOne + 1) / (4 * B ^ 3)
      hx := by norm_num
      hy := div_le_div_of_nonneg_right (by linarith) (by positivity) }
  else
    { xMin := (2 * uNeg) / (4 * B)
      xMax := (2 * uNeg + 1) / (4 * B)
      yMin := (2 * uZero * B + 2 * uOne) / (4 * B ^ 2)
      yMax := (2 * uZero * B + 2 * uOne + 1) / (4 * B ^ 2)
      hx := div_le_div_of_nonneg_right (by linarith) (by positivity)
      hy := div_le_div_of_nonneg_right (by linarith) (by positivity) }

/-- First coordinate of `blockAffineMap enc Φ hD w p`. -/
-- tier: T0
@[simp]
theorem blockAffineMap_zero {A : Type*} {N : ℕ} (enc : A ≃ Fin N)
    (Φ : GeneralizedShift A) (hD : Φ.D = shiftDom3) (w : Φ.D → A) (p : EuclideanPlane) :
    blockAffineMap enc Φ hD w p 0 =
      (cantorBase N : ℝ) ^ (-Φ.F w) * p 0 + blockOffsetX enc Φ hD w := by
  simp [blockAffineMap]

/-- Second coordinate of `blockAffineMap enc Φ hD w p`. -/
-- tier: T0
@[simp]
theorem blockAffineMap_one {A : Type*} {N : ℕ} (enc : A ≃ Fin N)
    (Φ : GeneralizedShift A) (hD : Φ.D = shiftDom3) (w : Φ.D → A) (p : EuclideanPlane) :
    blockAffineMap enc Φ hD w p 1 =
      (cantorBase N : ℝ) ^ (Φ.F w) * p 1 + blockOffsetY enc Φ hD w := by
  simp [blockAffineMap]

/-- Every `ShiftDir.toInt` displacement belongs to `{-1, 0, 1}`. -/
-- tier: T0
theorem shiftDir_toInt_mem (d : ShiftDir) :
    d.toInt = -1 ∨ d.toInt = 0 ∨ d.toInt = 1 := by
  cases d <;> simp [ShiftDir.toInt]

/-- Width of every `sourceRect enc w` equals `1 / (4 B)`. -/
-- tier: T1
@[simp]
theorem sourceRect_width {A : Type*} {N : ℕ} (enc : A ≃ Fin N) (w : shiftDom3 → A) :
    (sourceRect enc w).width = 1 / (4 * (cantorBase N : ℝ)) := by
  unfold AxisRect.width
  rw [sourceRect_xMax, sourceRect_xMin]
  ring

/-- Height of every `sourceRect enc w` equals `1 / (4 B²)`. -/
-- tier: T1
@[simp]
theorem sourceRect_height {A : Type*} {N : ℕ} (enc : A ≃ Fin N) (w : shiftDom3 → A) :
    (sourceRect enc w).height = 1 / (4 * (cantorBase N : ℝ) ^ 2) := by
  unfold AxisRect.height
  rw [sourceRect_yMax, sourceRect_yMin]
  ring

/-- Exponential identity `Real.exp (blockStretchMu enc Φ hD w) = B ^ (Φ.F w)`. -/
-- tier: T1
@[simp]
theorem exp_blockStretchMu {A : Type*} {N : ℕ} (enc : A ≃ Fin N)
    (Φ : GeneralizedShift A) (hD : Φ.D = shiftDom3) (w : Φ.D → A) :
    Real.exp (blockStretchMu enc Φ hD w) = (cantorBase N : ℝ) ^ (Φ.F w) := by
  have hB : 0 < (cantorBase N : ℝ) := by exact_mod_cast cantorBase_pos N
  rw [blockStretchMu, ← Real.log_zpow, Real.exp_log (zpow_pos hB _)]

/-- Exponential identity `Real.exp (-blockStretchMu enc Φ hD w) = B ^ (-Φ.F w)`. -/
-- tier: T1
@[simp]
theorem exp_neg_blockStretchMu {A : Type*} {N : ℕ} (enc : A ≃ Fin N)
    (Φ : GeneralizedShift A) (hD : Φ.D = shiftDom3) (w : Φ.D → A) :
    Real.exp (-blockStretchMu enc Φ hD w) = (cantorBase N : ℝ) ^ (-Φ.F w) := by
  have hB : 0 < (cantorBase N : ℝ) := by exact_mod_cast cantorBase_pos N
  have hrew : -blockStretchMu enc Φ hD w = ((-Φ.F w : ℤ) : ℝ) * Real.log (cantorBase N : ℝ) := by
    simp [blockStretchMu]
  rw [hrew, ← Real.log_zpow, Real.exp_log (zpow_pos hB _)]

/-- Exponential-stretch form `(exp (-μ_w) x + a_w, exp μ_w y + b_w)` of `blockAffineMap`. -/
-- tier: T1
theorem blockAffineMap_eq_exp_stretch {A : Type*} {N : ℕ} (enc : A ≃ Fin N)
    (Φ : GeneralizedShift A) (hD : Φ.D = shiftDom3) (w : Φ.D → A) (p : EuclideanPlane) :
    blockAffineMap enc Φ hD w p =
      WithLp.toLp 2
        ![Real.exp (-blockStretchMu enc Φ hD w) * p 0 + blockOffsetX enc Φ hD w,
          Real.exp (blockStretchMu enc Φ hD w) * p 1 + blockOffsetY enc Φ hD w] := by
  rw [exp_neg_blockStretchMu, exp_blockStretchMu]
  rfl

/-- Characterization of `(sourceRect enc w).toSet` as a product of `cantorClosedInterval`s of
lengths `(1, 2)`. -/
-- tier: T2
theorem sourceRect_toSet_eq {A : Type*} {N : ℕ} (enc : A ≃ Fin N) (w : shiftDom3 → A) :
    (sourceRect enc w).toSet =
      { p : EuclideanPlane |
        p 0 ∈ cantorClosedInterval ![enc (w dom3NegOne)] ∧
        p 1 ∈ cantorClosedInterval ![enc (w dom3Zero), enc (w dom3One)] } := by
  ext p
  rw [AxisRect.mem_toSet_iff]
  simp only [Set.mem_ofPred_eq, cantorClosedInterval, cantorPrefixCode_one, cantorPrefixCode_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, pow_one,
    sourceRect_xMin, sourceRect_xMax, sourceRect_yMin, sourceRect_yMax, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat]

/-- Every `sourceRect enc w` is contained in `quarterSquare = [0, 1/4]²`. -/
-- tier: T2
theorem sourceRect_subset_quarterSquare {A : Type*} {N : ℕ} (enc : A ≃ Fin N)
    (w : shiftDom3 → A) :
    (sourceRect enc w).toSet ⊆ quarterSquare.toSet := by
  intro p hp
  rw [sourceRect_toSet_eq] at hp
  rw [AxisRect.mem_toSet_iff, quarterSquare_xMin, quarterSquare_xMax, quarterSquare_yMin,
    quarterSquare_yMax]
  exact ⟨cantorClosedInterval_subset_Icc_quarter _ hp.1,
    cantorClosedInterval_subset_Icc_quarter _ hp.2⟩

/-- If `restrictDom shiftDom3 s = w`, then `(cantorDiskEmbed enc s).1` belongs to
`(sourceRect enc w).toSet`. -/
-- tier: T2
theorem cantorDiskEmbed_mem_sourceRect {A : Type*} {N : ℕ} (enc : A ≃ Fin N)
    {s : ℤ → A} {w : shiftDom3 → A} (hw : restrictDom shiftDom3 s = w) :
    (cantorDiskEmbed enc s).1 ∈ (sourceRect enc w).toSet := by
  subst hw
  rw [sourceRect_toSet_eq]
  refine ⟨?_, ?_⟩
  · refine scaledCantorCoord_mem_cantorClosedInterval (fun j ↦ enc (negHalf s j))
      ![enc (restrictDom shiftDom3 s dom3NegOne)] fun j ↦ ?_
    fin_cases j
    rfl
  · refine scaledCantorCoord_mem_cantorClosedInterval (fun j ↦ enc (nonnegHalf s j))
      ![enc (restrictDom shiftDom3 s dom3Zero), enc (restrictDom shiftDom3 s dom3One)] fun j ↦ ?_
    fin_cases j <;> rfl

/-- Distinct 3-cell blocks `w₁ ≠ w₂` on `shiftDom3` have pairwise disjoint source rectangles. -/
-- tier: T2
theorem sourceRect_pairwise_disjoint {A : Type*} {N : ℕ} (enc : A ≃ Fin N) :
    Pairwise (Disjoint on fun w : shiftDom3 → A ↦ (sourceRect enc w).toSet) := by
  intro w₁ w₂ hne
  rw [Function.onFun, Set.disjoint_left]
  intro p hp₁ hp₂
  rw [sourceRect_toSet_eq] at hp₁ hp₂
  by_cases hneg : w₁ dom3NegOne = w₂ dom3NegOne
  · have hpos_ne :
        ![enc (w₁ dom3Zero), enc (w₁ dom3One)] ≠ ![enc (w₂ dom3Zero), enc (w₂ dom3One)] := by
      intro heq
      apply hne
      rw [← mkDom3_eta w₁, ← mkDom3_eta w₂, hneg,
        enc.injective (congrFun heq 0), enc.injective (congrFun heq 1)]
    exact Set.disjoint_left.mp (disjoint_cantorClosedInterval_of_ne hpos_ne) hp₁.2 hp₂.2
  · have hneg_ne : ![enc (w₁ dom3NegOne)] ≠ ![enc (w₂ dom3NegOne)] := fun heq ↦
      hneg (enc.injective (congrFun heq 0))
    exact Set.disjoint_left.mp (disjoint_cantorClosedInterval_of_ne hneg_ne) hp₁.1 hp₂.1

/-- Decomposition of `(imageRect enc Φ hD w).toSet` as a product of `cantorClosedInterval`s
matching the cylinder constraints `D - F(w)` on `Φ.eval` (`geometry_spec.md` §1.3 & §2.1). -/
-- tier: T2
theorem exists_cantorClosedInterval_of_imageRect {A : Type*} {N : ℕ} (enc : A ≃ Fin N)
    (Φ : GeneralizedShift A) (hD : Φ.D = shiftDom3) (w : Φ.D → A)
    (hf : Φ.F w = -1 ∨ Φ.F w = 0 ∨ Φ.F w = 1) :
    ∃ (mNeg mPos : ℕ) (pNeg : Fin mNeg → Fin N) (pPos : Fin mPos → Fin N),
      (imageRect enc Φ hD w).toSet =
        { p : EuclideanPlane |
          p 0 ∈ cantorClosedInterval pNeg ∧ p 1 ∈ cantorClosedInterval pPos } ∧
      ∀ y : ℤ → A,
        (∀ j : Fin mNeg, enc (y (-((j.1 : ℤ) + 1))) = pNeg j) →
        (∀ j : Fin mPos, enc (y (j.1 : ℤ)) = pPos j) →
        ∀ i : Φ.D, y (i.1 - Φ.F w) = Φ.G w i := by
  let u := restrictToDom3 hD (Φ.G w)
  have hm1_ne_1 : (-1 : ℤ) ≠ 1 := by decide
  have h0_ne_1 : (0 : ℤ) ≠ 1 := by decide
  have h0_ne_m1 : (0 : ℤ) ≠ -1 := by decide
  rcases hf with hf | hf | hf
  · refine ⟨0, 3, ![], ![enc (u dom3NegOne), enc (u dom3Zero), enc (u dom3One)], ?_, ?_⟩
    · ext p
      simp only [imageRect, u, hf, hm1_ne_1, ↓reduceIte, AxisRect.mem_toSet_iff, Set.mem_ofPred_eq,
        cantorClosedInterval, cantorPrefixCode_zero, cantorPrefixCode_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, pow_zero, mul_one, zero_div, zero_add, Nat.cast_zero, Nat.cast_add,
        Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      rfl
    · intro y _ hyPos ⟨k, hk⟩
      have hk3 : k ∈ shiftDom3 := hD ▸ hk
      rw [hf]
      rcases (mem_shiftDom3_iff k).mp hk3 with rfl | rfl | rfl
      · have h0 := enc.injective (hyPos 0)
        simpa [u, restrictToDom3, dom3NegOne] using h0
      · have h1 := enc.injective (hyPos 1)
        simpa [u, restrictToDom3, dom3Zero] using h1
      · have h2 := enc.injective (hyPos 2)
        simpa [u, restrictToDom3, dom3One] using h2
  · refine ⟨1, 2, ![enc (u dom3NegOne)], ![enc (u dom3Zero), enc (u dom3One)], ?_, ?_⟩
    · ext p
      simp only [imageRect, u, hf, h0_ne_1, h0_ne_m1, ↓reduceIte, AxisRect.mem_toSet_iff,
        Set.mem_ofPred_eq, cantorClosedInterval, cantorPrefixCode_one, cantorPrefixCode_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, pow_one, Nat.cast_add,
        Nat.cast_mul, Nat.cast_ofNat]
    · intro y hyNeg hyPos ⟨k, hk⟩
      have hk3 : k ∈ shiftDom3 := hD ▸ hk
      rw [hf, sub_zero]
      rcases (mem_shiftDom3_iff k).mp hk3 with rfl | rfl | rfl
      · have h0 := enc.injective (hyNeg 0)
        simpa [u, restrictToDom3, dom3NegOne] using h0
      · have h0 := enc.injective (hyPos 0)
        simpa [u, restrictToDom3, dom3Zero] using h0
      · have h1 := enc.injective (hyPos 1)
        simpa [u, restrictToDom3, dom3One] using h1
  · refine ⟨2, 1, ![enc (u dom3Zero), enc (u dom3NegOne)], ![enc (u dom3One)], ?_, ?_⟩
    · ext p
      simp only [imageRect, u, hf, ↓reduceIte, AxisRect.mem_toSet_iff, Set.mem_ofPred_eq,
        cantorClosedInterval, cantorPrefixCode_two, cantorPrefixCode_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, pow_one, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat]
    · intro y hyNeg hyPos ⟨k, hk⟩
      have hk3 : k ∈ shiftDom3 := hD ▸ hk
      rw [hf]
      rcases (mem_shiftDom3_iff k).mp hk3 with rfl | rfl | rfl
      · have h1 := enc.injective (hyNeg 1)
        simpa [u, restrictToDom3, dom3NegOne] using h1
      · have h0 := enc.injective (hyNeg 0)
        simpa [u, restrictToDom3, dom3Zero] using h0
      · have h0 := enc.injective (hyPos 0)
        simpa [u, restrictToDom3, dom3One] using h0

/-- Every `imageRect enc Φ hD w` (for `Φ.F w ∈ {-1, 0, 1}`) is contained in
`quarterSquare = [0, 1/4]²`. -/
-- tier: T2
theorem imageRect_subset_quarterSquare {A : Type*} {N : ℕ} (enc : A ≃ Fin N)
    (Φ : GeneralizedShift A) (hD : Φ.D = shiftDom3) (w : Φ.D → A)
    (hf : Φ.F w = -1 ∨ Φ.F w = 0 ∨ Φ.F w = 1) :
    (imageRect enc Φ hD w).toSet ⊆ quarterSquare.toSet := by
  obtain ⟨_, _, pNeg, pPos, hset, _⟩ := exists_cantorClosedInterval_of_imageRect enc Φ hD w hf
  intro p hp
  rw [hset] at hp
  rw [AxisRect.mem_toSet_iff, quarterSquare_xMin, quarterSquare_xMax, quarterSquare_yMin,
    quarterSquare_yMax]
  exact ⟨cantorClosedInterval_subset_Icc_quarter pNeg hp.1,
    cantorClosedInterval_subset_Icc_quarter pPos hp.2⟩

/-- Exact rectangle image identity `A_w(R_w) = R'_w` (`geometry_spec.md` §1.3). -/
-- tier: T2
theorem blockAffineMap_image_sourceRect {A : Type*} {N : ℕ} (enc : A ≃ Fin N)
    (Φ : GeneralizedShift A) (hD : Φ.D = shiftDom3) (w : Φ.D → A)
    (hf : Φ.F w = -1 ∨ Φ.F w = 0 ∨ Φ.F w = 1) :
    blockAffineMap enc Φ hD w '' (sourceRect enc (restrictToDom3 hD w)).toSet =
      (imageRect enc Φ hD w).toSet := by
  have hB_raw : 0 < (cantorBase N : ℝ) := by exact_mod_cast cantorBase_pos N
  set B : ℝ := (cantorBase N : ℝ)
  have hB : 0 < B := hB_raw
  have hB0 : B ≠ 0 := hB.ne'
  have hsx : 0 < B ^ (-Φ.F w) := zpow_pos hB (-Φ.F w)
  have hsy : 0 < B ^ (Φ.F w) := zpow_pos hB (Φ.F w)
  have himg := AxisRect.image_posScaleTranslate (sourceRect enc (restrictToDom3 hD w))
    hsx hsy (blockOffsetX enc Φ hD w) (blockOffsetY enc Φ hD w)
  change (fun p : EuclideanPlane ↦
      WithLp.toLp 2
        ![B ^ (-Φ.F w) * p 0 + blockOffsetX enc Φ hD w,
          B ^ (Φ.F w) * p 1 + blockOffsetY enc Φ hD w]) ''
    (sourceRect enc (restrictToDom3 hD w)).toSet = (imageRect enc Φ hD w).toSet
  rw [himg]
  ext q
  rw [Set.mem_ofPred_eq, AxisRect.mem_toSet_iff]
  have hm1_ne_1 : (-1 : ℤ) ≠ 1 := by decide
  have h0_ne_1 : (0 : ℤ) ≠ 1 := by decide
  have h0_ne_m1 : (0 : ℤ) ≠ -1 := by decide
  rcases hf with hf | hf | hf
  · simp only [sourceRect_xMin, sourceRect_xMax, sourceRect_yMin, sourceRect_yMax,
      blockOffsetX, blockOffsetY, imageRect, hf, hm1_ne_1, ↓reduceIte, neg_neg, zpow_one,
      zpow_neg_one]
    have hx₁ : B * (2 * ↑(enc (restrictToDom3 hD w dom3NegOne)).1 / (4 * B)) +
        -↑(enc (restrictToDom3 hD w dom3NegOne)).1 / 2 = 0 := by
      field_simp [hB0]; ring
    have hx₂ : B * ((2 * ↑(enc (restrictToDom3 hD w dom3NegOne)).1 + 1) / (4 * B)) +
        -↑(enc (restrictToDom3 hD w dom3NegOne)).1 / 2 = 1 / 4 := by
      field_simp [hB0]; ring
    have hy₁ :
        B⁻¹ * ((2 * ↑(enc (restrictToDom3 hD w dom3Zero)).1 * B +
            2 * ↑(enc (restrictToDom3 hD w dom3One)).1) / (4 * B ^ 2)) +
          (↑(enc (restrictToDom3 hD (Φ.G w) dom3NegOne)).1 * B ^ 2 +
            (↑(enc (restrictToDom3 hD (Φ.G w) dom3Zero)).1 -
              ↑(enc (restrictToDom3 hD w dom3Zero)).1) * B +
            (↑(enc (restrictToDom3 hD (Φ.G w) dom3One)).1 -
              ↑(enc (restrictToDom3 hD w dom3One)).1)) / (2 * B ^ 3) =
          (2 * ↑(enc (restrictToDom3 hD (Φ.G w) dom3NegOne)).1 * B ^ 2 +
            2 * ↑(enc (restrictToDom3 hD (Φ.G w) dom3Zero)).1 * B +
            2 * ↑(enc (restrictToDom3 hD (Φ.G w) dom3One)).1) / (4 * B ^ 3) := by
      field_simp [hB0]; ring
    have hy₂ :
        B⁻¹ * ((2 * ↑(enc (restrictToDom3 hD w dom3Zero)).1 * B +
            2 * ↑(enc (restrictToDom3 hD w dom3One)).1 + 1) / (4 * B ^ 2)) +
          (↑(enc (restrictToDom3 hD (Φ.G w) dom3NegOne)).1 * B ^ 2 +
            (↑(enc (restrictToDom3 hD (Φ.G w) dom3Zero)).1 -
              ↑(enc (restrictToDom3 hD w dom3Zero)).1) * B +
            (↑(enc (restrictToDom3 hD (Φ.G w) dom3One)).1 -
              ↑(enc (restrictToDom3 hD w dom3One)).1)) / (2 * B ^ 3) =
          (2 * ↑(enc (restrictToDom3 hD (Φ.G w) dom3NegOne)).1 * B ^ 2 +
            2 * ↑(enc (restrictToDom3 hD (Φ.G w) dom3Zero)).1 * B +
            2 * ↑(enc (restrictToDom3 hD (Φ.G w) dom3One)).1 + 1) / (4 * B ^ 3) := by
      field_simp [hB0]; ring
    rw [hx₁, hx₂, hy₁, hy₂]
  · simp only [sourceRect_xMin, sourceRect_xMax, sourceRect_yMin, sourceRect_yMax,
      blockOffsetX, blockOffsetY, imageRect, hf, h0_ne_1, h0_ne_m1, ↓reduceIte, neg_zero,
      zpow_zero, one_mul]
    have hx₁ : 2 * ↑(enc (restrictToDom3 hD w dom3NegOne)).1 / (4 * B) +
        (↑(enc (restrictToDom3 hD (Φ.G w) dom3NegOne)).1 -
          ↑(enc (restrictToDom3 hD w dom3NegOne)).1) / (2 * B) =
        2 * ↑(enc (restrictToDom3 hD (Φ.G w) dom3NegOne)).1 / (4 * B) := by
      field_simp [hB0]; ring
    have hx₂ : (2 * ↑(enc (restrictToDom3 hD w dom3NegOne)).1 + 1) / (4 * B) +
        (↑(enc (restrictToDom3 hD (Φ.G w) dom3NegOne)).1 -
          ↑(enc (restrictToDom3 hD w dom3NegOne)).1) / (2 * B) =
        (2 * ↑(enc (restrictToDom3 hD (Φ.G w) dom3NegOne)).1 + 1) / (4 * B) := by
      field_simp [hB0]; ring
    have hy₁ :
        (2 * ↑(enc (restrictToDom3 hD w dom3Zero)).1 * B +
          2 * ↑(enc (restrictToDom3 hD w dom3One)).1) / (4 * B ^ 2) +
          ((↑(enc (restrictToDom3 hD (Φ.G w) dom3Zero)).1 -
              ↑(enc (restrictToDom3 hD w dom3Zero)).1) * B +
            (↑(enc (restrictToDom3 hD (Φ.G w) dom3One)).1 -
              ↑(enc (restrictToDom3 hD w dom3One)).1)) / (2 * B ^ 2) =
          (2 * ↑(enc (restrictToDom3 hD (Φ.G w) dom3Zero)).1 * B +
            2 * ↑(enc (restrictToDom3 hD (Φ.G w) dom3One)).1) / (4 * B ^ 2) := by
      field_simp [hB0]; ring
    have hy₂ :
        (2 * ↑(enc (restrictToDom3 hD w dom3Zero)).1 * B +
          2 * ↑(enc (restrictToDom3 hD w dom3One)).1 + 1) / (4 * B ^ 2) +
          ((↑(enc (restrictToDom3 hD (Φ.G w) dom3Zero)).1 -
              ↑(enc (restrictToDom3 hD w dom3Zero)).1) * B +
            (↑(enc (restrictToDom3 hD (Φ.G w) dom3One)).1 -
              ↑(enc (restrictToDom3 hD w dom3One)).1)) / (2 * B ^ 2) =
          (2 * ↑(enc (restrictToDom3 hD (Φ.G w) dom3Zero)).1 * B +
            2 * ↑(enc (restrictToDom3 hD (Φ.G w) dom3One)).1 + 1) / (4 * B ^ 2) := by
      field_simp [hB0]; ring
    rw [hx₁, hx₂, hy₁, hy₂]
  · simp only [sourceRect_xMin, sourceRect_xMax, sourceRect_yMin, sourceRect_yMax,
      blockOffsetX, blockOffsetY, imageRect, hf, ↓reduceIte, zpow_neg_one, zpow_one]
    have hx₁ :
        B⁻¹ * (2 * ↑(enc (restrictToDom3 hD w dom3NegOne)).1 / (4 * B)) +
          (↑(enc (restrictToDom3 hD (Φ.G w) dom3Zero)).1 * B +
            ↑(enc (restrictToDom3 hD (Φ.G w) dom3NegOne)).1 -
            ↑(enc (restrictToDom3 hD w dom3NegOne)).1) / (2 * B ^ 2) =
          (2 * ↑(enc (restrictToDom3 hD (Φ.G w) dom3Zero)).1 * B +
            2 * ↑(enc (restrictToDom3 hD (Φ.G w) dom3NegOne)).1) / (4 * B ^ 2) := by
      field_simp [hB0]; ring
    have hx₂ :
        B⁻¹ * ((2 * ↑(enc (restrictToDom3 hD w dom3NegOne)).1 + 1) / (4 * B)) +
          (↑(enc (restrictToDom3 hD (Φ.G w) dom3Zero)).1 * B +
            ↑(enc (restrictToDom3 hD (Φ.G w) dom3NegOne)).1 -
            ↑(enc (restrictToDom3 hD w dom3NegOne)).1) / (2 * B ^ 2) =
          (2 * ↑(enc (restrictToDom3 hD (Φ.G w) dom3Zero)).1 * B +
            2 * ↑(enc (restrictToDom3 hD (Φ.G w) dom3NegOne)).1 + 1) / (4 * B ^ 2) := by
      field_simp [hB0]; ring
    have hy₁ :
        B * ((2 * ↑(enc (restrictToDom3 hD w dom3Zero)).1 * B +
          2 * ↑(enc (restrictToDom3 hD w dom3One)).1) / (4 * B ^ 2)) +
          (↑(enc (restrictToDom3 hD (Φ.G w) dom3One)).1 -
            ↑(enc (restrictToDom3 hD w dom3Zero)).1 * B -
            ↑(enc (restrictToDom3 hD w dom3One)).1) / (2 * B) =
          2 * ↑(enc (restrictToDom3 hD (Φ.G w) dom3One)).1 / (4 * B) := by
      field_simp [hB0]; ring
    have hy₂ :
        B * ((2 * ↑(enc (restrictToDom3 hD w dom3Zero)).1 * B +
          2 * ↑(enc (restrictToDom3 hD w dom3One)).1 + 1) / (4 * B ^ 2)) +
          (↑(enc (restrictToDom3 hD (Φ.G w) dom3One)).1 -
            ↑(enc (restrictToDom3 hD w dom3Zero)).1 * B -
            ↑(enc (restrictToDom3 hD w dom3One)).1) / (2 * B) =
          (2 * ↑(enc (restrictToDom3 hD (Φ.G w) dom3One)).1 + 1) / (4 * B) := by
      field_simp [hB0]; ring
    rw [hx₁, hx₂, hy₁, hy₂]

/-- Exact Cantor action identity: on the cylinder `restrictDom Φ.D s = w`, the block affine map
`blockAffineMap enc Φ hD w` sends `(cantorDiskEmbed enc s).1` to
`(cantorDiskEmbed enc (Φ.eval s)).1` (`geometry_spec.md` §1.1–§1.2). -/
-- tier: T2
theorem blockAffineMap_cantorDiskEmbed {A : Type*} {N : ℕ} (enc : A ≃ Fin N)
    (Φ : GeneralizedShift A) (hD : Φ.D = shiftDom3) {s : ℤ → A} {w : Φ.D → A}
    (hw : restrictDom Φ.D s = w) (hf : Φ.F w = -1 ∨ Φ.F w = 0 ∨ Φ.F w = 1) :
    blockAffineMap enc Φ hD w (cantorDiskEmbed enc s).1 =
      (cantorDiskEmbed enc (Φ.eval s)).1 := by
  subst hw
  have hB : 0 < (cantorBase N : ℝ) := by exact_mod_cast cantorBase_pos N
  have hB0 : (cantorBase N : ℝ) ≠ 0 := hB.ne'
  have hm1_ne_1 : (-1 : ℤ) ≠ 1 := by decide
  have h0_ne_1 : (0 : ℤ) ≠ 1 := by decide
  have h0_ne_m1 : (0 : ℤ) ≠ -1 := by decide
  have hs_neg : (cantorDiskEmbed enc s).1 0 =
      (2 * ((enc (restrictToDom3 hD (restrictDom Φ.D s) dom3NegOne)).1 : ℝ) +
        cantorCoord (fun j ↦ enc (s (-((j : ℤ) + 2))))) / (4 * (cantorBase N : ℝ)) := by
    change scaledCantorCoord (fun j ↦ enc (negHalf s j)) = _
    rw [scaledCantorCoord_eq_one_digit_add_tail]
    have htail : (fun j : ℕ ↦ enc (negHalf s (j + 1))) = fun j : ℕ ↦ enc (s (-((j : ℤ) + 2))) := by
      funext j
      simp only [negHalf]
      congr 2
    rw [htail]
    rfl
  have hs_pos : (cantorDiskEmbed enc s).1 1 =
      (2 * ((enc (restrictToDom3 hD (restrictDom Φ.D s) dom3Zero)).1 : ℝ) * (cantorBase N : ℝ) +
        2 * ((enc (restrictToDom3 hD (restrictDom Φ.D s) dom3One)).1 : ℝ) +
        cantorCoord (fun j ↦ enc (s ((j : ℤ) + 2)))) / (4 * (cantorBase N : ℝ) ^ 2) := by
    change scaledCantorCoord (fun j ↦ enc (nonnegHalf s j)) = _
    rw [scaledCantorCoord_eq_two_digits_add_tail]
    have htail : (fun j : ℕ ↦ enc (nonnegHalf s (j + 2))) =
        fun j : ℕ ↦ enc (s ((j : ℤ) + 2)) := by
      funext j
      simp [nonnegHalf]
    rw [htail]
    rfl
  have hnot_neg : ∀ j : ℕ, -((j : ℤ) + 2) ∉ Φ.D := by
    intro j
    rw [hD, notMem_shiftDom3_iff]
    omega
  have hnot_pos : ∀ j : ℕ, ((j : ℤ) + 2) ∉ Φ.D := by
    intro j
    rw [hD, notMem_shiftDom3_iff]
    omega
  have hm1_mem : (-1 : ℤ) ∈ Φ.D := hD.symm ▸ dom3NegOne.2
  have h0_mem : (0 : ℤ) ∈ Φ.D := hD.symm ▸ dom3Zero.2
  have h1_mem : (1 : ℤ) ∈ Φ.D := hD.symm ▸ dom3One.2
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, blockAffineMap_zero, hs_neg]
    change (cantorBase N : ℝ) ^ (-Φ.F (restrictDom Φ.D s)) *
        ((2 * ↑(enc (restrictToDom3 hD (restrictDom Φ.D s) dom3NegOne)).1 +
          cantorCoord (fun j ↦ enc (s (-((j : ℤ) + 2))))) / (4 * (cantorBase N : ℝ))) +
      blockOffsetX enc Φ hD (restrictDom Φ.D s) =
      scaledCantorCoord (fun j ↦ enc (negHalf (Φ.eval s) j))
    rcases hf with hf | hf | hf
    · have hseq : (fun j : ℕ ↦ enc (negHalf (Φ.eval s) j)) =
          fun j : ℕ ↦ enc (s (-((j : ℤ) + 2))) := by
        funext j
        congr 1
        simp only [negHalf, GeneralizedShift.eval_apply]
        have hidx : -((j : ℤ) + 1) + Φ.F (restrictDom Φ.D s) = -((j : ℤ) + 2) := by omega
        rw [hidx, replaceDom_notMem _ _ _ (hnot_neg j)]
      rw [hseq]
      unfold scaledCantorCoord
      simp only [blockOffsetX, hf, hm1_ne_1, ↓reduceIte, neg_neg, zpow_one]
      field_simp [hB0]
      ring
    · rw [scaledCantorCoord_eq_one_digit_add_tail]
      have hd0 : negHalf (Φ.eval s) 0 =
          restrictToDom3 hD (Φ.G (restrictDom Φ.D s)) dom3NegOne := by
        simp only [negHalf, GeneralizedShift.eval_apply, hf]
        norm_num
        exact replaceDom_mem _ _ _ hm1_mem
      have htail : (fun j : ℕ ↦ enc (negHalf (Φ.eval s) (j + 1))) =
          fun j : ℕ ↦ enc (s (-((j : ℤ) + 2))) := by
        funext j
        congr 1
        simp only [negHalf, GeneralizedShift.eval_apply]
        have hidx : -(((j + 1 : ℕ) : ℤ) + 1) + Φ.F (restrictDom Φ.D s) = -((j : ℤ) + 2) := by
          omega
        rw [hidx, replaceDom_notMem _ _ _ (hnot_neg j)]
      rw [hd0, htail]
      simp only [blockOffsetX, hf, h0_ne_1, h0_ne_m1, ↓reduceIte, neg_zero, zpow_zero, one_mul]
      field_simp [hB0]
      ring
    · rw [scaledCantorCoord_eq_two_digits_add_tail]
      have hd0 : negHalf (Φ.eval s) 0 =
          restrictToDom3 hD (Φ.G (restrictDom Φ.D s)) dom3Zero := by
        simp only [negHalf, GeneralizedShift.eval_apply, hf]
        norm_num
        exact replaceDom_mem _ _ _ h0_mem
      have hd1 : negHalf (Φ.eval s) 1 =
          restrictToDom3 hD (Φ.G (restrictDom Φ.D s)) dom3NegOne := by
        simp only [negHalf, GeneralizedShift.eval_apply, hf]
        norm_num
        exact replaceDom_mem _ _ _ hm1_mem
      have htail : (fun j : ℕ ↦ enc (negHalf (Φ.eval s) (j + 2))) =
          fun j : ℕ ↦ enc (s (-((j : ℤ) + 2))) := by
        funext j
        congr 1
        simp only [negHalf, GeneralizedShift.eval_apply]
        have hidx : -(((j + 2 : ℕ) : ℤ) + 1) + Φ.F (restrictDom Φ.D s) = -((j : ℤ) + 2) := by
          omega
        rw [hidx, replaceDom_notMem _ _ _ (hnot_neg j)]
      rw [hd0, hd1, htail]
      simp only [blockOffsetX, hf, ↓reduceIte, zpow_neg_one]
      field_simp [hB0]
      ring
  · simp only [Fin.mk_one, blockAffineMap_one, hs_pos]
    change (cantorBase N : ℝ) ^ (Φ.F (restrictDom Φ.D s)) *
        ((2 * ↑(enc (restrictToDom3 hD (restrictDom Φ.D s) dom3Zero)).1 * (cantorBase N : ℝ) +
          2 * ↑(enc (restrictToDom3 hD (restrictDom Φ.D s) dom3One)).1 +
          cantorCoord (fun j ↦ enc (s ((j : ℤ) + 2)))) / (4 * (cantorBase N : ℝ) ^ 2)) +
      blockOffsetY enc Φ hD (restrictDom Φ.D s) =
      scaledCantorCoord (fun j ↦ enc (nonnegHalf (Φ.eval s) j))
    rcases hf with hf | hf | hf
    · rw [scaledCantorCoord_eq_three_digits_add_tail]
      have hd0 : nonnegHalf (Φ.eval s) 0 =
          restrictToDom3 hD (Φ.G (restrictDom Φ.D s)) dom3NegOne := by
        simp only [nonnegHalf, GeneralizedShift.eval_apply, hf]
        norm_num
        exact replaceDom_mem _ _ _ hm1_mem
      have hd1 : nonnegHalf (Φ.eval s) 1 =
          restrictToDom3 hD (Φ.G (restrictDom Φ.D s)) dom3Zero := by
        simp only [nonnegHalf, GeneralizedShift.eval_apply, hf]
        norm_num
        exact replaceDom_mem _ _ _ h0_mem
      have hd2 : nonnegHalf (Φ.eval s) 2 =
          restrictToDom3 hD (Φ.G (restrictDom Φ.D s)) dom3One := by
        simp only [nonnegHalf, GeneralizedShift.eval_apply, hf]
        norm_num
        exact replaceDom_mem _ _ _ h1_mem
      have htail : (fun j : ℕ ↦ enc (nonnegHalf (Φ.eval s) (j + 3))) =
          fun j : ℕ ↦ enc (s ((j : ℤ) + 2)) := by
        funext j
        congr 1
        simp only [nonnegHalf, GeneralizedShift.eval_apply]
        have hidx : ((j + 3 : ℕ) : ℤ) + Φ.F (restrictDom Φ.D s) = (j : ℤ) + 2 := by omega
        rw [hidx, replaceDom_notMem _ _ _ (hnot_pos j)]
      rw [hd0, hd1, hd2, htail]
      simp only [blockOffsetY, hf, hm1_ne_1, ↓reduceIte, zpow_neg_one]
      field_simp [hB0]
      ring
    · rw [scaledCantorCoord_eq_two_digits_add_tail]
      have hd0 : nonnegHalf (Φ.eval s) 0 =
          restrictToDom3 hD (Φ.G (restrictDom Φ.D s)) dom3Zero := by
        simp only [nonnegHalf, GeneralizedShift.eval_apply, hf]
        norm_num
        exact replaceDom_mem _ _ _ h0_mem
      have hd1 : nonnegHalf (Φ.eval s) 1 =
          restrictToDom3 hD (Φ.G (restrictDom Φ.D s)) dom3One := by
        simp only [nonnegHalf, GeneralizedShift.eval_apply, hf]
        norm_num
        exact replaceDom_mem _ _ _ h1_mem
      have htail : (fun j : ℕ ↦ enc (nonnegHalf (Φ.eval s) (j + 2))) =
          fun j : ℕ ↦ enc (s ((j : ℤ) + 2)) := by
        funext j
        congr 1
        simp only [nonnegHalf, GeneralizedShift.eval_apply]
        have hidx : ((j + 2 : ℕ) : ℤ) + Φ.F (restrictDom Φ.D s) = (j : ℤ) + 2 := by omega
        rw [hidx, replaceDom_notMem _ _ _ (hnot_pos j)]
      rw [hd0, hd1, htail]
      simp only [blockOffsetY, hf, h0_ne_1, h0_ne_m1, ↓reduceIte, zpow_zero, one_mul]
      field_simp [hB0]
      ring
    · rw [scaledCantorCoord_eq_one_digit_add_tail]
      have hd0 : nonnegHalf (Φ.eval s) 0 =
          restrictToDom3 hD (Φ.G (restrictDom Φ.D s)) dom3One := by
        simp only [nonnegHalf, GeneralizedShift.eval_apply, hf]
        norm_num
        exact replaceDom_mem _ _ _ h1_mem
      have htail : (fun j : ℕ ↦ enc (nonnegHalf (Φ.eval s) (j + 1))) =
          fun j : ℕ ↦ enc (s ((j : ℤ) + 2)) := by
        funext j
        congr 1
        simp only [nonnegHalf, GeneralizedShift.eval_apply]
        have hidx : ((j + 1 : ℕ) : ℤ) + Φ.F (restrictDom Φ.D s) = (j : ℤ) + 2 := by omega
        rw [hidx, replaceDom_notMem _ _ _ (hnot_pos j)]
      rw [hd0, htail]
      simp only [blockOffsetY, hf, ↓reduceIte, zpow_one]
      field_simp [hB0]
      ring

/-- Cylinder preimage reconstruction: if `y : ℤ → A` satisfies `y (i - Φ.F w) = Φ.G w i` for all
`i ∈ Φ.D`, then `s := replaceDom Φ.D w (shiftSeq (-Φ.F w) y)` belongs to `cyl(w)` and satisfies
`Φ.eval s = y`. -/
-- tier: T1
theorem eval_replaceDom_shiftSeq_neg {A : Type*} (Φ : GeneralizedShift A) (w : Φ.D → A)
    {y : ℤ → A} (hy : ∀ i : Φ.D, y (i.1 - Φ.F w) = Φ.G w i) :
    Φ.eval (replaceDom Φ.D w (shiftSeq (-Φ.F w) y)) = y := by
  funext k
  rw [GeneralizedShift.eval_apply, restrictDom_replaceDom]
  by_cases hm : k + Φ.F w ∈ Φ.D
  · rw [replaceDom_mem _ _ _ hm, ← hy ⟨k + Φ.F w, hm⟩]
    dsimp only
    congr 1
    omega
  · rw [replaceDom_notMem _ _ _ hm, replaceDom_notMem _ _ _ hm, shiftSeq_apply]
    congr 1
    omega

/-- **Lemma G0 (`MISSION_DIRECTIVE_CMPP.md` §4.1, `docs/cmpp/geometry_spec.md` §2.1)**:
For any generalized shift `Φ` on `Φ.D = shiftDom3` with `Φ.F w ∈ {-1, 0, 1}`, if `Φ.eval` is
injective, then all target rectangles `imageRect enc Φ hD w` (`w : Φ.D → A`) are pairwise
disjoint. -/
-- tier: T2
theorem imageRect_pairwise_disjoint {A : Type*} {N : ℕ} (enc : A ≃ Fin N)
    (Φ : GeneralizedShift A) (hD : Φ.D = shiftDom3)
    (hF : ∀ w : Φ.D → A, Φ.F w = -1 ∨ Φ.F w = 0 ∨ Φ.F w = 1)
    (hinj : Function.Injective Φ.eval) :
    Pairwise (Disjoint on fun w : Φ.D → A ↦ (imageRect enc Φ hD w).toSet) := by
  intro w₁ w₂ hne
  rw [Function.onFun, Set.disjoint_left]
  intro z hz₁ hz₂
  obtain ⟨mNeg₁, mPos₁, pNeg₁, pPos₁, hset₁, hcyl₁⟩ :=
    exists_cantorClosedInterval_of_imageRect enc Φ hD w₁ (hF w₁)
  obtain ⟨mNeg₂, mPos₂, pNeg₂, pPos₂, hset₂, hcyl₂⟩ :=
    exists_cantorClosedInterval_of_imageRect enc Φ hD w₂ (hF w₂)
  rw [hset₁] at hz₁
  rw [hset₂] at hz₂
  have hcompatNeg := eq_of_cantorClosedInterval_inter_nonempty ⟨z 0, hz₁.1, hz₂.1⟩
  have hcompatPos := eq_of_cantorClosedInterval_inter_nonempty ⟨z 1, hz₁.2, hz₂.2⟩
  let a₀ : A := w₁ ⟨0, hD.symm ▸ dom3Zero.2⟩
  let yPos : ℕ → A := fun j ↦
    if hj₁ : j < mPos₁ then enc.symm (pPos₁ ⟨j, hj₁⟩)
    else if hj₂ : j < mPos₂ then enc.symm (pPos₂ ⟨j, hj₂⟩)
    else a₀
  let yNeg : ℕ → A := fun j ↦
    if hj₁ : j < mNeg₁ then enc.symm (pNeg₁ ⟨j, hj₁⟩)
    else if hj₂ : j < mNeg₂ then enc.symm (pNeg₂ ⟨j, hj₂⟩)
    else a₀
  let y : ℤ → A := fun k ↦
    match k with
    | Int.ofNat j => yPos j
    | Int.negSucc j => yNeg j
  have hyNeg_eq : ∀ j : ℕ, y (-((j : ℤ) + 1)) = yNeg j := fun j ↦ by
    rw [← Int.negSucc_eq j]
  have hyPos_eq : ∀ j : ℕ, y (j : ℤ) = yPos j := fun _ ↦ rfl
  have hyNeg₁ : ∀ j : Fin mNeg₁, enc (y (-((j.1 : ℤ) + 1))) = pNeg₁ j := by
    intro ⟨j, hj⟩
    rw [hyNeg_eq]
    simp [yNeg, hj]
  have hyPos₁ : ∀ j : Fin mPos₁, enc (y (j.1 : ℤ)) = pPos₁ j := by
    intro ⟨j, hj⟩
    rw [hyPos_eq]
    simp [yPos, hj]
  have hyNeg₂ : ∀ j : Fin mNeg₂, enc (y (-((j.1 : ℤ) + 1))) = pNeg₂ j := by
    intro ⟨j, hj₂⟩
    rw [hyNeg_eq]
    by_cases hj₁ : j < mNeg₁
    · simp [yNeg, hj₁, hcompatNeg j hj₁ hj₂]
    · simp [yNeg, hj₁, hj₂]
  have hyPos₂ : ∀ j : Fin mPos₂, enc (y (j.1 : ℤ)) = pPos₂ j := by
    intro ⟨j, hj₂⟩
    rw [hyPos_eq]
    by_cases hj₁ : j < mPos₁
    · simp [yPos, hj₁, hcompatPos j hj₁ hj₂]
    · simp [yPos, hj₁, hj₂]
  let s₁ : ℤ → A := replaceDom Φ.D w₁ (shiftSeq (-Φ.F w₁) y)
  let s₂ : ℤ → A := replaceDom Φ.D w₂ (shiftSeq (-Φ.F w₂) y)
  have hev₁ : Φ.eval s₁ = y := eval_replaceDom_shiftSeq_neg Φ w₁ (hcyl₁ y hyNeg₁ hyPos₁)
  have hev₂ : Φ.eval s₂ = y := eval_replaceDom_shiftSeq_neg Φ w₂ (hcyl₂ y hyNeg₂ hyPos₂)
  have hs_eq : s₁ = s₂ := hinj (hev₁.trans hev₂.symm)
  have hw_eq : w₁ = w₂ := by
    calc
      w₁ = restrictDom Φ.D s₁ := (restrictDom_replaceDom Φ.D w₁ _).symm
      _ = restrictDom Φ.D s₂ := by rw [hs_eq]
      _ = w₂ := restrictDom_replaceDom Φ.D w₂ _
  exact hne hw_eq

/-! ## 5. Specialization to `ReversibleTM.toGeneralizedShift` -/

/-- Every shift displacement `R.toGeneralizedShift.F w` of a `ReversibleTM` belongs to
`{-1, 0, 1}`. -/
-- tier: T1
theorem toGeneralizedShift_F_mem (R : ReversibleTM)
    (w : R.toGeneralizedShift.D → R.ShiftAlphabet) :
    R.toGeneralizedShift.F w = -1 ∨ R.toGeneralizedShift.F w = 0 ∨
      R.toGeneralizedShift.F w = 1 := by
  unfold ReversibleTM.toGeneralizedShift
  dsimp only
  rcases (w dom3Zero).2 with _ | q
  · exact Or.inr (Or.inl rfl)
  · exact shiftDir_toInt_mem _

/-- **Lemma G0 for `ReversibleTM`**: for any unidirectional reversible Turing machine `R` and
alphabet numbering `enc : R.ShiftAlphabet ≃ Fin N`, the `N³` target rectangles
`imageRect enc R.toGeneralizedShift R.toGeneralizedShift_D w` are pairwise disjoint. -/
-- tier: T2
theorem ReversibleTM.imageRect_pairwise_disjoint (R : ReversibleTM) {N : ℕ}
    (enc : R.ShiftAlphabet ≃ Fin N) :
    Pairwise (Disjoint on fun w : R.toGeneralizedShift.D → R.ShiftAlphabet ↦
      (imageRect enc R.toGeneralizedShift R.toGeneralizedShift_D w).toSet) :=
  CMPP.imageRect_pairwise_disjoint enc R.toGeneralizedShift R.toGeneralizedShift_D
    (toGeneralizedShift_F_mem R) R.bijective_eval.injective

/-- Specialization of `blockAffineMap_image_sourceRect` to `R.toGeneralizedShift`. -/
-- tier: T1
theorem ReversibleTM.blockAffineMap_image_sourceRect (R : ReversibleTM) {N : ℕ}
    (enc : R.ShiftAlphabet ≃ Fin N) (w : shiftDom3 → R.ShiftAlphabet) :
    blockAffineMap enc R.toGeneralizedShift R.toGeneralizedShift_D w '' (sourceRect enc w).toSet =
      (imageRect enc R.toGeneralizedShift R.toGeneralizedShift_D w).toSet :=
  CMPP.blockAffineMap_image_sourceRect enc R.toGeneralizedShift R.toGeneralizedShift_D w
    (toGeneralizedShift_F_mem R w)

/-- Specialization of `blockAffineMap_cantorDiskEmbed` to `R.toGeneralizedShift`. -/
-- tier: T1
theorem ReversibleTM.blockAffineMap_cantorDiskEmbed (R : ReversibleTM) {N : ℕ}
    (enc : R.ShiftAlphabet ≃ Fin N) {s : ℤ → R.ShiftAlphabet} {w : shiftDom3 → R.ShiftAlphabet}
    (hw : restrictDom shiftDom3 s = w) :
    blockAffineMap enc R.toGeneralizedShift R.toGeneralizedShift_D w (cantorDiskEmbed enc s).1 =
      (cantorDiskEmbed enc (R.toGeneralizedShift.eval s)).1 :=
  CMPP.blockAffineMap_cantorDiskEmbed enc R.toGeneralizedShift R.toGeneralizedShift_D hw
    (toGeneralizedShift_F_mem R w)

/-- Concrete 2-state, 2-symbol unidirectional `ReversibleTM` exercising all three shift directions
`{-1, 0, +1}` on `shiftDom3` (Gate G5 anti-vacuity witness). -/
def biDirToyTM : ReversibleTM where
  Γ := Bool
  Q := Bool
  stepPerm :=
    { toFun := fun p ↦ (!p.1, p.2)
      invFun := fun p ↦ (!p.1, p.2)
      left_inv := fun ⟨b, a⟩ ↦ by simp
      right_inv := fun ⟨b, a⟩ ↦ by simp }
  dirIn b := if b then .right else .left

/-- Explicit numbering `biDirToyTM.ShiftAlphabet ≃ Fin 6` (`N = 6`, `cantorBase 6 = 11`). -/
def biDirToyEnc : biDirToyTM.ShiftAlphabet ≃ Fin 6 where
  toFun x :=
    match x with
    | (false, none) => 0
    | (false, some false) => 1
    | (false, some true) => 2
    | (true, none) => 3
    | (true, some false) => 4
    | (true, some true) => 5
  invFun i :=
    match i with
    | ⟨0, _⟩ => (false, none)
    | ⟨1, _⟩ => (false, some false)
    | ⟨2, _⟩ => (false, some true)
    | ⟨3, _⟩ => (true, none)
    | ⟨4, _⟩ => (true, some false)
    | ⟨5, _⟩ => (true, some true)
  left_inv x := by rcases x with ⟨_ | _, _ | _ | _⟩ <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- Gate G5 non-vacuity sanity check: `biDirToyTM` realizes all three shift displacements
`{-1, 0, +1}`, maps distinct blocks to nonempty disjoint target rectangles inside `[0, 1/4]²`, and
moves a concrete Cantor configuration non-trivially under `blockAffineMap`. -/
-- tier: T1
theorem biDirToyTM_imageRect_sanity :
    let Φ := biDirToyTM.toGeneralizedShift
    let wLeft : shiftDom3 → biDirToyTM.ShiftAlphabet :=
      mkDom3 (false, none) (false, some true) (false, none)
    let wStay : shiftDom3 → biDirToyTM.ShiftAlphabet :=
      mkDom3 (false, none) (false, none) (false, none)
    let wRight : shiftDom3 → biDirToyTM.ShiftAlphabet :=
      mkDom3 (false, none) (false, some false) (false, none)
    let s₀ : ℤ → biDirToyTM.ShiftAlphabet :=
      biDirToyTM.encodeCfg { q := true, Tape := default }
    Φ.F wLeft = -1 ∧
    Φ.F wStay = 0 ∧
    Φ.F wRight = 1 ∧
    (imageRect biDirToyEnc Φ rfl wLeft).toSet.Nonempty ∧
    (imageRect biDirToyEnc Φ rfl wRight).toSet.Nonempty ∧
    Disjoint (imageRect biDirToyEnc Φ rfl wLeft).toSet
      (imageRect biDirToyEnc Φ rfl wRight).toSet ∧
    blockAffineMap biDirToyEnc Φ rfl (restrictDom shiftDom3 s₀)
        (cantorDiskEmbed biDirToyEnc s₀).1 ≠
      (cantorDiskEmbed biDirToyEnc s₀).1 := by
  intro Φ wLeft wStay wRight s₀
  have hne : wLeft ≠ wRight := by
    intro h
    have h0 := congrFun h dom3Zero
    dsimp [wLeft, wRight] at h0
    cases h0
  refine ⟨rfl, rfl, rfl, AxisRect.nonempty_toSet _, AxisRect.nonempty_toSet _,
    ReversibleTM.imageRect_pairwise_disjoint biDirToyTM biDirToyEnc hne, ?_⟩
  rw [ReversibleTM.blockAffineMap_cantorDiskEmbed biDirToyTM biDirToyEnc rfl]
  intro heq
  have hseq := cantorDiskEmbed_injective biDirToyEnc (Subtype.ext heq)
  rw [biDirToyTM.eval_encodeCfg] at hseq
  have h0 := congrArg Prod.snd (congrFun hseq 0)
  dsimp [s₀, biDirToyTM, ReversibleTM.step, ReversibleTM.encodeCfg] at h0
  cases h0

end S4TuringPoisson.CMPP
