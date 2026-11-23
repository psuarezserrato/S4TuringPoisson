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

public import S4TuringPoisson.Smoothing.CMPP.Digits
public import S4TuringPoisson.Smoothing.DiskSmoothing
public import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# CMPP Hamiltonian Flow Primitives L1 & L2 (CMPP Milestone A2)

This module formalizes Milestone A2 (`S4TuringPoisson/Smoothing/CMPP/Primitives.lean`) of the
`CMPP21` Hamiltonian realization pipeline (`MISSION_DIRECTIVE_CMPP.md` §4.2, §7, §10 and
`docs/cmpp/geometry_spec.md` §3.3 & §4.2):

1. **Autonomous Planar Hamiltonians (`CompactlySupportedPlanarHamiltonian.IsAutonomous`)**:
   - Defines time-independence `∀ t y, P.H (t, y) = P.H (0, y)` required by Deliverable R5
     (4-manifold Poisson-Hamiltonian lifting on `Sphere4`), and verifies autonomy of
     `ofAutonomous`, `bumpedHyperbolicStretchHamiltonian`, and `bumpedCenterRotationHamiltonian`.

2. **Swept Translation Tubes & Open Rectangle Expansions (`translationTube`, `openExpand`)**:
   - Defines `translationTube S v = { x + t • v | x ∈ S, t ∈ [0, 1] }`, proves compactness for
     compact `S`, endpoint inclusions at `t = 0` and `t = 1`, inclusion of axis-rectangle tubes in
     `(R.tubeRect dx dy).toSet`, and open `ε`-expansions `AxisRect.openExpand` for Milestone A3.

3. **Smooth Compact-in-Open Urysohn Cutoff (`exists_contDiff_cutoff_of_isCompact_subset_isOpen`)**:
   - Constructs a $C^\infty$ cutoff `χ : EuclideanPlane → [0, 1]` identically `1` on an open
     neighborhood of any compact `K ⊆ U` with `tsupport χ ⊆ U`.

4. **Primitive L1 — Autonomous Rigid Translation (`exists_translation_hamiltonian`)**:
   - Multiplies the linear Hamiltonian `transLinear v y = v₀ y₁ - v₁ y₀` (`X = +v`) by a smooth
     cutoff `≡ 1` near `translationTube S v` and supported in `U ⊆ Metric.ball 0 r₀`, yielding an
     autonomous `CompactlySupportedPlanarHamiltonian r₀` whose time-`1` flow translates `S` rigidly
     by `+v` and fixes `Uᶜ` pointwise.

5. **Primitive L2 — Tight Rectangle Hyperbolic Stretch & Cantor Workbench Bounds**:
   - Proves exterior fixity `bumpedHyperbolicStretchIsotopy_eq_self_of_notMem_ball` outside
     `Metric.ball c r_out` and tight rectangle exactness
     `bumpedHyperbolicStretchIsotopy_timeOne_of_mem_rect` on
     `[c₀ - δ₀, c₀ + δ₀] × [c₁ - δ₁, c₁ + δ₁]` whenever
     `max(δ₀, e^{-μ} δ₀)² + max(δ₁, e^μ δ₁)² < (r_out / 2)²`, specialized unconditionally
     to `cantorBase N` (`B ≥ 3`, `r_out = 3/10`) in
     `bumpedHyperbolicStretchIsotopy_cantorRect_timeOne`, together with Gate G5 non-vacuity checks.
-/

@[expose] public section

open Bundle Filter Function Metric Module Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace S4TuringPoisson

/-- An autonomous compactly supported planar Hamiltonian `P` satisfies `P.H (t, y) = P.H (0, y)`
for all `(t, y)` (`docs/cmpp/geometry_spec.md` §4.2). -/
def CompactlySupportedPlanarHamiltonian.IsAutonomous {r₀ : ℝ}
    (P : CompactlySupportedPlanarHamiltonian r₀) : Prop :=
  ∀ (t : ℝ) (y : EuclideanPlane), P.H (t, y) = P.H (0, y)

end S4TuringPoisson

namespace S4TuringPoisson.CMPP

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

/-! ## 1. Autonomous Planar Hamiltonians & Basic Definitions -/

/-- Swept linear translation tube `{ x + t • v | x ∈ S, t ∈ [0, 1] }` of a planar set `S` along
displacement vector `v : EuclideanPlane`. -/
def translationTube (S : Set EuclideanPlane) (v : EuclideanPlane) : Set EuclideanPlane :=
  { y : EuclideanPlane | ∃ x ∈ S, ∃ t ∈ Set.Icc (0 : ℝ) 1, y = x + t • v }

/-- Open axis-parallel `ε`-expansion `(xMin - ε, xMax + ε) × (yMin - ε, yMax + ε)` of an
`AxisRect`. -/
def AxisRect.openExpand (R : AxisRect) (ε : ℝ) : Set EuclideanPlane :=
  { p : EuclideanPlane |
    p 0 ∈ Set.Ioo (R.xMin - ε) (R.xMax + ε) ∧
    p 1 ∈ Set.Ioo (R.yMin - ε) (R.yMax + ε) }

/-- Construct an `AxisRect` `[c₀ - δ₀, c₀ + δ₀] × [c₁ - δ₁, c₁ + δ₁]` from center `c` and
non-negative half-widths `δ₀, δ₁`. -/
noncomputable def AxisRect.ofCenter (c : EuclideanPlane) {δ₀ δ₁ : ℝ} (hδ₀ : 0 ≤ δ₀)
    (hδ₁ : 0 ≤ δ₁) : AxisRect where
  xMin := c 0 - δ₀
  xMax := c 0 + δ₀
  yMin := c 1 - δ₁
  yMax := c 1 + δ₁
  hx := by linarith
  hy := by linarith

/-- Linear planar Hamiltonian `v₀ y₁ - v₁ y₀` whose Hamiltonian vector field with respect to
`planeAreaForm = dx ∧ dy` is the constant vector `+v`. -/
noncomputable def transLinear (v y : EuclideanPlane) : ℝ :=
  v 0 * y 1 - v 1 * y 0

/-- Continuous linear functional `y ↦ v₀ y₁ - v₁ y₀` underlying `transLinear v`. -/
noncomputable def transLinearCLM (v : EuclideanPlane) : EuclideanPlane →L[ℝ] ℝ :=
  v 0 • planeCoordCLM 1 - v 1 • planeCoordCLM 0

/-- Every Hamiltonian constructed via `CompactlySupportedPlanarHamiltonian.ofAutonomous` is
autonomous. -/
-- tier: T0
theorem ofAutonomous_isAutonomous {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    (h : EuclideanPlane → ℝ) (hh : ContDiff ℝ ∞ h)
    (hsupp : ∀ y : EuclideanPlane, y ∉ Metric.ball (0 : EuclideanPlane) r₀ → h y = 0) :
    (CompactlySupportedPlanarHamiltonian.ofAutonomous hr₀ h hh hsupp).IsAutonomous :=
  fun _ _ ↦ rfl

/-- Time-`t` slice of `CompactlySupportedPlanarHamiltonian.ofAutonomous` equals `h`. -/
-- tier: T0
@[simp]
theorem ofAutonomous_slice {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    (h : EuclideanPlane → ℝ) (hh : ContDiff ℝ ∞ h)
    (hsupp : ∀ y : EuclideanPlane, y ∉ Metric.ball (0 : EuclideanPlane) r₀ → h y = 0)
    (t : ℝ) :
    (CompactlySupportedPlanarHamiltonian.ofAutonomous hr₀ h hh hsupp).slice t = h :=
  rfl

/-- For an autonomous `CompactlySupportedPlanarHamiltonian`, every time-`t` slice equals the
time-`0` slice. -/
-- tier: T0
theorem slice_eq_of_isAutonomous {r₀ : ℝ} {P : CompactlySupportedPlanarHamiltonian r₀}
    (hP : P.IsAutonomous) (t : ℝ) :
    P.slice t = P.slice 0 := by
  funext y
  exact hP t y

/-- `bumpedHyperbolicStretchHamiltonian` is autonomous. -/
-- tier: T0
theorem bumpedHyperbolicStretchHamiltonian_isAutonomous {r₀ : ℝ}
    (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1) (c : EuclideanPlane) {r_out : ℝ} (hr_out : 0 < r_out)
    (hsub : Metric.ball c r_out ⊆ Metric.ball (0 : EuclideanPlane) r₀) (μ : ℝ) :
    (bumpedHyperbolicStretchHamiltonian hr₀ c hr_out hsub μ).IsAutonomous :=
  fun _ _ ↦ rfl

/-- `bumpedCenterRotationHamiltonian` is autonomous. -/
-- tier: T0
theorem bumpedCenterRotationHamiltonian_isAutonomous {r₀ : ℝ}
    (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1) (c : EuclideanPlane) {r_in r_out : ℝ}
    (hr_in : 0 < r_in) (hr_lt : r_in < r_out)
    (hsub : Metric.ball c r_out ⊆ Metric.ball (0 : EuclideanPlane) r₀) (θ : ℝ) :
    (bumpedCenterRotationHamiltonian hr₀ c hr_in hr_lt hsub θ).IsAutonomous :=
  fun _ _ ↦ rfl

/-- Pointwise membership characterization for `translationTube S v`. -/
-- tier: T0
@[simp]
theorem mem_translationTube_iff (S : Set EuclideanPlane) (v y : EuclideanPlane) :
    y ∈ translationTube S v ↔ ∃ x ∈ S, ∃ t ∈ Set.Icc (0 : ℝ) 1, y = x + t • v :=
  Iff.rfl

/-- Initial slice `t = 0`: every set `S` is contained in `translationTube S v`. -/
-- tier: T0
theorem subset_translationTube_zero (S : Set EuclideanPlane) (v : EuclideanPlane) :
    S ⊆ translationTube S v := by
  intro x hx
  exact ⟨x, hx, 0, ⟨le_rfl, zero_le_one⟩, by simp⟩

/-- Final slice `t = 1`: for every `x ∈ S`, `x + v` belongs to `translationTube S v`. -/
-- tier: T0
theorem add_mem_translationTube_one {S : Set EuclideanPlane} {x : EuclideanPlane}
    (hx : x ∈ S) (v : EuclideanPlane) :
    x + v ∈ translationTube S v :=
  ⟨x, hx, 1, ⟨zero_le_one, le_rfl⟩, by simp⟩

/-- Pointwise membership characterization for `AxisRect.openExpand`. -/
-- tier: T0
@[simp]
theorem AxisRect.mem_openExpand_iff (R : AxisRect) (ε : ℝ) (p : EuclideanPlane) :
    p ∈ R.openExpand ε ↔
      p 0 ∈ Set.Ioo (R.xMin - ε) (R.xMax + ε) ∧
      p 1 ∈ Set.Ioo (R.yMin - ε) (R.yMax + ε) :=
  by
  unfold AxisRect.openExpand
  simp

/-- For any `ε > 0`, `R.toSet` is contained in the open `ε`-expansion `R.openExpand ε`. -/
-- tier: T0
theorem AxisRect.toSet_subset_openExpand (R : AxisRect) {ε : ℝ} (hε : 0 < ε) :
    R.toSet ⊆ R.openExpand ε := by
  intro p hp
  rw [AxisRect.mem_toSet_iff] at hp
  rw [AxisRect.mem_openExpand_iff]
  exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩,
    ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩

/-- Left `x`-endpoint of `AxisRect.ofCenter`. -/
-- tier: T0
@[simp]
theorem AxisRect.ofCenter_xMin (c : EuclideanPlane) {δ₀ δ₁ : ℝ} (hδ₀ : 0 ≤ δ₀)
    (hδ₁ : 0 ≤ δ₁) :
    (AxisRect.ofCenter c hδ₀ hδ₁).xMin = c 0 - δ₀ :=
  by
  simp [AxisRect.ofCenter]

/-- Right `x`-endpoint of `AxisRect.ofCenter`. -/
-- tier: T0
@[simp]
theorem AxisRect.ofCenter_xMax (c : EuclideanPlane) {δ₀ δ₁ : ℝ} (hδ₀ : 0 ≤ δ₀)
    (hδ₁ : 0 ≤ δ₁) :
    (AxisRect.ofCenter c hδ₀ hδ₁).xMax = c 0 + δ₀ :=
  by
  simp [AxisRect.ofCenter]

/-- Lower `y`-endpoint of `AxisRect.ofCenter`. -/
-- tier: T0
@[simp]
theorem AxisRect.ofCenter_yMin (c : EuclideanPlane) {δ₀ δ₁ : ℝ} (hδ₀ : 0 ≤ δ₀)
    (hδ₁ : 0 ≤ δ₁) :
    (AxisRect.ofCenter c hδ₀ hδ₁).yMin = c 1 - δ₁ := by
  simp [AxisRect.ofCenter]

/-- Upper `y`-endpoint of `AxisRect.ofCenter`. -/
-- tier: T0
@[simp]
theorem AxisRect.ofCenter_yMax (c : EuclideanPlane) {δ₀ δ₁ : ℝ} (hδ₀ : 0 ≤ δ₀)
    (hδ₁ : 0 ≤ δ₁) :
    (AxisRect.ofCenter c hδ₀ hδ₁).yMax = c 1 + δ₁ :=
  by
  simp [AxisRect.ofCenter]

/-- Evaluation of `transLinearCLM v` equals `transLinear v`. -/
-- tier: T0
@[simp]
theorem transLinearCLM_apply (v y : EuclideanPlane) :
    transLinearCLM v y = transLinear v y :=
  by
  rfl

/-- At zero displacement `v = 0`, `transLinear 0` vanishes identically. -/
-- tier: T0
@[simp]
theorem transLinear_zero (y : EuclideanPlane) : transLinear 0 y = 0 :=
  by
  simp [transLinear]

/-- For an autonomous `CompactlySupportedPlanarHamiltonian`, the Hamiltonian vector field
`P.vectorField t` is independent of `t`. -/
-- tier: T1
theorem vectorField_eq_of_isAutonomous {r₀ : ℝ} {P : CompactlySupportedPlanarHamiltonian r₀}
    (hP : P.IsAutonomous) (t : ℝ) (y : EuclideanPlane) :
    P.vectorField t y = P.vectorField 0 y := by
  unfold CompactlySupportedPlanarHamiltonian.vectorField
  rw [slice_eq_of_isAutonomous hP t]

/-- `bumpedRotationHamiltonian` is autonomous. -/
-- tier: T1
theorem bumpedRotationHamiltonian_isAutonomous {r₀ r_in : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hr_in : r_in ∈ Set.Ioo (0 : ℝ) r₀) :
    (bumpedRotationHamiltonian hr₀ hr_in).IsAutonomous :=
  bumpedCenterRotationHamiltonian_isAutonomous hr₀ 0 hr_in.1 hr_in.2 Subset.rfl (-Real.pi)

/-! ## 2. Swept Translation Tubes, `AxisRect.openExpand`, and Centered Rectangles -/

/-- For `x ∈ S` and `t ∈ [0, 1]`, the convex-combination point `x + t • v` belongs to
`translationTube S v`. -/
-- tier: T1
theorem mem_translationTube_of_mem_Icc {S : Set EuclideanPlane} {x : EuclideanPlane}
    (hx : x ∈ S) (v : EuclideanPlane) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    x + t • v ∈ translationTube S v :=
  ⟨x, hx, t, ht, rfl⟩

/-- Monotonicity of `translationTube` in the source set `S`. -/
-- tier: T1
theorem translationTube_mono_left {S₁ S₂ : Set EuclideanPlane} (hsub : S₁ ⊆ S₂)
    (v : EuclideanPlane) :
    translationTube S₁ v ⊆ translationTube S₂ v := by
  rintro y ⟨x, hx, t, ht, rfl⟩
  exact ⟨x, hsub hx, t, ht, rfl⟩

/-- Sweeping along zero displacement leaves `S` unchanged. -/
-- tier: T1
@[simp]
theorem translationTube_zero_right (S : Set EuclideanPlane) :
    translationTube S 0 = S := by
  ext y
  constructor
  · rintro ⟨x, hx, _, _, rfl⟩
    simpa using hx
  · intro hy
    exact subset_translationTube_zero S 0 hy

/-- Image of `S` under translation by `+v` is contained in `translationTube S v`. -/
-- tier: T1
theorem image_add_subset_translationTube (S : Set EuclideanPlane) (v : EuclideanPlane) :
    (fun x : EuclideanPlane ↦ x + v) '' S ⊆ translationTube S v := by
  rintro _ ⟨x, hx, rfl⟩
  exact add_mem_translationTube_one hx v

/-- If `S ⊆ EuclideanPlane` is compact, then its swept linear tube `translationTube S v` is
compact. -/
-- tier: T1
theorem isCompact_translationTube {S : Set EuclideanPlane} (hS : IsCompact S)
    (v : EuclideanPlane) :
    IsCompact (translationTube S v) := by
  let φ : EuclideanPlane × ℝ → EuclideanPlane := fun p ↦ p.1 + p.2 • v
  have hcont : Continuous φ :=
    continuous_fst.add (continuous_snd.smul continuous_const)
  have heq : φ '' (S ×ˢ Set.Icc (0 : ℝ) 1) = translationTube S v := by
    ext y
    simp only [Set.mem_image, Set.mem_prod, mem_translationTube_iff, Prod.exists, φ]
    constructor
    · rintro ⟨x, t, ⟨hx, ht⟩, rfl⟩
      exact ⟨x, hx, t, ht, rfl⟩
    · rintro ⟨x, hx, t, ht, rfl⟩
      exact ⟨x, t, ⟨hx, ht⟩, rfl⟩
  rw [← heq]
  exact (hS.prod isCompact_Icc).image hcont

/-- For any `AxisRect` `R` and displacement `(dx, dy)`, the swept tube
`translationTube R.toSet ![dx, dy]` is contained in `(R.tubeRect dx dy).toSet`. -/
-- tier: T1
theorem translationTube_axisRect_subset_tubeRect (R : AxisRect) (dx dy : ℝ) :
    translationTube R.toSet (WithLp.toLp 2 ![dx, dy]) ⊆ (R.tubeRect dx dy).toSet := by
  rintro y ⟨x, hx, t, ht, rfl⟩
  exact R.mem_tubeRect_of_mem_Icc hx dx dy ht

/-- Vector form of `translationTube_axisRect_subset_tubeRect` for arbitrary `v : EuclideanPlane`. -/
-- tier: T1
theorem translationTube_axisRect_subset_tubeRect_vec (R : AxisRect) (v : EuclideanPlane) :
    translationTube R.toSet v ⊆ (R.tubeRect (v 0) (v 1)).toSet := by
  have hv : v = WithLp.toLp 2 ![v 0, v 1] := by
    ext i
    fin_cases i <;> rfl
  conv_lhs => rw [hv]
  exact translationTube_axisRect_subset_tubeRect R (v 0) (v 1)

/-- Every `AxisRect.openExpand` is an open subset of `EuclideanPlane`. -/
-- tier: T1
theorem AxisRect.isOpen_openExpand (R : AxisRect) (ε : ℝ) :
    IsOpen (R.openExpand ε) := by
  have h0 : Continuous fun p : EuclideanPlane ↦ p 0 := (planeCoordCLM 0).continuous
  have h1 : Continuous fun p : EuclideanPlane ↦ p 1 := (planeCoordCLM 1).continuous
  exact (isOpen_Ioo.preimage h0).inter (isOpen_Ioo.preimage h1)

/-- Horizontal separation helper for Milestone A3: if `R₁.xMax ≤ R₂.xMin - ε`, then `R₁.toSet` is
disjoint from `R₂.openExpand ε`. -/
-- tier: T1
theorem AxisRect.disjoint_toSet_openExpand_of_xMax_le {R₁ R₂ : AxisRect} {ε : ℝ}
    (hx : R₁.xMax ≤ R₂.xMin - ε) :
    Disjoint R₁.toSet (R₂.openExpand ε) := by
  rw [Set.disjoint_left]
  intro p hp₁ hp₂
  rw [AxisRect.mem_toSet_iff] at hp₁
  rw [AxisRect.mem_openExpand_iff] at hp₂
  linarith [hp₁.1.2, hp₂.1.1]

/-- Horizontal separation helper for Milestone A3: if `R₂.xMax + ε ≤ R₁.xMin`, then `R₁.toSet` is
disjoint from `R₂.openExpand ε`. -/
-- tier: T1
theorem AxisRect.disjoint_toSet_openExpand_of_le_xMin {R₁ R₂ : AxisRect} {ε : ℝ}
    (hx : R₂.xMax + ε ≤ R₁.xMin) :
    Disjoint R₁.toSet (R₂.openExpand ε) := by
  rw [Set.disjoint_left]
  intro p hp₁ hp₂
  rw [AxisRect.mem_toSet_iff] at hp₁
  rw [AxisRect.mem_openExpand_iff] at hp₂
  linarith [hp₁.1.1, hp₂.1.2]

/-- Vertical separation helper for Milestone A3: if `R₁.yMax ≤ R₂.yMin - ε`, then `R₁.toSet` is
disjoint from `R₂.openExpand ε`. -/
-- tier: T1
theorem AxisRect.disjoint_toSet_openExpand_of_yMax_le {R₁ R₂ : AxisRect} {ε : ℝ}
    (hy : R₁.yMax ≤ R₂.yMin - ε) :
    Disjoint R₁.toSet (R₂.openExpand ε) := by
  rw [Set.disjoint_left]
  intro p hp₁ hp₂
  rw [AxisRect.mem_toSet_iff] at hp₁
  rw [AxisRect.mem_openExpand_iff] at hp₂
  linarith [hp₁.2.2, hp₂.2.1]

/-- Vertical separation helper for Milestone A3: if `R₂.yMax + ε ≤ R₁.yMin`, then `R₁.toSet` is
disjoint from `R₂.openExpand ε`. -/
-- tier: T1
theorem AxisRect.disjoint_toSet_openExpand_of_le_yMin {R₁ R₂ : AxisRect} {ε : ℝ}
    (hy : R₂.yMax + ε ≤ R₁.yMin) :
    Disjoint R₁.toSet (R₂.openExpand ε) := by
  rw [Set.disjoint_left]
  intro p hp₁ hp₂
  rw [AxisRect.mem_toSet_iff] at hp₁
  rw [AxisRect.mem_openExpand_iff] at hp₂
  linarith [hp₁.2.1, hp₂.2.2]

/-- Geometric center of `AxisRect.ofCenter c hδ₀ hδ₁` equals `c`. -/
-- tier: T1
@[simp]
theorem AxisRect.center_ofCenter (c : EuclideanPlane) {δ₀ δ₁ : ℝ} (hδ₀ : 0 ≤ δ₀)
    (hδ₁ : 0 ≤ δ₁) :
    (AxisRect.ofCenter c hδ₀ hδ₁).center = c := by
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, AxisRect.center_zero, AxisRect.ofCenter_xMin, AxisRect.ofCenter_xMax]
    ring
  · simp only [Fin.mk_one, AxisRect.center_one, AxisRect.ofCenter_yMin, AxisRect.ofCenter_yMax]
    ring

/-- Width of `AxisRect.ofCenter c hδ₀ hδ₁` equals `2 * δ₀`. -/
-- tier: T1
@[simp]
theorem AxisRect.width_ofCenter (c : EuclideanPlane) {δ₀ δ₁ : ℝ} (hδ₀ : 0 ≤ δ₀)
    (hδ₁ : 0 ≤ δ₁) :
    (AxisRect.ofCenter c hδ₀ hδ₁).width = 2 * δ₀ := by
  unfold AxisRect.width
  rw [AxisRect.ofCenter_xMax, AxisRect.ofCenter_xMin]
  ring

/-- Height of `AxisRect.ofCenter c hδ₀ hδ₁` equals `2 * δ₁`. -/
-- tier: T1
@[simp]
theorem AxisRect.height_ofCenter (c : EuclideanPlane) {δ₀ δ₁ : ℝ} (hδ₀ : 0 ≤ δ₀)
    (hδ₁ : 0 ≤ δ₁) :
    (AxisRect.ofCenter c hδ₀ hδ₁).height = 2 * δ₁ := by
  unfold AxisRect.height
  rw [AxisRect.ofCenter_yMax, AxisRect.ofCenter_yMin]
  ring

/-- Pointwise half-width characterization for `(AxisRect.ofCenter c hδ₀ hδ₁).toSet`. -/
-- tier: T1
theorem AxisRect.mem_ofCenter_iff (c : EuclideanPlane) {δ₀ δ₁ : ℝ} (hδ₀ : 0 ≤ δ₀)
    (hδ₁ : 0 ≤ δ₁) (y : EuclideanPlane) :
    y ∈ (AxisRect.ofCenter c hδ₀ hδ₁).toSet ↔
      |y 0 - c 0| ≤ δ₀ ∧ |y 1 - c 1| ≤ δ₁ := by
  rw [AxisRect.mem_toSet_iff, AxisRect.ofCenter_xMin, AxisRect.ofCenter_xMax,
    AxisRect.ofCenter_yMin, AxisRect.ofCenter_yMax, Set.mem_Icc, Set.mem_Icc, abs_le, abs_le]
  constructor
  · rintro ⟨⟨hx₁, hx₂⟩, ⟨hy₁, hy₂⟩⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · rintro ⟨⟨hx₁, hx₂⟩, ⟨hy₁, hy₂⟩⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- Every point `y ∈ R.toSet` deviates from `R.center` by at most `(R.width / 2, R.height / 2)`. -/
-- tier: T1
theorem AxisRect.abs_sub_center_le_half_of_mem {R : AxisRect} {y : EuclideanPlane}
    (hy : y ∈ R.toSet) :
    |y 0 - R.center 0| ≤ R.width / 2 ∧ |y 1 - R.center 1| ≤ R.height / 2 := by
  rw [AxisRect.mem_toSet_iff] at hy
  rw [AxisRect.center_zero, AxisRect.center_one, AxisRect.width, AxisRect.height, abs_le, abs_le]
  exact ⟨⟨by linarith [hy.1.1], by linarith [hy.1.2]⟩,
    ⟨by linarith [hy.2.1], by linarith [hy.2.2]⟩⟩

/-! ## 3. Smooth Compact-in-Open Urysohn Cutoff & Open Interval Thickening -/

/-- Any open subset `W ⊆ ℝ` containing `[0, 1]` contains `(-ε, 1 + ε)` for some `ε > 0`. -/
-- tier: T1
theorem exists_Ioo_subset_of_isOpen_of_Icc_subset {W : Set ℝ} (hW : IsOpen W)
    (hsub : Set.Icc (0 : ℝ) 1 ⊆ W) :
    ∃ ε : ℝ, 0 < ε ∧ Set.Ioo (-ε) (1 + ε) ⊆ W := by
  obtain ⟨ε, hε, hthick⟩ := isCompact_Icc.exists_cthickening_subset_open hW hsub
  refine ⟨ε, hε, fun u hu ↦ hthick ?_⟩
  rcases lt_trichotomy u 0 with hu0 | rfl | hu0
  · refine Metric.thickening_subset_cthickening ε _ (Metric.mem_thickening_iff.mpr ⟨0, ?_, ?_⟩)
    · exact ⟨le_rfl, zero_le_one⟩
    · rw [Real.dist_eq, sub_zero, abs_of_neg hu0]
      exact neg_lt.mp hu.1
  · exact Metric.thickening_subset_cthickening ε _
      (Metric.self_subset_thickening hε _ ⟨le_rfl, zero_le_one⟩)
  · rcases le_or_gt u 1 with hu1 | hu1
    · exact Metric.thickening_subset_cthickening ε _
        (Metric.self_subset_thickening hε _ ⟨hu0.le, hu1⟩)
    · refine Metric.thickening_subset_cthickening ε _ (Metric.mem_thickening_iff.mpr ⟨1, ?_, ?_⟩)
      · exact ⟨zero_le_one, le_rfl⟩
      · rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hu1)]
        linarith [hu.2]

/-- **Smooth Compact-in-Open Urysohn Cutoff on `EuclideanPlane`**:
For any compact subset `K` of an open set `U ⊆ EuclideanPlane`, there exists a $C^\infty$ cutoff
`χ : EuclideanPlane → ℝ` taking values in `[0, 1]`, identically equal to `1` on an open
neighborhood `V` of `K`, with compact topological support `tsupport χ ⊆ U`. -/
-- tier: T2
theorem exists_contDiff_cutoff_of_isCompact_subset_isOpen
    {K U : Set EuclideanPlane} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : EuclideanPlane → ℝ,
      ContDiff ℝ ∞ χ ∧
      (∀ y : EuclideanPlane, χ y ∈ Set.Icc (0 : ℝ) 1) ∧
      (∃ V : Set EuclideanPlane, IsOpen V ∧ K ⊆ V ∧ ∀ y ∈ V, χ y = 1) ∧
      HasCompactSupport χ ∧
      tsupport χ ⊆ U := by
  obtain ⟨χ, hχ, hrange, hK_int, hcomp, hsupp⟩ := hK.exists_contDiff_cutoff hU hKU
  refine ⟨χ, hχ, fun y ↦ hrange (Set.mem_range_self y),
    ⟨interior (χ ⁻¹' {1}), isOpen_interior, hK_int, fun y hy ↦ interior_subset hy⟩,
    hcomp, hsupp⟩

/-! ## 4. Primitive L1: Autonomous Compact-Set Rigid Translation Hamiltonian -/

/-- `transLinear v` is $C^\infty$ on `EuclideanPlane`. -/
-- tier: T1
theorem contDiff_transLinear (v : EuclideanPlane) :
    ContDiff ℝ ∞ (transLinear v) :=
  (transLinearCLM v).contDiff

/-- Exact Fréchet derivative `transLinearCLM v` of `transLinear v` at every `x : EuclideanPlane`. -/
-- tier: T1
theorem hasFDerivAt_transLinear (v x : EuclideanPlane) :
    HasFDerivAt (transLinear v) (transLinearCLM v) x :=
  (transLinearCLM v).hasFDerivAt

/-- The Hamiltonian vector field of `transLinear v` with respect to `planeAreaForm = dx ∧ dy` is
identically `+v`. -/
-- tier: T2
theorem hamiltonianVectorField_transLinear (v x : EuclideanPlane) :
    TauCeti.SmoothTwoForm.hamiltonianVectorField planeAreaForm (transLinear v) x =
      (v : TangentSpace (𝓡 2) x) :=
  hamiltonianVectorField_planeAreaForm_eq_of_hasFDerivAt
    (hasFDerivAt_transLinear v x) v fun w ↦ by
      simp [transLinear]

/-- **Primitive L1 (Full Isotopy Form)**:
Given `r₀ ∈ (0, 1)`, compact `S ⊆ EuclideanPlane`, displacement `v : EuclideanPlane`, and open
`U ⊆ Metric.ball 0 r₀` containing `translationTube S v`, there exists an autonomous
`P : CompactlySupportedPlanarHamiltonian r₀` whose flow translates every `y ∈ S` along `y + t • v`
for all `t ∈ [0, 1]` and fixes every `y ∉ U` for all `t : ℝ`. -/
-- tier: T2
theorem exists_translation_hamiltonian_isotopy {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    {S : Set EuclideanPlane} (hS : IsCompact S) (v : EuclideanPlane)
    {U : Set EuclideanPlane} (hU : IsOpen U)
    (htube : translationTube S v ⊆ U)
    (hr : U ⊆ Metric.ball (0 : EuclideanPlane) r₀) :
    ∃ P : CompactlySupportedPlanarHamiltonian r₀,
      P.IsAutonomous ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ S, P.toDiskIsotopy.d (t, y) = y + t • v) ∧
      (∀ (t : ℝ) (y : EuclideanPlane), y ∉ U → P.toDiskIsotopy.d (t, y) = y) := by
  obtain ⟨χ, hχ, _, ⟨V, hV_open, htube_V, hχ_one⟩, _, hsupp⟩ :=
    exists_contDiff_cutoff_of_isCompact_subset_isOpen
      (isCompact_translationTube hS v) hU htube
  let h : EuclideanPlane → ℝ := fun y ↦ χ y * transLinear v y
  have hh : ContDiff ℝ ∞ h := hχ.mul (contDiff_transLinear v)
  have hsupp_ball : ∀ y : EuclideanPlane, y ∉ Metric.ball (0 : EuclideanPlane) r₀ → h y = 0 := by
    intro y hy
    have hnot : y ∉ tsupport χ := fun hm ↦ hy (hr (hsupp hm))
    simp [h, image_eq_zero_of_notMem_tsupport hnot]
  let P := CompactlySupportedPlanarHamiltonian.ofAutonomous hr₀ h hh hsupp_ball
  refine ⟨P, ofAutonomous_isAutonomous hr₀ h hh hsupp_ball, ?_, ?_⟩
  · intro t ht y₀ hy₀
    let γ : ℝ → EuclideanPlane := fun u ↦ y₀ + u • v
    have hγ_cont : Continuous γ :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hIcc_sub : Set.Icc (0 : ℝ) 1 ⊆ γ ⁻¹' V := by
      intro u hu
      exact htube_V ⟨y₀, hy₀, u, hu, rfl⟩
    obtain ⟨ε, hε, hIoo⟩ :=
      exists_Ioo_subset_of_isOpen_of_Icc_subset (hV_open.preimage hγ_cont) hIcc_sub
    have hγ_deriv : ∀ u ∈ Set.Ioo (-ε) (1 + ε),
        HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 2) γ u
          ((1 : ℝ →L[ℝ] ℝ).smulRight (P.vectorField u (γ u))) := by
      intro u hu
      have hγV : γ u ∈ V := hIoo hu
      have hev : P.slice u =ᶠ[𝓝 (γ u)] transLinear v := by
        filter_upwards [hV_open.mem_nhds hγV] with z hz
        change χ z * transLinear v z = transLinear v z
        rw [hχ_one z hz, one_mul]
      have hX : P.vectorField u (γ u) = (v : TangentSpace (𝓡 2) (γ u)) :=
        (hev.hamiltonianVectorField_eq planeAreaForm).trans
          (hamiltonianVectorField_transLinear v (γ u))
      rw [hX]
      have hd_smul : HasDerivAt (fun s : ℝ ↦ s • v) v u := by
        simpa only [one_smul] using (hasDerivAt_id' u).smul_const v
      have hd : HasDerivAt γ v u := hd_smul.const_add y₀
      exact hasMFDerivAt_iff_hasFDerivAt.mpr hd.hasFDerivAt
    have hflow := TauCeti.timeDependentFlowOf_eq_of_hasMFDerivAt
      (P.contMDiff_vectorField.of_le (by simp))
      (s := (0 : ℝ)) (t := t) (a := -ε) (b := 1 + ε)
      hγ_deriv
      ⟨by linarith, by linarith⟩
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hγ0 : γ 0 = y₀ := by simp [γ]
    rw [hγ0] at hflow
    simpa only [CompactlySupportedPlanarHamiltonian.toDiskIsotopy_d, γ] using hflow
  · intro t y hyU
    have hy_tsupp : y ∉ tsupport χ := fun hm ↦ hyU (hsupp hm)
    have hopen : (tsupport χ)ᶜ ∈ 𝓝 y :=
      (isClosed_tsupport χ).isOpen_compl.mem_nhds hy_tsupp
    have hX_zero : ∀ u : ℝ, P.vectorField u y = 0 := by
      intro u
      have hev : P.slice u =ᶠ[𝓝 y] fun _ ↦ (0 : ℝ) := by
        filter_upwards [hopen] with z hz
        change χ z * transLinear v z = 0
        rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
      exact TauCeti.SmoothTwoForm.hamiltonianVectorField_eq_zero_of_eventuallyEq hev
    exact TauCeti.timeDependentFlowOf_eq_self_of_forall_eq_zero
      (P.contMDiff_vectorField.of_le (by simp)) hX_zero 0 t

/-- **Primitive L1 (`MISSION_DIRECTIVE_CMPP.md` §4.2 & §10)**:
Given `r₀ ∈ (0, 1)`, compact `S ⊆ EuclideanPlane`, displacement `v : EuclideanPlane`, and open
`U ⊆ Metric.ball 0 r₀` containing `translationTube S v`, there exists an autonomous
`P : CompactlySupportedPlanarHamiltonian r₀` whose time-`1` flow translates `S` rigidly by `+v`
and fixes every point outside `U`. -/
-- tier: T2
theorem exists_translation_hamiltonian {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    {S : Set EuclideanPlane} (hS : IsCompact S) (v : EuclideanPlane)
    {U : Set EuclideanPlane} (hU : IsOpen U)
    (htube : translationTube S v ⊆ U)
    (hr : U ⊆ Metric.ball (0 : EuclideanPlane) r₀) :
    ∃ P : CompactlySupportedPlanarHamiltonian r₀,
      P.IsAutonomous ∧
      (∀ y ∈ S, P.toDiskIsotopy.d (1, y) = y + v) ∧
      (∀ y ∉ U, P.toDiskIsotopy.d (1, y) = y) := by
  obtain ⟨P, hauto, htrans, hfix⟩ :=
    exists_translation_hamiltonian_isotopy hr₀ hS v hU htube hr
  refine ⟨P, hauto, fun y hy ↦ ?_, fun y hy ↦ hfix 1 y hy⟩
  simpa only [one_smul] using htrans 1 ⟨zero_le_one, le_rfl⟩ y hy

/-- `UnitDisk2` `diskTimeOneMap` corollary of `exists_translation_hamiltonian`. -/
-- tier: T1
theorem exists_translation_hamiltonian_diskTimeOneMap {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    {S : Set EuclideanPlane} (hS : IsCompact S) (v : EuclideanPlane)
    {U : Set EuclideanPlane} (hU : IsOpen U)
    (htube : translationTube S v ⊆ U)
    (hr : U ⊆ Metric.ball (0 : EuclideanPlane) r₀) :
    ∃ P : CompactlySupportedPlanarHamiltonian r₀,
      P.IsAutonomous ∧
      (∀ y : UnitDisk2, y.1 ∈ S → (P.toDiskIsotopy.diskTimeOneMap y).1 = y.1 + v) ∧
      (∀ y : UnitDisk2, y.1 ∉ U → P.toDiskIsotopy.diskTimeOneMap y = y) := by
  obtain ⟨P, hauto, htrans, hfix⟩ :=
    exists_translation_hamiltonian hr₀ hS v hU htube hr
  refine ⟨P, hauto, fun y hy ↦ htrans y.1 hy, fun y hy ↦ Subtype.ext (hfix y.1 hy)⟩

/-- General `AxisRect` wrapper for `exists_translation_hamiltonian` using any open neighborhood
`U` of `(R.tubeRect dx dy).toSet` inside `Metric.ball 0 r₀`. -/
-- tier: T1
theorem exists_axisRect_translation_hamiltonian_of_isOpen {r₀ : ℝ}
    (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1) (R : AxisRect) (dx dy : ℝ)
    {U : Set EuclideanPlane} (hU : IsOpen U)
    (htube : (R.tubeRect dx dy).toSet ⊆ U)
    (hr : U ⊆ Metric.ball (0 : EuclideanPlane) r₀) :
    ∃ P : CompactlySupportedPlanarHamiltonian r₀,
      P.IsAutonomous ∧
      (∀ y ∈ R.toSet, P.toDiskIsotopy.d (1, y) = y + WithLp.toLp 2 ![dx, dy]) ∧
      (fun y ↦ P.toDiskIsotopy.d (1, y)) '' R.toSet = (R.translate dx dy).toSet ∧
      (∀ y ∉ U, P.toDiskIsotopy.d (1, y) = y) := by
  obtain ⟨P, hauto, htrans, hfix⟩ :=
    exists_translation_hamiltonian hr₀ R.isCompact_toSet (WithLp.toLp 2 ![dx, dy]) hU
      ((translationTube_axisRect_subset_tubeRect R dx dy).trans htube) hr
  refine ⟨P, hauto, htrans, ?_, hfix⟩
  rw [← R.image_add_toSet dx dy]
  exact Set.image_congr htrans

/-- Convenience `AxisRect` translation wrapper for Milestone A3 using
`(R.tubeRect dx dy).openExpand ε` (`ε > 0`). -/
-- tier: T1
theorem exists_axisRect_translation_hamiltonian {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)
    (R : AxisRect) (dx dy : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hr : (R.tubeRect dx dy).openExpand ε ⊆ Metric.ball (0 : EuclideanPlane) r₀) :
    ∃ P : CompactlySupportedPlanarHamiltonian r₀,
      P.IsAutonomous ∧
      (∀ y ∈ R.toSet, P.toDiskIsotopy.d (1, y) = y + WithLp.toLp 2 ![dx, dy]) ∧
      (fun y ↦ P.toDiskIsotopy.d (1, y)) '' R.toSet = (R.translate dx dy).toSet ∧
      (∀ y ∉ (R.tubeRect dx dy).openExpand ε, P.toDiskIsotopy.d (1, y) = y) :=
  exists_axisRect_translation_hamiltonian_of_isOpen hr₀ R dx dy
    ((R.tubeRect dx dy).isOpen_openExpand ε)
    ((R.tubeRect dx dy).toSet_subset_openExpand hε) hr

/-! ## 5. Primitive L2: Exterior Fixity, Tight Rectangle Stretch & Cantor Workbench Bounds -/

/-- Triangle-inequality inclusion `Metric.ball c r_out ⊆ Metric.ball 0 r₀` when
`‖c‖ + r_out ≤ r₀`. -/
-- tier: T1
theorem ball_subset_ball_zero_of_norm_add_le {c : EuclideanPlane} {r_out r₀ : ℝ}
    (h : ‖c‖ + r_out ≤ r₀) :
    Metric.ball c r_out ⊆ Metric.ball (0 : EuclideanPlane) r₀ := by
  intro y hy
  rw [Metric.mem_ball, dist_zero_right]
  have hyc : ‖y - c‖ < r_out := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
  have htri := norm_le_insert' y c
  linarith

/-- **Exterior Fixity of `bumpedHyperbolicStretchIsotopy`**:
`bumpedHyperbolicStretchIsotopy` fixes every point outside `Metric.ball c r_out` (including the
boundary sphere `‖y - c‖ = r_out`) at all times `t : ℝ`. -/
-- tier: T2
theorem bumpedHyperbolicStretchIsotopy_eq_self_of_notMem_ball {r₀ : ℝ}
    (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1) (c : EuclideanPlane) {r_out : ℝ} (hr_out : 0 < r_out)
    (hsub : Metric.ball c r_out ⊆ Metric.ball (0 : EuclideanPlane) r₀)
    (μ t : ℝ) {y : EuclideanPlane} (hy : y ∉ Metric.ball c r_out) :
    (bumpedHyperbolicStretchIsotopy hr₀ c hr_out hsub μ).d (t, y) = y := by
  let P := bumpedHyperbolicStretchHamiltonian hr₀ c hr_out hsub μ
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
        let χ : ContDiffBump c := ⟨r_out / 2, r_out, by linarith, by linarith⟩
        change χ z * stretchQuad c μ z = 0
        rw [χ.zero_of_le_dist hdist, zero_mul]
      exact TauCeti.SmoothTwoForm.hamiltonianVectorField_eq_zero_of_eventuallyEq hev
    have htend0 : Tendsto (fun n : ℕ ↦ V (ray n)) atTop (𝓝 (0 : EuclideanPlane)) := by
      simpa only [hray_zero] using (tendsto_const_nhds (x := (0 : EuclideanPlane)))
    change V y = (0 : EuclideanPlane)
    exact tendsto_nhds_unique (hV.continuous.continuousAt.tendsto.comp hray_tendsto) htend0
  exact TauCeti.timeDependentFlowOf_eq_self_of_forall_eq_zero
    (P.contMDiff_vectorField.of_le (by simp)) hX_zero 0 t

/-- Monotonicity bound `e^{u α} δ ≤ max δ (e^α δ)` for `u ∈ [0, 1]` and `δ ≥ 0`. -/
-- tier: T1
theorem exp_mul_le_max_of_mem_Icc {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (α : ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) :
    Real.exp (u * α) * δ ≤ max δ (Real.exp α * δ) := by
  rcases le_or_gt 0 α with hα | hα
  · have huα : u * α ≤ α := by nlinarith [hu.2]
    exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr huα) hδ).trans (le_max_right _ _)
  · have huα : u * α ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu.1 hα.le
    have hexp : Real.exp (u * α) ≤ 1 := by simpa using Real.exp_le_exp.mpr huα
    calc
      Real.exp (u * α) * δ ≤ 1 * δ := mul_le_mul_of_nonneg_right hexp hδ
      _ = δ := one_mul δ
      _ ≤ max δ (Real.exp α * δ) := le_max_left _ _

/-- **Primitive L2 (`docs/cmpp/geometry_spec.md` §3.3 — Tight Rectangle Hyperbolic Stretch)**:
For every point `y₀` in the centered rectangle `|y₀₀ - c₀| ≤ δ₀ ∧ |y₀₁ - c₁| ≤ δ₁` satisfying the
tight trajectory-radius bound
`(max δ₀ (e^{-μ} δ₀))² + (max δ₁ (e^μ δ₁))² < (r_out / 2)²`,
`bumpedHyperbolicStretchIsotopy` acts at `t = 1` by exact diagonal scaling
`c + ![e^{-μ}(y₀₀ - c₀), e^μ(y₀₁ - c₁)]`. -/
-- tier: T2
theorem bumpedHyperbolicStretchIsotopy_timeOne_of_mem_rect {r₀ : ℝ}
    (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1) (c : EuclideanPlane) {r_out δ₀ δ₁ : ℝ} (hr_out : 0 < r_out)
    (hsub : Metric.ball c r_out ⊆ Metric.ball (0 : EuclideanPlane) r₀) (μ : ℝ)
    (hδ : (max δ₀ (Real.exp (-μ) * δ₀)) ^ 2 + (max δ₁ (Real.exp μ * δ₁)) ^ 2 <
      (r_out / 2) ^ 2)
    {y₀ : EuclideanPlane}
    (hy₀ : |y₀ 0 - c 0| ≤ δ₀ ∧ |y₀ 1 - c 1| ≤ δ₁) :
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
  have hδ₀_nonneg : 0 ≤ δ₀ := (abs_nonneg _).trans hy₀.1
  have hδ₁_nonneg : 0 ≤ δ₁ := (abs_nonneg _).trans hy₀.2
  have hγ_cont : Continuous γ := by
    have h0 : Continuous fun u : ℝ ↦ Real.exp (-(u * μ)) * v 0 :=
      (Real.continuous_exp.comp (continuous_id.mul continuous_const).neg).mul continuous_const
    have h1 : Continuous fun u : ℝ ↦ Real.exp (u * μ) * v 1 :=
      (Real.continuous_exp.comp (continuous_id.mul continuous_const)).mul continuous_const
    refine continuous_const.add ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦ ?_))
    fin_cases i
    · simpa using h0
    · simpa using h1
  have hIcc_ball : Set.Icc (0 : ℝ) 1 ⊆ γ ⁻¹' Metric.ball c (r_out / 2) := by
    intro u hu
    rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
      EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Real.norm_eq_abs, sq_abs]
    have hv0 : |v 0| ≤ δ₀ := hy₀.1
    have hv1 : |v 1| ≤ δ₁ := hy₀.2
    have hb0 : |Real.exp (-(u * μ)) * v 0| ≤ max δ₀ (Real.exp (-μ) * δ₀) := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      calc
        Real.exp (-(u * μ)) * |v 0| ≤ Real.exp (u * (-μ)) * δ₀ := by
          rw [mul_neg]
          exact mul_le_mul_of_nonneg_left hv0 (Real.exp_nonneg _)
        _ ≤ max δ₀ (Real.exp (-μ) * δ₀) := exp_mul_le_max_of_mem_Icc hu (-μ) hδ₀_nonneg
    have hb1 : |Real.exp (u * μ) * v 1| ≤ max δ₁ (Real.exp μ * δ₁) := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      calc
        Real.exp (u * μ) * |v 1| ≤ Real.exp (u * μ) * δ₁ :=
          mul_le_mul_of_nonneg_left hv1 (Real.exp_nonneg _)
        _ ≤ max δ₁ (Real.exp μ * δ₁) := exp_mul_le_max_of_mem_Icc hu μ hδ₁_nonneg
    have hsq0 : (Real.exp (-(u * μ)) * v 0) ^ 2 ≤ (max δ₀ (Real.exp (-μ) * δ₀)) ^ 2 := by
      rw [← sq_abs (Real.exp (-(u * μ)) * v 0)]
      exact pow_le_pow_left₀ (abs_nonneg _) hb0 2
    have hsq1 : (Real.exp (u * μ) * v 1) ^ 2 ≤ (max δ₁ (Real.exp μ * δ₁)) ^ 2 := by
      rw [← sq_abs (Real.exp (u * μ) * v 1)]
      exact pow_le_pow_left₀ (abs_nonneg _) hb1 2
    have hsum_lt :
        (Real.exp (-(u * μ)) * v 0) ^ 2 + (Real.exp (u * μ) * v 1) ^ 2 < (r_out / 2) ^ 2 :=
      lt_of_le_of_lt (add_le_add hsq0 hsq1) hδ
    have hr2_pos : 0 < r_out / 2 := by linarith
    exact (Real.sqrt_lt' hr2_pos).mpr hsum_lt
  obtain ⟨ε, hε, hIoo⟩ :=
    exists_Ioo_subset_of_isOpen_of_Icc_subset (Metric.isOpen_ball.preimage hγ_cont) hIcc_ball
  have hγ_deriv : ∀ u ∈ Set.Ioo (-ε) (1 + ε),
      HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 2) γ u
        ((1 : ℝ →L[ℝ] ℝ).smulRight (P.vectorField u (γ u))) := by
    intro u hu
    have hγ_mem : γ u ∈ Metric.ball c (r_out / 2) := hIoo hu
    have hev : P.slice u =ᶠ[𝓝 (γ u)] stretchQuad c μ := by
      filter_upwards [χ.eventuallyEq_one_of_mem_ball hγ_mem] with z hz
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
    (s := (0 : ℝ)) (t := (1 : ℝ)) (a := -ε) (b := 1 + ε)
    hγ_deriv ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
  rw [hγ0] at hflow
  simpa only [bumpedHyperbolicStretchIsotopy, CompactlySupportedPlanarHamiltonian.toDiskIsotopy_d,
    γ, v, one_mul, PiLp.sub_apply] using hflow

/-- Centered-`AxisRect` corollary of `bumpedHyperbolicStretchIsotopy_timeOne_of_mem_rect` for any
`R : AxisRect` with `R.center = c`, `R.width / 2 ≤ δ₀`, and `R.height / 2 ≤ δ₁`. -/
-- tier: T1
theorem bumpedHyperbolicStretchIsotopy_timeOne_of_mem_axisRect {r₀ : ℝ}
    (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1) {R : AxisRect} {c : EuclideanPlane} (hc : R.center = c)
    {r_out δ₀ δ₁ : ℝ} (hr_out : 0 < r_out)
    (hsub : Metric.ball c r_out ⊆ Metric.ball (0 : EuclideanPlane) r₀) (μ : ℝ)
    (hw : R.width / 2 ≤ δ₀) (hh : R.height / 2 ≤ δ₁)
    (hδ : (max δ₀ (Real.exp (-μ) * δ₀)) ^ 2 + (max δ₁ (Real.exp μ * δ₁)) ^ 2 <
      (r_out / 2) ^ 2)
    {y₀ : EuclideanPlane} (hy₀ : y₀ ∈ R.toSet) :
    (bumpedHyperbolicStretchIsotopy hr₀ c hr_out hsub μ).d (1, y₀) =
      c + WithLp.toLp 2 ![Real.exp (-μ) * (y₀ 0 - c 0), Real.exp μ * (y₀ 1 - c 1)] := by
  obtain ⟨hx, hy⟩ := R.abs_sub_center_le_half_of_mem hy₀
  rw [hc] at hx hy
  exact bumpedHyperbolicStretchIsotopy_timeOne_of_mem_rect hr₀ c hr_out hsub μ hδ
    ⟨hx.trans hw, hy.trans hh⟩

/-- Centered-`AxisRect.ofCenter` corollary of
`bumpedHyperbolicStretchIsotopy_timeOne_of_mem_rect`. -/
-- tier: T1
theorem bumpedHyperbolicStretchIsotopy_timeOne_of_mem_ofCenter {r₀ : ℝ}
    (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1) (c : EuclideanPlane) {r_out δ₀ δ₁ : ℝ}
    (hδ₀ : 0 ≤ δ₀) (hδ₁ : 0 ≤ δ₁) (hr_out : 0 < r_out)
    (hsub : Metric.ball c r_out ⊆ Metric.ball (0 : EuclideanPlane) r₀) (μ : ℝ)
    (hδ : (max δ₀ (Real.exp (-μ) * δ₀)) ^ 2 + (max δ₁ (Real.exp μ * δ₁)) ^ 2 <
      (r_out / 2) ^ 2)
    {y₀ : EuclideanPlane} (hy₀ : y₀ ∈ (AxisRect.ofCenter c hδ₀ hδ₁).toSet) :
    (bumpedHyperbolicStretchIsotopy hr₀ c hr_out hsub μ).d (1, y₀) =
      c + WithLp.toLp 2 ![Real.exp (-μ) * (y₀ 0 - c 0), Real.exp μ * (y₀ 1 - c 1)] :=
  bumpedHyperbolicStretchIsotopy_timeOne_of_mem_rect hr₀ c hr_out hsub μ hδ
    ((AxisRect.mem_ofCenter_iff c hδ₀ hδ₁ y₀).mp hy₀)

/-- Unconditional Cantor workbench trajectory-radius bound (`docs/cmpp/geometry_spec.md` §3.3):
for every alphabet size `N : ℕ` (`B = cantorBase N ≥ 3`) and shift displacement
`f ∈ {-1, 0, 1}`, half-widths `δ₀ = 1 / (8 B)` and `δ₁ = 1 / (8 B²)` satisfy
`(max δ₀ (B^{-f} δ₀))² + (max δ₁ (B^f δ₁))² < (3 / 20)²`. -/
-- tier: T2
theorem cantorRect_stretch_bound (N : ℕ) {f : ℤ} (hf : f = -1 ∨ f = 0 ∨ f = 1) :
    let B : ℝ := (cantorBase N : ℝ)
    let δ₀ : ℝ := 1 / (8 * B)
    let δ₁ : ℝ := 1 / (8 * B ^ 2)
    (max δ₀ (B ^ (-f) * δ₀)) ^ 2 + (max δ₁ (B ^ f * δ₁)) ^ 2 < (3 / 20 : ℝ) ^ 2 := by
  intro B δ₀ δ₁
  have hB3 : (3 : ℝ) ≤ (cantorBase N : ℝ) := by exact_mod_cast three_le_cantorBase N
  change (3 : ℝ) ≤ B at hB3
  have hB_pos : 0 < B := by linarith
  have hB_ne : B ≠ 0 := hB_pos.ne'
  have hB_ge1 : (1 : ℝ) ≤ B := by linarith
  have hδ₀_pos : 0 < δ₀ := by dsimp [δ₀]; positivity
  have hδ₁_pos : 0 < δ₁ := by dsimp [δ₁]; positivity
  have hδ₀_le : δ₀ ≤ 1 / 24 := by
    dsimp [δ₀]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hB2_ge9 : (9 : ℝ) ≤ B ^ 2 := by nlinarith
  have hδ₁_le : δ₁ ≤ 1 / 72 := by
    dsimp [δ₁]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hB_inv_le : B⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hB_ge1
  rcases hf with rfl | rfl | rfl
  · have h0 : B ^ (-(-1 : ℤ)) * δ₀ = 1 / 8 := by
      simp only [neg_neg, zpow_one, δ₀]
      field_simp [hB_ne]
    have hmax0 : max δ₀ (B ^ (-(-1 : ℤ)) * δ₀) ≤ 1 / 8 := by
      rw [h0]
      exact max_le (by linarith) le_rfl
    have h1 : B ^ (-1 : ℤ) * δ₁ ≤ δ₁ := by
      rw [zpow_neg_one]
      exact mul_le_of_le_one_left hδ₁_pos.le hB_inv_le
    have hmax1 : max δ₁ (B ^ (-1 : ℤ) * δ₁) ≤ 1 / 72 :=
      (max_le le_rfl h1).trans hδ₁_le
    have hsq0 : (max δ₀ (B ^ (-(-1 : ℤ)) * δ₀)) ^ 2 ≤ (1 / 8 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (le_trans hδ₀_pos.le (le_max_left _ _)) hmax0 2
    have hsq1 : (max δ₁ (B ^ (-1 : ℤ) * δ₁)) ^ 2 ≤ (1 / 72 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (le_trans hδ₁_pos.le (le_max_left _ _)) hmax1 2
    linarith
  · simp only [neg_zero, zpow_zero, one_mul, max_self]
    have hsq0 : δ₀ ^ 2 ≤ (1 / 24 : ℝ) ^ 2 := pow_le_pow_left₀ hδ₀_pos.le hδ₀_le 2
    have hsq1 : δ₁ ^ 2 ≤ (1 / 72 : ℝ) ^ 2 := pow_le_pow_left₀ hδ₁_pos.le hδ₁_le 2
    linarith
  · have h0 : B ^ (-1 : ℤ) * δ₀ ≤ δ₀ := by
      rw [zpow_neg_one]
      exact mul_le_of_le_one_left hδ₀_pos.le hB_inv_le
    have hmax0 : max δ₀ (B ^ (-1 : ℤ) * δ₀) ≤ 1 / 24 :=
      (max_le le_rfl h0).trans hδ₀_le
    have h1 : B ^ (1 : ℤ) * δ₁ = δ₀ := by
      simp only [zpow_one, δ₁, δ₀]
      field_simp [hB_ne]
    have hmax1 : max δ₁ (B ^ (1 : ℤ) * δ₁) ≤ 1 / 24 := by
      rw [h1]
      exact max_le (by linarith) hδ₀_le
    have hsq0 : (max δ₀ (B ^ (-1 : ℤ) * δ₀)) ^ 2 ≤ (1 / 24 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (le_trans hδ₀_pos.le (le_max_left _ _)) hmax0 2
    have hsq1 : (max δ₁ (B ^ (1 : ℤ) * δ₁)) ^ 2 ≤ (1 / 24 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (le_trans hδ₁_pos.le (le_max_left _ _)) hmax1 2
    linarith

/-- **Workbench Cantor-Rectangle Hyperbolic Stretch (`docs/cmpp/geometry_spec.md` §3.3)**:
For any `N : ℕ` (`B = cantorBase N`), shift displacement `f ∈ {-1, 0, 1}`, and outer cutoff radius
`r_out ≥ 3 / 10` (in particular the workbench radius `r_out = 3 / 10`),
`bumpedHyperbolicStretchIsotopy` with `μ = f * log B` stretches every point in the centered
`1 / (4 B) × 1 / (4 B²)` Cantor rectangle around `c` by exact `(B^{-f}, B^f)` scaling at `t = 1`. -/
-- tier: T2
theorem bumpedHyperbolicStretchIsotopy_cantorRect_timeOne {r₀ : ℝ}
    (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1) (c : EuclideanPlane) {r_out : ℝ} (hr_out : 0 < r_out)
    (hr_out_ge : 3 / 10 ≤ r_out)
    (hsub : Metric.ball c r_out ⊆ Metric.ball (0 : EuclideanPlane) r₀)
    (N : ℕ) {f : ℤ} (hf : f = -1 ∨ f = 0 ∨ f = 1)
    {y₀ : EuclideanPlane}
    (hy₀ : |y₀ 0 - c 0| ≤ 1 / (8 * (cantorBase N : ℝ)) ∧
      |y₀ 1 - c 1| ≤ 1 / (8 * (cantorBase N : ℝ) ^ 2)) :
    (bumpedHyperbolicStretchIsotopy hr₀ c hr_out hsub
        ((f : ℝ) * Real.log (cantorBase N : ℝ))).d (1, y₀) =
      c + WithLp.toLp 2
        ![(cantorBase N : ℝ) ^ (-f) * (y₀ 0 - c 0),
          (cantorBase N : ℝ) ^ f * (y₀ 1 - c 1)] := by
  have hB_raw : 0 < (cantorBase N : ℝ) := by exact_mod_cast cantorBase_pos N
  let B : ℝ := (cantorBase N : ℝ)
  have hB : 0 < B := hB_raw
  let μ : ℝ := (f : ℝ) * Real.log B
  have hexp_pos : Real.exp μ = B ^ f := by
    dsimp [μ]
    rw [← Real.log_zpow, Real.exp_log (zpow_pos hB f)]
  have hexp_neg : Real.exp (-μ) = B ^ (-f) := by
    have hneg : -μ = ((-f : ℤ) : ℝ) * Real.log B := by simp [μ]
    rw [hneg, ← Real.log_zpow, Real.exp_log (zpow_pos hB (-f))]
  have hbound :
      (max (1 / (8 * B)) (Real.exp (-μ) * (1 / (8 * B)))) ^ 2 +
        (max (1 / (8 * B ^ 2)) (Real.exp μ * (1 / (8 * B ^ 2)))) ^ 2 < (r_out / 2) ^ 2 := by
    rw [hexp_neg, hexp_pos]
    have hlt := cantorRect_stretch_bound N hf
    have hr_sq : (3 / 20 : ℝ) ^ 2 ≤ (r_out / 2) ^ 2 := by
      have hle : (3 / 20 : ℝ) ≤ r_out / 2 := by linarith
      exact pow_le_pow_left₀ (by norm_num) hle 2
    exact lt_of_lt_of_le hlt hr_sq
  have hres := bumpedHyperbolicStretchIsotopy_timeOne_of_mem_rect hr₀ c hr_out hsub μ hbound hy₀
  rwa [hexp_neg, hexp_pos] at hres

/-! ## 6. Gate G5 Anti-Vacuity Sanity Check (L1 & L2) -/

/-- **Gate G5 Anti-Vacuity Witness for Milestone A2**:
1. **L1 (`exists_axisRect_translation_hamiltonian`)**: at `r₀ = 17/20`, translates `quarterSquare`
   rigidly by `(1/10, 1/5)` (`0 ↦ (1/10, 1/5) ≠ 0`, `diskTimeOneMap ≠ id`) while fixing
   `(-1/2, 0)` outside `(quarterSquare.tubeRect (1/10) (1/5)).openExpand (1/20)`.
2. **L2 (`bumpedHyperbolicStretchIsotopy_cantorRect_timeOne`)**: at the canonical workbench
   `c_wb = (0, -7/20)` (`r_out = 3/10`, `r₀ = 17/20`) for `N = 6` (`B = cantorBase 6 = 11`),
   realizes autonomous exact `(11⁻¹, 11)` and `(11, 11⁻¹)` Cantor-rectangle stretches
   (`diskTimeOneMap ≠ id`) while fixing `0 ∉ Metric.ball c_wb (3/10)`. -/
-- tier: T2
theorem cmppPrimitives_sanity :
    let hr₀ : (17 / 20 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    let c_wb : EuclideanPlane := WithLp.toLp 2 ![0, -7 / 20]
    (∃ P₁ : CompactlySupportedPlanarHamiltonian (17 / 20),
      P₁.IsAutonomous ∧
      P₁.toDiskIsotopy.d (1, 0) = WithLp.toLp 2 ![1 / 10, 1 / 5] ∧
      P₁.toDiskIsotopy.d (1, WithLp.toLp 2 ![-1 / 2, 0]) = WithLp.toLp 2 ![-1 / 2, 0] ∧
      P₁.toDiskIsotopy.diskTimeOneMap ≠ id) ∧
    (∃ hsub : Metric.ball c_wb (3 / 10) ⊆ Metric.ball (0 : EuclideanPlane) (17 / 20),
      let hr_out : (0 : ℝ) < 3 / 10 := by norm_num
      let p_wb : EuclideanPlane := c_wb + WithLp.toLp 2 ![1 / 88, 1 / 968]
      (bumpedHyperbolicStretchHamiltonian hr₀ c_wb hr_out hsub
        (Real.log (cantorBase 6 : ℝ))).IsAutonomous ∧
      (bumpedHyperbolicStretchIsotopy hr₀ c_wb hr_out hsub
        (((1 : ℤ) : ℝ) * Real.log (cantorBase 6 : ℝ))).d (1, p_wb) =
        c_wb + WithLp.toLp 2 ![1 / 968, 1 / 88] ∧
      (bumpedHyperbolicStretchIsotopy hr₀ c_wb hr_out hsub
        (((-1 : ℤ) : ℝ) * Real.log (cantorBase 6 : ℝ))).d (1, p_wb) =
        c_wb + WithLp.toLp 2 ![1 / 8, 1 / 10648] ∧
      (bumpedHyperbolicStretchIsotopy hr₀ c_wb hr_out hsub
        (((1 : ℤ) : ℝ) * Real.log (cantorBase 6 : ℝ))).d (1, 0) = 0 ∧
      (bumpedHyperbolicStretchIsotopy hr₀ c_wb hr_out hsub
        (((1 : ℤ) : ℝ) * Real.log (cantorBase 6 : ℝ))).diskTimeOneMap ≠ id) := by
  intro hr₀ c_wb
  constructor
  · have hopen_ball :
        (quarterSquare.tubeRect (1 / 10) (1 / 5)).openExpand (1 / 20) ⊆
          Metric.ball (0 : EuclideanPlane) (17 / 20) := by
      intro p hp
      rw [AxisRect.mem_openExpand_iff, AxisRect.tubeRect_xMin, AxisRect.tubeRect_xMax,
        AxisRect.tubeRect_yMin, AxisRect.tubeRect_yMax, quarterSquare_xMin, quarterSquare_xMax,
        quarterSquare_yMin, quarterSquare_yMax] at hp
      rw [Metric.mem_ball, dist_zero_right, EuclideanSpace.norm_eq, Fin.sum_univ_two]
      simp only [Real.norm_eq_abs, sq_abs]
      have hx_lo : (-1 / 20 : ℝ) < p 0 := by
        have hmin : min (0 : ℝ) (0 + 1 / 10) = 0 := by norm_num
        linarith [hp.1.1]
      have hx_hi : p 0 < 2 / 5 := by
        have hmax : max (1 / 4 : ℝ) (1 / 4 + 1 / 10) = 7 / 20 := by norm_num
        linarith [hp.1.2]
      have hy_lo : (-1 / 20 : ℝ) < p 1 := by
        have hmin : min (0 : ℝ) (0 + 1 / 5) = 0 := by norm_num
        linarith [hp.2.1]
      have hy_hi : p 1 < 1 / 2 := by
        have hmax : max (1 / 4 : ℝ) (1 / 4 + 1 / 5) = 9 / 20 := by norm_num
        linarith [hp.2.2]
      refine (Real.sqrt_lt' (by norm_num)).mpr ?_
      nlinarith
    obtain ⟨P₁, hauto, htrans, _, hfix⟩ :=
      exists_axisRect_translation_hamiltonian hr₀ quarterSquare (1 / 10) (1 / 5)
        (ε := 1 / 20) (by norm_num) hopen_ball
    have h0_mem : (0 : EuclideanPlane) ∈ quarterSquare.toSet := by
      rw [AxisRect.mem_toSet_iff, quarterSquare_xMin, quarterSquare_xMax, quarterSquare_yMin,
        quarterSquare_yMax]
      norm_num
    have hd0 : P₁.toDiskIsotopy.d (1, 0) = WithLp.toLp 2 ![1 / 10, 1 / 5] := by
      simpa using htrans 0 h0_mem
    have hnot_out :
        (WithLp.toLp 2 ![-1 / 2, 0] : EuclideanPlane) ∉
          (quarterSquare.tubeRect (1 / 10) (1 / 5)).openExpand (1 / 20) := by
      rw [AxisRect.mem_openExpand_iff, AxisRect.tubeRect_xMin, quarterSquare_xMin]
      intro h
      have hmin : min (0 : ℝ) (0 + 1 / 10) = 0 := by norm_num
      have hx0 : (WithLp.toLp 2 ![-1 / 2, 0] : EuclideanPlane) 0 = -1 / 2 := rfl
      linarith [h.1.1]
    refine ⟨P₁, hauto, hd0, hfix _ hnot_out, ?_⟩
    intro hid
    have h0_disk : (0 : EuclideanPlane) ∈ UnitDisk2 := by
      rw [UnitDisk2, Metric.mem_ball, dist_self]
      norm_num
    have heq := congrArg (fun p : UnitDisk2 ↦ p.1 0) (congrFun hid ⟨0, h0_disk⟩)
    change P₁.toDiskIsotopy.d (1, 0) 0 = (0 : EuclideanPlane) 0 at heq
    rw [hd0] at heq
    norm_num at heq
  · have hc_norm : ‖c_wb‖ = 7 / 20 := by
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
      simp only [c_wb, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Real.norm_eq_abs, sq_abs]
      rw [show (0 : ℝ) ^ 2 + (-7 / 20) ^ 2 = (7 / 20) ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    have hsub : Metric.ball c_wb (3 / 10) ⊆ Metric.ball (0 : EuclideanPlane) (17 / 20) :=
      ball_subset_ball_zero_of_norm_add_le (by rw [hc_norm]; norm_num)
    refine ⟨hsub, ?_⟩
    intro hr_out p_wb
    have hB6 : (cantorBase 6 : ℝ) = 11 := by
      have : cantorBase 6 = 11 := by decide
      exact_mod_cast this
    have hp_mem :
        |p_wb 0 - c_wb 0| ≤ 1 / (8 * (cantorBase 6 : ℝ)) ∧
          |p_wb 1 - c_wb 1| ≤ 1 / (8 * (cantorBase 6 : ℝ) ^ 2) := by
      rw [hB6]
      simp [p_wb]
      norm_num
    have hp_pos := bumpedHyperbolicStretchIsotopy_cantorRect_timeOne hr₀ c_wb hr_out le_rfl hsub 6
      (f := 1) (Or.inr (Or.inr rfl)) hp_mem
    have hp_neg := bumpedHyperbolicStretchIsotopy_cantorRect_timeOne hr₀ c_wb hr_out le_rfl hsub 6
      (f := -1) (Or.inl rfl) hp_mem
    have hp_pos' :
        (bumpedHyperbolicStretchIsotopy hr₀ c_wb hr_out hsub
          (((1 : ℤ) : ℝ) * Real.log (cantorBase 6 : ℝ))).d (1, p_wb) =
          c_wb + WithLp.toLp 2 ![1 / 968, 1 / 88] := by
      rw [hp_pos, hB6]
      congr 1
      ext i
      fin_cases i <;> simp [p_wb] <;> norm_num
    have hp_neg' :
        (bumpedHyperbolicStretchIsotopy hr₀ c_wb hr_out hsub
          (((-1 : ℤ) : ℝ) * Real.log (cantorBase 6 : ℝ))).d (1, p_wb) =
          c_wb + WithLp.toLp 2 ![1 / 8, 1 / 10648] := by
      rw [hp_neg, hB6]
      congr 1
      ext i
      fin_cases i <;> simp [p_wb] <;> norm_num
    have h0_not_wb : (0 : EuclideanPlane) ∉ Metric.ball c_wb (3 / 10) := by
      rw [Metric.mem_ball, dist_zero_left, hc_norm]
      norm_num
    have h0_fix := bumpedHyperbolicStretchIsotopy_eq_self_of_notMem_ball hr₀ c_wb hr_out hsub
      (((1 : ℤ) : ℝ) * Real.log (cantorBase 6 : ℝ)) 1 h0_not_wb
    refine ⟨bumpedHyperbolicStretchHamiltonian_isAutonomous hr₀ c_wb hr_out hsub _,
      hp_pos', hp_neg', h0_fix, ?_⟩
    intro hid
    have hp_ball : p_wb ∈ Metric.ball c_wb (3 / 10) := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, EuclideanSpace.norm_eq,
        Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Real.norm_eq_abs, sq_abs]
      refine (Real.sqrt_lt' (by norm_num)).mpr ?_
      norm_num
    have hp_disk : p_wb ∈ UnitDisk2 :=
      Metric.ball_subset_ball hr₀.2.le (hsub hp_ball)
    have heq := congrArg (fun p : UnitDisk2 ↦ p.1 0) (congrFun hid ⟨p_wb, hp_disk⟩)
    change (bumpedHyperbolicStretchIsotopy hr₀ c_wb hr_out hsub
      (((1 : ℤ) : ℝ) * Real.log (cantorBase 6 : ℝ))).d (1, p_wb) 0 = p_wb 0 at heq
    rw [hp_pos'] at heq
    simp [p_wb, c_wb] at heq

end S4TuringPoisson.CMPP
