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

public import S4TuringPoisson.Smoothing.CMPP.Relocation

/-!
# Smooth Autonomous Hamiltonian Realization of Generalized Shifts & Deliverable R4 (Milestone A4)

This module formalizes Milestone A4 (`S4TuringPoisson/Smoothing/CMPP/Realize.lean`) of the
`CMPP21` Hamiltonian realization pipeline (`MISSION_DIRECTIVE_CMPP.md` §1, §4.1–§4.2, §7, §8 and
`docs/cmpp/geometry_spec.md` §§1–3), wiring together Milestones A1, A2, and A3:

1. **Affine Block-to-Rectangle Bridge (`namespace S4TuringPoisson.CMPP`)**:
   - Bridges Milestone A1's `blockAffineMap`, `sourceRect`, `imageRect`, and `blockStretchMu`
     (`Digits.lean`) to Milestone A3's `rectAffineMap` (`Relocation.lean`) via
     `eq_rectAffineMap_of_image_eq`, proving `imageRect_width`, `imageRect_height`, and pointwise
     equality `blockAffineMap_eq_rectAffineMap`.
   - Combines `sourceRect_width`, `sourceRect_height`, `exp_blockStretchMu`,
     `exp_neg_blockStretchMu`, and Milestone A2's `cantorRect_stretch_bound` (`Primitives.lean`)
     to establish the canonical workbench trajectory bound `sourceRect_workbench_bound`.

2. **Smooth Autonomous Realization of Injective `shiftDom3` Generalized Shifts**:
   - **`exists_autonomous_hamiltonians_realizing_shift`**: for any finite-alphabet generalized shift
     `Φ : GeneralizedShift A` (`enc : A ≃ Fin N`) on `Φ.D = shiftDom3` with
     `Φ.F w ∈ {-1, 0, 1}` and `Function.Injective Φ.eval`, constructs a finite list `Ps` of
     **autonomous** planar Hamiltonians supported inside `Metric.ball 0 cmppR0` (`cmppR0 = 17 / 20`)
     satisfying `RealizesGeneralizedShiftByHamiltonians enc Φ cmppR0_mem_Ioo Ps`.
   - **`exists_autonomous_hamiltonians_realizing_reversibleTM`**: specializes unconditionally to
     every unidirectional reversible Turing machine `R : ReversibleTM` via `R.bijective_eval`.
   - **Gate G5 Concrete Witness (`biDirToyTM_realized_by_autonomous_hamiltonians`)**: realizes the
     bidirectional 3-shift-direction machine `biDirToyTM` by a non-empty list of autonomous planar
     Hamiltonians with `diskTimeOneMap ≠ id`.

3. **Interim Deliverable R4 (`CONDITIONAL-ON-UniversalReversibleSimulator`)**:
   - **`hasCMPP_of_simulator`**: explicitly parameterized definition (**not** an `instance`, per
     Gate G7) constructing `HasCMPPCantorCirculationHamiltonians` from any
     `S : UniversalReversibleSimulator`, together with autonomy witness
     `hasCMPP_of_simulator_isAutonomous` and `@[simp]` projections `hasCMPP_of_simulator_sim` and
     `hasCMPP_of_simulator_r₀`.
-/

@[expose] public section

open Bundle Filter Function Metric Module Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace S4TuringPoisson.CMPP

/-! ## 1. `restrictToDom3` Helpers & Block-to-`rectAffineMap` Bridge -/

/-- Transporting along `rfl : shiftDom3 = shiftDom3` is the identity on local blocks. -/
-- tier: T0
@[simp]
theorem restrictToDom3_rfl {A : Type*} (w : shiftDom3 → A) :
    restrictToDom3 rfl w = w := by
  rfl

/-- Transporting `restrictDom D s` along `hD : D = shiftDom3` yields `restrictDom shiftDom3 s`. -/
-- tier: T0
@[simp]
theorem restrictToDom3_restrictDom {A : Type*} {D : Finset ℤ} (hD : D = shiftDom3)
    (s : ℤ → A) :
    restrictToDom3 hD (restrictDom D s) = restrictDom shiftDom3 s := by
  subst hD
  ext i
  simp [restrictToDom3, restrictDom]

/-- Explicit digit index `0` of the blank inactive symbol `(false, none)` under `biDirToyEnc`. -/
-- tier: T0
@[simp]
theorem biDirToyEnc_false_none : biDirToyEnc (false, none) = 0 := by
  unfold biDirToyEnc
  simp

/-- Explicit digit index `4` of the active head symbol `(true, some false)` under `biDirToyEnc`. -/
-- tier: T0
@[simp]
theorem biDirToyEnc_true_some_false : biDirToyEnc (true, some false) = 4 := by
  unfold biDirToyEnc
  simp

/-- Transporting local blocks along `hD : D = shiftDom3` via `restrictToDom3 hD` is injective. -/
-- tier: T1
theorem restrictToDom3_injective {A : Type*} {D : Finset ℤ} (hD : D = shiftDom3) :
    Function.Injective (restrictToDom3 (A := A) hD) := by
  subst hD
  intro _ _ h
  exact h

/-- Source rectangles `sourceRect enc (restrictToDom3 hD w)` indexed by `w : D → A`
(`hD : D = shiftDom3`) are pairwise disjoint. -/
-- tier: T1
theorem sourceRect_restrictToDom3_pairwise_disjoint {A : Type*} {N : ℕ} (enc : A ≃ Fin N)
    {D : Finset ℤ} (hD : D = shiftDom3) :
    Pairwise (Disjoint on fun w : D → A ↦ (sourceRect enc (restrictToDom3 hD w)).toSet) :=
  fun _ _ hne ↦ sourceRect_pairwise_disjoint enc ((restrictToDom3_injective hD).ne hne)

/-- Combined scaling and `rectAffineMap` identification for `(sourceRect, imageRect)` derived from
`blockAffineMap_image_sourceRect`, `blockAffineMap_eq_exp_stretch`, and
`eq_rectAffineMap_of_image_eq`. -/
-- tier: T1
theorem imageRect_scaling_and_eq_rectAffineMap {A : Type*} {N : ℕ} (enc : A ≃ Fin N)
    (Φ : GeneralizedShift A) (hD : Φ.D = shiftDom3) (w : Φ.D → A)
    (hf : Φ.F w = -1 ∨ Φ.F w = 0 ∨ Φ.F w = 1) :
    (imageRect enc Φ hD w).width =
      Real.exp (-blockStretchMu enc Φ hD w) *
        (sourceRect enc (restrictToDom3 hD w)).width ∧
    (imageRect enc Φ hD w).height =
      Real.exp (blockStretchMu enc Φ hD w) *
        (sourceRect enc (restrictToDom3 hD w)).height ∧
    ∀ p : EuclideanPlane,
      blockAffineMap enc Φ hD w p =
        rectAffineMap (sourceRect enc (restrictToDom3 hD w)) (imageRect enc Φ hD w)
          (blockStretchMu enc Φ hD w) p := by
  have himg := blockAffineMap_image_sourceRect enc Φ hD w hf
  have hfun :
      blockAffineMap enc Φ hD w = fun p : EuclideanPlane ↦
        WithLp.toLp 2
          ![Real.exp (-blockStretchMu enc Φ hD w) * p 0 + blockOffsetX enc Φ hD w,
            Real.exp (blockStretchMu enc Φ hD w) * p 1 + blockOffsetY enc Φ hD w] :=
    funext (blockAffineMap_eq_exp_stretch enc Φ hD w)
  rw [hfun] at himg
  obtain ⟨hw, hh, hpt⟩ := eq_rectAffineMap_of_image_eq himg
  refine ⟨hw, hh, fun p ↦ ?_⟩
  rw [blockAffineMap_eq_exp_stretch]
  exact hpt p

/-- Width scaling `(imageRect enc Φ hD w).width = exp (-μ_w) * (sourceRect ...).width` for
`Φ.F w ∈ {-1, 0, 1}`. -/
-- tier: T1
theorem imageRect_width {A : Type*} {N : ℕ} (enc : A ≃ Fin N)
    (Φ : GeneralizedShift A) (hD : Φ.D = shiftDom3) (w : Φ.D → A)
    (hf : Φ.F w = -1 ∨ Φ.F w = 0 ∨ Φ.F w = 1) :
    (imageRect enc Φ hD w).width =
      Real.exp (-blockStretchMu enc Φ hD w) *
        (sourceRect enc (restrictToDom3 hD w)).width :=
  (imageRect_scaling_and_eq_rectAffineMap enc Φ hD w hf).1

/-- Height scaling `(imageRect enc Φ hD w).height = exp (μ_w) * (sourceRect ...).height` for
`Φ.F w ∈ {-1, 0, 1}`. -/
-- tier: T1
theorem imageRect_height {A : Type*} {N : ℕ} (enc : A ≃ Fin N)
    (Φ : GeneralizedShift A) (hD : Φ.D = shiftDom3) (w : Φ.D → A)
    (hf : Φ.F w = -1 ∨ Φ.F w = 0 ∨ Φ.F w = 1) :
    (imageRect enc Φ hD w).height =
      Real.exp (blockStretchMu enc Φ hD w) *
        (sourceRect enc (restrictToDom3 hD w)).height :=
  (imageRect_scaling_and_eq_rectAffineMap enc Φ hD w hf).2.1

/-- Pointwise identity identifying Milestone A1's `blockAffineMap` with Milestone A3's
`rectAffineMap` for every `w : Φ.D → A` (`Φ.F w ∈ {-1, 0, 1}`). -/
-- tier: T1
theorem blockAffineMap_eq_rectAffineMap {A : Type*} {N : ℕ} (enc : A ≃ Fin N)
    (Φ : GeneralizedShift A) (hD : Φ.D = shiftDom3) (w : Φ.D → A)
    (hf : Φ.F w = -1 ∨ Φ.F w = 0 ∨ Φ.F w = 1) (p : EuclideanPlane) :
    blockAffineMap enc Φ hD w p =
      rectAffineMap (sourceRect enc (restrictToDom3 hD w)) (imageRect enc Φ hD w)
        (blockStretchMu enc Φ hD w) p :=
  (imageRect_scaling_and_eq_rectAffineMap enc Φ hD w hf).2.2 p

/-- Every `sourceRect` with stretch parameter `blockStretchMu` (`Φ.F w ∈ {-1, 0, 1}`) satisfies the
canonical workbench trajectory-radius bound `< (3 / 20)²` of Relocation Theorem RT. -/
-- tier: T1
theorem sourceRect_workbench_bound {A : Type*} {N : ℕ} (enc : A ≃ Fin N)
    (Φ : GeneralizedShift A) (hD : Φ.D = shiftDom3) (w : Φ.D → A)
    (hf : Φ.F w = -1 ∨ Φ.F w = 0 ∨ Φ.F w = 1) :
    (max ((sourceRect enc (restrictToDom3 hD w)).width / 2)
        (Real.exp (-blockStretchMu enc Φ hD w) *
          ((sourceRect enc (restrictToDom3 hD w)).width / 2))) ^ 2 +
      (max ((sourceRect enc (restrictToDom3 hD w)).height / 2)
        (Real.exp (blockStretchMu enc Φ hD w) *
          ((sourceRect enc (restrictToDom3 hD w)).height / 2))) ^ 2 <
      (3 / 20 : ℝ) ^ 2 := by
  have hw :
      (sourceRect enc (restrictToDom3 hD w)).width / 2 =
        1 / (8 * (cantorBase N : ℝ)) := by
    rw [sourceRect_width]
    ring
  have hh :
      (sourceRect enc (restrictToDom3 hD w)).height / 2 =
        1 / (8 * (cantorBase N : ℝ) ^ 2) := by
    rw [sourceRect_height]
    ring
  rw [hw, hh, exp_neg_blockStretchMu, exp_blockStretchMu]
  exact cantorRect_stretch_bound N hf

/-! ## 2. Autonomous Hamiltonian Realization of Generalized Shifts & `ReversibleTM` -/

/-- **Smooth Autonomous Hamiltonian Realization of Injective `shiftDom3` Generalized Shifts**
(`CMPP21` Proposition 5.1 & Theorem 5.2, `MISSION_DIRECTIVE_CMPP.md` §4.1–§4.2 & §7):
For any finite-alphabet generalized shift `Φ : GeneralizedShift A` (`enc : A ≃ Fin N`) on
`Φ.D = shiftDom3` with local displacements `Φ.F w ∈ {-1, 0, 1}` and injective global shift map
`Function.Injective Φ.eval`, there exists a finite list `Ps` of **autonomous** planar Hamiltonians
supported inside `Metric.ball 0 cmppR0` (`cmppR0 = 17 / 20 ∈ (0, 1)`) realizing `Φ` at `t = 1` on
every sequence `s : ℤ → A` via `cantorDiskEmbed enc`. -/
-- tier: T2
theorem exists_autonomous_hamiltonians_realizing_shift {A : Type*} {N : ℕ}
    (enc : A ≃ Fin N) (Φ : GeneralizedShift A) (hD : Φ.D = shiftDom3)
    (hF : ∀ w : Φ.D → A, Φ.F w = -1 ∨ Φ.F w = 0 ∨ Φ.F w = 1)
    (hinj : Function.Injective Φ.eval) :
    ∃ Ps : List (CompactlySupportedPlanarHamiltonian cmppR0),
      (∀ H ∈ Ps, H.IsAutonomous) ∧
      RealizesGeneralizedShiftByHamiltonians enc Φ cmppR0_mem_Ioo Ps := by
  let _ : Fintype A := Fintype.ofEquiv (Fin N) enc.symm
  let P : (Φ.D → A) → AxisRect := fun w ↦ sourceRect enc (restrictToDom3 hD w)
  let P' : (Φ.D → A) → AxisRect := fun w ↦ imageRect enc Φ hD w
  let μ : (Φ.D → A) → ℝ := fun w ↦ blockStretchMu enc Φ hD w
  obtain ⟨Ps, hauto, hact⟩ :=
    exists_relocation_hamiltonians_diskTimeOneMap P P' μ
      (fun w ↦ sourceRect_subset_quarterSquare enc (restrictToDom3 hD w))
      (fun w ↦ imageRect_subset_quarterSquare enc Φ hD w (hF w))
      (sourceRect_restrictToDom3_pairwise_disjoint enc hD)
      (imageRect_pairwise_disjoint enc Φ hD hF hinj)
      (fun w ↦ imageRect_width enc Φ hD w (hF w))
      (fun w ↦ imageRect_height enc Φ hD w (hF w))
      (fun w ↦ sourceRect_workbench_bound enc Φ hD w (hF w))
  refine ⟨Ps, hauto, fun s ↦ ?_⟩
  let w : Φ.D → A := restrictDom Φ.D s
  have hmem : (cantorDiskEmbed enc s).1 ∈ (P w).toSet :=
    cantorDiskEmbed_mem_sourceRect enc rfl
  apply Subtype.ext
  rw [hact w (cantorDiskEmbed enc s) hmem]
  dsimp only [P, P', μ]
  rw [← blockAffineMap_eq_rectAffineMap enc Φ hD w (hF w) (cantorDiskEmbed enc s).1]
  exact blockAffineMap_cantorDiskEmbed enc Φ hD rfl (hF w)

/-- **Smooth Autonomous Hamiltonian Realization for `ReversibleTM` (`CMPP21` Theorem 5.2)**:
For every unidirectional reversible Turing machine `R : ReversibleTM` and explicit alphabet
numbering `enc : R.ShiftAlphabet ≃ Fin N`, there exists a finite list `Ps` of **autonomous** planar
Hamiltonians supported inside `Metric.ball 0 cmppR0` (`cmppR0 = 17 / 20`) realizing
`R.toGeneralizedShift` on `cantorDiskEmbed enc` at `t = 1`. -/
-- tier: T2
theorem exists_autonomous_hamiltonians_realizing_reversibleTM (R : ReversibleTM) {N : ℕ}
    (enc : R.ShiftAlphabet ≃ Fin N) :
    ∃ Ps : List (CompactlySupportedPlanarHamiltonian cmppR0),
      (∀ H ∈ Ps, H.IsAutonomous) ∧
      RealizesGeneralizedShiftByHamiltonians enc R.toGeneralizedShift cmppR0_mem_Ioo Ps :=
  exists_autonomous_hamiltonians_realizing_shift enc R.toGeneralizedShift
    R.toGeneralizedShift_D (toGeneralizedShift_F_mem R) R.bijective_eval.injective

/-- Non-vacuity helper: if `Ps` realizes a generalized shift `Φ` on `cantorDiskEmbed enc` and `Φ`
moves at least one sequence `Φ.eval s₀ ≠ s₀`, then `Ps ≠ []` and `diskTimeOneMap ≠ id`. -/
-- tier: T1
theorem ne_nil_and_diskTimeOneMap_ne_id_of_realizes {A : Type*} {N : ℕ} (enc : A ≃ Fin N)
    {Φ : GeneralizedShift A} {r₀ : ℝ} {hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1}
    {Ps : List (CompactlySupportedPlanarHamiltonian r₀)}
    (hreal : RealizesGeneralizedShiftByHamiltonians enc Φ hr₀ Ps)
    {s₀ : ℤ → A} (hne : Φ.eval s₀ ≠ s₀) :
    Ps ≠ [] ∧
      (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy hr₀ Ps).diskTimeOneMap ≠ id := by
  have hne_id :
      (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy hr₀ Ps).diskTimeOneMap ≠ id := by
    intro hid
    have heq :
        (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy hr₀ Ps).diskTimeOneMap
          (cantorDiskEmbed enc s₀) = cantorDiskEmbed enc s₀ :=
      congrFun hid (cantorDiskEmbed enc s₀)
    rw [hreal s₀] at heq
    exact hne (cantorDiskEmbed_injective enc heq)
  refine ⟨?_, hne_id⟩
  rintro rfl
  exact hne_id (AreaPreservingDiskIsotopy.refl_diskTimeOneMap hr₀)

/-! ## 3. Gate G5 Concrete Anti-Vacuity Witness (`biDirToyTM`) -/

/-- **Gate G5 Concrete Anti-Vacuity Witness for Milestone A4**:
Realizes `biDirToyTM.toGeneralizedShift` (which exercises all three shift directions
`{-1, 0, +1}`) on `cantorDiskEmbed biDirToyEnc` via a non-empty finite list `Ps` of **autonomous**
planar Hamiltonians supported inside `Metric.ball 0 cmppR0`, moving
`cantorDiskEmbed biDirToyEnc (biDirToyTM.encodeCfg ⟨true, default⟩)` non-trivially to
`cantorDiskEmbed biDirToyEnc (biDirToyTM.encodeCfg (biDirToyTM.step ⟨true, default⟩))` and
witnessing `diskTimeOneMap ≠ id`. -/
-- tier: T2
theorem biDirToyTM_realized_by_autonomous_hamiltonians :
    let c₀ : biDirToyTM.Cfg := { q := true, Tape := default }
    ∃ Ps : List (CompactlySupportedPlanarHamiltonian cmppR0),
      Ps ≠ [] ∧
      (∀ H ∈ Ps, H.IsAutonomous) ∧
      RealizesGeneralizedShiftByHamiltonians biDirToyEnc biDirToyTM.toGeneralizedShift
        cmppR0_mem_Ioo Ps ∧
      (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).diskTimeOneMap
          (cantorDiskEmbed biDirToyEnc (biDirToyTM.encodeCfg c₀)) =
        cantorDiskEmbed biDirToyEnc (biDirToyTM.encodeCfg (biDirToyTM.step c₀)) ∧
      (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).diskTimeOneMap
          (cantorDiskEmbed biDirToyEnc (biDirToyTM.encodeCfg c₀)) ≠
        cantorDiskEmbed biDirToyEnc (biDirToyTM.encodeCfg c₀) ∧
      (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).diskTimeOneMap ≠
        id := by
  intro c₀
  obtain ⟨Ps, hauto, hreal⟩ :=
    exists_autonomous_hamiltonians_realizing_reversibleTM biDirToyTM biDirToyEnc
  have hact_c₀ :
      (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).diskTimeOneMap
          (cantorDiskEmbed biDirToyEnc (biDirToyTM.encodeCfg c₀)) =
        cantorDiskEmbed biDirToyEnc (biDirToyTM.encodeCfg (biDirToyTM.step c₀)) := by
    rw [hreal (biDirToyTM.encodeCfg c₀), biDirToyTM.eval_encodeCfg]
  have hne_eval :
      biDirToyTM.toGeneralizedShift.eval (biDirToyTM.encodeCfg c₀) ≠
        biDirToyTM.encodeCfg c₀ := by
    rw [biDirToyTM.eval_encodeCfg]
    intro heq
    have h0 := congrArg Prod.snd (congrFun heq 0)
    dsimp [c₀, biDirToyTM, ReversibleTM.step, ReversibleTM.encodeCfg] at h0
    cases h0
  have hne_pt :
      (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy cmppR0_mem_Ioo Ps).diskTimeOneMap
          (cantorDiskEmbed biDirToyEnc (biDirToyTM.encodeCfg c₀)) ≠
        cantorDiskEmbed biDirToyEnc (biDirToyTM.encodeCfg c₀) := by
    rw [hreal (biDirToyTM.encodeCfg c₀)]
    exact fun heq ↦ hne_eval (cantorDiskEmbed_injective biDirToyEnc heq)
  obtain ⟨hPs_ne, hne_id⟩ := ne_nil_and_diskTimeOneMap_ne_id_of_realizes biDirToyEnc hreal hne_eval
  exact ⟨Ps, hPs_ne, hauto, hreal, hact_c₀, hne_pt, hne_id⟩

end S4TuringPoisson.CMPP

namespace S4TuringPoisson

/-! ## 4. Interim Deliverable R4 (`CONDITIONAL-ON-UniversalReversibleSimulator`) -/

/-- **Interim Deliverable R4 (`CONDITIONAL-ON-UniversalReversibleSimulator`)**
(`MISSION_DIRECTIVE_CMPP.md` §1, §7, §8 Gate G7):
Constructs `HasCMPPCantorCirculationHamiltonians` conditionally from any explicit
`S : UniversalReversibleSimulator` using autonomous planar Hamiltonians supported inside
`Metric.ball 0 CMPP.cmppR0` (`CMPP.cmppR0 = 17 / 20`).

Declared deliberately as a parameterized `def` (**not** an `instance`) until Milestone B3 + Z
supplies an unconditional `UniversalReversibleSimulator`. -/
@[instance_reducible, nolint defsWithUnderscore]
noncomputable def hasCMPP_of_simulator (S : UniversalReversibleSimulator) :
    HasCMPPCantorCirculationHamiltonians where
  sim := S
  r₀ := CMPP.cmppR0
  r₀_mem_Ioo := CMPP.cmppR0_mem_Ioo
  generators :=
    (CMPP.exists_autonomous_hamiltonians_realizing_reversibleTM S.R S.encShift).choose
  realizes_shift :=
    (CMPP.exists_autonomous_hamiltonians_realizing_reversibleTM S.R S.encShift).choose_spec.2

/-- Autonomy of all planar Hamiltonian generators in `hasCMPP_of_simulator S`
(`CONDITIONAL-ON-UniversalReversibleSimulator`, used by Milestone P / Deliverable R5). -/
-- tier: T1
theorem hasCMPP_of_simulator_isAutonomous (S : UniversalReversibleSimulator) :
    ∀ P ∈ (hasCMPP_of_simulator S).generators, P.IsAutonomous :=
  (CMPP.exists_autonomous_hamiltonians_realizing_reversibleTM S.R S.encShift).choose_spec.1

/-- Underlying `UniversalReversibleSimulator` projection for `hasCMPP_of_simulator S`
(`CONDITIONAL-ON-UniversalReversibleSimulator`). -/
-- tier: T0
@[simp]
theorem hasCMPP_of_simulator_sim (S : UniversalReversibleSimulator) :
    (hasCMPP_of_simulator S).sim = S := by
  rfl

/-- Canonical support radius `CMPP.cmppR0 = 17 / 20` of `hasCMPP_of_simulator S`
(`CONDITIONAL-ON-UniversalReversibleSimulator`). -/
-- tier: T0
@[simp]
theorem hasCMPP_of_simulator_r₀ (S : UniversalReversibleSimulator) :
    (hasCMPP_of_simulator S).r₀ = CMPP.cmppR0 := by
  rfl

end S4TuringPoisson
