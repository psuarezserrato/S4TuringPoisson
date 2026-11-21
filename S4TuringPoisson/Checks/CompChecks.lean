/-
Copyright (c) 2026 Pablo Suárez-Serrato. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Suárez-Serrato
-/
module

public import S4TuringPoisson.Dynamics.GeneralizedShift
public import S4TuringPoisson.Dynamics.UndecidabilityAndTransfer
public import S4TuringPoisson.Interfaces
public import S4TuringPoisson.Main
public import S4TuringPoisson.Smoothing.DiskSmoothing

/-!
# Adversarial Computability & Anti-Vacuity Checks (`MISSION_DIRECTIVE.md` §6 Gate 6)

This module belongs exclusively to `@verifier-comp` and verifies Milestone M0's computability and
disk-isotopy contracts (`S4TuringPoisson/Interfaces.lean`, Sections 3–4) against Section 6 Gate 6
and the anti-vacuity invariants:

1. **Concrete 2-State `FinTM0` Witnesses (`M_halt` and `M_loop`)**:
   - `M_halt` (`Γ = Bool`, `Λ = Bool`, `|Λ| = 2`) executes three genuine state/head transitions
     (`write true`, `move right`, `write true`) from the blank tape before halting with output
     window `[-1, 0, 1] ↦ [true, true, false]`.
   - `M_loop` (`Γ = Bool`, `Λ = Bool`, `|Λ| = 2`) oscillates forever between its two states and
     never halts on any input tape `t` or target window `(k, w)`.

2. **Decoupled Anti-Vacuity & Orbit Separation**:
   - Every `W : TuringCompleteWitness φ` produces nonempty open targets `U_halt` and `U_loop`
     (even though `M_loop` never halts), separates `p_halt ∉ U_halt` at `n = 0`, drives the forward
     orbit of `p_halt` into `U_halt` at some `n ≥ 1`, keeps the entire forward orbit of `p_loop`
     disjoint from `U_loop`, furnishes computable `2⁻ᵐ` rational chart approximations in
     `UnitDisk2`, and forces `φ ≠ id`.

3. **Disk Isotopy & Foliation-Tangency Gate 6 Instantiations**:
   - Specializes halting separation and non-identity to `diskTimeOneMap` and `sliceDiffeomorph 1`
     under `[HasTuringCompleteAreaPreservingDiskIsotopy]`, and provides the reusable
     foliation-tangency transfer check `gate6_foliation_and_halting_separation` (`f ∘ d̄ = f`,
     `∀ n x, f (d̄^[n] x) = f x`, halting/looping orbit separation, and `d̄ ≠ id`).
-/

@[expose] public section

open Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace S4TuringPoisson.Checks

/-! ## 1. Concrete 2-State `FinTM0` Halting and Looping Machines -/

/-- Concrete 2-state, 2-symbol `FinTM0` machine `M_halt` (`Γ = Bool`, `Λ = Bool`).
Starting on the blank tape `default` in state `false`, `M_halt`:
1. writes `true` at cell `0` and stays in state `false`,
2. reads `true`, moves right to cell `1`, and enters state `true`,
3. writes `true` at the new head cell and stays in state `true`,
4. reads `true` in state `true` and halts (`none`). -/
def M_halt : FinTM0 where
  Γ := Bool
  Λ := Bool
  machine q a :=
    match q, a with
    | false, false => some (false, Turing.TM0.Stmt.write true)
    | false, true => some (true, Turing.TM0.Stmt.move Turing.Dir.right)
    | true, false => some (true, Turing.TM0.Stmt.write true)
    | true, true => none

/-- `M_halt` has exactly `2` internal states. -/
theorem card_state_M_halt : Fintype.card M_halt.Λ = 2 := by
  decide

/-- `M_halt` has a `2`-symbol tape alphabet. -/
theorem card_alphabet_M_halt : Fintype.card M_halt.Γ = 2 := by
  decide

/-- Target window of radius `k = 1` (`{-1, 0, 1}`) matching `M_halt`'s terminal tape
`[-1 ↦ true, 0 ↦ true, 1 ↦ false]`. -/
def w_halt : Window M_halt 1 :=
  fun i ↦ decide (i.1 ≤ 0)

/-- `M_halt` does not halt at step `0` on the blank tape `default`. -/
theorem step_initCfg_M_halt_ne_none :
    Turing.TM0.step M_halt.machine (M_halt.initCfg default) ≠ none := by
  intro h
  cases h

/-- Terminal configuration reached by `M_halt` after `3` transitions from the blank tape. -/
def terminalCfg_M_halt : Turing.TM0.Cfg M_halt.Γ M_halt.Λ :=
  { q := true
    Tape :=
      { head := true
        left := Turing.ListBlank.mk [true]
        right := Turing.ListBlank.mk [] } }

/-- `M_halt` reaches `terminalCfg_M_halt` in `3` steps from the blank tape and halts with output
window `w_halt` on `[-1, 1]`. -/
theorem haltsWithWindow_M_halt : HaltsWithWindow M_halt default 1 w_halt := by
  rw [haltsWithWindow_iff_exists_steps]
  refine ⟨3, terminalCfg_M_halt, rfl, rfl, ?_⟩
  rintro ⟨i, hi⟩
  have hcases : i = -1 ∨ i = 0 ∨ i = 1 := by
    have h1 : -1 ≤ i := by simpa using hi.1
    have h2 : i ≤ 1 := by simpa using hi.2
    omega
  rcases hcases with rfl | rfl | rfl <;> rfl

/-- Concrete 2-state, 2-symbol `FinTM0` machine `M_loop` (`Γ = Bool`, `Λ = Bool`) that alternates
between moving right in state `false` and moving left in state `true`, never halting. -/
def M_loop : FinTM0 where
  Γ := Bool
  Λ := Bool
  machine q _ :=
    match q with
    | false => some (true, Turing.TM0.Stmt.move Turing.Dir.right)
    | true => some (false, Turing.TM0.Stmt.move Turing.Dir.left)

/-- `M_loop` has exactly `2` internal states. -/
theorem card_state_M_loop : Fintype.card M_loop.Λ = 2 := by
  decide

/-- `M_loop` has a `2`-symbol tape alphabet. -/
theorem card_alphabet_M_loop : Fintype.card M_loop.Γ = 2 := by
  decide

/-- Target window of radius `k = 1` on `M_loop` used for Gate 6 orbit non-reachability. -/
def w_loop : Window M_loop 1 :=
  fun _ ↦ false

/-- Every configuration of `M_loop` has a successor (`step ≠ none`). -/
theorem step_M_loop_ne_none (c : Turing.TM0.Cfg M_loop.Γ M_loop.Λ) :
    Turing.TM0.step M_loop.machine c ≠ none := by
  rcases c with ⟨_ | _, _⟩ <;> simp [M_loop, Turing.TM0.step]

/-- `M_loop` never halts on any input tape `t` or target window `(k, w)`. -/
theorem not_haltsWithWindow_M_loop (t : FinSupportedTape M_loop) (k : ℕ)
    (w : Window M_loop k) : ¬ HaltsWithWindow M_loop t k w := by
  rintro ⟨c, _, hterm, _⟩
  exact step_M_loop_ne_none c hterm

/-- Specialization of `not_haltsWithWindow_M_loop` to the blank tape and `w_loop`. -/
theorem not_haltsWithWindow_M_loop_default : ¬ HaltsWithWindow M_loop default 1 w_loop :=
  not_haltsWithWindow_M_loop default 1 w_loop

/-- The blank tape `default` is represented constructively as `Turing.Tape.mk₂ [] []`. -/
theorem tape_mk₂_nil_nil_eq_default {Γ : Type*} [Inhabited Γ] :
    (Turing.Tape.mk₂ [] [] : Turing.Tape Γ) = default :=
  rfl

/-! ## 2. Gate 6 Separation & Anti-Vacuity Verification on `TuringCompleteWitness` -/

section WitnessAudit

variable {X : Type*} [TopologicalSpace X] {φ : X → X}

/-- Encoded initial point `p_halt` for `M_halt` on the blank tape. -/
def p_halt (W : TuringCompleteWitness φ) : X :=
  W.encodePoint M_halt default

/-- Encoded target open set `U_halt` for `(M_halt, 1, w_halt)`. -/
def U_halt (W : TuringCompleteWitness φ) : Opens X :=
  W.encodeOpen M_halt 1 w_halt

/-- Encoded initial point `p_loop` for `M_loop` on the blank tape. -/
def p_loop (W : TuringCompleteWitness φ) : X :=
  W.encodePoint M_loop default

/-- Encoded target open set `U_loop` for `(M_loop, 1, w_loop)`. -/
def U_loop (W : TuringCompleteWitness φ) : Opens X :=
  W.encodeOpen M_loop 1 w_loop

/-- `U_halt` is nonempty. -/
theorem U_halt_nonempty (W : TuringCompleteWitness φ) : (U_halt W).1.Nonempty :=
  W.encodeOpen_nonempty M_halt 1 w_halt

/-- Anti-vacuity check: `U_loop` is nonempty even though `M_loop` never halts on any tape. -/
theorem U_loop_nonempty (W : TuringCompleteWitness φ) : (U_loop W).1.Nonempty :=
  W.encodeOpen_nonempty M_loop 1 w_loop

/-- `p_halt` lies outside `U_halt` at `n = 0` because `M_halt`'s initial configuration is
non-terminal. -/
theorem p_halt_notMem_U_halt (W : TuringCompleteWitness φ) : p_halt W ∉ U_halt W :=
  W.notMem_encodeOpen_of_step_ne_none M_halt default 1 w_halt step_initCfg_M_halt_ne_none

/-- The forward orbit of `p_halt` enters `U_halt` at a strictly positive iterate `n > 0`. -/
theorem exists_pos_orbit_mem_U_halt (W : TuringCompleteWitness φ) :
    ∃ n : ℕ, 0 < n ∧ φ^[n] (p_halt W) ∈ U_halt W := by
  obtain ⟨n, hn⟩ := (W.orbit_mem_encodeOpen_iff M_halt default 1 w_halt).mpr haltsWithWindow_M_halt
  rcases n with _ | n
  · exact False.elim (p_halt_notMem_U_halt W hn)
  · exact ⟨n + 1, Nat.succ_pos n, hn⟩

/-- Gate 6 positive orbit witness: `∃ n, φ^[n] (p_halt W) ∈ U_halt W`. -/
theorem exists_orbit_mem_U_halt (W : TuringCompleteWitness φ) :
    ∃ n : ℕ, φ^[n] (p_halt W) ∈ U_halt W := by
  obtain ⟨n, _, hn⟩ := exists_pos_orbit_mem_U_halt W
  exact ⟨n, hn⟩

/-- Gate 6 negative orbit witness: for all `n : ℕ`, `φ^[n] (p_loop W) ∉ U_loop W`. -/
theorem forall_orbit_notMem_U_loop (W : TuringCompleteWitness φ) (n : ℕ) :
    φ^[n] (p_loop W) ∉ U_loop W := by
  intro hmem
  exact not_haltsWithWindow_M_loop_default
    ((W.orbit_mem_encodeOpen_iff M_loop default 1 w_loop).mp ⟨n, hmem⟩)

/-- Computable dyadic rational chart approximations exist for `p_halt`'s disk coordinate
`W.coordPoint M_halt default` (since `default = Turing.Tape.mk₂ [] []`). -/
theorem computable_approx_coordPoint_M_halt (W : TuringCompleteWitness φ) :
    ∃ approx : ℕ → RatFrac × RatFrac,
      Computable approx ∧
      ∀ m : ℕ,
        ‖ratFracPairToEuclidean2 (approx m) - (W.coordPoint M_halt default).1‖ ≤
          (1 / 2 : ℝ) ^ m := by
  obtain ⟨_, approx₀, hcomp, hbound⟩ := W.computable_approx M_halt
  refine ⟨fun m ↦ approx₀ ([], [], m), ?_, ?_⟩
  · exact hcomp.comp ((Computable.const []).pair ((Computable.const []).pair Computable.id))
  · intro m
    simpa [tape_mk₂_nil_nil_eq_default] using hbound [] [] m

/-- Bundled Section 6 Gate 6 halting-separation and non-identity theorem for any Turing complete
self-map `φ : X → X`. -/
theorem gate6_halting_separation_of_isTuringComplete (hφ : IsTuringComplete φ) :
    ∃ (p_h p_l : X) (U_h U_l : Opens X),
      U_h.1.Nonempty ∧
      U_l.1.Nonempty ∧
      p_h ∉ U_h ∧
      (∃ n : ℕ, φ^[n] p_h ∈ U_h) ∧
      (∀ n : ℕ, φ^[n] p_l ∉ U_l) ∧
      φ ≠ id := by
  rcases hφ with ⟨W⟩
  exact ⟨p_halt W, p_loop W, U_halt W, U_loop W,
    U_halt_nonempty W, U_loop_nonempty W, p_halt_notMem_U_halt W,
    exists_orbit_mem_U_halt W, forall_orbit_notMem_U_loop W,
    IsTuringComplete.ne_id ⟨W⟩⟩

/-- Reusable Section 6 Gate 6 verification bundle combining concrete 2-state halting/looping orbit
separation, non-identity `d_bar ≠ id`, and fibration leaf invariance `f ∘ d_bar = f` (plus iterated
fiber preservation `∀ n x, f (d_bar^[n] x) = f x`). -/
theorem gate6_foliation_and_halting_separation {Y : Type*} (f : X → Y) (d_bar : X → X)
    (hf : f ∘ d_bar = f) (hd : IsTuringComplete d_bar) :
    ∃ (p_h p_l : X) (U_h U_l : Opens X),
      U_h.1.Nonempty ∧
      U_l.1.Nonempty ∧
      (∃ n : ℕ, d_bar^[n] p_h ∈ U_h) ∧
      (∀ n : ℕ, d_bar^[n] p_l ∉ U_l) ∧
      f ∘ d_bar = f ∧
      (∀ (n : ℕ) (x : X), f (d_bar^[n] x) = f x) ∧
      d_bar ≠ id := by
  obtain ⟨p_h, p_l, U_h, U_l, hUh, hUl, _, hreach, hloop, hne⟩ :=
    gate6_halting_separation_of_isTuringComplete hd
  refine ⟨p_h, p_l, U_h, U_l, hUh, hUl, hreach, hloop, hf, ?_, hne⟩
  intro n x
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    exact congrFun hf x

end WitnessAudit

/-! ## 3. M0.3 Disk Isotopy Gate 6 Specialization -/

section DiskIsotopyAudit

set_option linter.concreteInstances false

open HasTuringCompleteAreaPreservingDiskIsotopy

/-- Under `[HasTuringCompleteAreaPreservingDiskIsotopy]`, `diskTimeOneMap` satisfies the full
Gate 6 2-state halting/looping orbit separation and `diskTimeOneMap ≠ id`. -/
theorem diskTimeOneMap_gate6_separation [HasTuringCompleteAreaPreservingDiskIsotopy] :
    ∃ (p_h p_l : UnitDisk2) (U_h U_l : Opens UnitDisk2),
      U_h.1.Nonempty ∧
      U_l.1.Nonempty ∧
      p_h ∉ U_h ∧
      (∃ n : ℕ, diskTimeOneMap^[n] p_h ∈ U_h) ∧
      (∀ n : ℕ, diskTimeOneMap^[n] p_l ∉ U_l) ∧
      diskTimeOneMap ≠ id :=
  gate6_halting_separation_of_isTuringComplete isTuringComplete_diskTimeOneMap

/-- `diskTimeOneMap` is never the identity map on `UnitDisk2`. -/
theorem diskTimeOneMap_ne_id [HasTuringCompleteAreaPreservingDiskIsotopy] :
    diskTimeOneMap ≠ id :=
  isTuringComplete_diskTimeOneMap.ne_id

/-- The ambient planar time-`1` diffeomorphism `sliceDiffeomorph 1` is non-trivial (`≠ refl`). -/
theorem sliceDiffeomorph_one_ne_refl [HasTuringCompleteAreaPreservingDiskIsotopy] :
    sliceDiffeomorph 1 ≠ Diffeomorph.refl (𝓡 2) (EuclideanSpace ℝ (Fin 2)) ∞ := by
  intro heq
  apply diskTimeOneMap_ne_id
  funext y
  exact Subtype.ext (DFunLike.congr_fun heq y.1)

end DiskIsotopyAudit

/-! ## 4. Milestone M3.1 Generalized Shift & Square Cantor Audit -/

section M3GeneralizedShiftAudit

/-- `M_halt.toGeneralizedShift` acts on the canonical 3-cell domain `shiftDom3 = {-1, 0, 1}`. -/
theorem shiftDom_M_halt : M_halt.toGeneralizedShift.D = shiftDom3 :=
  rfl

/-- `M_loop.toGeneralizedShift` acts on the canonical 3-cell domain `shiftDom3 = {-1, 0, 1}`. -/
theorem shiftDom_M_loop : M_loop.toGeneralizedShift.D = shiftDom3 :=
  rfl

/-- Concrete verification that `cantorBase` for `M_halt.ShiftAlphabet` (`|A| = 8`) equals
`2 * 8 - 1 = 15`. -/
theorem cantorBase_M_halt_shiftAlphabet :
    cantorBase (Fintype.card M_halt.ShiftAlphabet) = 15 := by
  decide

/-- Concrete 2-state reversible Turing machine flipping its internal state while shifting right. -/
def R_flipRight : ReversibleTM where
  Γ := Bool
  Q := Bool
  stepPerm :=
    { toFun := fun p ↦ (!p.1, p.2)
      invFun := fun p ↦ (!p.1, p.2)
      left_inv := fun ⟨q, a⟩ ↦ by cases q <;> rfl
      right_inv := fun ⟨q, a⟩ ↦ by cases q <;> rfl }
  dirIn _ := ShiftDir.right

/-- `R_flipRight.toGeneralizedShift.eval` is a global bijection on `ℤ → R_flipRight.ShiftAlphabet`
(`CMPP21` Proposition 4.4). -/
theorem bijective_R_flipRight_shift : Function.Bijective R_flipRight.toGeneralizedShift.eval :=
  R_flipRight.bijective_eval

/-- `R_flipRight.toGeneralizedShift.eval` is non-trivial (`≠ id`). -/
theorem R_flipRight_shift_ne_id : R_flipRight.toGeneralizedShift.eval ≠ id := by
  intro heq
  let c₀ : R_flipRight.Cfg := ⟨false, default⟩
  have h0 := congrArg Prod.snd (congrFun (congrFun heq (R_flipRight.encodeCfg c₀)) 0)
  rw [R_flipRight.eval_encodeCfg] at h0
  cases h0

/-- `M_halt`'s initial shift encoding lies outside its halting cylinder at `n = 0`. -/
theorem encodeInit_M_halt_notMem_haltCylinder :
    M_halt.encodeInit default ∉ cylinderIcc 1 (M_halt.haltWindow 1 w_halt) :=
  M_halt.encodeInit_notMem_haltCylinder default 1 w_halt

/-- Positive M3.1 shift-orbit witness: `M_halt.toGeneralizedShift.eval` drives
`M_halt.encodeInit default` into `cylinderIcc 1 (M_halt.haltWindow 1 w_halt)`. -/
theorem exists_shift_orbit_M_halt :
    ∃ n : ℕ, M_halt.toGeneralizedShift.eval^[n] (M_halt.encodeInit default) ∈
      cylinderIcc 1 (M_halt.haltWindow 1 w_halt) :=
  (M_halt.orbit_mem_haltCylinder_iff_haltsWithWindow default 1 w_halt).mpr haltsWithWindow_M_halt

/-- Negative M3.1 shift-orbit witness: `M_loop.toGeneralizedShift.eval` never enters
`cylinderIcc 1 (M_loop.haltWindow 1 w_loop)` for any iterate `n : ℕ`. -/
theorem forall_shift_orbit_notMem_M_loop (n : ℕ) :
    M_loop.toGeneralizedShift.eval^[n] (M_loop.encodeInit default) ∉
      cylinderIcc 1 (M_loop.haltWindow 1 w_loop) := by
  intro hmem
  exact not_haltsWithWindow_M_loop_default
    ((M_loop.orbit_mem_haltCylinder_iff_haltsWithWindow default 1 w_loop).mp ⟨n, hmem⟩)

/-- Canonical `Fin` numbering of `M_halt.ShiftAlphabet`. -/
noncomputable def encS_M_halt :
    M_halt.ShiftAlphabet ≃ Fin (Fintype.card M_halt.ShiftAlphabet) :=
  shiftAlphabetEquivFin M_halt (Fintype.equivFin _) (Fintype.equivFin _)

/-- Canonical `Fin` numbering of `M_loop.ShiftAlphabet`. -/
noncomputable def encS_M_loop :
    M_loop.ShiftAlphabet ≃ Fin (Fintype.card M_loop.ShiftAlphabet) :=
  shiftAlphabetEquivFin M_loop (Fintype.equivFin _) (Fintype.equivFin _)

/-- Non-vacuity of the open Cantor rectangle for `M_loop`'s target window in `UnitDisk2`. -/
theorem cantorRect_M_loop_nonempty :
    (cantorCylinderRect encS_M_loop 1 (M_loop.haltWindow 1 w_loop) : Set UnitDisk2).Nonempty :=
  cantorCylinderRect_nonempty encS_M_loop 1 (M_loop.haltWindow 1 w_loop)

/-- Square Cantor embedding orbit separation in `UnitDisk2` for `M_halt` vs. `M_loop`. -/
theorem cantorDisk_shift_orbit_separation :
    (∃ n : ℕ,
      cantorDiskEmbed encS_M_halt
        (M_halt.toGeneralizedShift.eval^[n] (M_halt.encodeInit default)) ∈
      cantorCylinderRect encS_M_halt 1 (M_halt.haltWindow 1 w_halt)) ∧
    (∀ n : ℕ,
      cantorDiskEmbed encS_M_loop
        (M_loop.toGeneralizedShift.eval^[n] (M_loop.encodeInit default)) ∉
      cantorCylinderRect encS_M_loop 1 (M_loop.haltWindow 1 w_loop)) := by
  refine ⟨?_, fun n ↦ ?_⟩
  · obtain ⟨n, hn⟩ := exists_shift_orbit_M_halt
    exact ⟨n, (cantorDiskEmbed_mem_cantorCylinderRect_iff _ _ _ _).mpr hn⟩
  · rw [cantorDiskEmbed_mem_cantorCylinderRect_iff]
    exact forall_shift_orbit_notMem_M_loop n

end M3GeneralizedShiftAudit

/-! ## 5. Milestone M3.2 Universal Halting, Undecidability & 4D Fiber Transfer Audit -/

section M3UndecidabilityAndTransferAudit

/-- Concrete halting test on `universalHaltingTM0`: `Nat.Partrec.Code.zero` terminates with the
universal target window. -/
theorem haltsWithWindow_universalHaltingTM0_zero :
    HaltsWithWindow universalHaltingTM0 (universalInputTape Nat.Partrec.Code.zero) 0
      universalTargetWindow := by
  rw [haltsWithWindow_universalHaltingTM0_iff]
  exact Part.some_dom 0

/-- Concrete diverging partial recursive code `rfind' (const 1)` whose evaluation at `0` is
`Part.none`. -/
def divergingPartrecCode : Nat.Partrec.Code :=
  Nat.Partrec.Code.rfind' (Nat.Partrec.Code.const 1)

/-- Concrete non-halting test on `universalHaltingTM0`: `divergingPartrecCode` never halts on
`universalHaltingTM0`. -/
theorem not_haltsWithWindow_universalHaltingTM0_diverging :
    ¬ HaltsWithWindow universalHaltingTM0 (universalInputTape divergingPartrecCode) 0
      universalTargetWindow := by
  rw [haltsWithWindow_universalHaltingTM0_iff]
  dsimp only [divergingPartrecCode, Nat.Partrec.Code.eval, Nat.unpaired]
  simp only [Nat.Partrec.Code.eval_const, Part.map_eq_map, Part.map_some]
  intro hdom
  have hrf : (Nat.rfind fun _ : ℕ ↦ Part.some false).Dom := hdom
  obtain ⟨n, hn⟩ := Part.dom_iff_mem.mp hrf
  obtain ⟨ht, _⟩ := Nat.mem_rfind.mp hn
  simp at ht

/-- Model 4D product open embedding `ℝ² × UnitDisk2 ↪ ℝ² × ℝ²` representing a trivialized regular
fibration neighborhood `B × D²`. -/
def psiModel4D (p : EuclideanPlane × UnitDisk2) : EuclideanPlane × EuclideanPlane :=
  (p.1, p.2.1)

/-- `psiModel4D` is a topological open embedding. -/
theorem isOpenEmbedding_psiModel4D : Topology.IsOpenEmbedding psiModel4D :=
  Topology.IsOpenEmbedding.id.prodMap Metric.isOpen_ball.isOpenEmbedding_subtypeVal

set_option linter.concreteInstances false

open HasTuringCompleteAreaPreservingDiskIsotopy

/-- End-to-end M3.2 undecidability check on `diskTimeOneMap` under
`[HasTuringCompleteAreaPreservingDiskIsotopy]`. -/
theorem diskTimeOneMap_undecidable_orbit_reachability
    [HasTuringCompleteAreaPreservingDiskIsotopy] :
    ∃ (U : Opens UnitDisk2) (chart : UnitDisk2 → UnitDisk2)
      (coord : Nat.Partrec.Code → UnitDisk2)
      (approx : Nat.Partrec.Code × ℕ → RatFrac × RatFrac),
      U.1.Nonempty ∧
      Continuous chart ∧
      Function.Injective chart ∧
      Computable approx ∧
      (∀ (c : Nat.Partrec.Code) (m : ℕ),
        ‖ratFracPairToEuclidean2 (approx (c, m)) - (coord c).1‖ ≤ (1 / 2 : ℝ) ^ m) ∧
      (∀ c : Nat.Partrec.Code, chart (coord c) ∉ U) ∧
      REPred (fun c : Nat.Partrec.Code ↦ ∃ n : ℕ, diskTimeOneMap^[n] (chart (coord c)) ∈ U) ∧
      ¬ ComputablePred
        (fun c : Nat.Partrec.Code ↦ ∃ n : ℕ, diskTimeOneMap^[n] (chart (coord c)) ∈ U) ∧
      ¬ ∃ dec : Nat.Partrec.Code → Bool,
          Computable dec ∧
          ∀ c : Nat.Partrec.Code,
            dec c = true ↔ ∃ n : ℕ, diskTimeOneMap^[n] (chart (coord c)) ∈ U :=
  isTuringComplete_diskTimeOneMap.undecidable_orbit_reachability

/-- Model 4D leaf-preserving map `(b, y) ↦ (b, d (1, y))` on `ℝ² × ℝ²`. -/
noncomputable def dBarModel4D [HasTuringCompleteAreaPreservingDiskIsotopy]
    (q : EuclideanPlane × EuclideanPlane) : EuclideanPlane × EuclideanPlane :=
  (q.1, d (1, q.2))

/-- End-to-end M3.2 fiber-to-4-manifold transfer check: `dBarModel4D` is `IsTuringComplete` via
`IsTuringComplete.transfer` over `B₀ = Metric.ball 0 (1 / 2)`. -/
theorem isTuringComplete_dBarModel4D [HasTuringCompleteAreaPreservingDiskIsotopy] :
    IsTuringComplete dBarModel4D :=
  isTuringComplete_diskTimeOneMap.transfer isOpenEmbedding_psiModel4D Metric.isOpen_ball
    (by simp : (0 : EuclideanPlane) ∈ Metric.ball (0 : EuclideanPlane) (1 / 2))
    (fun _ _ _ ↦ rfl)

/-- Full Gate 6 foliation-tangency + halting separation + undecidability check on `dBarModel4D`,
verifying end-to-end M3 usability for M4/M5. -/
theorem dBarModel4D_gate6_and_undecidability [HasTuringCompleteAreaPreservingDiskIsotopy] :
    (∃ (p_h p_l : EuclideanPlane × EuclideanPlane)
        (U_h U_l : Opens (EuclideanPlane × EuclideanPlane)),
      U_h.1.Nonempty ∧
      U_l.1.Nonempty ∧
      (∃ n : ℕ, dBarModel4D^[n] p_h ∈ U_h) ∧
      (∀ n : ℕ, dBarModel4D^[n] p_l ∉ U_l) ∧
      Prod.fst ∘ dBarModel4D = Prod.fst ∧
      (∀ (n : ℕ) (x : EuclideanPlane × EuclideanPlane), (dBarModel4D^[n] x).1 = x.1) ∧
      dBarModel4D ≠ id) ∧
    (∃ (U : Opens (EuclideanPlane × EuclideanPlane))
        (chart : UnitDisk2 → EuclideanPlane × EuclideanPlane)
        (coord : Nat.Partrec.Code → UnitDisk2)
        (approx : Nat.Partrec.Code × ℕ → RatFrac × RatFrac),
      U.1.Nonempty ∧
      Computable approx ∧
      ¬ ComputablePred
        (fun c : Nat.Partrec.Code ↦ ∃ n : ℕ, dBarModel4D^[n] (chart (coord c)) ∈ U)) := by
  refine ⟨gate6_foliation_and_halting_separation Prod.fst dBarModel4D rfl
    isTuringComplete_dBarModel4D, ?_⟩
  obtain ⟨U, chart, coord, approx, hU, _, _, hcomp, _, _, _, hnotcomp, _⟩ :=
    isTuringComplete_dBarModel4D.undecidable_orbit_reachability
  exact ⟨U, chart, coord, approx, hU, hcomp, hnotcomp⟩

end M3UndecidabilityAndTransferAudit

/-! ## 6. Milestone M3.3 `CMPP21` Cantor-Circulation to Gate 6 Bridge Audit -/

section M3DiskSmoothingBridgeAudit

/-- Unconditional M3.3 rational Cantor approximation check on `M_halt`'s initial shift sequence. -/
theorem approxCantorList_M_halt_bound (m : ℕ) :
    let B := cantorBase (Fintype.card M_halt.ShiftAlphabet)
    let s := M_halt.encodeInit default
    let q₀ := approxCantorList B ((List.range (m + 1)).map fun j ↦ (encS_M_halt (negHalf s j)).1)
    let q₁ := approxCantorList B
      ((List.range (m + 1)).map fun j ↦ (encS_M_halt (nonnegHalf s j)).1)
    ‖ratFracPairToEuclidean2 (q₀, q₁) - (cantorDiskEmbed encS_M_halt s).1‖ ≤ (1 / 2 : ℝ) ^ m :=
  norm_approxCantorList_pair_sub_cantorDiskEmbed_le encS_M_halt (M_halt.encodeInit default) m

set_option linter.concreteInstances false

/-- Anti-vacuity check on `HasCMPPCantorCirculationHamiltonians`: the generating list of
`CompactlySupportedPlanarHamiltonian`s can never be empty (`[]`), since an empty list integrates to
`id` on `UnitDisk2`, contradicting `isTuringComplete_cmppDiskIsotopy.ne_id`. -/
theorem cmpp_generators_ne_nil [C : HasCMPPCantorCirculationHamiltonians] :
    C.generators ≠ [] := by
  intro hnil
  apply isTuringComplete_cmppDiskIsotopy.ne_id
  simp [cmppDiskIsotopy, hnil]

/-- Under `[HasCMPPCantorCirculationHamiltonians]`, `cmppDiskIsotopy.diskTimeOneMap` satisfies the
full Gate 6 2-state halting/looping separation and `≠ id`. -/
theorem cmppDiskIsotopy_gate6_separation [HasCMPPCantorCirculationHamiltonians] :
    ∃ (p_h p_l : UnitDisk2) (U_h U_l : Opens UnitDisk2),
      U_h.1.Nonempty ∧
      U_l.1.Nonempty ∧
      p_h ∉ U_h ∧
      (∃ n : ℕ, cmppDiskIsotopy.diskTimeOneMap^[n] p_h ∈ U_h) ∧
      (∀ n : ℕ, cmppDiskIsotopy.diskTimeOneMap^[n] p_l ∉ U_l) ∧
      cmppDiskIsotopy.diskTimeOneMap ≠ id :=
  gate6_halting_separation_of_isTuringComplete isTuringComplete_cmppDiskIsotopy

/-- **Milestone M3.3 End-to-End Bridge Verification**:
Verifies that `instHasTuringCompleteAreaPreservingDiskIsotopyOfCMPP` automatically synthesizes
`HasTuringCompleteAreaPreservingDiskIsotopy` from `[HasCMPPCantorCirculationHamiltonians]` and feeds
directly into Gate 6's `dBarModel4D_gate6_and_undecidability` (leaf preservation, 2-state halting
separation, `dBarModel4D ≠ id`, and `¬ ComputablePred` undecidability). -/
theorem cmpp_dBarModel4D_gate6_and_undecidability [HasCMPPCantorCirculationHamiltonians] :
    (∃ (p_h p_l : EuclideanPlane × EuclideanPlane)
        (U_h U_l : Opens (EuclideanPlane × EuclideanPlane)),
      U_h.1.Nonempty ∧
      U_l.1.Nonempty ∧
      (∃ n : ℕ, dBarModel4D^[n] p_h ∈ U_h) ∧
      (∀ n : ℕ, dBarModel4D^[n] p_l ∉ U_l) ∧
      Prod.fst ∘ dBarModel4D = Prod.fst ∧
      (∀ (n : ℕ) (x : EuclideanPlane × EuclideanPlane), (dBarModel4D^[n] x).1 = x.1) ∧
      dBarModel4D ≠ id) ∧
    (∃ (U : Opens (EuclideanPlane × EuclideanPlane))
        (chart : UnitDisk2 → EuclideanPlane × EuclideanPlane)
        (coord : Nat.Partrec.Code → UnitDisk2)
        (approx : Nat.Partrec.Code × ℕ → RatFrac × RatFrac),
      U.1.Nonempty ∧
      Computable approx ∧
      ¬ ComputablePred
        (fun c : Nat.Partrec.Code ↦ ∃ n : ℕ, dBarModel4D^[n] (chart (coord c)) ∈ U)) :=
  dBarModel4D_gate6_and_undecidability

end M3DiskSmoothingBridgeAudit

/-! ## 7. Final Section 6 Gate 6 Audit Directly on $S^4$ (`S4TuringPoisson.Main`) -/

section FinalGate6Sphere4Audit

set_option linter.concreteInstances false

/-- **Final Section 6 Gate 6 Witness Directly on `Sphere4` (`S⁴`)**:
Extracts `(V, π_f, d_bar)` from `Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_S4`
and applies `gate6_foliation_and_halting_separation` to the concrete 2-state `FinTM0` machines
`M_halt` and `M_loop`, proving simultaneously on `Sphere4`:
- concrete nonempty open targets `U_h, U_l : Opens Sphere4` with strictly positive Borel volume
  `0 < V.μ U_h.1` and `0 < V.μ U_l.1`,
- halting separation: `∃ n, (⇑d_bar)^[n] p_h ∈ U_h` and `∀ n, (⇑d_bar)^[n] p_l ∉ U_l`,
- symplectic-leaf / fibration tangency: `s4Fibration ∘ ⇑d_bar = s4Fibration` and
  `∀ n x, s4Fibration ((⇑d_bar)^[n] x) = s4Fibration x`,
- global unimodularity, Poisson automorphism (`IsPoissonMap`), volume-form pullback invariance
  `d_bar^* V.Ω = V.Ω`, `MeasureTheory.MeasurePreserving ⇑d_bar V.μ V.μ`, and
- non-triviality `(⇑d_bar : Sphere4 → Sphere4) ≠ id`. -/
theorem gate6_sphere4_witness [HasTuringCompleteAreaPreservingDiskIsotopy] :
    ∃ (V : PositiveVolumeForm (𝓡 4) Sphere4)
      (π_f : PoissonStructure (𝓡 4) Sphere4)
      (d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4)
      (p_h p_l : Sphere4)
      (U_h U_l : Opens Sphere4),
      U_h.1.Nonempty ∧
      U_l.1.Nonempty ∧
      0 < V.μ U_h.1 ∧
      0 < V.μ U_l.1 ∧
      (∃ n : ℕ, (⇑d_bar)^[n] p_h ∈ U_h) ∧
      (∀ n : ℕ, (⇑d_bar)^[n] p_l ∉ U_l) ∧
      s4Fibration ∘ ⇑d_bar = s4Fibration ∧
      (∀ (n : ℕ) (x : Sphere4), s4Fibration ((⇑d_bar)^[n] x) = s4Fibration x) ∧
      π_f.IsUnimodularWithVolume V.Ω ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_bar d_bar.contMDiff ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasureTheory.MeasurePreserving ⇑d_bar V.μ V.μ ∧
      (⇑d_bar : Sphere4 → Sphere4) ≠ id := by
  obtain ⟨V, π_f, d_bar, _, hunimod, _, _, _, _, hf_comp, hpoiss, _, hvol, hmp, htc, _⟩ :=
    Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_S4
  obtain ⟨p_h, p_l, U_h, U_l, hUh, hUl, hreach, hloop, hf_eq, hiter_f, hne_id⟩ :=
    gate6_foliation_and_halting_separation s4Fibration (⇑d_bar) hf_comp htc
  exact ⟨V, π_f, d_bar, p_h, p_l, U_h, U_l, hUh, hUl,
    V.measure_pos_of_nonempty U_h hUh,
    V.measure_pos_of_nonempty U_l hUl,
    hreach, hloop, hf_eq, hiter_f, hunimod, hpoiss, hvol, hmp, hne_id⟩

/-- **Final Section 6 Gate 6 Witness on `Sphere4` under `[HasCMPPCantorCirculationHamiltonians]`**:
Applies `gate6_foliation_and_halting_separation` directly to
`Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_S4_of_cmpp`. -/
theorem gate6_sphere4_witness_of_cmpp [HasCMPPCantorCirculationHamiltonians] :
    ∃ (V : PositiveVolumeForm (𝓡 4) Sphere4)
      (π_f : PoissonStructure (𝓡 4) Sphere4)
      (d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4)
      (p_h p_l : Sphere4)
      (U_h U_l : Opens Sphere4),
      U_h.1.Nonempty ∧
      U_l.1.Nonempty ∧
      0 < V.μ U_h.1 ∧
      0 < V.μ U_l.1 ∧
      (∃ n : ℕ, (⇑d_bar)^[n] p_h ∈ U_h) ∧
      (∀ n : ℕ, (⇑d_bar)^[n] p_l ∉ U_l) ∧
      s4Fibration ∘ ⇑d_bar = s4Fibration ∧
      (∀ (n : ℕ) (x : Sphere4), s4Fibration ((⇑d_bar)^[n] x) = s4Fibration x) ∧
      π_f.IsUnimodularWithVolume V.Ω ∧
      SmoothBivector.IsPoissonMap π_f.toSmoothBivector π_f.toSmoothBivector
        d_bar d_bar.contMDiff ∧
      TauCeti.SmoothForm.mpullback d_bar d_bar.contMDiff V.Ω = V.Ω ∧
      MeasureTheory.MeasurePreserving ⇑d_bar V.μ V.μ ∧
      (⇑d_bar : Sphere4 → Sphere4) ≠ id := by
  obtain ⟨V, π_f, d_bar, _, hunimod, _, _, _, _, hf_comp, hpoiss, _, hvol, hmp, htc, _⟩ :=
    Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_S4_of_cmpp
  obtain ⟨p_h, p_l, U_h, U_l, hUh, hUl, hreach, hloop, hf_eq, hiter_f, hne_id⟩ :=
    gate6_foliation_and_halting_separation s4Fibration (⇑d_bar) hf_comp htc
  exact ⟨V, π_f, d_bar, p_h, p_l, U_h, U_l, hUh, hUl,
    V.measure_pos_of_nonempty U_h hUh,
    V.measure_pos_of_nonempty U_l hUl,
    hreach, hloop, hf_eq, hiter_f, hunimod, hpoiss, hvol, hmp, hne_id⟩

/-- Corollary 2 Gate 6 check: instantiates
`Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_fourManifold` (and `_of_cmpp`) on
`Sphere4` via its unconditional `AdmitsWrinkledOrBrokenLefschetzFibration Sphere4` instance and
verifies 2-state halting/looping orbit separation and leaf preservation. -/
theorem gate6_fourManifold_corollary2_on_S4 [HasCMPPCantorCirculationHamiltonians] :
    ∃ (d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4)
      (p_h p_l : Sphere4)
      (U_h U_l : Opens Sphere4),
      U_h.1.Nonempty ∧
      U_l.1.Nonempty ∧
      (∃ n : ℕ, (⇑d_bar)^[n] p_h ∈ U_h) ∧
      (∀ n : ℕ, (⇑d_bar)^[n] p_l ∉ U_l) ∧
      ⇑(AdmitsWrinkledOrBrokenLefschetzFibration.fibration (M := Sphere4)) ∘ ⇑d_bar =
        ⇑(AdmitsWrinkledOrBrokenLefschetzFibration.fibration (M := Sphere4)) ∧
      (⇑d_bar : Sphere4 → Sphere4) ≠ id := by
  obtain ⟨_, _, d_bar, _, _, _, _, _, hf_comp, _, _, _, _, htc, _⟩ :=
    Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_fourManifold_of_cmpp Sphere4
  obtain ⟨p_h, p_l, U_h, U_l, hUh, hUl, hreach, hloop, hf_eq, _, hne_id⟩ :=
    gate6_foliation_and_halting_separation
      (⇑(AdmitsWrinkledOrBrokenLefschetzFibration.fibration (M := Sphere4)))
      (⇑d_bar) hf_comp htc
  exact ⟨d_bar, p_h, p_l, U_h, U_l, hUh, hUl, hreach, hloop, hf_eq, hne_id⟩

end FinalGate6Sphere4Audit

end S4TuringPoisson.Checks
