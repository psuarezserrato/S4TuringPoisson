/-
Copyright (c) 2026 Pablo Suárez-Serrato. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Suárez-Serrato
-/
module

public import S4TuringPoisson.Interfaces

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

end S4TuringPoisson.Checks
