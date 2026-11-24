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

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Logic.Equiv.Sum
public import S4TuringPoisson.Dynamics.GeneralizedShift

/-!
# Generic Bennett (1973) Reversibilization of Finite `TM0` Machines (CMPP Milestone B1)

This module formalizes Milestone B1 (`S4TuringPoisson/Dynamics/Reversible/Bennett.lean`) of the
`CMPP21` reversible-computation pipeline (`Bennett 1973`, `CMPP21` Lemma 4.3 & Proposition 4.4,
`MISSION_DIRECTIVE_CMPP.md` §4.4, §7):

1. **Partial-Injection Permutation Extension (`extendPartialInjPerm`)**:
   - Extends any partially defined injective transition rule `f : X → Option X` on a finite
     decidable type `X` to a total permutation `X ≃ X` agreeing with `f` everywhere `f x = some y`,
     using `Finset.card_image_of_injOn`, `Fintype.equivOfCardEq`, and `Equiv.sumCompl`.

2. **Single-Tape 2-Track Bennett Alphabet, Unidirectional States & Partial Transition Rule**:
   - `BennettCell M`: finite 5-field tape alphabet bundling the work-track symbol `sym : M.Γ`,
     work-head marker `workHead : Bool`, optional history record `hist : Option (M.Λ × M.Γ)`,
     history-cursor marker `histHead : Bool`, and post-halt cruise flag `haltMark : Bool`.
   - `BennettState M` and `bennettDirIn`: 13-phase unidirectional control state space where every
     state determines a unique incoming shift direction in `{left, stay, right}`.
   - `bennettRule M` and `bennettRuleInv M`: partially defined transition table and explicit left
     inverse witnessing `bennettRule_partial_injective`, packaged into
     `bennettReversibleTM M : ReversibleTM.{0, 0}`.

3. **Initial Encoding, `BennettInv`, Macro-Step Simulation & Orbit Equivalence**:
   - `bennettInitTape M t` and `bennettInitCfg M t`, with `nth` and `Tape.mk₂` projections for
     Milestone B3 (`UniversalReversibleSimulator`).
   - Walking lemmas (`seekHistLeft`, `seekHistRight`, `seekWorkLeft`, `seekWorkRight`), active
     macro-step `bennett_macroStep`, terminal step `bennett_haltStep`, full-tape halting equivalence
     `bennett_orbit_halted_full`, windowed halting equivalence `bennett_orbit_halted_iff`, and
     infinite non-repeating forward orbits `bennettReversibleTM_iterate_step_initCfg_ne` /
     `bennettReversibleTM_orbit_initCfg_injective` (all **UNCONDITIONAL**).

4. **Gate G5 Concrete Anti-Vacuity Witnesses**:
   - `bennettReversibleTM_eval_bijective`, concrete 4-branch halting witness `bennettToyHalt`, and
     non-halting witness `bennettToyLoop`.
-/

@[expose] public section

open Turing

namespace S4TuringPoisson.Reversible

/-! ## 1. Reusable Partial-Injection Permutation Extension (`extendPartialInjPerm`) -/

section PartialPerm

/-- Extend a partial injection `f : X → Option X` on a finite decidable type `X`
(`∀ x₁ x₂ y, f x₁ = some y → f x₂ = some y → x₁ = x₂`) to a global permutation `X ≃ X` by
pairing the active bijection `S ≃ T` (`S = {x | (f x).isSome}`, `T = S.image _`) with an arbitrary
cardinality-matched bijection `Sᶜ ≃ Tᶜ` via `Equiv.sumCompl`. -/
noncomputable def extendPartialInjPerm {X : Type*} [Fintype X] [DecidableEq X]
    (f : X → Option X)
    (hf : ∀ x₁ x₂ y, f x₁ = some y → f x₂ = some y → x₁ = x₂) : X ≃ X :=
  let g : X → X := fun x ↦ (f x).getD x
  let S : Finset X := Finset.univ.filter fun x ↦ (f x).isSome
  let T : Finset X := S.image g
  have hinj : Set.InjOn g (S : Set X) := by
    intro x₁ hx₁ x₂ hx₂ heq
    have hs₁ : (f x₁).isSome := (Finset.mem_filter.mp hx₁).2
    have hs₂ : (f x₂).isSome := (Finset.mem_filter.mp hx₂).2
    obtain ⟨y₁, hy₁⟩ := Option.isSome_iff_exists.mp hs₁
    obtain ⟨y₂, hy₂⟩ := Option.isSome_iff_exists.mp hs₂
    have hgy₁ : g x₁ = y₁ := by simp [g, hy₁]
    have hgy₂ : g x₂ = y₂ := by simp [g, hy₂]
    have hy : y₁ = y₂ := hgy₁.symm.trans (heq.trans hgy₂)
    subst hy
    exact hf x₁ x₂ y₁ hy₁ hy₂
  have hbij : Function.Bijective
      (fun x : { a // a ∈ S } ↦ (⟨g x.1, Finset.mem_image_of_mem g x.2⟩ : { b // b ∈ T })) := by
    refine ⟨fun x₁ x₂ h ↦ Subtype.ext (hinj x₁.2 x₂.2 (congrArg Subtype.val h)), ?_⟩
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  let eST : { a // a ∈ S } ≃ { b // b ∈ T } := Equiv.ofBijective _ hbij
  have hcardST : T.card = S.card := Finset.card_image_of_injOn hinj
  have hcardCompl : Fintype.card { a // a ∉ S } = Fintype.card { b // b ∉ T } := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, Fintype.card_coe,
      Fintype.card_coe, hcardST]
  let eCompl : { a // a ∉ S } ≃ { b // b ∉ T } := Fintype.equivOfCardEq hcardCompl
  ((Equiv.sumCompl (· ∈ S)).symm.trans (Equiv.sumCongr eST eCompl)).trans
    (Equiv.sumCompl (· ∈ T))

/-- Whenever `f x = some y`, `extendPartialInjPerm f hf` maps `x` to `y`. -/
-- tier: T1
theorem extendPartialInjPerm_eq_of_some {X : Type*} [Fintype X] [DecidableEq X]
    (f : X → Option X)
    (hf : ∀ x₁ x₂ y, f x₁ = some y → f x₂ = some y → x₁ = x₂)
    {x y : X} (hx : f x = some y) :
    extendPartialInjPerm f hf x = y := by
  unfold extendPartialInjPerm
  have hmem : x ∈ Finset.univ.filter (fun a ↦ (f a).isSome) := by
    simp [hx]
  simp [hmem, hx]

end PartialPerm

/-! ## 2. Single-Tape 2-Track Bennett Encoding & Unidirectional `ReversibleTM` -/

/-- Single-tape 2-track cell alphabet for Bennett's reversibilization of `M : FinTM0`:
* `sym`: symbol on the simulated work track;
* `workHead`: marker (`true` solely at the simulated work-head coordinate);
* `hist`: optional history record `(q, a)` written strictly to the left of prior history cells;
* `histHead`: marker (`true` solely at the current history-cursor coordinate);
* `haltMark`: post-halt right-cruise marker distinguishing `.halted` from `.haltRun`. -/
structure BennettCell (M : FinTM0) : Type where
  /-- Simulated work-track symbol. -/
  sym : M.Γ
  /-- Simulated work-head position marker. -/
  workHead : Bool
  /-- Optional history transition key `(q, a)`. -/
  hist : Option (M.Λ × M.Γ)
  /-- History-track cursor marker. -/
  histHead : Bool
  /-- Post-halt right-cruise marker (`false` before and at `.halted`, `true` along `.haltRun`). -/
  haltMark : Bool
  deriving DecidableEq

/-- Blank `BennettCell M`: blank work symbol with all boolean markers `false` and `hist = none`. -/
instance instInhabitedBennettCell (M : FinTM0) : Inhabited (BennettCell M) :=
  ⟨⟨default, false, none, false, false⟩⟩

/-- Canonical equivalence between `BennettCell M` and its 5-tuple representation. -/
def bennettCellEquiv (M : FinTM0) :
    BennettCell M ≃ M.Γ × Bool × Option (M.Λ × M.Γ) × Bool × Bool where
  toFun c := (c.sym, c.workHead, c.hist, c.histHead, c.haltMark)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv c := by cases c; rfl
  right_inv p := by rcases p with ⟨_, _, _, _, _⟩; rfl

/-- Finite-type instance for `BennettCell M` transported across `bennettCellEquiv M`. -/
instance instFintypeBennettCell (M : FinTM0) : Fintype (BennettCell M) :=
  Fintype.ofEquiv _ (bennettCellEquiv M).symm

/-- Work symbol of `default : BennettCell M` is `default : M.Γ`. -/
-- tier: T0
@[simp]
theorem BennettCell.default_sym (M : FinTM0) :
    (default : BennettCell M).sym = default := by
  rfl

/-- Work-head flag of `default : BennettCell M` is `false`. -/
-- tier: T0
@[simp]
theorem BennettCell.default_workHead (M : FinTM0) :
    (default : BennettCell M).workHead = false := by
  rfl

/-- History slot of `default : BennettCell M` is `none`. -/
-- tier: T0
@[simp]
theorem BennettCell.default_hist (M : FinTM0) :
    (default : BennettCell M).hist = none := by
  rfl

/-- History-cursor flag of `default : BennettCell M` is `false`. -/
-- tier: T0
@[simp]
theorem BennettCell.default_histHead (M : FinTM0) :
    (default : BennettCell M).histHead = false :=
  rfl

/-- Halt-cruise flag of `default : BennettCell M` is `false`. -/
-- tier: T0
@[simp]
theorem BennettCell.default_haltMark (M : FinTM0) :
    (default : BennettCell M).haltMark = false :=
  rfl

/-- Control state space for the single-tape unidirectional Bennett reversible machine of
`M : FinTM0`. Every constructor carries a fixed incoming head-shift direction `bennettDirIn`. -/
inductive BennettState (M : FinTM0) : Type
  /-- Ready at `posW` in state `q` with `rel = compare posW posH` (`dirIn = .stay`). -/
  | exec (q : M.Λ) (rel : Ordering)
  /-- Single-step accepting state at `posW` when `M.machine q a = none` (`dirIn = .stay`). -/
  | halted (q : M.Λ) (rel : Ordering)
  /-- Post-halt rightward cruise state setting `haltMark := true` (`dirIn = .right`). -/
  | haltRun (q : M.Λ) (rel : Ordering)
  /-- Stepping work head left from `posW` to `posW - 1` (`dirIn = .left`). -/
  | moveWorkLeft (e : M.Λ × M.Γ) (rel : Ordering)
  /-- Stepping work head right from `posW` to `posW + 1` (`dirIn = .right`). -/
  | moveWorkRight (e : M.Λ × M.Γ) (rel : Ordering)
  /-- Positioned at updated work head `posW'` with `rel = compare posW' posH` (`dirIn = .stay`). -/
  | afterExec (e : M.Λ × M.Γ) (rel : Ordering)
  /-- Walking left from `posW'` toward `posH < posW'` (`dirIn = .left`). -/
  | seekHistLeft (e : M.Λ × M.Γ)
  /-- Walking right from `posW'` toward `posH > posW'` (`dirIn = .right`). -/
  | seekHistRight (e : M.Λ × M.Γ)
  /-- Positioned at `posH` with `rel = compare posW' posH` (`dirIn = .stay`). -/
  | atHist (e : M.Λ × M.Γ) (rel : Ordering)
  /-- Stepping history cursor left from `posH` to `posH - 1` (`dirIn = .left`). -/
  | stepHistLeft (e : M.Λ × M.Γ) (rel : Ordering)
  /-- Positioned at `posH - 1` after recording `e`, with `rel = compare posW' (posH - 1)`
  (`dirIn = .stay`). -/
  | startReturn (q' : M.Λ) (rel : Ordering)
  /-- Walking left from `posH - 1` back to `posW' < posH - 1` (`dirIn = .left`). -/
  | seekWorkLeft (q' : M.Λ)
  /-- Walking right from `posH - 1` back to `posW' > posH - 1` (`dirIn = .right`). -/
  | seekWorkRight (q' : M.Λ)
  deriving DecidableEq

/-- Explicit sum-of-products equivalence used to endow `BennettState M` with `Fintype`. -/
def bennettStateEquiv (M : FinTM0) :
    BennettState M ≃
      ((M.Λ × Ordering) ⊕ (M.Λ × Ordering) ⊕ (M.Λ × Ordering) ⊕
        ((M.Λ × M.Γ) × Ordering) ⊕ ((M.Λ × M.Γ) × Ordering) ⊕ ((M.Λ × M.Γ) × Ordering)) ⊕
      ((M.Λ × M.Γ) ⊕ (M.Λ × M.Γ) ⊕ ((M.Λ × M.Γ) × Ordering) ⊕
        ((M.Λ × M.Γ) × Ordering) ⊕ (M.Λ × Ordering) ⊕ M.Λ ⊕ M.Λ) where
  toFun
    | .exec q r => .inl (.inl (q, r))
    | .halted q r => .inl (.inr (.inl (q, r)))
    | .haltRun q r => .inl (.inr (.inr (.inl (q, r))))
    | .moveWorkLeft e r => .inl (.inr (.inr (.inr (.inl (e, r)))))
    | .moveWorkRight e r => .inl (.inr (.inr (.inr (.inr (.inl (e, r))))))
    | .afterExec e r => .inl (.inr (.inr (.inr (.inr (.inr (e, r))))))
    | .seekHistLeft e => .inr (.inl e)
    | .seekHistRight e => .inr (.inr (.inl e))
    | .atHist e r => .inr (.inr (.inr (.inl (e, r))))
    | .stepHistLeft e r => .inr (.inr (.inr (.inr (.inl (e, r)))))
    | .startReturn q' r => .inr (.inr (.inr (.inr (.inr (.inl (q', r))))))
    | .seekWorkLeft q' => .inr (.inr (.inr (.inr (.inr (.inr (.inl q'))))))
    | .seekWorkRight q' => .inr (.inr (.inr (.inr (.inr (.inr (.inr q'))))))
  invFun
    | .inl (.inl (q, r)) => .exec q r
    | .inl (.inr (.inl (q, r))) => .halted q r
    | .inl (.inr (.inr (.inl (q, r)))) => .haltRun q r
    | .inl (.inr (.inr (.inr (.inl (e, r))))) => .moveWorkLeft e r
    | .inl (.inr (.inr (.inr (.inr (.inl (e, r)))))) => .moveWorkRight e r
    | .inl (.inr (.inr (.inr (.inr (.inr (e, r)))))) => .afterExec e r
    | .inr (.inl e) => .seekHistLeft e
    | .inr (.inr (.inl e)) => .seekHistRight e
    | .inr (.inr (.inr (.inl (e, r)))) => .atHist e r
    | .inr (.inr (.inr (.inr (.inl (e, r))))) => .stepHistLeft e r
    | .inr (.inr (.inr (.inr (.inr (.inl (q', r)))))) => .startReturn q' r
    | .inr (.inr (.inr (.inr (.inr (.inr (.inl q')))))) => .seekWorkLeft q'
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr q')))))) => .seekWorkRight q'
  left_inv s := by cases s <;> rfl
  right_inv x := by
    rcases x with
      (⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩) |
      (_ | _ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | _ | _) <;> rfl

/-- Finite-type instance for `BennettState M`. -/
instance instFintypeBennettState (M : FinTM0) : Fintype (BennettState M) :=
  Fintype.ofEquiv _ (bennettStateEquiv M).symm

/-- Unique incoming head-shift direction associated to each `BennettState M` (`CMPP21` Def. 4.2). -/
def bennettDirIn {M : FinTM0} : BennettState M → ShiftDir := fun
  | .exec _ _ => .stay
  | .halted _ _ => .stay
  | .haltRun _ _ => .right
  | .moveWorkLeft _ _ => .left
  | .moveWorkRight _ _ => .right
  | .afterExec _ _ => .stay
  | .seekHistLeft _ => .left
  | .seekHistRight _ => .right
  | .atHist _ _ => .stay
  | .stepHistLeft _ _ => .left
  | .startReturn _ _ => .stay
  | .seekWorkLeft _ => .left
  | .seekWorkRight _ => .right

/-- Incoming shift direction of `BennettState.exec` is `.stay`. -/
-- tier: T0
@[simp]
theorem bennettDirIn_exec {M : FinTM0} (q : M.Λ) (rel : Ordering) :
    bennettDirIn (BennettState.exec (M := M) q rel) = .stay :=
  rfl

/-- Incoming shift direction of `BennettState.halted` is `.stay`. -/
-- tier: T0
@[simp]
theorem bennettDirIn_halted {M : FinTM0} (q : M.Λ) (rel : Ordering) :
    bennettDirIn (BennettState.halted (M := M) q rel) = .stay := by
  simp [bennettDirIn]

/-- Incoming shift direction of `BennettState.haltRun` is `.right`. -/
-- tier: T0
@[simp]
theorem bennettDirIn_haltRun {M : FinTM0} (q : M.Λ) (rel : Ordering) :
    bennettDirIn (BennettState.haltRun (M := M) q rel) = .right :=
  rfl

/-- Incoming shift direction of `BennettState.moveWorkLeft` is `.left`. -/
-- tier: T0
@[simp]
theorem bennettDirIn_moveWorkLeft {M : FinTM0} (e : M.Λ × M.Γ) (rel : Ordering) :
    bennettDirIn (BennettState.moveWorkLeft (M := M) e rel) = .left :=
  rfl

/-- Incoming shift direction of `BennettState.moveWorkRight` is `.right`. -/
-- tier: T0
@[simp]
theorem bennettDirIn_moveWorkRight {M : FinTM0} (e : M.Λ × M.Γ) (rel : Ordering) :
    bennettDirIn (BennettState.moveWorkRight (M := M) e rel) = .right :=
  rfl

/-- Incoming shift direction of `BennettState.afterExec` is `.stay`. -/
-- tier: T0
@[simp]
theorem bennettDirIn_afterExec {M : FinTM0} (e : M.Λ × M.Γ) (rel : Ordering) :
    bennettDirIn (BennettState.afterExec (M := M) e rel) = .stay :=
  rfl

/-- Incoming shift direction of `BennettState.seekHistLeft` is `.left`. -/
-- tier: T0
@[simp]
theorem bennettDirIn_seekHistLeft {M : FinTM0} (e : M.Λ × M.Γ) :
    bennettDirIn (BennettState.seekHistLeft (M := M) e) = .left := by
  rfl

/-- Incoming shift direction of `BennettState.seekHistRight` is `.right`. -/
-- tier: T0
@[simp]
theorem bennettDirIn_seekHistRight {M : FinTM0} (e : M.Λ × M.Γ) :
    bennettDirIn (BennettState.seekHistRight (M := M) e) = .right := by
  simp [bennettDirIn]

/-- Incoming shift direction of `BennettState.atHist` is `.stay`. -/
-- tier: T0
@[simp]
theorem bennettDirIn_atHist {M : FinTM0} (e : M.Λ × M.Γ) (rel : Ordering) :
    bennettDirIn (BennettState.atHist (M := M) e rel) = .stay :=
  rfl

/-- Incoming shift direction of `BennettState.stepHistLeft` is `.left`. -/
-- tier: T0
@[simp]
theorem bennettDirIn_stepHistLeft {M : FinTM0} (e : M.Λ × M.Γ) (rel : Ordering) :
    bennettDirIn (BennettState.stepHistLeft (M := M) e rel) = .left :=
  rfl

/-- Incoming shift direction of `BennettState.startReturn` is `.stay`. -/
-- tier: T0
@[simp]
theorem bennettDirIn_startReturn {M : FinTM0} (q' : M.Λ) (rel : Ordering) :
    bennettDirIn (BennettState.startReturn (M := M) q' rel) = .stay := by
  unfold bennettDirIn
  simp

/-- Incoming shift direction of `BennettState.seekWorkLeft` is `.left`. -/
-- tier: T0
@[simp]
theorem bennettDirIn_seekWorkLeft {M : FinTM0} (q' : M.Λ) :
    bennettDirIn (BennettState.seekWorkLeft (M := M) q') = .left := by
  simp [bennettDirIn]

/-- Incoming shift direction of `BennettState.seekWorkRight` is `.right`. -/
-- tier: T0
@[simp]
theorem bennettDirIn_seekWorkRight {M : FinTM0} (q' : M.Λ) :
    bennettDirIn (BennettState.seekWorkRight (M := M) q') = .right := by
  simp [bennettDirIn]

/-- Partial injective state-cell transition table for Bennett's reversibilization of `M : FinTM0`.
Every active branch guards `workHead`, `histHead`, `haltMark`, `hist`, and `M.machine` so all image
pairs `(q', c')` have pairwise disjoint signatures. -/
def bennettRule (M : FinTM0) :
    BennettState M × BennettCell M → Option (BennettState M × BennettCell M) := fun
  | (.exec q rel, c) =>
    if c.workHead && !c.haltMark && (c.histHead == (rel == .eq)) then
      let e : M.Λ × M.Γ := (q, c.sym)
      match M.machine q c.sym with
      | none => some (.halted q rel, c)
      | some (_, .write b) => some (.afterExec e rel, { c with sym := b })
      | some (_, .move .left) =>
        let rMid : Ordering := match rel with | .gt => .gt | _ => .lt
        some (.moveWorkLeft e rMid, { c with workHead := false })
      | some (_, .move .right) =>
        let rMid : Ordering := match rel with | .lt => .lt | _ => .gt
        some (.moveWorkRight e rMid, { c with workHead := false })
    else
      none
  | (.halted q rel, c) =>
    if c.workHead && !c.haltMark then
      some (.haltRun q rel, { c with haltMark := true })
    else
      none
  | (.haltRun q rel, c) =>
    if !c.workHead && !c.haltMark then
      some (.haltRun q rel, { c with haltMark := true })
    else
      none
  | (.moveWorkLeft e rMid, c) =>
    if !c.workHead && !c.haltMark then
      match M.machine e.1 e.2 with
      | some (_, .move .left) =>
        match rMid with
        | .lt =>
          if !c.histHead then
            some (.afterExec e .lt, { c with workHead := true })
          else
            none
        | .gt =>
          let rel' : Ordering := if c.histHead then .eq else .gt
          some (.afterExec e rel', { c with workHead := true })
        | .eq => none
      | _ => none
    else
      none
  | (.moveWorkRight e rMid, c) =>
    if !c.workHead && !c.haltMark then
      match M.machine e.1 e.2 with
      | some (_, .move .right) =>
        match rMid with
        | .gt =>
          if !c.histHead then
            some (.afterExec e .gt, { c with workHead := true })
          else
            none
        | .lt =>
          let rel' : Ordering := if c.histHead then .eq else .lt
          some (.afterExec e rel', { c with workHead := true })
        | .eq => none
      | _ => none
    else
      none
  | (.afterExec e rel, c) =>
    if c.workHead && !c.haltMark && (c.histHead == (rel == .eq)) && (M.machine e.1 e.2).isSome then
      match rel with
      | .gt => some (.seekHistLeft e, c)
      | .eq => some (.atHist e .eq, c)
      | .lt => some (.seekHistRight e, c)
    else
      none
  | (.seekHistLeft e, c) =>
    if !c.workHead && !c.haltMark && (M.machine e.1 e.2).isSome then
      if c.histHead then
        some (.atHist e .gt, c)
      else
        some (.seekHistLeft e, c)
    else
      none
  | (.seekHistRight e, c) =>
    if !c.workHead && !c.haltMark && (M.machine e.1 e.2).isSome then
      if c.histHead then
        some (.atHist e .lt, c)
      else
        some (.seekHistRight e, c)
    else
      none
  | (.atHist e r, c) =>
    if c.histHead && !c.haltMark && (c.workHead == (r == .eq)) && (M.machine e.1 e.2).isSome then
      let rMid : Ordering := match r with | .lt => .lt | _ => .gt
      some (.stepHistLeft e rMid, { c with histHead := false })
    else
      none
  | (.stepHistLeft e rMid, c) =>
    if c.hist.isNone && !c.histHead && !c.haltMark then
      match M.machine e.1 e.2 with
      | none => none
      | some (q', _) =>
        match rMid with
        | .gt =>
          if !c.workHead then
            some (.startReturn q' .gt, { c with hist := some e, histHead := true })
          else
            none
        | .lt =>
          let rRet : Ordering := if c.workHead then .eq else .lt
          some (.startReturn q' rRet, { c with hist := some e, histHead := true })
        | .eq => none
    else
      none
  | (.startReturn q' rRet, c) =>
    if c.histHead && !c.haltMark && (c.workHead == (rRet == .eq)) then
      match rRet with
      | .lt => some (.seekWorkLeft q', c)
      | .eq => some (.exec q' .eq, c)
      | .gt => some (.seekWorkRight q', c)
    else
      none
  | (.seekWorkLeft q', c) =>
    if !c.histHead && !c.haltMark then
      if c.workHead then
        some (.exec q' .lt, c)
      else
        some (.seekWorkLeft q', c)
    else
      none
  | (.seekWorkRight q', c) =>
    if !c.histHead && !c.haltMark then
      if c.workHead then
        some (.exec q' .gt, c)
      else
        some (.seekWorkRight q', c)
    else
      none

/-- Explicit partial left-inverse of `bennettRule M`, reconstructing the unique preimage `(q, c)` of
every active output `(q', c')`. -/
def bennettRuleInv (M : FinTM0) :
    BennettState M × BennettCell M → Option (BennettState M × BennettCell M) := fun
  | (.exec q' rel, cOut) =>
    match rel with
    | .eq => some (.startReturn q' .eq, cOut)
    | .lt => some (.seekWorkLeft q', cOut)
    | .gt => some (.seekWorkRight q', cOut)
  | (.halted q rel, cOut) =>
    some (.exec q rel, cOut)
  | (.haltRun q rel, cOut) =>
    if cOut.workHead then
      some (.halted q rel, { cOut with haltMark := false })
    else
      some (.haltRun q rel, { cOut with haltMark := false })
  | (.moveWorkLeft e rMid, cOut) =>
    let rel : Ordering := match rMid with | .gt => .gt | _ => if cOut.histHead then .eq else .lt
    some (.exec e.1 rel, { cOut with workHead := true })
  | (.moveWorkRight e rMid, cOut) =>
    let rel : Ordering := match rMid with | .lt => .lt | _ => if cOut.histHead then .eq else .gt
    some (.exec e.1 rel, { cOut with workHead := true })
  | (.afterExec e rel', cOut) =>
    match M.machine e.1 e.2 with
    | none => none
    | some (_, .write _) => some (.exec e.1 rel', { cOut with sym := e.2 })
    | some (_, .move .left) =>
      let rMid : Ordering := match rel' with | .lt => .lt | _ => .gt
      some (.moveWorkLeft e rMid, { cOut with workHead := false })
    | some (_, .move .right) =>
      let rMid : Ordering := match rel' with | .gt => .gt | _ => .lt
      some (.moveWorkRight e rMid, { cOut with workHead := false })
  | (.seekHistLeft e, cOut) =>
    if cOut.workHead then
      some (.afterExec e .gt, cOut)
    else
      some (.seekHistLeft e, cOut)
  | (.seekHistRight e, cOut) =>
    if cOut.workHead then
      some (.afterExec e .lt, cOut)
    else
      some (.seekHistRight e, cOut)
  | (.atHist e r, cOut) =>
    match r with
    | .eq => some (.afterExec e .eq, cOut)
    | .gt => some (.seekHistLeft e, cOut)
    | .lt => some (.seekHistRight e, cOut)
  | (.stepHistLeft e rMid, cOut) =>
    let r : Ordering := match rMid with | .lt => .lt | _ => if cOut.workHead then .eq else .gt
    some (.atHist e r, { cOut with histHead := true })
  | (.startReturn _ rRet, cOut) =>
    match cOut.hist with
    | none => none
    | some e =>
      let rMid : Ordering := match rRet with | .gt => .gt | _ => .lt
      some (.stepHistLeft e rMid, { cOut with hist := none, histHead := false })
  | (.seekWorkLeft q', cOut) =>
    if cOut.histHead then
      some (.startReturn q' .lt, cOut)
    else
      some (.seekWorkLeft q', cOut)
  | (.seekWorkRight q', cOut) =>
    if cOut.histHead then
      some (.startReturn q' .gt, cOut)
    else
      some (.seekWorkRight q', cOut)

/-- `bennettRuleInv M` recovers `x` from every defined transition `bennettRule M x = some y`. -/
-- tier: T1
theorem bennettRuleInv_of_some (M : FinTM0) {x y : BennettState M × BennettCell M}
    (h : bennettRule M x = some y) :
    bennettRuleInv M y = some x := by
  rcases x with ⟨q, ⟨sym, workHead, hist, histHead, haltMark⟩⟩
  cases q with
  | exec q₀ rel =>
    dsimp [bennettRule] at h
    split_ifs at h with hg
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hg
    obtain ⟨⟨hwh, hhm⟩, hhh⟩ := hg
    subst hwh hhm
    rcases hm : M.machine q₀ sym with _ | ⟨q', (_ | _) | b⟩ <;> rw [hm] at h
    · injection h with hy; subst hy; rfl
    · injection h with hy; subst hy
      cases rel <;> simp [bennettRuleInv] at hhh ⊢ <;> subst hhh <;> rfl
    · injection h with hy; subst hy
      cases rel <;> simp [bennettRuleInv] at hhh ⊢ <;> subst hhh <;> rfl
    · injection h with hy; subst hy
      simp [bennettRuleInv, hm]
  | halted q₀ rel =>
    dsimp [bennettRule] at h
    split_ifs at h with hg
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hg
    obtain ⟨rfl, rfl⟩ := hg
    injection h with hy; subst hy
    rfl
  | haltRun q₀ rel =>
    dsimp [bennettRule] at h
    split_ifs at h with hg
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hg
    obtain ⟨rfl, rfl⟩ := hg
    injection h with hy; subst hy
    rfl
  | moveWorkLeft e rMid =>
    rcases hm : M.machine e.1 e.2 with _ | ⟨q', (_ | _) | b⟩ <;>
      cases workHead <;> cases haltMark <;> cases histHead <;> cases rMid <;>
      simp [bennettRule, hm] at h <;>
      subst h <;> simp [bennettRuleInv, hm]
  | moveWorkRight e rMid =>
    rcases hm : M.machine e.1 e.2 with _ | ⟨q', (_ | _) | b⟩ <;>
      cases workHead <;> cases haltMark <;> cases histHead <;> cases rMid <;>
      simp [bennettRule, hm] at h <;>
      subst h <;> simp [bennettRuleInv, hm]
  | afterExec e rel =>
    dsimp [bennettRule] at h
    split_ifs at h with hg
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hg
    obtain ⟨⟨⟨rfl, rfl⟩, _⟩, _⟩ := hg
    cases rel <;> (injection h with hy; subst hy; rfl)
  | seekHistLeft e =>
    dsimp [bennettRule] at h
    split_ifs at h with hg hhh
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hg
      obtain ⟨⟨rfl, rfl⟩, _⟩ := hg
      injection h with hy; subst hy; rfl
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hg
      obtain ⟨⟨rfl, rfl⟩, _⟩ := hg
      injection h with hy; subst hy; rfl
  | seekHistRight e =>
    dsimp [bennettRule] at h
    split_ifs at h with hg hhh
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hg
      obtain ⟨⟨rfl, rfl⟩, _⟩ := hg
      injection h with hy; subst hy; rfl
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hg
      obtain ⟨⟨rfl, rfl⟩, _⟩ := hg
      injection h with hy; subst hy; rfl
  | atHist e r =>
    dsimp [bennettRule] at h
    split_ifs at h with hg
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hg
    obtain ⟨⟨⟨rfl, rfl⟩, hwh⟩, _⟩ := hg
    injection h with hy; subst hy
    cases r <;> simp [bennettRuleInv] at hwh ⊢ <;> subst hwh <;> rfl
  | stepHistLeft e rMid =>
    rcases hm : M.machine e.1 e.2 with _ | ⟨q', stmt⟩ <;>
      rcases hist with _ | hval <;>
      cases workHead <;> cases histHead <;> cases haltMark <;> cases rMid <;>
      simp [bennettRule, hm] at h <;>
      subst h <;> simp [bennettRuleInv]
  | startReturn q' rRet =>
    dsimp [bennettRule] at h
    split_ifs at h with hg
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hg
    obtain ⟨⟨rfl, rfl⟩, _⟩ := hg
    cases rRet <;> (injection h with hy; subst hy; rfl)
  | seekWorkLeft q' =>
    dsimp [bennettRule] at h
    split_ifs at h with hg hwh
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hg
      obtain ⟨rfl, rfl⟩ := hg
      injection h with hy; subst hy; rfl
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hg
      obtain ⟨rfl, rfl⟩ := hg
      injection h with hy; subst hy; rfl
  | seekWorkRight q' =>
    dsimp [bennettRule] at h
    split_ifs at h with hg hwh
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hg
      obtain ⟨rfl, rfl⟩ := hg
      injection h with hy; subst hy; rfl
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hg
      obtain ⟨rfl, rfl⟩ := hg
      injection h with hy; subst hy; rfl

/-- `bennettRule M` is partially injective: distinct `(q₁, c₁)` and `(q₂, c₂)` never map to the
same `some y`. -/
-- tier: T1
theorem bennettRule_partial_injective (M : FinTM0)
    (x₁ x₂ y : BennettState M × BennettCell M)
    (h₁ : bennettRule M x₁ = some y) (h₂ : bennettRule M x₂ = some y) :
    x₁ = x₂ :=
  Option.some.inj ((bennettRuleInv_of_some M h₁).symm.trans (bennettRuleInv_of_some M h₂))

/-- Total state-cell permutation `(BennettState M × BennettCell M) ≃ _` extending `bennettRule M`
via `extendPartialInjPerm`. -/
noncomputable def bennettStepPerm (M : FinTM0) :
    (BennettState M × BennettCell M) ≃ (BennettState M × BennettCell M) :=
  extendPartialInjPerm (bennettRule M) (bennettRule_partial_injective M)

/-- Bennett's (1973) unidirectional reversible Turing machine `ReversibleTM.{0, 0}` associated to
any finite Post-Turing machine `M : FinTM0`. Marked `@[reducible]` so `(bennettReversibleTM M).Γ`
and `(bennettReversibleTM M).Q` unify at instance transparency with `BennettCell M` and
`BennettState M` while keeping `bennettStepPerm M` semireducible. -/
@[reducible]
noncomputable def bennettReversibleTM (M : FinTM0) : ReversibleTM.{0, 0} where
  Γ := BennettCell M
  Q := BennettState M
  stepPerm := bennettStepPerm M
  dirIn := bennettDirIn

/-- Finite-type instance on `(bennettReversibleTM M).ShiftAlphabet` (`BennettCell M × Option
(BennettState M)`). -/
instance instFintypeShiftAlphabetBennettReversibleTM (M : FinTM0) :
    Fintype (bennettReversibleTM M).ShiftAlphabet :=
  instFintypeProd (BennettCell M) (Option (BennettState M))

/-! ## 3. Initial Encoding, `BennettInv`, Macro-Step Simulation & Orbit Equivalence -/

/-- Pointed embedding sending each work symbol `a : M.Γ` to the inactive cell
`⟨a, false, none, false, false⟩` (preserving `default`). -/
def bennettInactiveCell (M : FinTM0) : PointedMap M.Γ (BennettCell M) where
  f a := ⟨a, false, none, false, false⟩
  map_pt' := rfl

/-- Initial 2-track Bennett tape encoding `t : FinSupportedTape M`: places both `workHead = true`
and `histHead = true` at cell `0` and maps the left and right `ListBlank` halves via
`bennettInactiveCell M`. -/
def bennettInitTape (M : FinTM0) (t : FinSupportedTape M) : Tape (BennettCell M) where
  head := ⟨t.head, true, none, true, false⟩
  left := t.left.map (bennettInactiveCell M)
  right := t.right.map (bennettInactiveCell M)

/-- Initial reversible configuration `⟨.exec default .eq, bennettInitTape M t⟩` of
`bennettReversibleTM M` on input tape `t`. -/
def bennettInitCfg (M : FinTM0) (t : FinSupportedTape M) : (bennettReversibleTM M).Cfg :=
  ⟨.exec default .eq, bennettInitTape M t⟩

/-- Pointwise evaluation of `bennettInactiveCell M` on `a : M.Γ`. -/
-- tier: T0
@[simp]
theorem bennettInactiveCell_apply (M : FinTM0) (a : M.Γ) :
    bennettInactiveCell M a = ⟨a, false, none, false, false⟩ := by
  rfl

/-- Head-shift direction map of `bennettReversibleTM M` is `bennettDirIn`. -/
-- tier: T0
@[simp]
theorem bennettReversibleTM_dirIn (M : FinTM0) :
    (bennettReversibleTM M).dirIn = bennettDirIn := by
  rfl

/-- Head cell of `bennettInitTape M t`. -/
-- tier: T0
@[simp]
theorem bennettInitTape_head (M : FinTM0) (t : FinSupportedTape M) :
    (bennettInitTape M t).head = ⟨t.head, true, none, true, false⟩ := by
  simp [bennettInitTape]

/-- Left half-tape of `bennettInitTape M t`. -/
-- tier: T0
@[simp]
theorem bennettInitTape_left (M : FinTM0) (t : FinSupportedTape M) :
    (bennettInitTape M t).left = t.left.map (bennettInactiveCell M) := by
  rfl

/-- Right half-tape of `bennettInitTape M t`. -/
-- tier: T0
@[simp]
theorem bennettInitTape_right (M : FinTM0) (t : FinSupportedTape M) :
    (bennettInitTape M t).right = t.right.map (bennettInactiveCell M) := by
  simp [bennettInitTape]

/-- Cell `0` of `bennettInitTape M t`. -/
-- tier: T0
theorem bennettInitTape_nth_zero (M : FinTM0) (t : FinSupportedTape M) :
    (bennettInitTape M t).nth 0 = ⟨t.head, true, none, true, false⟩ :=
  rfl

/-- Initial control state of `bennettInitCfg M t` is `.exec default .eq`. -/
-- tier: T0
@[simp]
theorem bennettInitCfg_q (M : FinTM0) (t : FinSupportedTape M) :
    (bennettInitCfg M t).q = .exec default .eq :=
  rfl

/-- Initial tape of `bennettInitCfg M t` is `bennettInitTape M t`. -/
-- tier: T0
@[simp]
theorem bennettInitCfg_tape (M : FinTM0) (t : FinSupportedTape M) :
    (bennettInitCfg M t).Tape = bennettInitTape M t :=
  rfl

/-- No initial configuration `bennettInitCfg M t` is in a `.halted` state at step `0`. -/
-- tier: T0
theorem bennettInitCfg_q_ne_halted (M : FinTM0) (t : FinSupportedTape M)
    (q : M.Λ) (rel : Ordering) :
    (bennettInitCfg M t).q ≠ .halted q rel := by
  intro h
  cases h

/-! ### `bennettInitTape` & `Tape.mk₂` Indexing Lemmas for Milestone B3 -/

/-- Negative-offset cell `-((j : ℤ) + 1)` of `bennettInitTape M t`. -/
-- tier: T1
theorem bennettInitTape_nth_negSucc (M : FinTM0) (t : FinSupportedTape M) (j : ℕ) :
    (bennettInitTape M t).nth (-((j : ℤ) + 1)) =
      ⟨t.nth (-((j : ℤ) + 1)), false, none, false, false⟩ := by
  have heq : -((j : ℤ) + 1) = -((j + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [heq]
  change ((bennettInitTape M t).left).nth j = _
  rw [bennettInitTape_left, ListBlank.nth_map, bennettInactiveCell_apply]
  rfl

/-- Positive-offset cell `(j : ℤ) + 1` of `bennettInitTape M t`. -/
-- tier: T1
@[simp]
theorem bennettInitTape_nth_succ (M : FinTM0) (t : FinSupportedTape M) (j : ℕ) :
    (bennettInitTape M t).nth ((j : ℤ) + 1) =
      ⟨t.nth ((j : ℤ) + 1), false, none, false, false⟩ := by
  have heq : ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [heq]
  change ((bennettInitTape M t).right).nth j = _
  rw [bennettInitTape_right, ListBlank.nth_map, bennettInactiveCell_apply]
  rfl

/-- Any nonzero cell `i ≠ 0` of `bennettInitTape M t` holds the inactive cell for `t.nth i`. -/
-- tier: T1
theorem bennettInitTape_nth_of_ne_zero (M : FinTM0) (t : FinSupportedTape M) {i : ℤ}
    (hi : i ≠ 0) :
    (bennettInitTape M t).nth i = ⟨t.nth i, false, none, false, false⟩ := by
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = -((j : ℤ) + 1) := ⟨(-i - 1).toNat, by omega⟩
    exact bennettInitTape_nth_negSucc M t j
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = (j : ℤ) + 1 := ⟨(i - 1).toNat, by omega⟩
    exact bennettInitTape_nth_succ M t j

/-- Work-track symbol projection `((bennettInitTape M t).nth i).sym = t.nth i` for all `i : ℤ`. -/
-- tier: T1
@[simp]
theorem bennettInitTape_nth_sym (M : FinTM0) (t : FinSupportedTape M) (i : ℤ) :
    ((bennettInitTape M t).nth i).sym = t.nth i := by
  by_cases hi : i = 0
  · subst hi; rfl
  · rw [bennettInitTape_nth_of_ne_zero M t hi]

/-- Cell `0` of `bennettInitTape M (Tape.mk₂ L R)`. -/
-- tier: T1
theorem bennettInitTape_mk₂_nth_zero (M : FinTM0) (L R : List M.Γ) :
    (bennettInitTape M (Tape.mk₂ L R)).nth 0 = ⟨R.headI, true, none, true, false⟩ :=
  rfl

/-- Negative cell `-((j : ℤ) + 1)` of `bennettInitTape M (Tape.mk₂ L R)`. -/
-- tier: T1
theorem bennettInitTape_mk₂_nth_negSucc (M : FinTM0) (L R : List M.Γ) (j : ℕ) :
    (bennettInitTape M (Tape.mk₂ L R)).nth (-((j : ℤ) + 1)) =
      ⟨L.getI j, false, none, false, false⟩ := by
  rw [bennettInitTape_nth_negSucc]
  have heq : -((j : ℤ) + 1) = -((j + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [heq]
  rfl

/-- Positive cell `(j : ℤ) + 1` of `bennettInitTape M (Tape.mk₂ L R)`. -/
-- tier: T1
theorem bennettInitTape_mk₂_nth_succ (M : FinTM0) (L R : List M.Γ) (j : ℕ) :
    (bennettInitTape M (Tape.mk₂ L R)).nth ((j : ℤ) + 1) =
      ⟨R.tail.getI j, false, none, false, false⟩ := by
  rw [bennettInitTape_nth_succ]
  have heq : ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [heq]
  rfl

/-- Negative Cantor half-sequence digit of `encodeCfg (bennettInitCfg M (Tape.mk₂ L R))` at `j`. -/
-- tier: T1
@[simp]
theorem bennettInitCfg_mk₂_negHalf (M : FinTM0) (L R : List M.Γ) (j : ℕ) :
    negHalf ((bennettReversibleTM M).encodeCfg (bennettInitCfg M (Tape.mk₂ L R))) j =
      (⟨L.getI j, false, none, false, false⟩, none) := by
  have hne : -((j : ℤ) + 1) ≠ 0 := by omega
  unfold negHalf ReversibleTM.encodeCfg bennettInitCfg
  dsimp only
  rw [bennettInitTape_mk₂_nth_negSucc]
  split_ifs with h0
  · exact absurd h0 hne
  · rfl

/-- Non-negative Cantor half-sequence digit `0` of `encodeCfg (bennettInitCfg M (Tape.mk₂ L R))`. -/
-- tier: T1
@[simp]
theorem bennettInitCfg_mk₂_nonnegHalf_zero (M : FinTM0) (L R : List M.Γ) :
    nonnegHalf ((bennettReversibleTM M).encodeCfg (bennettInitCfg M (Tape.mk₂ L R))) 0 =
      (⟨R.headI, true, none, true, false⟩, some (.exec default .eq)) :=
  rfl

/-- Non-negative Cantor half-sequence digit `j + 1` of
`encodeCfg (bennettInitCfg M (Tape.mk₂ L R))`. -/
-- tier: T1
@[simp]
theorem bennettInitCfg_mk₂_nonnegHalf_succ (M : FinTM0) (L R : List M.Γ) (j : ℕ) :
    nonnegHalf ((bennettReversibleTM M).encodeCfg (bennettInitCfg M (Tape.mk₂ L R))) (j + 1) =
      (⟨R.tail.getI j, false, none, false, false⟩, none) := by
  have hcast : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by push_cast; ring
  have hne : (j : ℤ) + 1 ≠ 0 := by omega
  unfold nonnegHalf ReversibleTM.encodeCfg bennettInitCfg
  dsimp only
  rw [hcast, bennettInitTape_mk₂_nth_succ]
  simp [hne]

/-! ### `Tape.move` Iteration, Single-Step Unfolding & Non-Halting Segments (`StepsNoHalt`) -/

/-- Self-write identity specialized to `(bennettReversibleTM M).Γ` tapes so `rcfg.Tape.write
rcfg.Tape.head` simplifies without semi-reducible instance drift. -/
-- tier: T1
theorem bennettTape_write_head (M : FinTM0) (T : Tape (bennettReversibleTM M).Γ) :
    T.write T.head = T :=
  Tape.write_self T

/-- `d` leftward tape moves shift `nth i` to `nth (i - d)`. -/
-- tier: T1
theorem tape_iterate_move_left_nth {Γ : Type*} [Inhabited Γ] (T : Tape Γ) (d : ℕ) (i : ℤ) :
    ((Tape.move Dir.left)^[d] T).nth i = T.nth (i - d) := by
  induction d generalizing T i with
  | zero => simp
  | succ d ih =>
    rw [Function.iterate_succ_apply, ih, Tape.move_left_nth]
    congr 1
    omega

/-- `d` rightward tape moves shift `nth i` to `nth (i + d)`. -/
-- tier: T1
theorem tape_iterate_move_right_nth {Γ : Type*} [Inhabited Γ] (T : Tape Γ) (d : ℕ) (i : ℤ) :
    ((Tape.move Dir.right)^[d] T).nth i = T.nth (i + d) := by
  induction d generalizing T i with
  | zero => simp
  | succ d ih =>
    rw [Function.iterate_succ_apply, ih, Tape.move_right_nth]
    congr 1
    omega

/-- Single-step unfolding of `(bennettReversibleTM M).step c` whenever `bennettRule M` evaluates
to `some (q', b)`. -/
-- tier: T1
theorem bennettReversibleTM_step_of_rule (M : FinTM0) (c : (bennettReversibleTM M).Cfg)
    {q' : BennettState M} {b : BennettCell M}
    (h : bennettRule M (c.q, c.Tape.head) = some (q', b)) :
    (bennettReversibleTM M).step c =
      match bennettDirIn q' with
      | .left => ⟨q', (c.Tape.write b).move Dir.left⟩
      | .stay => ⟨q', c.Tape.write b⟩
      | .right => ⟨q', (c.Tape.write b).move Dir.right⟩ := by
  unfold ReversibleTM.step
  have hp : (bennettReversibleTM M).stepPerm (c.q, c.Tape.head) = (q', b) :=
    extendPartialInjPerm_eq_of_some (bennettRule M) (bennettRule_partial_injective M) h
  dsimp only [bennettReversibleTM] at hp ⊢
  rw [hp]
  rfl

/-- Predicate asserting that `c₁` steps in `m` iterations of `(bennettReversibleTM M).step` to `c₂`
without visiting `.halted _ _` at any strict prefix index `j < m`. -/
def StepsNoHalt (M : FinTM0) (c₁ c₂ : (bennettReversibleTM M).Cfg) (m : ℕ) : Prop :=
  (bennettReversibleTM M).step^[m] c₁ = c₂ ∧
  ∀ j < m, ∀ q rel, ((bennettReversibleTM M).step^[j] c₁).q ≠ .halted q rel

/-- Zero-step reflexivity for `StepsNoHalt`. -/
-- tier: T1
theorem StepsNoHalt.refl (M : FinTM0) (c : (bennettReversibleTM M).Cfg) :
    StepsNoHalt M c c 0 :=
  ⟨rfl, fun _ hj _ _ ↦ absurd hj (Nat.not_lt_zero _)⟩

/-- Single-step constructor for `StepsNoHalt`. -/
-- tier: T1
theorem StepsNoHalt.single {M : FinTM0} {c₁ c₂ : (bennettReversibleTM M).Cfg}
    (hstep : (bennettReversibleTM M).step c₁ = c₂)
    (hnot : ∀ q rel, c₁.q ≠ .halted q rel) :
    StepsNoHalt M c₁ c₂ 1 := by
  refine ⟨hstep, fun j hj q rel ↦ ?_⟩
  have hj0 : j = 0 := by omega
  subst hj0
  exact hnot q rel

/-- Transitive composition of non-halting trajectory segments. -/
-- tier: T1
theorem StepsNoHalt.trans {M : FinTM0} {c₁ c₂ c₃ : (bennettReversibleTM M).Cfg} {m₁ m₂ : ℕ}
    (h₁ : StepsNoHalt M c₁ c₂ m₁) (h₂ : StepsNoHalt M c₂ c₃ m₂) :
    StepsNoHalt M c₁ c₃ (m₁ + m₂) := by
  refine ⟨?_, fun j hj q rel ↦ ?_⟩
  · rw [Nat.add_comm, Function.iterate_add_apply, h₁.1, h₂.1]
  · by_cases hlt : j < m₁
    · exact h₁.2 j hlt q rel
    · have hsub : j = (j - m₁) + m₁ := by omega
      rw [hsub, Function.iterate_add_apply, h₁.1]
      exact h₂.2 (j - m₁) (by omega) q rel

/-! ### Walking Lemmas (`seekHistLeft`, `seekHistRight`, `seekWorkLeft`, `seekWorkRight`) -/

/-- Leftward history-cursor search: starting in `.seekHistLeft e` with `histHead = false` on offsets
`0, -1, …, -(d - 1)` and `histHead = true` at `-d` (all with `workHead = false` and
`haltMark = false`), the machine reaches `⟨.atHist e .gt, (Tape.move .left)^[d] T⟩` in `d + 1`
non-halting steps. -/
-- tier: T1
theorem bennett_walk_seekHistLeft (M : FinTM0) (e : M.Λ × M.Γ)
    (he : (M.machine e.1 e.2).isSome = true) (d : ℕ) :
    ∀ c : (bennettReversibleTM M).Cfg,
      c.q = .seekHistLeft e →
      (∀ j < d,
        (c.Tape.nth (-(j : ℤ))).workHead = false ∧
        (c.Tape.nth (-(j : ℤ))).haltMark = false ∧
        (c.Tape.nth (-(j : ℤ))).histHead = false) →
      (c.Tape.nth (-(d : ℤ))).workHead = false →
      (c.Tape.nth (-(d : ℤ))).haltMark = false →
      (c.Tape.nth (-(d : ℤ))).histHead = true →
      StepsNoHalt M c ⟨.atHist e .gt, (Tape.move Dir.left)^[d] c.Tape⟩ (d + 1) := by
  induction d with
  | zero =>
    intro c hq _ hwh hhm hhh
    have hwh0 : c.Tape.head.workHead = false := by simpa using hwh
    have hhm0 : c.Tape.head.haltMark = false := by simpa using hhm
    have hhh0 : c.Tape.head.histHead = true := by simpa using hhh
    have hrule : bennettRule M (c.q, c.Tape.head) = some (.atHist e .gt, c.Tape.head) := by
      rw [hq]
      simp [bennettRule, hwh0, hhm0, hhh0, he]
    have hstep : (bennettReversibleTM M).step c = ⟨.atHist e .gt, c.Tape⟩ := by
      rw [bennettReversibleTM_step_of_rule M c hrule, bennettDirIn_atHist, bennettTape_write_head]
    exact StepsNoHalt.single hstep (by rw [hq]; intro _ _ h; cases h)
  | succ d ih =>
    intro c hq hlt hwh hhm hhh
    obtain ⟨hwh0, hhm0, hhh0⟩ := hlt 0 (Nat.zero_lt_succ d)
    have hwh0' : c.Tape.head.workHead = false := by simpa using hwh0
    have hhm0' : c.Tape.head.haltMark = false := by simpa using hhm0
    have hhh0' : c.Tape.head.histHead = false := by simpa using hhh0
    have hrule : bennettRule M (c.q, c.Tape.head) = some (.seekHistLeft e, c.Tape.head) := by
      rw [hq]
      simp [bennettRule, hwh0', hhm0', hhh0', he]
    let c' : (bennettReversibleTM M).Cfg := ⟨.seekHistLeft e, c.Tape.move Dir.left⟩
    have hstep : (bennettReversibleTM M).step c = c' := by
      rw [bennettReversibleTM_step_of_rule M c hrule, bennettDirIn_seekHistLeft,
        bennettTape_write_head]
    have h1 : StepsNoHalt M c c' 1 :=
      StepsNoHalt.single hstep (by rw [hq]; intro _ _ h; cases h)
    have hshift : ∀ k : ℕ, c'.Tape.nth (-(k : ℤ)) = c.Tape.nth (-((k + 1 : ℕ) : ℤ)) := by
      intro k
      simp only [c', Tape.move_left_nth]
      congr 1
      omega
    have h2 := ih c' rfl
      (fun j hj ↦ by rw [hshift j]; exact hlt (j + 1) (Nat.succ_lt_succ hj))
      (by rw [hshift d]; exact hwh)
      (by rw [hshift d]; exact hhm)
      (by rw [hshift d]; exact hhh)
    have hcomb := h1.trans h2
    have heq_len : 1 + (d + 1) = d + 1 + 1 := by omega
    rw [heq_len] at hcomb
    simpa [c', Function.iterate_succ_apply] using hcomb

/-- Rightward history-cursor search: starting in `.seekHistRight e` with `histHead = false` on
offsets `0, 1, …, d - 1` and `histHead = true` at `d` (all with `workHead = false` and
`haltMark = false`), the machine reaches `⟨.atHist e .lt, (Tape.move .right)^[d] T⟩` in `d + 1`
non-halting steps. -/
-- tier: T1
theorem bennett_walk_seekHistRight (M : FinTM0) (e : M.Λ × M.Γ)
    (he : (M.machine e.1 e.2).isSome = true) (d : ℕ) :
    ∀ c : (bennettReversibleTM M).Cfg,
      c.q = .seekHistRight e →
      (∀ j < d,
        (c.Tape.nth (j : ℤ)).workHead = false ∧
        (c.Tape.nth (j : ℤ)).haltMark = false ∧
        (c.Tape.nth (j : ℤ)).histHead = false) →
      (c.Tape.nth (d : ℤ)).workHead = false →
      (c.Tape.nth (d : ℤ)).haltMark = false →
      (c.Tape.nth (d : ℤ)).histHead = true →
      StepsNoHalt M c ⟨.atHist e .lt, (Tape.move Dir.right)^[d] c.Tape⟩ (d + 1) := by
  induction d with
  | zero =>
    intro c hq _ hwh hhm hhh
    have hwh0 : c.Tape.head.workHead = false := by simpa using hwh
    have hhm0 : c.Tape.head.haltMark = false := by simpa using hhm
    have hhh0 : c.Tape.head.histHead = true := by simpa using hhh
    have hrule : bennettRule M (c.q, c.Tape.head) = some (.atHist e .lt, c.Tape.head) := by
      rw [hq]
      simp [bennettRule, hwh0, hhm0, hhh0, he]
    have hstep : (bennettReversibleTM M).step c = ⟨.atHist e .lt, c.Tape⟩ := by
      rw [bennettReversibleTM_step_of_rule M c hrule, bennettDirIn_atHist, bennettTape_write_head]
    exact StepsNoHalt.single hstep (by rw [hq]; intro _ _ h; cases h)
  | succ d ih =>
    intro c hq hlt hwh hhm hhh
    obtain ⟨hwh0, hhm0, hhh0⟩ := hlt 0 (Nat.zero_lt_succ d)
    have hwh0' : c.Tape.head.workHead = false := by simpa using hwh0
    have hhm0' : c.Tape.head.haltMark = false := by simpa using hhm0
    have hhh0' : c.Tape.head.histHead = false := by simpa using hhh0
    have hrule : bennettRule M (c.q, c.Tape.head) = some (.seekHistRight e, c.Tape.head) := by
      rw [hq]
      simp [bennettRule, hwh0', hhm0', hhh0', he]
    let c' : (bennettReversibleTM M).Cfg := ⟨.seekHistRight e, c.Tape.move Dir.right⟩
    have hstep : (bennettReversibleTM M).step c = c' := by
      rw [bennettReversibleTM_step_of_rule M c hrule, bennettDirIn_seekHistRight,
        bennettTape_write_head]
    have h1 : StepsNoHalt M c c' 1 :=
      StepsNoHalt.single hstep (by rw [hq]; intro _ _ h; cases h)
    have hshift : ∀ k : ℕ, c'.Tape.nth (k : ℤ) = c.Tape.nth ((k + 1 : ℕ) : ℤ) := by
      intro k
      simp only [c', Tape.move_right_nth]
      congr 1
    have h2 := ih c' rfl
      (fun j hj ↦ by rw [hshift j]; exact hlt (j + 1) (Nat.succ_lt_succ hj))
      (by rw [hshift d]; exact hwh)
      (by rw [hshift d]; exact hhm)
      (by rw [hshift d]; exact hhh)
    have hcomb := h1.trans h2
    have heq_len : 1 + (d + 1) = d + 1 + 1 := by omega
    rw [heq_len] at hcomb
    simpa [c', Function.iterate_succ_apply] using hcomb

/-- Leftward work-head search: starting in `.seekWorkLeft q'` with `workHead = false` on offsets
`0, -1, …, -(d - 1)` and `workHead = true` at `-d` (all with `histHead = false` and
`haltMark = false`), the machine reaches `⟨.exec q' .lt, (Tape.move .left)^[d] T⟩` in `d + 1`
non-halting steps. -/
-- tier: T1
theorem bennett_walk_seekWorkLeft (M : FinTM0) (q' : M.Λ) (d : ℕ) :
    ∀ c : (bennettReversibleTM M).Cfg,
      c.q = .seekWorkLeft q' →
      (∀ j < d,
        (c.Tape.nth (-(j : ℤ))).histHead = false ∧
        (c.Tape.nth (-(j : ℤ))).haltMark = false ∧
        (c.Tape.nth (-(j : ℤ))).workHead = false) →
      (c.Tape.nth (-(d : ℤ))).histHead = false →
      (c.Tape.nth (-(d : ℤ))).haltMark = false →
      (c.Tape.nth (-(d : ℤ))).workHead = true →
      StepsNoHalt M c ⟨.exec q' .lt, (Tape.move Dir.left)^[d] c.Tape⟩ (d + 1) := by
  induction d with
  | zero =>
    intro c hq _ hhh hhm hwh
    have hhh0 : c.Tape.head.histHead = false := by simpa using hhh
    have hhm0 : c.Tape.head.haltMark = false := by simpa using hhm
    have hwh0 : c.Tape.head.workHead = true := by simpa using hwh
    have hrule : bennettRule M (c.q, c.Tape.head) = some (.exec q' .lt, c.Tape.head) := by
      rw [hq]
      simp [bennettRule, hhh0, hhm0, hwh0]
    have hstep : (bennettReversibleTM M).step c = ⟨.exec q' .lt, c.Tape⟩ := by
      rw [bennettReversibleTM_step_of_rule M c hrule, bennettDirIn_exec, bennettTape_write_head]
    exact StepsNoHalt.single hstep (by rw [hq]; intro _ _ h; cases h)
  | succ d ih =>
    intro c hq hlt hhh hhm hwh
    obtain ⟨hhh0, hhm0, hwh0⟩ := hlt 0 (Nat.zero_lt_succ d)
    have hhh0' : c.Tape.head.histHead = false := by simpa using hhh0
    have hhm0' : c.Tape.head.haltMark = false := by simpa using hhm0
    have hwh0' : c.Tape.head.workHead = false := by simpa using hwh0
    have hrule : bennettRule M (c.q, c.Tape.head) = some (.seekWorkLeft q', c.Tape.head) := by
      rw [hq]
      simp [bennettRule, hhh0', hhm0', hwh0']
    let c' : (bennettReversibleTM M).Cfg := ⟨.seekWorkLeft q', c.Tape.move Dir.left⟩
    have hstep : (bennettReversibleTM M).step c = c' := by
      rw [bennettReversibleTM_step_of_rule M c hrule, bennettDirIn_seekWorkLeft,
        bennettTape_write_head]
    have h1 : StepsNoHalt M c c' 1 :=
      StepsNoHalt.single hstep (by rw [hq]; intro _ _ h; cases h)
    have hshift : ∀ k : ℕ, c'.Tape.nth (-(k : ℤ)) = c.Tape.nth (-((k + 1 : ℕ) : ℤ)) := by
      intro k
      simp only [c', Tape.move_left_nth]
      congr 1
      omega
    have h2 := ih c' rfl
      (fun j hj ↦ by rw [hshift j]; exact hlt (j + 1) (Nat.succ_lt_succ hj))
      (by rw [hshift d]; exact hhh)
      (by rw [hshift d]; exact hhm)
      (by rw [hshift d]; exact hwh)
    have hcomb := h1.trans h2
    have heq_len : 1 + (d + 1) = d + 1 + 1 := by omega
    rw [heq_len] at hcomb
    simpa [c', Function.iterate_succ_apply] using hcomb

/-- Rightward work-head search: starting in `.seekWorkRight q'` with `workHead = false` on offsets
`0, 1, …, d - 1` and `workHead = true` at `d` (all with `histHead = false` and `haltMark = false`),
the machine reaches `⟨.exec q' .gt, (Tape.move .right)^[d] T⟩` in `d + 1` non-halting steps. -/
-- tier: T1
theorem bennett_walk_seekWorkRight (M : FinTM0) (q' : M.Λ) (d : ℕ) :
    ∀ c : (bennettReversibleTM M).Cfg,
      c.q = .seekWorkRight q' →
      (∀ j < d,
        (c.Tape.nth (j : ℤ)).histHead = false ∧
        (c.Tape.nth (j : ℤ)).haltMark = false ∧
        (c.Tape.nth (j : ℤ)).workHead = false) →
      (c.Tape.nth (d : ℤ)).histHead = false →
      (c.Tape.nth (d : ℤ)).haltMark = false →
      (c.Tape.nth (d : ℤ)).workHead = true →
      StepsNoHalt M c ⟨.exec q' .gt, (Tape.move Dir.right)^[d] c.Tape⟩ (d + 1) := by
  induction d with
  | zero =>
    intro c hq _ hhh hhm hwh
    have hhh0 : c.Tape.head.histHead = false := by simpa using hhh
    have hhm0 : c.Tape.head.haltMark = false := by simpa using hhm
    have hwh0 : c.Tape.head.workHead = true := by simpa using hwh
    have hrule : bennettRule M (c.q, c.Tape.head) = some (.exec q' .gt, c.Tape.head) := by
      rw [hq]
      simp [bennettRule, hhh0, hhm0, hwh0]
    have hstep : (bennettReversibleTM M).step c = ⟨.exec q' .gt, c.Tape⟩ := by
      rw [bennettReversibleTM_step_of_rule M c hrule, bennettDirIn_exec, bennettTape_write_head]
    exact StepsNoHalt.single hstep (by rw [hq]; intro _ _ h; cases h)
  | succ d ih =>
    intro c hq hlt hhh hhm hwh
    obtain ⟨hhh0, hhm0, hwh0⟩ := hlt 0 (Nat.zero_lt_succ d)
    have hhh0' : c.Tape.head.histHead = false := by simpa using hhh0
    have hhm0' : c.Tape.head.haltMark = false := by simpa using hhm0
    have hwh0' : c.Tape.head.workHead = false := by simpa using hwh0
    have hrule : bennettRule M (c.q, c.Tape.head) = some (.seekWorkRight q', c.Tape.head) := by
      rw [hq]
      simp [bennettRule, hhh0', hhm0', hwh0']
    let c' : (bennettReversibleTM M).Cfg := ⟨.seekWorkRight q', c.Tape.move Dir.right⟩
    have hstep : (bennettReversibleTM M).step c = c' := by
      rw [bennettReversibleTM_step_of_rule M c hrule, bennettDirIn_seekWorkRight,
        bennettTape_write_head]
    have h1 : StepsNoHalt M c c' 1 :=
      StepsNoHalt.single hstep (by rw [hq]; intro _ _ h; cases h)
    have hshift : ∀ k : ℕ, c'.Tape.nth (k : ℤ) = c.Tape.nth ((k + 1 : ℕ) : ℤ) := by
      intro k
      simp only [c', Tape.move_right_nth]
      congr 1
    have h2 := ih c' rfl
      (fun j hj ↦ by rw [hshift j]; exact hlt (j + 1) (Nat.succ_lt_succ hj))
      (by rw [hshift d]; exact hhh)
      (by rw [hshift d]; exact hhm)
      (by rw [hshift d]; exact hwh)
    have hcomb := h1.trans h2
    have heq_len : 1 + (d + 1) = d + 1 + 1 := by omega
    rw [heq_len] at hcomb
    simpa [c', Function.iterate_succ_apply] using hcomb

/-! ### `BennettInv`, Macro-Step Simulation & Terminal Halting Cruise -/

/-- Simulation invariant coupling an active `TM0` configuration `cfg` at absolute work-head
coordinate `posW : ℤ` and history-cursor coordinate `posH : ℤ` to
`rcfg : (bennettReversibleTM M).Cfg`:
* `rcfg.q = .exec cfg.q (compare posW posH)`;
* the work-track projection `(rcfg.Tape.nth i).sym` matches `cfg.Tape.nth i` for all `i : ℤ`;
* `workHead` is `true` solely at `i = 0` (physical coordinate `posW`);
* `histHead` is `true` solely where `posW + i = posH` (physical coordinate `posH`);
* `hist = none` strictly to the left of `posH` (`posW + i < posH`);
* `haltMark = false` everywhere. -/
structure BennettInv (M : FinTM0) (posW posH : ℤ)
    (cfg : TM0.Cfg M.Γ M.Λ) (rcfg : (bennettReversibleTM M).Cfg) : Prop where
  /-- Control state sits in `.exec cfg.q (compare posW posH)`. -/
  q_eq : rcfg.q = .exec cfg.q (compare posW posH)
  /-- Work-track symbols agree globally with `cfg.Tape`. -/
  sym_eq : ∀ i : ℤ, (rcfg.Tape.nth i).sym = cfg.Tape.nth i
  /-- Work-head marker sits uniquely at head offset `0`. -/
  workHead_eq : ∀ i : ℤ, (rcfg.Tape.nth i).workHead = decide (i = 0)
  /-- History-cursor marker sits uniquely at physical coordinate `posH`. -/
  histHead_eq : ∀ i : ℤ, (rcfg.Tape.nth i).histHead = decide (posW + i = posH)
  /-- All cells strictly to the left of `posH` have empty history slots. -/
  hist_none_lt : ∀ i : ℤ, posW + i < posH → (rcfg.Tape.nth i).hist = none
  /-- Post-halt flag is `false` on every cell. -/
  haltMark_false : ∀ i : ℤ, (rcfg.Tape.nth i).haltMark = false

/-- `BennettInv` holds initially at `(posW, posH) = (0, 0)` for `(M.initCfg t, bennettInitCfg M t)`.
-/
-- tier: T1
theorem bennettInv_initCfg (M : FinTM0) (t : FinSupportedTape M) :
    BennettInv M 0 0 (M.initCfg t) (bennettInitCfg M t) where
  q_eq := rfl
  sym_eq i := bennettInitTape_nth_sym M t i
  workHead_eq i := by
    by_cases hi : i = 0
    · subst hi; rfl
    · change ((bennettInitTape M t).nth i).workHead = decide (i = 0)
      rw [bennettInitTape_nth_of_ne_zero M t hi]
      simp [hi]
  histHead_eq i := by
    by_cases hi : i = 0
    · subst hi; rfl
    · change ((bennettInitTape M t).nth i).histHead = decide (0 + i = 0)
      rw [bennettInitTape_nth_of_ne_zero M t hi]
      simp [hi]
  hist_none_lt i _ := by
    by_cases hi : i = 0
    · subst hi; rfl
    · change ((bennettInitTape M t).nth i).hist = none
      rw [bennettInitTape_nth_of_ne_zero M t hi]
  haltMark_false i := by
    by_cases hi : i = 0
    · subst hi; rfl
    · change ((bennettInitTape M t).nth i).haltMark = false
      rw [bennettInitTape_nth_of_ne_zero M t hi]

/-- Intermediate invariant at `.afterExec e (compare posW' posH)` (centered at `posW'`). -/
structure AfterExecInv (M : FinTM0) (posW' posH : ℤ) (e : M.Λ × M.Γ)
    (cfg' : TM0.Cfg M.Γ M.Λ) (rcfg : (bennettReversibleTM M).Cfg) : Prop where
  /-- Control state is `.afterExec e (compare posW' posH)`. -/
  q_eq : rcfg.q = .afterExec e (compare posW' posH)
  /-- Work symbols match `cfg'.Tape`. -/
  sym_eq : ∀ i : ℤ, (rcfg.Tape.nth i).sym = cfg'.Tape.nth i
  /-- Work-head marker is `true` solely at `0`. -/
  workHead_eq : ∀ i : ℤ, (rcfg.Tape.nth i).workHead = decide (i = 0)
  /-- History-cursor marker is `true` solely where `posW' + i = posH`. -/
  histHead_eq : ∀ i : ℤ, (rcfg.Tape.nth i).histHead = decide (posW' + i = posH)
  /-- Cells strictly left of `posH` have `hist = none`. -/
  hist_none_lt : ∀ i : ℤ, posW' + i < posH → (rcfg.Tape.nth i).hist = none
  /-- `haltMark` is `false` everywhere. -/
  haltMark_false : ∀ i : ℤ, (rcfg.Tape.nth i).haltMark = false

/-- Intermediate invariant at `.atHist e (compare posW' posH)` (centered at `posH`). -/
structure AtHistInv (M : FinTM0) (posW' posH : ℤ) (e : M.Λ × M.Γ)
    (cfg' : TM0.Cfg M.Γ M.Λ) (rcfg : (bennettReversibleTM M).Cfg) : Prop where
  /-- Control state is `.atHist e (compare posW' posH)`. -/
  q_eq : rcfg.q = .atHist e (compare posW' posH)
  /-- Work symbols match `cfg'.Tape` shifted by `posH - posW'`. -/
  sym_eq : ∀ i : ℤ, (rcfg.Tape.nth i).sym = cfg'.Tape.nth (posH + i - posW')
  /-- Work-head marker is `true` solely where `posH + i = posW'`. -/
  workHead_eq : ∀ i : ℤ, (rcfg.Tape.nth i).workHead = decide (posH + i = posW')
  /-- History-cursor marker is `true` solely at `0`. -/
  histHead_eq : ∀ i : ℤ, (rcfg.Tape.nth i).histHead = decide (i = 0)
  /-- Cells strictly left of `posH` (`i < 0`) have `hist = none`. -/
  hist_none_lt : ∀ i : ℤ, i < 0 → (rcfg.Tape.nth i).hist = none
  /-- `haltMark` is `false` everywhere. -/
  haltMark_false : ∀ i : ℤ, (rcfg.Tape.nth i).haltMark = false

/-- Intermediate invariant at `.startReturn cfg'.q (compare posW' posH')` (centered at `posH'`). -/
structure StartReturnInv (M : FinTM0) (posW' posH' : ℤ)
    (cfg' : TM0.Cfg M.Γ M.Λ) (rcfg : (bennettReversibleTM M).Cfg) : Prop where
  /-- Control state is `.startReturn cfg'.q (compare posW' posH')`. -/
  q_eq : rcfg.q = .startReturn cfg'.q (compare posW' posH')
  /-- Work symbols match `cfg'.Tape` shifted by `posH' - posW'`. -/
  sym_eq : ∀ i : ℤ, (rcfg.Tape.nth i).sym = cfg'.Tape.nth (posH' + i - posW')
  /-- Work-head marker is `true` solely where `posH' + i = posW'`. -/
  workHead_eq : ∀ i : ℤ, (rcfg.Tape.nth i).workHead = decide (posH' + i = posW')
  /-- History-cursor marker is `true` solely at `0`. -/
  histHead_eq : ∀ i : ℤ, (rcfg.Tape.nth i).histHead = decide (i = 0)
  /-- Cells strictly left of `posH'` (`i < 0`) have `hist = none`. -/
  hist_none_lt : ∀ i : ℤ, i < 0 → (rcfg.Tape.nth i).hist = none
  /-- `haltMark` is `false` everywhere. -/
  haltMark_false : ∀ i : ℤ, (rcfg.Tape.nth i).haltMark = false

/-- Boolean bridge `(decide (a = b) == (compare a b == .eq)) = true` for `a b : ℤ`. -/
-- tier: T1
theorem decide_eq_beq_compare_eq (a b : ℤ) :
    (decide (a = b) == (compare a b == .eq)) = true := by
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · have hne : a ≠ b := ne_of_lt hlt
    have hc : compare a b = .lt := compare_lt_iff_lt.mpr hlt
    simp [hne, hc]
  · simp
  · have hne : a ≠ b := ne_of_gt hgt
    have hc : compare a b = .gt := compare_gt_iff_gt.mpr hgt
    simp [hne, hc]

/-- Phase 1 of a Bennett macro-step: executes `M.machine cfg.q cfg.Tape.head = some (q', stmt)` at
`posW` in `1` (`.write`) or `2` (`.move`) reversible steps, establishing `AfterExecInv`. -/
-- tier: T1
theorem bennett_phase1_exec (M : FinTM0) {posW posH : ℤ}
    {cfg cfg' : TM0.Cfg M.Γ M.Λ} {rcfg : (bennettReversibleTM M).Cfg}
    (hinv : BennettInv M posW posH cfg rcfg)
    (hstep : TM0.step M.machine cfg = some cfg') :
    ∃ m₁ > 0, ∃ posW' rcfg₁,
      AfterExecInv M posW' posH (cfg.q, cfg.Tape.head) cfg' rcfg₁ ∧
      StepsNoHalt M rcfg rcfg₁ m₁ := by
  rcases cfg with ⟨q, T⟩
  simp only [TM0.step] at hstep
  have hhead_sym : rcfg.Tape.head.sym = T.head := hinv.sym_eq 0
  have hwh0 : rcfg.Tape.head.workHead = true := by simpa using hinv.workHead_eq 0
  have hhm0 : rcfg.Tape.head.haltMark = false := hinv.haltMark_false 0
  have hhh0 : rcfg.Tape.head.histHead = decide (posW = posH) := by
    simpa using hinv.histHead_eq 0
  have hguard :
      (rcfg.Tape.head.workHead && !rcfg.Tape.head.haltMark &&
        (rcfg.Tape.head.histHead == (compare posW posH == .eq))) = true := by
    rw [hwh0, hhm0, hhh0]
    simpa using decide_eq_beq_compare_eq posW posH
  rcases hm : M.machine q T.head with _ | ⟨q', (_ | _) | b⟩ <;> rw [hm] at hstep
  · cases hstep
  · -- Branch `Stmt.move Dir.left` (`m₁ = 2`, `posW' = posW - 1`)
    simp only [Option.map_some, Option.some.injEq] at hstep
    subst hstep
    let rMid : Ordering := match compare posW posH with | .gt => .gt | _ => .lt
    let b₁ : (bennettReversibleTM M).Γ := { rcfg.Tape.head with workHead := false }
    have hrule₁ : bennettRule M (rcfg.q, rcfg.Tape.head) =
        some (.moveWorkLeft (q, T.head) rMid, b₁) := by
      rw [hinv.q_eq]
      dsimp only [bennettRule]
      rw [hguard]
      simp only [↓reduceIte, hhead_sym, hm, rMid, b₁]
      rfl
    let rcfg_mid : (bennettReversibleTM M).Cfg :=
      ⟨.moveWorkLeft (q, T.head) rMid, (rcfg.Tape.write b₁).move Dir.left⟩
    have hs₁ : (bennettReversibleTM M).step rcfg = rcfg_mid := by
      rw [bennettReversibleTM_step_of_rule M rcfg hrule₁]
      rfl
    have hseg₁ : StepsNoHalt M rcfg rcfg_mid 1 :=
      StepsNoHalt.single hs₁ (by rw [hinv.q_eq]; intro _ _ h; cases h)
    have hmid_head : rcfg_mid.Tape.head = rcfg.Tape.nth (-1) := by
      change ((rcfg.Tape.write b₁).move Dir.left).nth 0 = _
      rw [Tape.move_left_nth, Tape.write_nth]
      simp
    have hmid_wh : rcfg_mid.Tape.head.workHead = false := by
      rw [hmid_head]; simpa using hinv.workHead_eq (-1)
    have hmid_hm : rcfg_mid.Tape.head.haltMark = false := by
      rw [hmid_head]; exact hinv.haltMark_false (-1)
    have hmid_hh : rcfg_mid.Tape.head.histHead = decide (posW - 1 = posH) := by
      rw [hmid_head]
      have := hinv.histHead_eq (-1)
      have heq : (posW + -1 = posH) ↔ (posW - 1 = posH) := by omega
      simpa [heq] using this
    let b₂ : (bennettReversibleTM M).Γ := { rcfg_mid.Tape.head with workHead := true }
    have hrule₂ : bennettRule M (rcfg_mid.q, rcfg_mid.Tape.head) =
        some (.afterExec (q, T.head) (compare (posW - 1) posH), b₂) := by
      change bennettRule M (.moveWorkLeft (q, T.head) rMid, rcfg_mid.Tape.head) = _
      dsimp only [bennettRule]
      rw [hmid_wh, hmid_hm]
      simp only [Bool.not_false, Bool.true_and, ↓reduceIte, hm]
      rcases lt_trichotomy posW posH with hlt | rfl | hgt
      · have hc0 : compare posW posH = .lt := compare_lt_iff_lt.mpr hlt
        have hc1 : compare (posW - 1) posH = .lt := compare_lt_iff_lt.mpr (by omega)
        have hne1 : posW - 1 ≠ posH := by omega
        rw [hc1]
        simp [rMid, hc0, hmid_hh, hmid_hm, hne1, b₂]
      · have hc1 : compare (posW - 1) posW = .lt := compare_lt_iff_lt.mpr (by omega)
        have hne1 : posW - 1 ≠ posW := by omega
        rw [hc1]
        simp [rMid, hmid_hh, hmid_hm, hne1, b₂]
      · have hc0 : compare posW posH = .gt := compare_gt_iff_gt.mpr hgt
        by_cases heq1 : posW - 1 = posH
        · have hc1 : compare (posW - 1) posH = .eq := compare_eq_iff_eq.mpr heq1
          rw [hc1]
          simp [rMid, hc0, hmid_hh, hmid_hm, heq1, b₂]
        · have hc1 : compare (posW - 1) posH = .gt := compare_gt_iff_gt.mpr (by omega)
          rw [hc1]
          simp [rMid, hc0, hmid_hh, hmid_hm, heq1, b₂]
    let rcfg₁ : (bennettReversibleTM M).Cfg :=
      ⟨.afterExec (q, T.head) (compare (posW - 1) posH), rcfg_mid.Tape.write b₂⟩
    have hs₂ : (bennettReversibleTM M).step rcfg_mid = rcfg₁ := by
      rw [bennettReversibleTM_step_of_rule M rcfg_mid hrule₂]
      rfl
    have hseg₂ : StepsNoHalt M rcfg_mid rcfg₁ 1 :=
      StepsNoHalt.single hs₂ (fun _ _ h ↦ by cases h)
    refine ⟨2, by omega, posW - 1, rcfg₁, ?_, hseg₁.trans hseg₂⟩
    have hnth : ∀ i : ℤ, rcfg₁.Tape.nth i =
        if i = 0 then { rcfg.Tape.nth (-1) with workHead := true }
        else if i = 1 then { rcfg.Tape.nth 0 with workHead := false }
        else rcfg.Tape.nth (i - 1) := by
      intro i
      simp only [rcfg₁, rcfg_mid, Tape.write_nth, Tape.move_left_nth, b₂, b₁]
      by_cases hi0 : i = 0
      · subst hi0; simp
      · by_cases hi1 : i = 1
        · subst hi1; simp [Tape.nth_zero]
        · have hne : i - 1 ≠ 0 := by omega
          simp [hi0, hi1, hne]
    refine ⟨rfl, fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_, fun i hlt ↦ ?_, fun i ↦ ?_⟩
    · rw [hnth i, Tape.move_left_nth]
      split_ifs with hi0 hi1
      · subst hi0; simpa using hinv.sym_eq (-1)
      · subst hi1; simpa [Tape.nth_zero] using hinv.sym_eq 0
      · exact hinv.sym_eq (i - 1)
    · rw [hnth i]
      split_ifs with hi0 hi1
      · simp [hi0]
      · simp [hi0]
      · have hne : i - 1 ≠ 0 := by omega
        simp [hi0, hinv.workHead_eq (i - 1), hne]
    · rw [hnth i]
      have heq_pos : (posW - 1 + i = posH) ↔ (posW + (i - 1) = posH) := by omega
      rw [decide_eq_decide.mpr heq_pos]
      split_ifs with hi0 hi1
      · subst hi0; simpa using hinv.histHead_eq (-1)
      · subst hi1; simpa [Tape.nth_zero] using hinv.histHead_eq 0
      · exact hinv.histHead_eq (i - 1)
    · rw [hnth i]
      have hlt' : posW + (i - 1) < posH := by omega
      split_ifs with hi0 hi1
      · subst hi0; exact hinv.hist_none_lt (-1) (by omega)
      · subst hi1; simpa [Tape.nth_zero] using hinv.hist_none_lt 0 (by omega)
      · exact hinv.hist_none_lt (i - 1) hlt'
    · rw [hnth i]
      split_ifs with hi0 hi1
      · subst hi0; exact hinv.haltMark_false (-1)
      · subst hi1; exact hinv.haltMark_false 0
      · exact hinv.haltMark_false (i - 1)
  · -- Branch `Stmt.move Dir.right` (`m₁ = 2`, `posW' = posW + 1`)
    simp only [Option.map_some, Option.some.injEq] at hstep
    subst hstep
    let rMid : Ordering := match compare posW posH with | .lt => .lt | _ => .gt
    let b₁ : (bennettReversibleTM M).Γ := { rcfg.Tape.head with workHead := false }
    have hrule₁ : bennettRule M (rcfg.q, rcfg.Tape.head) =
        some (.moveWorkRight (q, T.head) rMid, b₁) := by
      rw [hinv.q_eq]
      dsimp only [bennettRule]
      rw [hguard]
      simp only [↓reduceIte, hhead_sym, hm, rMid, b₁]
      rfl
    let rcfg_mid : (bennettReversibleTM M).Cfg :=
      ⟨.moveWorkRight (q, T.head) rMid, (rcfg.Tape.write b₁).move Dir.right⟩
    have hs₁ : (bennettReversibleTM M).step rcfg = rcfg_mid := by
      rw [bennettReversibleTM_step_of_rule M rcfg hrule₁]
      rfl
    have hseg₁ : StepsNoHalt M rcfg rcfg_mid 1 :=
      StepsNoHalt.single hs₁ (by rw [hinv.q_eq]; intro _ _ h; cases h)
    have hmid_head : rcfg_mid.Tape.head = rcfg.Tape.nth 1 := by
      change ((rcfg.Tape.write b₁).move Dir.right).nth 0 = _
      rw [Tape.move_right_nth, Tape.write_nth]
      simp
    have hmid_wh : rcfg_mid.Tape.head.workHead = false := by
      rw [hmid_head]; simpa using hinv.workHead_eq 1
    have hmid_hm : rcfg_mid.Tape.head.haltMark = false := by
      rw [hmid_head]; exact hinv.haltMark_false 1
    have hmid_hh : rcfg_mid.Tape.head.histHead = decide (posW + 1 = posH) := by
      rw [hmid_head]; exact hinv.histHead_eq 1
    let b₂ : (bennettReversibleTM M).Γ := { rcfg_mid.Tape.head with workHead := true }
    have hrule₂ : bennettRule M (rcfg_mid.q, rcfg_mid.Tape.head) =
        some (.afterExec (q, T.head) (compare (posW + 1) posH), b₂) := by
      change bennettRule M (.moveWorkRight (q, T.head) rMid, rcfg_mid.Tape.head) = _
      dsimp only [bennettRule]
      rw [hmid_wh, hmid_hm]
      simp only [Bool.not_false, Bool.true_and, ↓reduceIte, hm]
      rcases lt_trichotomy posW posH with hlt | rfl | hgt
      · have hc0 : compare posW posH = .lt := compare_lt_iff_lt.mpr hlt
        by_cases heq1 : posW + 1 = posH
        · have hc1 : compare (posW + 1) posH = .eq := compare_eq_iff_eq.mpr heq1
          rw [hc1]
          simp [rMid, hc0, hmid_hh, hmid_hm, heq1, b₂]
        · have hc1 : compare (posW + 1) posH = .lt := compare_lt_iff_lt.mpr (by omega)
          rw [hc1]
          simp [rMid, hc0, hmid_hh, hmid_hm, heq1, b₂]
      · have hc1 : compare (posW + 1) posW = .gt := compare_gt_iff_gt.mpr (by omega)
        have hne1 : posW + 1 ≠ posW := by omega
        rw [hc1]
        simp [rMid, hmid_hh, hmid_hm, hne1, b₂]
      · have hc0 : compare posW posH = .gt := compare_gt_iff_gt.mpr hgt
        have hc1 : compare (posW + 1) posH = .gt := compare_gt_iff_gt.mpr (by omega)
        have hne1 : posW + 1 ≠ posH := by omega
        rw [hc1]
        simp [rMid, hc0, hmid_hh, hmid_hm, hne1, b₂]
    let rcfg₁ : (bennettReversibleTM M).Cfg :=
      ⟨.afterExec (q, T.head) (compare (posW + 1) posH), rcfg_mid.Tape.write b₂⟩
    have hs₂ : (bennettReversibleTM M).step rcfg_mid = rcfg₁ := by
      rw [bennettReversibleTM_step_of_rule M rcfg_mid hrule₂]
      rfl
    have hseg₂ : StepsNoHalt M rcfg_mid rcfg₁ 1 :=
      StepsNoHalt.single hs₂ (fun _ _ h ↦ by cases h)
    refine ⟨2, by omega, posW + 1, rcfg₁, ?_, hseg₁.trans hseg₂⟩
    have hnth : ∀ i : ℤ, rcfg₁.Tape.nth i =
        if i = 0 then { rcfg.Tape.nth 1 with workHead := true }
        else if i = -1 then { rcfg.Tape.nth 0 with workHead := false }
        else rcfg.Tape.nth (i + 1) := by
      intro i
      simp only [rcfg₁, rcfg_mid, Tape.write_nth, Tape.move_right_nth, b₂, b₁]
      by_cases hi0 : i = 0
      · subst hi0; simp
      · by_cases hin1 : i = -1
        · subst hin1; simp [Tape.nth_zero]
        · have hne : i + 1 ≠ 0 := by omega
          simp [hi0, hin1, hne]
    refine ⟨rfl, fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_, fun i hlt ↦ ?_, fun i ↦ ?_⟩
    · rw [hnth i, Tape.move_right_nth]
      split_ifs with hi0 hin1
      · subst hi0; simpa using hinv.sym_eq 1
      · subst hin1; simpa [Tape.nth_zero] using hinv.sym_eq 0
      · exact hinv.sym_eq (i + 1)
    · rw [hnth i]
      split_ifs with hi0 hin1
      · simp [hi0]
      · simp [hi0]
      · have hne : i + 1 ≠ 0 := by omega
        simp [hi0, hinv.workHead_eq (i + 1), hne]
    · rw [hnth i]
      have heq_pos : (posW + 1 + i = posH) ↔ (posW + (i + 1) = posH) := by omega
      rw [decide_eq_decide.mpr heq_pos]
      split_ifs with hi0 hin1
      · subst hi0; simpa using hinv.histHead_eq 1
      · subst hin1; simpa [Tape.nth_zero] using hinv.histHead_eq 0
      · exact hinv.histHead_eq (i + 1)
    · rw [hnth i]
      have hlt' : posW + (i + 1) < posH := by omega
      split_ifs with hi0 hin1
      · subst hi0; exact hinv.hist_none_lt 1 (by omega)
      · subst hin1; simpa [Tape.nth_zero] using hinv.hist_none_lt 0 (by omega)
      · exact hinv.hist_none_lt (i + 1) hlt'
    · rw [hnth i]
      split_ifs with hi0 hin1
      · subst hi0; exact hinv.haltMark_false 1
      · subst hin1; exact hinv.haltMark_false 0
      · exact hinv.haltMark_false (i + 1)
  · -- Branch `Stmt.write b` (`m₁ = 1`, `posW' = posW`)
    simp only [Option.map_some, Option.some.injEq] at hstep
    subst hstep
    let b₁ : (bennettReversibleTM M).Γ := { rcfg.Tape.head with sym := b }
    have hrule₁ : bennettRule M (rcfg.q, rcfg.Tape.head) =
        some (.afterExec (q, T.head) (compare posW posH), b₁) := by
      rw [hinv.q_eq]
      dsimp only [bennettRule]
      rw [hguard]
      simp only [↓reduceIte, hhead_sym, hm, b₁]
    let rcfg₁ : (bennettReversibleTM M).Cfg :=
      ⟨.afterExec (q, T.head) (compare posW posH), rcfg.Tape.write b₁⟩
    have hs₁ : (bennettReversibleTM M).step rcfg = rcfg₁ := by
      rw [bennettReversibleTM_step_of_rule M rcfg hrule₁]
      rfl
    refine ⟨1, by omega, posW, rcfg₁, ?_,
      StepsNoHalt.single hs₁ (by rw [hinv.q_eq]; intro _ _ h; cases h)⟩
    refine ⟨rfl, fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_, fun i hlt ↦ ?_, fun i ↦ ?_⟩
    · simp only [rcfg₁, Tape.write_nth, b₁]
      split_ifs with hi0
      · rfl
      · exact hinv.sym_eq i
    · simp only [rcfg₁, Tape.write_nth, b₁]
      split_ifs with hi0
      · subst hi0; exact hwh0
      · exact hinv.workHead_eq i
    · simp only [rcfg₁, Tape.write_nth, b₁]
      split_ifs with hi0
      · subst hi0; simpa using hinv.histHead_eq 0
      · exact hinv.histHead_eq i
    · simp only [rcfg₁, Tape.write_nth, b₁]
      split_ifs with hi0
      · subst hi0; exact hinv.hist_none_lt 0 hlt
      · exact hinv.hist_none_lt i hlt
    · simp only [rcfg₁, Tape.write_nth, b₁]
      split_ifs with hi0
      · subst hi0; exact hhm0
      · exact hinv.haltMark_false i

/-- Phase 2 of a Bennett macro-step: walks from `AfterExecInv` (centered at `posW'`) to
`AtHistInv` (centered at `posH`). -/
-- tier: T1
theorem bennett_phase2_seekHist (M : FinTM0) {posW' posH : ℤ} {e : M.Λ × M.Γ}
    {cfg' : TM0.Cfg M.Γ M.Λ} {rcfg₁ : (bennettReversibleTM M).Cfg}
    (he : (M.machine e.1 e.2).isSome = true)
    (hinv : AfterExecInv M posW' posH e cfg' rcfg₁) :
    ∃ m₂ > 0, ∃ rcfg₂,
      AtHistInv M posW' posH e cfg' rcfg₂ ∧
      StepsNoHalt M rcfg₁ rcfg₂ m₂ := by
  have hwh0 : rcfg₁.Tape.head.workHead = true := by simpa using hinv.workHead_eq 0
  have hhm0 : rcfg₁.Tape.head.haltMark = false := hinv.haltMark_false 0
  have hhh0 : rcfg₁.Tape.head.histHead = decide (posW' = posH) := by
    simpa using hinv.histHead_eq 0
  have hguard :
      (rcfg₁.Tape.head.workHead && !rcfg₁.Tape.head.haltMark &&
        (rcfg₁.Tape.head.histHead == (compare posW' posH == .eq)) &&
        (M.machine e.1 e.2).isSome) = true := by
    rw [hwh0, hhm0, hhh0, he]
    simpa using decide_eq_beq_compare_eq posW' posH
  rcases lt_trichotomy posW' posH with hlt | rfl | hgt
  · -- `posW' < posH`: step `.right` into `seekHistRight` and walk `d` steps right
    have hc : compare posW' posH = .lt := compare_lt_iff_lt.mpr hlt
    have hrule : bennettRule M (rcfg₁.q, rcfg₁.Tape.head) =
        some (.seekHistRight e, rcfg₁.Tape.head) := by
      rw [hinv.q_eq, hc]
      dsimp only [bennettRule]
      rw [hc] at hguard
      rw [hguard]
      rfl
    let c_start : (bennettReversibleTM M).Cfg := ⟨.seekHistRight e, rcfg₁.Tape.move Dir.right⟩
    have hs : (bennettReversibleTM M).step rcfg₁ = c_start := by
      rw [bennettReversibleTM_step_of_rule M rcfg₁ hrule, bennettDirIn_seekHistRight,
        bennettTape_write_head]
    have h1 : StepsNoHalt M rcfg₁ c_start 1 :=
      StepsNoHalt.single hs (by rw [hinv.q_eq]; intro _ _ h; cases h)
    let d : ℕ := (posH - (posW' + 1)).toNat
    have hd_eq : (d : ℤ) = posH - (posW' + 1) := Int.toNat_of_nonneg (by omega)
    have hwalk := bennett_walk_seekHistRight M e he d c_start rfl
      (fun j hj ↦ by
        simp only [c_start, Tape.move_right_nth]
        refine ⟨?_, hinv.haltMark_false ((j : ℤ) + 1), ?_⟩
        · simpa [show ((j : ℤ) + 1) ≠ 0 by omega] using hinv.workHead_eq ((j : ℤ) + 1)
        · have hne : posW' + ((j : ℤ) + 1) ≠ posH := by omega
          simpa [hne] using hinv.histHead_eq ((j : ℤ) + 1))
      (by
        simp only [c_start, Tape.move_right_nth]
        simpa [show ((d : ℤ) + 1) ≠ 0 by omega] using hinv.workHead_eq ((d : ℤ) + 1))
      (by simp only [c_start, Tape.move_right_nth]; exact hinv.haltMark_false ((d : ℤ) + 1))
      (by
        simp only [c_start, Tape.move_right_nth]
        have heq_pos : posW' + ((d : ℤ) + 1) = posH := by omega
        simpa [heq_pos] using hinv.histHead_eq ((d : ℤ) + 1))
    let rcfg₂ : (bennettReversibleTM M).Cfg :=
      ⟨.atHist e .lt, (Tape.move Dir.right)^[d] c_start.Tape⟩
    refine ⟨1 + (d + 1), by omega, rcfg₂, ?_, h1.trans hwalk⟩
    have hnth : ∀ i : ℤ, rcfg₂.Tape.nth i = rcfg₁.Tape.nth (posH + i - posW') := by
      intro i
      simp only [rcfg₂, c_start, tape_iterate_move_right_nth, Tape.move_right_nth]
      congr 1
      omega
    refine ⟨hc.symm ▸ rfl, fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_, fun i hi ↦ ?_, fun i ↦ ?_⟩
    · rw [hnth i, hinv.sym_eq]
    · rw [hnth i, hinv.workHead_eq]
      exact decide_eq_decide.mpr (by omega)
    · rw [hnth i, hinv.histHead_eq]
      exact decide_eq_decide.mpr (by omega)
    · rw [hnth i]
      exact hinv.hist_none_lt _ (by omega)
    · rw [hnth i]
      exact hinv.haltMark_false _
  · -- `posW' = posH`: 1 `.stay` step directly to `.atHist e .eq`
    have hc : compare posW' posW' = .eq := compare_eq_iff_eq.mpr rfl
    have hrule : bennettRule M (rcfg₁.q, rcfg₁.Tape.head) =
        some (.atHist e .eq, rcfg₁.Tape.head) := by
      rw [hinv.q_eq, hc]
      dsimp only [bennettRule]
      rw [hc] at hguard
      rw [hguard]
      rfl
    let rcfg₂ : (bennettReversibleTM M).Cfg := ⟨.atHist e .eq, rcfg₁.Tape⟩
    have hs : (bennettReversibleTM M).step rcfg₁ = rcfg₂ := by
      rw [bennettReversibleTM_step_of_rule M rcfg₁ hrule, bennettDirIn_atHist,
        bennettTape_write_head]
    refine ⟨1, by omega, rcfg₂, ?_,
      StepsNoHalt.single hs (by rw [hinv.q_eq]; intro _ _ h; cases h)⟩
    refine ⟨hc.symm ▸ rfl, fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_, fun i hi ↦ ?_, fun i ↦ ?_⟩
    · simpa [rcfg₂] using hinv.sym_eq i
    · simpa [rcfg₂] using hinv.workHead_eq i
    · simpa [rcfg₂] using hinv.histHead_eq i
    · exact hinv.hist_none_lt i (by omega)
    · exact hinv.haltMark_false i
  · -- `posW' > posH`: step `.left` into `seekHistLeft` and walk `d` steps left
    have hc : compare posW' posH = .gt := compare_gt_iff_gt.mpr hgt
    have hrule : bennettRule M (rcfg₁.q, rcfg₁.Tape.head) =
        some (.seekHistLeft e, rcfg₁.Tape.head) := by
      rw [hinv.q_eq, hc]
      dsimp only [bennettRule]
      rw [hc] at hguard
      rw [hguard]
      rfl
    let c_start : (bennettReversibleTM M).Cfg := ⟨.seekHistLeft e, rcfg₁.Tape.move Dir.left⟩
    have hs : (bennettReversibleTM M).step rcfg₁ = c_start := by
      rw [bennettReversibleTM_step_of_rule M rcfg₁ hrule, bennettDirIn_seekHistLeft,
        bennettTape_write_head]
    have h1 : StepsNoHalt M rcfg₁ c_start 1 :=
      StepsNoHalt.single hs (by rw [hinv.q_eq]; intro _ _ h; cases h)
    let d : ℕ := ((posW' - 1) - posH).toNat
    have hd_eq : (d : ℤ) = (posW' - 1) - posH := Int.toNat_of_nonneg (by omega)
    have hwalk := bennett_walk_seekHistLeft M e he d c_start rfl
      (fun j hj ↦ by
        simp only [c_start, Tape.move_left_nth]
        refine ⟨?_, hinv.haltMark_false (-(j : ℤ) - 1), ?_⟩
        · simpa [show (-(j : ℤ) - 1) ≠ 0 by omega] using hinv.workHead_eq (-(j : ℤ) - 1)
        · have hne : posW' + (-(j : ℤ) - 1) ≠ posH := by omega
          simpa [hne] using hinv.histHead_eq (-(j : ℤ) - 1))
      (by
        simp only [c_start, Tape.move_left_nth]
        simpa [show (-(d : ℤ) - 1) ≠ 0 by omega] using hinv.workHead_eq (-(d : ℤ) - 1))
      (by simp only [c_start, Tape.move_left_nth]; exact hinv.haltMark_false (-(d : ℤ) - 1))
      (by
        simp only [c_start, Tape.move_left_nth]
        have heq_pos : posW' + (-(d : ℤ) - 1) = posH := by omega
        simpa [heq_pos] using hinv.histHead_eq (-(d : ℤ) - 1))
    let rcfg₂ : (bennettReversibleTM M).Cfg :=
      ⟨.atHist e .gt, (Tape.move Dir.left)^[d] c_start.Tape⟩
    refine ⟨1 + (d + 1), by omega, rcfg₂, ?_, h1.trans hwalk⟩
    have hnth : ∀ i : ℤ, rcfg₂.Tape.nth i = rcfg₁.Tape.nth (posH + i - posW') := by
      intro i
      simp only [rcfg₂, c_start, tape_iterate_move_left_nth, Tape.move_left_nth]
      congr 1
      omega
    refine ⟨hc.symm ▸ rfl, fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_, fun i hi ↦ ?_, fun i ↦ ?_⟩
    · rw [hnth i, hinv.sym_eq]
    · rw [hnth i, hinv.workHead_eq]
      exact decide_eq_decide.mpr (by omega)
    · rw [hnth i, hinv.histHead_eq]
      exact decide_eq_decide.mpr (by omega)
    · rw [hnth i]
      exact hinv.hist_none_lt _ (by omega)
    · rw [hnth i]
      exact hinv.haltMark_false _

/-- Phase 3 of a Bennett macro-step: steps the history cursor from `posH` to `posH - 1`, writes
`some e` into the fresh history slot at `posH - 1`, and establishes `StartReturnInv` in `2` steps.
-/
-- tier: T1
theorem bennett_phase3_recordHist (M : FinTM0) {posW' posH : ℤ} {e : M.Λ × M.Γ}
    {stmt : TM0.Stmt M.Γ} {cfg' : TM0.Cfg M.Γ M.Λ} {rcfg₂ : (bennettReversibleTM M).Cfg}
    (hm : M.machine e.1 e.2 = some (cfg'.q, stmt))
    (hinv : AtHistInv M posW' posH e cfg' rcfg₂) :
    ∃ rcfg₃,
      StartReturnInv M posW' (posH - 1) cfg' rcfg₃ ∧
      StepsNoHalt M rcfg₂ rcfg₃ 2 := by
  have he : (M.machine e.1 e.2).isSome = true := by simp [hm]
  have hhh0 : rcfg₂.Tape.head.histHead = true := by simpa using hinv.histHead_eq 0
  have hhm0 : rcfg₂.Tape.head.haltMark = false := hinv.haltMark_false 0
  have hwh0 : rcfg₂.Tape.head.workHead = decide (posW' = posH) := by
    change (rcfg₂.Tape.nth 0).workHead = _
    rw [hinv.workHead_eq 0]
    exact decide_eq_decide.mpr (by omega)
  have hguard₁ :
      (rcfg₂.Tape.head.histHead && !rcfg₂.Tape.head.haltMark &&
        (rcfg₂.Tape.head.workHead == (compare posW' posH == .eq)) &&
        (M.machine e.1 e.2).isSome) = true := by
    rw [hhh0, hhm0, hwh0, he]
    simpa using decide_eq_beq_compare_eq posW' posH
  let rMid : Ordering := match compare posW' posH with | .lt => .lt | _ => .gt
  let b₁ : (bennettReversibleTM M).Γ := { rcfg₂.Tape.head with histHead := false }
  have hrule₁ : bennettRule M (rcfg₂.q, rcfg₂.Tape.head) =
      some (.stepHistLeft e rMid, b₁) := by
    rw [hinv.q_eq]
    dsimp only [bennettRule]
    rw [hguard₁]
    simp only [↓reduceIte, rMid, b₁]
    rfl
  let c_mid : (bennettReversibleTM M).Cfg :=
    ⟨.stepHistLeft e rMid, (rcfg₂.Tape.write b₁).move Dir.left⟩
  have hs₁ : (bennettReversibleTM M).step rcfg₂ = c_mid := by
    rw [bennettReversibleTM_step_of_rule M rcfg₂ hrule₁]
    rfl
  have hseg₁ : StepsNoHalt M rcfg₂ c_mid 1 :=
    StepsNoHalt.single hs₁ (by rw [hinv.q_eq]; intro _ _ h; cases h)
  have hmid_head : c_mid.Tape.head = rcfg₂.Tape.nth (-1) := by
    change ((rcfg₂.Tape.write b₁).move Dir.left).nth 0 = _
    rw [Tape.move_left_nth, Tape.write_nth]
    simp
  have hmid_hist : c_mid.Tape.head.hist = none := by
    rw [hmid_head]; exact hinv.hist_none_lt (-1) (by omega)
  have hmid_hh : c_mid.Tape.head.histHead = false := by
    rw [hmid_head]; simpa using hinv.histHead_eq (-1)
  have hmid_hm : c_mid.Tape.head.haltMark = false := by
    rw [hmid_head]; exact hinv.haltMark_false (-1)
  have hmid_wh : c_mid.Tape.head.workHead = decide (posW' = posH - 1) := by
    rw [hmid_head, hinv.workHead_eq (-1)]
    exact decide_eq_decide.mpr (by omega)
  let b₂ : (bennettReversibleTM M).Γ := { c_mid.Tape.head with hist := some e, histHead := true }
  have hrule₂ : bennettRule M (c_mid.q, c_mid.Tape.head) =
      some (.startReturn cfg'.q (compare posW' (posH - 1)), b₂) := by
    change bennettRule M (.stepHistLeft e rMid, c_mid.Tape.head) = _
    dsimp only [bennettRule]
    rw [hmid_hist, hmid_hh, hmid_hm]
    simp only [Option.isNone_none, Bool.not_false, Bool.and_self, ↓reduceIte, hm]
    rcases lt_trichotomy posW' posH with hlt | rfl | hgt
    · have hc0 : compare posW' posH = .lt := compare_lt_iff_lt.mpr hlt
      have hrMid : rMid = .lt := by simp [rMid, hc0]
      rw [hrMid]
      by_cases heq1 : posW' = posH - 1
      · have hc1 : compare posW' (posH - 1) = .eq := compare_eq_iff_eq.mpr heq1
        rw [hc1]
        simp [hmid_wh, hmid_hm, heq1, b₂]
      · have hc1 : compare posW' (posH - 1) = .lt := compare_lt_iff_lt.mpr (by omega)
        rw [hc1]
        simp [hmid_wh, hmid_hm, heq1, b₂]
    · have hc1 : compare posW' (posW' - 1) = .gt := compare_gt_iff_gt.mpr (by omega)
      have hne1 : posW' ≠ posW' - 1 := by omega
      rw [hc1]
      simp [rMid, hmid_wh, hmid_hm, hne1, b₂]
    · have hc0 : compare posW' posH = .gt := compare_gt_iff_gt.mpr hgt
      have hc1 : compare posW' (posH - 1) = .gt := compare_gt_iff_gt.mpr (by omega)
      have hne1 : posW' ≠ posH - 1 := by omega
      rw [hc1]
      simp [rMid, hc0, hmid_wh, hmid_hm, hne1, b₂]
  let rcfg₃ : (bennettReversibleTM M).Cfg :=
    ⟨.startReturn cfg'.q (compare posW' (posH - 1)), c_mid.Tape.write b₂⟩
  have hs₂ : (bennettReversibleTM M).step c_mid = rcfg₃ := by
    rw [bennettReversibleTM_step_of_rule M c_mid hrule₂]
    rfl
  have hseg₂ : StepsNoHalt M c_mid rcfg₃ 1 :=
    StepsNoHalt.single hs₂ (fun _ _ h ↦ by cases h)
  refine ⟨rcfg₃, ?_, hseg₁.trans hseg₂⟩
  have hnth : ∀ i : ℤ, rcfg₃.Tape.nth i =
      if i = 0 then { rcfg₂.Tape.nth (-1) with hist := some e, histHead := true }
      else if i = 1 then { rcfg₂.Tape.nth 0 with histHead := false }
      else rcfg₂.Tape.nth (i - 1) := by
    intro i
    simp only [rcfg₃, c_mid, Tape.write_nth, Tape.move_left_nth, b₂, b₁]
    by_cases hi0 : i = 0
    · subst hi0; simp
    · by_cases hi1 : i = 1
      · subst hi1; simp [Tape.nth_zero]
      · have hne : i - 1 ≠ 0 := by omega
        simp [hi0, hi1, hne]
  refine ⟨rfl, fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_, fun i hi ↦ ?_, fun i ↦ ?_⟩
  · rw [hnth i]
    have hidx : posH - 1 + i - posW' = posH + (i - 1) - posW' := by omega
    rw [hidx]
    split_ifs with hi0 hi1
    · subst hi0; simpa using hinv.sym_eq (-1)
    · subst hi1; simpa [Tape.nth_zero] using hinv.sym_eq 0
    · exact hinv.sym_eq (i - 1)
  · rw [hnth i]
    have heq_pos : (posH - 1 + i = posW') ↔ (posH + (i - 1) = posW') := by omega
    rw [decide_eq_decide.mpr heq_pos]
    split_ifs with hi0 hi1
    · subst hi0; simpa using hinv.workHead_eq (-1)
    · subst hi1; simpa [Tape.nth_zero] using hinv.workHead_eq 0
    · exact hinv.workHead_eq (i - 1)
  · rw [hnth i]
    split_ifs with hi0 hi1
    · simp [hi0]
    · simp [hi0]
    · have hne : i - 1 ≠ 0 := by omega
      simp [hi0, hinv.histHead_eq (i - 1), hne]
  · rw [hnth i]
    have hi0 : i ≠ 0 := by omega
    have hi1 : i ≠ 1 := by omega
    simp only [hi0, hi1, ↓reduceIte]
    exact hinv.hist_none_lt (i - 1) (by omega)
  · rw [hnth i]
    split_ifs with hi0 hi1
    · subst hi0; exact hinv.haltMark_false (-1)
    · subst hi1; exact hinv.haltMark_false 0
    · exact hinv.haltMark_false (i - 1)

/-- Phase 4 of a Bennett macro-step: walks from `StartReturnInv` (centered at `posH'`) back to
`posW'`, re-establishing `BennettInv M posW' posH' cfg' rcfg'`. -/
-- tier: T1
theorem bennett_phase4_returnWork (M : FinTM0) {posW' posH' : ℤ}
    {cfg' : TM0.Cfg M.Γ M.Λ} {rcfg₃ : (bennettReversibleTM M).Cfg}
    (hinv : StartReturnInv M posW' posH' cfg' rcfg₃) :
    ∃ m₄ > 0, ∃ rcfg₄,
      BennettInv M posW' posH' cfg' rcfg₄ ∧
      StepsNoHalt M rcfg₃ rcfg₄ m₄ := by
  have hhh0 : rcfg₃.Tape.head.histHead = true := by simpa using hinv.histHead_eq 0
  have hhm0 : rcfg₃.Tape.head.haltMark = false := hinv.haltMark_false 0
  have hwh0 : rcfg₃.Tape.head.workHead = decide (posW' = posH') := by
    change (rcfg₃.Tape.nth 0).workHead = _
    rw [hinv.workHead_eq 0]
    exact decide_eq_decide.mpr (by omega)
  have hguard :
      (rcfg₃.Tape.head.histHead && !rcfg₃.Tape.head.haltMark &&
        (rcfg₃.Tape.head.workHead == (compare posW' posH' == .eq))) = true := by
    rw [hhh0, hhm0, hwh0]
    simpa using decide_eq_beq_compare_eq posW' posH'
  rcases lt_trichotomy posW' posH' with hlt | rfl | hgt
  · -- `posW' < posH'`: step `.left` into `seekWorkLeft` and walk `d` steps left
    have hc : compare posW' posH' = .lt := compare_lt_iff_lt.mpr hlt
    have hrule : bennettRule M (rcfg₃.q, rcfg₃.Tape.head) =
        some (.seekWorkLeft cfg'.q, rcfg₃.Tape.head) := by
      rw [hinv.q_eq, hc]
      dsimp only [bennettRule]
      rw [hc] at hguard
      rw [hguard]
      rfl
    let c_start : (bennettReversibleTM M).Cfg := ⟨.seekWorkLeft cfg'.q, rcfg₃.Tape.move Dir.left⟩
    have hs : (bennettReversibleTM M).step rcfg₃ = c_start := by
      rw [bennettReversibleTM_step_of_rule M rcfg₃ hrule, bennettDirIn_seekWorkLeft,
        bennettTape_write_head]
    have h1 : StepsNoHalt M rcfg₃ c_start 1 :=
      StepsNoHalt.single hs (by rw [hinv.q_eq]; intro _ _ h; cases h)
    let d : ℕ := ((posH' - 1) - posW').toNat
    have hd_eq : (d : ℤ) = (posH' - 1) - posW' := Int.toNat_of_nonneg (by omega)
    have hwalk := bennett_walk_seekWorkLeft M cfg'.q d c_start rfl
      (fun j hj ↦ by
        simp only [c_start, Tape.move_left_nth]
        refine ⟨?_, hinv.haltMark_false (-(j : ℤ) - 1), ?_⟩
        · simpa [show (-(j : ℤ) - 1) ≠ 0 by omega] using hinv.histHead_eq (-(j : ℤ) - 1)
        · have hne : posH' + (-(j : ℤ) - 1) ≠ posW' := by omega
          simpa [hne] using hinv.workHead_eq (-(j : ℤ) - 1))
      (by
        simp only [c_start, Tape.move_left_nth]
        simpa [show (-(d : ℤ) - 1) ≠ 0 by omega] using hinv.histHead_eq (-(d : ℤ) - 1))
      (by simp only [c_start, Tape.move_left_nth]; exact hinv.haltMark_false (-(d : ℤ) - 1))
      (by
        simp only [c_start, Tape.move_left_nth]
        have heq_pos : posH' + (-(d : ℤ) - 1) = posW' := by omega
        simpa [heq_pos] using hinv.workHead_eq (-(d : ℤ) - 1))
    let rcfg₄ : (bennettReversibleTM M).Cfg :=
      ⟨.exec cfg'.q .lt, (Tape.move Dir.left)^[d] c_start.Tape⟩
    refine ⟨1 + (d + 1), by omega, rcfg₄, ?_, h1.trans hwalk⟩
    have hnth : ∀ i : ℤ, rcfg₄.Tape.nth i = rcfg₃.Tape.nth (posW' + i - posH') := by
      intro i
      simp only [rcfg₄, c_start, tape_iterate_move_left_nth, Tape.move_left_nth]
      congr 1
      omega
    refine ⟨hc.symm ▸ rfl, fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_, fun i hi ↦ ?_, fun i ↦ ?_⟩
    · rw [hnth i, hinv.sym_eq]
      congr 1
      omega
    · rw [hnth i, hinv.workHead_eq]
      exact decide_eq_decide.mpr (by omega)
    · rw [hnth i, hinv.histHead_eq]
      exact decide_eq_decide.mpr (by omega)
    · rw [hnth i]
      exact hinv.hist_none_lt _ (by omega)
    · rw [hnth i]
      exact hinv.haltMark_false _
  · -- `posW' = posH'`: 1 `.stay` step directly to `.exec cfg'.q .eq`
    have hc : compare posW' posW' = .eq := compare_eq_iff_eq.mpr rfl
    have hrule : bennettRule M (rcfg₃.q, rcfg₃.Tape.head) =
        some (.exec cfg'.q .eq, rcfg₃.Tape.head) := by
      rw [hinv.q_eq, hc]
      dsimp only [bennettRule]
      rw [hc] at hguard
      rw [hguard]
      rfl
    let rcfg₄ : (bennettReversibleTM M).Cfg := ⟨.exec cfg'.q .eq, rcfg₃.Tape⟩
    have hs : (bennettReversibleTM M).step rcfg₃ = rcfg₄ := by
      rw [bennettReversibleTM_step_of_rule M rcfg₃ hrule, bennettDirIn_exec,
        bennettTape_write_head]
    refine ⟨1, by omega, rcfg₄, ?_,
      StepsNoHalt.single hs (by rw [hinv.q_eq]; intro _ _ h; cases h)⟩
    refine ⟨hc.symm ▸ rfl, fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_, fun i hi ↦ ?_, fun i ↦ ?_⟩
    · simpa [rcfg₄] using hinv.sym_eq i
    · simpa [rcfg₄] using hinv.workHead_eq i
    · simpa [rcfg₄] using hinv.histHead_eq i
    · exact hinv.hist_none_lt i (by omega)
    · exact hinv.haltMark_false i
  · -- `posW' > posH'`: step `.right` into `seekWorkRight` and walk `d` steps right
    have hc : compare posW' posH' = .gt := compare_gt_iff_gt.mpr hgt
    have hrule : bennettRule M (rcfg₃.q, rcfg₃.Tape.head) =
        some (.seekWorkRight cfg'.q, rcfg₃.Tape.head) := by
      rw [hinv.q_eq, hc]
      dsimp only [bennettRule]
      rw [hc] at hguard
      rw [hguard]
      rfl
    let c_start : (bennettReversibleTM M).Cfg := ⟨.seekWorkRight cfg'.q, rcfg₃.Tape.move Dir.right⟩
    have hs : (bennettReversibleTM M).step rcfg₃ = c_start := by
      rw [bennettReversibleTM_step_of_rule M rcfg₃ hrule, bennettDirIn_seekWorkRight,
        bennettTape_write_head]
    have h1 : StepsNoHalt M rcfg₃ c_start 1 :=
      StepsNoHalt.single hs (by rw [hinv.q_eq]; intro _ _ h; cases h)
    let d : ℕ := (posW' - (posH' + 1)).toNat
    have hd_eq : (d : ℤ) = posW' - (posH' + 1) := Int.toNat_of_nonneg (by omega)
    have hwalk := bennett_walk_seekWorkRight M cfg'.q d c_start rfl
      (fun j hj ↦ by
        simp only [c_start, Tape.move_right_nth]
        refine ⟨?_, hinv.haltMark_false ((j : ℤ) + 1), ?_⟩
        · simpa [show ((j : ℤ) + 1) ≠ 0 by omega] using hinv.histHead_eq ((j : ℤ) + 1)
        · have hne : posH' + ((j : ℤ) + 1) ≠ posW' := by omega
          simpa [hne] using hinv.workHead_eq ((j : ℤ) + 1))
      (by
        simp only [c_start, Tape.move_right_nth]
        simpa [show ((d : ℤ) + 1) ≠ 0 by omega] using hinv.histHead_eq ((d : ℤ) + 1))
      (by simp only [c_start, Tape.move_right_nth]; exact hinv.haltMark_false ((d : ℤ) + 1))
      (by
        simp only [c_start, Tape.move_right_nth]
        have heq_pos : posH' + ((d : ℤ) + 1) = posW' := by omega
        simpa [heq_pos] using hinv.workHead_eq ((d : ℤ) + 1))
    let rcfg₄ : (bennettReversibleTM M).Cfg :=
      ⟨.exec cfg'.q .gt, (Tape.move Dir.right)^[d] c_start.Tape⟩
    refine ⟨1 + (d + 1), by omega, rcfg₄, ?_, h1.trans hwalk⟩
    have hnth : ∀ i : ℤ, rcfg₄.Tape.nth i = rcfg₃.Tape.nth (posW' + i - posH') := by
      intro i
      simp only [rcfg₄, c_start, tape_iterate_move_right_nth, Tape.move_right_nth]
      congr 1
      omega
    refine ⟨hc.symm ▸ rfl, fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_, fun i hi ↦ ?_, fun i ↦ ?_⟩
    · rw [hnth i, hinv.sym_eq]
      congr 1
      omega
    · rw [hnth i, hinv.workHead_eq]
      exact decide_eq_decide.mpr (by omega)
    · rw [hnth i, hinv.histHead_eq]
      exact decide_eq_decide.mpr (by omega)
    · rw [hnth i]
      exact hinv.hist_none_lt _ (by omega)
    · rw [hnth i]
      exact hinv.haltMark_false _

/-- **Bennett Active Macro-Step (`UNCONDITIONAL`)**:
Every active single step `TM0.step M.machine cfg = some cfg'` from `BennettInv M posW posH cfg rcfg`
is simulated by `m > 0` reversible steps of `bennettReversibleTM M` advancing `posH` to `posH - 1`
without ever visiting `.halted _ _` at any intermediate step `j < m`. -/
-- tier: T2
theorem bennett_macroStep (M : FinTM0) {posW posH : ℤ}
    {cfg cfg' : TM0.Cfg M.Γ M.Λ} {rcfg : (bennettReversibleTM M).Cfg}
    (hinv : BennettInv M posW posH cfg rcfg)
    (hstep : TM0.step M.machine cfg = some cfg') :
    ∃ m > 0, ∃ posW' rcfg',
      BennettInv M posW' (posH - 1) cfg' rcfg' ∧
      (bennettReversibleTM M).step^[m] rcfg = rcfg' ∧
      ∀ j < m, ∀ q rel, ((bennettReversibleTM M).step^[j] rcfg).q ≠ .halted q rel := by
  have hm_eq : ∃ stmt, M.machine cfg.q cfg.Tape.head = some (cfg'.q, stmt) := by
    rcases cfg with ⟨q, T⟩
    simp only [TM0.step] at hstep
    rcases hm : M.machine q T.head with _ | ⟨q', stmt⟩ <;> rw [hm] at hstep
    · cases hstep
    · simp only [Option.map_some, Option.some.injEq] at hstep
      subst hstep
      exact ⟨stmt, rfl⟩
  obtain ⟨stmt, hm⟩ := hm_eq
  have he : (M.machine cfg.q cfg.Tape.head).isSome = true := by simp [hm]
  obtain ⟨m₁, hm₁, posW', rcfg₁, hinv₁, hseg₁⟩ := bennett_phase1_exec M hinv hstep
  obtain ⟨m₂, hm₂, rcfg₂, hinv₂, hseg₂⟩ := bennett_phase2_seekHist M he hinv₁
  obtain ⟨rcfg₃, hinv₃, hseg₃⟩ := bennett_phase3_recordHist M hm hinv₂
  obtain ⟨m₄, hm₄, rcfg₄, hinv₄, hseg₄⟩ := bennett_phase4_returnWork M hinv₃
  have htot := ((hseg₁.trans hseg₂).trans hseg₃).trans hseg₄
  exact ⟨m₁ + m₂ + 2 + m₄, by omega, posW', rcfg₄, hinv₄, htot.1, htot.2⟩

/-- Post-halt rightward cruise: once in `.haltRun q rel` over an infinite half-tape with
`workHead = false` and `haltMark = false` at all non-negative offsets, every subsequent iterate
remains in `.haltRun q rel`. -/
-- tier: T1
theorem bennett_haltRun_cruise (M : FinTM0) (q : M.Λ) (rel : Ordering) (d : ℕ) :
    ∀ c : (bennettReversibleTM M).Cfg,
      c.q = .haltRun q rel →
      (∀ j : ℕ, (c.Tape.nth (j : ℤ)).workHead = false ∧ (c.Tape.nth (j : ℤ)).haltMark = false) →
      ((bennettReversibleTM M).step^[d] c).q = .haltRun q rel := by
  induction d with
  | zero => intro c hq _; exact hq
  | succ d ih =>
    intro c hq hall
    obtain ⟨hwh0, hhm0⟩ := hall 0
    have hwh0' : c.Tape.head.workHead = false := by simpa using hwh0
    have hhm0' : c.Tape.head.haltMark = false := by simpa using hhm0
    let b : (bennettReversibleTM M).Γ := { c.Tape.head with haltMark := true }
    have hrule : bennettRule M (c.q, c.Tape.head) = some (.haltRun q rel, b) := by
      rw [hq]
      simp [bennettRule, hwh0', hhm0', b]
    let c' : (bennettReversibleTM M).Cfg := ⟨.haltRun q rel, (c.Tape.write b).move Dir.right⟩
    have hs : (bennettReversibleTM M).step c = c' := by
      rw [bennettReversibleTM_step_of_rule M c hrule]
      rfl
    rw [Function.iterate_succ_apply, hs]
    refine ih c' rfl fun j ↦ ?_
    have hne : (j : ℤ) + 1 ≠ 0 := by omega
    have hnth : c'.Tape.nth (j : ℤ) = c.Tape.nth ((j + 1 : ℕ) : ℤ) := by
      simp only [c', Tape.move_right_nth, Tape.write_nth, hne, ↓reduceIte]
      rfl
    rw [hnth]
    exact hall (j + 1)

/-- **Bennett Terminal Halting Step (`UNCONDITIONAL`)**:
When `TM0.step M.machine cfg = none` under `BennettInv M posW posH cfg rcfg`, one step of
`bennettReversibleTM M` enters `.halted cfg.q (compare posW posH)` with identical full-tape work
symbols, and every iterate `k ≥ 2` remains permanently in `.haltRun cfg.q _`. -/
-- tier: T2
theorem bennett_haltStep (M : FinTM0) {posW posH : ℤ}
    {cfg : TM0.Cfg M.Γ M.Λ} {rcfg : (bennettReversibleTM M).Cfg}
    (hinv : BennettInv M posW posH cfg rcfg)
    (hterm : TM0.step M.machine cfg = none) :
    ((bennettReversibleTM M).step rcfg).q = .halted cfg.q (compare posW posH) ∧
    (∀ i : ℤ, (((bennettReversibleTM M).step rcfg).Tape.nth i).sym = cfg.Tape.nth i) ∧
    ∀ k ≥ 2, ∃ r : Ordering, ((bennettReversibleTM M).step^[k] rcfg).q = .haltRun cfg.q r := by
  have hm_none : M.machine cfg.q cfg.Tape.head = none := by
    rcases cfg with ⟨q, T⟩
    simpa [TM0.step] using hterm
  have hhead_sym : rcfg.Tape.head.sym = cfg.Tape.head := hinv.sym_eq 0
  have hwh0 : rcfg.Tape.head.workHead = true := by simpa using hinv.workHead_eq 0
  have hhm0 : rcfg.Tape.head.haltMark = false := hinv.haltMark_false 0
  have hhh0 : rcfg.Tape.head.histHead = decide (posW = posH) := by
    simpa using hinv.histHead_eq 0
  have hguard :
      (rcfg.Tape.head.workHead && !rcfg.Tape.head.haltMark &&
        (rcfg.Tape.head.histHead == (compare posW posH == .eq))) = true := by
    rw [hwh0, hhm0, hhh0]
    simpa using decide_eq_beq_compare_eq posW posH
  let rel₀ := compare posW posH
  have hrule₁ : bennettRule M (rcfg.q, rcfg.Tape.head) =
      some (.halted cfg.q rel₀, rcfg.Tape.head) := by
    rw [hinv.q_eq]
    dsimp only [bennettRule]
    rw [hguard]
    simp only [↓reduceIte, hhead_sym, hm_none, rel₀]
  have hs₁ : (bennettReversibleTM M).step rcfg = ⟨.halted cfg.q rel₀, rcfg.Tape⟩ := by
    rw [bennettReversibleTM_step_of_rule M rcfg hrule₁, bennettDirIn_halted,
      bennettTape_write_head]
  refine ⟨by rw [hs₁], fun i ↦ by rw [hs₁]; exact hinv.sym_eq i, fun k hk ↦ ?_⟩
  let c₁ : (bennettReversibleTM M).Cfg := ⟨.halted cfg.q rel₀, rcfg.Tape⟩
  let b₂ : (bennettReversibleTM M).Γ := { rcfg.Tape.head with haltMark := true }
  have hrule₂ : bennettRule M (c₁.q, c₁.Tape.head) = some (.haltRun cfg.q rel₀, b₂) := by
    simp [c₁, bennettRule, hwh0, hhm0, b₂]
  let c₂ : (bennettReversibleTM M).Cfg :=
    ⟨.haltRun cfg.q rel₀, (rcfg.Tape.write b₂).move Dir.right⟩
  have hs₂ : (bennettReversibleTM M).step c₁ = c₂ := by
    rw [bennettReversibleTM_step_of_rule M c₁ hrule₂]
    rfl
  have hk_decomp : k = (k - 2) + 2 := by omega
  refine ⟨rel₀, ?_⟩
  rw [hk_decomp, Function.iterate_add_apply]
  change ((bennettReversibleTM M).step^[k - 2]
    ((bennettReversibleTM M).step ((bennettReversibleTM M).step rcfg))).q = _
  rw [hs₁, hs₂]
  refine bennett_haltRun_cruise M cfg.q rel₀ (k - 2) c₂ rfl fun j ↦ ?_
  have hne : (j : ℤ) + 1 ≠ 0 := by omega
  have hnth : c₂.Tape.nth (j : ℤ) = rcfg.Tape.nth ((j : ℤ) + 1) := by
    simp [c₂, Tape.move_right_nth, Tape.write_nth, hne]
  rw [hnth]
  exact ⟨by simpa [hne] using hinv.workHead_eq ((j : ℤ) + 1), hinv.haltMark_false ((j : ℤ) + 1)⟩

/-! ### Multi-Step Macro Induction & Full / Windowed Halting Orbit Equivalence -/

/-- Iterated active `M.stepOpt` macro-simulation: `s` active `TM0` transitions from `BennettInv`
produce `N ≥ s` non-halting reversible steps establishing `BennettInv` at `posH - s`. -/
-- tier: T1
theorem bennett_iterate_macroStep (M : FinTM0) (s : ℕ) :
    ∀ {posW posH : ℤ} {cfg₀ cfg : TM0.Cfg M.Γ M.Λ} {rcfg₀ : (bennettReversibleTM M).Cfg},
      BennettInv M posW posH cfg₀ rcfg₀ →
      M.stepOpt^[s] (some cfg₀) = some cfg →
      ∃ N ≥ s, ∃ posW' rcfg,
        BennettInv M posW' (posH - s) cfg rcfg ∧
        StepsNoHalt M rcfg₀ rcfg N := by
  induction s with
  | zero =>
    intro posW posH cfg₀ cfg rcfg₀ hinv hs
    cases hs
    refine ⟨0, le_rfl, posW, rcfg₀, ?_, StepsNoHalt.refl M rcfg₀⟩
    simpa using hinv
  | succ s ih =>
    intro posW posH cfg₀ cfg rcfg₀ hinv hs
    rw [Function.iterate_succ_apply] at hs
    change M.stepOpt^[s] (TM0.step M.machine cfg₀) = some cfg at hs
    rcases h1 : TM0.step M.machine cfg₀ with _ | cfg₁ <;> rw [h1] at hs
    · rw [M.iterate_stepOpt_none] at hs; cases hs
    · obtain ⟨m, hm, posW₁, rcfg₁, hinv₁, hstep_m, hno_m⟩ := bennett_macroStep M hinv h1
      obtain ⟨N', hN', posW', rcfg, hinv', hseg'⟩ := ih hinv₁ hs
      have hposH : posH - 1 - (s : ℤ) = posH - ((s + 1 : ℕ) : ℤ) := by push_cast; omega
      rw [hposH] at hinv'
      exact ⟨m + N', by omega, posW', rcfg, hinv', StepsNoHalt.trans ⟨hstep_m, hno_m⟩ hseg'⟩

/-- Dichotomy for `k` steps of `M.stepOpt` from `c₀`: either `M` stays active for `k` steps or `M`
halted at some step `s < k`. -/
-- tier: T1
theorem stepOpt_dichotomy (M : FinTM0) (c₀ : TM0.Cfg M.Γ M.Λ) :
    ∀ k : ℕ,
      (∃ c, M.stepOpt^[k] (some c₀) = some c) ∨
      (∃ s < k, ∃ c, M.stepOpt^[s] (some c₀) = some c ∧ TM0.step M.machine c = none)
  | 0 => Or.inl ⟨c₀, rfl⟩
  | k + 1 => by
    rcases stepOpt_dichotomy M c₀ k with ⟨c, hk⟩ | ⟨s, hsk, c, hs, hterm⟩
    · rcases hstep : TM0.step M.machine c with _ | c'
      · exact Or.inr ⟨k, Nat.lt_succ_self k, c, hk, hstep⟩
      · refine Or.inl ⟨c', ?_⟩
        rw [Function.iterate_succ_apply', hk]
        exact hstep
    · exact Or.inr ⟨s, Nat.lt_succ_of_lt hsk, c, hs, hterm⟩

/-- Forward full-tape halting simulation: every terminal `TM0` configuration reachable from
`M.initCfg t` is reached at `.halted c.q rel` at some step `n ≥ 1` of `bennettReversibleTM M` with
identical work-track symbols across all of `ℤ`. -/
-- tier: T2
theorem bennett_orbit_halted_forward (M : FinTM0) (t : FinSupportedTape M)
    {c : TM0.Cfg M.Γ M.Λ} (hreach : TM0.Reaches M.machine (M.initCfg t) c)
    (hterm : TM0.step M.machine c = none) :
    ∃ n ≥ 1, ∃ rel : Ordering,
      ((bennettReversibleTM M).step^[n] (bennettInitCfg M t)).q = .halted c.q rel ∧
      ∀ i : ℤ,
        (((bennettReversibleTM M).step^[n] (bennettInitCfg M t)).Tape.nth i).sym =
          c.Tape.nth i := by
  obtain ⟨s, hs⟩ := (M.reaches_iff_exists_iterate_stepOpt (M.initCfg t) c).mp hreach
  obtain ⟨N, _, posW', rcfg, hinv, hseg⟩ :=
    bennett_iterate_macroStep M s (bennettInv_initCfg M t) hs
  obtain ⟨hq, hsym, _⟩ := bennett_haltStep M hinv hterm
  refine ⟨N + 1, by omega, compare posW' (0 - (s : ℤ)), ?_, fun i ↦ ?_⟩
  · rw [Function.iterate_succ_apply', hseg.1, hq]
  · rw [Function.iterate_succ_apply', hseg.1, hsym i]

/-- Converse full-tape halting simulation: if
`(bennettReversibleTM M).step^[n] (bennettInitCfg M t)` enters `.halted q rel`, then `M` reaches a
terminal configuration `c` with `c.q = q` and full-tape symbol equality across all `i : ℤ`. -/
-- tier: T2
theorem bennett_orbit_halted_backward (M : FinTM0) (t : FinSupportedTape M)
    {n : ℕ} {q : M.Λ} {rel : Ordering}
    (hn : ((bennettReversibleTM M).step^[n] (bennettInitCfg M t)).q = .halted q rel) :
    ∃ c : TM0.Cfg M.Γ M.Λ,
      c.q = q ∧
      TM0.Reaches M.machine (M.initCfg t) c ∧
      TM0.step M.machine c = none ∧
      ∀ i : ℤ,
        (((bennettReversibleTM M).step^[n] (bennettInitCfg M t)).Tape.nth i).sym =
          c.Tape.nth i := by
  rcases stepOpt_dichotomy M (M.initCfg t) (n + 1) with ⟨c_act, hact⟩ | ⟨s, _, c, hs, hterm⟩
  · obtain ⟨N, hN, _, _, _, hseg⟩ :=
      bennett_iterate_macroStep M (n + 1) (bennettInv_initCfg M t) hact
    exact absurd hn (hseg.2 n (by omega) q rel)
  · obtain ⟨N, _, posW', rcfg, hinv, hseg⟩ :=
      bennett_iterate_macroStep M s (bennettInv_initCfg M t) hs
    obtain ⟨hq1, hsym1, hrun⟩ := bennett_haltStep M hinv hterm
    have hn_eq : n = N + 1 := by
      rcases lt_trichotomy n N with hlt | rfl | hgt
      · exact absurd hn (hseg.2 n hlt q rel)
      · rw [hseg.1, hinv.q_eq] at hn
        cases hn
      · by_cases heq : n = N + 1
        · exact heq
        · have hk2 : n - N ≥ 2 := by omega
          have hdecomp : n = (n - N) + N := by omega
          rw [hdecomp, Function.iterate_add_apply, hseg.1] at hn
          obtain ⟨r, hr⟩ := hrun (n - N) hk2
          rw [hr] at hn
          cases hn
    subst hn_eq
    rw [Function.iterate_succ_apply', hseg.1, hq1] at hn
    injection hn with hcq _
    refine ⟨c, hcq, (M.reaches_iff_exists_iterate_stepOpt _ _).mpr ⟨s, hs⟩, hterm, fun i ↦ ?_⟩
    rw [Function.iterate_succ_apply', hseg.1, hsym1 i]

/-- **Full-Tape Bennett Orbit Equivalence (`UNCONDITIONAL`)**:
Packages both directions (`bennett_orbit_halted_backward` and `bennett_orbit_halted_forward`)
between `.halted` visits of `bennettReversibleTM M` and terminal `TM0.Reaches` computations of `M`,
preserving work-track symbols across all of `ℤ` (consumed directly by Milestone B3). -/
-- tier: T2
theorem bennett_orbit_halted_full (M : FinTM0) (t : FinSupportedTape M) :
    (∀ {n : ℕ} {q : M.Λ} {rel : Ordering},
      ((bennettReversibleTM M).step^[n] (bennettInitCfg M t)).q = .halted q rel →
        ∃ c : TM0.Cfg M.Γ M.Λ,
          c.q = q ∧
          TM0.Reaches M.machine (M.initCfg t) c ∧
          TM0.step M.machine c = none ∧
          ∀ i : ℤ,
            (((bennettReversibleTM M).step^[n] (bennettInitCfg M t)).Tape.nth i).sym =
              c.Tape.nth i) ∧
    (∀ {c : TM0.Cfg M.Γ M.Λ},
      TM0.Reaches M.machine (M.initCfg t) c →
      TM0.step M.machine c = none →
        ∃ n ≥ 1, ∃ rel : Ordering,
          ((bennettReversibleTM M).step^[n] (bennettInitCfg M t)).q = .halted c.q rel ∧
          ∀ i : ℤ,
            (((bennettReversibleTM M).step^[n] (bennettInitCfg M t)).Tape.nth i).sym =
              c.Tape.nth i) :=
  ⟨fun h ↦ bennett_orbit_halted_backward M t h,
   fun hr ht ↦ bennett_orbit_halted_forward M t hr ht⟩

/-- **Bennett (1973) Windowed Halting Orbit Equivalence (`UNCONDITIONAL`)**:
For any finite `TM0` machine `M : FinTM0`, input tape `t : FinSupportedTape M`, radius `k : ℕ`, and
output window `w : Window M k`, the forward reversible orbit of `bennettInitCfg M t` under
`bennettReversibleTM M` visits `.halted q rel` with work-track window `w` on `[-k, k]` if and only
if `HaltsWithWindow M t k w`. -/
-- tier: T2
theorem bennett_orbit_halted_iff (M : FinTM0) (t : FinSupportedTape M)
    (k : ℕ) (w : Window M k) :
    (∃ (n : ℕ) (q : M.Λ) (rel : Ordering),
      ((bennettReversibleTM M).step^[n] (bennettInitCfg M t)).q = .halted q rel ∧
      ∀ i : Set.Icc (-(k : ℤ)) (k : ℤ),
        (((bennettReversibleTM M).step^[n] (bennettInitCfg M t)).Tape.nth i.1).sym = w i) ↔
    HaltsWithWindow M t k w := by
  obtain ⟨hbwd, hfwd⟩ := bennett_orbit_halted_full M t
  constructor
  · rintro ⟨n, q, rel, hq, hwin⟩
    obtain ⟨c, _, hreach, hterm, hsym⟩ := hbwd hq
    exact ⟨c, hreach, hterm, fun i ↦ (hsym i.1).symm.trans (hwin i)⟩
  · rintro ⟨c, hreach, hterm, hwin⟩
    obtain ⟨n, _, rel, hq, hsym⟩ := hfwd hreach hterm
    exact ⟨n, c.q, rel, hq, fun i ↦ (hsym i.1).trans (hwin i)⟩

/-! ### Infinite Non-Repeating Forward Orbits from `bennettInitCfg` -/

/-- Local boolean tape invariant shared by all stationary/walking active phases of
`bennettReversibleTM M` when the physical head sits at `pos`, work head at `posW`, and history
cursor at `posH`. -/
private structure ActiveTapeInv (M : FinTM0) (pos posW posH : ℤ)
    (T : Tape (BennettCell M)) : Prop where
  workHead_eq : ∀ i : ℤ, (T.nth i).workHead = decide (pos + i = posW)
  histHead_eq : ∀ i : ℤ, (T.nth i).histHead = decide (pos + i = posH)
  hist_none_lt : ∀ i : ℤ, pos + i < posH → (T.nth i).hist = none
  haltMark_false : ∀ i : ℤ, (T.nth i).haltMark = false

private theorem activeTapeInv_initTape (M : FinTM0) (t : FinSupportedTape M) :
    ActiveTapeInv M 0 0 0 (bennettInitTape M t) where
  workHead_eq i := by simpa using (bennettInv_initCfg M t).workHead_eq i
  histHead_eq i := (bennettInv_initCfg M t).histHead_eq i
  hist_none_lt := (bennettInv_initCfg M t).hist_none_lt
  haltMark_false := (bennettInv_initCfg M t).haltMark_false

private theorem ActiveTapeInv.write_sym {M : FinTM0} {pos posW posH : ℤ}
    {T : Tape (BennettCell M)} (h : ActiveTapeInv M pos posW posH T) (b : M.Γ) :
    ActiveTapeInv M pos posW posH (T.write { T.head with sym := b }) where
  workHead_eq i := by
    by_cases hi : i = 0
    · subst hi; simpa using h.workHead_eq 0
    · simp [Tape.write_nth, hi, h.workHead_eq i]
  histHead_eq i := by
    by_cases hi : i = 0
    · subst hi; simpa using h.histHead_eq 0
    · simp [Tape.write_nth, hi, h.histHead_eq i]
  hist_none_lt i hlt := by
    by_cases hi : i = 0
    · subst hi; simpa using h.hist_none_lt 0 hlt
    · simp [Tape.write_nth, hi, h.hist_none_lt i hlt]
  haltMark_false i := by
    by_cases hi : i = 0
    · subst hi; simpa using h.haltMark_false 0
    · simp [Tape.write_nth, hi, h.haltMark_false i]

private theorem ActiveTapeInv.move_left {M : FinTM0} {pos posW posH : ℤ}
    {T : Tape (BennettCell M)} (h : ActiveTapeInv M pos posW posH T) :
    ActiveTapeInv M (pos - 1) posW posH (T.move Dir.left) where
  workHead_eq i := by
    rw [Tape.move_left_nth, h.workHead_eq (i - 1)]
    exact decide_eq_decide.mpr (by omega)
  histHead_eq i := by
    rw [Tape.move_left_nth, h.histHead_eq (i - 1)]
    exact decide_eq_decide.mpr (by omega)
  hist_none_lt i hlt := by
    rw [Tape.move_left_nth]
    exact h.hist_none_lt (i - 1) (by omega)
  haltMark_false i := by
    rw [Tape.move_left_nth]
    exact h.haltMark_false (i - 1)

private theorem ActiveTapeInv.move_right {M : FinTM0} {pos posW posH : ℤ}
    {T : Tape (BennettCell M)} (h : ActiveTapeInv M pos posW posH T) :
    ActiveTapeInv M (pos + 1) posW posH (T.move Dir.right) where
  workHead_eq i := by
    rw [Tape.move_right_nth, h.workHead_eq (i + 1)]
    exact decide_eq_decide.mpr (by omega)
  histHead_eq i := by
    rw [Tape.move_right_nth, h.histHead_eq (i + 1)]
    exact decide_eq_decide.mpr (by omega)
  hist_none_lt i hlt := by
    rw [Tape.move_right_nth]
    exact h.hist_none_lt (i + 1) (by omega)
  haltMark_false i := by
    rw [Tape.move_right_nth]
    exact h.haltMark_false (i + 1)

/-- Single-step forward invariant certifying that every state along the forward trajectory of
`bennettInitCfg M t` takes a defined `bennettRule M` transition (`isSome = true`). -/
private def ValidTrajectoryCfg (M : FinTM0) (c : (bennettReversibleTM M).Cfg) : Prop :=
  match c.q with
  | .exec _ rel =>
    ∃ posW posH, ActiveTapeInv M posW posW posH c.Tape ∧ rel = compare posW posH
  | .halted _ _ =>
    c.Tape.head.workHead = true ∧ c.Tape.head.haltMark = false ∧
      ∀ j : ℕ, (c.Tape.nth ((j : ℤ) + 1)).workHead = false ∧
        (c.Tape.nth ((j : ℤ) + 1)).haltMark = false
  | .haltRun _ _ =>
    ∀ j : ℕ, (c.Tape.nth (j : ℤ)).workHead = false ∧ (c.Tape.nth (j : ℤ)).haltMark = false
  | .moveWorkLeft e rMid =>
    ∃ pos posH q', M.machine e.1 e.2 = some (q', .move .left) ∧
      (∀ i : ℤ, (c.Tape.nth i).workHead = false) ∧
      (∀ i : ℤ, (c.Tape.nth i).histHead = decide (pos + i = posH)) ∧
      (∀ i : ℤ, pos + i < posH → (c.Tape.nth i).hist = none) ∧
      (∀ i : ℤ, (c.Tape.nth i).haltMark = false) ∧
      ((rMid = .gt ∧ posH ≤ pos) ∨ (rMid = .lt ∧ pos < posH))
  | .moveWorkRight e rMid =>
    ∃ pos posH q', M.machine e.1 e.2 = some (q', .move .right) ∧
      (∀ i : ℤ, (c.Tape.nth i).workHead = false) ∧
      (∀ i : ℤ, (c.Tape.nth i).histHead = decide (pos + i = posH)) ∧
      (∀ i : ℤ, pos + i < posH → (c.Tape.nth i).hist = none) ∧
      (∀ i : ℤ, (c.Tape.nth i).haltMark = false) ∧
      ((rMid = .lt ∧ pos ≤ posH) ∨ (rMid = .gt ∧ posH < pos))
  | .afterExec e rel =>
    ∃ posW posH, ActiveTapeInv M posW posW posH c.Tape ∧ rel = compare posW posH ∧
      (M.machine e.1 e.2).isSome = true
  | .seekHistLeft e =>
    ∃ pos posW posH, ActiveTapeInv M pos posW posH c.Tape ∧ posH ≤ pos ∧ pos < posW ∧
      (M.machine e.1 e.2).isSome = true
  | .seekHistRight e =>
    ∃ pos posW posH, ActiveTapeInv M pos posW posH c.Tape ∧ posW < pos ∧ pos ≤ posH ∧
      (M.machine e.1 e.2).isSome = true
  | .atHist e r =>
    ∃ posW posH, ActiveTapeInv M posH posW posH c.Tape ∧ r = compare posW posH ∧
      (M.machine e.1 e.2).isSome = true
  | .stepHistLeft e rMid =>
    ∃ pos posW, (M.machine e.1 e.2).isSome = true ∧
      (∀ i : ℤ, (c.Tape.nth i).histHead = false) ∧
      (∀ i : ℤ, (c.Tape.nth i).workHead = decide (pos + i = posW)) ∧
      (∀ i : ℤ, i ≤ 0 → (c.Tape.nth i).hist = none) ∧
      (∀ i : ℤ, (c.Tape.nth i).haltMark = false) ∧
      ((rMid = .lt ∧ posW ≤ pos) ∨ (rMid = .gt ∧ pos < posW))
  | .startReturn _ rRet =>
    ∃ posW posH, ActiveTapeInv M posH posW posH c.Tape ∧ rRet = compare posW posH
  | .seekWorkLeft _ =>
    ∃ pos posW posH, ActiveTapeInv M pos posW posH c.Tape ∧ posW ≤ pos ∧ pos < posH
  | .seekWorkRight _ =>
    ∃ pos posW posH, ActiveTapeInv M pos posW posH c.Tape ∧ posH < pos ∧ pos ≤ posW

private theorem validTrajectoryCfg_step (M : FinTM0) {c : (bennettReversibleTM M).Cfg}
    (hv : ValidTrajectoryCfg M c) :
    (bennettRule M (c.q, c.Tape.head)).isSome = true ∧
    ValidTrajectoryCfg M ((bennettReversibleTM M).step c) := by
  rcases c with ⟨q, T⟩
  cases q with
  | exec q₀ rel =>
    obtain ⟨posW, posH, hT, rfl⟩ := hv
    have hwh0 : T.head.workHead = true := by simpa using hT.workHead_eq 0
    have hhm0 : T.head.haltMark = false := hT.haltMark_false 0
    have hhh0 : T.head.histHead = decide (posW = posH) := by simpa using hT.histHead_eq 0
    have hguard : (T.head.workHead && !T.head.haltMark &&
        (T.head.histHead == (compare posW posH == .eq))) = true := by
      rw [hwh0, hhm0, hhh0]
      simpa using decide_eq_beq_compare_eq posW posH
    rcases hm : M.machine q₀ T.head.sym with _ | ⟨q', (_ | _) | b⟩
    · have hr : bennettRule M (.exec q₀ (compare posW posH), T.head) =
          some (.halted q₀ (compare posW posH), T.head) := by
        dsimp only [bennettRule]; rw [hguard]; simp [hm]
      refine ⟨by simp [hr], ?_⟩
      rw [bennettReversibleTM_step_of_rule M ⟨_, T⟩ hr, bennettDirIn_halted, bennettTape_write_head]
      refine ⟨hwh0, hhm0, fun j ↦ ?_⟩
      have hne : posW + ((j : ℤ) + 1) ≠ posW := by omega
      exact ⟨by simpa [hne] using hT.workHead_eq ((j : ℤ) + 1), hT.haltMark_false ((j : ℤ) + 1)⟩
    · let rMid : Ordering := match compare posW posH with | .gt => .gt | _ => .lt
      have hr : bennettRule M (.exec q₀ (compare posW posH), T.head) =
          some (.moveWorkLeft (q₀, T.head.sym) rMid, { T.head with workHead := false }) := by
        dsimp only [bennettRule]; rw [hguard]; simp only [↓reduceIte, hm]; rfl
      refine ⟨by simp [hr], ?_⟩
      rw [bennettReversibleTM_step_of_rule M ⟨_, T⟩ hr, bennettDirIn_moveWorkLeft]
      refine ⟨posW - 1, posH, q', hm, fun i ↦ ?_, fun i ↦ ?_, fun i hlt ↦ ?_, fun i ↦ ?_, ?_⟩
      · rw [Tape.move_left_nth, Tape.write_nth]
        split_ifs with h0
        · rfl
        · have hne : posW + (i - 1) ≠ posW := by omega
          simpa [hne] using hT.workHead_eq (i - 1)
      · rw [Tape.move_left_nth, Tape.write_nth]
        have heq_p : (posW - 1 + i = posH) ↔ (posW + (i - 1) = posH) := by omega
        rw [decide_eq_decide.mpr heq_p]
        split_ifs with h0
        · have hi : i = 1 := by omega
          subst hi; simpa using hT.histHead_eq 0
        · exact hT.histHead_eq (i - 1)
      · rw [Tape.move_left_nth, Tape.write_nth]
        split_ifs with h0
        · have hi : i = 1 := by omega
          subst hi; simpa using hT.hist_none_lt 0 (by omega)
        · exact hT.hist_none_lt (i - 1) (by omega)
      · rw [Tape.move_left_nth, Tape.write_nth]
        split_ifs with h0
        · exact hT.haltMark_false 0
        · exact hT.haltMark_false (i - 1)
      · dsimp only [rMid]
        rcases lt_trichotomy posW posH with hlt | rfl | hgt
        · rw [compare_lt_iff_lt.mpr hlt]; exact Or.inr ⟨rfl, by omega⟩
        · rw [compare_eq_iff_eq.mpr rfl]; exact Or.inr ⟨rfl, by omega⟩
        · rw [compare_gt_iff_gt.mpr hgt]; exact Or.inl ⟨rfl, by omega⟩
    · let rMid : Ordering := match compare posW posH with | .lt => .lt | _ => .gt
      have hr : bennettRule M (.exec q₀ (compare posW posH), T.head) =
          some (.moveWorkRight (q₀, T.head.sym) rMid, { T.head with workHead := false }) := by
        dsimp only [bennettRule]; rw [hguard]; simp only [↓reduceIte, hm]; rfl
      refine ⟨by simp [hr], ?_⟩
      rw [bennettReversibleTM_step_of_rule M ⟨_, T⟩ hr, bennettDirIn_moveWorkRight]
      refine ⟨posW + 1, posH, q', hm, fun i ↦ ?_, fun i ↦ ?_, fun i hlt ↦ ?_, fun i ↦ ?_, ?_⟩
      · rw [Tape.move_right_nth, Tape.write_nth]
        split_ifs with h0
        · rfl
        · have hne : posW + (i + 1) ≠ posW := by omega
          simpa [hne] using hT.workHead_eq (i + 1)
      · rw [Tape.move_right_nth, Tape.write_nth]
        have heq_p : (posW + 1 + i = posH) ↔ (posW + (i + 1) = posH) := by omega
        rw [decide_eq_decide.mpr heq_p]
        split_ifs with h0
        · have hi : i = -1 := by omega
          subst hi; simpa using hT.histHead_eq 0
        · exact hT.histHead_eq (i + 1)
      · rw [Tape.move_right_nth, Tape.write_nth]
        split_ifs with h0
        · have hi : i = -1 := by omega
          subst hi; simpa using hT.hist_none_lt 0 (by omega)
        · exact hT.hist_none_lt (i + 1) (by omega)
      · rw [Tape.move_right_nth, Tape.write_nth]
        split_ifs with h0
        · exact hT.haltMark_false 0
        · exact hT.haltMark_false (i + 1)
      · dsimp only [rMid]
        rcases lt_trichotomy posW posH with hlt | rfl | hgt
        · rw [compare_lt_iff_lt.mpr hlt]; exact Or.inl ⟨rfl, by omega⟩
        · rw [compare_eq_iff_eq.mpr rfl]; exact Or.inr ⟨rfl, by omega⟩
        · rw [compare_gt_iff_gt.mpr hgt]; exact Or.inr ⟨rfl, by omega⟩
    · have hr : bennettRule M (.exec q₀ (compare posW posH), T.head) =
          some (.afterExec (q₀, T.head.sym) (compare posW posH), { T.head with sym := b }) := by
        dsimp only [bennettRule]; rw [hguard]; simp [hm]
      refine ⟨by simp [hr], ?_⟩
      rw [bennettReversibleTM_step_of_rule M ⟨_, T⟩ hr, bennettDirIn_afterExec]
      exact ⟨posW, posH, hT.write_sym b, rfl, by simp [hm]⟩
  | halted q₀ rel =>
    dsimp only [ValidTrajectoryCfg] at hv
    obtain ⟨hwh0, hhm0, hrest⟩ := hv
    have hr : bennettRule M (.halted q₀ rel, T.head) =
        some (.haltRun q₀ rel, { T.head with haltMark := true }) := by
      simp [bennettRule, hwh0, hhm0]
    refine ⟨by simp [hr], ?_⟩
    rw [bennettReversibleTM_step_of_rule M ⟨_, T⟩ hr, bennettDirIn_haltRun]
    intro j
    have hne : (j : ℤ) + 1 ≠ 0 := by omega
    have hnth : (((T.write { T.head with haltMark := true }).move Dir.right).nth (j : ℤ)) =
        T.nth ((j : ℤ) + 1) := by
      simp [Tape.move_right_nth, Tape.write_nth, hne]
    dsimp only [ValidTrajectoryCfg]
    rw [hnth]
    exact hrest j
  | haltRun q₀ rel =>
    dsimp only [ValidTrajectoryCfg] at hv
    obtain ⟨hwh0, hhm0⟩ := hv 0
    have hwh0' : T.head.workHead = false := by simpa using hwh0
    have hhm0' : T.head.haltMark = false := by simpa using hhm0
    have hr : bennettRule M (.haltRun q₀ rel, T.head) =
        some (.haltRun q₀ rel, { T.head with haltMark := true }) := by
      simp [bennettRule, hwh0', hhm0']
    refine ⟨by simp [hr], ?_⟩
    rw [bennettReversibleTM_step_of_rule M ⟨_, T⟩ hr, bennettDirIn_haltRun]
    intro j
    have hne : (j : ℤ) + 1 ≠ 0 := by omega
    have hcast : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by push_cast; ring
    have hnth : (((T.write { T.head with haltMark := true }).move Dir.right).nth (j : ℤ)) =
        T.nth ((j + 1 : ℕ) : ℤ) := by
      rw [hcast]
      simp [Tape.move_right_nth, Tape.write_nth, hne]
    dsimp only [ValidTrajectoryCfg]
    rw [hnth]
    exact hv (j + 1)
  | moveWorkLeft e rMid =>
    obtain ⟨pos, posH, q', hm, hwh, hhh, hhist, hhm, hcases⟩ := hv
    have hwh0 : T.head.workHead = false := hwh 0
    have hhm0 : T.head.haltMark = false := hhm 0
    have hT_next : ActiveTapeInv M pos pos posH (T.write { T.head with workHead := true }) :=
      { workHead_eq := fun i ↦ by
          by_cases hi : i = 0
          · subst hi; simp
          · have hne : pos + i ≠ pos := by omega
            simp [Tape.write_nth, hi, hne, hwh i]
        histHead_eq := fun i ↦ by
          by_cases hi : i = 0
          · subst hi; simpa using hhh 0
          · simp [Tape.write_nth, hi, hhh i]
        hist_none_lt := fun i hlt ↦ by
          by_cases hi : i = 0
          · subst hi; simpa using hhist 0 hlt
          · simp [Tape.write_nth, hi, hhist i hlt]
        haltMark_false := fun i ↦ by
          by_cases hi : i = 0
          · subst hi; exact hhm 0
          · simp [Tape.write_nth, hi, hhm i] }
    rcases hcases with ⟨rfl, hle⟩ | ⟨rfl, hlt⟩
    · let rel' : Ordering := if T.head.histHead then .eq else .gt
      have hr : bennettRule M (.moveWorkLeft e .gt, T.head) =
          some (.afterExec e rel', { T.head with workHead := true }) := by
        simp [bennettRule, hwh0, hhm0, hm, rel']
      refine ⟨by simp [hr], ?_⟩
      rw [bennettReversibleTM_step_of_rule M ⟨_, T⟩ hr, bennettDirIn_afterExec]
      have hrel' : rel' = compare pos posH := by
        have hhh0 : T.head.histHead = decide (pos = posH) := by simpa using hhh 0
        dsimp [rel']; rw [hhh0]
        by_cases heq : pos = posH
        · simp [heq]
        · have hgt : posH < pos := by omega
          simp [heq, compare_gt_iff_gt.mpr hgt]
      exact ⟨pos, posH, hT_next, hrel', by simp [hm]⟩
    · have hhh0 : T.head.histHead = false := by
        have hne : pos ≠ posH := by omega
        simpa [hne] using hhh 0
      have hr : bennettRule M (.moveWorkLeft e .lt, T.head) =
          some (.afterExec e .lt, { T.head with workHead := true }) := by
        simp [bennettRule, hwh0, hhm0, hm, hhh0]
      refine ⟨by simp [hr], ?_⟩
      rw [bennettReversibleTM_step_of_rule M ⟨_, T⟩ hr, bennettDirIn_afterExec]
      exact ⟨pos, posH, hT_next, (compare_lt_iff_lt.mpr hlt).symm, by simp [hm]⟩
  | moveWorkRight e rMid =>
    obtain ⟨pos, posH, q', hm, hwh, hhh, hhist, hhm, hcases⟩ := hv
    have hwh0 : T.head.workHead = false := hwh 0
    have hhm0 : T.head.haltMark = false := hhm 0
    have hT_next : ActiveTapeInv M pos pos posH (T.write { T.head with workHead := true }) :=
      { workHead_eq := fun i ↦ by
          by_cases hi : i = 0
          · subst hi; simp
          · have hne : pos + i ≠ pos := by omega
            simp [Tape.write_nth, hi, hne, hwh i]
        histHead_eq := fun i ↦ by
          by_cases hi : i = 0
          · subst hi; simpa using hhh 0
          · simp [Tape.write_nth, hi, hhh i]
        hist_none_lt := fun i hlt ↦ by
          by_cases hi : i = 0
          · subst hi; simpa using hhist 0 hlt
          · simp [Tape.write_nth, hi, hhist i hlt]
        haltMark_false := fun i ↦ by
          by_cases hi : i = 0
          · subst hi; exact hhm 0
          · simp [Tape.write_nth, hi, hhm i] }
    rcases hcases with ⟨rfl, hle⟩ | ⟨rfl, hgt⟩
    · let rel' : Ordering := if T.head.histHead then .eq else .lt
      have hr : bennettRule M (.moveWorkRight e .lt, T.head) =
          some (.afterExec e rel', { T.head with workHead := true }) := by
        simp [bennettRule, hwh0, hhm0, hm, rel']
      refine ⟨by simp [hr], ?_⟩
      rw [bennettReversibleTM_step_of_rule M ⟨_, T⟩ hr, bennettDirIn_afterExec]
      have hrel' : rel' = compare pos posH := by
        have hhh0 : T.head.histHead = decide (pos = posH) := by simpa using hhh 0
        dsimp [rel']; rw [hhh0]
        by_cases heq : pos = posH
        · simp [heq]
        · have hlt : pos < posH := by omega
          simp [heq, compare_lt_iff_lt.mpr hlt]
      exact ⟨pos, posH, hT_next, hrel', by simp [hm]⟩
    · have hhh0 : T.head.histHead = false := by
        have hne : pos ≠ posH := by omega
        simpa [hne] using hhh 0
      have hr : bennettRule M (.moveWorkRight e .gt, T.head) =
          some (.afterExec e .gt, { T.head with workHead := true }) := by
        simp [bennettRule, hwh0, hhm0, hm, hhh0]
      refine ⟨by simp [hr], ?_⟩
      rw [bennettReversibleTM_step_of_rule M ⟨_, T⟩ hr, bennettDirIn_afterExec]
      exact ⟨pos, posH, hT_next, (compare_gt_iff_gt.mpr hgt).symm, by simp [hm]⟩
  | afterExec e rel =>
    obtain ⟨posW, posH, hT, rfl, he⟩ := hv
    have hwh0 : T.head.workHead = true := by simpa using hT.workHead_eq 0
    have hhm0 : T.head.haltMark = false := hT.haltMark_false 0
    have hhh0 : T.head.histHead = decide (posW = posH) := by simpa using hT.histHead_eq 0
    have hguard : (T.head.workHead && !T.head.haltMark &&
        (T.head.histHead == (compare posW posH == .eq)) && (M.machine e.1 e.2).isSome) = true := by
      rw [hwh0, hhm0, hhh0, he]
      simpa using decide_eq_beq_compare_eq posW posH
    rcases lt_trichotomy posW posH with hlt | rfl | hgt
    · have hc : compare posW posH = .lt := compare_lt_iff_lt.mpr hlt
      have hr : bennettRule M (.afterExec e (compare posW posH), T.head) =
          some (.seekHistRight e, T.head) := by
        dsimp only [bennettRule]; rw [hguard, hc]; rfl
      refine ⟨by simp [hr], ?_⟩
      rw [bennettReversibleTM_step_of_rule M ⟨_, T⟩ hr, bennettDirIn_seekHistRight,
        bennettTape_write_head]
      exact ⟨posW + 1, posW, posH, hT.move_right, by omega, by omega, he⟩
    · have hc : compare posW posW = .eq := compare_eq_iff_eq.mpr rfl
      have hr : bennettRule M (.afterExec e (compare posW posW), T.head) =
          some (.atHist e .eq, T.head) := by
        dsimp only [bennettRule]; rw [hguard, hc]; rfl
      refine ⟨by dsimp only; rw [hr]; rfl, ?_⟩
      rw [bennettReversibleTM_step_of_rule M ⟨_, T⟩ hr, bennettDirIn_atHist, bennettTape_write_head]
      exact ⟨posW, posW, hT, hc.symm, he⟩
    · have hc : compare posW posH = .gt := compare_gt_iff_gt.mpr hgt
      have hr : bennettRule M (.afterExec e (compare posW posH), T.head) =
          some (.seekHistLeft e, T.head) := by
        dsimp only [bennettRule]; rw [hguard, hc]; rfl
      refine ⟨by simp [hr], ?_⟩
      rw [bennettReversibleTM_step_of_rule M ⟨_, T⟩ hr, bennettDirIn_seekHistLeft,
        bennettTape_write_head]
      exact ⟨posW - 1, posW, posH, hT.move_left, by omega, by omega, he⟩
  | seekHistLeft e =>
    obtain ⟨pos, posW, posH, hT, hle, hlt, he⟩ := hv
    have hwh0 : T.head.workHead = false := by
      have hne : pos ≠ posW := by omega
      simpa [hne] using hT.workHead_eq 0
    have hhm0 : T.head.haltMark = false := hT.haltMark_false 0
    by_cases hp : pos = posH
    · subst hp
      have hhh0 : T.head.histHead = true := by simpa using hT.histHead_eq 0
      have hr : bennettRule M (.seekHistLeft e, T.head) = some (.atHist e .gt, T.head) := by
        simp [bennettRule, hwh0, hhm0, he, hhh0]
      refine ⟨by simp [hr], ?_⟩
      rw [bennettReversibleTM_step_of_rule M ⟨_, T⟩ hr, bennettDirIn_atHist, bennettTape_write_head]
      exact ⟨posW, pos, hT, (compare_gt_iff_gt.mpr hlt).symm, he⟩
    · have hhh0 : T.head.histHead = false := by
        simpa [hp] using hT.histHead_eq 0
      have hr : bennettRule M (.seekHistLeft e, T.head) = some (.seekHistLeft e, T.head) := by
        simp [bennettRule, hwh0, hhm0, he, hhh0]
      refine ⟨by simp [hr], ?_⟩
      rw [bennettReversibleTM_step_of_rule M ⟨_, T⟩ hr, bennettDirIn_seekHistLeft,
        bennettTape_write_head]
      exact ⟨pos - 1, posW, posH, hT.move_left, by omega, by omega, he⟩
  | seekHistRight e =>
    obtain ⟨pos, posW, posH, hT, hlt, hle, he⟩ := hv
    have hwh0 : T.head.workHead = false := by
      have hne : pos ≠ posW := by omega
      simpa [hne] using hT.workHead_eq 0
    have hhm0 : T.head.haltMark = false := hT.haltMark_false 0
    by_cases hp : pos = posH
    · subst hp
      have hhh0 : T.head.histHead = true := by simpa using hT.histHead_eq 0
      have hr : bennettRule M (.seekHistRight e, T.head) = some (.atHist e .lt, T.head) := by
        simp [bennettRule, hwh0, hhm0, he, hhh0]
      refine ⟨by simp [hr], ?_⟩
      rw [bennettReversibleTM_step_of_rule M ⟨_, T⟩ hr, bennettDirIn_atHist, bennettTape_write_head]
      exact ⟨posW, pos, hT, (compare_lt_iff_lt.mpr hlt).symm, he⟩
    · have hhh0 : T.head.histHead = false := by
        simpa [hp] using hT.histHead_eq 0
      have hr : bennettRule M (.seekHistRight e, T.head) = some (.seekHistRight e, T.head) := by
        simp [bennettRule, hwh0, hhm0, he, hhh0]
      refine ⟨by simp [hr], ?_⟩
      rw [bennettReversibleTM_step_of_rule M ⟨_, T⟩ hr, bennettDirIn_seekHistRight,
        bennettTape_write_head]
      exact ⟨pos + 1, posW, posH, hT.move_right, by omega, by omega, he⟩
  | atHist e r =>
    obtain ⟨posW, posH, hT, rfl, he⟩ := hv
    have hhh0 : T.head.histHead = true := by simpa using hT.histHead_eq 0
    have hhm0 : T.head.haltMark = false := hT.haltMark_false 0
    have hwh0 : T.head.workHead = decide (posW = posH) := by
      have h0 := hT.workHead_eq 0
      simp only [add_zero] at h0
      exact h0.trans (decide_eq_decide.mpr eq_comm)
    have hguard : (T.head.histHead && !T.head.haltMark &&
        (T.head.workHead == (compare posW posH == .eq)) && (M.machine e.1 e.2).isSome) = true := by
      rw [hhh0, hhm0, hwh0, he]
      simpa using decide_eq_beq_compare_eq posW posH
    let rMid : Ordering := match compare posW posH with | .lt => .lt | _ => .gt
    have hr : bennettRule M (.atHist e (compare posW posH), T.head) =
        some (.stepHistLeft e rMid, { T.head with histHead := false }) := by
      dsimp only [bennettRule]; rw [hguard]; rfl
    refine ⟨by simp [hr], ?_⟩
    rw [bennettReversibleTM_step_of_rule M ⟨_, T⟩ hr, bennettDirIn_stepHistLeft]
    refine ⟨posH - 1, posW, he, fun i ↦ ?_, fun i ↦ ?_, fun i hi ↦ ?_, fun i ↦ ?_, ?_⟩
    · rw [Tape.move_left_nth, Tape.write_nth]
      split_ifs with h0
      · rfl
      · have hne : posH + (i - 1) ≠ posH := by omega
        simpa [hne] using hT.histHead_eq (i - 1)
    · rw [Tape.move_left_nth, Tape.write_nth]
      have heq_p : (posH - 1 + i = posW) ↔ (posH + (i - 1) = posW) := by omega
      rw [decide_eq_decide.mpr heq_p]
      split_ifs with h0
      · have hi1 : i = 1 := by omega
        subst hi1; simpa using hT.workHead_eq 0
      · exact hT.workHead_eq (i - 1)
    · rw [Tape.move_left_nth, Tape.write_nth]
      have hne : i - 1 ≠ 0 := by omega
      simp only [hne, ↓reduceIte]
      exact hT.hist_none_lt (i - 1) (by omega)
    · rw [Tape.move_left_nth, Tape.write_nth]
      split_ifs with h0
      · exact hT.haltMark_false 0
      · exact hT.haltMark_false (i - 1)
    · dsimp only [rMid]
      rcases lt_trichotomy posW posH with hlt | rfl | hgt
      · rw [compare_lt_iff_lt.mpr hlt]; exact Or.inl ⟨rfl, by omega⟩
      · rw [compare_eq_iff_eq.mpr rfl]; exact Or.inr ⟨rfl, by omega⟩
      · rw [compare_gt_iff_gt.mpr hgt]; exact Or.inr ⟨rfl, by omega⟩
  | stepHistLeft e rMid =>
    obtain ⟨pos, posW, he, hhh, hwh, hhist, hhm, hcases⟩ := hv
    obtain ⟨⟨q', stmt⟩, hm⟩ := Option.isSome_iff_exists.mp he
    have hhist0 : T.head.hist = none := hhist 0 le_rfl
    have hhh0 : T.head.histHead = false := hhh 0
    have hhm0 : T.head.haltMark = false := hhm 0
    have hT_next : ActiveTapeInv M pos posW pos
        (T.write { T.head with hist := some e, histHead := true }) :=
      { workHead_eq := fun i ↦ by
          by_cases hi : i = 0
          · subst hi; simpa using hwh 0
          · simp [Tape.write_nth, hi, hwh i]
        histHead_eq := fun i ↦ by
          by_cases hi : i = 0
          · subst hi; simp
          · have hne : pos + i ≠ pos := by omega
            simp [Tape.write_nth, hi, hne, hhh i]
        hist_none_lt := fun i hlt ↦ by
          have hi0 : i ≠ 0 := by omega
          simp only [Tape.write_nth, hi0, ↓reduceIte]
          exact hhist i (by omega)
        haltMark_false := fun i ↦ by
          by_cases hi : i = 0
          · subst hi; exact hhm 0
          · simp [Tape.write_nth, hi, hhm i] }
    rcases hcases with ⟨rfl, hle⟩ | ⟨rfl, hlt⟩
    · let rRet : Ordering := if T.head.workHead then .eq else .lt
      have hr : bennettRule M (.stepHistLeft e .lt, T.head) =
          some (.startReturn q' rRet, { T.head with hist := some e, histHead := true }) := by
        simp [bennettRule, hhist0, hhh0, hhm0, hm, rRet]
      refine ⟨by simp [hr], ?_⟩
      rw [bennettReversibleTM_step_of_rule M ⟨_, T⟩ hr, bennettDirIn_startReturn]
      have hrRet : rRet = compare posW pos := by
        have hwh0 : T.head.workHead = decide (pos = posW) := by simpa using hwh 0
        dsimp [rRet]; rw [hwh0]
        by_cases heq : pos = posW
        · simp [heq]
        · have hlt' : posW < pos := by omega
          simp [heq, compare_lt_iff_lt.mpr hlt']
      exact ⟨posW, pos, hT_next, hrRet⟩
    · have hwh0 : T.head.workHead = false := by
        have hne : pos ≠ posW := by omega
        simpa [hne] using hwh 0
      have hr : bennettRule M (.stepHistLeft e .gt, T.head) =
          some (.startReturn q' .gt, { T.head with hist := some e, histHead := true }) := by
        simp [bennettRule, hhist0, hhh0, hhm0, hm, hwh0]
      refine ⟨by simp [hr], ?_⟩
      rw [bennettReversibleTM_step_of_rule M ⟨_, T⟩ hr, bennettDirIn_startReturn]
      exact ⟨posW, pos, hT_next, (compare_gt_iff_gt.mpr hlt).symm⟩
  | startReturn q' rRet =>
    obtain ⟨posW, posH, hT, rfl⟩ := hv
    have hhh0 : T.head.histHead = true := by simpa using hT.histHead_eq 0
    have hhm0 : T.head.haltMark = false := hT.haltMark_false 0
    have hwh0 : T.head.workHead = decide (posW = posH) := by
      have h0 := hT.workHead_eq 0
      simp only [add_zero] at h0
      exact h0.trans (decide_eq_decide.mpr eq_comm)
    have hguard : (T.head.histHead && !T.head.haltMark &&
        (T.head.workHead == (compare posW posH == .eq))) = true := by
      rw [hhh0, hhm0, hwh0]
      simpa using decide_eq_beq_compare_eq posW posH
    rcases lt_trichotomy posW posH with hlt | rfl | hgt
    · have hc : compare posW posH = .lt := compare_lt_iff_lt.mpr hlt
      have hr : bennettRule M (.startReturn q' (compare posW posH), T.head) =
          some (.seekWorkLeft q', T.head) := by
        dsimp only [bennettRule]; rw [hguard, hc]; rfl
      refine ⟨by simp [hr], ?_⟩
      rw [bennettReversibleTM_step_of_rule M ⟨_, T⟩ hr, bennettDirIn_seekWorkLeft,
        bennettTape_write_head]
      exact ⟨posH - 1, posW, posH, hT.move_left, by omega, by omega⟩
    · have hc : compare posW posW = .eq := compare_eq_iff_eq.mpr rfl
      have hr : bennettRule M (.startReturn q' (compare posW posW), T.head) =
          some (.exec q' .eq, T.head) := by
        dsimp only [bennettRule]; rw [hguard, hc]; rfl
      refine ⟨by dsimp only; rw [hr]; rfl, ?_⟩
      rw [bennettReversibleTM_step_of_rule M ⟨_, T⟩ hr, bennettDirIn_exec, bennettTape_write_head]
      exact ⟨posW, posW, hT, hc.symm⟩
    · have hc : compare posW posH = .gt := compare_gt_iff_gt.mpr hgt
      have hr : bennettRule M (.startReturn q' (compare posW posH), T.head) =
          some (.seekWorkRight q', T.head) := by
        dsimp only [bennettRule]; rw [hguard, hc]; rfl
      refine ⟨by simp [hr], ?_⟩
      rw [bennettReversibleTM_step_of_rule M ⟨_, T⟩ hr, bennettDirIn_seekWorkRight,
        bennettTape_write_head]
      exact ⟨posH + 1, posW, posH, hT.move_right, by omega, by omega⟩
  | seekWorkLeft q' =>
    obtain ⟨pos, posW, posH, hT, hle, hlt⟩ := hv
    have hhh0 : T.head.histHead = false := by
      have hne : pos ≠ posH := by omega
      simpa [hne] using hT.histHead_eq 0
    have hhm0 : T.head.haltMark = false := hT.haltMark_false 0
    by_cases hp : pos = posW
    · subst hp
      have hwh0 : T.head.workHead = true := by simpa using hT.workHead_eq 0
      have hr : bennettRule M (.seekWorkLeft q', T.head) = some (.exec q' .lt, T.head) := by
        simp [bennettRule, hhh0, hhm0, hwh0]
      refine ⟨by simp [hr], ?_⟩
      rw [bennettReversibleTM_step_of_rule M ⟨_, T⟩ hr, bennettDirIn_exec, bennettTape_write_head]
      exact ⟨pos, posH, hT, (compare_lt_iff_lt.mpr hlt).symm⟩
    · have hwh0 : T.head.workHead = false := by
        simpa [hp] using hT.workHead_eq 0
      have hr : bennettRule M (.seekWorkLeft q', T.head) = some (.seekWorkLeft q', T.head) := by
        simp [bennettRule, hhh0, hhm0, hwh0]
      refine ⟨by simp [hr], ?_⟩
      rw [bennettReversibleTM_step_of_rule M ⟨_, T⟩ hr, bennettDirIn_seekWorkLeft,
        bennettTape_write_head]
      exact ⟨pos - 1, posW, posH, hT.move_left, by omega, by omega⟩
  | seekWorkRight q' =>
    obtain ⟨pos, posW, posH, hT, hlt, hle⟩ := hv
    have hhh0 : T.head.histHead = false := by
      have hne : pos ≠ posH := by omega
      simpa [hne] using hT.histHead_eq 0
    have hhm0 : T.head.haltMark = false := hT.haltMark_false 0
    by_cases hp : pos = posW
    · subst hp
      have hwh0 : T.head.workHead = true := by simpa using hT.workHead_eq 0
      have hr : bennettRule M (.seekWorkRight q', T.head) = some (.exec q' .gt, T.head) := by
        simp [bennettRule, hhh0, hhm0, hwh0]
      refine ⟨by simp [hr], ?_⟩
      rw [bennettReversibleTM_step_of_rule M ⟨_, T⟩ hr, bennettDirIn_exec, bennettTape_write_head]
      exact ⟨pos, posH, hT, (compare_gt_iff_gt.mpr hlt).symm⟩
    · have hwh0 : T.head.workHead = false := by
        simpa [hp] using hT.workHead_eq 0
      have hr : bennettRule M (.seekWorkRight q', T.head) = some (.seekWorkRight q', T.head) := by
        simp [bennettRule, hhh0, hhm0, hwh0]
      refine ⟨by simp [hr], ?_⟩
      rw [bennettReversibleTM_step_of_rule M ⟨_, T⟩ hr, bennettDirIn_seekWorkRight,
        bennettTape_write_head]
      exact ⟨pos + 1, posW, posH, hT.move_right, by omega, by omega⟩

private theorem validTrajectoryCfg_iterate_initCfg (M : FinTM0) (t : FinSupportedTape M) :
    ∀ k : ℕ, ValidTrajectoryCfg M ((bennettReversibleTM M).step^[k] (bennettInitCfg M t))
  | 0 => by
    dsimp only [Function.iterate_zero, id_eq, ValidTrajectoryCfg, bennettInitCfg]
    exact ⟨0, 0, activeTapeInv_initTape M t, rfl⟩
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    exact (validTrajectoryCfg_step M (validTrajectoryCfg_iterate_initCfg M t k)).2

private theorem invStep_bennettInitCfg (M : FinTM0) (t : FinSupportedTape M) :
    (bennettReversibleTM M).invStep (bennettInitCfg M t) =
      ⟨.startReturn default .eq, bennettInitTape M t⟩ := by
  let hd : BennettCell M := (bennettInitTape M t).head
  have hrule : bennettRule M (.startReturn default .eq, hd) = some (.exec default .eq, hd) := rfl
  have hperm : bennettStepPerm M (.startReturn default .eq, hd) = (.exec default .eq, hd) :=
    extendPartialInjPerm_eq_of_some (bennettRule M) (bennettRule_partial_injective M) hrule
  have hsymm : (bennettStepPerm M).symm (.exec default .eq, hd) = (.startReturn default .eq, hd) :=
    (bennettStepPerm M).symm_apply_eq.mpr hperm.symm
  unfold ReversibleTM.invStep bennettInitCfg
  dsimp only [bennettReversibleTM, bennettDirIn]
  change (⟨((bennettStepPerm M).symm (.exec default .eq, hd)).1,
    (bennettInitTape M t).write ((bennettStepPerm M).symm (.exec default .eq, hd)).2⟩ :
      (bennettReversibleTM M).Cfg) = _
  rw [hsymm, bennettTape_write_head]

/-- No positive iterate `m ≥ 1` of `(bennettReversibleTM M).step` returns `bennettInitCfg M t` to
itself (since `invStep (bennettInitCfg M t)` sits in `.startReturn default .eq` over `hist = none`,
which has no `bennettRule` preimage). -/
-- tier: T2
theorem bennettReversibleTM_iterate_step_initCfg_ne (M : FinTM0) (t : FinSupportedTape M)
    {m : ℕ} (hm : 1 ≤ m) :
    (bennettReversibleTM M).step^[m] (bennettInitCfg M t) ≠ bennettInitCfg M t := by
  intro heq
  rcases m with _ | m
  · omega
  · rcases m with _ | k
    · have hinv := congrArg (bennettReversibleTM M).invStep heq
      rw [Function.iterate_one, (bennettReversibleTM M).invStep_step,
        invStep_bennettInitCfg] at hinv
      have hq := congrArg ReversibleTM.Cfg.q hinv
      cases hq
    · let c_k := (bennettReversibleTM M).step^[k] (bennettInitCfg M t)
      have h2 : (bennettReversibleTM M).step ((bennettReversibleTM M).step c_k) =
          bennettInitCfg M t := by
        simpa only [Function.iterate_succ_apply', c_k] using heq
      have h1 : (bennettReversibleTM M).step c_k =
          ⟨.startReturn default .eq, bennettInitTape M t⟩ := by
        have hinv := congrArg (bennettReversibleTM M).invStep h2
        rwa [(bennettReversibleTM M).invStep_step, invStep_bennettInitCfg] at hinv
      have hisSome := (validTrajectoryCfg_step M (validTrajectoryCfg_iterate_initCfg M t k)).1
      obtain ⟨⟨q', b⟩, hrule⟩ := Option.isSome_iff_exists.mp hisSome
      have hstep := bennettReversibleTM_step_of_rule M c_k hrule
      rw [h1] at hstep
      have hq' : q' = .startReturn default .eq := by
        rcases hdir : bennettDirIn q' <;> rw [hdir] at hstep <;>
          exact (congrArg ReversibleTM.Cfg.q hstep).symm
      subst hq'
      rw [bennettDirIn_startReturn] at hstep
      have htape := congrArg (fun c : (bennettReversibleTM M).Cfg ↦ c.Tape.head) hstep
      change (bennettInitTape M t).head = (c_k.Tape.write b).head at htape
      rw [tape_write_head] at htape
      subst htape
      have hinv_rule := bennettRuleInv_of_some M hrule
      cases hinv_rule

/-- The forward reversible orbit `n ↦ (bennettReversibleTM M).step^[n] (bennettInitCfg M t)` is
injective (`Function.Injective`) for every `M : FinTM0` and `t : FinSupportedTape M`. -/
-- tier: T1
theorem bennettReversibleTM_orbit_initCfg_injective (M : FinTM0) (t : FinSupportedTape M) :
    Function.Injective
      (fun n : ℕ ↦ (bennettReversibleTM M).step^[n] (bennettInitCfg M t)) := by
  intro n₁ n₂ h
  dsimp only at h
  rcases lt_trichotomy n₁ n₂ with hlt | rfl | hgt
  · have hdecomp : n₂ = n₁ + (n₂ - n₁) := by omega
    rw [hdecomp, Function.iterate_add_apply] at h
    have hper := ((bennettReversibleTM M).stepEquiv.injective.iterate n₁ h).symm
    exact absurd hper (bennettReversibleTM_iterate_step_initCfg_ne M t (by omega))
  · rfl
  · have hdecomp : n₁ = n₂ + (n₁ - n₂) := by omega
    rw [hdecomp, Function.iterate_add_apply] at h
    have hper := (bennettReversibleTM M).stepEquiv.injective.iterate n₂ h
    exact absurd hper (bennettReversibleTM_iterate_step_initCfg_ne M t (by omega))

/-! ## 4. Gate G5 Concrete Anti-Vacuity Witnesses -/

/-- Global shift bijectivity of `(bennettReversibleTM M).toGeneralizedShift.eval` on
`ℤ → (bennettReversibleTM M).ShiftAlphabet` (`CMPP21` Proposition 4.4, **UNCONDITIONAL**). -/
-- tier: T1
theorem bennettReversibleTM_eval_bijective (M : FinTM0) :
    Function.Bijective (bennettReversibleTM M).toGeneralizedShift.eval :=
  (bennettReversibleTM M).bijective_eval

/-- Concrete 4-state `FinTM0` witness exercising all four `TM0` transition branches:
* state `0` (`default`): `.write true` → state `1`,
* state `1`: `.move .right` → state `2`,
* state `2`: `.move .left` → state `3`,
* state `3`: `none` (halt with `true` at `0` and `false` elsewhere). -/
def bennettToyHalt : FinTM0 where
  Γ := Bool
  Λ := Fin 4
  machine q _ :=
    match q.1 with
    | 0 => some (1, TM0.Stmt.write true)
    | 1 => some (2, TM0.Stmt.move Dir.right)
    | 2 => some (3, TM0.Stmt.move Dir.left)
    | _ => none

/-- Expected radius-`1` halting output window `[false, true, false]` of `bennettToyHalt` on the
blank tape `default`. -/
def bennettToyHaltWindow : Window bennettToyHalt 1 :=
  fun i ↦ decide (i.1 = 0)

/-- Terminal configuration reached by `bennettToyHalt` after `3` transitions from `default`. -/
def bennettToyHaltTerminalCfg : TM0.Cfg bennettToyHalt.Γ bennettToyHalt.Λ :=
  { q := (3 : Fin 4)
    Tape := (((default : Tape Bool).write true).move Dir.right).move Dir.left }

/-- `bennettToyHalt` halts in `3` steps from `default` with window `bennettToyHaltWindow`. -/
-- tier: T1
theorem bennettToyHalt_haltsWithWindow :
    HaltsWithWindow bennettToyHalt default 1 bennettToyHaltWindow := by
  rw [haltsWithWindow_iff_exists_steps]
  refine ⟨3, bennettToyHaltTerminalCfg, rfl, rfl, ?_⟩
  rintro ⟨i, hi⟩
  have hcases : i = -1 ∨ i = 0 ∨ i = 1 := by
    have h1 : -1 ≤ i := by simpa using hi.1
    have h2 : i ≤ 1 := by simpa using hi.2
    omega
  rcases hcases with rfl | rfl | rfl <;>
    (simp only [bennettToyHaltTerminalCfg, bennettToyHaltWindow]; rfl)

/-- **Gate G5 Halting Witness (`UNCONDITIONAL`)**:
`bennettReversibleTM bennettToyHalt` has a bijective generalized shift and reaches `.halted` at some
positive iterate `n ≥ 1` reproducing `bennettToyHaltWindow` on `[-1, 1]`. -/
-- tier: T2
theorem bennettToyHalt_reversible_reaches_halted :
    Function.Bijective (bennettReversibleTM bennettToyHalt).toGeneralizedShift.eval ∧
    ∃ n ≥ 1, ∃ (q : bennettToyHalt.Λ) (rel : Ordering),
      ((bennettReversibleTM bennettToyHalt).step^[n]
        (bennettInitCfg bennettToyHalt default)).q = .halted q rel ∧
      ∀ i : Set.Icc (-1 : ℤ) 1,
        (((bennettReversibleTM bennettToyHalt).step^[n]
          (bennettInitCfg bennettToyHalt default)).Tape.nth i.1).sym =
            bennettToyHaltWindow i := by
  refine ⟨bennettReversibleTM_eval_bijective bennettToyHalt, ?_⟩
  obtain ⟨n, q, rel, hq, hwin⟩ :=
    (bennett_orbit_halted_iff bennettToyHalt default 1 bennettToyHaltWindow).mpr
      bennettToyHalt_haltsWithWindow
  have hn0 : n ≠ 0 := by
    intro h0
    subst h0
    exact bennettInitCfg_q_ne_halted bennettToyHalt default q rel hq
  exact ⟨n, by omega, q, rel, hq, hwin⟩

/-- Concrete non-halting `FinTM0` witness that moves right forever on every symbol. -/
def bennettToyLoop : FinTM0 where
  Γ := Bool
  Λ := Unit
  machine _ _ := some ((), TM0.Stmt.move Dir.right)

/-- **Gate G5 Non-Halting Witness (`UNCONDITIONAL`)**:
`bennettReversibleTM bennettToyLoop` has a bijective generalized shift and never enters `.halted` at
any iterate `n : ℕ` from any initial tape `t`. -/
-- tier: T2
theorem bennettToyLoop_never_halted (t : FinSupportedTape bennettToyLoop)
    (n : ℕ) (q : bennettToyLoop.Λ) (rel : Ordering) :
    ((bennettReversibleTM bennettToyLoop).step^[n] (bennettInitCfg bennettToyLoop t)).q ≠
      .halted q rel := by
  intro hq
  obtain ⟨c, _, _, hterm, _⟩ := bennett_orbit_halted_backward bennettToyLoop t hq
  rcases c with ⟨_, _⟩
  simp [bennettToyLoop, TM0.step] at hterm

end S4TuringPoisson.Reversible
