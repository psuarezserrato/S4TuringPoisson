/-
Copyright (c) 2026 Pablo Suárez-Serrato. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Suárez-Serrato
-/
module

public import Mathlib.Computability.TuringMachine.ToPartrec
public import S4TuringPoisson.Interfaces

/-!
# Algorithmic Undecidability of Orbit Reachability & Fiber-to-4-Manifold Transfer (Milestone M3.2)

This module implements Milestone M3.2 of `S4TuringPoisson`:

1. **Universal `FinTM0` Halting Reduction & Algorithmic Undecidability Transfer**:
   - Restricts any finitely supported `Turing.TM0.Machine` (`Turing.TM0.Supports`) to a concrete
     `FinTM0` machine (`restrictSupportedTM0`), and wraps any `FinTM0` machine with a 1-step
     head-clearing halt state (`FinTM0.cleanHalt`) so plain halting becomes equivalent to
     `HaltsWithWindow _ _ 0 (fun _ ↦ default)`.
   - Instantiates Mathlib's `PartrecToTM2` → `TM2to1` → `TM1to0` pipeline on the universal partial
     recursive evaluator `(Denumerable.ofNat Nat.Partrec.Code e).eval 0` to obtain a **single
     fixed** universal machine `universalHaltingTM0 : FinTM0` and primitive-recursive input tapes
     `universalInputTape c` such that:
     $$
       \text{HaltsWithWindow}\;\text{universalHaltingTM0}\;(\text{universalInputTape}\;c)\;0\;
         \text{universalTargetWindow}
       \;\iff\; (c.\text{eval}\;0).\text{Dom}.
     $$
   - Deduces from `ComputablePred.halting_problem` (`Mathlib.Computability.Halting`) that for
     **any** topological space `X` and self-map `φ : X → X` satisfying `IsTuringComplete φ`, there
     exist a single nonempty constructible open target `U : Opens X` and a computably constructible
     family of initial points `p : Nat.Partrec.Code → X` (equipped with a uniform `Computable` `2⁻ᵐ`
     rational chart approximation generator) such that forward-orbit reachability
     `∃ n : ℕ, φ^[n] (p c) ∈ U` is recursively enumerable (`REPred`) yet **algorithmically
     undecidable** (`¬ ComputablePred`), ruling out any total computable decision procedure.

2. **Fiber-to-4-Manifold Transfer (`TuringCompleteWitness.transfer`, `IsTuringComplete.transfer`)**:
   - Given a topological space `M`, base space `B`, fiber space `Y` (in particular `UnitDisk2`), an
     open embedding `Ψ : B × Y → M`, an open subset `B₀` of `B` containing a basepoint `c ∈ B₀`, a
     fiber map `d : Y → Y`, and a global map `d_bar : M → M` satisfying
     `∀ b ∈ B₀, ∀ y : Y, d_bar (Ψ (b, y)) = Ψ (b, d y)`, proves:
     - `∀ n : ℕ, d_bar^[n] (Ψ (c, p)) = Ψ (c, d^[n] p)`,
     - exact orbit-entry equivalence into lifted open product targets `Ψ '' (B₀ ×ˢ U)`, and
     - `IsTuringComplete d → IsTuringComplete d_bar`, preserving `W.computable_approx` verbatim via
       `chart' := fun y ↦ Ψ (c, W.chart y)` and `coordPoint' := W.coordPoint`.
-/

@[expose] public section

open Denumerable Encodable Relation Set TopologicalSpace
open scoped Topology

namespace S4TuringPoisson

/-! ## 1. Finite-State Restriction & Clean-Halting `FinTM0` Reduction -/

section TM0Reduction

/-- Restrict a `Turing.TM0.Machine Γ Λ` supported on a finite state set `S : Finset Λ`
(`Turing.TM0.Supports M₀ ↑S`) to a bona fide `FinTM0` machine with state space `↥S`. -/
noncomputable def restrictSupportedTM0 {Γ Λ : Type} [Fintype Γ] [DecidableEq Γ] [Inhabited Γ]
    [Inhabited Λ] (M₀ : Turing.TM0.Machine Γ Λ) (S : Finset Λ)
    (hs : Turing.TM0.Supports M₀ ↑S) : FinTM0 :=
  let _ : DecidableEq Λ := Classical.decEq Λ
  let _ : Inhabited ↥S := ⟨⟨default, hs.1⟩⟩
  { Γ := Γ
    Λ := ↥S
    machine := fun q a ↦
      match h : M₀ q.1 a with
      | none => none
      | some (q', stmt) => some (⟨q', hs.2 h q.2⟩, stmt) }

/-- Forgetful configuration map from `restrictSupportedTM0 M₀ S hs` back to
`Turing.TM0.Cfg Γ Λ`. -/
def liftRestrictedCfg {Γ Λ : Type} [Fintype Γ] [DecidableEq Γ] [Inhabited Γ] [Inhabited Λ]
    {M₀ : Turing.TM0.Machine Γ Λ} {S : Finset Λ} (hs : Turing.TM0.Supports M₀ ↑S)
    (c : Turing.TM0.Cfg (restrictSupportedTM0 M₀ S hs).Γ (restrictSupportedTM0 M₀ S hs).Λ) :
    Turing.TM0.Cfg Γ Λ :=
  ⟨c.q.1, c.Tape⟩

theorem step_restrictSupportedTM0 {Γ Λ : Type} [Fintype Γ] [DecidableEq Γ] [Inhabited Γ]
    [Inhabited Λ] (M₀ : Turing.TM0.Machine Γ Λ) (S : Finset Λ)
    (hs : Turing.TM0.Supports M₀ ↑S)
    (c : Turing.TM0.Cfg (restrictSupportedTM0 M₀ S hs).Γ (restrictSupportedTM0 M₀ S hs).Λ) :
    (Turing.TM0.step (restrictSupportedTM0 M₀ S hs).machine c).map (liftRestrictedCfg hs) =
      Turing.TM0.step M₀ (liftRestrictedCfg hs c) := by
  suffices ∀ (q : ↥S) (T : Turing.Tape Γ),
      (Turing.TM0.step (restrictSupportedTM0 M₀ S hs).machine ⟨q, T⟩).map
        (liftRestrictedCfg hs) = Turing.TM0.step M₀ ⟨q.1, T⟩ from
    this c.q c.Tape
  intro ⟨q, hq⟩ T
  unfold Turing.TM0.step restrictSupportedTM0 liftRestrictedCfg
  dsimp only
  split
  · next h =>
    exact (congrArg (Option.map _) h).symm
  · next q' stmt h =>
    refine Eq.trans ?_ (congrArg (Option.map _) h).symm
    cases stmt <;> rfl

/-- Halting of `restrictSupportedTM0 M₀ S hs` from `Tape.mk₁ l` is equivalent to
`(TM0.eval M₀ l).Dom`. -/
theorem exists_halts_restrictSupportedTM0_iff_eval_dom {Γ Λ : Type} [Fintype Γ] [DecidableEq Γ]
    [Inhabited Γ] [Inhabited Λ] (M₀ : Turing.TM0.Machine Γ Λ) (S : Finset Λ)
    (hs : Turing.TM0.Supports M₀ ↑S) (l : List Γ) :
    (∃ c, Turing.TM0.Reaches (restrictSupportedTM0 M₀ S hs).machine
        ((restrictSupportedTM0 M₀ S hs).initCfg (Turing.Tape.mk₁ l)) c ∧
      Turing.TM0.step (restrictSupportedTM0 M₀ S hs).machine c = none) ↔
      (Turing.TM0.eval M₀ l).Dom := by
  let Mf := restrictSupportedTM0 M₀ S hs
  have hdom : (Turing.TM0.eval M₀ l).Dom ↔
      ∃ c₀, Turing.TM0.Reaches M₀ (Turing.TM0.init l) c₀ ∧ Turing.TM0.step M₀ c₀ = none := by
    simp only [Turing.TM0.eval, Part.dom_iff_mem, Part.mem_map_iff, StateTransition.mem_eval]
    constructor
    · rintro ⟨_, ⟨c₀, hc₀, rfl⟩⟩
      exact ⟨c₀, hc₀⟩
    · rintro ⟨c₀, hc₀⟩
      exact ⟨c₀.Tape.right₀, c₀, hc₀, rfl⟩
  rw [hdom]
  constructor
  · rintro ⟨c, hreach, hnone⟩
    have hreach₀ : ∀ {a b}, Turing.TM0.Reaches Mf.machine a b →
        Turing.TM0.Reaches M₀ (liftRestrictedCfg hs a) (liftRestrictedCfg hs b) := by
      intro a b hr
      induction hr with
      | refl => exact ReflTransGen.refl
      | @tail x y _ hxy ih =>
        refine ih.tail ?_
        have hst := step_restrictSupportedTM0 M₀ S hs x
        rw [hxy] at hst
        exact hst.symm
    refine ⟨liftRestrictedCfg hs c, hreach₀ hreach, ?_⟩
    have hst := step_restrictSupportedTM0 M₀ S hs c
    rw [hnone] at hst
    exact hst.symm
  · rintro ⟨c₀, hreach, hnone⟩
    have hpull : ∀ {a₀ b₀}, Turing.TM0.Reaches M₀ a₀ b₀ →
        ∀ a : Turing.TM0.Cfg Mf.Γ Mf.Λ, liftRestrictedCfg hs a = a₀ →
          ∃ b : Turing.TM0.Cfg Mf.Γ Mf.Λ,
            liftRestrictedCfg hs b = b₀ ∧ Turing.TM0.Reaches Mf.machine a b := by
      intro a₀ b₀ hr
      induction hr with
      | refl =>
        intro a ha
        exact ⟨a, ha, ReflTransGen.refl⟩
      | @tail x₀ y₀ _ hxy ih =>
        intro a ha
        obtain ⟨x, rfl, hax⟩ := ih a ha
        have hst := step_restrictSupportedTM0 M₀ S hs x
        rw [hxy] at hst
        rcases hxstep : Turing.TM0.step Mf.machine x with _ | y
        · rw [hxstep] at hst
          cases hst
        · rw [hxstep, Option.map_some, Option.some.injEq] at hst
          exact ⟨y, hst, hax.tail hxstep⟩
    obtain ⟨c, rfl, hc⟩ := hpull hreach (Mf.initCfg (Turing.Tape.mk₁ l)) rfl
    refine ⟨c, hc, ?_⟩
    have hst := step_restrictSupportedTM0 M₀ S hs c
    rw [hnone, Option.map_eq_none_iff] at hst
    exact hst

/-- Wrap a `FinTM0` machine `M` so that instead of halting immediately with an unknown symbol under
the head, it writes `default : M.Γ` at cell `0` and transitions to a clean-halting flag
`(true, q)`, halting on the very next step. Consequently, plain halting of `M` becomes equivalent
to `HaltsWithWindow M.cleanHalt t 0 (fun _ ↦ default)`. -/
def FinTM0.cleanHalt (M : FinTM0) : FinTM0 where
  Γ := M.Γ
  Λ := Bool × M.Λ
  machine state a :=
    match state.1 with
    | false =>
      match M.machine state.2 a with
      | some (q', stmt) => some ((false, q'), stmt)
      | none => some ((true, state.2), Turing.TM0.Stmt.write default)
    | true => none

/-- `M.cleanHalt` never halts at step `0` because its initial state `(false, default)` always emits
`some`. -/
theorem FinTM0.step_initCfg_cleanHalt_ne_none (M : FinTM0) (t : FinSupportedTape M.cleanHalt) :
    Turing.TM0.step M.cleanHalt.machine (M.cleanHalt.initCfg t) ≠ none := by
  dsimp only [FinTM0.cleanHalt, FinTM0.initCfg, Turing.TM0.step]
  change (match (false : Bool) with
    | false =>
      match M.machine default t.1 with
      | some (q', stmt) => some ((false, q'), stmt)
      | none => some ((true, default), Turing.TM0.Stmt.write default)
    | true => none).map _ ≠ none
  rcases M.machine default t.1 with _ | ⟨q', stmt⟩ <;> simp

/-- Lift a boolean flag, `M`-state, and `M`-tape into a configuration of `M.cleanHalt`. -/
def FinTM0.mkCleanCfg (M : FinTM0) (b : Bool) (q : M.Λ) (T : Turing.Tape M.Γ) :
    Turing.TM0.Cfg M.cleanHalt.Γ M.cleanHalt.Λ :=
  { q := (b, q), Tape := T }

theorem FinTM0.step_cleanHalt_of_step_eq_some (M : FinTM0)
    {c c' : Turing.TM0.Cfg M.Γ M.Λ} (hstep : Turing.TM0.step M.machine c = some c') :
    Turing.TM0.step M.cleanHalt.machine (M.mkCleanCfg false c.q c.Tape) =
      some (M.mkCleanCfg false c'.q c'.Tape) := by
  rcases c with ⟨q, T⟩
  simp only [Turing.TM0.step] at hstep
  rcases hm : M.machine q T.1 with _ | ⟨q', stmt⟩
  · simp [hm] at hstep
  · simp only [hm, Option.map_some, Option.some.injEq] at hstep
    subst hstep
    rcases stmt <;> (simp only [FinTM0.cleanHalt, FinTM0.mkCleanCfg, Turing.TM0.step, hm,
      Option.map_some, Option.some.injEq]; exact rfl)

theorem FinTM0.stepOpt_cleanHalt_of_stepOpt (M : FinTM0) :
    ∀ {n : ℕ} {c₀ c : Turing.TM0.Cfg M.Γ M.Λ},
      M.stepOpt^[n] (some c₀) = some c →
      M.cleanHalt.stepOpt^[n] (some (M.mkCleanCfg false c₀.q c₀.Tape)) =
        some (M.mkCleanCfg false c.q c.Tape)
  | 0, _, _, h => by
    cases h
    rfl
  | n + 1, c₀, c, h => by
    rw [Function.iterate_succ_apply] at h ⊢
    change M.stepOpt^[n] (Turing.TM0.step M.machine c₀) = some c at h
    rcases h1 : Turing.TM0.step M.machine c₀ with _ | c₁
    · rw [h1, M.iterate_stepOpt_none] at h
      cases h
    · rw [h1] at h
      change M.cleanHalt.stepOpt^[n]
        (Turing.TM0.step M.cleanHalt.machine (M.mkCleanCfg false c₀.q c₀.Tape)) = _
      rw [M.step_cleanHalt_of_step_eq_some h1]
      exact M.stepOpt_cleanHalt_of_stepOpt h

theorem FinTM0.cleanHalt_dichotomy (M : FinTM0) (c₀ : Turing.TM0.Cfg M.Γ M.Λ) :
    ∀ n : ℕ,
      (∃ c, M.stepOpt^[n] (some c₀) = some c ∧
        M.cleanHalt.stepOpt^[n] (some (M.mkCleanCfg false c₀.q c₀.Tape)) =
          some (M.mkCleanCfg false c.q c.Tape)) ∨
      (∃ m c, m < n ∧ M.stepOpt^[m] (some c₀) = some c ∧ Turing.TM0.step M.machine c = none)
  | 0 => Or.inl ⟨c₀, rfl, rfl⟩
  | n + 1 => by
    rcases M.cleanHalt_dichotomy c₀ n with ⟨c, hn, hclean⟩ | ⟨m, c, hmn, hm, hterm⟩
    · rcases hstep : Turing.TM0.step M.machine c with _ | c'
      · exact Or.inr ⟨n, c, Nat.lt_succ_self n, hn, hstep⟩
      · refine Or.inl ⟨c', ?_, ?_⟩
        · rw [Function.iterate_succ_apply', hn]
          exact hstep
        · rw [Function.iterate_succ_apply', hclean]
          exact M.step_cleanHalt_of_step_eq_some hstep
    · exact Or.inr ⟨m, c, Nat.lt_succ_of_lt hmn, hm, hterm⟩

/-- `HaltsWithWindow M.cleanHalt t 0 (fun _ ↦ default)` holds if and only if `M` halts from
`M.initCfg t`. -/
theorem FinTM0.haltsWithWindow_cleanHalt_iff (M : FinTM0) (t : FinSupportedTape M) :
    HaltsWithWindow M.cleanHalt t 0 (fun _ ↦ default) ↔
      ∃ c, Turing.TM0.Reaches M.machine (M.initCfg t) c ∧ Turing.TM0.step M.machine c = none := by
  rw [haltsWithWindow_iff_exists_steps M.cleanHalt t 0]
  constructor
  · rintro ⟨n, c', hn, hterm, _⟩
    have hinit : M.cleanHalt.initCfg t = M.mkCleanCfg false (M.initCfg t).q (M.initCfg t).Tape :=
      rfl
    rw [hinit] at hn
    rcases M.cleanHalt_dichotomy (M.initCfg t) n with ⟨c, _, hclean⟩ | ⟨m, c, _, hm, hnone⟩
    · rw [hclean, Option.some.injEq] at hn
      subst hn
      rcases hm : M.machine c.q c.Tape.1 with _ | ⟨q', stmt⟩ <;>
        simp [FinTM0.cleanHalt, FinTM0.mkCleanCfg, Turing.TM0.step, hm] at hterm
    · exact ⟨c, (M.reaches_iff_exists_iterate_stepOpt _ _).mpr ⟨m, hm⟩, hnone⟩
  · rintro ⟨c, hreach, hnone⟩
    obtain ⟨m, hm⟩ := (M.reaches_iff_exists_iterate_stepOpt _ _).mp hreach
    have hclean := M.stepOpt_cleanHalt_of_stepOpt hm
    have hnone_raw : M.machine c.q c.Tape.1 = none := by
      rcases c with ⟨q, T⟩
      simpa [Turing.TM0.step] using hnone
    refine ⟨m + 1, M.mkCleanCfg true c.q (c.Tape.write default), ?_, ?_, ?_⟩
    · have hinit : M.cleanHalt.initCfg t =
          M.mkCleanCfg false (M.initCfg t).q (M.initCfg t).Tape := rfl
      rw [hinit, Function.iterate_succ_apply', hclean]
      simp only [FinTM0.stepOpt, FinTM0.cleanHalt, FinTM0.mkCleanCfg, Turing.TM0.step, hnone_raw,
        Option.bind_some, Option.map_some, Option.some.injEq]
      exact rfl
    · simp [FinTM0.cleanHalt, FinTM0.mkCleanCfg, Turing.TM0.step]
    · rintro ⟨i, hi⟩
      obtain ⟨hi1, hi2⟩ := hi
      have hi0 : i = 0 := by omega
      subst hi0
      rfl

end TM0Reduction

/-! ## 2. Universal Halting `FinTM0` Machine & Undecidability of Orbit Reachability -/

section UniversalHalting

/-- Universal partial recursive 1-argument function `e ↦ (ofNat Code e).eval 0`. -/
def universalEvalAtZero (e : ℕ) : Part ℕ :=
  (Denumerable.ofNat Nat.Partrec.Code e).eval 0

theorem partrec_universalEvalAtZero : Partrec universalEvalAtZero :=
  Nat.Partrec.Code.eval_part.comp (Computable.ofNat Nat.Partrec.Code) (Computable.const 0)

/-- Simplified `Turing.ToPartrec.Code` program computing `universalEvalAtZero`. -/
noncomputable def universalToPartrecCode : Turing.ToPartrec.Code :=
  Classical.choose
    (Turing.ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr partrec_universalEvalAtZero))

theorem universalToPartrecCode_eval (e : ℕ) :
    universalToPartrecCode.eval [e] = pure <$> universalEvalAtZero e :=
  Classical.choose_spec
    (Turing.ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr partrec_universalEvalAtZero))
    ⟨[e], rfl⟩

/-- Explicit 4-element equivalence `PartrecToTM2.K' ≃ Fin 4` furnishing `Fintype K'`. -/
def kPrimeEquivFin4 : Turing.PartrecToTM2.K' ≃ Fin 4 where
  toFun
    | .main => 0
    | .rev => 1
    | .aux => 2
    | .stack => 3
  invFun
    | ⟨0, _⟩ => .main
    | ⟨1, _⟩ => .rev
    | ⟨2, _⟩ => .aux
    | ⟨3, _⟩ => .stack
  left_inv k := by cases k <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance instFintypePartrecToTM2K' : Fintype Turing.PartrecToTM2.K' :=
  Fintype.ofEquiv (Fin 4) kPrimeEquivFin4.symm

/-- Finite tape alphabet `Bool × (K' → Option Γ')` of the universal `TM2to1` / `TM1to0` machine. -/
abbrev UniversalAlphabet : Type :=
  Turing.TM2to1.Γ' Turing.PartrecToTM2.K' (fun _ ↦ Turing.PartrecToTM2.Γ')

instance instDecidableEqUniversalAlphabet : DecidableEq UniversalAlphabet :=
  inferInstanceAs (DecidableEq (Bool × (Turing.PartrecToTM2.K' → Option Turing.PartrecToTM2.Γ')))

/-- `Inhabited` instance on `PartrecToTM2.Λ'` pointing at the start state of
`universalToPartrecCode` with `Cont'.halt`. -/
@[instance_reducible]
noncomputable def instInhabitedUniversalΛ₂ : Inhabited Turing.PartrecToTM2.Λ' :=
  ⟨Turing.PartrecToTM2.trNormal universalToPartrecCode Turing.PartrecToTM2.Cont'.halt⟩

/-- Raw `TM1` simulator of the universal `PartrecToTM2` stack machine. -/
noncomputable def universalTM1 :=
  let _ : Inhabited Turing.PartrecToTM2.Λ' := instInhabitedUniversalΛ₂
  Turing.TM2to1.tr Turing.PartrecToTM2.tr

/-- Raw `TM0` simulator of `universalTM1`. -/
noncomputable def universalRawTM0 :=
  let _ : Inhabited Turing.PartrecToTM2.Λ' := instInhabitedUniversalΛ₂
  Turing.TM1to0.tr universalTM1

/-- Finite reachable state set supporting `universalRawTM0`. -/
noncomputable def universalStateFinset :=
  let _ : Inhabited Turing.PartrecToTM2.Λ' := instInhabitedUniversalΛ₂
  let S₂ := Turing.PartrecToTM2.codeSupp universalToPartrecCode Turing.PartrecToTM2.Cont'.halt
  let S₁ := Turing.TM2to1.trSupp Turing.PartrecToTM2.tr S₂
  Turing.TM1to0.trStmts universalTM1 S₁

theorem supports_universalRawTM0 :
    let _ : Inhabited Turing.PartrecToTM2.Λ' := instInhabitedUniversalΛ₂
    Turing.TM0.Supports universalRawTM0 ↑universalStateFinset := by
  let _ : Inhabited Turing.PartrecToTM2.Λ' := instInhabitedUniversalΛ₂
  have hs₂ := Turing.PartrecToTM2.tr_supports universalToPartrecCode Turing.PartrecToTM2.Cont'.halt
  have hs₁ := Turing.TM2to1.tr_supports Turing.PartrecToTM2.tr hs₂
  exact Turing.TM1to0.tr_supports universalTM1 hs₁

/-- **Single fixed universal `FinTM0` machine** whose clean-halting window queries capture the
halting problem `(c.eval 0).Dom` across all `c : Nat.Partrec.Code`. -/
noncomputable def universalHaltingTM0 : FinTM0 :=
  let _ : Inhabited Turing.PartrecToTM2.Λ' := instInhabitedUniversalΛ₂
  (restrictSupportedTM0 universalRawTM0 universalStateFinset supports_universalRawTM0).cleanHalt

/-- Encoded input tape list for `c : Nat.Partrec.Code` fed into `universalHaltingTM0`. -/
def universalInputList (c : Nat.Partrec.Code) : List UniversalAlphabet :=
  Turing.TM2to1.trInit (Γ := fun _ ↦ Turing.PartrecToTM2.Γ') Turing.PartrecToTM2.K'.main
    (Turing.PartrecToTM2.trList [Encodable.encode c])

/-- Encoded initial `Turing.Tape` (`Tape.mk₁ (universalInputList c)`) for `c : Nat.Partrec.Code`. -/
noncomputable def universalInputTape (c : Nat.Partrec.Code) :
    FinSupportedTape universalHaltingTM0 :=
  Turing.Tape.mk₁ (universalInputList c)

/-- Fixed radius-`0` target window `fun _ ↦ default` for `universalHaltingTM0`. -/
noncomputable def universalTargetWindow : Window universalHaltingTM0 0 :=
  fun _ ↦ default

/-- `universalHaltingTM0` never halts at step `0` on any input code `c`. -/
theorem step_initCfg_universalHaltingTM0_ne_none (c : Nat.Partrec.Code) :
    Turing.TM0.step universalHaltingTM0.machine
      (universalHaltingTM0.initCfg (universalInputTape c)) ≠ none := by
  let _ : Inhabited Turing.PartrecToTM2.Λ' := instInhabitedUniversalΛ₂
  exact FinTM0.step_initCfg_cleanHalt_ne_none
    (restrictSupportedTM0 universalRawTM0 universalStateFinset supports_universalRawTM0)
    (universalInputTape c)

/-- Exact simulation equivalence between `HaltsWithWindow` on the single fixed machine
`universalHaltingTM0` and Mathlib's halting predicate `(c.eval 0).Dom`. -/
theorem haltsWithWindow_universalHaltingTM0_iff (c : Nat.Partrec.Code) :
    HaltsWithWindow universalHaltingTM0 (universalInputTape c) 0 universalTargetWindow ↔
      (c.eval 0).Dom := by
  let _ : Inhabited Turing.PartrecToTM2.Λ' := instInhabitedUniversalΛ₂
  refine (FinTM0.haltsWithWindow_cleanHalt_iff
    (restrictSupportedTM0 universalRawTM0 universalStateFinset supports_universalRawTM0)
    (Turing.Tape.mk₁ (universalInputList c))).trans ?_
  refine (exists_halts_restrictSupportedTM0_iff_eval_dom universalRawTM0 universalStateFinset
    supports_universalRawTM0 (universalInputList c)).trans ?_
  dsimp only [universalRawTM0]
  rw [Turing.TM1to0.tr_eval]
  dsimp only [universalTM1, universalInputList]
  refine (Turing.TM2to1.tr_eval_dom Turing.PartrecToTM2.tr Turing.PartrecToTM2.K'.main
    (Turing.PartrecToTM2.trList [Encodable.encode c])).trans ?_
  have hinit_eq :
      (@Turing.TM2.init Turing.PartrecToTM2.K' (fun _ ↦ Turing.PartrecToTM2.Γ')
        Turing.PartrecToTM2.Λ' (Option Turing.PartrecToTM2.Γ') instInhabitedUniversalΛ₂ _
        inferInstance Turing.PartrecToTM2.K'.main
        (Turing.PartrecToTM2.trList [Encodable.encode c])) =
      Turing.PartrecToTM2.init universalToPartrecCode [Encodable.encode c] := by
    unfold Turing.TM2.init Turing.PartrecToTM2.init instInhabitedUniversalΛ₂
    congr 1
    funext k
    cases k <;> rfl
  have hstep_eq :
      StateTransition.eval (Turing.TM2.step Turing.PartrecToTM2.tr)
        (@Turing.TM2.init Turing.PartrecToTM2.K' (fun _ ↦ Turing.PartrecToTM2.Γ')
          Turing.PartrecToTM2.Λ' (Option Turing.PartrecToTM2.Γ') instInhabitedUniversalΛ₂ _
          inferInstance Turing.PartrecToTM2.K'.main
          (Turing.PartrecToTM2.trList [Encodable.encode c])) =
        Turing.PartrecToTM2.halt <$> universalToPartrecCode.eval [Encodable.encode c] :=
    (congrArg (StateTransition.eval (Turing.TM2.step Turing.PartrecToTM2.tr)) hinit_eq).trans
      (Turing.PartrecToTM2.tr_eval universalToPartrecCode [Encodable.encode c])
  refine (Eq.to_iff (congrArg Part.Dom hstep_eq)).trans ?_
  refine (Eq.to_iff (congrArg Part.Dom (universalToPartrecCode_eval (Encodable.encode c)))).trans ?_
  simp [universalEvalAtZero, Denumerable.ofNat_encode]

/-! ### Uniform Computability of `universalInputList` & Chart Approximations -/

/-- Little-endian binary increment on `List PartrecToTM2.Γ'` matching `PosNum.succ` / `Num.succ`. -/
def succΓ'List : List Turing.PartrecToTM2.Γ' → List Turing.PartrecToTM2.Γ'
  | [] => [Turing.PartrecToTM2.Γ'.bit1]
  | Turing.PartrecToTM2.Γ'.bit1 :: l => Turing.PartrecToTM2.Γ'.bit0 :: succΓ'List l
  | _ :: l => Turing.PartrecToTM2.Γ'.bit1 :: l

theorem succΓ'List_trPosNum :
    ∀ p : PosNum,
      succΓ'List (Turing.PartrecToTM2.trPosNum p) = Turing.PartrecToTM2.trPosNum p.succ
  | .one => rfl
  | .bit1 p => congrArg (List.cons Turing.PartrecToTM2.Γ'.bit0) (succΓ'List_trPosNum p)
  | .bit0 _ => rfl

theorem succΓ'List_trNum :
    ∀ x : Num, succΓ'List (Turing.PartrecToTM2.trNum x) = Turing.PartrecToTM2.trNum x.succ
  | .zero => rfl
  | .pos p => succΓ'List_trPosNum p

theorem trNat_eq_iterate_succΓ'List :
    ∀ n : ℕ, Turing.PartrecToTM2.trNat n = succΓ'List^[n] []
  | 0 => rfl
  | n + 1 => by
    have hsucc : ((n + 1 : ℕ) : Num) = (n : Num).succ := by
      rw [Nat.cast_succ, Num.add_one]
    calc
      Turing.PartrecToTM2.trNat (n + 1)
          = Turing.PartrecToTM2.trNum ((n + 1 : ℕ) : Num) := rfl
      _ = Turing.PartrecToTM2.trNum (n : Num).succ := by rw [hsucc]
      _ = succΓ'List (Turing.PartrecToTM2.trNat n) := (succΓ'List_trNum (n : Num)).symm
      _ = succΓ'List (succΓ'List^[n] []) := by rw [trNat_eq_iterate_succΓ'List n]
      _ = succΓ'List^[n + 1] [] := (Function.iterate_succ_apply' succΓ'List n []).symm

/-- Every function out of `Fin n` into a `Primcodable` type is primitive recursive. -/
theorem primrec_of_fin_dom {n : ℕ} {β : Type*} [Primcodable β] (f : Fin n → β) : Primrec f := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact (Primrec.option_get (f := fun _ : Fin 0 ↦ (none : Option β))
      (h := fun x ↦ x.elim0) (Primrec.const none)).of_eq fun x ↦ x.elim0
  · let b₀ : β := f ⟨0, hpos⟩
    refine ((Primrec.list_getD b₀).comp (Primrec.const (List.ofFn f)) Primrec.fin_val).of_eq ?_
    intro x
    simp [List.getD_eq_getElem?_getD, x.isLt]

/-- Numbering of `PartrecToTM2.Γ'` (`0 = consₗ`, `1 = cons`, `2 = bit0`, `3 = bit1`). -/
def gammaPrimeToFin4 : Turing.PartrecToTM2.Γ' ≃ Fin 4 where
  toFun
    | .consₗ => 0
    | .cons => 1
    | .bit0 => 2
    | .bit1 => 3
  invFun
    | ⟨0, _⟩ => .consₗ
    | ⟨1, _⟩ => .cons
    | ⟨2, _⟩ => .bit0
    | ⟨3, _⟩ => .bit1
  left_inv x := by cases x <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- Little-endian binary increment on `List (Fin 4)` mirroring `succΓ'List` under
`gammaPrimeToFin4`. -/
def succFin4List (l : List (Fin 4)) : List (Fin 4) :=
  List.recOn l [3] fun b tl ih ↦ if b = (3 : Fin 4) then (2 : Fin 4) :: ih else (3 : Fin 4) :: tl

@[simp]
theorem succFin4List_nil : succFin4List [] = [3] :=
  rfl

@[simp]
theorem succFin4List_cons (b : Fin 4) (tl : List (Fin 4)) :
    succFin4List (b :: tl) =
      if b = (3 : Fin 4) then (2 : Fin 4) :: succFin4List tl else (3 : Fin 4) :: tl :=
  rfl

theorem map_gammaPrimeToFin4_succΓ'List (l : List Turing.PartrecToTM2.Γ') :
    (succΓ'List l).map gammaPrimeToFin4 = succFin4List (l.map gammaPrimeToFin4) := by
  induction l with
  | nil => rfl
  | cons a tl ih =>
    cases a
    · rfl
    · rfl
    · rfl
    · change (2 : Fin 4) :: (succΓ'List tl).map gammaPrimeToFin4 =
        succFin4List ((3 : Fin 4) :: tl.map gammaPrimeToFin4)
      rw [succFin4List_cons, ih]
      rfl

theorem primrec_succFin4List : Primrec succFin4List := by
  have hb : Primrec (fun x : List (Fin 4) × Fin 4 × List (Fin 4) × List (Fin 4) ↦ x.2.1) :=
    Primrec.fst.comp Primrec.snd
  have htl : Primrec (fun x : List (Fin 4) × Fin 4 × List (Fin 4) × List (Fin 4) ↦ x.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hih : Primrec (fun x : List (Fin 4) × Fin 4 × List (Fin 4) × List (Fin 4) ↦ x.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hcond : PrimrecPred (fun x : List (Fin 4) × Fin 4 × List (Fin 4) × List (Fin 4) ↦
      x.2.1 = (3 : Fin 4)) :=
    Primrec.eq.comp hb (Primrec.const (3 : Fin 4))
  have hstep : Primrec₂ (fun (_ : List (Fin 4)) (p : Fin 4 × List (Fin 4) × List (Fin 4)) ↦
      if p.1 = (3 : Fin 4) then (2 : Fin 4) :: p.2.2 else (3 : Fin 4) :: p.2.1) :=
    (Primrec.ite hcond
      (Primrec.list_cons.comp (Primrec.const (2 : Fin 4)) hih)
      (Primrec.list_cons.comp (Primrec.const (3 : Fin 4)) htl)).to₂
  exact (Primrec.list_rec (f := id) Primrec.id (Primrec.const [(3 : Fin 4)]) hstep).of_eq
    fun _ ↦ rfl

theorem primrec_map_trNat :
    Primrec (fun n : ℕ ↦ (Turing.PartrecToTM2.trNat n).map gammaPrimeToFin4) := by
  have hiter : Primrec (fun n : ℕ ↦ succFin4List^[n] []) :=
    Primrec.nat_iterate Primrec.id (Primrec.const [])
      (primrec_succFin4List.comp Primrec.snd).to₂
  refine hiter.of_eq fun n ↦ ?_
  rw [trNat_eq_iterate_succΓ'List n]
  have hcomm : ∀ k : ℕ, (succΓ'List^[k] []).map gammaPrimeToFin4 = succFin4List^[k] [] := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        map_gammaPrimeToFin4_succΓ'List, ih]
  exact (hcomm n).symm

/-- For any finite alphabet numbering `encΓ` of `UniversalAlphabet`, the map sending a partial
recursive code `c : Nat.Partrec.Code` to its encoded input symbol list
`(universalInputList c).map encΓ` is primitive recursive (hence `Computable`). -/
theorem primrec_map_universalInputList {N : ℕ}
    (encΓ : UniversalAlphabet ≃ Fin N) :
    Primrec (fun c : Nat.Partrec.Code ↦ (universalInputList c).map encΓ) := by
  let mkSymFalse : Turing.PartrecToTM2.Γ' → UniversalAlphabet :=
    fun a ↦ (false, Function.update (fun _ ↦ none) Turing.PartrecToTM2.K'.main (some a))
  let setSymTrue : UniversalAlphabet → UniversalAlphabet :=
    fun x ↦
      let p : Bool × (Turing.PartrecToTM2.K' → Option Turing.PartrecToTM2.Γ') := x
      (true, p.2)
  let pushFalse : Fin 4 → Fin N :=
    fun i ↦ encΓ (mkSymFalse (gammaPrimeToFin4.symm i))
  let setTrue : Fin N → Fin N :=
    fun j ↦ encΓ (setSymTrue (encΓ.symm j))
  let defSym : Fin N := encΓ default
  have htrList : Primrec (fun c : Nat.Partrec.Code ↦
      (Turing.PartrecToTM2.trList [Encodable.encode c]).map gammaPrimeToFin4) := by
    have hnat := primrec_map_trNat.comp (Primrec.encode (α := Nat.Partrec.Code))
    exact (Primrec.list_concat.comp hnat (Primrec.const (1 : Fin 4))).of_eq fun c ↦ by
      simp [Turing.PartrecToTM2.trList, gammaPrimeToFin4]
  have hL' : Primrec (fun c : Nat.Partrec.Code ↦
      ((Turing.PartrecToTM2.trList [Encodable.encode c]).map gammaPrimeToFin4).reverse.map
        pushFalse) :=
    Primrec.list_map (Primrec.list_reverse.comp htrList)
      ((primrec_of_fin_dom pushFalse).comp Primrec.snd).to₂
  have hhead : Primrec (fun c : Nat.Partrec.Code ↦
      setTrue ((((Turing.PartrecToTM2.trList [Encodable.encode c]).map
        gammaPrimeToFin4).reverse.map pushFalse).getD 0 defSym)) :=
    (primrec_of_fin_dom setTrue).comp
      ((Primrec.list_getD defSym).comp hL' (Primrec.const 0))
  refine (Primrec.list_cons.comp hhead (Primrec.list_tail.comp hL')).of_eq fun c ↦ ?_
  set L := Turing.PartrecToTM2.trList [Encodable.encode c]
  have hL'_eq :
      ((L.map gammaPrimeToFin4).reverse.map pushFalse) =
        (L.reverse.map mkSymFalse).map encΓ := by
    rw [← List.map_reverse, List.map_map, List.map_map]
    refine List.map_congr_left fun a _ ↦ ?_
    simp [pushFalse]
  dsimp only [universalInputList]
  rw [hL'_eq]
  set Lraw : List UniversalAlphabet := L.reverse.map mkSymFalse
  have hhd : (Lraw.map encΓ).getD 0 defSym = encΓ Lraw.headI := by
    rcases Lraw with _ | ⟨x, xs⟩ <;> rfl
  have hset : setTrue (encΓ Lraw.headI) = encΓ (setSymTrue Lraw.headI) := by
    simp [setTrue]
  rw [hhd, hset, ← List.map_tail]
  rfl

/-- **Halting Undecidability Transfer (`TuringCompleteWitness` form)**:
Given any `W : TuringCompleteWitness φ` on a topological space `X`, there exist a **single fixed**
nonempty open target `U : Opens X`, a family of initial points `p : Nat.Partrec.Code → X`
represented in `W.chart` by disk coordinates `coord : Nat.Partrec.Code → UnitDisk2`, and a
**single `Computable` dyadic approximation procedure** `approx : Nat.Partrec.Code × ℕ →
RatFrac × RatFrac` such that:
1. `U.1.Nonempty`,
2. `p c = W.chart (coord c)` and `‖ratFracPairToEuclidean2 (approx (c, m)) - (coord c).1‖ ≤ 2⁻ᵐ`
   for all `c, m`,
3. `p c ∉ U` at `n = 0` for all `c`,
4. `(∃ n : ℕ, φ^[n] (p c) ∈ U) ↔ (c.eval 0).Dom` for all `c`,
5. forward-orbit reachability `fun c ↦ ∃ n : ℕ, φ^[n] (p c) ∈ U` is recursively enumerable
   (`REPred`) yet **algorithmically undecidable** (`¬ ComputablePred`). -/
theorem TuringCompleteWitness.undecidable_orbit_reachability {X : Type*} [TopologicalSpace X]
    {φ : X → X} (W : TuringCompleteWitness φ) :
    ∃ (U : Opens X) (p : Nat.Partrec.Code → X) (coord : Nat.Partrec.Code → UnitDisk2)
      (approx : Nat.Partrec.Code × ℕ → RatFrac × RatFrac),
      U.1.Nonempty ∧
      (∀ c : Nat.Partrec.Code, p c = W.chart (coord c)) ∧
      Computable approx ∧
      (∀ (c : Nat.Partrec.Code) (m : ℕ),
        ‖ratFracPairToEuclidean2 (approx (c, m)) - (coord c).1‖ ≤ (1 / 2 : ℝ) ^ m) ∧
      (∀ c : Nat.Partrec.Code, p c ∉ U) ∧
      (∀ c : Nat.Partrec.Code, (∃ n : ℕ, φ^[n] (p c) ∈ U) ↔ (c.eval 0).Dom) ∧
      REPred (fun c : Nat.Partrec.Code ↦ ∃ n : ℕ, φ^[n] (p c) ∈ U) ∧
      ¬ ComputablePred (fun c : Nat.Partrec.Code ↦ ∃ n : ℕ, φ^[n] (p c) ∈ U) := by
  obtain ⟨encΓ, approx₀, hcomp₀, hbound₀⟩ := W.computable_approx universalHaltingTM0
  let U : Opens X := W.encodeOpen universalHaltingTM0 0 universalTargetWindow
  let p : Nat.Partrec.Code → X :=
    fun c ↦ W.encodePoint universalHaltingTM0 (universalInputTape c)
  let coord : Nat.Partrec.Code → UnitDisk2 :=
    fun c ↦ W.coordPoint universalHaltingTM0 (universalInputTape c)
  let approx : Nat.Partrec.Code × ℕ → RatFrac × RatFrac :=
    fun cm ↦ approx₀ ([], (universalInputList cm.1).map encΓ, cm.2)
  have hiff : ∀ c : Nat.Partrec.Code, (∃ n : ℕ, φ^[n] (p c) ∈ U) ↔ (c.eval 0).Dom := by
    intro c
    exact (W.orbit_mem_encodeOpen_iff universalHaltingTM0 (universalInputTape c) 0
      universalTargetWindow).trans (haltsWithWindow_universalHaltingTM0_iff c)
  refine ⟨U, p, coord, approx, W.encodeOpen_nonempty _ _ _,
    fun c ↦ W.encodePoint_eq_chart _ _, ?_, ?_, ?_, hiff, ?_, ?_⟩
  · have hR : Computable (fun cm : Nat.Partrec.Code × ℕ ↦
        (universalInputList cm.1).map encΓ) :=
      (primrec_map_universalInputList encΓ).to_comp.comp Computable.fst
    exact hcomp₀.comp ((Computable.const []).pair (hR.pair Computable.snd))
  · intro c m
    have hmk : Turing.Tape.mk₂ ([] : List universalHaltingTM0.Γ) (universalInputList c) =
        universalInputTape c := rfl
    simpa [approx, coord, hmk] using hbound₀ [] (universalInputList c) m
  · intro c
    exact W.notMem_encodeOpen_of_step_ne_none universalHaltingTM0 (universalInputTape c) 0
      universalTargetWindow (step_initCfg_universalHaltingTM0_ne_none c)
  · exact (ComputablePred.halting_problem_re 0).of_eq fun c ↦ (hiff c).symm
  · intro hcomp
    exact ComputablePred.halting_problem 0 (hcomp.of_eq hiff)

/-- **Halting Undecidability Transfer (`IsTuringComplete` headline form)**:
For any topological space `X` and Turing complete map `φ : X → X`, forward-orbit reachability from
computably constructible points (approximable at dyadic rate `2⁻ᵐ` inside a continuous injective
disk chart) into a fixed nonempty open target `U : Opens X` is algorithmically undecidable
(`¬ ComputablePred`), and no total computable decision procedure exists. -/
theorem IsTuringComplete.undecidable_orbit_reachability {X : Type*} [TopologicalSpace X]
    {φ : X → X} (hφ : IsTuringComplete φ) :
    ∃ (U : Opens X) (chart : UnitDisk2 → X) (coord : Nat.Partrec.Code → UnitDisk2)
      (approx : Nat.Partrec.Code × ℕ → RatFrac × RatFrac),
      U.1.Nonempty ∧
      Continuous chart ∧
      Function.Injective chart ∧
      Computable approx ∧
      (∀ (c : Nat.Partrec.Code) (m : ℕ),
        ‖ratFracPairToEuclidean2 (approx (c, m)) - (coord c).1‖ ≤ (1 / 2 : ℝ) ^ m) ∧
      (∀ c : Nat.Partrec.Code, chart (coord c) ∉ U) ∧
      REPred (fun c : Nat.Partrec.Code ↦ ∃ n : ℕ, φ^[n] (chart (coord c)) ∈ U) ∧
      ¬ ComputablePred (fun c : Nat.Partrec.Code ↦ ∃ n : ℕ, φ^[n] (chart (coord c)) ∈ U) ∧
      ¬ ∃ dec : Nat.Partrec.Code → Bool,
          Computable dec ∧
          ∀ c : Nat.Partrec.Code, dec c = true ↔ ∃ n : ℕ, φ^[n] (chart (coord c)) ∈ U := by
  obtain ⟨W⟩ := hφ
  obtain ⟨U, p, coord, approx, hU, hp, hcomp, hbound, hnot0, _, hre, hnotcomp⟩ :=
    W.undecidable_orbit_reachability
  have hp_eq : p = fun c ↦ W.chart (coord c) := funext hp
  subst hp_eq
  refine ⟨U, W.chart, coord, approx, hU, W.chart_continuous, W.chart_injective, hcomp, hbound,
    hnot0, hre, hnotcomp, ?_⟩
  rintro ⟨dec, hdec_comp, hdec_iff⟩
  apply hnotcomp
  let instDec : DecidablePred (fun c : Nat.Partrec.Code ↦ ∃ n : ℕ, φ^[n] (W.chart (coord c)) ∈ U) :=
    fun c ↦ decidable_of_iff (dec c = true) (hdec_iff c)
  refine ⟨instDec, ?_⟩
  refine hdec_comp.of_eq fun c ↦ ?_
  by_cases h : dec c = true
  · have hP : ∃ n : ℕ, φ^[n] (W.chart (coord c)) ∈ U := (hdec_iff c).mp h
    simp [h, hP]
  · have hfalse : dec c = false := Bool.eq_false_iff.mpr h
    have hnP : ¬ ∃ n : ℕ, φ^[n] (W.chart (coord c)) ∈ U := fun hP ↦ h ((hdec_iff c).mpr hP)
    simp [hfalse, hnP]

end UniversalHalting

/-! ## 3. Fiber-to-4-Manifold Transfer Lemma (`TuringCompleteWitness.transfer`) -/

section FiberTransfer

/-- Iterated equivariance along a fiber over `b ∈ B₀`: if `d_bar (Ψ (b, y)) = Ψ (b, d y)` for all
`y : Y`, then `d_bar^[n] (Ψ (b, y)) = Ψ (b, d^[n] y)` for every `n : ℕ`. -/
theorem iterate_eq_on_fiber {B Y M : Type*} (Ψ : B × Y → M) {B₀ : Set B}
    {d : Y → Y} {d_bar : M → M}
    (hcomm : ∀ b ∈ B₀, ∀ y : Y, d_bar (Ψ (b, y)) = Ψ (b, d y))
    {b : B} (hb : b ∈ B₀) (y : Y) (n : ℕ) :
    d_bar^[n] (Ψ (b, y)) = Ψ (b, d^[n] y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, hcomm b hb (d^[n] y), Function.iterate_succ_apply']

/-- Lifted open target `Ψ '' (B₀ ×ˢ U.1)` in the ambient manifold `M` induced by an open embedding
`Ψ : B × Y → M` and an open base neighborhood `B₀ ⊆ B`. -/
def liftProductOpen {B Y M : Type*} [TopologicalSpace B] [TopologicalSpace Y] [TopologicalSpace M]
    {Ψ : B × Y → M} (hΨ : Topology.IsOpenEmbedding Ψ) {B₀ : Set B} (hB₀ : IsOpen B₀)
    (U : Opens Y) : Opens M :=
  ⟨Ψ '' (B₀ ×ˢ U.1), hΨ.isOpenMap _ (hB₀.prod U.2)⟩

theorem liftProductOpen_nonempty {B Y M : Type*} [TopologicalSpace B] [TopologicalSpace Y]
    [TopologicalSpace M] {Ψ : B × Y → M} (hΨ : Topology.IsOpenEmbedding Ψ) {B₀ : Set B}
    (hB₀ : IsOpen B₀) {c : B} (hc : c ∈ B₀) {U : Opens Y} (hU : U.1.Nonempty) :
    (liftProductOpen hΨ hB₀ U).1.Nonempty := by
  obtain ⟨y₀, hy₀⟩ := hU
  exact ⟨Ψ (c, y₀), (c, y₀), ⟨hc, hy₀⟩, rfl⟩

theorem mem_liftProductOpen_iff {B Y M : Type*} [TopologicalSpace B] [TopologicalSpace Y]
    [TopologicalSpace M] {Ψ : B × Y → M} (hΨ : Topology.IsOpenEmbedding Ψ) {B₀ : Set B}
    (hB₀ : IsOpen B₀) {c : B} (hc : c ∈ B₀) (U : Opens Y) (y : Y) :
    Ψ (c, y) ∈ liftProductOpen hΨ hB₀ U ↔ y ∈ U := by
  change Ψ (c, y) ∈ Ψ '' (B₀ ×ˢ U.1) ↔ y ∈ U.1
  rw [hΨ.injective.mem_set_image]
  exact ⟨fun h ↦ h.2, fun hy ↦ ⟨hc, hy⟩⟩

/-- **Fiber-to-4-Manifold Witness Transfer**:
Transfer a `TuringCompleteWitness d` on a fiber space `Y` (e.g. `UnitDisk2` or regular surface
fiber `F`) across an open product embedding `Ψ : B × Y → M` (`Topology.IsOpenEmbedding Ψ`) over an
open set `B₀` containing `c` on which `d_bar (Ψ (b, y)) = Ψ (b, d y)`.
Preserves `W.computable_approx` **verbatim** (`coordPoint := W.coordPoint`,
`chart := fun y ↦ Ψ (c, W.chart y)`). -/
def TuringCompleteWitness.transfer {B Y M : Type*} [TopologicalSpace B] [TopologicalSpace Y]
    [TopologicalSpace M] {Ψ : B × Y → M} (hΨ : Topology.IsOpenEmbedding Ψ)
    {B₀ : Set B} (hB₀ : IsOpen B₀) {c : B} (hc : c ∈ B₀)
    {d : Y → Y} {d_bar : M → M}
    (hcomm : ∀ b ∈ B₀, ∀ y : Y, d_bar (Ψ (b, y)) = Ψ (b, d y))
    (W : TuringCompleteWitness d) :
    TuringCompleteWitness d_bar where
  encodePoint M_tm t := Ψ (c, W.encodePoint M_tm t)
  encodeOpen M_tm k w := liftProductOpen hΨ hB₀ (W.encodeOpen M_tm k w)
  encodeOpen_nonempty M_tm k w :=
    liftProductOpen_nonempty hΨ hB₀ hc (W.encodeOpen_nonempty M_tm k w)
  orbit_mem_encodeOpen_iff M_tm t k w := by
    refine (exists_congr fun n ↦ ?_).trans (W.orbit_mem_encodeOpen_iff M_tm t k w)
    rw [iterate_eq_on_fiber Ψ hcomm hc (W.encodePoint M_tm t) n]
    exact mem_liftProductOpen_iff hΨ hB₀ hc (W.encodeOpen M_tm k w) _
  notMem_encodeOpen_of_step_ne_none M_tm t k w hstep := by
    rw [mem_liftProductOpen_iff hΨ hB₀ hc (W.encodeOpen M_tm k w)]
    exact W.notMem_encodeOpen_of_step_ne_none M_tm t k w hstep
  chart y := Ψ (c, W.chart y)
  chart_continuous := hΨ.continuous.comp (continuous_const.prodMk W.chart_continuous)
  chart_injective y₁ y₂ h := W.chart_injective (Prod.mk.inj (hΨ.injective h)).2
  coordPoint := W.coordPoint
  encodePoint_eq_chart M_tm t := congrArg (fun z ↦ Ψ (c, z)) (W.encodePoint_eq_chart M_tm t)
  computable_approx := W.computable_approx

/-- **Fiber-to-4-Manifold `IsTuringComplete` Transfer Lemma**:
If `Ψ : B × Y → M` is an open embedding, `c ∈ B₀` with `IsOpen B₀`, and
`∀ b ∈ B₀, ∀ y : Y, d_bar (Ψ (b, y)) = Ψ (b, d y)`, then
`IsTuringComplete d → IsTuringComplete d_bar`. -/
theorem IsTuringComplete.transfer {B Y M : Type*} [TopologicalSpace B] [TopologicalSpace Y]
    [TopologicalSpace M] {Ψ : B × Y → M} (hΨ : Topology.IsOpenEmbedding Ψ)
    {B₀ : Set B} (hB₀ : IsOpen B₀) {c : B} (hc : c ∈ B₀)
    {d : Y → Y} {d_bar : M → M}
    (hcomm : ∀ b ∈ B₀, ∀ y : Y, d_bar (Ψ (b, y)) = Ψ (b, d y))
    (hd : IsTuringComplete d) :
    IsTuringComplete d_bar := by
  obtain ⟨W⟩ := hd
  exact ⟨W.transfer hΨ hB₀ hc hcomm⟩

/-- Specialization of `IsTuringComplete.transfer` to an open subset `B : Set Base` of an ambient
base manifold `Base` (such as `B ⊂ S²`), an open subdisk `B₀ ⊆ B` (`IsOpen B₀`, `c ∈ B₀`), and the
open unit disk fiber `UnitDisk2`. -/
theorem IsTuringComplete.transfer_unitDisk2_of_subset {Base M : Type*} [TopologicalSpace Base]
    [TopologicalSpace M] {B B₀ : Set Base} (hB₀_sub : B₀ ⊆ B) (hB₀ : IsOpen B₀)
    {c : Base} (hc : c ∈ B₀) {Ψ : B × UnitDisk2 → M} (hΨ : Topology.IsOpenEmbedding Ψ)
    {d : UnitDisk2 → UnitDisk2} {d_bar : M → M}
    (hcomm : ∀ (b : B), b.1 ∈ B₀ → ∀ y : UnitDisk2, d_bar (Ψ (b, y)) = Ψ (b, d y))
    (hd : IsTuringComplete d) :
    IsTuringComplete d_bar := by
  let B₀' : Set B := Subtype.val ⁻¹' B₀
  have hB₀'_open : IsOpen B₀' := hB₀.preimage continuous_subtype_val
  have hc' : (⟨c, hB₀_sub hc⟩ : B) ∈ B₀' := hc
  exact hd.transfer hΨ hB₀'_open hc' (fun b hb y ↦ hcomm b hb y)

/-- Direct single-fiber open-embedding transfer (e.g. lifting `d : UnitDisk2 → UnitDisk2` along a
Darboux or stereographic disk open embedding `ι : UnitDisk2 → F` into a closed surface fiber `F`
where `d_F (ι y) = ι (d y)`). -/
def TuringCompleteWitness.ofOpenEmbedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : X → Y} (hι : Topology.IsOpenEmbedding ι) {φ : X → X} {ψ : Y → Y}
    (hcomm : ∀ x : X, ψ (ι x) = ι (φ x)) (W : TuringCompleteWitness φ) :
    TuringCompleteWitness ψ where
  encodePoint M_tm t := ι (W.encodePoint M_tm t)
  encodeOpen M_tm k w := ⟨ι '' (W.encodeOpen M_tm k w).1, hι.isOpenMap _ (W.encodeOpen M_tm k w).2⟩
  encodeOpen_nonempty M_tm k w := (W.encodeOpen_nonempty M_tm k w).image ι
  orbit_mem_encodeOpen_iff M_tm t k w := by
    have hiter : ∀ (x : X) (n : ℕ), ψ^[n] (ι x) = ι (φ^[n] x) := by
      intro x n
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply', ih, hcomm, Function.iterate_succ_apply']
    refine (exists_congr fun n ↦ ?_).trans (W.orbit_mem_encodeOpen_iff M_tm t k w)
    change ψ^[n] (ι (W.encodePoint M_tm t)) ∈ ι '' (W.encodeOpen M_tm k w).1 ↔ _
    rw [hiter, hι.injective.mem_set_image]
    rfl
  notMem_encodeOpen_of_step_ne_none M_tm t k w hstep := by
    change ι (W.encodePoint M_tm t) ∉ ι '' (W.encodeOpen M_tm k w).1
    rw [hι.injective.mem_set_image]
    exact W.notMem_encodeOpen_of_step_ne_none M_tm t k w hstep
  chart y := ι (W.chart y)
  chart_continuous := hι.continuous.comp W.chart_continuous
  chart_injective := hι.injective.comp W.chart_injective
  coordPoint := W.coordPoint
  encodePoint_eq_chart M_tm t := congrArg ι (W.encodePoint_eq_chart M_tm t)
  computable_approx := W.computable_approx

theorem IsTuringComplete.of_openEmbedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : X → Y} (hι : Topology.IsOpenEmbedding ι) {φ : X → X} {ψ : Y → Y}
    (hcomm : ∀ x : X, ψ (ι x) = ι (φ x)) (hφ : IsTuringComplete φ) :
    IsTuringComplete ψ := by
  obtain ⟨W⟩ := hφ
  exact ⟨W.ofOpenEmbedding hι hcomm⟩

end FiberTransfer

end S4TuringPoisson
