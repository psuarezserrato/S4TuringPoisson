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

public import TuringRecursive
public import S4TuringPoisson.Interfaces

/-!
# Exact-Output Windowed Universal `FinTM0` Machine (CMPP Milestone B2)

This module implements Milestone B2 (`S4TuringPoisson/Dynamics/Reversible/Universal.lean`) of the
`CMPP21` reversible-computation pipeline (`MISSION_DIRECTIVE_CMPP.md` §4.4, §7, §8), packaging the
exact-output windowed universal `TM0` machine `TuringRecursive.U` (`T-E(3)`) as a `FinTM0` and
establishing the **unconditional** universal simulation theorem for arbitrary `FinTM0` machines
(with **no** fixed-machine fallback, per Decision D2):

1. **Universal `FinTM0` Packaging (`universalFinTM0`)**:
   - Bundles `TuringRecursive.U : TM0.Machine Γ₀ UniversalΛ` over the fixed 1250-symbol alphabet
     `Γ₀` and finite state space `UniversalΛ` into `universalFinTM0 : FinTM0`, keeping `Fintype Γ₀`
     local to avoid typeclass diamonds with `UndecidabilityAndTransfer.lean`.

2. **Pointed `ℕ`-Relabeling & Primitive Recursive Input Encoding**:
   - `relabelSym`, `relabelState`, `relabelCode`: injective pointed relabelings `M.Γ → ℕ`,
     `M.Λ → ℕ` and tabular code `TM0Code` extracted from `TM0Code.exists_relabeling M.machine`,
     commuting with `StateTransition.eval` (`relabel_evalCfg`).
   - `encodeInputList` and `encodeInputTape`: canonical `Γ₀`-list and `Tape Γ₀` input encodings
     `encUniv (relabelCode M, (M.initCfg t).map (relabelSym M) (relabelState M))`, proved primitive
     recursive on two-sided list representations `Tape.mk₂` (`primrec_encodeInputList`).

3. **Non-Vacuous `AcceptingOutputCodes`, Prefix-Free Cylinder Isolation & Universal Simulation**:
   - `AcceptingOutputCodes M k w`: set of relabeled `TM0.Cfg ℕ ℕ` configurations whose preimage
     tape agrees with `w : Window M k` on `[-k, k]`, proved **unconditionally nonempty** for every
     `(M, k, w)` including non-halting machines (`acceptingOutputCodes_nonempty`).
   - `eq_of_tape_mk₁_encNat_agree`: prefix-free cylinder isolation proving from
     `default_notMem_encNat` and `decNat_encNat` that agreement of `Tape.mk₁ (encNat n₂)` and
     `Tape.mk₁ (encNat n₁)` on `0 .. (encNat n₁).length` forces `n₂ = n₁` (ruling out prefix
     collisions such as `encNat 1 <+: encNat 2`).
   - `universalFinTM0_halt_tape_eq_encNat`, `universalFinTM0_halts_with_code_iff`, and
     `universalFinTM0_halts_with_cylinder_iff` (**UNCONDITIONAL**): exact equivalence between
     halting of `universalFinTM0` on `encodeInputTape M t` with an `AcceptingOutputCodes M k w`
     output tape (or cylinder prefix of radius `(encNat (Encodable.encode c_nat)).length`) and
     `HaltsWithWindow M t k w`.

4. **Gate G5 Concrete Anti-Vacuity Witnesses**:
   - Concrete halting witness `univToyHalt` (accepting its true window and rejecting a wrong
     window), concrete non-halting witness `univToyLoop` (nonempty `AcceptingOutputCodes` while
     `universalFinTM0` never halts), and explicit prefix/boundary separation between `encNat 1` and
     `encNat 2`.
-/

@[expose] public section

open Turing TuringRecursive
open scoped TuringRecursive

namespace S4TuringPoisson.Reversible

/-! ## 1. Universal `FinTM0` Packaging (`universalFinTM0`) -/

/-- The fixed-alphabet universal Post–Turing machine `TuringRecursive.U` (`T-E(3)`) packaged as a
`FinTM0` over tape alphabet `Γ₀` (`1250` symbols) and finite state space `UniversalΛ`. -/
noncomputable def universalFinTM0 : FinTM0 :=
  letI : Fintype Γ₀ := Fintype.ofEquiv _ TuringRecursive.gamma0Equiv.symm
  { Γ := Γ₀, Λ := UniversalΛ, machine := U }

/-- Tape alphabet of `universalFinTM0` is `TuringRecursive.Γ₀`. -/
-- tier: T0
@[simp]
theorem universalFinTM0_Γ : universalFinTM0.Γ = Γ₀ :=
  rfl

/-- State space of `universalFinTM0` is `TuringRecursive.UniversalΛ`. -/
-- tier: T0
@[simp]
theorem universalFinTM0_Λ : universalFinTM0.Λ = UniversalΛ := by
  unfold universalFinTM0
  simp

/-- Transition table of `universalFinTM0` is `TuringRecursive.U`. -/
-- tier: T0
@[simp]
theorem universalFinTM0_machine : universalFinTM0.machine = U := by
  unfold universalFinTM0
  simp

/-- Initializing `universalFinTM0` on `Tape.mk₁ l` coincides with `TM0.init l`. -/
-- tier: T0
@[simp]
theorem universalFinTM0_initCfg_mk₁ (l : List Γ₀) :
    universalFinTM0.initCfg (Tape.mk₁ l) = TM0.init l :=
  rfl

/-! ## 2. Arbitrary `FinTM0` Relabeling & Primitive Recursive Input Encoding -/

/-- Injective pointed symbol relabeling `M.Γ → ℕ` (`default ↦ 0`) selected from
`TuringRecursive.TM0Code.exists_relabeling M.machine`. -/
noncomputable def relabelSym (M : FinTM0) : PointedMap M.Γ ℕ :=
  (TM0Code.exists_relabeling M.machine).choose

/-- Injective pointed state relabeling `M.Λ → ℕ` (`default ↦ 0`) selected from
`TuringRecursive.TM0Code.exists_relabeling M.machine`. -/
noncomputable def relabelState (M : FinTM0) : PointedMap M.Λ ℕ :=
  (TM0Code.exists_relabeling M.machine).choose_spec.choose

/-- Concrete tabular `TM0Code` over `ℕ` simulating `M.machine` along `relabelSym M` and
`relabelState M`. -/
noncomputable def relabelCode (M : FinTM0) : TM0Code :=
  (TM0Code.exists_relabeling M.machine).choose_spec.choose_spec.choose

/-- `relabelSym M` maps the blank tape symbol `default : M.Γ` to `0 : ℕ`. -/
-- tier: T0
theorem relabelSym_default (M : FinTM0) : relabelSym M default = 0 :=
  PointedMap.map_pt (relabelSym M)

/-- `relabelState M` maps the initial state `default : M.Λ` to `0 : ℕ`. -/
-- tier: T0
theorem relabelState_default (M : FinTM0) : relabelState M default = 0 :=
  PointedMap.map_pt (relabelState M)

/-- The pointed symbol relabeling `relabelSym M` is injective. -/
-- tier: T1
theorem relabelSym_injective (M : FinTM0) : Function.Injective (relabelSym M) :=
  (TM0Code.exists_relabeling M.machine).choose_spec.choose_spec.choose_spec.1

/-- The pointed state relabeling `relabelState M` is injective. -/
-- tier: T1
theorem relabelState_injective (M : FinTM0) : Function.Injective (relabelState M) :=
  (TM0Code.exists_relabeling M.machine).choose_spec.choose_spec.choose_spec.2.1

/-- Run-to-completion evaluation of `(relabelCode M).machine` on any relabeled configuration
`c.map (relabelSym M) (relabelState M)` commutes with `StateTransition.eval` of `M.machine`. -/
-- tier: T1
theorem relabel_evalCfg (M : FinTM0) (c : TM0.Cfg M.Γ M.Λ) :
    StateTransition.eval (TM0.step (relabelCode M).machine)
        (c.map (relabelSym M) (relabelState M)) =
      (StateTransition.eval (TM0.step M.machine) c).map
        (TM0.Cfg.map (relabelSym M) (relabelState M)) :=
  (TM0Code.exists_relabeling M.machine).choose_spec.choose_spec.choose_spec.2.2.1 c

/-- Encoded input `List Γ₀` feeding `(relabelCode M, (M.initCfg t).map ...)` into
`universalFinTM0`. -/
noncomputable def encodeInputList (M : FinTM0) (t : FinSupportedTape M) : List Γ₀ :=
  encUniv (relabelCode M, (M.initCfg t).map (relabelSym M) (relabelState M))

/-- Encoded initial `FinSupportedTape universalFinTM0` (`Tape.mk₁ (encodeInputList M t)`) for
`(M, t)`. -/
noncomputable def encodeInputTape (M : FinTM0) (t : FinSupportedTape M) :
    FinSupportedTape universalFinTM0 :=
  Tape.mk₁ (encodeInputList M t)

/-- Unfolding identity for `encodeInputList M t`. -/
-- tier: T0
theorem encodeInputList_apply (M : FinTM0) (t : FinSupportedTape M) :
    encodeInputList M t =
      encUniv (relabelCode M, (M.initCfg t).map (relabelSym M) (relabelState M)) := by
  unfold encodeInputList
  rfl

/-- Unfolding identity for `encodeInputTape M t`. -/
-- tier: T0
theorem encodeInputTape_apply (M : FinTM0) (t : FinSupportedTape M) :
    encodeInputTape M t = Tape.mk₁ (encodeInputList M t) := by
  unfold encodeInputTape
  rfl

/-- Mapping a two-sided tape `Tape.mk₂ L R` by a `PointedMap` maps both `L` and `R`wise. -/
-- tier: T0
@[simp]
theorem tape_mk₂_map {Γ Γ' : Type*} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
    (L R : List Γ) :
    (Tape.mk₂ L R).map f = Tape.mk₂ (L.map f) (R.map f) :=
  Tape.map_mk₂ f L R

/-- For any fixed `M : FinTM0` and alphabet numbering `encΓ : M.Γ ≃ Fin n`, mapping a pair of
`Fin n`-encoded half-tape lists `(L, R)` to `encodeInputList M (Tape.mk₂ ...)` is primitive
recursive. -/
-- tier: T2
theorem primrec_encodeInputList_of_equiv {n : ℕ} (M : FinTM0) (encΓ : M.Γ ≃ Fin n) :
    Primrec fun p : List (Fin n) × List (Fin n) ↦
      encodeInputList M (Tape.mk₂ (p.1.map encΓ.symm) (p.2.map encΓ.symm)) := by
  let φ : Fin n → ℕ := fun i ↦ relabelSym M (encΓ.symm i)
  have hφ : Primrec φ := Primrec.dom_finite φ
  have hL : Primrec fun p : List (Fin n) × List (Fin n) ↦ p.1.map φ :=
    Primrec.list_map Primrec.fst (hφ.comp Primrec.snd).to₂
  have hR : Primrec fun p : List (Fin n) × List (Fin n) ↦ p.2.map φ :=
    Primrec.list_map Primrec.snd (hφ.comp Primrec.snd).to₂
  have hTape : Primrec fun p : List (Fin n) × List (Fin n) ↦
      Tape.mk₂ (p.1.map φ) (p.2.map φ) :=
    Primrec.tape_mk₂.comp hL hR
  have hCfg : Primrec fun p : List (Fin n) × List (Fin n) ↦
      (⟨relabelState M default, Tape.mk₂ (p.1.map φ) (p.2.map φ)⟩ : TM0.Cfg ℕ ℕ) :=
    Primrec.cfg_mk (.const (relabelState M default)) hTape
  have hMain : Primrec fun p : List (Fin n) × List (Fin n) ↦
      encUniv (relabelCode M, ⟨relabelState M default, Tape.mk₂ (p.1.map φ) (p.2.map φ)⟩) :=
    primrec_encUniv.comp ((Primrec.const (relabelCode M)).pair hCfg)
  refine hMain.of_eq fun p ↦ ?_
  unfold encodeInputList FinTM0.initCfg TM0.Cfg.map
  dsimp only
  rw [Tape.map_mk₂, List.map_map, List.map_map]
  rfl

/-- For every `M : FinTM0`, with `encΓ := Fintype.equivFin M.Γ`, the input-list encoder
`(L, R) ↦ encodeInputList M (Tape.mk₂ (L.map encΓ.symm) (R.map encΓ.symm))` is primitive
recursive. -/
-- tier: T1
theorem primrec_encodeInputList (M : FinTM0) :
    let encΓ := Fintype.equivFin M.Γ
    Primrec fun p : List (Fin (Fintype.card M.Γ)) × List (Fin (Fintype.card M.Γ)) ↦
      encodeInputList M (Tape.mk₂ (p.1.map encΓ.symm) (p.2.map encΓ.symm)) :=
  primrec_encodeInputList_of_equiv M (Fintype.equivFin M.Γ)

/-! ## 3. Nonempty `AcceptingOutputCodes`, Prefix-Free Isolation & Simulation Equivalence -/

/-- Set of `ℕ`-relabeled configurations `c_nat : TM0.Cfg ℕ ℕ` arising from an `M`-configuration `c`
whose tape agrees with `w : Window M k` on `[-k, k]`.

Omits `TM0.step M.machine c = none` by design so `AcceptingOutputCodes M k w` is unconditionally
nonempty even when `M` has no halting states (`M_loop`), while simulation soundness recovers
`TM0.step M.machine c = none` from the halting output of `universalFinTM0`. -/
def AcceptingOutputCodes (M : FinTM0) (k : ℕ) (w : Window M k) : Set (TM0.Cfg ℕ ℕ) :=
  { c_nat | ∃ c : TM0.Cfg M.Γ M.Λ,
    c_nat = c.map (relabelSym M) (relabelState M) ∧
    ∀ i : Set.Icc (-(k : ℤ)) (k : ℤ), c.Tape.nth i.1 = w i }

/-- `AcceptingOutputCodes M k w` is unconditionally nonempty for every `(M, k, w)`. -/
-- tier: T1
theorem acceptingOutputCodes_nonempty (M : FinTM0) (k : ℕ) (w : Window M k) :
    (AcceptingOutputCodes M k w).Nonempty := by
  let L : List M.Γ := List.ofFn fun j : Fin k ↦
    w ⟨-((j.1 : ℤ) + 1), by
      refine ⟨?_, ?_⟩ <;> omega⟩
  let R : List M.Γ := List.ofFn fun j : Fin (k + 1) ↦
    w ⟨(j.1 : ℤ), by
      refine ⟨?_, ?_⟩ <;> omega⟩
  let c : TM0.Cfg M.Γ M.Λ := ⟨default, Tape.mk₂ L R⟩
  refine ⟨c.map (relabelSym M) (relabelState M), c, rfl, ?_⟩
  rintro ⟨i, hi₁, hi₂⟩
  rcases i with n | n
  · have hn : n < k + 1 := by
      change (n : ℤ) ≤ (k : ℤ) at hi₂
      omega
    have hRlen : n < R.length := by
      simpa [R] using hn
    change (Tape.mk' (ListBlank.mk L) (ListBlank.mk R)).nth (n : ℤ) = w ⟨(n : ℤ), hi₁, hi₂⟩
    rw [Tape.mk'_nth_nat, ListBlank.nth_mk, List.getI_eq_getElem R hRlen]
    simp only [R, List.getElem_ofFn]
  · have hn : n < k := by
      change -(k : ℤ) ≤ Int.negSucc n at hi₁
      omega
    have hLlen : n < L.length := by
      simpa [L] using hn
    have hnth : (Tape.mk₂ L R).nth (Int.negSucc n) = L.getI n := rfl
    rw [hnth, List.getI_eq_getElem L hLlen]
    simp only [L, List.getElem_ofFn]
    congr 1

/-- `ListBlank.map f` is injective whenever the underlying `PointedMap` `f` is injective. -/
-- tier: T1
theorem listBlank_map_injective {Γ Γ' : Type*} [Inhabited Γ] [Inhabited Γ']
    {f : PointedMap Γ Γ'} (hf : Function.Injective f) :
    Function.Injective (ListBlank.map f) := by
  intro L₁ L₂ h
  refine ListBlank.ext fun n ↦ hf ?_
  rw [← ListBlank.nth_map, h, ListBlank.nth_map]

/-- `Tape.map f` is injective whenever the underlying `PointedMap` `f` is injective. -/
-- tier: T1
theorem tape_map_injective {Γ Γ' : Type*} [Inhabited Γ] [Inhabited Γ']
    {f : PointedMap Γ Γ'} (hf : Function.Injective f) :
    Function.Injective (Tape.map f) := by
  rintro ⟨h₁, l₁, r₁⟩ ⟨h₂, l₂, r₂⟩ h
  dsimp only [Tape.map] at h
  injection h with hh hl hr
  rw [hf hh, listBlank_map_injective hf hl, listBlank_map_injective hf hr]

/-- `TM0.Cfg.map f g` is injective whenever both `f` and `g` are injective. -/
-- tier: T1
theorem cfg_map_injective {Γ Γ' Λ Λ' : Type*} [Inhabited Γ] [Inhabited Γ']
    {f : PointedMap Γ Γ'} {g : Λ → Λ'}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (TM0.Cfg.map f g) := by
  rintro ⟨q₁, t₁⟩ ⟨q₂, t₂⟩ h
  injection h with hq ht
  rw [hg hq, tape_map_injective hf ht]

/-- Reading non-negative offset `(i : ℤ)` of `Tape.mk₁ l` returns `l.getI i`. -/
-- tier: T0
@[simp]
theorem tape_mk₁_nth_nat {Γ : Type*} [Inhabited Γ] (l : List Γ) (i : ℕ) :
    (Tape.mk₁ l).nth (i : ℤ) = l.getI i := by
  simp [Tape.mk₁, Tape.mk₂, Tape.mk'_nth_nat, ListBlank.nth_mk]

/-- **Prefix-Free Cylinder Isolation for `encNat`**: if `Tape.mk₁ (encNat n₂)` agrees with
`Tape.mk₁ (encNat n₁)` at every cell `0 ≤ i ≤ (encNat n₁).length` (including the trailing blank at
index `(encNat n₁).length`), then `n₂ = n₁`. -/
-- tier: T2
theorem eq_of_tape_mk₁_encNat_agree {n₁ n₂ : ℕ}
    (h : ∀ i : ℕ, i ≤ (encNat n₁).length →
      (Tape.mk₁ (encNat n₂)).nth (i : ℤ) = (Tape.mk₁ (encNat n₁)).nth (i : ℤ)) :
    n₂ = n₁ := by
  have hgetI : ∀ i : ℕ, i ≤ (encNat n₁).length →
      (encNat n₂).getI i = (encNat n₁).getI i := fun i hi ↦ by
    simpa only [Tape.mk₁, Tape.mk₂, Tape.mk'_nth_nat, ListBlank.nth_mk] using h i hi
  have hlen : (encNat n₂).length = (encNat n₁).length := by
    rcases Nat.lt_trichotomy (encNat n₂).length (encNat n₁).length with hlt | heq | hgt
    · exfalso
      have h1 : (encNat n₂).getI (encNat n₂).length =
          (encNat n₁).getI (encNat n₂).length :=
        hgetI (encNat n₂).length (Nat.le_of_lt hlt)
      rw [List.getI_eq_default _ le_rfl, List.getI_eq_getElem _ hlt] at h1
      exact default_notMem_encNat n₁ (h1 ▸ List.getElem_mem hlt)
    · exact heq
    · exfalso
      have h1 : (encNat n₂).getI (encNat n₁).length =
          (encNat n₁).getI (encNat n₁).length :=
        hgetI (encNat n₁).length le_rfl
      rw [List.getI_eq_getElem _ hgt, List.getI_eq_default _ le_rfl] at h1
      exact default_notMem_encNat n₂ (h1 ▸ List.getElem_mem hgt)
  have hlist : encNat n₂ = encNat n₁ := by
    refine List.ext_getElem hlen fun i hi₂ hi₁ ↦ ?_
    have h1 := hgetI i (Nat.le_of_lt hi₁)
    rwa [List.getI_eq_getElem _ hi₂, List.getI_eq_getElem _ hi₁] at h1
  calc
    n₂ = decNat (ListBlank.mk (encNat n₂)) := (decNat_encNat n₂).symm
    _ = decNat (ListBlank.mk (encNat n₁)) := by rw [hlist]
    _ = n₁ := decNat_encNat n₁

/-- Exact halting-tape bridge for `universalFinTM0`: whenever `universalFinTM0` reaches a terminal
configuration `u'` from `encodeInputTape M t`, its halting tape is
`Tape.mk₁ (encNat (Encodable.encode c_nat))` for the terminal relabeled configuration `c_nat` of
`(relabelCode M).machine`. -/
-- tier: T2
theorem universalFinTM0_halt_tape_eq_encNat (M : FinTM0) (t : FinSupportedTape M)
    {u' : TM0.Cfg Γ₀ UniversalΛ}
    (hreach : TM0.Reaches universalFinTM0.machine
      (universalFinTM0.initCfg (encodeInputTape M t)) u')
    (hterm : TM0.step universalFinTM0.machine u' = none) :
    ∃ c_nat ∈ StateTransition.eval (TM0.step (relabelCode M).machine)
        ((M.initCfg t).map (relabelSym M) (relabelState M)),
      u'.Tape = Tape.mk₁ (encNat (Encodable.encode c_nat)) := by
  have hu' : u' ∈ StateTransition.eval (TM0.step U)
      (TM0.init (encUniv (relabelCode M, (M.initCfg t).map (relabelSym M) (relabelState M)))) :=
    StateTransition.mem_eval.mpr ⟨hreach, hterm⟩
  have hmem : u'.Tape ∈
      (StateTransition.eval (TM0.step U)
        (TM0.init
          (encUniv (relabelCode M, (M.initCfg t).map (relabelSym M) (relabelState M))))).map
        TM0.Cfg.Tape :=
    (Part.mem_map_iff _).mpr ⟨u', hu', rfl⟩
  rw [U_evalCfg_tape] at hmem
  obtain ⟨c_nat, hc_nat, hTape⟩ := (Part.mem_map_iff _).mp hmem
  exact ⟨c_nat, hc_nat, hTape.symm⟩

/-- **Unconditional Universal `FinTM0` Simulation Theorem (`UNCONDITIONAL`, Milestone B2)**:
For every finite Post–Turing machine `M : FinTM0`, input tape `t : FinSupportedTape M`, radius
`k : ℕ`, and target window `w : Window M k`, `universalFinTM0` started on `encodeInputTape M t`
halts with output tape `Tape.mk₁ (encNat (Encodable.encode c_nat))` for some
`c_nat ∈ AcceptingOutputCodes M k w` if and only if `HaltsWithWindow M t k w`. -/
-- tier: T2
theorem universalFinTM0_halts_with_code_iff (M : FinTM0) (t : FinSupportedTape M)
    (k : ℕ) (w : Window M k) :
    (∃ u' : TM0.Cfg Γ₀ UniversalΛ,
      TM0.Reaches universalFinTM0.machine (universalFinTM0.initCfg (encodeInputTape M t)) u' ∧
      TM0.step universalFinTM0.machine u' = none ∧
      ∃ c_nat ∈ AcceptingOutputCodes M k w,
        u'.Tape = Tape.mk₁ (encNat (Encodable.encode c_nat))) ↔
    HaltsWithWindow M t k w := by
  constructor
  · rintro ⟨u', hreach, hterm, c_nat, ⟨c, hc_eq, hwin⟩, hTape⟩
    obtain ⟨d_nat, hd_eval, hd_Tape⟩ := universalFinTM0_halt_tape_eq_encNat M t hreach hterm
    have henc_eq : Encodable.encode d_nat = Encodable.encode c_nat :=
      eq_of_tape_mk₁_encNat_agree fun i _ ↦ by rw [← hd_Tape, hTape]
    have hdc : d_nat = c_nat := Encodable.encode_injective henc_eq
    rw [hdc, relabel_evalCfg M (M.initCfg t)] at hd_eval
    obtain ⟨c', hc'_eval, hc'_map⟩ := (Part.mem_map_iff _).mp hd_eval
    have hcc' : c' = c :=
      cfg_map_injective (relabelSym_injective M) (relabelState_injective M)
        (hc'_map.trans hc_eq)
    obtain ⟨hreachM, htermM⟩ := StateTransition.mem_eval.mp hc'_eval
    subst hcc'
    exact ⟨c', hreachM, htermM, hwin⟩
  · rintro ⟨c, hreachM, htermM, hwin⟩
    have hc_eval : c ∈ StateTransition.eval (TM0.step M.machine) (M.initCfg t) :=
      StateTransition.mem_eval.mpr ⟨hreachM, htermM⟩
    let c_nat : TM0.Cfg ℕ ℕ := c.map (relabelSym M) (relabelState M)
    have hnat_eval : c_nat ∈ StateTransition.eval (TM0.step (relabelCode M).machine)
        ((M.initCfg t).map (relabelSym M) (relabelState M)) := by
      rw [relabel_evalCfg M (M.initCfg t)]
      exact (Part.mem_map_iff _).mpr ⟨c, hc_eval, rfl⟩
    obtain ⟨u', hu'_eval, hu'_Tape⟩ :=
      (U_mem_evalCfg_iff (relabelCode M)
        ((M.initCfg t).map (relabelSym M) (relabelState M)) c_nat).mp hnat_eval
    obtain ⟨hreachU, htermU⟩ := StateTransition.mem_eval.mp hu'_eval
    exact ⟨u', hreachU, htermU, c_nat, ⟨c, rfl, hwin⟩, hu'_Tape⟩

/-- Cylinder-window corollary of `universalFinTM0_halts_with_code_iff` (`UNCONDITIONAL`, consumed by
Milestone B3): matching `u'.Tape` on the prefix `0 .. (encNat (Encodable.encode c_nat)).length`
for some `c_nat ∈ AcceptingOutputCodes M k w` is equivalent to `HaltsWithWindow M t k w`. -/
-- tier: T2
theorem universalFinTM0_halts_with_cylinder_iff (M : FinTM0) (t : FinSupportedTape M)
    (k : ℕ) (w : Window M k) :
    (∃ u' : TM0.Cfg Γ₀ UniversalΛ,
      TM0.Reaches universalFinTM0.machine (universalFinTM0.initCfg (encodeInputTape M t)) u' ∧
      TM0.step universalFinTM0.machine u' = none ∧
      ∃ c_nat ∈ AcceptingOutputCodes M k w,
        ∀ i : ℕ, i ≤ (encNat (Encodable.encode c_nat)).length →
          u'.Tape.nth (i : ℤ) =
            (Tape.mk₁ (encNat (Encodable.encode c_nat))).nth (i : ℤ)) ↔
    HaltsWithWindow M t k w := by
  rw [← universalFinTM0_halts_with_code_iff]
  constructor
  · rintro ⟨u', hreach, hterm, c_nat, hc_acc, hcyl⟩
    obtain ⟨d_nat, _, hd_Tape⟩ := universalFinTM0_halt_tape_eq_encNat M t hreach hterm
    have henc_eq : Encodable.encode d_nat = Encodable.encode c_nat :=
      eq_of_tape_mk₁_encNat_agree fun i hi ↦ by
        rw [← hd_Tape]
        exact hcyl i hi
    have hdc : d_nat = c_nat := Encodable.encode_injective henc_eq
    subst hdc
    exact ⟨u', hreach, hterm, d_nat, hc_acc, hd_Tape⟩
  · rintro ⟨u', hreach, hterm, c_nat, hc_acc, hTape⟩
    exact ⟨u', hreach, hterm, c_nat, hc_acc, fun i _ ↦ by rw [hTape]⟩

/-! ## 4. Gate G5 Concrete Anti-Vacuity Witnesses -/

/-- Concrete 2-state halting `FinTM0` writing `true` at cell `0` and halting in state `true`. -/
def univToyHalt : FinTM0 where
  Γ := Bool
  Λ := Bool
  machine q _ :=
    match q with
    | false => some (true, TM0.Stmt.write true)
    | true => none

/-- True radius-`1` halting window `[false, true, false]` of `univToyHalt` on `default`. -/
def univToyHaltWindow : Window univToyHalt 1 :=
  fun i ↦ decide (i.1 = 0)

/-- Wrong radius-`1` window `[true, true, true]` rejected by `univToyHalt` on `default`. -/
def univToyWrongWindow : Window univToyHalt 1 :=
  fun _ ↦ true

/-- `univToyHalt` halts in `1` step on `default` with output window `univToyHaltWindow`. -/
-- tier: T1
theorem univToyHalt_haltsWithWindow :
    HaltsWithWindow univToyHalt default 1 univToyHaltWindow := by
  rw [haltsWithWindow_iff_exists_steps]
  refine ⟨1, { q := true, Tape := (default : Tape Bool).write true }, rfl, rfl, ?_⟩
  rintro ⟨i, hi₁, hi₂⟩
  have hcases : i = -1 ∨ i = 0 ∨ i = 1 := by
    change -1 ≤ i at hi₁
    change i ≤ 1 at hi₂
    omega
  rcases hcases with rfl | rfl | rfl <;> rfl

/-- `univToyHalt` on `default` does **not** halt with `univToyWrongWindow`. -/
-- tier: T1
theorem univToyHalt_not_haltsWithWrongWindow :
    ¬ HaltsWithWindow univToyHalt default 1 univToyWrongWindow := by
  rw [haltsWithWindow_iff_exists_steps]
  rintro ⟨n, c, hn, hterm, hwin⟩
  rcases n with _ | _ | n
  · injection hn with hc
    subst hc
    cases hterm
  · change TM0.step univToyHalt.machine (univToyHalt.initCfg default) = some c at hn
    injection hn with hc
    subst hc
    have h1 := hwin ⟨1, by omega, by omega⟩
    exact Bool.false_ne_true h1
  · rw [Function.iterate_succ_apply, Function.iterate_succ_apply] at hn
    change univToyHalt.stepOpt^[n]
      (univToyHalt.stepOpt (TM0.step univToyHalt.machine (univToyHalt.initCfg default))) =
      some c at hn
    have hstep1 :
        univToyHalt.stepOpt (TM0.step univToyHalt.machine (univToyHalt.initCfg default)) =
          none := rfl
    rw [hstep1, univToyHalt.iterate_stepOpt_none] at hn
    cases hn

/-- **Gate G5 Halting & Wrong-Window Rejection Witness (`UNCONDITIONAL`)**:
`universalFinTM0` on `encodeInputTape univToyHalt default` halts in `AcceptingOutputCodes` for
`univToyHaltWindow` and rejects `univToyWrongWindow`. -/
-- tier: T2
theorem univToyHalt_universal_simulation :
    (∃ u' : TM0.Cfg Γ₀ UniversalΛ,
      TM0.Reaches universalFinTM0.machine
        (universalFinTM0.initCfg (encodeInputTape univToyHalt default)) u' ∧
      TM0.step universalFinTM0.machine u' = none ∧
      ∃ c_nat ∈ AcceptingOutputCodes univToyHalt 1 univToyHaltWindow,
        u'.Tape = Tape.mk₁ (encNat (Encodable.encode c_nat))) ∧
    ¬ (∃ u' : TM0.Cfg Γ₀ UniversalΛ,
      TM0.Reaches universalFinTM0.machine
        (universalFinTM0.initCfg (encodeInputTape univToyHalt default)) u' ∧
      TM0.step universalFinTM0.machine u' = none ∧
      ∃ c_nat ∈ AcceptingOutputCodes univToyHalt 1 univToyWrongWindow,
        u'.Tape = Tape.mk₁ (encNat (Encodable.encode c_nat))) :=
  ⟨(universalFinTM0_halts_with_code_iff univToyHalt default 1 univToyHaltWindow).mpr
      univToyHalt_haltsWithWindow,
    mt (universalFinTM0_halts_with_code_iff univToyHalt default 1 univToyWrongWindow).mp
      univToyHalt_not_haltsWithWrongWindow⟩

/-- Concrete non-halting `FinTM0` moving right forever on every tape symbol. -/
def univToyLoop : FinTM0 where
  Γ := Bool
  Λ := Unit
  machine _ _ := some ((), TM0.Stmt.move Dir.right)

/-- **Gate G5 Non-Halting Witness (`UNCONDITIONAL`)**:
Even on `univToyLoop` (which has no halting transitions), `AcceptingOutputCodes univToyLoop k w` is
nonempty while `universalFinTM0` never reaches any halting configuration from
`encodeInputTape univToyLoop t`. -/
-- tier: T2
theorem univToyLoop_universal_never_halts (t : FinSupportedTape univToyLoop)
    (k : ℕ) (w : Window univToyLoop k) :
    (AcceptingOutputCodes univToyLoop k w).Nonempty ∧
    ∀ u' : TM0.Cfg Γ₀ UniversalΛ,
      TM0.Reaches universalFinTM0.machine
        (universalFinTM0.initCfg (encodeInputTape univToyLoop t)) u' →
      TM0.step universalFinTM0.machine u' ≠ none := by
  refine ⟨acceptingOutputCodes_nonempty univToyLoop k w, fun u' hreach hterm ↦ ?_⟩
  obtain ⟨c_nat, hc_eval, _⟩ := universalFinTM0_halt_tape_eq_encNat univToyLoop t hreach hterm
  rw [relabel_evalCfg univToyLoop (univToyLoop.initCfg t)] at hc_eval
  obtain ⟨c, hcM, _⟩ := (Part.mem_map_iff _).mp hc_eval
  obtain ⟨_, htermM⟩ := StateTransition.mem_eval.mp hcM
  rcases c with ⟨_, _⟩
  simp [univToyLoop, TM0.step] at htermM

/-- **Gate G5 Prefix-Collision & Boundary-Cell Witness (`UNCONDITIONAL`)**:
`encNat 1` is a strict prefix of `encNat 2`, yet `Tape.mk₁ (encNat 2)` and `Tape.mk₁ (encNat 1)`
disagree at the boundary cell `i = (encNat 1).length` (showing why `i ≤ (encNat n₁).length` in
`eq_of_tape_mk₁_encNat_agree` is sharp). -/
-- tier: T1
theorem encNat_one_prefix_and_cell_sep :
    encNat 1 <+: encNat 2 ∧
    (Tape.mk₁ (encNat 2)).nth ((encNat 1).length : ℤ) ≠
      (Tape.mk₁ (encNat 1)).nth ((encNat 1).length : ℤ) := by
  have heq1 : encNat 1 = [mkMainΓ₀ true .cons, mkMainΓ₀ false .bit1] := rfl
  have heq2 :
      encNat 2 = [mkMainΓ₀ true .cons, mkMainΓ₀ false .bit1, mkMainΓ₀ false .bit0] := rfl
  refine ⟨⟨[mkMainΓ₀ false .bit0], by rw [heq1, heq2]; rfl⟩, fun h ↦ ?_⟩
  have hget : (encNat 2).getI (encNat 1).length = (encNat 1).getI (encNat 1).length := by
    simpa only [Tape.mk₁, Tape.mk₂, Tape.mk'_nth_nat, ListBlank.nth_mk] using h
  rw [heq1, heq2] at hget
  change mkMainΓ₀ false .bit0 = default at hget
  have hmain : (mkMainΓ₀ false .bit0).2 .main = (default : Γ₀).2 .main :=
    congrFun (congrArg Prod.snd hget) .main
  cases hmain

end S4TuringPoisson.Reversible
