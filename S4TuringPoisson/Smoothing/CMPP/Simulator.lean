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

public import S4TuringPoisson.Dynamics.Reversible.Bennett
public import S4TuringPoisson.Dynamics.Reversible.Universal
public import S4TuringPoisson.Smoothing.CMPP.Realize

/-!
# Unconditional Universal Reversible Turing Simulator (CMPP Milestone B3 & Refactor I2)

This module formalizes Milestone B3 (`S4TuringPoisson/Smoothing/CMPP/Simulator.lean`) of the
`CMPP21` reversible-computation and Hamiltonian-realization pipeline (`Bennett 1973`, `CMPP21`
Theorem 2.2 & Lemma 4.3, `MISSION_DIRECTIVE_CMPP.md` §4.4, §5 I2, §7), assembling Milestone B1
(`Bennett.lean`) and Milestone B2 (`Universal.lean`) into an **unconditional** inhabitant
`universalReversibleSimulator : UniversalReversibleSimulator`:

1. **Underlying Universal Reversible Machine & Initial Encoding (`S4TuringPoisson.CMPP`)**:
   - `universalRevTM`: Bennett's unidirectional reversible Turing machine
     `Reversible.bennettReversibleTM Reversible.universalFinTM0 : ReversibleTM.{0, 0}`, with finite
     shift-alphabet numbering `universalShiftEquiv` of cardinality `universalShiftCard`.
   - `universalInitRevCfg M t`: initial reversible configuration
     `Reversible.bennettInitCfg Reversible.universalFinTM0 (Reversible.encodeInputTape M t)`
     (independent of `(k, w)`), proved never to lie in `.halted` at step `0`.

2. **Variable-Radius Accepting Cylinder Blocks (Permitted Refactor I2)**:
   - `IsAcceptingCylinderBlock` and `universalAcceptBlocks M k w`: nonempty variable-radius family
     of cylinder blocks `⟨K_c, W⟩` (`K_c = (encNat (Encodable.encode c_nat)).length`) over
     `c_nat ∈ Reversible.AcceptingOutputCodes M k w` requiring `.halted q rel` at cell `0` and exact
     work-symbol agreement with `Tape.mk₁ (encNat (Encodable.encode c_nat))` on `0 .. K_c`.
   - Exact reversible orbit equivalence `universalOrbit_mem_acceptBlocks_iff` combining
     `Reversible.bennett_orbit_halted_backward`, `Reversible.bennett_orbit_halted_forward`, and
     `Reversible.universalFinTM0_halts_with_cylinder_iff`.

3. **Primitive-Recursive Initial Cantor Digit Enumerators**:
   - `universalSimulator_primrec_initDigits`: proves `primrec_initDigits` for every `M : FinTM0`
     using `Reversible.primrec_encodeInputList`, `Primrec.dom_finite` over the `1250`-symbol
     alphabet `Γ₀`, and `Primrec.nat_casesOn` factored cleanly over an abstract list-valued
     primitive-recursive map.

4. **Unconditional `universalReversibleSimulator` & Gate G5 End-to-End $S^4$ Sanity**:
   - Exports `S4TuringPoisson.universalReversibleSimulator : UniversalReversibleSimulator`
     (**UNCONDITIONAL**) and `section Sanity` (`universalReversibleSimulator_cmpp`,
     `universalReversibleSimulator_cmpp_isAutonomous`, and `universalReversibleSimulator_sanity` on
     `Sphere4`, `Checks.M_halt`, and `Checks.M_loop`), without registering a global
     `HasCMPPCantorCirculationHamiltonians` typeclass instance (reserved for Milestone Z).
-/

@[expose] public section

open Set TopologicalSpace Turing TuringRecursive
open scoped ContDiff Manifold Topology TuringRecursive

namespace S4TuringPoisson.CMPP

/-! ## 1. Universal Reversible Machine, Alphabet Numbering & Discrete Helpers -/

/-- Underlying unidirectional universal reversible Turing machine (`Bennett 1973` applied to
`Reversible.universalFinTM0`). Marked `@[reducible]` so `Fintype universalRevTM.ShiftAlphabet`
resolves directly to `Reversible.instFintypeShiftAlphabetBennettReversibleTM`. -/
@[reducible]
noncomputable def universalRevTM : ReversibleTM.{0, 0} :=
  Reversible.bennettReversibleTM Reversible.universalFinTM0

/-- Cardinality of the shift alphabet `universalRevTM.ShiftAlphabet`. -/
noncomputable def universalShiftCard : ℕ :=
  Fintype.card universalRevTM.ShiftAlphabet

/-- Explicit numbering `universalRevTM.ShiftAlphabet ≃ Fin universalShiftCard`. -/
noncomputable def universalShiftEquiv :
    universalRevTM.ShiftAlphabet ≃ Fin universalShiftCard :=
  Fintype.equivFin universalRevTM.ShiftAlphabet

/-- Initial reversible configuration of `universalRevTM` encoding `(M, t)` (independent of
`(k, w)`). -/
noncomputable def universalInitRevCfg (M : FinTM0) (t : FinSupportedTape M) :
    universalRevTM.Cfg :=
  Reversible.bennettInitCfg Reversible.universalFinTM0 (Reversible.encodeInputTape M t)

/-- Constant shift-alphabet digit index of the blank inactive cell `(default, none)` on the negative
half-tape of `universalInitRevCfg`. -/
noncomputable def universalNegBlankDigit : ℕ :=
  (universalShiftEquiv (default, none)).1

/-- Shift-alphabet digit index at cell `0` of `universalInitRevCfg` when the initial work-head
symbol on `universalFinTM0` is `a : Γ₀`. -/
noncomputable def universalHeadDigit (a : Γ₀) : ℕ :=
  (universalShiftEquiv (⟨a, true, none, true, false⟩, some (.exec default .eq))).1

/-- Shift-alphabet digit index at positive cell `m + 1` of `universalInitRevCfg` when the work-track
symbol on `universalFinTM0` is `a : Γ₀`. -/
noncomputable def universalTailDigit (a : Γ₀) : ℕ :=
  (universalShiftEquiv (⟨a, false, none, false, false⟩, none)).1

/-- Initial control state of `universalInitRevCfg M t` is `.exec default .eq`. -/
-- tier: T0
@[simp]
theorem universalInitRevCfg_q (M : FinTM0) (t : FinSupportedTape M) :
    (universalInitRevCfg M t).q = .exec default .eq :=
  rfl

/-- Initial tape of `universalInitRevCfg M t` is `bennettInitTape universalFinTM0` on
`encodeInputTape M t`. -/
-- tier: T0
@[simp]
theorem universalInitRevCfg_tape (M : FinTM0) (t : FinSupportedTape M) :
    (universalInitRevCfg M t).Tape =
      Reversible.bennettInitTape Reversible.universalFinTM0 (Reversible.encodeInputTape M t) :=
  rfl

/-- No initial simulator configuration `universalInitRevCfg M t` is in `.halted q rel` at step `0`.
-/
-- tier: T0
theorem universalInitRevCfg_q_ne_halted (M : FinTM0) (t : FinSupportedTape M)
    (q : Reversible.universalFinTM0.Λ) (rel : Ordering) :
    (universalInitRevCfg M t).q ≠ .halted q rel :=
  Reversible.bennettInitCfg_q_ne_halted Reversible.universalFinTM0 (Reversible.encodeInputTape M t)
    q rel

/-- Unfolding equation for `universalNegBlankDigit`. -/
-- tier: T0
@[simp]
theorem universalNegBlankDigit_eq :
    universalNegBlankDigit = (universalShiftEquiv (default, none)).1 :=
  by
  simp [universalNegBlankDigit]

/-- Zero lies in the symmetric integer interval `Set.Icc (-(K : ℤ)) (K : ℤ)` for every `K : ℕ`. -/
-- tier: T0
theorem zero_mem_Icc_neg_natCast (K : ℕ) : (0 : ℤ) ∈ Set.Icc (-(K : ℤ)) (K : ℤ) :=
  ⟨by omega, by omega⟩

/-- Every natural index `i ≤ K` casts into `Set.Icc (-(K : ℤ)) (K : ℤ)`. -/
-- tier: T0
theorem natCast_mem_Icc_of_le {i K : ℕ} (hi : i ≤ K) :
    (i : ℤ) ∈ Set.Icc (-(K : ℤ)) (K : ℤ) :=
  ⟨by omega, by omega⟩

/-- Membership `(i : ℤ) ∈ Set.Icc (-(K : ℤ)) (K : ℤ)` implies `i ≤ K`. -/
-- tier: T0
theorem le_of_natCast_mem_Icc {i K : ℕ} (hi : (i : ℤ) ∈ Set.Icc (-(K : ℤ)) (K : ℤ)) :
    i ≤ K := by
  rcases hi with ⟨_, h⟩
  omega

/-- One-sided tape initialization `Tape.mk₁ l` coincides with `Tape.mk₂ [] l`. -/
-- tier: T0
theorem tape_mk₁_eq_mk₂_nil {Γ : Type*} [Inhabited Γ] (l : List Γ) :
    Tape.mk₁ l = Tape.mk₂ [] l :=
  by
  rfl

/-- Indexing `l.getI 0` on an inhabited list agrees with `l.headI`. -/
-- tier: T0
theorem list_getI_zero {Γ : Type*} [Inhabited Γ] (l : List Γ) :
    l.getI 0 = l.headI := by
  cases l <;> rfl

/-- Mapping a list along `e : α ≃ β` and then `e.symm` recovers the original list. -/
-- tier: T0
theorem list_map_symm_map {α β : Type*} (e : α ≃ β) (l : List α) :
    (l.map e).map e.symm = l := by
  simp

/-! ## 2. Variable-Radius Accepting Cylinder Blocks & Reversible Orbit Equivalence -/

/-- Predicate characterizing when a radius-`K` cylinder block
`W : Set.Icc (-K) K → universalRevTM.ShiftAlphabet` witnesses halting of `universalFinTM0` in
`.halted q rel` with work-track prefix matching `Tape.mk₁ (encNat (Encodable.encode c_nat))` on
`0 .. K`. -/
def IsAcceptingCylinderBlock (c_nat : TM0.Cfg ℕ ℕ) (K : ℕ)
    (W : Set.Icc (-(K : ℤ)) (K : ℤ) → universalRevTM.ShiftAlphabet) : Prop :=
  K = (encNat (Encodable.encode c_nat)).length ∧
  (∃ (q : Reversible.universalFinTM0.Λ) (rel : Ordering),
    (W ⟨0, zero_mem_Icc_neg_natCast K⟩).2 = some (.halted q rel)) ∧
  ∀ (i : ℕ) (hi : (i : ℤ) ∈ Set.Icc (-(K : ℤ)) (K : ℤ)),
    (W ⟨(i : ℤ), hi⟩).1.sym = (Tape.mk₁ (encNat (Encodable.encode c_nat))).nth (i : ℤ)

/-- Family of variable-radius accepting cylinder blocks `⟨K, W⟩` for `(M, k, w)` (independent of
the input tape `t`). -/
def universalAcceptBlocks (M : FinTM0) (k : ℕ) (w : Window M k) :
    Set (Σ K : ℕ, Set.Icc (-(K : ℤ)) (K : ℤ) → universalRevTM.ShiftAlphabet) :=
  { b | ∃ c_nat ∈ Reversible.AcceptingOutputCodes M k w,
      IsAcceptingCylinderBlock c_nat b.1 b.2 }

/-- Canonical accepting cylinder block of radius `(encNat (Encodable.encode c_nat)).length`
associated to any relabeled configuration `c_nat : TM0.Cfg ℕ ℕ`. -/
noncomputable def canonicalAcceptBlock (c_nat : TM0.Cfg ℕ ℕ) :
    Σ K : ℕ, Set.Icc (-(K : ℤ)) (K : ℤ) → universalRevTM.ShiftAlphabet :=
  ⟨(encNat (Encodable.encode c_nat)).length, fun j ↦
    (⟨(Tape.mk₁ (encNat (Encodable.encode c_nat))).nth j.1,
        decide (j.1 = 0), none, decide (j.1 = 0), false⟩,
      if j.1 = 0 then some (.halted default .eq) else none)⟩

/-- `canonicalAcceptBlock c_nat` satisfies `IsAcceptingCylinderBlock c_nat`. -/
-- tier: T1
theorem isAcceptingCylinderBlock_canonical (c_nat : TM0.Cfg ℕ ℕ) :
    IsAcceptingCylinderBlock c_nat (canonicalAcceptBlock c_nat).1
      (canonicalAcceptBlock c_nat).2 :=
  ⟨rfl, ⟨default, .eq, rfl⟩, fun _ _ ↦ rfl⟩

/-- `universalAcceptBlocks M k w` is unconditionally nonempty for every `(M, k, w)` (even when `M`
has no halting states). -/
-- tier: T1
theorem universalAcceptBlocks_nonempty (M : FinTM0) (k : ℕ) (w : Window M k) :
    (universalAcceptBlocks M k w).Nonempty := by
  obtain ⟨c_nat, hc⟩ := Reversible.acceptingOutputCodes_nonempty M k w
  exact ⟨canonicalAcceptBlock c_nat, c_nat, hc, isAcceptingCylinderBlock_canonical c_nat⟩

/-- Every initial configuration `universalInitRevCfg M t` lies outside all accepting cylinder blocks
in `universalAcceptBlocks M k w` at step `0` (since its control state is `.exec default .eq ≠
.halted q rel`). -/
-- tier: T1
theorem encodeCfg_universalInitRevCfg_notMem (M : FinTM0) (t : FinSupportedTape M)
    (k : ℕ) (w : Window M k)
    {b : Σ K : ℕ, Set.Icc (-(K : ℤ)) (K : ℤ) → universalRevTM.ShiftAlphabet}
    (hb : b ∈ universalAcceptBlocks M k w) :
    universalRevTM.encodeCfg (universalInitRevCfg M t) ∉ cylinderIcc b.1 b.2 := by
  intro hcyl
  rcases hb with ⟨_, _, _, ⟨q, rel, hq0⟩, _⟩
  have h0 := congrArg Prod.snd (hcyl ⟨0, zero_mem_Icc_neg_natCast b.1⟩)
  dsimp only [ReversibleTM.encodeCfg, ↓reduceIte] at h0
  rw [hq0] at h0
  exact universalInitRevCfg_q_ne_halted M t q rel (Option.some.inj h0)

/-- **Unconditional Universal Reversible Orbit Equivalence (`UNCONDITIONAL`, Milestone B3)**:
For every finite Post–Turing machine `M : FinTM0`, input tape `t : FinSupportedTape M`, radius
`k : ℕ`, and target window `w : Window M k`, the forward reversible orbit of
`universalInitRevCfg M t` under `universalRevTM.step` enters `cylinderIcc b.1 b.2` for some
`b ∈ universalAcceptBlocks M k w` if and only if `HaltsWithWindow M t k w`. -/
-- tier: T2
theorem universalOrbit_mem_acceptBlocks_iff (M : FinTM0) (t : FinSupportedTape M)
    (k : ℕ) (w : Window M k) :
    (∃ n : ℕ, ∃ b ∈ universalAcceptBlocks M k w,
      universalRevTM.encodeCfg (universalRevTM.step^[n] (universalInitRevCfg M t)) ∈
        cylinderIcc b.1 b.2) ↔
    HaltsWithWindow M t k w := by
  rw [← Reversible.universalFinTM0_halts_with_cylinder_iff M t k w]
  constructor
  · rintro ⟨n, b, ⟨c_nat, hc_acc, hbK, ⟨q, rel, hq0⟩, hsym⟩, hcyl⟩
    let rcfg := universalRevTM.step^[n] (universalInitRevCfg M t)
    have h0 := congrArg Prod.snd (hcyl ⟨0, zero_mem_Icc_neg_natCast b.1⟩)
    dsimp only [ReversibleTM.encodeCfg, ↓reduceIte] at h0
    rw [hq0] at h0
    have hq : rcfg.q = .halted q rel := Option.some.inj h0
    obtain ⟨u', _, hreachU, htermU, htape_sym⟩ :=
      Reversible.bennett_orbit_halted_backward Reversible.universalFinTM0
        (Reversible.encodeInputTape M t) hq
    refine ⟨u', hreachU, htermU, c_nat, hc_acc, fun i hi ↦ ?_⟩
    have hi_mem : (i : ℤ) ∈ Set.Icc (-(b.1 : ℤ)) (b.1 : ℤ) :=
      natCast_mem_Icc_of_le (hbK.symm ▸ hi)
    have hcell := congrArg (fun x ↦ x.1.sym) (hcyl ⟨(i : ℤ), hi_mem⟩)
    dsimp only [ReversibleTM.encodeCfg] at hcell
    exact (htape_sym (i : ℤ)).symm.trans (hcell.trans (hsym i hi_mem))
  · rintro ⟨u', hreachU, htermU, c_nat, hc_acc, hprefix⟩
    obtain ⟨n, _, rel, hq, htape_sym⟩ :=
      Reversible.bennett_orbit_halted_forward Reversible.universalFinTM0
        (Reversible.encodeInputTape M t) hreachU htermU
    let rcfg := universalRevTM.step^[n] (universalInitRevCfg M t)
    let qU : Reversible.universalFinTM0.Λ := u'.q
    let K := (encNat (Encodable.encode c_nat)).length
    let b : Σ K : ℕ, Set.Icc (-(K : ℤ)) (K : ℤ) → universalRevTM.ShiftAlphabet :=
      ⟨K, fun j ↦ universalRevTM.encodeCfg rcfg j.1⟩
    refine ⟨n, b, ⟨c_nat, hc_acc, rfl, ⟨qU, rel, congrArg some hq⟩, fun i hi ↦ ?_⟩, fun _ ↦ rfl⟩
    dsimp only [b, ReversibleTM.encodeCfg]
    exact (htape_sym (i : ℤ)).trans (hprefix i (le_of_natCast_mem_Icc hi))

/-! ## 3. Primitive-Recursive Initial Cantor Digit Enumerators -/

/-- Every lookup table `Γ₀ → ℕ` on the finite `1250`-symbol universal alphabet `Γ₀` is primitive
recursive. -/
-- tier: T1
theorem primrec_of_dom_gamma0 (g : Γ₀ → ℕ) : Primrec g := by
  have : Finite Γ₀ := Finite.of_equiv _ TuringRecursive.gamma0Equiv.symm
  exact Primrec.dom_finite g

/-- Abstract primitive-recursive `Nat.casesOn` combinator over a list-valued map `f : α → List Γ₀`,
avoiding any `whnf` unfolding of `encodeInputList` when composing `universalHeadDigit` and
`universalTailDigit`. -/
-- tier: T1
theorem primrec_nonnegDigitAux {α : Type*} [Primcodable α]
    {f : α → List Γ₀} (hf : Primrec f)
    {g₀ gS : Γ₀ → ℕ} (hg₀ : Primrec g₀) (hgS : Primrec gS) :
    Primrec fun q : α × ℕ ↦
      Nat.casesOn (motive := fun _ ↦ ℕ) q.2
        (g₀ ((f q.1).getI 0))
        (fun m ↦ gS ((f q.1).tail.getI m)) := by
  refine Primrec.nat_casesOn Primrec.snd ?_ ?_
  · exact hg₀.comp (Primrec.list_getI.comp (hf.comp Primrec.fst) (Primrec.const 0))
  · exact (hgS.comp (Primrec.list_getI.comp
      (Primrec.list_tail.comp (hf.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd)).to₂

/-- Negative Cantor half-sequence digit of `universalInitRevCfg M (Tape.mk₂ L R_tape)` at any index
`j : ℕ` equals the constant blank digit `universalNegBlankDigit`. -/
-- tier: T1
theorem universalInitRevCfg_negHalf_digit (M : FinTM0) (L R_tape : List M.Γ) (j : ℕ) :
    (universalShiftEquiv
      (negHalf (universalRevTM.encodeCfg (universalInitRevCfg M (Tape.mk₂ L R_tape))) j)).1 =
        universalNegBlankDigit := by
  let lU : List Reversible.universalFinTM0.Γ :=
    Reversible.encodeInputList M (Tape.mk₂ L R_tape)
  have htape : Reversible.encodeInputTape M (Tape.mk₂ L R_tape) = Tape.mk₂ [] lU := rfl
  unfold universalInitRevCfg
  rw [htape, Reversible.bennettInitCfg_mk₂_negHalf]
  rfl

/-- Non-negative Cantor half-sequence digit `0` of `universalInitRevCfg M (Tape.mk₂ L R_tape)`. -/
-- tier: T1
theorem universalInitRevCfg_nonnegHalf_zero_digit (M : FinTM0) (L R_tape : List M.Γ) :
    (universalShiftEquiv
      (nonnegHalf (universalRevTM.encodeCfg (universalInitRevCfg M (Tape.mk₂ L R_tape))) 0)).1 =
        universalHeadDigit ((Reversible.encodeInputList M (Tape.mk₂ L R_tape)).getI 0) := by
  let lU : List Reversible.universalFinTM0.Γ :=
    Reversible.encodeInputList M (Tape.mk₂ L R_tape)
  have htape : Reversible.encodeInputTape M (Tape.mk₂ L R_tape) = Tape.mk₂ [] lU := rfl
  unfold universalInitRevCfg
  rw [htape, Reversible.bennettInitCfg_mk₂_nonnegHalf_zero, ← list_getI_zero lU]
  rfl

/-- Non-negative Cantor half-sequence digit `m + 1` of
`universalInitRevCfg M (Tape.mk₂ L R_tape)`. -/
-- tier: T1
theorem universalInitRevCfg_nonnegHalf_succ_digit (M : FinTM0) (L R_tape : List M.Γ) (m : ℕ) :
    (universalShiftEquiv
      (nonnegHalf
        (universalRevTM.encodeCfg (universalInitRevCfg M (Tape.mk₂ L R_tape))) (m + 1))).1 =
        universalTailDigit ((Reversible.encodeInputList M (Tape.mk₂ L R_tape)).tail.getI m) := by
  let lU : List Reversible.universalFinTM0.Γ :=
    Reversible.encodeInputList M (Tape.mk₂ L R_tape)
  have htape : Reversible.encodeInputTape M (Tape.mk₂ L R_tape) = Tape.mk₂ [] lU := rfl
  unfold universalInitRevCfg
  rw [htape, Reversible.bennettInitCfg_mk₂_nonnegHalf_succ]
  rfl

/-- **Primitive-Recursive Initial Cantor Digit Enumerators (`UNCONDITIONAL`, Milestone B3)**:
For every `M : FinTM0`, both Cantor half-sequence digit functions of
`universalRevTM.encodeCfg (universalInitRevCfg M (Tape.mk₂ L R_tape))` are primitive recursive in
`(L.map encΓ, R_tape.map encΓ, j)` (`encΓ := Fintype.equivFin M.Γ`). -/
-- tier: T2
theorem universalSimulator_primrec_initDigits (M : FinTM0) :
    ∃ (encΓ : M.Γ ≃ Fin (Fintype.card M.Γ))
      (negDig posDig :
        List (Fin (Fintype.card M.Γ)) × List (Fin (Fintype.card M.Γ)) × ℕ → ℕ),
      Primrec negDig ∧
      Primrec posDig ∧
      ∀ (L R_tape : List M.Γ) (j : ℕ),
        negDig (L.map encΓ, R_tape.map encΓ, j) =
          (universalShiftEquiv
            (negHalf
              (universalRevTM.encodeCfg (universalInitRevCfg M (Tape.mk₂ L R_tape))) j)).1 ∧
        posDig (L.map encΓ, R_tape.map encΓ, j) =
          (universalShiftEquiv
            (nonnegHalf
              (universalRevTM.encodeCfg (universalInitRevCfg M (Tape.mk₂ L R_tape))) j)).1 := by
  let encΓ := Fintype.equivFin M.Γ
  let Pair := List (Fin (Fintype.card M.Γ)) × List (Fin (Fintype.card M.Γ))
  let Arg := List (Fin (Fintype.card M.Γ)) × List (Fin (Fintype.card M.Γ)) × ℕ
  let f : Pair → List Γ₀ := fun p ↦
    Reversible.encodeInputList M (Tape.mk₂ (p.1.map encΓ.symm) (p.2.map encΓ.symm))
  let reassoc : Arg → Pair × ℕ := fun x ↦ ((x.1, x.2.1), x.2.2)
  let negDig : Arg → ℕ := fun _ ↦ universalNegBlankDigit
  let posDig : Arg → ℕ :=
    (fun q : Pair × ℕ ↦
      Nat.casesOn (motive := fun _ ↦ ℕ) q.2
        (universalHeadDigit ((f q.1).getI 0))
        (fun m ↦ universalTailDigit ((f q.1).tail.getI m))) ∘ reassoc
  have hf : Primrec f := Reversible.primrec_encodeInputList M
  have hreassoc : Primrec reassoc :=
    Primrec.pair (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have hposP : Primrec posDig :=
    (primrec_nonnegDigitAux hf
      (primrec_of_dom_gamma0 universalHeadDigit)
      (primrec_of_dom_gamma0 universalTailDigit)).comp hreassoc
  refine ⟨encΓ, negDig, posDig, Primrec.const universalNegBlankDigit, hposP, fun L R_tape j ↦ ?_⟩
  have hf_eq : f (L.map encΓ, R_tape.map encΓ) =
      Reversible.encodeInputList M (Tape.mk₂ L R_tape) := by
    dsimp only [f]
    rw [list_map_symm_map, list_map_symm_map]
  refine ⟨(universalInitRevCfg_negHalf_digit M L R_tape j).symm, ?_⟩
  rcases j with _ | m
  · change universalHeadDigit ((f (L.map encΓ, R_tape.map encΓ)).getI 0) = _
    rw [hf_eq]
    exact (universalInitRevCfg_nonnegHalf_zero_digit M L R_tape).symm
  · change universalTailDigit ((f (L.map encΓ, R_tape.map encΓ)).tail.getI m) = _
    rw [hf_eq]
    exact (universalInitRevCfg_nonnegHalf_succ_digit M L R_tape m).symm

/-! ### Generative Primitive-Recursive Rational-Box Enumerator & Orbit Injectivity (`SC-R4`) -/

/-- Explicit 3-element numbering `Ordering ≃ Fin 3` (`lt ↦ 0`, `eq ↦ 1`, `gt ↦ 2`). -/
def orderingEquivFin3 : Ordering ≃ Fin 3 where
  toFun
    | .lt => 0
    | .eq => 1
    | .gt => 2
  invFun
    | ⟨0, _⟩ => .lt
    | ⟨1, _⟩ => .eq
    | ⟨2, _⟩ => .gt
  left_inv o := by cases o <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- Indexing `(l.drop k).getI (n - k)` at `k ≤ n` agrees with `l.getI n`. -/
-- tier: T1
theorem list_drop_getI {α : Type*} [Inhabited α] (l : List α) {k n : ℕ} (h : k ≤ n) :
    (l.drop k).getI (n - k) = l.getI n := by
  by_cases hn : n < l.length
  · have hsub : n - k < (l.drop k).length := by simp; omega
    rw [List.getI_eq_getElem _ hsub, List.getI_eq_getElem _ hn, List.getElem_drop]
    congr 1
    omega
  · have hge : l.length ≤ n := Nat.le_of_not_lt hn
    have hge_drop : (l.drop k).length ≤ n - k := by simp; omega
    rw [List.getI_eq_default _ hge_drop, List.getI_eq_default _ hge]

/-- Indexing `(l₁ ++ l₂).getI n` past `l₁.length ≤ n` agrees with `l₂.getI (n - l₁.length)`. -/
-- tier: T1
theorem list_append_getI_right {α : Type*} [Inhabited α] (l₁ l₂ : List α) {n : ℕ}
    (h : l₁.length ≤ n) :
    (l₁ ++ l₂).getI n = l₂.getI (n - l₁.length) := by
  by_cases hn : n < (l₁ ++ l₂).length
  · have hsub : n - l₁.length < l₂.length := by simp at hn; omega
    rw [List.getI_eq_getElem _ hn, List.getI_eq_getElem _ hsub, List.getElem_append_right h]
  · have hge : (l₁ ++ l₂).length ≤ n := Nat.le_of_not_lt hn
    have hge₂ : l₂.length ≤ n - l₁.length := by simp at hge; omega
    rw [List.getI_eq_default _ hge, List.getI_eq_default _ hge₂]

/-- Reassembling a `Tape` from `T.left` and `T.right₀` via `Tape.mk'` recovers `T`. -/
-- tier: T1
theorem tape_mk'_left_right₀ {Γ : Type*} [Inhabited Γ] (T : Tape Γ) :
    Tape.mk' T.left T.right₀ = T := by
  rcases T with ⟨hd, l, r⟩
  simp [Tape.mk', Tape.right₀]

/-- Indexing `T.right₀.nth n` coincides with `T.nth (n : ℤ)`. -/
-- tier: T1
theorem tape_right₀_nth {Γ : Type*} [Inhabited Γ] (T : Tape Γ) (n : ℕ) :
    T.right₀.nth n = T.nth (n : ℤ) := by
  rcases n with _ | m <;> simp [Tape.right₀, Tape.nth]

/-- Decode the negative half-window list (`-1, …, -k`) from `encodeWindow encΓ k w`. -/
def decodeNegWindowList {nΓ : ℕ} (d₀ : Fin nΓ) (k : ℕ) (w_list : List (Fin nΓ)) :
    List (Fin nΓ) :=
  (List.range k).map fun idx ↦ w_list.getD (k - 1 - idx) d₀

/-- Decode the non-negative half-window list (`0, …, k`) from `encodeWindow encΓ k w`. -/
def decodePosWindowList {nΓ : ℕ} (d₀ : Fin nΓ) (k : ℕ) (w_list : List (Fin nΓ)) :
    List (Fin nΓ) :=
  (List.range (k + 1)).map fun idx ↦ w_list.getD (k + idx) d₀

/-- Mapping `decodeNegWindowList` of `encodeWindow encΓ k w` along `encΓ.symm` recovers the exact
negative window entries `w (-1), …, w (-k)`. -/
-- tier: T1
theorem decodeNegWindowList_encodeWindow {M : FinTM0}
    (encΓ : M.Γ ≃ Fin (Fintype.card M.Γ)) (k : ℕ) (w : Window M k) :
    (decodeNegWindowList (encΓ default) k (encodeWindow encΓ k w)).map encΓ.symm =
      List.ofFn fun j : Fin k ↦ w ⟨Int.negSucc j.1, ⟨by omega, by omega⟩⟩ := by
  refine List.ext_getElem (by simp [decodeNegWindowList]) fun idx h₁ h₂ ↦ ?_
  have hidx : idx < k := by simpa [decodeNegWindowList] using h₁
  have hlt : k - 1 - idx < (encodeWindow encΓ k w).length := by simp; omega
  simp only [decodeNegWindowList, List.getElem_map, List.getElem_range,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
  simp only [encodeWindow, List.getElem_ofFn, Equiv.symm_apply_apply]
  congr 1
  apply Subtype.ext
  dsimp only
  omega

/-- Mapping `decodePosWindowList` of `encodeWindow encΓ k w` along `encΓ.symm` recovers the exact
non-negative window entries `w 0, …, w k`. -/
-- tier: T1
theorem decodePosWindowList_encodeWindow {M : FinTM0}
    (encΓ : M.Γ ≃ Fin (Fintype.card M.Γ)) (k : ℕ) (w : Window M k) :
    (decodePosWindowList (encΓ default) k (encodeWindow encΓ k w)).map encΓ.symm =
      List.ofFn fun j : Fin (k + 1) ↦ w ⟨(j.1 : ℤ), ⟨by omega, by omega⟩⟩ := by
  refine List.ext_getElem (by simp [decodePosWindowList]) fun idx h₁ h₂ ↦ ?_
  have hidx : idx < k + 1 := by simpa [decodePosWindowList] using h₁
  have hlt : k + idx < (encodeWindow encΓ k w).length := by simp; omega
  simp only [decodePosWindowList, List.getElem_map, List.getElem_range,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
  simp only [encodeWindow, List.getElem_ofFn, Equiv.symm_apply_apply]
  congr 1
  apply Subtype.ext
  dsimp only
  omega

/-- Extending the decoded half-window lists by arbitrary tails `L_tail, R_tail` always yields a
`Tape M.Γ` agreeing with `w` on `[-k, k]`. -/
-- tier: T1
theorem tape_mk₂_window_append_nth {M : FinTM0} (k : ℕ) (w : Window M k)
    (L_tail R_tail : List M.Γ) (i : Set.Icc (-(k : ℤ)) (k : ℤ)) :
    (Tape.mk₂
      ((List.ofFn fun j : Fin k ↦ w ⟨Int.negSucc j.1, ⟨by omega, by omega⟩⟩) ++ L_tail)
      ((List.ofFn fun j : Fin (k + 1) ↦ w ⟨(j.1 : ℤ), ⟨by omega, by omega⟩⟩) ++ R_tail)).nth
        i.1 = w i := by
  rcases i with ⟨i, hi₁, hi₂⟩
  rcases i with n | n
  · have hn : n < k + 1 := by
      change (n : ℤ) ≤ (k : ℤ) at hi₂
      omega
    set R_win : List M.Γ :=
      List.ofFn fun j : Fin (k + 1) ↦ w ⟨(j.1 : ℤ), ⟨by omega, by omega⟩⟩
    have hR₁ : n < R_win.length := by simpa [R_win] using hn
    have hR₂ : n < (R_win ++ R_tail).length := by simp [R_win]; omega
    change (Tape.mk' _ (ListBlank.mk (R_win ++ R_tail))).nth (n : ℤ) = _
    rw [Tape.mk'_nth_nat, ListBlank.nth_mk, List.getI_eq_getElem _ hR₂,
      List.getElem_append_left hR₁]
    simp only [R_win, List.getElem_ofFn]
    rfl
  · have hn : n < k := by
      change -(k : ℤ) ≤ Int.negSucc n at hi₁
      omega
    set L_win : List M.Γ :=
      List.ofFn fun j : Fin k ↦ w ⟨Int.negSucc j.1, ⟨by omega, by omega⟩⟩
    have hL₁ : n < L_win.length := by simpa [L_win] using hn
    have hL₂ : n < (L_win ++ L_tail).length := by simp [L_win]; omega
    have hnth : (Tape.mk₂ (L_win ++ L_tail)
        ((List.ofFn fun j : Fin (k + 1) ↦ w ⟨(j.1 : ℤ), ⟨by omega, by omega⟩⟩) ++
          R_tail)).nth (Int.negSucc n) = (L_win ++ L_tail).getI n := rfl
    rw [hnth, List.getI_eq_getElem _ hL₂, List.getElem_append_left hL₁]
    simp only [L_win, List.getElem_ofFn]

/-- Every `T : Tape M.Γ` agreeing with `w : Window M k` on `[-k, k]` decomposes as `Tape.mk₂` of
the window prefixes appended with `T.left.trim.drop k` and `T.right₀.trim.drop (k + 1)`. -/
-- tier: T2
theorem tape_eq_mk₂_window_append_drop {M : FinTM0} {k : ℕ} {w : Window M k} {T : Tape M.Γ}
    (hw : ∀ i : Set.Icc (-(k : ℤ)) (k : ℤ), T.nth i.1 = w i) :
    Tape.mk₂
      ((List.ofFn fun j : Fin k ↦ w ⟨Int.negSucc j.1, ⟨by omega, by omega⟩⟩) ++
        T.left.trim.drop k)
      ((List.ofFn fun j : Fin (k + 1) ↦ w ⟨(j.1 : ℤ), ⟨by omega, by omega⟩⟩) ++
        T.right₀.trim.drop (k + 1)) = T := by
  set L_win : List M.Γ := List.ofFn fun j : Fin k ↦ w ⟨Int.negSucc j.1, ⟨by omega, by omega⟩⟩
  set R_win : List M.Γ :=
    List.ofFn fun j : Fin (k + 1) ↦ w ⟨(j.1 : ℤ), ⟨by omega, by omega⟩⟩
  rw [Tape.mk₂]
  have hL : ListBlank.mk (L_win ++ T.left.trim.drop k) = T.left := by
    refine ListBlank.ext fun n ↦ ?_
    rw [ListBlank.nth_mk]
    by_cases hn : n < k
    · have h₁ : n < L_win.length := by simpa [L_win] using hn
      have h₂ : n < (L_win ++ T.left.trim.drop k).length := by simp [L_win]; omega
      rw [List.getI_eq_getElem _ h₂, List.getElem_append_left h₁]
      simp only [L_win, List.getElem_ofFn]
      exact (hw ⟨Int.negSucc n, ⟨by omega, by omega⟩⟩).symm
    · have hge : k ≤ n := Nat.le_of_not_lt hn
      have hlen : L_win.length = k := by simp [L_win]
      rw [list_append_getI_right _ _ (by rw [hlen]; exact hge), hlen,
        list_drop_getI _ hge, ← ListBlank.nth_mk, ListBlank.mk_trim]
  have hR : ListBlank.mk (R_win ++ T.right₀.trim.drop (k + 1)) = T.right₀ := by
    refine ListBlank.ext fun n ↦ ?_
    rw [ListBlank.nth_mk]
    by_cases hn : n < k + 1
    · have h₁ : n < R_win.length := by simpa [R_win] using hn
      have h₂ : n < (R_win ++ T.right₀.trim.drop (k + 1)).length := by simp [R_win]; omega
      rw [List.getI_eq_getElem _ h₂, List.getElem_append_left h₁, tape_right₀_nth]
      simp only [R_win, List.getElem_ofFn]
      exact (hw ⟨(n : ℤ), ⟨by omega, by omega⟩⟩).symm
    · have hge : k + 1 ≤ n := Nat.le_of_not_lt hn
      have hlen : R_win.length = k + 1 := by simp [R_win]
      rw [list_append_getI_right _ _ (by rw [hlen]; exact hge), hlen,
        list_drop_getI _ hge, ← ListBlank.nth_mk, ListBlank.mk_trim]
  rw [hL, hR, tape_mk'_left_right₀]

/-- Finite-table symbol/state patcher at cell `0` forcing `.sym := a` and `.2 := some (.halted qU
rel)` on a template shift-alphabet symbol. -/
noncomputable def patchAcceptHeadSymbol
    (x : (Fin universalShiftCard × Fin (Fintype.card Reversible.universalFinTM0.Λ) × Fin 3) ×
      Γ₀) :
    universalRevTM.ShiftAlphabet :=
  let cell := (universalShiftEquiv.symm x.1.1).1
  let qU := (Fintype.equivFin Reversible.universalFinTM0.Λ).symm x.1.2.1
  let rel := orderingEquivFin3.symm x.1.2.2
  ({ cell with sym := x.2 }, some (.halted qU rel))

/-- Finite-table symbol patcher at positive cells `1 .. K` forcing `.sym := a` while preserving
all other cell/state components of a template shift-alphabet symbol. -/
noncomputable def patchAcceptPosSymbol (x : Fin universalShiftCard × Γ₀) :
    universalRevTM.ShiftAlphabet :=
  let s := universalShiftEquiv.symm x.1
  ({ s.1 with sym := x.2 }, s.2)

/-- Parameterized accepting cylinder window of radius `(encNat (Encodable.encode c_nat)).length`
built from `(c_nat, negRaw, headInfo, posRaw)`. -/
noncomputable def mkAcceptCylinderWindow (c_nat : TM0.Cfg ℕ ℕ)
    (negRaw : List (Fin universalShiftCard))
    (headInfo : Fin universalShiftCard ×
      Fin (Fintype.card Reversible.universalFinTM0.Λ) × Fin 3)
    (posRaw : List (Fin universalShiftCard)) :
    Set.Icc (-((encNat (Encodable.encode c_nat)).length : ℤ))
      ((encNat (Encodable.encode c_nat)).length : ℤ) →
      universalRevTM.ShiftAlphabet :=
  let l_enc := encNat (Encodable.encode c_nat)
  let dS₀ := universalShiftEquiv (default, none)
  fun j ↦
    match j.1 with
    | Int.ofNat 0 => patchAcceptHeadSymbol (headInfo, l_enc.getI 0)
    | Int.ofNat (m + 1) => patchAcceptPosSymbol (posRaw.getD m dS₀, l_enc.getI (m + 1))
    | Int.negSucc m => universalShiftEquiv.symm (negRaw.getD m dS₀)

/-- Every window built by `mkAcceptCylinderWindow` satisfies `IsAcceptingCylinderBlock`. -/
-- tier: T1
theorem isAcceptingCylinderBlock_mkAcceptCylinderWindow (c_nat : TM0.Cfg ℕ ℕ)
    (negRaw : List (Fin universalShiftCard))
    (headInfo : Fin universalShiftCard ×
      Fin (Fintype.card Reversible.universalFinTM0.Λ) × Fin 3)
    (posRaw : List (Fin universalShiftCard)) :
    IsAcceptingCylinderBlock c_nat (encNat (Encodable.encode c_nat)).length
      (mkAcceptCylinderWindow c_nat negRaw headInfo posRaw) := by
  refine ⟨rfl, ⟨(Fintype.equivFin Reversible.universalFinTM0.Λ).symm headInfo.2.1,
    orderingEquivFin3.symm headInfo.2.2, rfl⟩, fun i hi ↦ ?_⟩
  rcases i with _ | m
  · rw [Reversible.tape_mk₁_nth_nat]
    rfl
  · rw [Reversible.tape_mk₁_nth_nat]
    rfl

/-- Surjectivity of `mkAcceptCylinderWindow`: every `b = ⟨K, W⟩` satisfying
`IsAcceptingCylinderBlock c_nat b.1 b.2` is recovered from its negative, head, and positive
template codes. -/
-- tier: T2
theorem exists_mkAcceptCylinderWindow_eq {c_nat : TM0.Cfg ℕ ℕ}
    {b : Σ K : ℕ, Set.Icc (-(K : ℤ)) (K : ℤ) → universalRevTM.ShiftAlphabet}
    (hW : IsAcceptingCylinderBlock c_nat b.1 b.2) :
    ∃ (negRaw : List (Fin universalShiftCard))
      (headInfo : Fin universalShiftCard ×
        Fin (Fintype.card Reversible.universalFinTM0.Λ) × Fin 3)
      (posRaw : List (Fin universalShiftCard)),
      b = ⟨(encNat (Encodable.encode c_nat)).length,
        mkAcceptCylinderWindow c_nat negRaw headInfo posRaw⟩ := by
  rcases b with ⟨K, W⟩
  dsimp only at hW
  rcases hW with ⟨rfl, ⟨qU, rel, hq0⟩, hsym⟩
  let negRaw : List (Fin universalShiftCard) :=
    List.ofFn fun j : Fin (encNat (Encodable.encode c_nat)).length ↦
      universalShiftEquiv (W ⟨Int.negSucc j.1, ⟨by omega, by omega⟩⟩)
  let headInfo : Fin universalShiftCard ×
      Fin (Fintype.card Reversible.universalFinTM0.Λ) × Fin 3 :=
    (universalShiftEquiv (W ⟨0, zero_mem_Icc_neg_natCast _⟩),
      Fintype.equivFin Reversible.universalFinTM0.Λ qU,
      orderingEquivFin3 rel)
  let posRaw : List (Fin universalShiftCard) :=
    List.ofFn fun j : Fin (encNat (Encodable.encode c_nat)).length ↦
      universalShiftEquiv (W ⟨((j.1 + 1 : ℕ) : ℤ), ⟨by omega, by omega⟩⟩)
  refine ⟨negRaw, headInfo, posRaw, congrArg (Sigma.mk _) ?_⟩
  funext ⟨i, hi₁, hi₂⟩
  rcases i with (_ | m) | m
  · have hsym0 := hsym 0 (zero_mem_Icc_neg_natCast _)
    rw [Reversible.tape_mk₁_nth_nat] at hsym0
    have hidx0 : (⟨Int.ofNat 0, hi₁, hi₂⟩ :
        Set.Icc (-((encNat (Encodable.encode c_nat)).length : ℤ))
          ((encNat (Encodable.encode c_nat)).length : ℤ)) =
        ⟨0, zero_mem_Icc_neg_natCast _⟩ := rfl
    rw [hidx0]
    dsimp only [mkAcceptCylinderWindow, patchAcceptHeadSymbol, headInfo]
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply, ← hsym0, ← hq0]
    exact Prod.mk.eta
  · have hm : m < (encNat (Encodable.encode c_nat)).length := by
      change ((m + 1 : ℕ) : ℤ) ≤ ((encNat (Encodable.encode c_nat)).length : ℤ) at hi₂
      omega
    have hlen : m < posRaw.length := by simpa [posRaw] using hm
    have hsym_m := hsym (m + 1) ⟨hi₁, hi₂⟩
    rw [Reversible.tape_mk₁_nth_nat] at hsym_m
    have hidx_m : (⟨Int.ofNat (m + 1), hi₁, hi₂⟩ :
        Set.Icc (-((encNat (Encodable.encode c_nat)).length : ℤ))
          ((encNat (Encodable.encode c_nat)).length : ℤ)) =
        ⟨((m + 1 : ℕ) : ℤ), ⟨hi₁, hi₂⟩⟩ := rfl
    rw [hidx_m]
    dsimp only [mkAcceptCylinderWindow, patchAcceptPosSymbol]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some]
    simp only [posRaw, List.getElem_ofFn, Equiv.symm_apply_apply]
    rw [← hsym_m]
  · have hm : m < (encNat (Encodable.encode c_nat)).length := by
      change -((encNat (Encodable.encode c_nat)).length : ℤ) ≤ Int.negSucc m at hi₁
      omega
    have hlen : m < negRaw.length := by simpa [negRaw] using hm
    dsimp only [mkAcceptCylinderWindow]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some]
    simp only [negRaw, List.getElem_ofFn, Equiv.symm_apply_apply]

/-- Tuple of Gödel-decodable parameters indexing accepting Cantor rational boxes for a machine `M`
with `|M.Γ| = nΓ` and `|M.Λ| = nΛ`. -/
abbrev AcceptBoxTuple (nΓ nΛ : ℕ) : Type :=
  Fin nΛ × List (Fin nΓ) × List (Fin nΓ) ×
    List (Fin universalShiftCard) ×
    (Fin universalShiftCard × Fin (Fintype.card Reversible.universalFinTM0.Λ) × Fin 3) ×
    List (Fin universalShiftCard)

/-- **Generative `Computable` Rational-Box Enumerator (`UNCONDITIONAL`, Deliverable `SC-R4`)**:
For every `M : FinTM0`, produces a `Primrec` (hence `Computable`) enumerator `enumBoxes` such that
every `j : ℕ` yields a nonempty rational 2-box inside `UnitDisk2` and the union over `j : ℕ` equals
the union of `cantorCylinderRect` over `universalAcceptBlocks M k w`. -/
-- tier: T2
theorem universalSimulator_computable_targetBoxes (M : FinTM0) :
    ∃ (encΓ : M.Γ ≃ Fin (Fintype.card M.Γ))
      (enumBoxes : ℕ × List (Fin (Fintype.card M.Γ)) × ℕ → RatBox2),
      Computable enumBoxes ∧
      ∀ (k : ℕ) (w : Window M k),
        (∀ j : ℕ, (evalRatBox2 (enumBoxes (k, encodeWindow encΓ k w, j))).1.Nonempty) ∧
        (⋃ b ∈ universalAcceptBlocks M k w, (cantorCylinderRect universalShiftEquiv b.1 b.2).1) =
          ⋃ j : ℕ, (evalRatBox2 (enumBoxes (k, encodeWindow encΓ k w, j))).1 := by
  have : Finite Γ₀ := Finite.of_equiv _ TuringRecursive.gamma0Equiv.symm
  let nΓ := Fintype.card M.Γ
  let nΛ := Fintype.card M.Λ
  let nUΛ := Fintype.card Reversible.universalFinTM0.Λ
  let encΓ : M.Γ ≃ Fin nΓ := Fintype.equivFin M.Γ
  let encΛ : M.Λ ≃ Fin nΛ := Fintype.equivFin M.Λ
  let encUΛ : Reversible.universalFinTM0.Λ ≃ Fin nUΛ :=
    Fintype.equivFin Reversible.universalFinTM0.Λ
  let dΓ₀ : Fin nΓ := encΓ default
  let dΛ₀ : Fin nΛ := encΛ default
  let dS₀ : Fin universalShiftCard := universalShiftEquiv (default, none)
  let dUΛ₀ : Fin nUΛ := encUΛ default
  let Tup := AcceptBoxTuple nΓ nΛ
  let defaultTup : Tup := (dΛ₀, [], [], [], (dS₀, dUΛ₀, 1), [])
  let decodeTup : ℕ → Tup := fun j ↦ (Encodable.decode j).getD defaultTup
  let φΓ : Fin nΓ → ℕ := fun d ↦ Reversible.relabelSym M (encΓ.symm d)
  let φΛ : Fin nΛ → ℕ := fun q ↦ Reversible.relabelState M (encΛ.symm q)
  let patchHeadNat : (Fin universalShiftCard × Fin nUΛ × Fin 3) × Γ₀ → ℕ :=
    fun x ↦ (universalShiftEquiv (patchAcceptHeadSymbol x)).1
  let patchPosNat : Fin universalShiftCard × Γ₀ → ℕ :=
    fun x ↦ (universalShiftEquiv (patchAcceptPosSymbol x)).1
  let Input := ℕ × List (Fin nΓ) × ℕ
  let mkCfgNat : ℕ → List (Fin nΓ) → Tup → TM0.Cfg ℕ ℕ := fun k w_list tup ↦
    ⟨φΛ tup.1,
      Tape.mk₂
        ((decodeNegWindowList dΓ₀ k w_list ++ tup.2.1).map φΓ)
        ((decodePosWindowList dΓ₀ k w_list ++ tup.2.2.1).map φΓ)⟩
  let negDigitsOf : TM0.Cfg ℕ ℕ → Tup → List ℕ := fun c_nat tup ↦
    let l_enc := encNat (Encodable.encode c_nat)
    (List.range l_enc.length).map fun idx ↦ (tup.2.2.2.1.getD idx dS₀).1
  let posDigitsOf : TM0.Cfg ℕ ℕ → Tup → List ℕ := fun c_nat tup ↦
    let l_enc := encNat (Encodable.encode c_nat)
    patchHeadNat (tup.2.2.2.2.1, l_enc.getI 0) ::
      ((List.range l_enc.length).map fun idx ↦
        patchPosNat (tup.2.2.2.2.2.getD idx dS₀, l_enc.getI (idx + 1)))
  let B := cantorBase universalShiftCard
  let enumBoxes : Input → RatBox2 := fun inp ↦
    let tup := decodeTup inp.2.2
    let c_nat := mkCfgNat inp.1 inp.2.1 tup
    cantorCylinderRatBox B (negDigitsOf c_nat tup) (posDigitsOf c_nat tup)
  have hrect_eq : ∀ (k : ℕ) (w : Window M k) (tup : Tup),
      let c_nat := mkCfgNat k (encodeWindow encΓ k w) tup
      let K := (encNat (Encodable.encode c_nat)).length
      let W := mkAcceptCylinderWindow c_nat tup.2.2.2.1 tup.2.2.2.2.1 tup.2.2.2.2.2
      (⟨K, W⟩ : Σ K : ℕ, Set.Icc (-(K : ℤ)) (K : ℤ) → universalRevTM.ShiftAlphabet) ∈
        universalAcceptBlocks M k w ∧
      evalRatBox2
        (cantorCylinderRatBox B (negDigitsOf c_nat tup) (posDigitsOf c_nat tup)) =
        cantorCylinderRect universalShiftEquiv K W := by
    intro k w tup
    dsimp only
    set c_nat := mkCfgNat k (encodeWindow encΓ k w) tup
    set l_enc := encNat (Encodable.encode c_nat)
    set K := l_enc.length
    set W := mkAcceptCylinderWindow c_nat tup.2.2.2.1 tup.2.2.2.2.1 tup.2.2.2.2.2
    have hc_acc : c_nat ∈ Reversible.AcceptingOutputCodes M k w := by
      let L_tail := tup.2.1.map encΓ.symm
      let R_tail := tup.2.2.1.map encΓ.symm
      let c_M : TM0.Cfg M.Γ M.Λ :=
        ⟨encΛ.symm tup.1,
          Tape.mk₂
            ((decodeNegWindowList dΓ₀ k (encodeWindow encΓ k w)).map encΓ.symm ++ L_tail)
            ((decodePosWindowList dΓ₀ k (encodeWindow encΓ k w)).map encΓ.symm ++ R_tail)⟩
      refine ⟨c_M, ?_, ?_⟩
      · dsimp only [c_nat, mkCfgNat, c_M, L_tail, R_tail, TM0.Cfg.map, φΓ, φΛ]
        rw [Tape.map_mk₂, ← List.map_append, ← List.map_append, List.map_map, List.map_map]
        rfl
      · intro i
        dsimp only [c_M]
        rw [decodeNegWindowList_encodeWindow encΓ k w, decodePosWindowList_encodeWindow encΓ k w]
        exact tape_mk₂_window_append_nth k w L_tail R_tail i
    refine ⟨⟨c_nat, hc_acc, isAcceptingCylinderBlock_mkAcceptCylinderWindow c_nat
      tup.2.2.2.1 tup.2.2.2.2.1 tup.2.2.2.2.2⟩, ?_⟩
    refine evalRatBox2_cantorCylinderRatBox_eq universalShiftEquiv K W ?_ ?_
    · refine List.ext_getElem (by simp [negDigitsOf, K, l_enc]) fun idx h₁ h₂ ↦ ?_
      have hidx : idx < K := by simpa [negDigitsOf, K, l_enc] using h₁
      have hneg_idx : -((idx : ℤ) + 1) = Int.negSucc idx := by omega
      simp only [negDigitsOf, List.getElem_map, List.getElem_range, List.getElem_ofFn,
        windowNegPrefix, W, mkAcceptCylinderWindow, hneg_idx, Equiv.apply_symm_apply]
      rfl
    · refine List.ext_getElem (by simp [posDigitsOf, K, l_enc]) fun idx h₁ h₂ ↦ ?_
      rcases idx with _ | m
      · simp only [posDigitsOf, List.getElem_cons_zero, List.getElem_ofFn, windowNonnegPrefix,
          W, mkAcceptCylinderWindow, patchHeadNat]
      · simp only [posDigitsOf, List.getElem_cons_succ, List.getElem_map, List.getElem_range,
          List.getElem_ofFn, windowNonnegPrefix, W, mkAcceptCylinderWindow, patchPosNat]
        rfl
  refine ⟨encΓ, enumBoxes, ?_, fun k w ↦ ?_⟩
  · apply Primrec.to_comp
    have hk : Primrec (fun inp : Input ↦ inp.1) := Primrec.fst
    have hw : Primrec (fun inp : Input ↦ inp.2.1) := Primrec.fst.comp Primrec.snd
    have hdecode : Primrec decodeTup :=
      Primrec.option_getD.comp Primrec.decode (Primrec.const defaultTup)
    have htup : Primrec (fun inp : Input ↦ decodeTup inp.2.2) :=
      hdecode.comp (Primrec.snd.comp Primrec.snd)
    have hq : Primrec (fun inp : Input ↦ (decodeTup inp.2.2).1) := Primrec.fst.comp htup
    have h2 : Primrec (fun inp : Input ↦ (decodeTup inp.2.2).2) := Primrec.snd.comp htup
    have hL_ex : Primrec (fun inp : Input ↦ (decodeTup inp.2.2).2.1) := Primrec.fst.comp h2
    have h3 : Primrec (fun inp : Input ↦ (decodeTup inp.2.2).2.2) := Primrec.snd.comp h2
    have hR_ex : Primrec (fun inp : Input ↦ (decodeTup inp.2.2).2.2.1) := Primrec.fst.comp h3
    have h4 : Primrec (fun inp : Input ↦ (decodeTup inp.2.2).2.2.2) := Primrec.snd.comp h3
    have hnegRaw : Primrec (fun inp : Input ↦ (decodeTup inp.2.2).2.2.2.1) := Primrec.fst.comp h4
    have h5 : Primrec (fun inp : Input ↦ (decodeTup inp.2.2).2.2.2.2) := Primrec.snd.comp h4
    have hheadInfo : Primrec (fun inp : Input ↦ (decodeTup inp.2.2).2.2.2.2.1) :=
      Primrec.fst.comp h5
    have hposRaw : Primrec (fun inp : Input ↦ (decodeTup inp.2.2).2.2.2.2.2) :=
      Primrec.snd.comp h5
    have hnegWin : Primrec (fun inp : Input ↦ decodeNegWindowList dΓ₀ inp.1 inp.2.1) :=
      Primrec.list_map (Primrec.list_range.comp hk)
        (((Primrec.list_getD dΓ₀).comp (hw.comp Primrec.fst)
          (Primrec.nat_sub.comp
            (Primrec.nat_sub.comp (hk.comp Primrec.fst) (Primrec.const 1))
            Primrec.snd)).to₂)
    have hposWin : Primrec (fun inp : Input ↦ decodePosWindowList dΓ₀ inp.1 inp.2.1) :=
      Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp hk))
        (((Primrec.list_getD dΓ₀).comp (hw.comp Primrec.fst)
          (Primrec.nat_add.comp (hk.comp Primrec.fst) Primrec.snd)).to₂)
    have hφΓ : Primrec φΓ := Primrec.dom_finite φΓ
    have hφΛ : Primrec φΛ := Primrec.dom_finite φΛ
    have hfullL : Primrec (fun inp : Input ↦
        (decodeNegWindowList dΓ₀ inp.1 inp.2.1 ++ (decodeTup inp.2.2).2.1).map φΓ) :=
      Primrec.list_map (Primrec.list_append.comp hnegWin hL_ex) (hφΓ.comp Primrec.snd).to₂
    have hfullR : Primrec (fun inp : Input ↦
        (decodePosWindowList dΓ₀ inp.1 inp.2.1 ++ (decodeTup inp.2.2).2.2.1).map φΓ) :=
      Primrec.list_map (Primrec.list_append.comp hposWin hR_ex) (hφΓ.comp Primrec.snd).to₂
    have hc_nat : Primrec (fun inp : Input ↦ mkCfgNat inp.1 inp.2.1 (decodeTup inp.2.2)) :=
      Primrec.cfg_mk (hφΛ.comp hq) (Primrec.tape_mk₂.comp hfullL hfullR)
    have hl_enc : Primrec (fun inp : Input ↦
        encNat (Encodable.encode (mkCfgNat inp.1 inp.2.1 (decodeTup inp.2.2)))) :=
      primrec_encNat.comp (Primrec.encode.comp hc_nat)
    have hK_len : Primrec (fun inp : Input ↦
        (encNat (Encodable.encode (mkCfgNat inp.1 inp.2.1 (decodeTup inp.2.2)))).length) :=
      Primrec.list_length.comp hl_enc
    have hnegDigits : Primrec (fun inp : Input ↦
        negDigitsOf (mkCfgNat inp.1 inp.2.1 (decodeTup inp.2.2)) (decodeTup inp.2.2)) :=
      Primrec.list_map (Primrec.list_range.comp hK_len)
        (Primrec.fin_val.comp
          ((Primrec.list_getD dS₀).comp (hnegRaw.comp Primrec.fst) Primrec.snd)).to₂
    have hpatchHead : Primrec patchHeadNat := Primrec.dom_finite patchHeadNat
    have hpatchPos : Primrec patchPosNat := Primrec.dom_finite patchPosNat
    have hheadDig : Primrec (fun inp : Input ↦
        patchHeadNat ((decodeTup inp.2.2).2.2.2.2.1,
          (encNat (Encodable.encode (mkCfgNat inp.1 inp.2.1 (decodeTup inp.2.2)))).getI 0)) :=
      hpatchHead.comp (Primrec.pair hheadInfo (Primrec.list_getI.comp hl_enc (Primrec.const 0)))
    have htailDigs : Primrec (fun inp : Input ↦
        (List.range
          (encNat (Encodable.encode (mkCfgNat inp.1 inp.2.1 (decodeTup inp.2.2)))).length).map
          fun idx ↦
            patchPosNat ((decodeTup inp.2.2).2.2.2.2.2.getD idx dS₀,
              (encNat (Encodable.encode (mkCfgNat inp.1 inp.2.1 (decodeTup inp.2.2)))).getI
                (idx + 1))) :=
      Primrec.list_map (Primrec.list_range.comp hK_len)
        (hpatchPos.comp
          (Primrec.pair
            ((Primrec.list_getD dS₀).comp (hposRaw.comp Primrec.fst) Primrec.snd)
            (Primrec.list_getI.comp (hl_enc.comp Primrec.fst)
              (Primrec.succ.comp Primrec.snd)))).to₂
    have hposDigits : Primrec (fun inp : Input ↦
        posDigitsOf (mkCfgNat inp.1 inp.2.1 (decodeTup inp.2.2)) (decodeTup inp.2.2)) :=
      Primrec.list_cons.comp hheadDig htailDigs
    exact (primrec_cantorCylinderRatBox B).comp hnegDigits hposDigits
  · refine ⟨fun j ↦ ?_, ?_⟩
    · have heq := (hrect_eq k w (decodeTup j)).2
      dsimp only [enumBoxes]
      rw [heq]
      exact cantorCylinderRect_nonempty universalShiftEquiv _ _
    · apply Set.Subset.antisymm
      · intro y hy
        rw [Set.mem_iUnion₂] at hy
        rcases hy with ⟨b, ⟨c_nat, ⟨c, hc_eq, hwin⟩, hW⟩, hy_rect⟩
        obtain ⟨negRaw, headInfo, posRaw, rfl⟩ := exists_mkAcceptCylinderWindow_eq hW
        dsimp only at hy_rect
        let L_ex : List (Fin nΓ) := (c.Tape.left.trim.drop k).map encΓ
        let R_ex : List (Fin nΓ) := (c.Tape.right₀.trim.drop (k + 1)).map encΓ
        let tup : Tup := (encΛ c.q, L_ex, R_ex, negRaw, headInfo, posRaw)
        have hc_mk : mkCfgNat k (encodeWindow encΓ k w) tup = c_nat := by
          rw [hc_eq]
          have hq_eq : φΛ (encΛ c.q) = Reversible.relabelState M c.q := by
            simp [φΛ]
          have hL_map :
              (decodeNegWindowList dΓ₀ k (encodeWindow encΓ k w) ++ L_ex).map φΓ =
                ((List.ofFn fun j : Fin k ↦ w ⟨Int.negSucc j.1, ⟨by omega, by omega⟩⟩) ++
                  c.Tape.left.trim.drop k).map (Reversible.relabelSym M) := by
            rw [← decodeNegWindowList_encodeWindow encΓ k w]
            simp [L_ex, φΓ, dΓ₀, List.map_append, List.map_map, Function.comp_def]
          have hR_map :
              (decodePosWindowList dΓ₀ k (encodeWindow encΓ k w) ++ R_ex).map φΓ =
                ((List.ofFn fun j : Fin (k + 1) ↦ w ⟨(j.1 : ℤ), ⟨by omega, by omega⟩⟩) ++
                  c.Tape.right₀.trim.drop (k + 1)).map (Reversible.relabelSym M) := by
            rw [← decodePosWindowList_encodeWindow encΓ k w]
            simp [R_ex, φΓ, dΓ₀, List.map_append, List.map_map, Function.comp_def]
          dsimp only [mkCfgNat, tup, TM0.Cfg.map]
          rw [hq_eq, hL_map, hR_map, ← Tape.map_mk₂, tape_eq_mk₂_window_append_drop hwin]
        have hdec_surj : ∃ j₀ : ℕ, decodeTup j₀ = tup :=
          ⟨Encodable.encode tup, by dsimp only [decodeTup]; rw [Encodable.encodek]; rfl⟩
        obtain ⟨j₀, hj₀⟩ := hdec_surj
        rw [Set.mem_iUnion]
        refine ⟨j₀, ?_⟩
        have hbox : enumBoxes (k, encodeWindow encΓ k w, j₀) =
            cantorCylinderRatBox B
              (negDigitsOf (mkCfgNat k (encodeWindow encΓ k w) tup) tup)
              (posDigitsOf (mkCfgNat k (encodeWindow encΓ k w) tup) tup) := by
          dsimp only [enumBoxes]
          rw [hj₀]
        rw [hbox, (hrect_eq k w tup).2]
        change y ∈ (cantorCylinderRect universalShiftEquiv
          (encNat (Encodable.encode (mkCfgNat k (encodeWindow encΓ k w) tup))).length
          (mkAcceptCylinderWindow (mkCfgNat k (encodeWindow encΓ k w) tup)
            negRaw headInfo posRaw)).1
        rw [hc_mk]
        exact hy_rect
      · intro y hy
        rw [Set.mem_iUnion] at hy
        obtain ⟨j, hy_j⟩ := hy
        obtain ⟨hmem_acc, heq_box⟩ := hrect_eq k w (decodeTup j)
        dsimp only [enumBoxes] at hy_j
        rw [heq_box] at hy_j
        exact Set.mem_biUnion hmem_acc hy_j

/-- Every initial simulator configuration `universalInitRevCfg M t` generates an infinite injective
forward orbit under `universalRevTM.step` (`Deliverable SC-R4`). -/
-- tier: T1
theorem universalSimulator_orbit_initRevCfg_injective (M : FinTM0) (t : FinSupportedTape M) :
    Function.Injective (fun n : ℕ ↦ universalRevTM.step^[n] (universalInitRevCfg M t)) :=
  Reversible.bennettReversibleTM_orbit_initCfg_injective Reversible.universalFinTM0
    (Reversible.encodeInputTape M t)

end S4TuringPoisson.CMPP

namespace S4TuringPoisson

/-! ## 4. Unconditional `universalReversibleSimulator` & Gate G5 End-to-End $S^4$ Sanity -/

/-- **Unconditional Universal Reversible Turing Simulator (`UNCONDITIONAL`, Milestone B3 & SC-R4)**
(`Bennett 1973`, `CMPP21` Theorem 2.2 & Lemma 4.3, `MISSION_DIRECTIVE_CMPP.md` §4.4, §5 I2, §7):
Simulates every finite Post–Turing machine `M : FinTM0` on bi-infinite sequences over the fixed
finite shift alphabet of `Reversible.bennettReversibleTM Reversible.universalFinTM0`, with
variable-radius accepting cylinder blocks (`Refactor I2`), primitive-recursive initial Cantor digit
enumerators, generative primitive-recursive rational-box target enumerators, and injective forward
orbits. -/
noncomputable def universalReversibleSimulator : UniversalReversibleSimulator where
  R := CMPP.universalRevTM
  shiftCard := CMPP.universalShiftCard
  encShift := CMPP.universalShiftEquiv
  initRevCfg := CMPP.universalInitRevCfg
  acceptBlocks := CMPP.universalAcceptBlocks
  acceptBlocks_nonempty := CMPP.universalAcceptBlocks_nonempty
  orbit_mem_acceptBlocks_iff := CMPP.universalOrbit_mem_acceptBlocks_iff
  encodeCfg_init_notMem_of_step_ne_none M t k w _ _ hb :=
    CMPP.encodeCfg_universalInitRevCfg_notMem M t k w hb
  primrec_initDigits := CMPP.universalSimulator_primrec_initDigits
  computable_targetBoxes := CMPP.universalSimulator_computable_targetBoxes
  orbit_initRevCfg_injective := CMPP.universalSimulator_orbit_initRevCfg_injective

section Sanity

/-- Unconditional `HasCMPPCantorCirculationHamiltonians` witness built by feeding
`universalReversibleSimulator` into `hasCMPP_of_simulator`.

Declared deliberately as a `def` (**not** a global `[instance]`, which belongs to Wave 4
Milestone Z in `CMPPInstance.lean`). -/
@[instance_reducible, nolint defsWithUnderscore]
noncomputable def universalReversibleSimulator_cmpp :
    HasCMPPCantorCirculationHamiltonians :=
  hasCMPP_of_simulator universalReversibleSimulator

/-- Every planar Hamiltonian generator in `universalReversibleSimulator_cmpp.generators` is
autonomous (`UNCONDITIONAL`). -/
-- tier: T1
theorem universalReversibleSimulator_cmpp_isAutonomous :
    ∀ P ∈ universalReversibleSimulator_cmpp.generators, P.IsAutonomous :=
  hasCMPP_of_simulator_isAutonomous universalReversibleSimulator

end Sanity

end S4TuringPoisson
