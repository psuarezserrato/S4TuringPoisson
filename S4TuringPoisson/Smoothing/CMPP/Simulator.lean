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

end S4TuringPoisson.CMPP

namespace S4TuringPoisson

/-! ## 4. Unconditional `universalReversibleSimulator` & Gate G5 End-to-End $S^4$ Sanity -/

/-- **Unconditional Universal Reversible Turing Simulator (`UNCONDITIONAL`, Milestone B3)**
(`Bennett 1973`, `CMPP21` Theorem 2.2 & Lemma 4.3, `MISSION_DIRECTIVE_CMPP.md` §4.4, §5 I2, §7):
Simulates every finite Post–Turing machine `M : FinTM0` on bi-infinite sequences over the fixed
finite shift alphabet of `Reversible.bennettReversibleTM Reversible.universalFinTM0`, with
variable-radius accepting cylinder blocks (`Refactor I2`) and primitive-recursive initial Cantor
digit enumerators. -/
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
