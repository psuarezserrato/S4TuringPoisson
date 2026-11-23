-- Verified by gemma_loop.py (declaration: S4TuringPoisson.Reversible.tape_mk₁_nth_nat, tier: T0, attempt: 1, spec: Universal.lean)
@[simp]
theorem tape_mk₁_nth_nat {Γ : Type*} [Inhabited Γ] (l : List Γ) (i : ℕ) :
    (Tape.mk₁ l).nth (i : ℤ) = l.getI i :=
  by
  simp [Tape.mk₁, Tape.mk₂, Tape.mk'_nth_nat, ListBlank.nth_mk]
