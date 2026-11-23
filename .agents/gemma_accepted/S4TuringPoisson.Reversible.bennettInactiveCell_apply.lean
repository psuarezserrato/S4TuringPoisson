-- Verified by gemma_loop.py (declaration: S4TuringPoisson.Reversible.bennettInactiveCell_apply, tier: T0, attempt: 2, spec: Bennett.lean)
@[simp]
theorem bennettInactiveCell_apply (M : FinTM0) (a : M.Γ) :
    bennettInactiveCell M a = ⟨a, false, none, false, false⟩ :=
  by
  rfl
