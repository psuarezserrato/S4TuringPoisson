-- Verified by gemma_loop.py (declaration: S4TuringPoisson.Reversible.BennettCell.default_sym, tier: T0, attempt: 2, spec: Bennett.lean)
@[simp]
theorem BennettCell.default_sym (M : FinTM0) :
    (default : BennettCell M).sym = default :=
  by
  rfl
