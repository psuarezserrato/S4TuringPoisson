-- Verified by gemma_loop.py (declaration: S4TuringPoisson.Reversible.bennettReversibleTM_dirIn, tier: T0, attempt: 1, spec: Bennett.lean)
@[simp]
theorem bennettReversibleTM_dirIn (M : FinTM0) :
    (bennettReversibleTM M).dirIn = bennettDirIn :=
  by
  rfl
