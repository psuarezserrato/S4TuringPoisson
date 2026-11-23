-- Verified by gemma_loop.py (declaration: S4TuringPoisson.Reversible.bennettInitTape_left, tier: T0, attempt: 3, spec: Bennett.lean)
@[simp]
theorem bennettInitTape_left (M : FinTM0) (t : FinSupportedTape M) :
    (bennettInitTape M t).left = t.left.map (bennettInactiveCell M) :=
  by
  rfl
