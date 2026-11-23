-- Verified by gemma_loop.py (declaration: S4TuringPoisson.Reversible.bennettInitTape_right, tier: T0, attempt: 1, spec: Bennett.lean)
@[simp]
theorem bennettInitTape_right (M : FinTM0) (t : FinSupportedTape M) :
    (bennettInitTape M t).right = t.right.map (bennettInactiveCell M) :=
  by
  simp [bennettInitTape]
