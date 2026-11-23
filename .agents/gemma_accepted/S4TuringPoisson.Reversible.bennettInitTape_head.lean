-- Verified by gemma_loop.py (declaration: S4TuringPoisson.Reversible.bennettInitTape_head, tier: T0, attempt: 2, spec: Bennett.lean)
@[simp]
theorem bennettInitTape_head (M : FinTM0) (t : FinSupportedTape M) :
    (bennettInitTape M t).head = ⟨t.head, true, none, true, false⟩ :=
  by
  simp [bennettInitTape]
