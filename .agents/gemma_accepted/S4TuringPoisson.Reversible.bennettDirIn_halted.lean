-- Verified by gemma_loop.py (declaration: S4TuringPoisson.Reversible.bennettDirIn_halted, tier: T0, attempt: 1, spec: Bennett.lean)
@[simp]
theorem bennettDirIn_halted {M : FinTM0} (q : M.Λ) (rel : Ordering) :
    bennettDirIn (BennettState.halted (M := M) q rel) = .stay :=
  by
  simp [bennettDirIn]
