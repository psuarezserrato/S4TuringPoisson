-- Verified by gemma_loop.py (declaration: S4TuringPoisson.Reversible.bennettDirIn_startReturn, tier: T0, attempt: 2, spec: Bennett.lean)
@[simp]
theorem bennettDirIn_startReturn {M : FinTM0} (q' : M.Λ) (rel : Ordering) :
    bennettDirIn (BennettState.startReturn (M := M) q' rel) = .stay :=
  by
  unfold bennettDirIn
  simp
