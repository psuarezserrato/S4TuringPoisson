-- Verified by gemma_loop.py (declaration: S4TuringPoisson.Reversible.bennettDirIn_seekWorkRight, tier: T0, attempt: 2, spec: Bennett.lean)
@[simp]
theorem bennettDirIn_seekWorkRight {M : FinTM0} (q' : M.Λ) :
    bennettDirIn (BennettState.seekWorkRight (M := M) q') = .right :=
  by
  simp [bennettDirIn]
