-- Verified by gemma_loop.py (declaration: S4TuringPoisson.Reversible.bennettDirIn_seekWorkLeft, tier: T0, attempt: 2, spec: Bennett.lean)
@[simp]
theorem bennettDirIn_seekWorkLeft {M : FinTM0} (q' : M.Λ) :
    bennettDirIn (BennettState.seekWorkLeft (M := M) q') = .left :=
  by
  simp [bennettDirIn]
