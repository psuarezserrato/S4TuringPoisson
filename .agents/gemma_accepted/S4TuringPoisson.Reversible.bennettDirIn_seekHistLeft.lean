-- Verified by gemma_loop.py (declaration: S4TuringPoisson.Reversible.bennettDirIn_seekHistLeft, tier: T0, attempt: 1, spec: Bennett.lean)
@[simp]
theorem bennettDirIn_seekHistLeft {M : FinTM0} (e : M.Λ × M.Γ) :
    bennettDirIn (BennettState.seekHistLeft (M := M) e) = .left :=
  by
  rfl
