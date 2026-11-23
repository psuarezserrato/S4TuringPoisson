-- Verified by gemma_loop.py (declaration: S4TuringPoisson.Reversible.bennettDirIn_seekHistRight, tier: T0, attempt: 5, spec: Bennett.lean)
@[simp]
theorem bennettDirIn_seekHistRight {M : FinTM0} (e : M.Λ × M.Γ) :
    bennettDirIn (BennettState.seekHistRight (M := M) e) = .right :=
  by
  simp [bennettDirIn]
