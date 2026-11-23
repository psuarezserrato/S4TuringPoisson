-- Verified by gemma_loop.py (declaration: S4TuringPoisson.Reversible.encodeInputList_apply, tier: T0, attempt: 1, spec: Universal.lean)
theorem encodeInputList_apply (M : FinTM0) (t : FinSupportedTape M) :
    encodeInputList M t =
      encUniv (relabelCode M, (M.initCfg t).map (relabelSym M) (relabelState M)) :=
  by
  unfold encodeInputList
  rfl
