-- Verified by gemma_loop.py (declaration: S4TuringPoisson.Reversible.universalFinTM0_machine, tier: T0, attempt: 1, spec: Universal.lean)
@[simp]
theorem universalFinTM0_machine : universalFinTM0.machine = U :=
  by
  unfold universalFinTM0
  simp
