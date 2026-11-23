-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.universalNegBlankDigit_eq, tier: T0, attempt: 1, spec: Simulator.lean)
@[simp]
theorem universalNegBlankDigit_eq :
    universalNegBlankDigit = (universalShiftEquiv (default, none)).1 :=
  by
  simp [universalNegBlankDigit]
