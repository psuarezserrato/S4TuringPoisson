-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.cmppR0_pos, tier: T0, attempt: 1, spec: Relocation.lean)
theorem cmppR0_pos : 0 < cmppR0 :=
  by
  unfold cmppR0
  norm_cast
  linarith
