-- Verified by gemma_loop.py (declaration: S4TuringPoisson.hasCMPP_of_simulator_sim, tier: T0, attempt: 1, spec: Realize.lean)
@[simp]
theorem hasCMPP_of_simulator_sim (S : UniversalReversibleSimulator) :
    (hasCMPP_of_simulator S).sim = S :=
  by
  rfl
