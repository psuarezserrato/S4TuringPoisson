-- Verified by gemma_loop.py (declaration: S4TuringPoisson.hasCMPP_of_simulator_r₀, tier: T0, attempt: 1, spec: Realize.lean)
@[simp]
theorem hasCMPP_of_simulator_r₀ (S : UniversalReversibleSimulator) :
    (hasCMPP_of_simulator S).r₀ = CMPP.cmppR0 :=
  by
  rfl
