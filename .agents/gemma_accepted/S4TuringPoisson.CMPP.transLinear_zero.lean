-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.transLinear_zero, tier: T0, attempt: 2, spec: Primitives.lean)
@[simp]
theorem transLinear_zero (y : EuclideanPlane) : transLinear 0 y = 0 :=
  by
  simp [transLinear]
