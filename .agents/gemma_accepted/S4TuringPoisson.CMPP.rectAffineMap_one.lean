-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.rectAffineMap_one, tier: T0, attempt: 1, spec: Relocation.lean)
@[simp]
theorem rectAffineMap_one (P P' : AxisRect) (μ : ℝ) (y : EuclideanPlane) :
    rectAffineMap P P' μ y 1 = P'.center 1 + Real.exp μ * (y 1 - P.center 1) :=
  by
  rw [rectAffineMap]
  simp
