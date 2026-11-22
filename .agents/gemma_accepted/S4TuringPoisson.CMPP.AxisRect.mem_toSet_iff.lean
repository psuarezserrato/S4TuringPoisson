-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.AxisRect.mem_toSet_iff, tier: T0, attempt: 2, spec: Digits.lean)
@[simp]
theorem mem_toSet_iff (R : AxisRect) (p : EuclideanPlane) :
    p ∈ R.toSet ↔ p 0 ∈ Set.Icc R.xMin R.xMax ∧ p 1 ∈ Set.Icc R.yMin R.yMax :=
  by
  rw [AxisRect.toSet]
  simp
