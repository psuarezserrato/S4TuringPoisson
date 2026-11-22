-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.AxisRect.mem_openExpand_iff, tier: T0, attempt: 4, spec: Primitives.lean)
@[simp]
theorem AxisRect.mem_openExpand_iff (R : AxisRect) (ε : ℝ) (p : EuclideanPlane) :
    p ∈ R.openExpand ε ↔
      p 0 ∈ Set.Ioo (R.xMin - ε) (R.xMax + ε) ∧
      p 1 ∈ Set.Ioo (R.yMin - ε) (R.yMax + ε) :=
  by
  unfold AxisRect.openExpand
  simp
