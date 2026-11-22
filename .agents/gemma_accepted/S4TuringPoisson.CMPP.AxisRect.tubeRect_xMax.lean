-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.AxisRect.tubeRect_xMax, tier: T0, attempt: 5, spec: Digits.lean)
@[simp]
theorem tubeRect_xMax (R : AxisRect) (dx dy : ℝ) :
    (R.tubeRect dx dy).xMax = max R.xMax (R.xMax + dx) :=
  by
  rfl
