-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.AxisRect.tubeRect_yMin, tier: T0, attempt: 4, spec: Digits.lean)
@[simp]
theorem tubeRect_yMin (R : AxisRect) (dx dy : ℝ) :
    (R.tubeRect dx dy).yMin = min R.yMin (R.yMin + dy) :=
  by
  rfl
