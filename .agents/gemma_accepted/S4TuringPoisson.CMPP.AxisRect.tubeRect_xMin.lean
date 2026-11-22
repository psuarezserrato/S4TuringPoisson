-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.AxisRect.tubeRect_xMin, tier: T0, attempt: 5, spec: Digits.lean)
@[simp]
theorem tubeRect_xMin (R : AxisRect) (dx dy : ℝ) :
    (R.tubeRect dx dy).xMin = min R.xMin (R.xMin + dx) :=
  by
  rfl
