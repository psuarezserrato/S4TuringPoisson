-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.AxisRect.translate_yMin, tier: T0, attempt: 2, spec: Digits.lean)
@[simp]
theorem translate_yMin (R : AxisRect) (dx dy : ℝ) :
    (R.translate dx dy).yMin = R.yMin + dy :=
  by
  unfold translate
  simp
