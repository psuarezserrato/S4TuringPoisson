-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.AxisRect.translate_xMin, tier: T0, attempt: 1, spec: Digits.lean)
@[simp]
theorem translate_xMin (R : AxisRect) (dx dy : ℝ) :
    (R.translate dx dy).xMin = R.xMin + dx :=
  by
  unfold translate
  simp
