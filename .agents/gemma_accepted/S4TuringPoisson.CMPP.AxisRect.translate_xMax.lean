-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.AxisRect.translate_xMax, tier: T0, attempt: 1, spec: Digits.lean)
@[simp]
theorem translate_xMax (R : AxisRect) (dx dy : ℝ) :
    (R.translate dx dy).xMax = R.xMax + dx :=
  by
  unfold translate
  simp
