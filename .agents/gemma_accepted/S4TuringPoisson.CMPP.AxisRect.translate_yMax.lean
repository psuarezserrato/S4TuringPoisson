-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.AxisRect.translate_yMax, tier: T0, attempt: 1, spec: Digits.lean)
@[simp]
theorem translate_yMax (R : AxisRect) (dx dy : ℝ) :
    (R.translate dx dy).yMax = R.yMax + dy :=
  by
  unfold translate
  simp
