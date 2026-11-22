-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.AxisRect.translate_height, tier: T0, attempt: 3, spec: Digits.lean)
@[simp]
theorem translate_height (R : AxisRect) (dx dy : ℝ) :
    (R.translate dx dy).height = R.height :=
  by
  unfold height
  simp only [translate]
  linarith
