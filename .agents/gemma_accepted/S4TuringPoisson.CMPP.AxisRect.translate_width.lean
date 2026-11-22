-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.AxisRect.translate_width, tier: T0, attempt: 1, spec: Digits.lean)
@[simp]
theorem translate_width (R : AxisRect) (dx dy : ℝ) :
    (R.translate dx dy).width = R.width :=
  by
  unfold width
  unfold translate
  field_simp
  linarith
