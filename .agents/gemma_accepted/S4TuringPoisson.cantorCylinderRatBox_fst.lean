-- Verified by gemma_loop.py (declaration: S4TuringPoisson.cantorCylinderRatBox_fst, tier: T0, attempt: 1, spec: GeneralizedShift.lean)
@[simp]
theorem cantorCylinderRatBox_fst (B : ℕ) (negDigits posDigits : List ℕ) :
    (cantorCylinderRatBox B negDigits posDigits).1 = cantorIntervalRatPair B negDigits :=
  by
  simp [cantorCylinderRatBox]
