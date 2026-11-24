-- Verified by gemma_loop.py (declaration: S4TuringPoisson.cantorCylinderRatBox_snd, tier: T0, attempt: 1, spec: GeneralizedShift.lean)
@[simp]
theorem cantorCylinderRatBox_snd (B : ℕ) (negDigits posDigits : List ℕ) :
    (cantorCylinderRatBox B negDigits posDigits).2 = cantorIntervalRatPair B posDigits :=
  by
  simp [cantorCylinderRatBox]
