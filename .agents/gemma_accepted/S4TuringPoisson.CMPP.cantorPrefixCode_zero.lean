-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.cantorPrefixCode_zero, tier: T0, attempt: 1, spec: Digits.lean)
@[simp]
theorem cantorPrefixCode_zero (B : ℕ) (p : Fin 0 → ℕ) :
    cantorPrefixCode B p = 0 :=
  by
  simp [cantorPrefixCode]
