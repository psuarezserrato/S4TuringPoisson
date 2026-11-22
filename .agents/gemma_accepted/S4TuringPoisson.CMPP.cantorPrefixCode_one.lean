-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.cantorPrefixCode_one, tier: T0, attempt: 1, spec: Digits.lean)
@[simp]
theorem cantorPrefixCode_one (B : ℕ) (p : Fin 1 → ℕ) :
    cantorPrefixCode B p = 2 * p 0 :=
  by
  simp [cantorPrefixCode]
