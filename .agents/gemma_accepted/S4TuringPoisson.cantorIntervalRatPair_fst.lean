-- Verified by gemma_loop.py (declaration: S4TuringPoisson.cantorIntervalRatPair_fst, tier: T0, attempt: 2, spec: GeneralizedShift.lean)
@[simp]
theorem cantorIntervalRatPair_fst (B : ℕ) (digits : List ℕ) :
    (cantorIntervalRatPair B digits).1 = cantorIntervalLeftRatFrac B digits :=
  by
  rfl
