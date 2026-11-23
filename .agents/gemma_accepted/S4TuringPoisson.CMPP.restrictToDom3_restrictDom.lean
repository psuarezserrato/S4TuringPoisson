-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.restrictToDom3_restrictDom, tier: T0, attempt: 2, spec: Realize.lean)
@[simp]
theorem restrictToDom3_restrictDom {A : Type*} {D : Finset ℤ} (hD : D = shiftDom3)
    (s : ℤ → A) :
    restrictToDom3 hD (restrictDom D s) = restrictDom shiftDom3 s :=
  by
  subst hD
  ext i
  simp [restrictToDom3, restrictDom]
