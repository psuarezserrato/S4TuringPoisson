-- Verified by gemma_loop.py (declaration: S4TuringPoisson.poissonHamiltonianTimeOneDiffeomorph_apply, tier: T0, attempt: 4, spec: PoissonHamiltonian.lean)
@[simp]
theorem poissonHamiltonianTimeOneDiffeomorph_apply
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
    [A : AdmitsWrinkledOrBrokenLefschetzFibration M]
    (H : C^∞⟮𝓡 4, M; ℝ⟯) (x : M) :
    poissonHamiltonianTimeOneDiffeomorph M H x =
      TauCeti.timeDependentFlowOf
        (fun _ : ℝ ↦ (adaptedJacobianPoisson M).hamiltonianVectorField H) 0 1 x :=
  by
  simp [poissonHamiltonianTimeOneDiffeomorph]
