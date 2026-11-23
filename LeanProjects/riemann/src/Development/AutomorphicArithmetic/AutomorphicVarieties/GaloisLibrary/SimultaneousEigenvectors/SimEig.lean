import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SimultaneousEigenvectors

theorem UpperTheory.V.LinAlg.simEig :
    ∀ {K M : Type} [Field K] [IsAlgClosed K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
        {J : Type} (T : J → Module.End K M), (∀ i j : J, T i * T j = T j * T i) →
        ∀ (d : ℕ) (U : Submodule K M), Module.finrank K U = d → U ≠ ⊥ → (∀ j : J, ∀ x ∈ U, T j x ∈ U) →
        ∃ v ∈ U, v ≠ 0 ∧ ∀ j : J, ∃ c : K, T j v = c • v :=
  _root_.UpperTheory.Reformulated.B.SimultaneousEigenvectorInvariantSubspace.simEig
