import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.DensExact

namespace PI.DensSplitW

def FiberCard : Prop :=
  ∀ (K V U : Type) [Field K] [Fintype K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup U] [Module K U] (φ : V →ₗ[K] U), Function.Surjective φ →
    ∀ (k : ℕ) (g : Fin k → U),
      Nat.card {z : Fin k → V // LinearIndependent K z ∧ ∀ j, φ (z j) = g j} =
        Fintype.card K ^ (Module.finrank K (Submodule.span K (Set.range g)) *
            Module.finrank K (LinearMap.ker φ)) *
          ∏ i ∈ Finset.range (k - Module.finrank K (Submodule.span K (Set.range g))),
            (Fintype.card K ^ Module.finrank K (LinearMap.ker φ) - Fintype.card K ^ i)

end PI.DensSplitW
