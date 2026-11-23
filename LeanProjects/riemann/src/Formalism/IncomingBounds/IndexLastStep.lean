import Formalism.LogFactorialIndices.StatementIdx

noncomputable section

namespace Formalism.IncomingBounds

open Module

def IndexLastStep : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [FiniteDimensional K X] (ϖ : O), Irreducible ϖ →
    ∀ (e : ℤ) (M Θ : Submodule O X), Formalism.LatticeIndexTer.IsLat O K X M → Formalism.LatticeIndexTer.IsLat O K X Θ →
      ∀ W : Submodule K X,
        Formalism.LatticeIndexTer.idx O X (M ⊓ W.restrictScalars O) (Θ ⊓ W.restrictScalars O) ≤
          e * (finrank K W : ℤ) +
            ((Formalism.LatticeIndexTer.qlen O X
              (M.map ((((algebraMap O K ϖ) ^ e) • LinearMap.id : X →ₗ[K] X).restrictScalars O) ⊔ Θ)
              Θ).toNat : ℤ)

end Formalism.IncomingBounds
