import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.HeckeValueEstimateOfRecordValue

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

def CountLoc : Prop :=
  ∀ (p n' : ℕ) (W Qq : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq],
    IsFractionRing W Qq → Irreducible (p : W) → Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n' →
    ∀ (N N' g i : ℕ), N' = N + g → ∀ (A : Submodule W (Fin N → Qq)) (B : Submodule W (Fin N' → Qq)),
      IsLattice W A → IsLattice W B → ∀ x : Matrix (Fin N') (Fin N) Qq,
      Nat.card {B1 : Submodule W (Fin N' → Qq) // IsEdge p n' i ⟨B1, B⟩ ∧ ∀ y ∈ A, x.mulVec y ∈ B1} =
        ∑ l ∈ range (i + 1), (p ^ n') ^ ((i - l) * (g - l)) * Formalism.G0.gaussBinom (p ^ n') g l *
          Nat.card {A1 : Submodule W (Fin N → Qq) // IsEdge p n' (i - l) ⟨A, A1⟩ ∧ ∀ y ∈ A1, x.mulVec y ∈ B}

end Formalism.MainNotions.FormalGroupSystem.Pf
