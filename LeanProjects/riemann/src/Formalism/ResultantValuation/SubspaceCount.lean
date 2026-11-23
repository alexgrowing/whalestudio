import Formalism.ResultantValuation.KoszulSecondDifferential

noncomputable section

namespace Formalism.ResultantValuation

def SubspaceCount : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (j : ℕ),
    (Nat.card {W : Submodule F V // Module.finrank F W = j} : ℤ) *
        ∏ i ∈ Finset.range j, ((Fintype.card F : ℤ) ^ j - (Fintype.card F : ℤ) ^ i) =
      ∏ i ∈ Finset.range j,
        ((Fintype.card F : ℤ) ^ Module.finrank F V - (Fintype.card F : ℤ) ^ i)

end Formalism.ResultantValuation
