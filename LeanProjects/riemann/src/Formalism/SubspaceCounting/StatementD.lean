import Formalism.SubspaceCounting.Statement

noncomputable section

namespace Formalism.G0

def AllButLESmith : Prop := by
  classical
  exact
  ∀ {O M ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup M] [Module O M] [Fintype ι] (π : O), Irreducible π →
    ∀ (P : Submodule O M) (n : ℕ) (snf : Module.Basis.SmithNormalForm P ι n) (g E : ℕ),
    AllButLE π ⊤ P g E ↔
      ((Finset.univ.filter fun i : Fin n => ¬ snf.a i ∣ π ^ E).card + (Fintype.card ι - n) ≤ g)

end Formalism.G0
