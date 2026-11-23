import Mathlib

open CategoryTheory

namespace PI.CharIdem

variable {G : Type} [Group G] [Fintype G]

noncomputable def charIdem (V : FDRep ℂ G) : MonoidAlgebra ℂ G :=
  ∑ g : G, MonoidAlgebra.single g (((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ)) * V.character g⁻¹)

noncomputable def act (V : FDRep ℂ G) : MonoidAlgebra ℂ G →ₐ[ℂ] Module.End ℂ V :=
  MonoidAlgebra.lift ℂ (Module.End ℂ V) G V.ρ

def CharIdem : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (V W : FDRep ℂ G), Simple V → Simple W →
    act V (charIdem V) = 1 ∧
    (IsEmpty (V ≅ W) → act W (charIdem V) = 0) ∧
    IsIdempotentElem (charIdem V) ∧
    (∀ x : MonoidAlgebra ℂ G, charIdem V * x = x * charIdem V) ∧
    (IsEmpty (V ≅ W) → charIdem V * charIdem W = 0)

end PI.CharIdem
