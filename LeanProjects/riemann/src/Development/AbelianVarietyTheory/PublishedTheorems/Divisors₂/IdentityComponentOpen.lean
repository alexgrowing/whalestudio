import Mathlib

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.Published

def IdentityComponentOpen : Prop :=
  ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom →
    ∃ (G₀ : Over S) (_ : GrpObj G₀) (j : G₀ ⟶ G), IsMonHom j ∧ IsOpenImmersion j.left ∧
      ∀ x : G.left, x ∈ Set.range j.left ↔
        x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))

end GlobalTheory.Published
