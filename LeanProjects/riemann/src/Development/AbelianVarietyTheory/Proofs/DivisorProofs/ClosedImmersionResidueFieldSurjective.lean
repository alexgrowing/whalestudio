import Mathlib
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory

theorem residueFieldMap_surjective_of_isClosedImmersion
    (X Y : AlgebraicGeometry.Scheme.{0}) (i : X ⟶ Y) [AlgebraicGeometry.IsClosedImmersion i]
    (x : X) : Function.Surjective (i.residueFieldMap x).hom := by
  have h1 : Function.Surjective (i.stalkMap x).hom := i.stalkMap_surjective x
  have h2 : Function.Surjective (X.residue x).hom := X.residue_surjective x
  have h3 : Function.Surjective (Y.residue (i x) ≫ i.residueFieldMap x).hom := by
    rw [Scheme.residue_residueFieldMap]
    exact h2.comp h1
  exact Function.Surjective.of_comp (g := (Y.residue (i x)).hom) h3

end GlobalTheory
