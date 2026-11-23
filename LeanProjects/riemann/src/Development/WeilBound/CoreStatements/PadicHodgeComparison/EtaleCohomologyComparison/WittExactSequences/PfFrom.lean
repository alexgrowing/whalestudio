import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ToPfFull

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

namespace CrystallineSemistableComparison.D

abbrev pfOb {R : Type} [CommRing R] {p : ℕ} (X : Type) [CommRing X] [Algebra R X] (h : Pf p X) : PfC p R :=
  ⟨CommAlgCat.of R X, h⟩

abbrev pfHom {R : Type} [CommRing R] {p : ℕ} {X Y : Type} [CommRing X] [Algebra R X] [CommRing Y] [Algebra R Y]
    {hX : Pf p X} {hY : Pf p Y} (φ : X →ₐ[R] Y) : pfOb (R := R) X hX ⟶ pfOb (R := R) Y hY :=
  ObjectProperty.homMk (CommAlgCat.ofHom φ)

abbrev pfFrom {R : Type} [CommRing R] {p : ℕ} (A : PfC p R) (B : Type) [CommRing B] [Algebra R B] [Algebra A.obj B]
    [IsScalarTower R A.obj B] (hB : Pf p B) : A ⟶ pfOb (R := R) B hB :=
  ObjectProperty.homMk (CommAlgCat.ofHom (IsScalarTower.toAlgHom R A.obj B))

end CrystallineSemistableComparison.D
