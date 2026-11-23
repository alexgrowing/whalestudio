import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison.Pb

namespace CrystallineSemistableComparison.Om.Glob

abbrev FV {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (a : ℕ) :
    (KS q (a + 1) {V}).FullSubcategory ⥤ ModuleCat.{0} K :=
  (KS q (a + 1) {V}).ι ⋙ HT.grT (smFun X q) a

end CrystallineSemistableComparison.Om.Glob
