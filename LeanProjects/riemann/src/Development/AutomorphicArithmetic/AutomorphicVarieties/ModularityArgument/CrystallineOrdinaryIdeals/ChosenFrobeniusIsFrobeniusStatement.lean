import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ChosenFrobeniusIsFrobenius
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chosenFrobenius_isFrobenius : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O), GlobalTheory.OrdLoc.IsFr D (GlobalTheory.OrdLoc.fr D) := by
  first | exact @GlobalTheory.OrdLoc.fr_isFr | exact GlobalTheory.OrdLoc.fr_isFr | (intros; apply GlobalTheory.OrdLoc.fr_isFr <;> assumption)
