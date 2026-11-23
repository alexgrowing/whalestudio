import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SaturatedOrdinaryIdealCutsOutCrystallineLocus
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.saturatedOrdinaryIdeal_cuts_out_crystalline_locus : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ), GlobalTheory.OrdLoc.PtsCr D U (GlobalTheory.OrdLoc.IY D U) ∧ GlobalTheory.OrdLoc.CrPts D U (GlobalTheory.OrdLoc.IY D U) := by
  first | exact @GlobalTheory.OrdLoc.ideal_cuts_crystalline_locus | exact GlobalTheory.OrdLoc.ideal_cuts_crystalline_locus | (intros; apply GlobalTheory.OrdLoc.ideal_cuts_crystalline_locus <;> assumption)
