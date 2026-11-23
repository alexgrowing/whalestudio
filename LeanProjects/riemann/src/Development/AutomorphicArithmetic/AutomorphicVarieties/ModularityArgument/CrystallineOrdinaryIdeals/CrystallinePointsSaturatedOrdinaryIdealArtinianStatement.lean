import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CrystallinePointsSaturatedOrdinaryIdealArtinian
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallinePoints_saturatedOrdinaryIdeal_artinian : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ), GlobalTheory.OrdLoc.CrPts D U (GlobalTheory.OrdLoc.IY D U) := by
  first | exact @GlobalTheory.OrdLoc.crPts_IY | exact GlobalTheory.OrdLoc.crPts_IY | (intros; apply GlobalTheory.OrdLoc.crPts_IY <;> assumption)
