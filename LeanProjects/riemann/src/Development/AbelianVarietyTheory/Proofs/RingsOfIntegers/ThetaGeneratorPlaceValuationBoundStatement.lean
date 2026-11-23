import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ThetaGeneratorPlaceValuationBound
import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie GlobalTheory.PlaceTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGenerator_place_valuation_bound : ThBoundSt := by
  first | exact @GlobalTheory.ThetaBound.thBound | exact GlobalTheory.ThetaBound.thBound | (intros; apply GlobalTheory.ThetaBound.thBound <;> assumption)
