import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShapeFinalOfShapeChange
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shape_final_of_shape_change : ∀ (D : D7) (Y : ShimX D.what₂.Tau), ∀ (Φ : ℝ → Fn Y) (hh : Fn Y), ShapeC Φ hh → ShapeF Φ hh := by
  first | exact @GlobalTheory.Mean4.shapeF_of_shapeC | exact GlobalTheory.Mean4.shapeF_of_shapeC | (intros; apply GlobalTheory.Mean4.shapeF_of_shapeC <;> assumption)
