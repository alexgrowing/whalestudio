import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShapeChangeOfRelabelling
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shape_change_of_relabelling : ∀ (D : D7) (Y : ShimX D.what₂.Tau), ∀ (Φ : ℝ → Fn Y) (hh : Fn Y), 0 < Y.vol → Relabel Φ → FlagHt D.what₂.Tau Y.N hh → ShapeT Φ hh → ShapeC Φ hh := by
  first | exact @GlobalTheory.Mean4.EqualCoeff.shapeC_of_shapeT | exact GlobalTheory.Mean4.EqualCoeff.shapeC_of_shapeT | (intros; apply GlobalTheory.Mean4.EqualCoeff.shapeC_of_shapeT <;> assumption)
