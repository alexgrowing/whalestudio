import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqualVolumeAndSlopeMean
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equal_volume_and_slope_mean : ∀ (D : D7) (Y : ShimX D.what₂.Tau), ∀ (A : SlopeTestRemainingChoices Y), ∀ (Φ : ℝ → Fn Y) (C : ℝ), 2 < D.R.f * (Y.N - 1) → LimFam Φ → PolySize A Φ → Agree A → Degrees A → EqVol A → Propor Y → Lower Φ C → GlobalTheory.IndefiniteRowSideFullHecke.ComponentMean.VolEq Y ∧ GlobalTheory.IndefiniteRowSideFullHecke.ComponentMean.SlopeMean Y C := by
  first | exact @GlobalTheory.Mean4.volEq_and_slopeMean | exact GlobalTheory.Mean4.volEq_and_slopeMean | (intros; apply GlobalTheory.Mean4.volEq_and_slopeMean <;> assumption)
