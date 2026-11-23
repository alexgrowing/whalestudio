import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeEqualitySlopeMean
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_equality_slope_mean : ∀ r Cf : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (Y : DV.ShimX D.what₂.Tau), 2 < D.R.f * (Y.N - 1) → DeRhamMinusHodgeTateGoodPrimesAt Y → DeRhamHodgeTateDifferenceKilledAt Y → Propor Y → FewBad Y → ∀ (A : SlopeTestRemainingChoices Y) (Φ : ℝ → Fn Y) (hh : Fn Y), Inputs A Φ hh r Cf → GlobalTheory.IndefiniteRowSideFullHecke.ComponentMean.VolEq Y ∧ GlobalTheory.IndefiniteRowSideFullHecke.ComponentMean.SlopeMean Y C := by
  first | exact @GlobalTheory.MeanOne.slopeMean_at | exact GlobalTheory.MeanOne.slopeMean_at | (intros; apply GlobalTheory.MeanOne.slopeMean_at <;> assumption)
