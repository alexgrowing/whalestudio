import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanGeTransferDictionary
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mean_ge_transfer_dictionary : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (c' : Coeff Y.d.l₂), Y.d.c₂.F ≤ c'.F → ∀ (U' : GlobalTheory.ShFam.UnfFam Y.d.Xo₂ c' D.R.r (-D.host.xi0)) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (B X : ℝ), (∀ τ, StrictAnti (u τ)) → MeanGe (fun σ => GlobalTheory.ThetaDictCompare.toU (U'.U σ)) (xiR D) u B X → MeanGe Y.U (xiR D) u B X := by
  first | exact @GlobalTheory.SlopeDesc.meanGe_descent | exact GlobalTheory.SlopeDesc.meanGe_descent | (intros; apply GlobalTheory.SlopeDesc.meanGe_descent <;> assumption)
