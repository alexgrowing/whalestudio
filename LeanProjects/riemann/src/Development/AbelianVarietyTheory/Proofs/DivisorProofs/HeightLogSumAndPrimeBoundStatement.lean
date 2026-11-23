import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightLogSumAndPrimeBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_log_sum_and_prime_bound : ∀ (D : D7) (A : Amb D) (κ : Lv A) (B : ℝ), (Function.support (htLog κ B)).Finite ∧ ∑ᶠ v, htLog κ B v = (Module.finrank ℚ D.what₂.LL : ℝ) * htCost κ.l B ∧ ∀ v, 0 ≤ htLog κ B v ∧ ∀ p ∈ htPrimes κ.l B, -Real.log (NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v (p : D.what₂.LL)) * htEx D.host.E p ≤ htLog κ B v := by
  first | exact @GlobalTheory.CovHt.Link.htLog_sum | exact GlobalTheory.CovHt.Link.htLog_sum | (intros; apply GlobalTheory.CovHt.Link.htLog_sum <;> assumption)
