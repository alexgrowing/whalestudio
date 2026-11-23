import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableChernPolyTopDensity
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
open MvPolynomial GlobalTheory GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_chernPolyTopDensity : ∀ {n : ℕ} {ι : Type} {m : ι → ℕ} (R : MvPolynomial (ι × ℕ) ℝ) (G : V n → Mat m ℂ), Measurable (fun v => chernTop R G v) := by
  first | exact @GlobalTheory.ChernMeas.measurable_chernTop | exact GlobalTheory.ChernMeas.measurable_chernTop | (intros; apply GlobalTheory.ChernMeas.measurable_chernTop <;> assumption)
