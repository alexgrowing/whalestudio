import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernDvdOfDifferencesDvd
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagRelativeTangentTopChern_dvd_of_differences_dvd : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (P : MvPolynomial (Root m) ℝ), (∀ (τ : ι) (i j : Fin (m τ)), i < j → (X ⟨τ, j⟩ - X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ) ∣ P) → rootDiscr m ∣ P := by
  first | exact @GlobalTheory.GoodMetric.DiscrDvd.rootDiscr_dvd | exact GlobalTheory.GoodMetric.DiscrDvd.rootDiscr_dvd | (intros; apply GlobalTheory.GoodMetric.DiscrDvd.rootDiscr_dvd <;> assumption)
