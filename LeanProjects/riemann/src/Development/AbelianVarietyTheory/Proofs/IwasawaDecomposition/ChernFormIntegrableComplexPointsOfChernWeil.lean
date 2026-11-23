import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PolyRep
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.GoodTopChernForm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ChernWeilNumbers
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AntisymmFibrePointThree
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.GoodMetric

theorem hasChernIntegral_top_of_chernWeil : GlobalTheory.Published.ChernWeilNumbers → ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricOn E ⊤ H → ∀ R : MvPolynomial (ι × ℕ) ℝ, ∃ t : ℝ, HasChernIntegral E ⊤ H R t := by
  intro h F _ σ X ι _ m E H hH R
  obtain ⟨Y, E', φ, f, gr, -, hR, hg⟩ := Model.exists_flagSpace X E
  exact ⟨_, h F σ X Y ι m E E' φ f gr hR hg H hH R⟩

end GlobalTheory.GoodMetric
