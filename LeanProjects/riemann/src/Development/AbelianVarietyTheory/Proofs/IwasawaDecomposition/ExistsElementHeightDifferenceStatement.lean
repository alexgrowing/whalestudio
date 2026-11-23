import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsElementHeightDifference
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_element_height_difference : ∀ (F : Type) [Field F] [NumberField F] (c : HeightOneSpectrum (𝓞 F) → ℝ), (Function.support c).Finite → (∀ v, ∃ (m : ℕ) (z : ℤ), 0 < m ∧ (m : ℝ) * c v = (z : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ)) → ∃ (h : ℕ+) (b b' : 𝓞 F), b ≠ 0 ∧ b' ≠ 0 ∧ ∀ v, ((h : ℕ) : ℝ) * c v = Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F b)) - Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F b')) := by
  first | exact @GlobalTheory.exists_mul_eq_log_adicAbv_sub | exact GlobalTheory.exists_mul_eq_log_adicAbv_sub | (intros; apply GlobalTheory.exists_mul_eq_log_adicAbv_sub <;> assumption)
