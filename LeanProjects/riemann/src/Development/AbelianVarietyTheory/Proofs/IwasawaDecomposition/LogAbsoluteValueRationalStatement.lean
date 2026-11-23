import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogAbsoluteValueRational
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_absolute_value_rational : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (α : AlgebraicClosure F), α ≠ 0 → ∃ (m : ℕ) (z : ℤ), 0 < m ∧ (m : ℝ) * Real.log (e.w α) = (z : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
  first | exact @GlobalTheory.ExtValueGroup.log_w_rat | exact GlobalTheory.ExtValueGroup.log_w_rat | (intros; apply GlobalTheory.ExtValueGroup.log_w_rat <;> assumption)
