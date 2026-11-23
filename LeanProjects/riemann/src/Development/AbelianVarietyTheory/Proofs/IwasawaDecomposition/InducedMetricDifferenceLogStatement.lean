import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricDifferenceLog
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_metric_difference_log : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L L' : HermLB M.p) (k : ℕ+) (cf cf' : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced M L k cf → A.Induced M L' k cf' → ∀ v : HeightOneSpectrum (𝓞 F), ∃ (e : Ext v) (α : AlgebraicClosure F), α ≠ 0 ∧ ((k : ℕ) : ℝ) * (A.n : ℕ) * (cf' v - cf v) = Real.log (e.w α) := by
  first | exact @GlobalTheory.TrueGeo.ValGroup.main | exact GlobalTheory.TrueGeo.ValGroup.main | (intros; apply GlobalTheory.TrueGeo.ValGroup.main <;> assumption)
