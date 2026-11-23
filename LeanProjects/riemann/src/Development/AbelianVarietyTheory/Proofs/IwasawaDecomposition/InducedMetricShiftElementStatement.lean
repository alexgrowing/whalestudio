import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricShiftElement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_metric_shift_element : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ) (b : 𝓞 F), b ≠ 0 → ∀ ht : ∀ σ : 𝓞 F →+* ℂ, Real.log ‖((starRingEnd ℂ).comp σ) b‖ = Real.log ‖σ b‖, A.Induced M L k cf → A.Induced M (L.shift (fun σ => Real.log ‖σ b‖) ht) k (fun v => cf v + Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F b)) / (((k : ℕ) : ℝ) * (A.n : ℕ))) := by
  first | exact @GlobalTheory.TrueGeo.IndScale.induced_shift | exact GlobalTheory.TrueGeo.IndScale.induced_shift | (intros; apply GlobalTheory.TrueGeo.IndScale.induced_shift <;> assumption)
