import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarScalingByRealIdele
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_haar_scaling_by_real_idele : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ → ∀ [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] (ι : Type) [Fintype ι] (μ : Measure (ι → AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] (t : ℝ), 0 < t → μ.map (fun x i => (show AdeleRing (𝓞 F) F from (θ t, 1)) * x i) = ENNReal.ofReal ((t ^ (Module.finrank ℚ F * Fintype.card ι))⁻¹) • μ := by
  first | exact @GlobalTheory.CompanionTheory.AdelicFlow.map_scalar | exact GlobalTheory.CompanionTheory.AdelicFlow.map_scalar | (intros; apply GlobalTheory.CompanionTheory.AdelicFlow.map_scalar <;> assumption)
