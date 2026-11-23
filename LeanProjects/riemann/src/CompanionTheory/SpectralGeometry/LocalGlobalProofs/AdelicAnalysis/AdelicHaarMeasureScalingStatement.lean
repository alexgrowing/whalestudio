import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureScaling
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_haar_measure_scaling : ∀ (F : Type) [Field F] [NumberField F], ∀ [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → (∀ (c : F), c ≠ 0 → ∀ s : Set (A F), MeasurableSet s → lf ((fun x => algebraMap F (A F) c * x) '' s) = ENNReal.ofReal (|((Algebra.norm ℚ c : ℚ) : ℝ)|⁻¹) * lf s) ∧ (∀ b : F, lf {x | x ∈ Oh F ∧ algebraMap F (A F) b * x ∈ Oh F} = ((den b : ℝ≥0∞))⁻¹) ∧ ∀ (a : (A F)ˣ) (s : Set (A F)), MeasurableSet s → lf ((fun x => (a : A F) * x) '' s) = lf ((fun x => (a : A F) * x) '' Oh F) * lf s := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.Scale.lf_scale | exact GlobalTheory.CompanionTheory.SW.Core.Scale.lf_scale | (intros; apply GlobalTheory.CompanionTheory.SW.Core.Scale.lf_scale <;> assumption)
