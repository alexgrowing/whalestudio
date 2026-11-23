import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PrimitiveVectorQuadraticLevelMeasure
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_vector_quadratic_level_measure : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → Valued.v (2 : Fv F v) = 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι (Fv F v)), B.IsSymm → (∀ i j, B i j ∈ v.adicCompletionIntegers F) → Valued.v B.det = 1 → ∀ x₀ : ι → Fv F v, (∀ i, x₀ i ∈ v.adicCompletionIntegers F) → (∃ i, Valued.v (x₀ i) = 1) → ∀ A : Set (Fv F v), MeasurableSet A → (Measure.pi fun _ : ι => lam) {x | (∀ i, Valued.v (x i - x₀ i) < 1) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} = (Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ ^ (Fintype.card ι - 1) * lam (A ∩ {s | Valued.v (s - (2 : Fv F v)⁻¹ * (x₀ ⬝ᵥ (B *ᵥ x₀))) < 1}) := by
  first | exact @GlobalTheory.CompanionTheory.SW.Hensel.measure_residue_class | exact GlobalTheory.CompanionTheory.SW.Hensel.measure_residue_class | (intros; apply GlobalTheory.CompanionTheory.SW.Hensel.measure_residue_class <;> assumption)
