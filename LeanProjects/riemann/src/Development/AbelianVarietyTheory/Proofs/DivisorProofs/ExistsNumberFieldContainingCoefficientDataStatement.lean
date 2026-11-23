import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumberFieldContainingCoefficientData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_numberField_containing_coefficientData : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (B : Base D cc dl) (cD : D.what₂.Tau → ℂ) (K : Type) [Field K] [NumberField K] (σ₀ : K →+* ℂ) (R : Ranks), StandardLatticesGL3.Crv D cc dl → IsDgen D cD → (∀ i < R.m, ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ TaylorLogMetric.CoefIn D (B.thZero (R.N i) (R.N (i + 1))) M) → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ThetaFieldData B cD σ₀ R M := by
  first | exact @GlobalTheory.ColNorms.ExField.exists_field_holdsData | exact GlobalTheory.ColNorms.ExField.exists_field_holdsData | (intros; apply GlobalTheory.ColNorms.ExField.exists_field_holdsData <;> assumption)
