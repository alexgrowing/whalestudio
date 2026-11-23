import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IndexFormulaNormsInvolution
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.index_formula_norms_involution : ∀ (A : Type) [CommGroup A] (σ : A →* A) (ε : A), (∀ a, σ (σ a) = a) → (∀ a, a * σ a = 1 → ∃ b, a = b / σ b) → ε ≠ 1 → ε ^ 2 = 1 → σ ε = ε → (∀ a : A, a ^ 2 = 1 → a = 1 ∨ a = ε) → 2 * (sqs (⊤ : Subgroup A)).index * (MonoidHom.id A * σ).range.relIndex (σ.eqLocus (MonoidHom.id A)) = (sqs (σ.eqLocus (MonoidHom.id A))).relIndex (σ.eqLocus (MonoidHom.id A)) ^ 2 := by
  first | exact @GlobalTheory.QNorm.two_mul_index_sqs_mul_relIndex_norm_involution | exact GlobalTheory.QNorm.two_mul_index_sqs_mul_relIndex_norm_involution | (intros; apply GlobalTheory.QNorm.two_mul_index_sqs_mul_relIndex_norm_involution <;> assumption)
