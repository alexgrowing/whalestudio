import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RelIndexNormMulRelIndexSqsKer
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_norm_mul_relIndex_sqs_ker' : ∀ (A : Type) [CommGroup A] (σ : A →* A), (∀ a, σ (σ a) = a) → (∀ a, a * σ a = 1 → ∃ b, a = b / σ b) → (MonoidHom.id A * σ).range.relIndex (σ.eqLocus (MonoidHom.id A)) * (sqs (MonoidHom.id A * σ).ker).relIndex (MonoidHom.id A * σ).ker = (sqs (σ.eqLocus (MonoidHom.id A))).relIndex (σ.eqLocus (MonoidHom.id A)) := by
  first | exact @GlobalTheory.QNorm.relIndex_norm_mul_relIndex_sqs_ker | exact GlobalTheory.QNorm.relIndex_norm_mul_relIndex_sqs_ker | (intros; apply GlobalTheory.QNorm.relIndex_norm_mul_relIndex_sqs_ker <;> assumption)
