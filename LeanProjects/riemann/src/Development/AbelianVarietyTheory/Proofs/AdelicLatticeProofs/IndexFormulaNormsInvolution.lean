import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RelIndexNormMulRelIndexSqsKerStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoMulIndexSqsInvolutionStatement
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem two_mul_index_sqs_mul_relIndex_norm_involution :
    ∀ (A : Type) [CommGroup A] (σ : A →* A) (ε : A), (∀ a, σ (σ a) = a) → (∀ a, a * σ a = 1 → ∃ b, a = b / σ b) → ε ≠ 1 → ε ^ 2 = 1 → σ ε = ε → (∀ a : A, a ^ 2 = 1 → a = 1 ∨ a = ε) → 2 * (sqs (⊤ : Subgroup A)).index * (MonoidHom.id A * σ).range.relIndex (σ.eqLocus (MonoidHom.id A)) = (sqs (σ.eqLocus (MonoidHom.id A))).relIndex (σ.eqLocus (MonoidHom.id A)) ^ 2 := by
  intro A _ σ ε h1 h2 h3 h4 h5 h6
  have hn := GlobalTheory.T.relIndex_norm_mul_relIndex_sqs_ker' A σ h1 h2
  have hs := GlobalTheory.T.two_mul_index_sqs_eq_relIndex_fixed_mul_relIndex_ker A σ ε h1 h2 h3 h4 h5 h6
  rw [hs, sq, mul_assoc, mul_comm ((sqs (MonoidHom.id A * σ).ker).relIndex (MonoidHom.id A * σ).ker), hn]

end GlobalTheory.QNorm
