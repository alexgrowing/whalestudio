import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicEmbeddingsSameNormConjugate
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_embeddings_same_norm_conjugate : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (ι ι' : AlgebraicClosure F →+* ℂ_[p]), (∀ a, ‖ι a‖ = ‖ι' a‖) → ∃ σ : ℂ_[p] ≃+* ℂ_[p], (∀ z, ‖σ z‖ = ‖z‖) ∧ ∀ a, σ (ι' a) = ι a := by
  first | exact @GlobalTheory.CpAlgEmb.exists_isometric_ringEquiv | exact GlobalTheory.CpAlgEmb.exists_isometric_ringEquiv | (intros; apply GlobalTheory.CpAlgEmb.exists_isometric_ringEquiv <;> assumption)
