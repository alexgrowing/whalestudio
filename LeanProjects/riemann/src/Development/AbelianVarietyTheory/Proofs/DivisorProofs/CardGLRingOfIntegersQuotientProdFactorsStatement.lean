import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardGLRingOfIntegersQuotientProdFactors
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowBlockIndicatorFromLtIff
open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_GL_ringOfIntegers_quotient_prod_factors : ∀ (E : Type) [Field E] [NumberField E] (𝔪 : Ideal (𝓞 E)), 𝔪 ≠ ⊥ → ∀ n : ℕ,
    (Nat.card (GL (Fin n) (𝓞 E ⧸ 𝔪)) : ℝ) = ∏ w ∈ (normalizedFactors 𝔪).toFinset,
      (Ideal.absNorm w : ℝ) ^ ((normalizedFactors 𝔪).count w * n ^ 2) * glVol (Ideal.absNorm w : ℝ) n := by
  first | exact @GlobalTheory.CardGLQuot.card_GL_quot_prod | exact GlobalTheory.CardGLQuot.card_GL_quot_prod | (intros; apply GlobalTheory.CardGLQuot.card_GL_quot_prod <;> assumption)
