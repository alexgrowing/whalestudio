import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoMulCardInfinitePlaceLeQuadratic
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_mul_card_infinitePlace_le_quadratic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → 2 * Fintype.card (InfinitePlace F) ≤ Fintype.card (InfinitePlace E) + tReal F δ := by
  first | exact @GlobalTheory.QNorm.two_mul_card_infinitePlace_le | exact GlobalTheory.QNorm.two_mul_card_infinitePlace_le | (intros; apply GlobalTheory.QNorm.two_mul_card_infinitePlace_le <;> assumption)
