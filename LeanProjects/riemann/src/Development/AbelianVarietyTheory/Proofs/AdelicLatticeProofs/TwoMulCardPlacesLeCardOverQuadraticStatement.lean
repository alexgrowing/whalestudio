import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoMulCardPlacesLeCardOverQuadratic
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_mul_card_places_le_card_over_quadratic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → 2 * S.card ≤ SE.card + tFin F δ S := by
  first | exact @GlobalTheory.QNorm.two_mul_card_le_card_over | exact GlobalTheory.QNorm.two_mul_card_le_card_over | (intros; apply GlobalTheory.QNorm.two_mul_card_le_card_over <;> assumption)
