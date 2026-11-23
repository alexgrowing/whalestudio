import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportProductQuotient
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_support_product_quotient : ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (f₁ : G₁ → ℂ) (f₂ : G₂ → ℂ), (Function.support fun q : G₁ ⧸ K₁ => f₁ q.out).Finite → (Function.support fun q : G₂ ⧸ K₂ => f₂ q.out).Finite → (∀ k ∈ K₁, ∀ g, f₁ (g * k) = f₁ g) → (∀ k ∈ K₂, ∀ g, f₂ (g * k) = f₂ g) → (Function.support fun q : (G₁ × G₂) ⧸ K₁.prod K₂ => f₁ q.out.1 * f₂ q.out.2).Finite := by
  first | exact @GlobalTheory.CompanionTheory.ProdQuotient.support_mul_out_finite | exact GlobalTheory.CompanionTheory.ProdQuotient.support_mul_out_finite | (intros; apply GlobalTheory.CompanionTheory.ProdQuotient.support_mul_out_finite <;> assumption)
