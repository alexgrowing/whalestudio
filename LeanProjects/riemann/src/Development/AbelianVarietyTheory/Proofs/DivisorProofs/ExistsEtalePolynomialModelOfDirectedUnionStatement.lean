import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtalePolynomialModelOfDirectedUnion
import Mathlib
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etale_polynomial_descent_of_directed_union : ∀ (T : Type) [CommRing T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (𝒜 : ι → Subring T), Monotone 𝒜 → (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E] [Algebra.Etale (Polynomial T) E],
    ∃ (i : ι) (E₀ : Type) (_ : CommRing E₀) (_ : Algebra (Polynomial (𝒜 i)) E₀),
      Algebra.Etale (Polynomial (𝒜 i)) E₀ ∧
      letI : Algebra (Polynomial (𝒜 i)) (Polynomial T) := (Polynomial.mapRingHom (𝒜 i).subtype).toAlgebra
      Nonempty (TensorProduct (Polynomial (𝒜 i)) (Polynomial T) E₀ ≃ₐ[Polynomial T] E) := by
  first | (exact @GlobalTheory.EtaleDescent.exists_etale_polynomial_model_of_directed_union) | (exact GlobalTheory.EtaleDescent.exists_etale_polynomial_model_of_directed_union) | (intros; apply GlobalTheory.EtaleDescent.exists_etale_polynomial_model_of_directed_union  <;> assumption)
