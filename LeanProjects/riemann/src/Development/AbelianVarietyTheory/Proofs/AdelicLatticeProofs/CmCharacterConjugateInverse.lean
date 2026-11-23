import Mathlib
import Formalism.UnipotentAdelicQuotients.ThmBInHecke
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeAlgebraMapOfConjFixed

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory

theorem ideleChar_conj_eq_inv_of_trivial_on_base :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ χ : (AE F E)ˣ →* Circle, (∀ a : (AF F)ˣ, χ (idF F E a) = 1) → ∀ x y : (AE F E)ˣ, (y : AE F E) = cA σ x → χ y = (χ x)⁻¹ := by
  intro F E _ _ _ _ _ σ h χ hχ x y hy
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨n, hn⟩ := exists_unit_mul_conj_eq_algebraMap F E σ h1 h2 h3 h4 (AF F) x
  have hxy : x * y = idF F E n := by
    apply Units.ext
    rw [Units.val_mul, hy]
    exact hn
  have h5 : χ x * χ y = 1 := by rw [← map_mul, hxy, hχ]
  exact eq_inv_of_mul_eq_one_right h5

end GlobalTheory
