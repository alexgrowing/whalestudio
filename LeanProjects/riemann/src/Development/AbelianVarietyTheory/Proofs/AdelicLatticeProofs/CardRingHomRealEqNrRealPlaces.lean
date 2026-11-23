import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem card_ringHom_real_eq_nrRealPlaces :
    ∀ (F : Type) [Field F] [NumberField F], Nat.card (F →+* ℝ) = InfinitePlace.nrRealPlaces F := by
  intro F _ _
  let e : (F →+* ℝ) ≃ {φ : F →+* ℂ // ComplexEmbedding.IsReal φ} :=
    { toFun := fun ψ => ⟨Complex.ofRealHom.comp ψ, by
        rw [ComplexEmbedding.isReal_iff]
        ext x
        simp [ComplexEmbedding.conjugate_coe_eq]⟩
      invFun := fun φ => φ.2.embedding
      left_inv := fun ψ => by
        ext x
        simp [ComplexEmbedding.IsReal.embedding]
      right_inv := fun φ => by
        apply Subtype.ext
        ext x
        simp }
  classical
  rw [Nat.card_congr (e.trans InfinitePlace.mkReal), Nat.card_eq_fintype_card]

end GlobalTheory.QNorm
