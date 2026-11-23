import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_isKum : ∀ (p : ℕ) (F : Type) [Field F] [CharZero F] (ζ δ : F), p.Prime → IsPrimitiveRoot ζ p → (∀ r : F, r ^ p ≠ δ) → ∃ (E : Type) (_ : Field E) (_ : Algebra F E) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ := by
  intro p F _ _ ζ δ hp hζ hδ
  have : Fact (Irreducible (X ^ p - C δ)) := ⟨X_pow_sub_C_irreducible_of_prime hp hδ⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  refine ⟨AdjoinRoot (X ^ p - C δ), inferInstance, inferInstance, AdjoinRoot.root _,
    autAdjoinRootXPowSubC p δ hζ.toRootsOfUnity, ?_⟩
  refine ⟨hp, hζ, hδ, ?_, ?_, AdjoinRoot.adjoinRoot_eq_top⟩
  · have h := AdjoinRoot.eval₂_root (X ^ p - C δ)
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h
    rw [h, AdjoinRoot.algebraMap_eq]
  · rw [autAdjoinRootXPowSubC_root, Algebra.smul_def, IsPrimitiveRoot.val_toRootsOfUnity_coe]

end GlobalTheory.CNorm
