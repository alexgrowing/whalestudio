import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem tensor_exists_of_galois_fixed :
    ∀ (F M E K : Type) [Field F] [CharZero F] [Field M] [Field E] [Algebra F M] [Algebra M E] [Algebra F E] [IsScalarTower F M E] [FiniteDimensional M E] [IsGalois M E] [CommRing K] [Algebra F K] (y : K ⊗[F] E), (∀ h : E ≃ₐ[M] E, Algebra.TensorProduct.map (AlgHom.id K K) ((h.restrictScalars F : E ≃ₐ[F] E) : E →ₐ[F] E) y = y) → ∃ z : K ⊗[F] M, Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom F M E) z = y := by
  intro F M E K _ _ _ _ _ _ _ _ _ _ _ _ y hy
  classical
  have key : ∀ x : K ⊗[F] E, ∃ z : K ⊗[F] M,
      Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom F M E) z =
      ∑ h : E ≃ₐ[M] E, Algebra.TensorProduct.map (AlgHom.id K K)
        ((h.restrictScalars F : E ≃ₐ[F] E) : E →ₐ[F] E) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul k e =>
      refine ⟨k ⊗ₜ Algebra.trace M E e, ?_⟩
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rw [← TensorProduct.tmul_sum]
      congr 1
      exact trace_eq_sum_automorphisms e
    | add a b ha hb =>
      obtain ⟨za, ha⟩ := ha
      obtain ⟨zb, hb⟩ := hb
      refine ⟨za + zb, ?_⟩
      simp only [map_add, Finset.sum_add_distrib, ha, hb]
  obtain ⟨z, hz⟩ := key y
  simp only [hy, Finset.sum_const, Finset.card_univ] at hz
  have hm : ((Fintype.card (E ≃ₐ[M] E) : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨((Fintype.card (E ≃ₐ[M] E) : ℕ) : F)⁻¹ • z, ?_⟩
  rw [LinearMapClass.map_smul_of_tower, hz, ← Nat.cast_smul_eq_nsmul F, smul_smul,
    inv_mul_cancel₀ hm, one_smul]

end GlobalTheory.CNorm
