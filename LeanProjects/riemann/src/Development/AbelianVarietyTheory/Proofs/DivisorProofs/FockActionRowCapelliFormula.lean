import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EabIsKCInr

open MvPolynomial Formalism.BasicNotions.TH

namespace GlobalTheory.LowIrr

theorem pderiv_neg_eq_zero {P Q R S : ℕ} (f : Pol P Q R S)
    (hf : ∀ l ∈ f.vars, linePos l = true) (l : Ln P Q R S) (hl : linePos l = false) :
    pderiv l f = 0 :=
  pderiv_eq_zero_of_notMem_vars fun h => by simp [hf l h] at hl

theorem fockAct2_posOnly (P Q R S : ℕ) (f : Pol P Q R S) (hf : ∀ l ∈ f.vars, linePos l = true) :
    (∀ c d : Fin R, fockAct2 P Q R S (Eab (.inl c) (.inl d)) f =
      GlobalTheory.Capelli.rowOp ℂ (zR P Q R S) c d f + (if c = d then (((P : ℂ) - Q) / 2) else 0) • f) ∧
    (∀ c d : Fin S, fockAct2 P Q R S (Eab (.inr c) (.inr d)) f =
      GlobalTheory.Capelli.rowOp ℂ (yS P Q R S) c d f + (if c = d then (((Q : ℂ) - P) / 2) else 0) • f) := by
  have h0 := pderiv_neg_eq_zero f hf
  constructor
  · intro c d
    rw [fockAct2_Eab, LinearMap.sum_apply, Fintype.sum_sum_type, GlobalTheory.Capelli.rowOp_apply,
      ← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
    simp only [zR, Equiv.symm_apply_apply,
      GlobalTheory.CompactHarm.omE_pp (Sum.inl _, Sum.inl _) (Sum.inl _, Sum.inl _) rfl rfl,
      GlobalTheory.CompactHarm.omE_nn (Sum.inr _, Sum.inl _) (Sum.inr _, Sum.inl _) rfl rfl,
      h0 (Sum.inr _, Sum.inl _) rfl, mul_zero, neg_zero, zero_sub, add_zero,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, Prod.mk.injEq, Sum.inl.injEq, true_and,
      Sum.inr.injEq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]
    split_ifs
    · module
    · simp
  · intro c d
    rw [fockAct2_Eab, LinearMap.sum_apply, Fintype.sum_sum_type, GlobalTheory.Capelli.rowOp_apply,
      ← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
    simp only [yS, Equiv.symm_apply_apply,
      GlobalTheory.CompactHarm.omE_pp (Sum.inr _, Sum.inr _) (Sum.inr _, Sum.inr _) rfl rfl,
      GlobalTheory.CompactHarm.omE_nn (Sum.inl _, Sum.inr _) (Sum.inl _, Sum.inr _) rfl rfl,
      h0 (Sum.inl _, Sum.inr _) rfl, mul_zero, neg_zero, zero_sub, zero_add,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, Prod.mk.injEq, Sum.inr.injEq, true_and,
      Sum.inl.injEq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]
    split_ifs
    · module
    · simp

end GlobalTheory.LowIrr
