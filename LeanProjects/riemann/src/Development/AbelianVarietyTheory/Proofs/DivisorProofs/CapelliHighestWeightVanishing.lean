import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EabIsKCInr

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CompactHarm

namespace GlobalTheory.MixedHW

variable {P Q R S : ℕ}

theorem fock_action_mixed_capelli_inl (a b : Fin P) (f : Pol P Q R S) :
    fockAct1 P Q R S (Eab (.inl a) (.inl b)) f =
      GlobalTheory.Capelli.mixedOp ℂ (GlobalTheory.LowIrr.zR P Q R S) (GlobalTheory.LowIrr.yS P Q R S)
        (finSumFinEquiv (.inl a)) (finSumFinEquiv (.inl b)) f +
      (if a = b then ((cPair R S : ℚ) : ℂ) else 0) • f := by
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type, GlobalTheory.Capelli.mixedOp_apply]
  simp only [omE_pp (Sum.inl _, Sum.inl _) (Sum.inl _, Sum.inl _) rfl rfl,
    omE_nn (Sum.inl _, Sum.inr _) (Sum.inl _, Sum.inr _) rfl rfl, GlobalTheory.LowIrr.zR, GlobalTheory.LowIrr.yS,
    Equiv.symm_apply_apply,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Prod.mk.injEq, Sum.inl.injEq, and_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    cPair, ← Nat.cast_smul_eq_nsmul ℂ]
  split_ifs
  · push_cast; module
  · simp [sub_eq_add_neg]

theorem fock_action_mixed_capelli_inr (a b : Fin Q) (f : Pol P Q R S) :
    fockAct1 P Q R S (Eab (.inr a) (.inr b)) f =
      -GlobalTheory.Capelli.mixedOp ℂ (GlobalTheory.LowIrr.zR P Q R S) (GlobalTheory.LowIrr.yS P Q R S)
        (finSumFinEquiv (.inr b)) (finSumFinEquiv (.inr a)) f -
      (if a = b then ((cPair R S : ℚ) : ℂ) else 0) • f := by
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type, GlobalTheory.Capelli.mixedOp_apply]
  simp only [omE_nn (Sum.inr _, Sum.inl _) (Sum.inr _, Sum.inl _) rfl rfl,
    omE_pp (Sum.inr _, Sum.inr _) (Sum.inr _, Sum.inr _) rfl rfl, GlobalTheory.LowIrr.zR, GlobalTheory.LowIrr.yS,
    Equiv.symm_apply_apply,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Prod.mk.injEq, Sum.inr.injEq, and_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    cPair, ← Nat.cast_smul_eq_nsmul ℂ]
  split_ifs
  · push_cast; module
  · simp [sub_eq_add_neg]; abel

theorem eab_kc (a b : Fin P) : IsKC (Eab (.inl a) (.inl b) : Mat P Q) := by
  intro u v h; simp only [Eab, Matrix.single_apply]; split_ifs with h'
  · obtain ⟨rfl, rfl⟩ := h'; exact absurd trivial h
  · rfl

theorem eab_kc' (a b : Fin Q) : IsKC (Eab (.inr a) (.inr b) : Mat P Q) := by
  intro u v h; simp only [Eab, Matrix.single_apply]; split_ifs with h'
  · obtain ⟨rfl, rfl⟩ := h'; exact absurd trivial h
  · rfl

theorem trace_eab {p q : ℕ} (a b : Ix p q) : (Eab a b : Mat p q).trace = if a = b then 1 else 0 := by
  split_ifs with h
  · subst h; exact Matrix.trace_single_eq_same _ _
  · exact Matrix.trace_single_eq_of_ne _ _ _ h

theorem pderiv_neg_zero (f : Pol P Q R S) (hf : ∀ l ∈ f.vars, linePos l = true) (l : Ln P Q R S)
    (hl : linePos l = false) : pderiv l f = 0 :=
  pderiv_eq_zero_of_notMem_vars fun h => by simp [hf l h] at hl

theorem mixed_hw_harm : ∀ (P Q R S : ℕ) (x : ℚ) (k k' : ℕ), x - Formalism.BasicNotions.TH.cPair R S = k →
    x + Formalism.BasicNotions.TH.cPair R S = k' → ∀ f : Formalism.BasicNotions.TH.Pol P Q R S, f ∈ GlobalTheory.KFixIrr.chiOne P Q R S x →
    (∀ l ∈ f.vars, Formalism.BasicNotions.TH.linePos l = true) →
    (∀ i j : Fin (P + Q), i < j → GlobalTheory.Capelli.mixedOp ℂ (GlobalTheory.LowIrr.zR P Q R S) (GlobalTheory.LowIrr.yS P Q R S) i j f = 0) ∧
    (∀ i : Fin (P + Q), GlobalTheory.Capelli.mixedOp ℂ (GlobalTheory.LowIrr.zR P Q R S) (GlobalTheory.LowIrr.yS P Q R S) i i f =
      GlobalTheory.LowIrr.kap P Q k k' i • f) ∧
    ∀ (c : Fin R) (d : Fin S), ∑ i, MvPolynomial.pderiv (GlobalTheory.LowIrr.zR P Q R S (c, i))
      (MvPolynomial.pderiv (GlobalTheory.LowIrr.yS P Q R S (d, i)) f) = 0 := by
  intro P Q R S x k k' hk hk' f hf hpos
  rw [GlobalTheory.KFixIrr.mem_chiOne] at hf
  have hk2 : ((x : ℂ) - ((cPair R S : ℚ) : ℂ)) = (k : ℂ) := by exact_mod_cast hk
  have hk2' : ((x : ℂ) + ((cPair R S : ℚ) : ℂ)) = (k' : ℂ) := by exact_mod_cast hk'
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective j
    rcases a with a | a <;> rcases b with b | b
    · have hab : a ≠ b := by rintro rfl; exact lt_irrefl _ hij
      have h1 := fock_action_mixed_capelli_inl (Q := Q) (R := R) (S := S) a b f
      rw [hf _ (eab_kc a b), trace_eab, if_neg (by simpa using hab), if_neg hab] at h1
      simpa using h1.symm
    · rw [GlobalTheory.Capelli.mixedOp_apply]
      simp only [GlobalTheory.LowIrr.zR, GlobalTheory.LowIrr.yS, Equiv.symm_apply_apply]
      have h1 : ∀ c : Fin R, pderiv ((Sum.inr b, Sum.inl c) : Ln P Q R S) f = 0 :=
        fun c => pderiv_neg_zero f hpos _ rfl
      have h2 : ∀ d : Fin S, pderiv ((Sum.inl a, Sum.inr d) : Ln P Q R S) f = 0 :=
        fun d => pderiv_neg_zero f hpos _ rfl
      simp [h1, h2]
    · exfalso
      simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.lt_def, Fin.coe_castAdd,
        Fin.coe_natAdd] at hij
      omega
    · have hab : a ≠ b := by rintro rfl; exact lt_irrefl _ hij
      have h1 := fock_action_mixed_capelli_inr (P := P) (R := R) (S := S) b a f
      rw [hf _ (eab_kc' b a), trace_eab, if_neg (by simpa using hab.symm), if_neg hab.symm] at h1
      have : GlobalTheory.Capelli.mixedOp ℂ (GlobalTheory.LowIrr.zR P Q R S) (GlobalTheory.LowIrr.yS P Q R S)
        (finSumFinEquiv (.inr a)) (finSumFinEquiv (.inr b)) f = -0 := by
        rw [← neg_eq_iff_eq_neg]; simpa using h1.symm
      simpa using this
  · intro i
    obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
    rcases a with a | a
    · have h1 := fock_action_mixed_capelli_inl (Q := Q) (R := R) (S := S) a a f
      rw [hf _ (eab_kc a a), trace_eab, if_pos rfl, if_pos rfl] at h1
      have hlt : ((finSumFinEquiv (Sum.inl a : Fin P ⊕ Fin Q) : Fin (P + Q)) : ℕ) < P := by
        simp [finSumFinEquiv_apply_left]
      rw [GlobalTheory.LowIrr.kap, if_pos hlt, ← hk2]
      rw [mul_one] at h1
      rw [sub_smul, h1, add_sub_cancel_right]
    · have h1 := fock_action_mixed_capelli_inr (P := P) (R := R) (S := S) a a f
      rw [hf _ (eab_kc' a a), trace_eab, if_pos rfl, if_pos rfl] at h1
      have hlt : ¬ ((finSumFinEquiv (Sum.inr a : Fin P ⊕ Fin Q) : Fin (P + Q)) : ℕ) < P := by
        simp [finSumFinEquiv_apply_right]
      rw [GlobalTheory.LowIrr.kap, if_neg hlt, ← hk2']
      rw [mul_one] at h1
      rw [neg_smul, add_smul, h1]
      abel
  · intro c d
    refine Finset.sum_eq_zero fun i _ => ?_
    obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
    simp only [GlobalTheory.LowIrr.zR, GlobalTheory.LowIrr.yS, Equiv.symm_apply_apply]
    rcases a with a | a
    · rw [pderiv_neg_zero f hpos _ rfl, map_zero]
    · rw [GlobalTheory.Capelli.pderiv_swap, pderiv_neg_zero f hpos _ rfl, map_zero]

end GlobalTheory.MixedHW
