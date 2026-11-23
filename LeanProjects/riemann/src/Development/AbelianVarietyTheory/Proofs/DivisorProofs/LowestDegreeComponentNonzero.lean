import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemTensSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroEquivariantPairingHasForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerPairingAdjointMixedLower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFirstActionMatrixUnitEq

noncomputable section

open scoped TensorProduct
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair GlobalTheory.FockSplit

namespace GlobalTheory.KFixIrr.LowMinor

variable {P Q R S : ℕ}

theorem sameBlock_self (a : Ix P Q) : sameBlock a a := by
  cases a <;> trivial

theorem fockAct1_detR_pow (h : P ≤ R) (k : ℕ) (i j : Ix P Q) (hij : sameBlock i j) :
    fockAct1 P Q R 0 (Eab i j) (detR P Q R h ^ k) =
      (if i = j then Sum.elim (fun _ => (k : ℂ) + (R : ℂ) / 2) (fun _ => -((R : ℂ) / 2)) i else 0) •
        detR P Q R h ^ k := by
  have e1 : embR P Q R h k 1 = detR P Q R h ^ k := by simp [embR]
  have e2 : actR P Q R k (Eab i j) 1 =
      (if i = j then Sum.elim (fun _ => (k : ℂ) + (R : ℂ) / 2) (fun _ => -((R : ℂ) / 2)) i else 0) • 1 := by
    rw [actR_apply]
    simp only [Eab, Matrix.single_apply, ite_smul, one_smul, zero_smul, LinearMap.sum_apply]
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp only [and_self, if_true]
    rcases i with a | b <;> rcases j with a' | b'
    · simp only [opR, derM, mulM, LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply, Derivation.map_one_eq_zero]
      simp only [Sum.inl.injEq]
      split_ifs <;> simp
    · exact absurd hij (by simp [sameBlock])
    · exact absurd hij (by simp [sameBlock])
    · simp only [opR, derM, mulM, Sum.inr.injEq]
      split_ifs <;> simp
  rw [← e1, actR_full, e2, map_smul, e1]

theorem fockAct1_detS_pow (h : Q ≤ S) (k' : ℕ) (i j : Ix P Q) (hij : sameBlock i j) :
    fockAct1 P Q 0 S (Eab i j) (detS P Q S h ^ k') =
      (if i = j then Sum.elim (fun _ => -((S : ℂ) / 2)) (fun _ => (k' : ℂ) + (S : ℂ) / 2) i else 0) •
        detS P Q S h ^ k' := by
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add]
  rcases i with a | b <;> rcases j with a' | b'
  · have hD : ∀ c : Fin S, pderiv ((Sum.inl a, Sum.inr c) : Ln P Q 0 S) (detS P Q S h ^ k') = 0 := fun c => by
      rw [Derivation.leibniz_pow, SDown.pderiv_u_detS h a c]; simp
    simp only [GlobalTheory.CompactHarm.omE_nn (Sum.inl a, Sum.inr _) (Sum.inl a', Sum.inr _) rfl rfl, hD, mul_zero, neg_zero,
      zero_sub, Prod.mk.injEq, Sum.inl.injEq, and_true, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    split_ifs with hh
    · simp only [Sum.elim_inl, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, neg_smul]
      congr 2; ring
    · simp
  · exact absurd hij (by simp [sameBlock])
  · exact absurd hij (by simp [sameBlock])
  · have hsum : ∑ c : Fin S, X ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) * pderiv (Sum.inr b', Sum.inr c) (detS P Q S h ^ k') =
        (if b = b' then (k' : ℂ) else 0) • detS P Q S h ^ k' := by
      have e : ∀ c : Fin S, X ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) * pderiv (Sum.inr b', Sum.inr c) (detS P Q S h ^ k') =
          ((k' : Pol P Q 0 S) * detS P Q S h ^ (k' - 1)) *
            (X (Sum.inr b, Sum.inr c) * pderiv (Sum.inr b', Sum.inr c) (detS P Q S h)) := fun c => by
        rw [Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul]; ring
      rw [Finset.sum_congr rfl fun c _ => e c, ← Finset.mul_sum, SDown.sum_X_pderiv_detS h b' b]
      split_ifs with hb
      · rcases k' with _ | n
        · simp
        · rw [mul_assoc, ← pow_succ, Nat.add_sub_cancel, ← map_natCast (C : ℂ →+* Pol P Q 0 S), C_mul']
      · simp
    simp only [GlobalTheory.CompactHarm.omE_pp (Sum.inr b, Sum.inr _) (Sum.inr b', Sum.inr _) rfl rfl, Finset.sum_add_distrib,
      hsum, Prod.mk.injEq, Sum.inr.injEq, and_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    split_ifs with hh
    · simp only [Sum.elim_inr, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← add_smul]
      congr 1; ring
    · simp

theorem detS_isHomogeneous (h : Q ≤ S) : (detS P Q S h).IsHomogeneous Q := by
  unfold detS
  rw [Matrix.det_apply']
  refine IsHomogeneous.sum _ _ _ fun σ _ => ?_
  have h1 : (∏ i : Fin Q, (Matrix.of fun b c : Fin Q =>
      (X (Sum.inr b, Sum.inr (Fin.castLE h c)) : Pol P Q 0 S)) (σ i) i).IsHomogeneous (∑ _i : Fin Q, 1) :=
    IsHomogeneous.prod _ _ _ fun i _ => isHomogeneous_X ℂ _
  have h0 : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : Pol P Q 0 S).IsHomogeneous 0 := by
    have := isHomogeneous_C (Ix P Q × Ix 0 S) (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)
    rwa [map_intCast] at this
  simpa using h0.mul h1

end GlobalTheory.KFixIrr.LowMinor

namespace GlobalTheory.KFixIrr.LowMinor

variable {P Q R S : ℕ}

def wit (P Q R S : ℕ) (h : P ≤ R) (h' : Q ≤ S) (k k' : ℕ) : Pol P Q R S :=
  rename (jR P Q R S) (detR P Q R h ^ k) * rename (jS P Q R S) (detS P Q S h' ^ k')

theorem wit_ne_zero (h : P ≤ R) (h' : Q ≤ S) (k k' : ℕ) : wit P Q R S h h' k k' ≠ 0 := by
  unfold wit
  refine mul_ne_zero ?_ ?_
  · rw [Ne, map_eq_zero_iff _ (rename_injective _ jR_injective)]
    exact pow_ne_zero _ (detR_ne_zero P Q R h)
  · rw [Ne, map_eq_zero_iff _ (rename_injective _ jS_injective)]
    exact pow_ne_zero _ (detS_ne_zero P Q S h')

theorem wit_isHomogeneous (h : P ≤ R) (h' : Q ≤ S) (k k' : ℕ) : (wit P Q R S h h' k k').IsHomogeneous (P * k + Q * k') := by
  unfold wit
  exact (((GlobalTheory.CharPair.GradR.detR_isHomogeneous P Q R h).pow k).rename_isHomogeneous).mul
    (((detS_isHomogeneous h').pow k').rename_isHomogeneous)

theorem fockAct1_Eab_wit (h : P ≤ R) (h' : Q ≤ S) (k k' : ℕ) (x : ℚ) (hk : x - cPair R S = k)
    (hk' : x + cPair R S = k') (i j : Ix P Q) (hij : sameBlock i j) :
    fockAct1 P Q R S (Eab i j) (wit P Q R S h h' k k') = (if i = j then (x : ℂ) else 0) • wit P Q R S h h' k k' := by
  unfold wit
  rw [fockAct1_Eab_mul, fockAct1_detR_pow h k i j hij, fockAct1_detS_pow h' k' i j hij, map_smul, map_smul,
    smul_mul_assoc, mul_smul_comm, ← add_smul]
  congr 1
  have hx1 : (x : ℂ) = (k : ℂ) + ((R : ℂ) - (S : ℂ)) / 2 := by
    have : x = (k : ℚ) + ((R : ℚ) - (S : ℚ)) / 2 := by rw [← hk, cPair]; ring
    rw [this]; push_cast; ring
  have hx2 : (x : ℂ) = (k' : ℂ) - ((R : ℂ) - (S : ℂ)) / 2 := by
    have : x = (k' : ℚ) - ((R : ℚ) - (S : ℚ)) / 2 := by rw [← hk', cPair]; ring
    rw [this]; push_cast; ring
  split_ifs with e
  · subst e
    rcases i with a | b
    · simp only [Sum.elim_inl, hx1]; ring
    · simp only [Sum.elim_inr, hx2]; ring
  · simp

theorem fockAct1_wit (h : P ≤ R) (h' : Q ≤ S) (k k' : ℕ) (x : ℚ) (hk : x - cPair R S = k)
    (hk' : x + cPair R S = k') (Z : Mat P Q) (hZ : IsKC Z) :
    fockAct1 P Q R S Z (wit P Q R S h h' k k') = ((x : ℂ) * Z.trace) • wit P Q R S h h' k k' := by
  have hZs : Z = ∑ a, ∑ b, Z a b • Eab a b := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
    simp only [Eab, Matrix.smul_single, smul_eq_mul, mul_one]
  have term : ∀ a b : Ix P Q, Z a b • fockAct1 P Q R S (Eab a b) (wit P Q R S h h' k k') =
      (if a = b then Z a a * (x : ℂ) else 0) • wit P Q R S h h' k k' := by
    intro a b
    by_cases hs : sameBlock a b
    · rw [fockAct1_Eab_wit h h' k k' x hk hk' a b hs, smul_smul]
      split_ifs with e
      · subst e; rfl
      · simp
    · have hab : a ≠ b := by rintro rfl; exact hs (sameBlock_self a)
      rw [hZ a b hs, zero_smul, if_neg hab, zero_smul]
  conv_lhs => rw [hZs]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, term]
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← Finset.sum_smul, Matrix.trace, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun a _ => by simp [Matrix.diag, mul_comm]

end GlobalTheory.KFixIrr.LowMinor

namespace GlobalTheory.KFixIrr

theorem lowOne_minors_ne_bot : ∀ (P Q R S : ℕ) (x : ℚ) (k k' : ℕ), P ≤ R → Q ≤ S → 0 < k → 0 < k' →
    x - Formalism.BasicNotions.TH.cPair R S = k → x + Formalism.BasicNotions.TH.cPair R S = k' →
    GlobalTheory.KFixIrr.lowOne P Q R S x (P * k + Q * k') ≠ ⊥ := by
  intro P Q R S x k k' h h' _ _ hk hk'
  rw [Submodule.ne_bot_iff]
  refine ⟨LowMinor.wit P Q R S h h' k k', ?_, LowMinor.wit_ne_zero h h' k k'⟩
  rw [mem_lowOne, mem_chiOne]
  exact ⟨fun Z hZ => LowMinor.fockAct1_wit h h' k k' x hk hk' Z hZ,
    (LowMinor.wit_isHomogeneous h h' k k').totalDegree_le⟩

end GlobalTheory.KFixIrr

end
