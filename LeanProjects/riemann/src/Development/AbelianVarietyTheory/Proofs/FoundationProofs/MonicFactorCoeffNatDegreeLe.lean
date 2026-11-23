import Mathlib

open Polynomial

namespace GlobalTheory.MonicFactorDegree

variable {κ : Type} [Field κ]

noncomputable def subst (D : ℕ) : Polynomial (Polynomial κ) →+* Polynomial (Polynomial κ) :=
  eval₂RingHom (mapRingHom (C : κ →+* Polynomial κ)) (C X * X ^ D)

lemma term_coeff (D j m i : ℕ) (p : Polynomial κ) :
    (((mapRingHom (C : κ →+* Polynomial κ)) p * (C X * X ^ D) ^ j).coeff m).coeff i =
      if D * j ≤ m then (if i = j then p.coeff (m - D * j) else 0) else 0 := by
  have hC : (C (X : Polynomial κ) : Polynomial (Polynomial κ)) ^ j = C (X ^ j) := (C_pow ..).symm
  rw [mul_pow, hC, ← pow_mul, ← mul_assoc, coeff_mul_X_pow']
  split_ifs with h1 h2
  · subst h2; rw [coeff_mul_C, coe_mapRingHom, coeff_map, coeff_C_mul_X_pow]; simp
  · rw [coeff_mul_C, coe_mapRingHom, coeff_map, coeff_C_mul_X_pow]; simp [h2]
  · simp

lemma subst_coeff_coeff (D : ℕ) (P : Polynomial (Polynomial κ)) (i k : ℕ) :
    ((subst D P).coeff (k + D * i)).coeff i = (P.coeff i).coeff k := by
  simp only [subst, coe_eval₂RingHom, eval₂_eq_sum, Polynomial.sum, finset_sum_coeff, term_coeff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · intro hi; simp [notMem_support_iff.mp hi]

theorem monic_factor_coeff_natDegree_le : ∀ {κ : Type} [Field κ] (Φ A B : Polynomial (Polynomial κ))
    (D : ℕ), Φ.Monic → A.Monic → B.Monic → Φ = A * B → (∀ i, (Φ.coeff i).natDegree ≤ D) →
    ∀ i, (A.coeff i).natDegree ≤ Φ.natDegree * D := by
  intro κ _ Φ A B D hΦ _ hB hAB hD i
  by_cases hi : A.coeff i = 0
  · simp [hi]
  have key : ∀ P : Polynomial (Polynomial κ), ∀ j, P.coeff j ≠ 0 →
      (P.coeff j).natDegree + D * j ≤ (subst D P).natDegree ∧ subst D P ≠ 0 := by
    intro P j hj
    have h := subst_coeff_coeff D P j (P.coeff j).natDegree
    have hne : (subst D P).coeff ((P.coeff j).natDegree + D * j) ≠ 0 := by
      intro h0
      rw [h0, coeff_zero] at h
      exact hj (leadingCoeff_eq_zero.mp h.symm)
    exact ⟨le_natDegree_of_ne_zero hne, fun h0 => hne (by simp [h0])⟩
  have hAi := key A i hi
  have hB0 := (key B B.natDegree (by rw [hB.coeff_natDegree]; exact one_ne_zero)).2
  have hmul : (subst D Φ).natDegree = (subst D A).natDegree + (subst D B).natDegree := by
    rw [hAB, map_mul, natDegree_mul hAi.2 hB0]
  have hup : (subst D Φ).natDegree ≤ Φ.natDegree * D := by
    simp only [subst, coe_eval₂RingHom, eval₂_eq_sum, Polynomial.sum]
    apply natDegree_sum_le_of_forall_le
    intro j hj
    have hjd : j ≤ Φ.natDegree := le_natDegree_of_mem_supp j hj
    have h1 : (mapRingHom (C : κ →+* Polynomial κ) (Φ.coeff j)).natDegree ≤ (Φ.coeff j).natDegree := by
      rw [coe_mapRingHom]; exact natDegree_map_le
    have h2 : ((C X * X ^ D : Polynomial (Polynomial κ)) ^ j).natDegree ≤ j * D := by
      calc _ ≤ j * (C X * X ^ D : Polynomial (Polynomial κ)).natDegree := natDegree_pow_le
        _ ≤ j * D := by
          apply Nat.mul_le_mul_left
          calc _ ≤ (C X : Polynomial (Polynomial κ)).natDegree + (X ^ D : Polynomial (Polynomial κ)).natDegree :=
                natDegree_mul_le
            _ = D := by simp
    have h3 : (Φ.coeff j).natDegree + j * D ≤ Φ.natDegree * D := by
      rcases hjd.lt_or_eq with h | h
      · have h4 := hD j
        have h5 : (j + 1) * D ≤ Φ.natDegree * D := Nat.mul_le_mul_right _ h
        rw [add_mul, one_mul] at h5
        omega
      · rw [h, hΦ.coeff_natDegree, natDegree_one, zero_add]
    exact (natDegree_mul_le).trans (by omega)
  have := hAi.1
  have h6 : (A.coeff i).natDegree ≤ (subst D A).natDegree := by omega
  omega

end GlobalTheory.MonicFactorDegree
