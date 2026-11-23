import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormFormOneUnitary.PRowWSColW

open Matrix Finset Formalism.QuantumDeterminants

noncomputable section

namespace NFOne

theorem K_iso (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ)
    (Vs : ∀ b, b < j → ∀ q : Fin (2 * r + k + 1), r + k < q.val →
      V b q = if (sg k r q).val = b then 1 else 0)
    (p q : Fin (2 * r + k + 1)) (hp : r + k < p.val) (hq : r + k < q.val)
    (hb : (sg k r q).val < j) (hc : (sg k r p).val < j) :
    herm (Hpk k r) (V (sg k r q).val) (V (sg k r p).val) =
      star (V (sg k r p).val (sg k r q)) + V (sg k r q).val (sg k r p) +
      ∑ i, (if r ≤ i.val ∧ i.val ≤ r + k then
        dW k r i * star (V (sg k r p).val i) * V (sg k r q).val i else 0) := by
  have hp' := p.isLt; have hq' := q.isLt
  rw [herm_eq]
  have pt : ∀ i : Fin (2 * r + k + 1),
      star (V (sg k r p).val i) * (Hpk k r *ᵥ V (sg k r q).val) i =
        (if i = sg k r q then star (V (sg k r p).val (sg k r q)) else 0) +
        (if i = p then V (sg k r q).val (sg k r p) else 0) +
        (if r ≤ i.val ∧ i.val ≤ r + k then
          dW k r i * star (V (sg k r p).val i) * V (sg k r q).val i else 0) := by
    intro i
    have hi := i.isLt
    rw [Hpk_mulVec]
    by_cases h1 : i.val < r
    · rw [if_neg (show ¬ (r ≤ i.val ∧ i.val ≤ r + k) by omega),
        if_neg (show ¬ (i = p) from fun h => by rw [h] at h1; omega),
        if_neg (show ¬ (r ≤ i.val ∧ i.val ≤ r + k) by omega), add_zero, add_zero]
      rw [Vs _ hb (sg k r i) (by simp only [sg_val]; omega)]
      by_cases h2 : i = sg k r q
      · rw [if_pos (show (sg k r (sg k r i)).val = (sg k r q).val by rw [h2, sg_sg]), if_pos h2,
          mul_one, h2]
      · rw [if_neg (show ¬ ((sg k r (sg k r i)).val = (sg k r q).val) by
            intro h; apply h2; ext; simp only [sg_val] at h ⊢; omega), if_neg h2, mul_zero]
    · by_cases h3 : i.val ≤ r + k
      · rw [if_pos (show r ≤ i.val ∧ i.val ≤ r + k from ⟨by omega, h3⟩),
          if_neg (show ¬ (i = sg k r q) from fun h => by rw [h] at h1; simp only [sg_val] at h1; omega),
          if_neg (show ¬ (i = p) from fun h => by rw [h] at h3; omega),
          if_pos (show r ≤ i.val ∧ i.val ≤ r + k from ⟨by omega, h3⟩)]
        ring
      · rw [if_neg (show ¬ (r ≤ i.val ∧ i.val ≤ r + k) by omega),
          if_neg (show ¬ (r ≤ i.val ∧ i.val ≤ r + k) by omega),
          if_neg (show ¬ (i = sg k r q) from fun h => by rw [h] at h3; simp only [sg_val] at h3; omega),
          zero_add, add_zero]
        rw [Vs _ hc i (by omega)]
        by_cases h2 : i = p
        · rw [if_pos (show (sg k r i).val = (sg k r p).val by rw [h2]), if_pos h2, h2]; simp
        · rw [if_neg (show ¬ ((sg k r i).val = (sg k r p).val) by
            intro h; apply h2; ext; simp only [sg_val] at h; omega), if_neg h2]; simp
  rw [Finset.sum_congr rfl (fun i _ => pt i), Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem E_zero (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ)
    (V0 : ∀ c, j ≤ c → V c = 0)
    (Vs : ∀ b, b < j → ∀ q : Fin (2 * r + k + 1), r + k < q.val →
      V b q = if (sg k r q).val = b then 1 else 0)
    (Viso : ∀ b c, b < j → c < j → herm (Hpk k r) (V b) (V c) = 0)
    (p q : Fin (2 * r + k + 1)) :
    ((Pm k r j V)ᴴ * Hpk k r) p q + (Hpk k r * Pm k r j V) p q +
      ((Pm k r j V)ᴴ * (Hpk k r * Pm k r j V)) p q = 0 := by
  have hp2 := p.isLt
  have hq2 := q.isLt
  rw [PH_apply, HP_apply, PHP_apply]
  have hC : ¬ (r + k < p.val ∧ r + k < q.val) →
      ∑ i, (if r ≤ i.val ∧ i.val ≤ r + k then
        dW k r i * star (Pm k r j V i p) * Pm k r j V i q else 0) = 0 := by
    intro hpq
    refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with hi
    · by_cases hp : r + k < p.val
      · rw [P_rowWS_colW k r j V i q hi.1 (by omega), mul_zero]
      · rw [P_rowWS_colW k r j V i p hi.1 (by omega), star_zero, mul_zero, zero_mul]
    · rfl
  by_cases hpX : p.val < r
  · have hpW : ¬ (r ≤ p.val ∧ p.val ≤ r + k) := by omega
    have hA : ∀ x : Fin (2 * r + k + 1), Pm k r j V x p = 0 := fun x => P_colX k r j V x p hpX
    have hB : Pm k r j V (sg k r p) q = 0 := P_rowS k r j V (sg k r p) q (by rw [sg_val]; omega)
    rw [if_neg hpW, hB, hC (by omega), hA, hA]
    simp
  · by_cases hpW : r ≤ p.val ∧ p.val ≤ r + k
    · rw [if_pos hpW, hC (by omega), add_zero]
      by_cases hqX : q.val < r
      · have hqW : ¬ (r ≤ q.val ∧ q.val ≤ r + k) := by omega
        rw [if_neg hqW, P_rowS k r j V (sg k r q) p (by rw [sg_val]; omega), P_colX k r j V p q hqX]
        simp
      · by_cases hqW : r ≤ q.val ∧ q.val ≤ r + k
        · rw [if_pos hqW, P_rowWS_colW k r j V q p hqW.1 hpW.2, P_rowWS_colW k r j V p q hpW.1 hqW.2]
          simp
        · have hqS : r + k < q.val := by omega
          rw [if_neg hqW, P_XW k r j V (sg k r q) p (by rw [sg_val]; omega) hpW.1 hpW.2,
            P_WS k r j V p q hpW.1 hpW.2 hqS, star_neg, star_mul', star_star, star_dW]
          ring
    · have hpS : r + k < p.val := by omega
      rw [if_neg hpW]
      by_cases hqX : q.val < r
      · have hqW : ¬ (r ≤ q.val ∧ q.val ≤ r + k) := by omega
        rw [if_neg hqW, P_rowS k r j V (sg k r q) p (by rw [sg_val]; omega),
          P_colX k r j V (sg k r p) q hqX, hC (by omega)]
        simp
      · by_cases hqW : r ≤ q.val ∧ q.val ≤ r + k
        · rw [if_pos hqW, P_WS k r j V q p hqW.1 hqW.2 hpS,
            P_XW k r j V (sg k r p) q (by rw [sg_val]; omega) hqW.1 hqW.2, hC (by omega)]
          ring
        · have hqS : r + k < q.val := by omega
          rw [if_neg hqW]
          have hC' : ∑ i, (if r ≤ i.val ∧ i.val ≤ r + k then
              dW k r i * star (Pm k r j V i p) * Pm k r j V i q else 0) =
              ∑ i, (if r ≤ i.val ∧ i.val ≤ r + k then
                dW k r i * star (V (sg k r p).val i) * V (sg k r q).val i else 0) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            split_ifs with hi
            · rw [P_WS k r j V i p hi.1 hi.2 hpS, P_WS k r j V i q hi.1 hi.2 hqS]
            · rfl
          rw [hC', P_XS k r j V (sg k r q) p (by rw [sg_val]; omega) hpS,
            P_XS k r j V (sg k r p) q (by rw [sg_val]; omega) hqS]
          by_cases hbp : (sg k r p).val < j
          · by_cases hbq : (sg k r q).val < j
            · rw [if_pos hbp, if_pos hbq]
              have hK := K_iso k r j V Vs p q hpS hqS hbq hbp
              rw [Viso _ _ hbq hbp] at hK
              exact hK.symm
            · have h0 := V0 _ (Nat.le_of_not_lt hbq)
              rw [if_pos hbp, if_neg hbq, h0]
              simp
          · have h0 := V0 _ (Nat.le_of_not_lt hbp)
            rw [if_neg hbp, h0]
            by_cases hbq : (sg k r q).val < j
            · rw [if_pos hbq]
              simp
            · have h0' := V0 _ (Nat.le_of_not_lt hbq)
              rw [if_neg hbq, h0']
              simp

theorem unitary_P (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ)
    (V0 : ∀ c, j ≤ c → V c = 0)
    (Vs : ∀ b, b < j → ∀ q : Fin (2 * r + k + 1), r + k < q.val →
      V b q = if (sg k r q).val = b then 1 else 0)
    (Viso : ∀ b c, b < j → c < j → herm (Hpk k r) (V b) (V c) = 0) :
    (1 + Pm k r j V)ᴴ * Hpk k r * (1 + Pm k r j V) = Hpk k r := by
  have hE : (Pm k r j V)ᴴ * Hpk k r + Hpk k r * Pm k r j V +
      (Pm k r j V)ᴴ * (Hpk k r * Pm k r j V) = 0 := by
    ext p q
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact E_zero k r j V V0 Vs Viso p q
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one]
  calc (1 + (Pm k r j V)ᴴ) * Hpk k r * (1 + Pm k r j V)
      = Hpk k r + ((Pm k r j V)ᴴ * Hpk k r + Hpk k r * Pm k r j V +
          (Pm k r j V)ᴴ * (Hpk k r * Pm k r j V)) := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
        abel
    _ = Hpk k r := by rw [hE, add_zero]

end NFOne
