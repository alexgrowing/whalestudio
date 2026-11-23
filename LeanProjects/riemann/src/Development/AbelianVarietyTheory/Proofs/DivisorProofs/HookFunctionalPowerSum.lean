import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AltCoeffRho

noncomputable section
open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula

namespace GlobalTheory.FlagHook.HookPow

theorem altCoeff_perm {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (n : ι → Fin N → ℕ)
    (π : ι → Equiv.Perm (Fin N)) (P : MvPolynomial (ι × Fin N) ℝ) :
    altCoeff (fun t c => n t (π t c)) P =
      (∏ t, ((Equiv.Perm.sign (π t) : ℤ) : ℝ)) * altCoeff n P := by
  unfold altCoeff
  rw [mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft π) _ _ fun σ => ?_
  rw [← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun t _ => ?_
  simp only [Equiv.coe_mulLeft, Pi.mul_apply, Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (π t)) with h | h <;> simp [h]

theorem altCoeff_perm_one {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (n : ι → Fin N → ℕ)
    (τ : ι) (π : Equiv.Perm (Fin N)) (P : MvPolynomial (ι × Fin N) ℝ) :
    altCoeff (Function.update n τ (fun c => n τ (π c))) P =
      ((Equiv.Perm.sign π : ℤ) : ℝ) * altCoeff n P := by
  have h := altCoeff_perm n (Function.update 1 τ π) P
  rw [Finset.prod_eq_single τ (by intro b _ hb; simp [Function.update_of_ne hb]) (by simp)] at h
  simp only [Function.update_self] at h
  rw [← h]
  congr 1
  funext t c
  by_cases ht : t = τ
  · subst ht; simp
  · simp [Function.update_of_ne ht]

theorem altCoeff_eq_zero {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (n : ι → Fin N → ℕ)
    (τ : ι) (a b : Fin N) (hab : a ≠ b) (h : n τ a = n τ b) (P : MvPolynomial (ι × Fin N) ℝ) :
    altCoeff n P = 0 := by
  have h1 := altCoeff_perm_one n τ (Equiv.swap a b) P
  have h2 : (fun c => n τ (Equiv.swap a b c)) = n τ := by
    funext c
    rw [Equiv.swap_apply_def]
    split_ifs with h3 h4
    · rw [h3, h]
    · rw [h4, h]
    · rfl
  rw [h2, Function.update_eq_self, Equiv.Perm.sign_swap hab] at h1
  simp at h1
  linarith

theorem altCoeff_pw_mul {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (n : ι → Fin N → ℕ)
    (τ : ι) (k : ℕ) (G : MvPolynomial (ι × Fin N) ℝ) :
    altCoeff n (pw N τ k * G) = ∑ c : Fin N, if k ≤ n τ c then
      altCoeff (Function.update n τ (Function.update (n τ) c (n τ c - k))) G else 0 := by
  have key : ∀ σ : ι → Equiv.Perm (Fin N),
      (pw N τ k * G).coeff (Finsupp.equivFunOnFinite.symm (fun x : ι × Fin N => n x.1 (σ x.1 x.2))) =
      ∑ c : Fin N, if k ≤ n τ c then G.coeff (Finsupp.equivFunOnFinite.symm (fun x : ι × Fin N =>
        (Function.update n τ (Function.update (n τ) c (n τ c - k))) x.1 (σ x.1 x.2))) else 0 := by
    intro σ
    unfold pw
    rw [Finset.sum_mul, coeff_sum]
    refine Fintype.sum_equiv (σ τ) _ _ fun i => ?_
    rw [X_pow_eq_monomial, coeff_monomial_mul', one_mul]
    refine if_congr (by simp [Finsupp.single_le_iff]) ?_ rfl
    congr 1
    ext ⟨t, j⟩
    by_cases ht : t = τ
    · subst ht
      by_cases hj : j = i
      · subst hj; simp
      · have : σ t j ≠ σ t i := fun h => hj ((σ t).injective h)
        simp [Function.update_of_ne this, Finsupp.single_apply, Ne.symm hj]
    · simp [Function.update_of_ne ht, Finsupp.single_apply, Ne.symm ht]
  unfold altCoeff
  simp_rw [key, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

theorem altCoeff_hook_pw {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (τ : ι) (k r : ℕ) (hr : r < k) (hk : k ≤ N) (G : MvPolynomial (ι × Fin N) ℝ) :
    altCoeff (fun τ' => if τ' = τ then hookRho N k r else rho N) (pw N τ k * G) =
      (-1) ^ r * degFl ι N G := by
  have hN : 0 < N := by omega
  rw [altCoeff_pw_mul, Finset.sum_eq_single (⟨0, hN⟩ : Fin N)]
  · simp only [if_true]
    rw [if_pos (by simp [hookRho]; omega)]
    have h := altCoeff_perm_one (Function.update (fun τ' => if τ' = τ then hookRho N k r else rho N) τ
      (Function.update (hookRho N k r) ⟨0, hN⟩ (hookRho N k r ⟨0, hN⟩ - k))) τ
      (Fin.cycleRange (⟨r, by omega⟩ : Fin N)) G
    rw [Function.update_idem, Function.update_self, Fin.sign_cycleRange] at h
    have e : (Function.update (fun τ' => if τ' = τ then hookRho N k r else rho N) τ
        (fun c => Function.update (hookRho N k r) ⟨0, hN⟩ (hookRho N k r ⟨0, hN⟩ - k)
          (Fin.cycleRange (⟨r, by omega⟩ : Fin N) c))) = fun _ => rho N := by
      funext t c
      by_cases ht : t = τ
      · subst ht
        rw [Function.update_self, Function.update_apply]
        have hc := c.2
        rcases lt_trichotomy c (⟨r, by omega⟩ : Fin N) with h1 | h1 | h1
        · have h2 := Fin.coe_cycleRange_of_lt h1
          have h3 : (c : ℕ) < r := h1
          simp only [Fin.ext_iff, hookRho, rho, h2]
          split_ifs <;> first | omega | contradiction
        · have h2 := Fin.coe_cycleRange_of_le h1.le
          rw [if_pos h1] at h2
          have h3 : (c : ℕ) = r := congrArg Fin.val h1
          simp only [Fin.ext_iff, hookRho, rho, h2, if_true, h3]
          omega
        · have h3 : r < (c : ℕ) := h1
          simp only [Fin.ext_iff, hookRho, rho, Fin.cycleRange_of_gt h1]
          split_ifs <;> omega
      · simp [Function.update_of_ne ht, ht]
    rw [e, altCoeff_rho] at h
    rw [h, ← mul_assoc]
    simp [← mul_pow]
  · intro c _ hc
    simp only [if_true]
    split_ifs with hkc
    · have hc0 : (c : ℕ) ≠ 0 := fun h => hc (Fin.ext h)
      have hcN := c.2
      by_cases hcr : (c : ℕ) ≤ r
      · simp only [hookRho, if_neg hc0, if_pos hcr] at hkc
        by_cases hk1 : k = 1
        · omega
        refine altCoeff_eq_zero _ τ c ⟨c + k - 1, by omega⟩ (by simp [Fin.ext_iff]; omega) ?_ _
        rw [Function.update_self, Function.update_self,
          Function.update_of_ne (by simp [Fin.ext_iff]; omega)]
        simp only [hookRho]
        split_ifs <;> omega
      · simp only [hookRho, if_neg hc0, if_neg hcr] at hkc
        refine altCoeff_eq_zero _ τ c ⟨c + k, by omega⟩ (by simp [Fin.ext_iff]; omega) ?_ _
        rw [Function.update_self, Function.update_self,
          Function.update_of_ne (by simp [Fin.ext_iff]; omega)]
        simp only [hookRho]
        split_ifs <;> omega
    · rfl
  · simp

theorem hookFl_pw_mul' {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (τ : ι) (k : ℕ)
    (G : MvPolynomial (ι × Fin N) ℝ) (h1 : 1 ≤ k) (hk : k ≤ N) :
    hookFl τ k (pw N τ k * G) = degFl ι N G := by
  unfold hookFl
  rw [Finset.sum_congr rfl (g := fun _ => degFl ι N G)]
  · have : (k : ℝ) ≠ 0 := by positivity
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  · intro r hr
    rw [altCoeff_hook_pw τ k r (Finset.mem_range.mp hr) hk, ← mul_assoc, ← mul_pow]
    simp

theorem hookFl_pw_mul : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (τ : ι) (k : ℕ)
    (G : MvPolynomial (ι × Fin N) ℝ), 1 ≤ k → k ≤ N → G.IsHomogeneous (dimFl ι N) →
    hookFl τ k (pw N τ k * G) = degFl ι N G :=
  fun _ _ _ _ τ k G h1 hk _ => hookFl_pw_mul' τ k G h1 hk

end GlobalTheory.FlagHook.HookPow
