import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AltCoeffRho

noncomputable section
open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula

namespace GlobalTheory.HookKill

theorem altCoeff_perm {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (n : ι → Fin N → ℕ)
    (π : ι → Equiv.Perm (Fin N)) (P : MvPolynomial (ι × Fin N) ℝ) :
    altCoeff (fun t => n t ∘ π t) P
      = (∏ t, ((Equiv.Perm.sign (π t) : ℤ) : ℝ)) * altCoeff n P := by
  unfold altCoeff
  rw [mul_left_comm]
  congr 1
  rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft π)⁻¹]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  · refine Finset.prod_congr rfl fun t _ => ?_
    simp
  · congr 2
    funext x
    simp

theorem altCoeff_update_perm {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (n : ι → Fin N → ℕ)
    (τ : ι) (P : MvPolynomial (ι × Fin N) ℝ) (m : Fin N → ℕ) (π : Equiv.Perm (Fin N)) :
    altCoeff (Function.update n τ (m ∘ π)) P
      = ((Equiv.Perm.sign π : ℤ) : ℝ) * altCoeff (Function.update n τ m) P := by
  have h := altCoeff_perm (Function.update n τ m) (Pi.mulSingle τ π) P
  have h1 : (fun t => Function.update n τ m t ∘ (Pi.mulSingle τ π : ι → Equiv.Perm (Fin N)) t)
      = Function.update n τ (m ∘ π) := by
    funext t
    by_cases ht : t = τ
    · subst ht; simp
    · simp [ht]
  have h2 : (∏ t, ((Equiv.Perm.sign ((Pi.mulSingle τ π : ι → Equiv.Perm (Fin N)) t) : ℤ) : ℝ))
      = ((Equiv.Perm.sign π : ℤ) : ℝ) := by
    rw [Finset.prod_eq_single τ]
    · simp
    · intro t _ ht; simp [ht]
    · simp
  rw [h1, h2] at h
  exact h

theorem altCoeff_pw_mul {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (n : ι → Fin N → ℕ)
    (τ : ι) (k : ℕ) (G : MvPolynomial (ι × Fin N) ℝ) (m : Fin N → ℕ) :
    altCoeff (Function.update n τ m) (pw N τ k * G)
      = ∑ c : Fin N, if k ≤ m c then
          altCoeff (Function.update n τ (Function.update m c (m c - k))) G else 0 := by
  unfold altCoeff pw
  have : ∀ (c : Fin N) (a b : ℝ), (if k ≤ m c then a * b else 0) = a * if k ≤ m c then b else 0 := by
    intro c a b; split_ifs <;> simp
  simp only [this]
  rw [← Finset.mul_sum]
  congr 1
  have h2 : ∀ (c : Fin N) (f : (ι → Equiv.Perm (Fin N)) → ℝ),
      (if k ≤ m c then ∑ σ, f σ else 0) = ∑ σ, if k ≤ m c then f σ else 0 := by
    intro c f; split_ifs <;> simp
  simp only [h2, this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_mul, coeff_sum]
  refine Eq.trans ?_ (Equiv.sum_comp (σ τ) _)
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [X_pow_eq_monomial, coeff_monomial_mul']
  have h3 : (Finsupp.single (τ, i) k ≤ Finsupp.equivFunOnFinite.symm
      (fun x : ι × Fin N => Function.update n τ m x.1 (σ x.1 x.2))) ↔ k ≤ m (σ τ i) := by
    rw [Finsupp.single_le_iff]; simp
  simp only [h3]
  split_ifs with h
  · rw [one_mul]
    congr 1
    ext ⟨t, j⟩
    by_cases ht : t = τ
    · subst ht
      by_cases hj : j = i
      · subst hj; simp
      · have : σ t j ≠ σ t i := fun h => hj ((σ t).injective h)
        simp [hj, this]
    · simp [ht]
  · rfl

section Alt
variable {N : ℕ} (B : (Fin N → ℕ) → ℝ)
  (hB : ∀ (m : Fin N → ℕ) (π : Equiv.Perm (Fin N)), B (m ∘ π) = ((Equiv.Perm.sign π : ℤ) : ℝ) * B m)
include hB

theorem alt_swap (m : Fin N → ℕ) {a b : Fin N} (hab : a ≠ b) :
    B (m ∘ Equiv.swap a b) = - B m := by
  rw [hB, Equiv.Perm.sign_swap hab]; simp

theorem alt_zero (m : Fin N → ℕ) {a b : Fin N} (hab : a ≠ b) (h : m a = m b) : B m = 0 := by
  have h1 := alt_swap B hB m hab
  have h2 : m ∘ Equiv.swap a b = m := by
    funext x
    simp only [Function.comp, Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1, h]
    · rw [h2, h]
    · rfl
  rw [h2] at h1
  linarith

theorem down_rho (k : ℕ) (hk : 1 ≤ k) :
    (∑ c : Fin N, if k ≤ rho N c then B (Function.update (rho N) c (rho N c - k)) else 0) = 0 := by
  refine Finset.sum_eq_zero fun c _ => ?_
  split_ifs with h
  · have hc := c.2
    simp only [rho] at h
    have hne : (⟨c + k, by omega⟩ : Fin N) ≠ c := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    refine alt_zero B hB _ hne ?_
    rw [Function.update_of_ne hne]
    simp only [Function.update_self, rho]
    omega
  · rfl

theorem hook_sum (k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) :
    ∑ r ∈ range k, (-1 : ℝ) ^ r * B (hookRho N k r)
      = ∑ i : Fin N, B (Function.update (rho N) i (rho N i + k)) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have h1 : ∀ i : Fin (M + 1), B (Function.update (rho (M + 1)) i (rho (M + 1) i + k))
      = if (i : ℕ) < k then (-1 : ℝ) ^ (i : ℕ) * B (hookRho (M + 1) k i) else 0 := by
    intro i
    have hi := i.2
    split_ifs with h
    · have : Function.update (rho (M + 1)) i (rho (M + 1) i + k)
          = hookRho (M + 1) k i ∘ Fin.cycleRange i := by
        funext j
        have hj := j.2
        rcases lt_trichotomy j i with hji | hji | hji
        · have h3 : ((Fin.cycleRange i j : Fin (M + 1)) : ℕ) = j + 1 := Fin.coe_cycleRange_of_lt hji
          have h4 : (j : ℕ) < i := hji
          rw [Function.update_of_ne hji.ne]
          simp only [Function.comp, hookRho, rho, h3]
          rw [if_neg (Nat.succ_ne_zero _), if_pos (show (j : ℕ) + 1 ≤ i from h4)]
          omega
        · subst hji
          simp only [Function.comp, hookRho, rho, Fin.cycleRange_self, Function.update_self]
          simp
          omega
        · have h4 : (i : ℕ) < j := hji
          rw [Function.update_of_ne hji.ne']
          simp only [Function.comp, hookRho, rho, Fin.cycleRange_of_gt hji]
          split_ifs <;> omega
      rw [this, hB, Fin.sign_cycleRange]
      simp
    · have hne : (⟨i - k, by omega⟩ : Fin (M + 1)) ≠ i := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      refine alt_zero B hB _ hne ?_
      rw [Function.update_of_ne hne]
      simp only [Function.update_self, rho]
      omega
  simp only [h1]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < k then (-1 : ℝ) ^ i * B (hookRho (M + 1) k i) else 0),
    ← Finset.sum_filter]
  congr 1
  ext r
  simp only [mem_range, mem_filter]
  omega

theorem up_down (k k' : ℕ) (hkN : k ≤ N) (hk' : 1 ≤ k') (hne : k' ≠ k) :
    (∑ i : Fin N, ∑ c : Fin N, if k' ≤ Function.update (rho N) i (rho N i + k) c then
      B (Function.update (Function.update (rho N) i (rho N i + k)) c
        (Function.update (rho N) i (rho N i + k) c - k')) else 0) = 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun c _ => ?_
  have hc := c.2
  by_cases h : (c : ℕ) + k' < N
  · have hd : (⟨c + k', h⟩ : Fin N) ≠ c := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    have hr : rho N c = N - 1 - c := rfl
    have hr' : rho N ⟨c + k', h⟩ = N - 1 - (c + k') := rfl
    rw [Finset.sum_eq_add c ⟨c + k', h⟩ hd.symm]
    · rw [Function.update_self, Function.update_of_ne hd.symm, if_pos (by omega), if_pos (by omega),
        Function.update_idem]
      have := alt_swap B hB (Function.update (rho N) c (rho N c + k - k')) hd
      have h5 : Function.update (rho N) c (rho N c + k - k') ∘ Equiv.swap ⟨c + k', h⟩ c
          = Function.update (Function.update (rho N) ⟨c + k', h⟩ (rho N ⟨c + k', h⟩ + k)) c
            (rho N c - k') := by
        funext j
        simp only [Function.comp, Equiv.swap_apply_def]
        split_ifs with h1 h2
        · subst h1
          rw [Function.update_self, Function.update_of_ne hd, Function.update_self]
          omega
        · subst h2
          rw [Function.update_self, Function.update_of_ne hd]
          omega
        · rw [Function.update_of_ne h2, Function.update_of_ne h2, Function.update_of_ne h1]
      rw [h5] at this
      linarith
    · intro i _ hi
      split_ifs with h6
      · refine alt_zero B hB _ hd ?_
        rw [Function.update_of_ne hd, Function.update_of_ne hi.2.symm, Function.update_self,
          Function.update_of_ne hi.1.symm]
        omega
      · rfl
    · simp
    · simp
  · have hr : rho N c = N - 1 - c := rfl
    refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with h6
    · by_cases hi : c = i
      · subst hi
        rw [Function.update_self] at h6
        rw [Function.update_idem, Function.update_self]
        have hd : (⟨c + k' - k, by omega⟩ : Fin N) ≠ c := by
          intro h; have := congrArg Fin.val h; simp at this; omega
        refine alt_zero B hB _ hd ?_
        rw [Function.update_of_ne hd, Function.update_self]
        simp only [rho]
        omega
      · rw [Function.update_of_ne hi] at h6
        omega
    · rfl

end Alt

theorem hookFl_pw_mul_eq_zero (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (τ τ'' : ι) (k k' : ℕ)
    (G : MvPolynomial (ι × Fin N) ℝ) (hk : 1 ≤ k) (hkN : k ≤ N) (hk' : 1 ≤ k')
    (hne : (τ'', k') ≠ (τ, k)) : hookFl τ k (pw N τ'' k' * G) = 0 := by
  unfold hookFl
  refine mul_eq_zero_of_right _ ?_
  by_cases hτ : τ'' = τ
  · subst hτ
    have hkk : k' ≠ k := fun h => hne (by rw [h])
    have h1 : ∀ r, (fun τ' => if τ' = τ'' then hookRho N k r else rho N)
        = Function.update (fun _ => rho N) τ'' (hookRho N k r) := by
      intro r; funext t; simp [Function.update_apply]
    simp only [h1]
    rw [hook_sum (fun m => altCoeff (Function.update (fun _ => rho N) τ'' m) (pw N τ'' k' * G))
      (fun m π => altCoeff_update_perm _ _ _ m π) k hk hkN]
    simp only [altCoeff_pw_mul]
    exact up_down (fun m => altCoeff (Function.update (fun _ => rho N) τ'' m) G)
      (fun m π => altCoeff_update_perm _ _ _ m π) k k' hkN hk' hkk
  · refine Finset.sum_eq_zero fun r _ => mul_eq_zero_of_right _ ?_
    have h1 : (fun τ' => if τ' = τ then hookRho N k r else rho N)
        = Function.update (fun τ' => if τ' = τ then hookRho N k r else rho N) τ'' (rho N) := by
      funext t
      by_cases ht : t = τ''
      · subst ht; simp [hτ]
      · simp [ht]
    rw [h1, altCoeff_pw_mul]
    exact down_rho (fun m => altCoeff
      (Function.update (fun τ' => if τ' = τ then hookRho N k r else rho N) τ'' m) G)
      (fun m π => altCoeff_update_perm _ _ _ m π) k' hk'

end GlobalTheory.HookKill
