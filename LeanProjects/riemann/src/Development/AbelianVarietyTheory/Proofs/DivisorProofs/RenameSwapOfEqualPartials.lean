import Mathlib
open MvPolynomial

namespace GlobalTheory

theorem sym_of_factorial_recurrence (f : ℕ → ℕ → ℝ)
    (h : ∀ a b, f a (b + 1) * ((b : ℝ) + 1) = f (a + 1) b * ((a : ℝ) + 1)) :
    ∀ a b, f a b = f b a := by
  set g : ℕ → ℕ → ℝ := fun a b => (a.factorial : ℝ) * (b.factorial : ℝ) * f a b with hg
  have step : ∀ a b, g a (b + 1) = g (a + 1) b := by
    intro a b
    simp only [hg, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    have := h a b
    linear_combination ((a.factorial : ℝ) * (b.factorial : ℝ)) * this
  have diag : ∀ b a, g a b = g (a + b) 0 := by
    intro b
    induction b with
    | zero => intro a; simp
    | succ b ih => intro a; rw [step, ih]; congr 1; omega
  intro a b
  have e : g a b = g b a := by rw [diag b a, diag a b, Nat.add_comm]
  have ha : (a.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  have hb : (b.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero b
  simp only [hg] at e
  have hab : (a.factorial : ℝ) * (b.factorial : ℝ) ≠ 0 := mul_ne_zero ha hb
  have : (a.factorial : ℝ) * (b.factorial : ℝ) * f a b = (a.factorial : ℝ) * (b.factorial : ℝ) * f b a := by
    rw [e]; ring
  exact mul_left_cancel₀ hab this

theorem rename_swap_eq_of_pderiv_eq : ∀ (n : ℕ) (i i' : Fin (n + 1)) (K : MvPolynomial (Fin (n + 1)) ℝ),
    pderiv i' K = pderiv i K → rename (Equiv.swap i i') K = K := by
  intro n i i' K hK
  by_cases hii : i = i'
  · subst hii; simp [Equiv.swap_self, rename_id]
  ext m
  set β0 : Fin (n + 1) →₀ ℕ := (m.erase i).erase i' with hβ0
  set f : ℕ → ℕ → ℝ := fun a b => coeff (β0 + Finsupp.single i a + Finsupp.single i' b) K with hf
  have hrec : ∀ a b, f a (b + 1) * ((b : ℝ) + 1) = f (a + 1) b * ((a : ℝ) + 1) := by
    intro a b
    have h1 := congrArg (coeff (β0 + Finsupp.single i a + Finsupp.single i' b)) hK
    rw [coeff_pderiv, coeff_pderiv] at h1
    have ei : (β0 + Finsupp.single i a + Finsupp.single i' b) i = a := by
      simp [hβ0, Finsupp.single_apply, Ne.symm hii, hii]
    have ei' : (β0 + Finsupp.single i a + Finsupp.single i' b) i' = b := by
      simp [hβ0, Finsupp.single_apply, hii]
    rw [ei, ei'] at h1
    simp only [hf]
    have s1 : β0 + Finsupp.single i a + Finsupp.single i' b + Finsupp.single i' 1
        = β0 + Finsupp.single i a + Finsupp.single i' (b + 1) := by
      rw [add_assoc, ← Finsupp.single_add]
    have s2 : β0 + Finsupp.single i a + Finsupp.single i' b + Finsupp.single i 1
        = β0 + Finsupp.single i (a + 1) + Finsupp.single i' b := by
      rw [add_assoc, add_comm (Finsupp.single i' b), ← add_assoc, add_assoc β0, ← Finsupp.single_add]
    rw [s1, s2] at h1
    exact h1
  have hsym := sym_of_factorial_recurrence f hrec
  have hm : m = β0 + Finsupp.single i (m i) + Finsupp.single i' (m i') := by
    ext j
    by_cases hj : j = i
    · subst hj; simp [hβ0, Finsupp.single_apply, hii]
    · by_cases hj' : j = i'
      · subst hj'; simp [hβ0, Finsupp.single_apply, hii, Ne.symm hii]
      · simp [hβ0, Finsupp.single_apply, hj, hj', Ne.symm hj, Ne.symm hj']
  set m' : Fin (n + 1) →₀ ℕ := Finsupp.mapDomain (Equiv.swap i i') m with hm'
  have hmm : Finsupp.mapDomain (Equiv.swap i i') m' = m := by
    ext j
    rw [hm', Finsupp.mapDomain_equiv_apply, Finsupp.mapDomain_equiv_apply]
    simp
  have hm'e : m' = β0 + Finsupp.single i (m i') + Finsupp.single i' (m i) := by
    ext j
    rw [hm', Finsupp.mapDomain_equiv_apply, Equiv.symm_swap]
    by_cases hj : j = i
    · subst hj; simp [hβ0, Finsupp.single_apply, hii]
    · by_cases hj' : j = i'
      · subst hj'; simp [hβ0, Finsupp.single_apply, hii, Ne.symm hii]
      · rw [Equiv.swap_apply_of_ne_of_ne hj hj']
        simp [hβ0, Finsupp.single_apply, hj, hj', Ne.symm hj, Ne.symm hj']
  have h1 : coeff m (rename (Equiv.swap i i') K) = coeff m' K := by
    rw [← coeff_rename_mapDomain _ (Equiv.swap i i').injective K m', hmm]
  have hfm : f (m i) (m i') = coeff m K := by
    simp only [hf]; rw [← hm]
  rw [h1, hm'e]
  exact (hsym (m i') (m i)).trans hfm

end GlobalTheory
