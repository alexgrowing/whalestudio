import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AltCoeffRho

noncomputable section
open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula

namespace GlobalTheory.AltCoeffPow

def dv (k e : ℕ) (v : ℝ) : ℝ := (e.factorial : ℝ)⁻¹ * (e.descFactorial k : ℝ) * v ^ (e - k)

theorem dv_of_le {k e : ℕ} (h : k ≤ e) (v : ℝ) :
    dv k e v = ((e - k).factorial : ℝ)⁻¹ * v ^ (e - k) := by
  unfold dv
  congr 1
  have h1 := Nat.factorial_mul_descFactorial h
  have h2 : (e.factorial : ℝ) = ((e - k).factorial : ℝ) * (e.descFactorial k : ℝ) := by
    exact_mod_cast h1.symm
  have h3 : ((e - k).factorial : ℝ) ≠ 0 := by positivity
  have h4 : (e.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  rw [h2]; ring

theorem coeff_X_pow_mul_lin_pow {α : Type} [Fintype α] [DecidableEq α] (e : α →₀ ℕ) (a : α → ℝ)
    (x₀ : α) (m M : ℕ) (h : M + m = ∑ x, e x) :
    coeff e (X x₀ ^ m * (∑ x, a x • X x : MvPolynomial α ℝ) ^ M) =
      (M.factorial : ℝ) * ∏ x, dv (Finsupp.single x₀ m x) (e x) (a x) := by
  rw [X_pow_eq_monomial, coeff_monomial_mul']
  split_ifs with hle
  · have hs : ∑ x, (e - Finsupp.single x₀ m) x = M := by
      have h1 : ∑ x, (e - Finsupp.single x₀ m) x + ∑ x, Finsupp.single x₀ m x = ∑ x, e x := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finsupp.tsub_apply, Nat.sub_add_cancel (hle x)]
      have h2 : ∑ x, Finsupp.single x₀ m x = m := by
        simp [Finsupp.single_apply]
      omega
    rw [one_mul, coeff_linearCombination_X_pow_of_fintype,
      Finsupp.sum_fintype _ _ (fun _ => rfl), if_pos hs,
      Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _),
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rw [Finset.prod_congr rfl (fun x _ => dv_of_le (hle x) (a x)), Finset.prod_mul_distrib,
      ← mul_assoc]
    congr 1
    have h1 := Nat.multinomial_spec Finset.univ (e - Finsupp.single x₀ m : α →₀ ℕ)
    rw [hs] at h1
    have h2 : (M.factorial : ℝ) = (∏ x, ((e x - Finsupp.single x₀ m x).factorial : ℝ)) *
        (Nat.multinomial Finset.univ (e - Finsupp.single x₀ m : α →₀ ℕ) : ℝ) := by
      rw [← h1]; simp [Finsupp.tsub_apply]
    have h3 : (∏ x, ((e x - Finsupp.single x₀ m x).factorial : ℝ)) ≠ 0 := by positivity
    rw [h2, Finset.prod_inv_distrib]
    field_simp
  · rw [Finsupp.single_le_iff, not_le] at hle
    rw [Finset.prod_eq_zero (Finset.mem_univ x₀), mul_zero]
    simp [dv, hle]

theorem iterate_pderiv_monomial {α : Type} [DecidableEq α] (i : α) (s : α →₀ ℕ) (c : ℝ) (m : ℕ) :
    (pderiv i)^[m] (monomial s c) =
      monomial (s - Finsupp.single i m) (c * ((s i).descFactorial m : ℝ)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, pderiv_monomial, tsub_tsub, ← Finsupp.single_add,
      Nat.descFactorial_succ]
    congr 1
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same, Nat.cast_mul]
    ring

theorem iterate_pderiv_sum {α β : Type} (i : α) (s : Finset β) (f : β → MvPolynomial α ℝ) (m : ℕ) :
    (pderiv i)^[m] (∑ b ∈ s, f b) = ∑ b ∈ s, (pderiv i)^[m] (f b) := by
  induction m with
  | zero => simp
  | succ m ih => simp only [Function.iterate_succ_apply', ih, map_sum]

theorem detE_eq {N : ℕ} (n : Fin N → ℕ) :
    detE n = ∑ σ : Equiv.Perm (Fin N), monomial (Finsupp.equivFunOnFinite.symm fun j => n (σ j))
      (((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ j, ((n (σ j)).factorial : ℝ)⁻¹) := by
  rw [detE, ← Matrix.det_transpose, Matrix.det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Matrix.transpose_apply, Matrix.of_apply, Finset.prod_mul_distrib, map_mul, map_prod,
    map_intCast, Finsupp.coe_equivFunOnFinite_symm, mul_assoc]

theorem eval_iterate_pderiv_detE {N : ℕ} (n : Fin N → ℕ) (v : Fin N → ℝ) (i : Fin N) (m : ℕ) :
    eval v ((pderiv i)^[m] (detE n)) = ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
      ∏ j, dv (Finsupp.single i m j) (n (σ j)) (v j) := by
  rw [detE_eq, iterate_pderiv_sum, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [iterate_pderiv_monomial, eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  have h : ∏ j, ((n (σ j)).descFactorial (Finsupp.single i m j) : ℝ) =
      ((n (σ i)).descFactorial m : ℝ) := by
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      simp [Finsupp.single_eq_of_ne hj]
    · simp
  simp only [dv, Finset.prod_mul_distrib, h, Finsupp.tsub_apply,
    Finsupp.coe_equivFunOnFinite_symm, mul_assoc]

theorem eval_detE {N : ℕ} (n : Fin N → ℕ) (v : Fin N → ℝ) :
    eval v (detE n) = ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
      ∏ j, dv 0 (n (σ j)) (v j) := by
  rw [detE_eq, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp [dv, Finset.prod_mul_distrib, mul_assoc]

theorem altCoeff_X_pow_mul_linRoot_pow (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ)
    (n : ι → Fin N → ℕ) (u : ι → Fin N → ℝ) (τ' : ι) (i : Fin N) (m M : ℕ)
    (h : M + m = ∑ τ, ∑ c, n τ c) :
    altCoeff n (X (τ', i) ^ m * linRoot u ^ M) = (-1) ^ (dimFl ι N + M) * (M.factorial : ℝ) *
      (eval (u τ') ((pderiv i)^[m] (detE (n τ'))) *
        ∏ τ ∈ univ.erase τ', eval (u τ) (detE (n τ))) := by
  have hl : (X (τ', i) ^ m * linRoot u ^ M : MvPolynomial (ι × Fin N) ℝ) =
      C ((-1) ^ M) * (X (τ', i) ^ m * (∑ x : ι × Fin N, u x.1 x.2 • X x) ^ M) := by
    simp only [linRoot, smul_eq_C_mul, map_pow, map_neg, map_one]
    rw [neg_pow]; ring
  set F : ι → Equiv.Perm (Fin N) → ℝ := fun τ σ => ((Equiv.Perm.sign σ : ℤ) : ℝ) *
    ∏ j, dv (Finsupp.single (τ', i) m (τ, j)) (n τ (σ j)) (u τ j) with hF
  have hc : ∀ σ : ι → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) *
      coeff (Finsupp.equivFunOnFinite.symm (fun x : ι × Fin N => n x.1 (σ x.1 x.2)))
        (X (τ', i) ^ m * linRoot u ^ M : MvPolynomial (ι × Fin N) ℝ) =
      (-1) ^ M * (M.factorial : ℝ) * ∏ τ, F τ (σ τ) := by
    intro σ
    rw [hl, coeff_C_mul, coeff_X_pow_mul_lin_pow _ (fun x : ι × Fin N => u x.1 x.2)]
    · simp only [hF, Finset.prod_mul_distrib, Fintype.prod_prod_type,
        Finsupp.coe_equivFunOnFinite_symm]
      ring
    · rw [h, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp only [Finsupp.coe_equivFunOnFinite_symm]
      exact (Equiv.sum_comp (σ τ) (n τ)).symm
  have hp : ∑ σ : ι → Equiv.Perm (Fin N), ∏ τ, F τ (σ τ) = ∏ τ, ∑ σ, F τ σ := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  have h1 : ∑ σ, F τ' σ = eval (u τ') ((pderiv i)^[m] (detE (n τ'))) := by
    rw [eval_iterate_pderiv_detE]
    simp [hF, Finsupp.single_apply]
  have h2 : ∀ τ ∈ univ.erase τ', ∑ σ, F τ σ = eval (u τ) (detE (n τ)) := by
    intro τ hτ
    rw [eval_detE]
    have := (Finset.ne_of_mem_erase hτ).symm
    simp [hF, Finsupp.single_apply, this]
  unfold altCoeff
  rw [Finset.sum_congr rfl (fun σ _ => hc σ), ← Finset.mul_sum, hp,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ'), h1, Finset.prod_congr rfl h2, pow_add]
  ring

end GlobalTheory.AltCoeffPow
