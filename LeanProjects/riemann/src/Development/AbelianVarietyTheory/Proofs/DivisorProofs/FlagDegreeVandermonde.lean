import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AltCoeffRho

open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula

noncomputable section

namespace GlobalTheory.FlagHook.Degree

theorem sum_rho (N : ℕ) : ∑ i : Fin N, (N - 1 - (i : ℕ)) = N * (N - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N, Finset.sum_range_reflect (fun i => i) N,
    Finset.sum_range_id]

theorem prod_rho_factorial (N : ℕ) :
    ∏ i : Fin N, ((N - 1 - (i : ℕ)).factorial : ℝ) = ∏ m ∈ range N, (m.factorial : ℝ) := by
  rw [Fin.prod_univ_eq_prod_range (fun i => ((N - 1 - i).factorial : ℝ)) N,
    Finset.prod_range_reflect (fun i => (i.factorial : ℝ)) N]

theorem signed_sum {N : ℕ} (v : Fin N → ℝ) :
    ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, v i ^ (N - 1 - ((σ i : Fin N) : ℕ)) =
      ∏ i, ∏ j ∈ Ioi i, (v i - v j) := by
  have h := Matrix.det_projVandermonde (fun _ : Fin N => (1 : ℝ)) v
  rw [← Matrix.det_transpose, Matrix.det_apply'] at h
  simp only [Matrix.transpose_apply, Matrix.projVandermonde_apply, one_pow, one_mul, Fin.val_rev] at h
  rw [← h]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  omega

theorem eval_detE_rho (N : ℕ) (v : Fin N → ℝ) :
    eval v (detE (rho N)) = (∏ a : Fin N, ∏ b ∈ Ioi a, (v a - v b)) / ∏ m ∈ range N, (m.factorial : ℝ) := by
  rw [← signed_sum, ← prod_rho_factorial, detE, ← Matrix.det_transpose, Matrix.det_apply', map_sum,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_prod, mul_div_assoc,
    ← Equiv.prod_comp σ (fun i : Fin N => ((N - 1 - (i : ℕ)).factorial : ℝ)), ← Finset.prod_div_distrib]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp [rho, div_eq_inv_mul]

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

omit [DecidableEq ι] in
theorem sum_permExp (σ : ι → Equiv.Perm (Fin N)) : ∑ x, permExp σ x = dimFl ι N := by
  rw [Fintype.sum_prod_type]
  have h : ∀ τ, ∑ i : Fin N, permExp σ (τ, i) = N * (N - 1) / 2 := by
    intro τ
    rw [← sum_rho N]
    exact Fintype.sum_equiv (σ τ) _ _ (fun i => by simp [permExp])
  simp [h, dimFl]

omit [DecidableEq ι] in
theorem multinomial_permExp (σ : ι → Equiv.Perm (Fin N)) :
    ((permExp σ).multinomial : ℝ) =
      ((dimFl ι N).factorial : ℝ) / ∏ _τ : ι, ∏ m ∈ range N, (m.factorial : ℝ) := by
  have hne : (∏ _τ : ι, ∏ m ∈ range N, (m.factorial : ℝ)) ≠ 0 := by positivity
  rw [Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _), eq_div_iff hne, ← sum_permExp σ,
    ← Nat.multinomial_spec, Nat.cast_mul, mul_comm, Fintype.prod_prod_type]
  congr 1
  push_cast
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← prod_rho_factorial]
  exact (Fintype.prod_equiv (σ τ) _ _ (fun i => by simp [permExp])).symm

theorem flagDeg_eq (u : ι → Fin N → ℝ) :
    flagDeg ι N u = ((dimFl ι N).factorial : ℝ) * ∏ τ, eval (u τ) (detE (rho N)) := by
  have hl : linRoot u = ∑ x : ι × Fin N, (-u x.1 x.2) • (X x : MvPolynomial (ι × Fin N) ℝ) := by
    simp [linRoot, smul_eq_C_mul]
  have hc : ∀ σ : ι → Equiv.Perm (Fin N), (linRoot u ^ dimFl ι N).coeff (permExp σ) =
      (((dimFl ι N).factorial : ℝ) / ∏ _τ : ι, ∏ m ∈ range N, (m.factorial : ℝ)) * ((-1) ^ dimFl ι N *
        ∏ τ, ∏ i, u τ i ^ (N - 1 - ((σ τ i : Fin N) : ℕ))) := by
    intro σ
    rw [hl, coeff_linearCombination_X_pow_of_fintype, Finsupp.sum_fintype _ _ (fun _ => rfl),
      if_pos (sum_permExp σ), multinomial_permExp, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Finset.prod_congr rfl (fun x _ => neg_pow (u x.1 x.2) (permExp σ x)), Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, sum_permExp, Fintype.prod_prod_type]
    simp [permExp]
  have hs : ((-1 : ℝ) ^ dimFl ι N) * (-1) ^ dimFl ι N = 1 := by
    rw [← mul_pow]; simp
  simp only [eval_detE_rho]
  rw [Finset.prod_div_distrib, ← mul_div_assoc, mul_div_right_comm]
  simp only [← signed_sum]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, flagDeg, degFl, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hc, Finset.prod_mul_distrib]
  linear_combination ((((dimFl ι N).factorial : ℝ) / ∏ _τ : ι, ∏ m ∈ range N, (m.factorial : ℝ)) *
    (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) * ∏ τ, ∏ i, u τ i ^ (N - 1 - ((σ τ i : Fin N) : ℕ))) * hs

theorem flagDeg_eq_and_product :
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (u : ι → Fin N → ℝ),
      flagDeg ι N u = ((dimFl ι N).factorial : ℝ) * ∏ τ, eval (u τ) (detE (rho N))) ∧
    ∀ (N : ℕ) (v : Fin N → ℝ), eval v (detE (rho N)) =
      (∏ a : Fin N, ∏ b ∈ Ioi a, (v a - v b)) / ∏ m ∈ range N, (m.factorial : ℝ) :=
  ⟨fun _ _ _ _ u => flagDeg_eq u, eval_detE_rho⟩

end GlobalTheory.FlagHook.Degree
