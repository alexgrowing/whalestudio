import Mathlib
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl

open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly

namespace GlobalTheory.FlagDegSign

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

omit [DecidableEq ι] in
theorem sum_permExp (σ : ι → Equiv.Perm (Fin N)) : ∑ x, permExp σ x = dimFl ι N := by
  rw [Fintype.sum_prod_type]
  have h : ∀ τ, ∑ i : Fin N, permExp σ (τ, i) = N * (N - 1) / 2 := by
    intro τ
    rw [← Formalism.DegreeFormula.PermutationPointDegree.sum_delta N]
    exact Fintype.sum_equiv (σ τ) _ _ (fun i => by simp [permExp])
  simp [h, dimFl]

omit [DecidableEq ι] in
theorem multinomial_permExp (σ : ι → Equiv.Perm (Fin N)) :
    (permExp σ).multinomial = (permExp (fun _ : ι => (1 : Equiv.Perm (Fin N)))).multinomial := by
  rw [Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _),
    Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)]
  unfold Nat.multinomial
  rw [sum_permExp, sum_permExp, Fintype.prod_prod_type, Fintype.prod_prod_type]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  exact Fintype.prod_equiv (σ τ) _ _ (fun i => by simp [permExp])

theorem signed_sum (v : Fin N → ℝ) :
    ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, v i ^ (N - 1 - ((σ i : Fin N) : ℕ)) =
      ∏ i, ∏ j > i, (v i - v j) := by
  have h := Matrix.det_projVandermonde (fun _ : Fin N => (1 : ℝ)) v
  rw [← Matrix.det_transpose, Matrix.det_apply'] at h
  simp only [Matrix.transpose_apply, Matrix.projVandermonde_apply, one_pow, one_mul, Fin.val_rev] at h
  rw [← h]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  omega

theorem flagDeg_eq (lam : ι → Fin N → ℝ) :
    flagDeg ι N lam = ((permExp (fun _ : ι => (1 : Equiv.Perm (Fin N)))).multinomial : ℝ) *
      ∏ τ, ∏ i, ∏ j > i, (lam τ i - lam τ j) := by
  have hl : linRoot lam = ∑ x : ι × Fin N, (-lam x.1 x.2) • (X x : MvPolynomial (ι × Fin N) ℝ) := by
    simp [linRoot, smul_eq_C_mul]
  have hc : ∀ σ : ι → Equiv.Perm (Fin N), (linRoot lam ^ dimFl ι N).coeff (permExp σ) =
      ((permExp (fun _ : ι => (1 : Equiv.Perm (Fin N)))).multinomial : ℝ) * ((-1) ^ dimFl ι N *
        ∏ τ, ∏ i, lam τ i ^ (N - 1 - ((σ τ i : Fin N) : ℕ))) := by
    intro σ
    rw [hl, coeff_linearCombination_X_pow_of_fintype, Finsupp.sum_fintype _ _ (fun _ => rfl),
      if_pos (sum_permExp σ), multinomial_permExp, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Finset.prod_congr rfl (fun x _ => neg_pow (lam x.1 x.2) (permExp σ x)), Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, sum_permExp, Fintype.prod_prod_type]
    simp [permExp]
  have hs : ((-1 : ℝ) ^ dimFl ι N) * (-1) ^ dimFl ι N = 1 := by
    rw [← mul_pow]; simp
  simp only [← signed_sum]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, flagDeg, degFl, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hc, Finset.prod_mul_distrib]
  linear_combination (((permExp (fun _ : ι => (1 : Equiv.Perm (Fin N)))).multinomial : ℝ) *
    (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) * ∏ τ, ∏ i, lam τ i ^ (N - 1 - ((σ τ i : Fin N) : ℕ))) * hs

omit [DecidableEq ι] in
theorem multinomial_pos :
    (0 : ℝ) < ((permExp (fun _ : ι => (1 : Equiv.Perm (Fin N)))).multinomial : ℝ) := by
  rw [Finsupp.multinomial_eq]
  exact_mod_cast Nat.multinomial_pos _ _

theorem flagDeg_pos_and_nonneg (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (lam : ι → Fin N → ℝ) :
    (RegDom lam → 0 < flagDeg ι N lam) ∧ (Dom lam → 0 ≤ flagDeg ι N lam) := by
  rw [flagDeg_eq]
  refine ⟨fun h => mul_pos multinomial_pos ?_, fun h => mul_nonneg multinomial_pos.le ?_⟩
  · exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Finset.prod_pos fun j hj =>
      sub_pos.2 (h τ i j (by simpa using hj))
  · exact Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j hj =>
      sub_nonneg.2 (h τ i j (le_of_lt (by simpa using hj)))

end GlobalTheory.FlagDegSign
