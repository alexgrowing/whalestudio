import Mathlib
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly

namespace GlobalTheory

theorem abs_prod_sub_prod_le_sum_of_le_one {ι : Type} [DecidableEq ι] (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i, |f i| ≤ 1) (hg : ∀ i, |g i| ≤ 1) :
    |∏ i ∈ s, f i - ∏ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    have hG : |∏ i ∈ s, g i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun i _ => abs_nonneg _) (fun i _ => hg i)
    have e : f j * ∏ i ∈ s, f i - g j * ∏ i ∈ s, g i
        = (f j - g j) * ∏ i ∈ s, g i + f j * (∏ i ∈ s, f i - ∏ i ∈ s, g i) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) hG
    · rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (hf j)).trans ih

theorem abs_monomial_sub_le_of_norm_le_one {σ : Type} [Fintype σ] [DecidableEq σ] (m : σ →₀ ℕ)
    (a b : σ → ℝ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    |∏ i, a i ^ m i - ∏ i, b i ^ m i| ≤ ((∑ i, m i : ℕ) : ℝ) * ‖a - b‖ := by
  have ha' : ∀ i, |a i| ≤ 1 := fun i => (norm_le_pi_norm a i).trans ha
  have hb' : ∀ i, |b i| ≤ 1 := fun i => (norm_le_pi_norm b i).trans hb
  refine (abs_prod_sub_prod_le_sum_of_le_one _ (fun i => a i ^ m i) (fun i => b i ^ m i)
    (fun i => ?_) (fun i => ?_)).trans ?_
  · rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (ha' i)
  · rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hb' i)
  · rw [Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : |a i - b i| ≤ ‖a - b‖ := norm_le_pi_norm (a - b) i
    have h2 := abs_prod_sub_prod_le_sum_of_le_one (Finset.range (m i)) (fun _ => a i) (fun _ => b i)
      (fun _ => ha' i) (fun _ => hb' i)
    simp only [Finset.prod_const, Finset.card_range, Finset.sum_const, nsmul_eq_mul] at h2
    exact h2.trans (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _))

theorem exists_lipschitz_eval_of_coeff_le (σ : Type) [Fintype σ] [DecidableEq σ] (d : ℕ) :
    ∃ n : ℝ, 0 ≤ n ∧ ∀ (P : MvPolynomial σ ℝ) (c : ℝ) (a b : σ → ℝ), P.totalDegree ≤ d →
      (∀ m, |P.coeff m| ≤ c) → ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      |eval a P - eval b P| ≤ n * c * ‖a - b‖ := by
  classical
  let S : Finset (σ →₀ ℕ) := Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => d)
  refine ⟨(S.card : ℝ) * d, by positivity, fun P c a b hd hc ha hb => ?_⟩
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc 0)
  have hdeg : ∀ m ∈ P.support, ∑ i, m i ≤ d := by
    intro m hm
    have := (le_totalDegree hm).trans hd
    rwa [Finsupp.sum_fintype _ _ (by simp)] at this
  have hsub : P.support ⊆ S := by
    intro m hm
    refine Finset.mem_Iic.2 fun i => ?_
    have : m i ≤ ∑ i, m i := Finset.single_le_sum (f := fun i => m i) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
    simpa using this.trans (hdeg m hm)
  rw [eval_eq', eval_eq', ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ m ∈ P.support, |P.coeff m * ∏ i, a i ^ m i - P.coeff m * ∏ i, b i ^ m i|
      ≤ ∑ m ∈ P.support, c * ((d : ℝ) * ‖a - b‖) := by
        refine Finset.sum_le_sum fun m hm => ?_
        rw [← mul_sub, abs_mul]
        refine mul_le_mul (hc m) ((abs_monomial_sub_le_of_norm_le_one m a b ha hb).trans ?_)
          (abs_nonneg _) hc0
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdeg m hm) (norm_nonneg _)
    _ = (P.support.card : ℝ) * (c * ((d : ℝ) * ‖a - b‖)) := by simp
    _ ≤ (S.card : ℝ) * (c * ((d : ℝ) * ‖a - b‖)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) (by positivity)
    _ = _ := by ring

end GlobalTheory
