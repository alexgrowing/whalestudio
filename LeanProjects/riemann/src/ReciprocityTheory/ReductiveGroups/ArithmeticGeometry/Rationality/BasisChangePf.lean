import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.BasisChangeSt

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

namespace BasisChangePf

open MvPolynomial

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {ι : Type*}

def CB (Q : MvPolynomial ι K) (c : ℝ) : Prop := ∀ μ, ‖coeff μ Q‖ ≤ c

lemma cb_sum {α : Type*} (s : Finset α) (g : α → MvPolynomial ι K) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ a ∈ s, CB (g a) c) : CB (∑ a ∈ s, g a) c := by
  classical
  intro μ
  rw [MvPolynomial.coeff_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hc (fun a ha => h a ha μ)

lemma cb_mul {Q R : MvPolynomial ι K} {c d : ℝ} (hc : 0 ≤ c) (hQ : CB Q c) (hR : CB R d)
    (hd : 0 ≤ d) : CB (Q * R) (c * d) := by
  classical
  intro μ
  rw [MvPolynomial.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hc hd) (fun x _ => ?_)
  rw [norm_mul]
  exact mul_le_mul (hQ _) (hR _) (norm_nonneg _) hc

lemma cb_one : CB (1 : MvPolynomial ι K) 1 := by
  classical
  intro μ
  rw [MvPolynomial.coeff_one]
  split_ifs <;> simp

lemma cb_pow {Q : MvPolynomial ι K} {c : ℝ} (hc : 0 ≤ c) (hQ : CB Q c) (n : ℕ) : CB (Q ^ n) (c ^ n) := by
  induction n with
  | zero => simpa using (cb_one : CB (1 : MvPolynomial ι K) 1)
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact cb_mul (pow_nonneg hc n) ih hQ hc

lemma cb_prod {α : Type*} (s : Finset α) (g : α → MvPolynomial ι K) (c : α → ℝ) (hc : ∀ a, 0 ≤ c a)
    (h : ∀ a ∈ s, CB (g a) (c a)) : CB (∏ a ∈ s, g a) (∏ a ∈ s, c a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (cb_one : CB (1 : MvPolynomial ι K) 1)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact cb_mul (hc a) (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))
      (Finset.prod_nonneg fun b _ => hc b)

lemma cb_C_mul (a : K) {Q : MvPolynomial ι K} {c : ℝ} (hQ : CB Q c) : CB (C a * Q) (‖a‖ * c) := by
  classical
  intro μ
  rw [MvPolynomial.coeff_C_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hQ μ) (norm_nonneg a)

lemma cb_lin [Fintype ι] (A : ι → ι → K) {c : ℝ} (hc : 0 ≤ c) (hA : ∀ i k, ‖A i k‖ ≤ c) (i : ι) :
    CB (∑ k, C (A i k) * X k) c := by
  classical
  refine cb_sum _ _ hc (fun k _ => fun μ => ?_)
  rw [MvPolynomial.coeff_C_mul, norm_mul]
  calc ‖A i k‖ * ‖MvPolynomial.coeff μ (X k : MvPolynomial ι K)‖ ≤ ‖A i k‖ * 1 := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        rw [MvPolynomial.coeff_X']
        split_ifs <;> simp
    _ ≤ c := by simpa using hA i k

end BasisChangePf

open BasisChangePf in
theorem basisChange_holds : BasisChangeStatement := by
  intro K _ _ ι _ P d hP hP1 A C hC hA μ
  classical
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hL : ∀ i, CB (∑ k, MvPolynomial.C (A i k) * MvPolynomial.X k : MvPolynomial ι K) C :=
    fun i => cb_lin A hC0 hA i
  have key : CB (MvPolynomial.bind₁ (fun i => ∑ k, MvPolynomial.C (A i k) * MvPolynomial.X k) P) (C ^ d) := by
    conv => arg 1; rw [P.as_sum]
    rw [map_sum]
    refine cb_sum _ _ (pow_nonneg hC0 d) (fun v hv => ?_)
    rw [MvPolynomial.bind₁_monomial]
    have hdeg : v.degree = d := by
      rw [Finsupp.degree_eq_weight_one]
      exact hP (MvPolynomial.mem_support_iff.1 hv)
    have hprod : CB (∏ i ∈ v.support, (∑ k, MvPolynomial.C (A i k) * MvPolynomial.X k) ^ v i)
        (∏ i ∈ v.support, C ^ v i) :=
      cb_prod _ _ _ (fun i => pow_nonneg hC0 _) (fun i _ => cb_pow hC0 (hL i) (v i))
    have hb := cb_C_mul (MvPolynomial.coeff v P) hprod
    have hpow : ∏ i ∈ v.support, C ^ v i = C ^ d := by
      rw [Finset.prod_pow_eq_pow_sum, ← hdeg]
      rfl
    intro ν
    calc ‖MvPolynomial.coeff ν (MvPolynomial.C (MvPolynomial.coeff v P) *
          ∏ i ∈ v.support, (∑ k, MvPolynomial.C (A i k) * MvPolynomial.X k) ^ v i)‖
        ≤ ‖MvPolynomial.coeff v P‖ * ∏ i ∈ v.support, C ^ v i := hb ν
      _ ≤ 1 * C ^ d := by
          rw [hpow]
          exact mul_le_mul_of_nonneg_right (hP1 v) (pow_nonneg hC0 d)
      _ = C ^ d := one_mul _
  exact key μ

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
