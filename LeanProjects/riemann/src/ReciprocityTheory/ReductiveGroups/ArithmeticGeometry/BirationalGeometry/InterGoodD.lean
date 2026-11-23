import Mathlib
import Lemmata.GeneralBFactMore.Imports
import Lemmata.FirstBlockLemmaA.Imports

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

noncomputable section

variable {k : Type*} [Field k]

def substFun {r : ℕ} (lam : Fin r → k) : Fin (r + 1) → Polynomial (MvPolynomial (Fin r) k) :=
  Fin.cons Polynomial.X (fun i => Polynomial.C (C (lam i)) * Polynomial.X + Polynomial.C (X i))

def subst {r : ℕ} (lam : Fin r → k) :
    MvPolynomial (Fin (r + 1)) k →ₐ[k] Polynomial (MvPolynomial (Fin r) k) :=
  aeval (substFun lam)

theorem substFun_natDegree {r : ℕ} (lam : Fin r → k) (j : Fin (r + 1)) :
    (substFun lam j).natDegree ≤ 1 := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [substFun]
  · simp only [substFun, Fin.cons_succ]
    exact Polynomial.natDegree_linear_le

theorem substFun_coeff_one {r : ℕ} (lam : Fin r → k) (j : Fin (r + 1)) :
    (substFun lam j).coeff 1 = C ((Fin.cons (1 : k) lam : Fin (r + 1) → k) j) := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [substFun]
  · simp [substFun, Polynomial.coeff_C]

theorem prod_pow_natDegree_coeff {R ι : Type*} [CommRing R] (s : Finset ι) (p : ι → Polynomial R)
    (e : ι → ℕ) (hp : ∀ i, (p i).natDegree ≤ 1) :
    (∏ i ∈ s, p i ^ e i).natDegree ≤ ∑ i ∈ s, e i ∧
      (∏ i ∈ s, p i ^ e i).coeff (∑ i ∈ s, e i) = ∏ i ∈ s, (p i).coeff 1 ^ e i := by
  first | exact Bl.general_b_fact_more.goal1 .. | (apply Bl.general_b_fact_more.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_more.goal1 <;> assumption)

theorem subst_monomial {r : ℕ} (lam : Fin r → k) (m : Fin (r + 1) →₀ ℕ) (a : k) :
    (subst lam (monomial m a)).natDegree ≤ Finsupp.degree m ∧
      (subst lam (monomial m a)).coeff (Finsupp.degree m) =
        C (eval (Fin.cons (1 : k) lam) (monomial m a)) := by
  have h := prod_pow_natDegree_coeff m.support (substFun lam) m (substFun_natDegree lam)
  have hdeg : Finsupp.degree m = ∑ i ∈ m.support, m i := rfl
  simp only [subst, aeval_monomial, Finsupp.prod, eval_monomial]
  rw [hdeg, Polynomial.algebraMap_apply, algebraMap_eq]
  refine ⟨(Polynomial.natDegree_C_mul_le _ _).trans h.1, ?_⟩
  rw [Polynomial.coeff_C_mul, h.2]
  simp only [substFun_coeff_one, ← map_pow, ← map_prod, ← C_mul]

theorem subst_natDegree_le {r : ℕ} (lam : Fin r → k) (F : MvPolynomial (Fin (r + 1)) k) :
    (subst lam F).natDegree ≤ F.totalDegree := by
  conv_lhs => rw [F.as_sum, map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  exact (subst_monomial lam m _).1.trans (le_totalDegree hm)

theorem subst_coeff_totalDegree {r : ℕ} (lam : Fin r → k) (F : MvPolynomial (Fin (r + 1)) k) :
    (subst lam F).coeff F.totalDegree =
      C (eval (Fin.cons (1 : k) lam) (homogeneousComponent F.totalDegree F)) := by
  classical
  rw [show subst lam F = ∑ v ∈ F.support, subst lam (monomial v (coeff v F)) by
    rw [← map_sum, ← F.as_sum]]
  rw [homogeneousComponent_apply, map_sum, map_sum, Polynomial.finsetSum_coeff,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hle : Finsupp.degree m ≤ F.totalDegree := le_totalDegree hm
  split_ifs with hd
  · rw [← hd]; exact (subst_monomial lam m _).2
  · have hlt : Finsupp.degree m < F.totalDegree := lt_of_le_of_ne hle hd
    exact Polynomial.coeff_eq_zero_of_natDegree_lt ((subst_monomial lam m _).1.trans_lt hlt)

theorem homogeneousComponent_totalDegree_ne_zero {σ : Type*} {F : MvPolynomial σ k} (hF : F ≠ 0) :
    homogeneousComponent F.totalDegree F ≠ 0 := by
  obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup F.support (support_nonempty.mpr hF)
    (fun s => s.sum fun _ e => e)
  intro h0
  have := congrArg (coeff m) h0
  rw [coeff_homogeneousComponent, if_pos (by rw [totalDegree, hmax]; rfl), coeff_zero] at this
  exact (mem_support_iff.mp hm) this

theorem eval_smul_of_degree {σ : Type*} [Fintype σ] (H : MvPolynomial σ k) (d : ℕ)
    (hH : ∀ m ∈ H.support, Finsupp.degree m = d) (c : k) (v : σ → k) :
    eval (c • v) H = c ^ d * eval v H := by
  first | exact Bl.FirstBlockLemmaA.goal1 .. | (apply Bl.FirstBlockLemmaA.goal1 <;> assumption) | (intros; apply Bl.FirstBlockLemmaA.goal1 <;> assumption)

theorem exists_eval_cons_one_ne_zero [Infinite k] {r : ℕ} (H : MvPolynomial (Fin (r + 1)) k)
    (d : ℕ) (hH : ∀ m ∈ H.support, Finsupp.degree m = d) (h0 : H ≠ 0) :
    ∃ lam : Fin r → k, eval (Fin.cons (1 : k) lam) H ≠ 0 := by
  by_contra hall
  push Not at hall
  apply h0
  have hX : H * X 0 = 0 := by
    apply MvPolynomial.funext
    intro y
    rw [map_mul, eval_X, map_zero]
    by_cases hy : y 0 = 0
    · rw [hy, mul_zero]
    · have hyeq : y = y 0 • (Fin.cons (1 : k) (fun i => (y 0)⁻¹ * y i.succ) : Fin (r + 1) → k) := by
        funext j
        refine Fin.cases ?_ (fun i => ?_) j
        · simp
        · simp [hy]
      rw [hyeq, eval_smul_of_degree H d hH, hall, mul_zero, zero_mul]
  rcases mul_eq_zero.mp hX with h | h
  · exact h
  · exact absurd h (X_ne_zero 0)

theorem eval₂_subst {R : Type*} [CommRing R] [Algebra k R] {r : ℕ} (lam : Fin r → k)
    (ℓ : Fin (r + 1) → R) (F : MvPolynomial (Fin (r + 1)) k) :
    Polynomial.eval₂ ((aeval (fun i => ℓ i.succ - lam i • ℓ 0) : MvPolynomial (Fin r) k →ₐ[k] R) :
      MvPolynomial (Fin r) k →+* R) (ℓ 0) (subst lam F) =
      aeval ℓ F := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    simp [subst, Polynomial.eval₂_C, Polynomial.algebraMap_apply]
  | add p q hp hq => rw [map_add, Polynomial.eval₂_add, hp, hq, map_add]
  | mul_X p j hp =>
    rw [map_mul, Polynomial.eval₂_mul, hp, map_mul]
    congr 1
    simp only [subst, aeval_X]
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [substFun]
    · simp [substFun, Algebra.smul_def]

def IntOver (k : Type*) [Field k] {R : Type*} [CommRing R] [Algebra k R] {r : ℕ} (ℓ : Fin r → R)
    (x : R) : Prop :=
  ((aeval ℓ : MvPolynomial (Fin r) k →ₐ[k] R) : MvPolynomial (Fin r) k →+* R).IsIntegralElem x

theorem exists_isIntegralElem_linear [Infinite k] {R : Type*} [CommRing R] [Algebra k R] {r : ℕ}
    (ℓ : Fin (r + 1) → R) (F : MvPolynomial (Fin (r + 1)) k) (hF : F ≠ 0) (h : aeval ℓ F = 0) :
    ∃ lam : Fin r → k, IntOver k (fun i => ℓ i.succ - lam i • ℓ 0) (ℓ 0) := by
  classical
  set d := F.totalDegree
  have hsupp : ∀ m ∈ (homogeneousComponent d F).support, Finsupp.degree m = d := by
    intro m hm
    rw [mem_support_iff, coeff_homogeneousComponent] at hm
    by_contra hne
    exact hm (if_neg hne)
  obtain ⟨lam, hlam⟩ := exists_eval_cons_one_ne_zero _ d hsupp
    (homogeneousComponent_totalDegree_ne_zero hF)
  set c := eval (Fin.cons (1 : k) lam) (homogeneousComponent d F)
  refine ⟨lam, Polynomial.C (C c⁻¹) * subst lam F, ?_, ?_⟩
  · refine Polynomial.monic_of_natDegree_le_of_coeff_eq_one d ?_ ?_
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (subst_natDegree_le lam F)
    · rw [Polynomial.coeff_C_mul, subst_coeff_totalDegree, ← C_mul, inv_mul_cancel₀ hlam, C_1]
  · rw [Polynomial.eval₂_mul, eval₂_subst, h, mul_zero]

end

end ReciprocityTheory.ChartRestriction.G.Geo
