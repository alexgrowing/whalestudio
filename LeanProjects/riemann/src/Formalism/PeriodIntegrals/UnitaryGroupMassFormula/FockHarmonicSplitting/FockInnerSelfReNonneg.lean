import Formalism.PeriodIntegrals.JointBlockShapes.MinusPart

noncomputable section

open MvPolynomial

namespace PI.FHS

variable {σ : Type*}

def wt (α : σ →₀ ℕ) : ℂ := α.prod (fun _ k => (k.factorial : ℂ))

lemma wt_eq_nat (α : σ →₀ ℕ) : wt α = ((α.prod fun _ k => k.factorial : ℕ) : ℂ) := by
  simp [wt, Finsupp.prod]

lemma wt_pos_nat (α : σ →₀ ℕ) : 0 < (α.prod fun _ k => k.factorial : ℕ) := by
  unfold Finsupp.prod
  exact Finset.prod_pos fun i _ => Nat.factorial_pos _

lemma conj_wt (α : σ →₀ ℕ) : (starRingEnd ℂ) (wt α) = wt α := by
  rw [wt_eq_nat, map_natCast]

private theorem fockInner_eq_sum_support_left (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner P Q = ∑ α ∈ P.support, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α := by
  unfold FockH1Action.fockInner
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [Finset.sum_eq_single α]
  · rw [if_pos rfl, wt]
  · intro β _ hβ
    rw [if_neg (Ne.symm hβ), mul_zero]
  · intro hα
    rw [MvPolynomial.mem_support_iff, not_not] at hα
    simp only [hα, mul_zero, zero_mul]

lemma fockInner_eq_sum (P Q : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : ∀ α, coeff α P ≠ 0 → coeff α Q ≠ 0 → α ∈ S) :
    FockH1Action.fockInner P Q = ∑ α ∈ S, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α := by
  classical
  rw [fockInner_eq_sum_support_left]
  have h1 : ∑ α ∈ P.support, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α
      = ∑ α ∈ P.support ∪ S, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α := by
    apply Finset.sum_subset (fun x hx => Finset.mem_union_left _ hx)
    intro α _ hα
    rw [MvPolynomial.mem_support_iff, not_not] at hα
    rw [hα, map_zero, zero_mul, zero_mul]
  have h2 : ∑ α ∈ S, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α
      = ∑ α ∈ P.support ∪ S, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α := by
    apply Finset.sum_subset (fun x hx => Finset.mem_union_right _ hx)
    intro α _ hα
    by_cases hP : coeff α P = 0
    · rw [hP, map_zero, zero_mul, zero_mul]
    · by_cases hQ : coeff α Q = 0
      · rw [hQ, mul_zero, zero_mul]
      · exact absurd (hS α hP hQ) hα
  rw [h1, h2]

lemma fockInner_eq_sum_left (P Q : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : P.support ⊆ S) :
    FockH1Action.fockInner P Q = ∑ α ∈ S, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α :=
  fockInner_eq_sum P Q S (fun _ hP _ => hS (MvPolynomial.mem_support_iff.mpr hP))

lemma fockInner_eq_sum_right (P Q : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : Q.support ⊆ S) :
    FockH1Action.fockInner P Q = ∑ α ∈ S, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α :=
  fockInner_eq_sum P Q S (fun _ _ hQ => hS (MvPolynomial.mem_support_iff.mpr hQ))

lemma fockInner_add_left (P P' Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (P + P') Q = FockH1Action.fockInner P Q + FockH1Action.fockInner P' Q := by
  rw [fockInner_eq_sum_right (P + P') Q Q.support (Finset.Subset.refl _),
    fockInner_eq_sum_right P Q Q.support (Finset.Subset.refl _),
    fockInner_eq_sum_right P' Q Q.support (Finset.Subset.refl _),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [coeff_add, map_add]
  ring

lemma fockInner_add_right (P Q Q' : MvPolynomial σ ℂ) :
    FockH1Action.fockInner P (Q + Q') = FockH1Action.fockInner P Q + FockH1Action.fockInner P Q' := by
  rw [fockInner_eq_sum_support_left, fockInner_eq_sum_support_left P Q, fockInner_eq_sum_support_left P Q',
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [coeff_add]
  ring

lemma fockInner_smul_left (c : ℂ) (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (c • P) Q = (starRingEnd ℂ) c * FockH1Action.fockInner P Q := by
  rw [fockInner_eq_sum_right (c • P) Q Q.support (Finset.Subset.refl _),
    fockInner_eq_sum_right P Q Q.support (Finset.Subset.refl _), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  simp only [coeff_smul, smul_eq_mul, map_mul]
  ring

lemma fockInner_smul_right (c : ℂ) (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner P (c • Q) = c * FockH1Action.fockInner P Q := by
  rw [fockInner_eq_sum_support_left, fockInner_eq_sum_support_left P Q, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  simp only [coeff_smul, smul_eq_mul]
  ring

lemma fockInner_neg_right (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner P (-Q) = - FockH1Action.fockInner P Q := by
  rw [fockInner_eq_sum_support_left, fockInner_eq_sum_support_left P Q, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [coeff_neg]
  ring

lemma fockInner_neg_left (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (-P) Q = - FockH1Action.fockInner P Q := by
  rw [fockInner_eq_sum_right (-P) Q Q.support (Finset.Subset.refl _),
    fockInner_eq_sum_right P Q Q.support (Finset.Subset.refl _),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [coeff_neg, map_neg]
  ring

lemma fockInner_zero_left (Q : MvPolynomial σ ℂ) : FockH1Action.fockInner 0 Q = 0 := by
  simp [fockInner_eq_sum_support_left]

lemma fockInner_zero_right (P : MvPolynomial σ ℂ) : FockH1Action.fockInner P 0 = 0 := by
  simp [fockInner_eq_sum_support_left]

lemma fockInner_conj (P Q : MvPolynomial σ ℂ) :
    (starRingEnd ℂ) (FockH1Action.fockInner Q P) = FockH1Action.fockInner P Q := by
  rw [fockInner_eq_sum_right Q P P.support (Finset.Subset.refl _),
    fockInner_eq_sum_support_left P Q, map_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [map_mul, map_mul, conj_wt, Complex.conj_conj]
  ring

private theorem conj_mul_self_eq_normSq (z : ℂ) : (starRingEnd ℂ) z * z = ((Complex.normSq z : ℝ) : ℂ) := by
  exact Complex.normSq_eq_conj_mul_self.symm

lemma fockInner_self (P : MvPolynomial σ ℂ) : FockH1Action.fockInner P P =
    ∑ α ∈ P.support, (((Complex.normSq (coeff α P)) *
      ((α.prod fun _ k => k.factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
  rw [fockInner_eq_sum_support_left]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [conj_mul_self_eq_normSq, wt_eq_nat]
  rw [Complex.ofReal_mul, Complex.ofReal_natCast]

lemma fockInner_self_re_nonneg (P : MvPolynomial σ ℂ) : 0 ≤ (FockH1Action.fockInner P P).re := by
  rw [fockInner_self, Complex.re_sum]
  refine Finset.sum_nonneg (fun α _ => ?_)
  rw [Complex.ofReal_re]
  exact mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

lemma fockInner_self_eq_zero {P : MvPolynomial σ ℂ} (h : FockH1Action.fockInner P P = 0) : P = 0 := by
  have hre : ∑ α ∈ P.support, Complex.normSq (coeff α P) *
      ((α.prod fun _ k => k.factorial : ℕ) : ℝ) = 0 := by
    have h' := congrArg Complex.re h
    rw [fockInner_self, Complex.re_sum] at h'
    simpa only [Complex.ofReal_re, Complex.zero_re] using h'
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun α _ => mul_nonneg (Complex.normSq_nonneg (coeff α P)) (Nat.cast_nonneg _))).mp hre
  by_contra hP
  obtain ⟨α, hα⟩ := Finset.nonempty_iff_ne_empty.mpr (mt MvPolynomial.support_eq_empty.mp hP)
  rcases mul_eq_zero.mp (hterm α hα) with h1 | h1
  · rw [Complex.normSq_eq_zero] at h1
    exact (MvPolynomial.mem_support_iff.mp hα) h1
  · exact absurd h1 (Nat.cast_ne_zero.mpr (wt_pos_nat α).ne')

lemma wt_add_single [Fintype σ] [DecidableEq σ] (β : σ →₀ ℕ) (l : σ) :
    wt (β + Finsupp.single l 1) = ((β l + 1 : ℕ) : ℂ) * wt β := by
  have hw : ∀ γ : σ →₀ ℕ, wt γ = ∏ i, ((γ i).factorial : ℂ) := fun γ =>
    Finsupp.prod_fintype γ _ (fun _ => by simp)
  have key1 : ∏ i, (((β + Finsupp.single l 1 : σ →₀ ℕ) i).factorial : ℂ) =
      (((β + Finsupp.single l 1 : σ →₀ ℕ) l).factorial : ℂ) *
        ∏ i ∈ Finset.univ.erase l, (((β + Finsupp.single l 1 : σ →₀ ℕ) i).factorial : ℂ) := by
    exact (Finset.mul_prod_erase Finset.univ
        (fun i => (((β + Finsupp.single l 1 : σ →₀ ℕ) i).factorial : ℂ)) (Finset.mem_univ l)).symm
  have key2 : ∏ i, ((β i).factorial : ℂ) =
      ((β l).factorial : ℂ) * ∏ i ∈ Finset.univ.erase l, ((β i).factorial : ℂ) := by
    exact (Finset.mul_prod_erase Finset.univ
        (fun i => ((β i).factorial : ℂ)) (Finset.mem_univ l)).symm
  rw [hw, hw, key1, key2]
  have hrest : ∏ i ∈ Finset.univ.erase l, (((β + Finsupp.single l 1 : σ →₀ ℕ) i).factorial : ℂ)
      = ∏ i ∈ Finset.univ.erase l, ((β i).factorial : ℂ) := by
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm (Finset.ne_of_mem_erase hi)),
      add_zero]
  rw [hrest, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  push_cast
  ring

private theorem X_mul_monomial_eq_monomial_add_single (l : σ) (a : σ →₀ ℕ) (c : ℂ) :
    X l * monomial a c = monomial (a + Finsupp.single l 1) c := by
  rw [add_comm]
  rw [MvPolynomial.monomial_single_add, pow_one]

private theorem fockInner_monomial_monomial_self (a : σ →₀ ℕ) (c d : ℂ) :
    FockH1Action.fockInner (monomial a c) (monomial a d) = (starRingEnd ℂ) c * d * wt a := by
  classical
  rw [fockInner_eq_sum_left _ _ {a} support_monomial_subset, Finset.sum_singleton]
  simp [coeff_monomial]

private theorem fockInner_monomial_monomial_of_ne (a b : σ →₀ ℕ) (c d : ℂ) (h : b ≠ a) :
    FockH1Action.fockInner (monomial a c) (monomial b d) = 0 := by
  classical
  rw [fockInner_eq_sum_left _ _ {a} support_monomial_subset, Finset.sum_singleton]
  simp [coeff_monomial, h]

lemma fockInner_X_mul [Fintype σ] (l : σ) (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (X l * P) Q = FockH1Action.fockInner P (pderiv l Q) := by
  classical
  refine MvPolynomial.induction_on' P (fun a c => ?_) (fun P P' hP hP' => ?_)
  · refine MvPolynomial.induction_on' Q (fun b d => ?_) (fun Q Q' hQ hQ' => ?_)
    · rw [X_mul_monomial_eq_monomial_add_single, pderiv_monomial]
      by_cases h : b = a + Finsupp.single l 1
      · subst h
        rw [add_tsub_cancel_right, fockInner_monomial_monomial_self, fockInner_monomial_monomial_self,
          wt_add_single, Finsupp.add_apply, Finsupp.single_eq_same]
        push_cast
        ring
      · rw [fockInner_monomial_monomial_of_ne _ _ _ _ h]
        by_cases hbl : b l = 0
        · rw [hbl, Nat.cast_zero, mul_zero, map_zero, fockInner_zero_right]
        · have hb : b - Finsupp.single l 1 + Finsupp.single l 1 = b := by
            ext i
            by_cases hi : i = l
            · subst hi
              simp
              omega
            · simp [Ne.symm hi]
          have hne : b - Finsupp.single l 1 ≠ a := fun he => h (hb.symm.trans (by rw [he]))
          rw [fockInner_monomial_monomial_of_ne _ _ _ _ hne]
    · rw [fockInner_add_right, map_add, fockInner_add_right, hQ, hQ']
  · rw [mul_add, fockInner_add_left, fockInner_add_left, hP, hP']

lemma fockInner_pderiv [Fintype σ] (l : σ) (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (pderiv l P) Q = FockH1Action.fockInner P (X l * Q) := by
  rw [← fockInner_conj (pderiv l P) Q, ← fockInner_X_mul l Q P, fockInner_conj]

lemma fockInner_hc_left {n : ℕ} (P Q : MvPolynomial σ ℂ) (hQ : Q ∈ FockH1Action.homog σ n) :
    FockH1Action.fockInner (homogeneousComponent n P) Q = FockH1Action.fockInner P Q := by
  have hQ' : Q.IsHomogeneous n := (mem_homogeneousSubmodule _ _).mp hQ
  rw [fockInner_eq_sum_right (homogeneousComponent n P) Q Q.support
      (Finset.Subset.refl _),
    fockInner_eq_sum_right P Q Q.support (Finset.Subset.refl _)]
  refine Finset.sum_congr rfl (fun α hα => ?_)
  have hdeg := hQ' (MvPolynomial.mem_support_iff.mp hα)
  rw [coeff_homogeneousComponent]
  split_ifs with hc
  · rfl
  · exact absurd (by
      first
      | exact hdeg
      | (rw [Finsupp.degree_eq_weight_one]; exact hdeg)) hc

lemma fockInner_hc_right {n : ℕ} (P Q : MvPolynomial σ ℂ) (hP : P ∈ FockH1Action.homog σ n) :
    FockH1Action.fockInner P (homogeneousComponent n Q) = FockH1Action.fockInner P Q := by
  have hP' : P.IsHomogeneous n := (mem_homogeneousSubmodule _ _).mp hP
  rw [fockInner_eq_sum_support_left, fockInner_eq_sum_support_left P Q]
  refine Finset.sum_congr rfl (fun α hα => ?_)
  have hdeg := hP' (MvPolynomial.mem_support_iff.mp hα)
  rw [coeff_homogeneousComponent]
  split_ifs with hc
  · rfl
  · exact absurd (by
      first
      | exact hdeg
      | (rw [Finsupp.degree_eq_weight_one]; exact hdeg)) hc

end PI.FHS
