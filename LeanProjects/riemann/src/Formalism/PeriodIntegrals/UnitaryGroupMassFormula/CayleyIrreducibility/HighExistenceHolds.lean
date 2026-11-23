import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CayleyIrreducibility.DivClosedOf

noncomputable section

namespace Formalism.L2.SG.Pf.ColDictValCPf

open MvPolynomial

section Grade

variable {σ : Type*}

def TGood (w : σ → ℕ) (c d : ℕ) (F : Polynomial (MvPolynomial σ ℂ)) : Prop :=
  ∀ j m, coeff m (F.coeff j) ≠ 0 → Finsupp.weight w m + j * c = d

theorem tgood_CC (w : σ → ℕ) (c : ℕ) (r : ℂ) : TGood w c 0 (Polynomial.C (C r)) := by
  classical
  intro j m h
  rw [Polynomial.coeff_C] at h
  by_cases hj : j = 0
  · subst hj
    rw [if_pos rfl, coeff_C] at h
    by_cases hm : 0 = m
    · subst hm; simp
    · rw [if_neg hm] at h; exact absurd rfl h
  · rw [if_neg hj, coeff_zero] at h; exact absurd rfl h

theorem tgood_mul (w : σ → ℕ) (c : ℕ) {d₁ d₂ : ℕ} {F G : Polynomial (MvPolynomial σ ℂ)}
    (hF : TGood w c d₁ F) (hG : TGood w c d₂ G) : TGood w c (d₁ + d₂) (F * G) := by
  classical
  intro j m h
  rw [Polynomial.coeff_mul, coeff_sum] at h
  obtain ⟨x, hx, hx0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [coeff_mul] at hx0
  obtain ⟨y, hy, hy0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx0
  have h1 := hF x.1 y.1 (left_ne_zero_of_mul hy0)
  have h2 := hG x.2 y.2 (right_ne_zero_of_mul hy0)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx hy
  rw [← hx, ← hy, map_add, ← h1, ← h2]
  ring

theorem tgood_one (w : σ → ℕ) (c : ℕ) : TGood w c 0 (1 : Polynomial (MvPolynomial σ ℂ)) := by
  have := tgood_CC w c 1
  rwa [C_1, Polynomial.C_1] at this

theorem tgood_pow (w : σ → ℕ) (c : ℕ) {d : ℕ} {F : Polynomial (MvPolynomial σ ℂ)}
    (hF : TGood w c d F) (k : ℕ) : TGood w c (k * d) (F ^ k) := by
  induction k with
  | zero => rw [pow_zero, zero_mul]; exact tgood_one w c
  | succ k ih => rw [pow_succ, Nat.succ_mul]; exact tgood_mul w c ih hF

theorem tgood_prod {α : Type*} (w : σ → ℕ) (c : ℕ) (s : Finset α) (d : α → ℕ)
    (F : α → Polynomial (MvPolynomial σ ℂ)) (h : ∀ i ∈ s, TGood w c (d i) (F i)) :
    TGood w c (∑ i ∈ s, d i) (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact tgood_one w c
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact tgood_mul w c (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem tgood_aeval_monomial (w : σ → ℕ) (c : ℕ) (f : σ → Polynomial (MvPolynomial σ ℂ))
    (hf : ∀ v, TGood w c (w v) (f v)) (m : σ →₀ ℕ) (r : ℂ) :
    TGood w c (Finsupp.weight w m) (aeval f (monomial m r)) := by
  rw [aeval_monomial, Finsupp.weight_apply, Finsupp.prod, Finsupp.sum, Polynomial.algebraMap_apply,
    MvPolynomial.algebraMap_eq]
  have h1 := tgood_CC w c r
  have h2 := tgood_prod w c m.support (fun i => m i • w i) (fun i => f i ^ m i)
    (fun i _ => by simpa only [smul_eq_mul] using tgood_pow w c (hf i) (m i))
  have := tgood_mul w c h1 h2
  rwa [zero_add] at this

theorem aeval_support (w : σ → ℕ) (c : ℕ) (f : σ → Polynomial (MvPolynomial σ ℂ))
    (hf : ∀ v, TGood w c (w v) (f v)) (P : MvPolynomial σ ℂ) (j : ℕ) (m' : σ →₀ ℕ)
    (h : coeff m' ((aeval f P).coeff j) ≠ 0) :
    ∃ m, coeff m P ≠ 0 ∧ Finsupp.weight w m' + j * c = Finsupp.weight w m := by
  rw [P.as_sum, map_sum, Polynomial.finsetSum_coeff, coeff_sum] at h
  obtain ⟨m, hm, hm0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨m, mem_support_iff.mp hm, tgood_aeval_monomial w c f hf m _ j m' hm0⟩

end Grade

theorem tgood_gen {ι : Type} [DecidableEq ι] {n : ℕ} (τ : ι) (a b : Fin n) (hab : a < b)
    (v : ι × Fin n × Fin n) :
    TGood (fun v : ι × Fin n × Fin n => (v.2.1 : ℕ)) ((b : ℕ) - a) (v.2.1 : ℕ)
      (Polynomial.C (X v) + (if v.1 = τ ∧ v.2.1 = b then Polynomial.X * Polynomial.C (X (τ, a, v.2.2))
        else 0)) := by
  classical
  intro j m h
  rw [Polynomial.coeff_add, coeff_add] at h
  by_cases hj : j = 0
  · subst hj
    have h0 : coeff m ((if v.1 = τ ∧ v.2.1 = b then Polynomial.X * Polynomial.C (X (τ, a, v.2.2))
        else 0 : Polynomial (MvPolynomial (ι × Fin n × Fin n) ℂ)).coeff 0) = 0 := by
      split_ifs <;> simp
    rw [h0, add_zero, Polynomial.coeff_C_zero, coeff_X] at h
    by_cases hm : Finsupp.single v 1 = m
    · subst hm; simp [Finsupp.weight_single]
    · rw [if_neg hm] at h; exact absurd rfl h
  · rw [Polynomial.coeff_C, if_neg hj, coeff_zero, zero_add] at h
    by_cases hc : v.1 = τ ∧ v.2.1 = b
    · rw [if_pos hc, Polynomial.X_mul_C, Polynomial.coeff_C_mul_X] at h
      by_cases hj1 : j = 1
      · subst hj1
        rw [if_pos rfl, coeff_X] at h
        by_cases hm : Finsupp.single (τ, a, v.2.2) 1 = m
        · subst hm
          rw [Finsupp.weight_single, smul_eq_mul, one_mul, one_mul]
          have hb : (v.2.1 : ℕ) = b := congrArg Fin.val hc.2
          have hab' : (a : ℕ) < b := hab
          dsimp only
          omega
        · rw [if_neg hm] at h; exact absurd rfl h
      · rw [if_neg hj1, coeff_zero] at h; exact absurd rfl h
    · rw [if_neg hc, Polynomial.coeff_zero, coeff_zero] at h; exact absurd rfl h

theorem bigDiv_support {ι : Type} [DecidableEq ι] {n : ℕ} (τ : ι) (a b : Fin n) (hab : a < b) (k : ℕ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (m' : ι × Fin n × Fin n →₀ ℕ)
    (h : coeff m' (bigDiv τ a b k P) ≠ 0) :
    ∃ m, coeff m P ≠ 0 ∧ Finsupp.weight (fun v : ι × Fin n × Fin n => (v.2.1 : ℕ)) m' + k * ((b : ℕ) - a)
      = Finsupp.weight (fun v : ι × Fin n × Fin n => (v.2.1 : ℕ)) m :=
  aeval_support _ _ _ (tgood_gen τ a b hab) P k m' h

theorem high_existence_holds : HiEx := by
  intro ι _ _ n M hM hne
  classical
  have key : ∀ e : ℕ, ∀ P ∈ M, P ≠ 0 →
      (∀ m, coeff m P ≠ 0 → Finsupp.weight (fun v : ι × Fin n × Fin n => (v.2.1 : ℕ)) m < e) →
      ∃ Q ∈ M, Q ≠ 0 ∧ ∀ (τ : ι) (a b : Fin n), a < b → ∀ k, 1 ≤ k → bigDiv τ a b k Q = 0 := by
    intro e
    induction e with
    | zero =>
      intro P _ hP0 hb
      obtain ⟨m, hm⟩ := ne_zero_iff.mp hP0
      exact absurd (hb m hm) (Nat.not_lt_zero _)
    | succ e ih =>
      intro P hPM hP0 hb
      by_cases hall : ∀ (τ : ι) (a b : Fin n), a < b → ∀ k, 1 ≤ k → bigDiv τ a b k P = 0
      · exact ⟨P, hPM, hP0, hall⟩
      · push Not at hall
        obtain ⟨τ, a, b, hab, k, hk, hQ⟩ := hall
        refine ih _ (hM τ a b k P hPM) hQ ?_
        intro m' hm'
        obtain ⟨m, hm, heq⟩ := bigDiv_support τ a b hab k P m' hm'
        have h1 := hb m hm
        have hab' : (a : ℕ) < b := hab
        have h2 : 1 ≤ k * ((b : ℕ) - a) :=
          Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
        generalize k * ((b : ℕ) - a) = t at heq h2
        omega
  obtain ⟨P, hPM, hP0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact key (P.support.sup (Finsupp.weight (fun v : ι × Fin n × Fin n => (v.2.1 : ℕ))) + 1) P hPM hP0
    fun m hm => Nat.lt_succ_of_le (Finset.le_sup (mem_support_iff.mpr hm))

end Formalism.L2.SG.Pf.ColDictValCPf
