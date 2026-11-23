import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ExpIndep

noncomputable section

open Polynomial

namespace UpperTheory.V.Z.Inf

private lemma shift_inj {x y : ℂ} (hxy : x ≠ y) {p : ℂ[X]} (h : C x * taylor 1 p - C y * p = 0) : p = 0 := by
  by_contra hp
  have e := congrArg leadingCoeff (sub_eq_zero.mp h)
  rw [leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_C, leadingCoeff_taylor] at e
  exact hxy (mul_right_cancel₀ (leadingCoeff_ne_zero.mpr hp) e)

private lemma shift_lt {x : ℂ} (hx : x ≠ 0) {p : ℂ[X]} (hp : p ≠ 0) :
    (C x * taylor 1 p - C x * p).degree < p.degree := by
  rw [← mul_sub, degree_C_mul hx]
  have hne : taylor 1 p ≠ 0 := fun h0 =>
    hp (degree_eq_bot.mp (by rw [← degree_taylor p 1, h0, degree_zero]))
  have e := degree_sub_lt (degree_taylor p 1) hne (leadingCoeff_taylor 1 p)
  rwa [degree_taylor] at e

private lemma shift_sum (T : Finset ℝ) (P : ℝ → ℂ[X]) (y : ℂ)
    (h : ∀ s : ℂ, ∑ t ∈ T, (P t).eval s * Complex.exp (t * s) = 0) (s : ℂ) :
    ∑ t ∈ T, (C (Complex.exp t) * taylor 1 (P t) - C y * P t).eval s * Complex.exp (t * s) = 0 := by
  simp only [eval_sub, eval_mul, eval_C, taylor_eval, sub_mul, Finset.sum_sub_distrib]
  have e1 : ∑ t ∈ T, Complex.exp t * (P t).eval (s + 1) * Complex.exp (t * s) =
      ∑ t ∈ T, (P t).eval (s + 1) * Complex.exp (t * (s + 1)) :=
    Finset.sum_congr rfl fun t _ => by rw [mul_add, mul_one, Complex.exp_add]; ring
  have e2 : ∑ t ∈ T, y * (P t).eval s * Complex.exp (t * s) =
      y * ∑ t ∈ T, (P t).eval s * Complex.exp (t * s) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e1, e2, h, h, mul_zero, sub_zero]

private lemma indep (T : Finset ℝ) : ∀ (P : ℝ → ℂ[X]),
    (∀ s : ℂ, ∑ t ∈ T, (P t).eval s * Complex.exp (t * s) = 0) → ∀ t ∈ T, P t = 0 := by
  classical
  induction T using Finset.induction_on with
  | empty => intro P _ t ht; simp at ht
  | @insert t0 T' ht0 ih =>
    have zero_case : ∀ P : ℝ → ℂ[X], P t0 = 0 →
        (∀ s : ℂ, ∑ t ∈ insert t0 T', (P t).eval s * Complex.exp (t * s) = 0) →
        ∀ t ∈ insert t0 T', P t = 0 := by
      intro P h0 hP t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact h0
      · refine ih P (fun s => ?_) t ht
        have e := hP s
        rwa [Finset.sum_insert ht0, h0, eval_zero, zero_mul, zero_add] at e
    have main : ∀ n : ℕ, ∀ P : ℝ → ℂ[X], (P t0).natDegree < n →
        (∀ s : ℂ, ∑ t ∈ insert t0 T', (P t).eval s * Complex.exp (t * s) = 0) →
        ∀ t ∈ insert t0 T', P t = 0 := by
      intro n
      induction n with
      | zero => intro P h; exact absurd h (Nat.not_lt_zero _)
      | succ n ihn =>
        intro P hn hP
        by_cases h0 : P t0 = 0
        · exact zero_case P h0 hP
        set Q : ℝ → ℂ[X] := fun t => C (Complex.exp t) * taylor 1 (P t) - C (Complex.exp t0) * P t
          with hQ
        have hQs : ∀ s : ℂ, ∑ t ∈ insert t0 T', (Q t).eval s * Complex.exp (t * s) = 0 :=
          shift_sum _ P _ hP
        have hQ0 : ∀ t ∈ insert t0 T', Q t = 0 := by
          by_cases hq : Q t0 = 0
          · exact zero_case Q hq hQs
          · refine ihn Q ?_ hQs
            have hdeg : (Q t0).degree < (P t0).degree := shift_lt (Complex.exp_ne_zero _) h0
            have := natDegree_lt_natDegree hq hdeg
            omega
        have hT' : ∀ t ∈ T', P t = 0 := by
          intro t ht
          have hne : t ≠ t0 := fun e => ht0 (e ▸ ht)
          refine shift_inj (x := Complex.exp t) (y := Complex.exp t0) ?_
            (hQ0 t (Finset.mem_insert_of_mem ht))
          intro e
          apply hne
          rw [← Complex.ofReal_exp, ← Complex.ofReal_exp] at e
          exact Real.exp_injective (Complex.ofReal_injective e)
        have hP0 : P t0 = 0 := by
          apply Polynomial.funext
          intro s
          have e := hP s
          have hz : ∑ t ∈ T', (P t).eval s * Complex.exp (t * s) = 0 :=
            Finset.sum_eq_zero fun t ht => by rw [hT' t ht, eval_zero, zero_mul]
          rw [Finset.sum_insert ht0, hz, add_zero] at e
          simpa [Complex.exp_ne_zero] using e
        exact zero_case P hP0 hP
    intro P hP
    exact main _ P (Nat.lt_succ_self _) hP

private lemma extend {T S : Finset ℝ} (hTS : T ⊆ S) (a : ℝ → ℂ) (s : ℂ) :
    ∑ t ∈ S, (if t ∈ T then a t else 0) * Complex.exp (t * s) = ∑ t ∈ T, a t * Complex.exp (t * s) := by
  classical
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hTS]

theorem expIndep : ExpIndep := by
  classical
  rintro p q U V ⟨T, a, hU⟩ ⟨T', b, hV⟩ hU0 h
  obtain ⟨t, htT, hat⟩ : ∃ t ∈ T, a t ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hU0 (funext fun s => by
      rw [hU, Pi.zero_apply]
      exact Finset.sum_eq_zero fun t ht => by rw [hc t ht, zero_mul])
  have key := indep (T ∪ T')
    (fun t => C (if t ∈ T then a t else 0) * p - C (if t ∈ T' then b t else 0) * q)
    (fun s => ?_) t (Finset.mem_union_left _ htT)
  · rw [if_pos htT] at key
    exact ⟨a t, _, hat, sub_eq_zero.mp key⟩
  · have e1 := extend (Finset.subset_union_left : T ⊆ T ∪ T') a s
    have e2 := extend (Finset.subset_union_right : T' ⊆ T ∪ T') b s
    rw [← hU] at e1
    rw [← hV] at e2
    simp only [eval_sub, eval_mul, eval_C, sub_mul, Finset.sum_sub_distrib]
    have f1 : ∑ t ∈ T ∪ T', (if t ∈ T then a t else 0) * eval s p * Complex.exp (t * s) =
        eval s p * ∑ t ∈ T ∪ T', (if t ∈ T then a t else 0) * Complex.exp (t * s) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have f2 : ∑ t ∈ T ∪ T', (if t ∈ T' then b t else 0) * eval s q * Complex.exp (t * s) =
        eval s q * ∑ t ∈ T ∪ T', (if t ∈ T' then b t else 0) * Complex.exp (t * s) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [f1, f2, e1, e2, h s, sub_self]

end UpperTheory.V.Z.Inf
