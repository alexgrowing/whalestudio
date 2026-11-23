import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RenVar
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.GrassTop

lemma rel_mem_J {p q k : ℕ} (hk : 1 ≤ k) : rel k ∈ J p q :=
  Ideal.subset_span (Or.inl ⟨k, hk, rfl⟩)

lemma X_zero_sub_one_mem_J {p q : ℕ} (b : Bool) :
    (X (b, 0) - 1 : MvPolynomial (Bool × ℕ) ℝ) ∈ J p q :=
  Ideal.subset_span (Or.inr (Or.inl ⟨b, rfl⟩))

lemma X_true_mem_J {p q k : ℕ} (hk : p < k) : (X (true, k) : MvPolynomial (Bool × ℕ) ℝ) ∈ J p q :=
  Ideal.subset_span (Or.inr (Or.inr (Or.inl ⟨k, hk, rfl⟩)))

lemma X_false_mem_J {p q k : ℕ} (hk : q < k) : (X (false, k) : MvPolynomial (Bool × ℕ) ℝ) ∈ J p q :=
  Ideal.subset_span (Or.inr (Or.inr (Or.inr ⟨k, hk, rfl⟩)))

lemma mem_of_neg_one_pow_mul {I : Ideal (MvPolynomial (Bool × ℕ) ℝ)} {x : MvPolynomial (Bool × ℕ) ℝ}
    (n : ℕ) (h : C ((-1 : ℝ) ^ n) * x ∈ I) : x ∈ I := by
  have := I.mul_mem_left (C ((-1 : ℝ) ^ n)) h
  rwa [← mul_assoc, ← C_mul, ← mul_pow, neg_one_mul, neg_neg, one_pow, C_1, one_mul] at this

lemma X_mul_X_mem_J {p q : ℕ} (hpq : 1 ≤ p + q) :
    (X (true, p) * X (false, q) : MvPolynomial (Bool × ℕ) ℝ) ∈ J p q := by
  have hrel := rel_mem_J (p := p) (q := q) hpq
  have hp : p ∈ Finset.range (p + q + 1) := Finset.mem_range.2 (by omega)
  rw [rel, ← Finset.add_sum_erase _ _ hp] at hrel
  have hrest : (∑ a ∈ (Finset.range (p + q + 1)).erase p,
      C ((-1 : ℝ) ^ (p + q - a)) * X (true, a) * X (false, p + q - a)) ∈ J p q := by
    refine Ideal.sum_mem _ fun a ha => ?_
    have hap := Finset.ne_of_mem_erase ha
    rcases lt_or_gt_of_ne hap with h | h
    · exact (J p q).mul_mem_left _ (X_false_mem_J (by omega))
    · exact (J p q).mul_mem_right _ ((J p q).mul_mem_left _ (X_true_mem_J h))
  have := (J p q).sub_mem hrel hrest
  rw [add_sub_cancel_right, Nat.add_sub_cancel_left, mul_assoc] at this
  exact mem_of_neg_one_pow_mul q this

lemma sub_C_eval_mem {I : Ideal (MvPolynomial (Bool × ℕ) ℝ)} (v : Bool × ℕ → ℝ)
    (hv : ∀ y, X y - C (v y) ∈ I) (P : MvPolynomial (Bool × ℕ) ℝ) : P - C (eval v P) ∈ I := by
  refine MvPolynomial.induction_on (motive := fun P => P - C (eval v P) ∈ I) P (fun a => ?_) (fun P Q hP hQ => ?_) (fun P y hP => ?_)
  · simp
  · have := I.add_mem hP hQ
    convert this using 1
    simp only [map_add]; ring
  · have := I.add_mem (I.mul_mem_right (X y) hP) (I.mul_mem_left (C (eval v P)) (hv y))
    convert this using 1
    simp only [map_mul, eval_X]; ring

lemma X_false_mem_J_zero {q k : ℕ} (hk : 1 ≤ k) : (X (false, k) : MvPolynomial (Bool × ℕ) ℝ) ∈ J 0 q := by
  have hrel := rel_mem_J (p := 0) (q := q) hk
  rw [rel, Finset.sum_range_succ'] at hrel
  have hrest : (∑ i ∈ Finset.range k,
      C ((-1 : ℝ) ^ (k - (i + 1))) * X (true, i + 1) * X (false, k - (i + 1))) ∈ J 0 q :=
    Ideal.sum_mem _ fun i _ => (J 0 q).mul_mem_right _ ((J 0 q).mul_mem_left _ (X_true_mem_J (by omega)))
  have h0 := (J 0 q).sub_mem hrel hrest
  rw [add_sub_cancel_left, Nat.sub_zero] at h0
  have h1 := (J 0 q).sub_mem h0
    ((J 0 q).mul_mem_right (C ((-1 : ℝ) ^ k) * X (false, k)) (X_zero_sub_one_mem_J true))
  refine mem_of_neg_one_pow_mul k ?_
  convert h1 using 1
  ring

lemma X_true_mem_J_zero {p k : ℕ} (hk : 1 ≤ k) : (X (true, k) : MvPolynomial (Bool × ℕ) ℝ) ∈ J p 0 := by
  have hrel := rel_mem_J (p := p) (q := 0) hk
  rw [rel, Finset.sum_range_succ] at hrel
  have hrest : (∑ a ∈ Finset.range k,
      C ((-1 : ℝ) ^ (k - a)) * X (true, a) * X (false, k - a)) ∈ J p 0 :=
    Ideal.sum_mem _ fun a ha => (J p 0).mul_mem_left _ (X_false_mem_J (by simp at ha; omega))
  have h0 := (J p 0).sub_mem hrel hrest
  rw [add_sub_cancel_left, Nat.sub_self, pow_zero, C_1, one_mul] at h0
  have h1 := (J p 0).sub_mem h0 ((J p 0).mul_mem_left (X (true, k)) (X_zero_sub_one_mem_J false))
  convert h1 using 1
  ring

lemma hv_zero_left (q : ℕ) (y : Bool × ℕ) :
    X y - C (if y.2 = 0 then (1 : ℝ) else 0) ∈ J 0 q := by
  obtain ⟨b, k⟩ := y
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using X_zero_sub_one_mem_J (p := 0) (q := q) b
  · simp only [show k ≠ 0 by omega, if_false, C_0, sub_zero]
    cases b
    · exact X_false_mem_J_zero hk
    · exact X_true_mem_J hk

lemma hv_zero_right (p : ℕ) (y : Bool × ℕ) :
    X y - C (if y.2 = 0 then (1 : ℝ) else 0) ∈ J p 0 := by
  obtain ⟨b, k⟩ := y
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using X_zero_sub_one_mem_J (p := p) (q := 0) b
  · simp only [show k ≠ 0 by omega, if_false, C_0, sub_zero]
    cases b
    · exact X_false_mem_J hk
    · exact X_true_mem_J_zero hk

lemma base_left (q : ℕ) (h : MvPolynomial (Bool × ℕ) ℝ) :
    h ∈ (J 0 q).restrictScalars ℝ ⊔ Submodule.span ℝ (basis 0 q) := by
  have h1 := sub_C_eval_mem (fun y => if y.2 = 0 then (1 : ℝ) else 0) (hv_zero_left q) h
  set c := eval (fun y : Bool × ℕ => if y.2 = 0 then (1 : ℝ) else 0) h
  have hpow : (1 : MvPolynomial (Bool × ℕ) ℝ) - X (true, 0) ^ q ∈ J 0 q := by
    obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow (X (true, 0) : MvPolynomial (Bool × ℕ) ℝ) 1 q
    rw [one_pow] at hd
    have := (J 0 q).mul_mem_right d (X_zero_sub_one_mem_J true)
    rw [← hd] at this
    simpa using (J 0 q).neg_mem this
  have hdecomp : h = (h - C c + C c * (1 - X (true, 0) ^ q)) + c • X (true, 0) ^ q := by
    rw [smul_eq_C_mul]; ring
  rw [hdecomp]
  refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · rw [Submodule.restrictScalars_mem]
    exact (J 0 q).add_mem h1 ((J 0 q).mul_mem_left _ hpow)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr rfl))

lemma base_right (p : ℕ) (h : MvPolynomial (Bool × ℕ) ℝ) :
    h ∈ (J p 0).restrictScalars ℝ ⊔ Submodule.span ℝ (basis p 0) := by
  have h1 := sub_C_eval_mem (fun y => if y.2 = 0 then (1 : ℝ) else 0) (hv_zero_right p) h
  set c := eval (fun y : Bool × ℕ => if y.2 = 0 then (1 : ℝ) else 0) h
  have hdecomp : h = (h - C c) + c • X (true, p) ^ 0 := by
    rw [pow_zero, smul_eq_C_mul, mul_one]; ring
  rw [hdecomp]
  refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · rwa [Submodule.restrictScalars_mem]
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr rfl))

lemma J_le_succ_left (p q : ℕ) :
    J p q ≤ J (p + 1) q ⊔ Ideal.span {(X (true, p + 1) : MvPolynomial (Bool × ℕ) ℝ)} := by
  refine Ideal.span_le.2 ?_
  rintro f (⟨k, hk, rfl⟩ | ⟨b, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
  · exact Ideal.mem_sup_left (rel_mem_J hk)
  · exact Ideal.mem_sup_left (X_zero_sub_one_mem_J b)
  · rcases Nat.lt_or_ge (p + 1) k with h | h
    · exact Ideal.mem_sup_left (X_true_mem_J h)
    · obtain rfl : k = p + 1 := by omega
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  · exact Ideal.mem_sup_left (X_false_mem_J hk)

lemma J_le_succ_right (p q : ℕ) :
    J p q ≤ J p (q + 1) ⊔ Ideal.span {(X (false, q + 1) : MvPolynomial (Bool × ℕ) ℝ)} := by
  refine Ideal.span_le.2 ?_
  rintro f (⟨k, hk, rfl⟩ | ⟨b, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
  · exact Ideal.mem_sup_left (rel_mem_J hk)
  · exact Ideal.mem_sup_left (X_zero_sub_one_mem_J b)
  · exact Ideal.mem_sup_left (X_true_mem_J hk)
  · rcases Nat.lt_or_ge (q + 1) k with h | h
    · exact Ideal.mem_sup_left (X_false_mem_J h)
    · obtain rfl : k = q + 1 := by omega
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)

lemma wt_add_single (d : Bool × ℕ →₀ ℕ) (y : Bool × ℕ) :
    wt (d + Finsupp.single y 1) = wt d + y.2 := by
  unfold wt
  rw [Finsupp.sum_add_index' (fun _ => mul_zero _) (fun _ _ _ => mul_add _ _ _),
    Finsupp.sum_single_index (mul_zero _), mul_one]

lemma wt_single (y : Bool × ℕ) (n : ℕ) : wt (Finsupp.single y n) = y.2 * n := by
  unfold wt
  rw [Finsupp.sum_single_index (mul_zero _)]

lemma basis_subset_succ_left (p q : ℕ) : basis p (q + 1) ⊆ basis (p + 1) (q + 1) := by
  rintro f (⟨d, hd, rfl⟩ | rfl)
  · exact Or.inl ⟨d, lt_of_lt_of_le hd (Nat.mul_le_mul_right _ (Nat.le_succ p)), rfl⟩
  · refine Or.inl ⟨Finsupp.single (true, p) (q + 1), ?_, X_pow_eq_monomial⟩
    rw [wt_single]
    show p * (q + 1) < (p + 1) * (q + 1)
    nlinarith

lemma X_mul_span_basis (p q : ℕ) {s : MvPolynomial (Bool × ℕ) ℝ}
    (hs : s ∈ Submodule.span ℝ (basis (p + 1) q)) :
    X (true, p + 1) * s ∈ Submodule.span ℝ (basis (p + 1) (q + 1)) := by
  induction hs using Submodule.span_induction with
  | mem x hx =>
    apply Submodule.subset_span
    rcases hx with ⟨d, hd, rfl⟩ | rfl
    · refine Or.inl ⟨d + Finsupp.single (true, p + 1) 1, ?_, ?_⟩
      · rw [wt_add_single]
        show wt d + (p + 1) < (p + 1) * (q + 1)
        nlinarith
      · rw [add_comm d, monomial_single_add, pow_one]
    · exact Or.inr (by rw [pow_succ'])
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ a hx

lemma X_mul_mem (p q : ℕ) (f : MvPolynomial (Bool × ℕ) ℝ)
    (hf : f ∈ (J (p + 1) q).restrictScalars ℝ ⊔ Submodule.span ℝ (basis (p + 1) q)) :
    X (true, p + 1) * f ∈
      (J (p + 1) (q + 1)).restrictScalars ℝ ⊔ Submodule.span ℝ (basis (p + 1) (q + 1)) := by
  obtain ⟨j, hj, s, hs, rfl⟩ := Submodule.mem_sup.1 hf
  rw [mul_add]
  refine Submodule.add_mem _ (Submodule.mem_sup_left ?_)
    (Submodule.mem_sup_right (X_mul_span_basis p q hs))
  rw [Submodule.restrictScalars_mem] at hj ⊢
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (J_le_succ_right (p + 1) q hj)
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
  have hXX := X_mul_X_mem_J (p := p + 1) (q := q + 1) (by omega)
  have : X (true, p + 1) * (a + c * X (false, q + 1)) =
      X (true, p + 1) * a + c * (X (true, p + 1) * X (false, q + 1)) := by ring
  rw [this]
  exact (J _ _).add_mem ((J _ _).mul_mem_left _ ha) ((J _ _).mul_mem_left _ hXX)

theorem mem_rel_sup_span_low_or_top : ∀ (p q : ℕ) (h : MvPolynomial (Bool × ℕ) ℝ),
    h ∈ (J p q).restrictScalars ℝ ⊔ Submodule.span ℝ (basis p q) := by
  intro p
  induction p with
  | zero => exact base_left
  | succ p ihp =>
    intro q
    induction q with
    | zero => exact base_right (p + 1)
    | succ q ihq =>
      intro h
      obtain ⟨j, hj, s, hs, rfl⟩ := Submodule.mem_sup.1 (ihp (q + 1) h)
      rw [Submodule.restrictScalars_mem] at hj
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (J_le_succ_left p (q + 1) hj)
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
      refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.mem_sup_left ?_) ?_)
        (Submodule.mem_sup_right ?_)
      · rwa [Submodule.restrictScalars_mem]
      · rw [mul_comm]; exact X_mul_mem p q c (ihq c)
      · exact Submodule.span_mono (basis_subset_succ_left p q) hs

end GlobalTheory.GrassTop
