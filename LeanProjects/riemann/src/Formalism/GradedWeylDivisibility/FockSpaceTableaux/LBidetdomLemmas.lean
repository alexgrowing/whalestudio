import Formalism.GradedWeylDivisibility.StatementA

open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem support_prod_le_of_additive {σ ι R : Type*} [CommSemiring R] [DecidableEq ι] [DecidableEq σ]
    (F : (σ →₀ ℕ) → ℕ) (hF0 : F 0 = 0) (hFa : ∀ a b, F (a + b) = F a + F b)
    (s : Finset ι) (f : ι → MvPolynomial σ R) (b : ι → ℕ)
    (hb : ∀ i ∈ s, ∀ m ∈ (f i).support, F m ≤ b i) :
    ∀ m ∈ (∏ i ∈ s, f i).support, F m ≤ ∑ i ∈ s, b i := by
  induction s using Finset.induction_on with
  | empty =>
    intro m hm
    rw [Finset.prod_empty, mem_support_iff, coeff_one] at hm
    split_ifs at hm with h
    · subst h; simp [hF0]
    · exact absurd rfl hm
  | insert i s hi ih =>
    intro m hm
    rw [Finset.prod_insert hi] at hm
    obtain ⟨a, ha, c, hc, rfl⟩ := Finset.mem_add.mp (support_mul _ _ hm)
    rw [hFa, Finset.sum_insert hi]
    exact Nat.add_le_add (hb i (mem_insert_self _ _) a ha)
      (ih (fun j hj => hb j (mem_insert_of_mem hj)) c hc)

theorem support_prod_eq_of_additive {σ ι R : Type*} [CommSemiring R] [DecidableEq ι] [DecidableEq σ]
    (F : (σ →₀ ℕ) → ℕ) (hF0 : F 0 = 0) (hFa : ∀ a b, F (a + b) = F a + F b)
    (s : Finset ι) (f : ι → MvPolynomial σ R) (b : ι → ℕ)
    (hb : ∀ i ∈ s, ∀ m ∈ (f i).support, F m = b i) :
    ∀ m ∈ (∏ i ∈ s, f i).support, F m = ∑ i ∈ s, b i := by
  induction s using Finset.induction_on with
  | empty =>
    intro m hm
    rw [Finset.prod_empty, mem_support_iff, coeff_one] at hm
    split_ifs at hm with h
    · subst h; simp [hF0]
    · exact absurd rfl hm
  | insert i s hi ih =>
    intro m hm
    rw [Finset.prod_insert hi] at hm
    obtain ⟨a, ha, c, hc, rfl⟩ := Finset.mem_add.mp (support_mul _ _ hm)
    rw [hFa, Finset.sum_insert hi, hb i (mem_insert_self _ _) a ha,
      ih (fun j hj => hb j (mem_insert_of_mem hj)) c hc]

theorem rowDeg_add {r n : ℕ} (m m' : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    rowDeg (m + m') a = rowDeg m a + rowDeg m' a := by
  simp [rowDeg, Finset.sum_add_distrib]

theorem rowDeg_zero {r n : ℕ} (a : Fin r) : rowDeg (0 : Fin r × Fin n →₀ ℕ) a = 0 := by
  simp [rowDeg]

theorem rowDeg_single {r n : ℕ} (b a : Fin r) (s : Fin n) :
    rowDeg (Finsupp.single (b, s) 1) a = if b = a then 1 else 0 := by
  classical
  unfold rowDeg
  simp only [Finsupp.single_apply, Prod.mk.injEq]
  by_cases h : b = a
  · subst h; simp
  · simp [h]

def rowPart {r n : ℕ} (k : ℕ) (m : Fin r × Fin n →₀ ℕ) : ℕ :=
  ∑ a : Fin r with a.val < k, rowDeg m a

theorem rowPart_zero {r n : ℕ} (k : ℕ) : rowPart k (0 : Fin r × Fin n →₀ ℕ) = 0 := by
  simp [rowPart, rowDeg_zero]

theorem rowPart_add {r n : ℕ} (k : ℕ) (m m' : Fin r × Fin n →₀ ℕ) :
    rowPart k (m + m') = rowPart k m + rowPart k m' := by
  simp [rowPart, rowDeg_add, Finset.sum_add_distrib]

theorem rowPart_single {r n : ℕ} (k : ℕ) (b : Fin r) (s : Fin n) :
    rowPart k (Finsupp.single (b, s) 1 : Fin r × Fin n →₀ ℕ) = if b.val < k then 1 else 0 := by
  classical
  unfold rowPart
  simp only [rowDeg_single]
  rw [Finset.sum_ite_eq]
  simp

def rowTot {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) : ℕ := ∑ a : Fin r, rowDeg m a

theorem rowTot_zero {r n : ℕ} : rowTot (0 : Fin r × Fin n →₀ ℕ) = 0 := by
  simp [rowTot, rowDeg_zero]

theorem rowTot_add {r n : ℕ} (m m' : Fin r × Fin n →₀ ℕ) :
    rowTot (m + m') = rowTot m + rowTot m' := by
  simp [rowTot, rowDeg_add, Finset.sum_add_distrib]

theorem rowTot_single {r n : ℕ} (b : Fin r) (s : Fin n) :
    rowTot (Finsupp.single (b, s) 1 : Fin r × Fin n →₀ ℕ) = 1 := by
  classical
  unfold rowTot
  simp only [rowDeg_single]
  simp

theorem support_X_subset' {σ R : Type*} [CommSemiring R] (v : σ) :
    (X v : MvPolynomial σ R).support ⊆ {Finsupp.single v 1} :=
  support_monomial_subset

theorem initMinor_term_support {R : Type*} [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n)
    (σ : Equiv.Perm (Fin s)) (m : Fin r × Fin n →₀ ℕ)
    (hm : m ∈ (∏ i : Fin s, (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin r × Fin n) R)).support) :
    (∀ k, rowPart k m = #{p : Fin s | (I p).val < k}) ∧ rowTot m = s := by
  classical
  constructor
  · intro k
    have h := support_prod_eq_of_additive (rowPart k) (rowPart_zero k) (rowPart_add k) Finset.univ
      (fun i : Fin s => (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin r × Fin n) R))
      (fun i => if (I (σ i)).val < k then 1 else 0)
      (by
        intro i _ m' hm'
        have := support_X_subset' (R := R) _ hm'
        rw [Finset.mem_singleton] at this
        subst this
        exact rowPart_single k _ _) m hm
    rw [h, Equiv.sum_comp σ (fun p => if (I p).val < k then 1 else 0), Finset.sum_boole]
    simp
  · have h := support_prod_eq_of_additive rowTot rowTot_zero rowTot_add Finset.univ
      (fun i : Fin s => (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin r × Fin n) R))
      (fun _ => 1)
      (by
        intro i _ m' hm'
        have := support_X_subset' (R := R) _ hm'
        rw [Finset.mem_singleton] at this
        subst this
        exact rowTot_single _ _) m hm
    rw [h]; simp

theorem initMinor_support {R : Type*} [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n)
    (m : Fin r × Fin n →₀ ℕ) (hm : m ∈ (initMinor R I hs).support) :
    (∀ k, rowPart k m ≤ min k s) ∧ rowTot m = s := by
  classical
  by_cases hI : Function.Injective I
  · unfold initMinor at hm
    rw [Matrix.det_apply] at hm
    have h1 := support_sum hm
    rw [Finset.mem_biUnion] at h1
    obtain ⟨σ, -, hσ⟩ := h1
    rw [Units.smul_def] at hσ
    have hσ' := support_smul hσ
    simp only [Matrix.of_apply] at hσ'
    obtain ⟨hp, ht⟩ := initMinor_term_support I hs σ m hσ'
    refine ⟨fun k => ?_, ht⟩
    rw [hp k]
    refine le_min ?_ ?_
    · calc #{p : Fin s | (I p).val < k} ≤ #{a : Fin r | a.val < k} := by
            apply Finset.card_le_card_of_injOn I
            · intro p hp'
              simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hp' ⊢
              exact hp'
            · intro p _ q _ h; exact hI h
        _ = min r k := Fin.card_filter_val_lt
        _ ≤ k := min_le_right _ _
    · calc #{p : Fin s | (I p).val < k} ≤ #(Finset.univ : Finset (Fin s)) := Finset.card_filter_le _ _
        _ = s := by simp
  · exfalso
    simp only [Function.Injective, not_forall] at hI
    obtain ⟨p, q, hpq, hne⟩ := hI
    have h0 : initMinor R I hs = 0 := by
      unfold initMinor
      apply Matrix.det_zero_of_row_eq hne
      funext j
      simp [hpq]
    rw [h0, support_zero] at hm
    exact Finset.notMem_empty _ hm

theorem sum_min_eq_shapeDeg {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (k : ℕ) :
    ∑ k' : Fin K, min k (sz k') = ∑ t : Fin n with t.val < k, shapeDeg sz t := by
  classical
  unfold shapeDeg
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k' _
  rw [Finset.sum_boole, Finset.filter_filter]
  have e : #{t : Fin n | t.val < k ∧ t.val < sz k'} = #{t : Fin n | t.val < min k (sz k')} := by
    congr 1; ext t; simp [lt_min_iff]
  rw [Nat.cast_id, e, Fin.card_filter_val_lt]
  have := hsz k'
  omega

end Formalism.GradedWeylDivisibility
