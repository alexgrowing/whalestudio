import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def oppCount (ε : Fin n → Bool) (a : Fin n) : ℕ := (univ.filter fun b => ε b ≠ ε a).card

theorem dot_root_right (u : Fin n → ℝ) (a b : Fin n) : dot u (root a b) = u a - u b := by
  simp [dot, root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply, mul_boole]

theorem dot_sum_root_right (u : Fin n → ℝ) (Ph : Finset (Fin n × Fin n)) :
    dot u (∑ x ∈ Ph, root x.1 x.2) = ∑ x ∈ Ph, (u x.1 - u x.2) := by
  have h := fun x : Fin n × Fin n => dot_root_right u x.1 x.2
  simp only [dot] at h ⊢
  simp only [Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => h x

theorem oppCount_add (ε : Fin n → Bool) {a b : Fin n} (hab : ε a ≠ ε b) :
    (oppCount ε a : ℝ) + oppCount ε b = n := by
  have key : oppCount ε a + oppCount ε b = n := by
    unfold oppCount
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    have hc : ∀ c : Fin n, ((if ε c ≠ ε a then 1 else 0) + (if ε c ≠ ε b then 1 else 0) : ℕ) = 1 := by
      intro c
      revert hab
      cases ε a <;> cases ε b <;> cases ε c <;> simp
    simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  exact_mod_cast key

theorem sum_root_apply (Ph : Finset (Fin n × Fin n)) (c : Fin n) :
    (∑ x ∈ Ph, root x.1 x.2) c =
      ((Ph.filter fun x => x.1 = c).card : ℝ) - ((Ph.filter fun x => x.2 = c).card : ℝ) := by
  rw [Finset.sum_apply]
  simp only [root, Pi.sub_apply, Finset.sum_sub_distrib, Finset.card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : x.1 = c
    · rw [h]; simp
    · have h' : ¬ c = x.1 := fun e => h e.symm
      simp [Pi.single_apply, h, h']
  · refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : x.2 = c
    · rw [h]; simp
    · have h' : ¬ c = x.2 := fun e => h e.symm
      simp [Pi.single_apply, h, h']

theorem card_fst_le (ε : Fin n → Bool) (Ph : Finset (Fin n × Fin n))
    (hnc : ∀ x ∈ Ph, ε x.1 ≠ ε x.2) (c : Fin n) :
    (Ph.filter fun x => x.1 = c).card ≤ oppCount ε c := by
  unfold oppCount
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have h1 := hnc x hx.1
    rw [hx.2] at h1
    exact Ne.symm h1
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter] at hx hy
    exact Prod.ext (hx.2.trans hy.2.symm) hxy

theorem card_snd_le (ε : Fin n → Bool) (Ph : Finset (Fin n × Fin n))
    (hnc : ∀ x ∈ Ph, ε x.1 ≠ ε x.2) (c : Fin n) :
    (Ph.filter fun x => x.2 = c).card ≤ oppCount ε c := by
  unfold oppCount
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have h1 := hnc x hx.1
    rw [hx.2] at h1
    exact h1
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter] at hx hy
    exact Prod.ext hxy (hx.2.trans hy.2.symm)

theorem nsq_sum_root_le (ε : Fin n → Bool) (Ph : Finset (Fin n × Fin n))
    (hnc : ∀ x ∈ Ph, ε x.1 ≠ ε x.2) :
    nsq (∑ x ∈ Ph, root x.1 x.2) ≤ n * Ph.card := by
  have hpt : ∀ c, (∑ x ∈ Ph, root x.1 x.2) c * (∑ x ∈ Ph, root x.1 x.2) c ≤
      (((Ph.filter fun x => x.1 = c).card : ℝ) + ((Ph.filter fun x => x.2 = c).card : ℝ)) *
        (oppCount ε c : ℝ) := by
    intro c
    rw [sum_root_apply]
    have h1 : ((Ph.filter fun x => x.1 = c).card : ℝ) ≤ oppCount ε c := by
      exact_mod_cast card_fst_le ε Ph hnc c
    have h2 : ((Ph.filter fun x => x.2 = c).card : ℝ) ≤ oppCount ε c := by
      exact_mod_cast card_snd_le ε Ph hnc c
    have h3 : (0 : ℝ) ≤ ((Ph.filter fun x => x.1 = c).card : ℝ) := Nat.cast_nonneg _
    have h4 : (0 : ℝ) ≤ ((Ph.filter fun x => x.2 = c).card : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg h3 h4, mul_le_mul_of_nonneg_left h1 h3, mul_le_mul_of_nonneg_left h2 h4]
  have hfib : ∀ g : Fin n × Fin n → Fin n,
      ∑ c, ((Ph.filter fun x => g x = c).card : ℝ) * (oppCount ε c : ℝ) =
        ∑ x ∈ Ph, (oppCount ε (g x) : ℝ) := by
    intro g
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      Finset.sum_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp
  calc nsq (∑ x ∈ Ph, root x.1 x.2)
        = ∑ c, (∑ x ∈ Ph, root x.1 x.2) c * (∑ x ∈ Ph, root x.1 x.2) c := rfl
    _ ≤ ∑ c, (((Ph.filter fun x => x.1 = c).card : ℝ) + ((Ph.filter fun x => x.2 = c).card : ℝ)) *
          (oppCount ε c : ℝ) := Finset.sum_le_sum fun c _ => hpt c
    _ = ∑ c, ((Ph.filter fun x => x.1 = c).card : ℝ) * (oppCount ε c : ℝ) +
          ∑ c, ((Ph.filter fun x => x.2 = c).card : ℝ) * (oppCount ε c : ℝ) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        ring
    _ = ∑ x ∈ Ph, (oppCount ε x.1 : ℝ) + ∑ x ∈ Ph, (oppCount ε x.2 : ℝ) := by
        rw [hfib Prod.fst, hfib Prod.snd]
    _ = ∑ x ∈ Ph, (n : ℝ) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x hx => oppCount_add ε (hnc x hx)
    _ = n * Ph.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem kernel_lemma (ε : Fin n → Bool) (μ : Fin n → ℝ) {h : ℝ} (_hh : 0 < h) (Ph : Finset (Fin n × Fin n))
    (hnc : ∀ x ∈ Ph, ε x.1 ≠ ε x.2) (hpos : ∀ x ∈ Ph, h ≤ μ x.1 - μ x.2) :
    nsq (μ - ∑ x ∈ Ph, root x.1 x.2) ≤ nsq μ - (2 * h - n) * Ph.card := by
  have hexp : nsq (μ - ∑ x ∈ Ph, root x.1 x.2) =
      nsq μ - 2 * dot μ (∑ x ∈ Ph, root x.1 x.2) + nsq (∑ x ∈ Ph, root x.1 x.2) := by
    simp only [nsq, dot, Pi.sub_apply, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  have hd : h * Ph.card ≤ dot μ (∑ x ∈ Ph, root x.1 x.2) := by
    rw [dot_sum_root_right]
    have h2 : ∑ _x ∈ Ph, h ≤ ∑ x ∈ Ph, (μ x.1 - μ x.2) := Finset.sum_le_sum fun x hx => hpos x hx
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    linarith
  have hn := nsq_sum_root_le ε Ph hnc
  rw [hexp]
  linarith

end ReciprocityTheory.ChartRestriction.DS
