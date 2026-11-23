import Mathlib

namespace PI.Residue

open scoped ENNReal

section Comb

variable {α ι : Type*} [DecidableEq α] [DecidableEq ι]

def intersection_update_fsHerm_neg_one (N : α → ℕ) (idx : α → ι) (s : Multiset α) (i : ι) : ℕ :=
  ((s.filter (fun a => idx a = i)).map N).prod

theorem position_cons (N : α → ℕ) (idx : α → ι) (a : α) (s : Multiset α) (i : ι) :
    intersection_update_fsHerm_neg_one N idx (a ::ₘ s) i = (if idx a = i then N a else 1) * intersection_update_fsHerm_neg_one N idx s i := by
  unfold intersection_update_fsHerm_neg_one
  by_cases h : idx a = i
  · simp [h]
  · simp [h]

theorem prod_position [Fintype ι] (N : α → ℕ) (idx : α → ι) (s : Multiset α) :
    ∏ i, intersection_update_fsHerm_neg_one N idx s i = (s.map N).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [intersection_update_fsHerm_neg_one]
  | cons a s ih =>
    simp_rw [position_cons]
    rw [Finset.prod_mul_distrib, ih]
    simp

theorem factorization_multiset_prod (m : Multiset ℕ) (h : ∀ x ∈ m, x ≠ 0) (p : ℕ) :
    m.prod.factorization p = (m.map (fun x => x.factorization p)).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : a ≠ 0 := h a (Multiset.mem_cons_self a s)
    have hs : ∀ x ∈ s, x ≠ 0 := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    have hs' : s.prod ≠ 0 := by
      intro h0
      exact hs 0 (Multiset.prod_eq_zero_iff.mp h0) rfl
    rw [Multiset.prod_cons, Nat.factorization_mul ha hs', Multiset.map_cons, Multiset.sum_cons,
      Finsupp.add_apply, ih hs]

theorem factorization_position (N : α → ℕ) (idx : α → ι) (S : Set α) (h1 : ∀ a ∈ S, 1 < N a)
    (h2 : ∀ a ∈ S, ∀ b ∈ S, idx a = idx b → ¬ Nat.Coprime (N a) (N b) → a = b)
    {s : Multiset α} (hs : ∀ a ∈ s, a ∈ S) {a : α} (ha : a ∈ S) :
    (intersection_update_fsHerm_neg_one N idx s (idx a)).factorization (N a).minFac
      = s.count a * (N a).factorization (N a).minFac := by
  have hp : (N a).minFac.Prime := Nat.minFac_prime (h1 a ha).ne'
  unfold intersection_update_fsHerm_neg_one
  rw [factorization_multiset_prod, Multiset.map_map,
    Multiset.sum_map_eq_nsmul_single a,
    Multiset.count_filter_of_pos (p := fun b => idx b = idx a) rfl]
  · simp
  · intro b hba hb
    rw [Multiset.mem_filter] at hb
    simp only [Function.comp_apply]
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    apply hba
    refine h2 b (hs b hb.1) a ha hb.2 ?_
    intro hcop
    exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hdvd (Nat.minFac_dvd _) hcop
  · intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    rw [Multiset.mem_filter] at hb
    exact (Nat.zero_lt_of_lt (h1 b (hs b hb.1))).ne'

theorem position_inj (N : α → ℕ) (idx : α → ι) (S : Set α) (h1 : ∀ a ∈ S, 1 < N a)
    (h2 : ∀ a ∈ S, ∀ b ∈ S, idx a = idx b → ¬ Nat.Coprime (N a) (N b) → a = b)
    {s t : Multiset α} (hs : ∀ a ∈ s, a ∈ S) (ht : ∀ a ∈ t, a ∈ S)
    (h : intersection_update_fsHerm_neg_one N idx s = intersection_update_fsHerm_neg_one N idx t) : s = t := by
  ext a
  by_cases ha : a ∈ S
  · have e1 := factorization_position N idx S h1 h2 hs ha
    have e2 := factorization_position N idx S h1 h2 ht ha
    rw [h, e2] at e1
    have hp : (N a).minFac.Prime := Nat.minFac_prime (h1 a ha).ne'
    have hpos : 0 < (N a).factorization (N a).minFac :=
      hp.factorization_pos_of_dvd (Nat.zero_lt_of_lt (h1 a ha)).ne' (Nat.minFac_dvd _)
    exact (Nat.eq_of_mul_eq_mul_right hpos e1).symm
  · rw [Multiset.count_eq_zero_of_notMem (fun h' => ha (hs a h')),
      Multiset.count_eq_zero_of_notMem (fun h' => ha (ht a h'))]

end Comb

section Sums

theorem tsum_pi_prod (w : ℕ → ℝ≥0∞) (m : ℕ) :
    ∑' v : Fin m → ℕ, ∏ i, w (v i) = (∑' n, w n) ^ m := by
  induction m with
  | zero => simp [tsum_fintype]
  | succ m ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => ℕ)).tsum_eq, ENNReal.tsum_prod']
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    simp_rw [ENNReal.tsum_mul_left, ih, ENNReal.tsum_mul_right]
    rw [pow_succ, mul_comm]

theorem tsum_le_pow {β : Type*} {m : ℕ} (n : β → Fin m → ℕ) (hinj : Function.Injective n)
    (w : ℕ → ℝ≥0∞) (W : β → ℝ≥0∞) (hw : ∀ b, W b = ∏ i, w (n b i)) :
    ∑' b, W b ≤ (∑' k, w k) ^ m := by
  rw [← tsum_pi_prod]
  simp_rw [hw]
  exact ENNReal.tsum_comp_le_tsum_of_injective hinj (fun v => ∏ i, w (v i))

end Sums

end PI.Residue
