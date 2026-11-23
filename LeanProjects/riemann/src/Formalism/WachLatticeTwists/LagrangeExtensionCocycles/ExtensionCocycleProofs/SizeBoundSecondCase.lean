import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.StatementTop

namespace Formalism.RepresentationBoundsCohomology.N2.Size

open Finset

lemma JSet_subset (M h : ℕ) (jumps : Finset ℤ) (hj : ∀ a ∈ jumps, -(M : ℤ) ≤ a ∧ a ≤ h) :
    JSet jumps M ⊆ Icc (1 - (M : ℤ)) ((h : ℤ) + M) := by
  intro x hx
  simp only [JSet, eigSet, Finset.mem_union, Finset.mem_erase, Finset.mem_image, Finset.mem_product,
    Finset.mem_Icc] at hx
  rw [Finset.mem_Icc]
  rcases hx with ⟨-, ⟨⟨a, t⟩, ⟨ha, ht1, ht2⟩, rfl⟩⟩ | ⟨h1, h2⟩
  · have h3 := hj a ha
    constructor <;> omega
  · constructor <;> omega

lemma JSet_card (M h : ℕ) (jumps : Finset ℤ) (hj : ∀ a ∈ jumps, -(M : ℤ) ≤ a ∧ a ≤ h) :
    (JSet jumps M).card ≤ h + 2 * M := by
  calc (JSet jumps M).card ≤ (Icc (1 - (M : ℤ)) ((h : ℤ) + M)).card :=
        Finset.card_le_card (JSet_subset M h jumps hj)
    _ = h + 2 * M := by
        rw [Int.card_Icc]
        omega

variable (ℓ : ℕ) [Fact ℓ.Prime]

lemma sum_range_val (n : ℕ) :
    (∑ k ∈ range (n + 1), padicValNat ℓ k) = padicValNat ℓ n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Nat.factorial_succ,
      padicValNat.mul (by omega) (Nat.factorial_ne_zero n)]
    ring

lemma sum_val_half (n : ℕ) (T : Finset ℤ) (hT : ∀ j ∈ T, j.natAbs ≤ n)
    (hs : (∀ j ∈ T, j < 0) ∨ (∀ j ∈ T, 0 ≤ j)) :
    (∑ j ∈ T, padicValInt ℓ j) ≤ padicValNat ℓ n.factorial := by
  have hinj : Set.InjOn Int.natAbs (T : Set ℤ) := by
    intro x hx y hy hxy
    rcases Int.natAbs_eq_natAbs_iff.1 hxy with h' | h'
    · exact h'
    · rcases hs with h | h
      · have h1 := h x hx
        have h2 := h y hy
        omega
      · have h1 := h x hx
        have h2 := h y hy
        omega
  calc ∑ j ∈ T, padicValInt ℓ j = ∑ j ∈ T, padicValNat ℓ j.natAbs := rfl
    _ = ∑ k ∈ T.image Int.natAbs, padicValNat ℓ k := (Finset.sum_image hinj).symm
    _ ≤ ∑ k ∈ range (n + 1), padicValNat ℓ k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hk
          rw [Finset.mem_range]
          have := hT j hj
          omega
        · intro _ _ _
          exact Nat.zero_le _
    _ = padicValNat ℓ n.factorial := sum_range_val ℓ n

lemma sum_val_le (a b : ℕ) (T : Finset ℤ) (hT : T ⊆ Icc (-(a : ℤ)) b) :
    (∑ j ∈ T, padicValInt ℓ j) ≤ padicValNat ℓ a.factorial + padicValNat ℓ b.factorial := by
  rw [← Finset.sum_filter_add_sum_filter_not T (fun j => j < 0)]
  apply add_le_add
  · apply sum_val_half ℓ a
    · intro j hj
      rw [Finset.mem_filter] at hj
      have h1 := Finset.mem_Icc.1 (hT hj.1)
      omega
    · left
      intro j hj
      exact (Finset.mem_filter.1 hj).2
  · apply sum_val_half ℓ b
    · intro j hj
      rw [Finset.mem_filter] at hj
      have h1 := Finset.mem_Icc.1 (hT hj.1)
      omega
    · right
      intro j hj
      have h1 := (Finset.mem_filter.1 hj).2
      omega

lemma JSet_sum (M h : ℕ) (jumps : Finset ℤ) (hj : ∀ a ∈ jumps, -(M : ℤ) ≤ a ∧ a ≤ h) :
    (∑ j ∈ JSet jumps M, padicValInt ℓ j) ≤
      padicValNat ℓ M.factorial + padicValNat ℓ (h + M).factorial := by
  apply sum_val_le ℓ M (h + M) (JSet jumps M)
  intro x hx
  have h1 := Finset.mem_Icc.1 (JSet_subset M h jumps hj hx)
  rw [Finset.mem_Icc]
  push_cast
  constructor <;> omega

lemma legendre (n : ℕ) : (ℓ - 1) * padicValNat ℓ n.factorial ≤ n := by
  rw [sub_one_mul_padicValNat_factorial]
  exact Nat.sub_le _ _

lemma val_factorial_le_self (n : ℕ) : padicValNat ℓ n.factorial ≤ n := by
  have h2 := (Fact.out : ℓ.Prime).two_le
  exact le_trans (Nat.le_mul_of_pos_left _ (by omega)) (legendre ℓ n)

lemma val_factorial_le_div (n : ℕ) :
    (padicValNat ℓ n.factorial : ℝ) ≤ (n : ℝ) / ((ℓ : ℝ) - 1) := by
  have h2 := (Fact.out : ℓ.Prime).two_le
  have hpos : (0 : ℝ) < (ℓ : ℝ) - 1 := by
    have : (2 : ℝ) ≤ ℓ := by exact_mod_cast h2
    linarith
  rw [le_div_iff₀ hpos]
  have h := legendre ℓ n
  have hc : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have h' : (((ℓ - 1) * padicValNat ℓ n.factorial : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
  push_cast [Nat.cast_mul] at h'
  rw [hc] at h'
  linarith

end Formalism.RepresentationBoundsCohomology.N2.Size

namespace Formalism.RepresentationBoundsCohomology.N2

open Finset

theorem size_bound_second_case : StatSizeB := by
  intro ℓ _ M h H s jumps hs hMH hj
  unfold eWB eUB
  have h1 := Size.JSet_card M h jumps hj
  have h2 := Size.JSet_sum ℓ M h jumps hj
  have h3 := Size.val_factorial_le_self ℓ (2 * H)
  have h4 := Size.val_factorial_le_self ℓ M
  have h5 := Size.val_factorial_le_self ℓ (h + M)
  have hsum : ∑ j ∈ JSet jumps M, (s + padicValInt ℓ j) =
      (JSet jumps M).card * s + ∑ j ∈ JSet jumps M, padicValInt ℓ j := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
  rw [hsum]
  have h6 : (JSet jumps M).card * s ≤ (h + 2 * M) * s := Nat.mul_le_mul_right s h1
  have h7 : (h + 2 * M) * s ≤ 2 * H * s := Nat.mul_le_mul_right s (by omega)
  have h8 : M * s ≤ H * s := Nat.mul_le_mul_right s (by omega)
  have h9 : H ≤ H * s := Nat.le_mul_of_pos_right H hs
  nlinarith

theorem size_bound_first_case : StatSizeA := by
  intro ℓ _ hℓ M h H jumps hMH hj
  have hp : ℓ.Prime := Fact.out
  have h3 : 3 ≤ ℓ := by
    have := hp.two_le
    omega
  have h3r : (3 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast h3
  set t : ℝ := (ℓ : ℝ) - 1 with ht
  have ht2 : (2 : ℝ) ≤ t := by rw [ht]; linarith
  have htpos : (0 : ℝ) < t := by linarith
  have hH0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have hMHr : (M : ℝ) + (h : ℝ) ≤ (H : ℝ) := by exact_mod_cast hMH
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.logb ℓ ((H : ℝ) + 1) :=
    Real.logb_nonneg (by linarith) (by linarith)

  have hW0 : 0 ≤ (H : ℝ) * ℓ / t ^ 2 + 3 + Real.logb ℓ ((H : ℝ) + 1) := by positivity
  have hW : (eWA ℓ H : ℝ) ≤ (H : ℝ) * ℓ / t ^ 2 + 3 + Real.logb ℓ ((H : ℝ) + 1) :=
    Nat.floor_le hW0
  have hW2 : (H : ℝ) * ℓ / t ^ 2 ≤ 3 / 2 * ((H : ℝ) / t) := by
    rw [div_le_iff₀ (by positivity)]
    have e : 3 / 2 * ((H : ℝ) / t) * t ^ 2 = 3 / 2 * (H : ℝ) * t := by
      field_simp
    rw [e]
    have : (ℓ : ℝ) = t + 1 := by rw [ht]; ring
    rw [this]
    nlinarith

  have hv := Size.JSet_sum ℓ M h jumps hj
  have hvr : ((∑ j ∈ JSet jumps M, padicValInt ℓ j : ℕ) : ℝ) ≤
      (padicValNat ℓ M.factorial : ℝ) + (padicValNat ℓ (h + M).factorial : ℝ) := by
    exact_mod_cast hv
  have f2 := Size.val_factorial_le_div ℓ M
  have f3 := Size.val_factorial_le_div ℓ (h + M)
  rw [← ht] at f2 f3
  push_cast at f3

  have ha : (aStar ℓ M : ℝ) ≤ (M : ℝ) / t + 1 := by
    unfold aStar
    push_cast
    have := @Nat.cast_div_le ℝ _ _ _ M (ℓ - 1)
    rw [Nat.cast_sub (by omega), Nat.cast_one, ← ht] at this
    linarith
  have f4 := Size.val_factorial_le_div ℓ (aStar ℓ M)
  rw [← ht] at f4
  have f5 : (aStar ℓ M : ℝ) / t ≤ ((M : ℝ) / t + 1) / 2 := by
    have h0 : (0 : ℝ) ≤ (aStar ℓ M : ℝ) := Nat.cast_nonneg _
    calc (aStar ℓ M : ℝ) / t ≤ (aStar ℓ M : ℝ) / 2 :=
          div_le_div_of_nonneg_left h0 (by norm_num) ht2
      _ ≤ ((M : ℝ) / t + 1) / 2 := by linarith
  have d1 : (M : ℝ) / t ≤ (H : ℝ) / t := div_le_div_of_nonneg_right (by linarith) htpos.le
  have d2 : (M : ℝ) / t + ((h : ℝ) + (M : ℝ)) / t ≤ 2 * ((H : ℝ) / t) := by
    rw [← add_div, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) htpos.le
  have e0 : 15 / 2 * (H : ℝ) / t = 15 / 2 * ((H : ℝ) / t) := by ring
  have hHt : 0 ≤ (H : ℝ) / t := by positivity
  unfold eUA
  push_cast at hvr ⊢
  rw [e0]
  linarith

end Formalism.RepresentationBoundsCohomology.N2
