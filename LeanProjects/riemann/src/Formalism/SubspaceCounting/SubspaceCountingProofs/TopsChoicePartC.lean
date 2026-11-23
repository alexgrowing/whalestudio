import Formalism.SubspaceCounting.TopsChoiceSecondBound

noncomputable section

namespace Formalism.G0

namespace TopsConditionalProbabilityBounds

open Finset

theorem weight_nonneg (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (T : Finset ℕ) :
    0 ≤ δ ^ (T.card - 1) * (1 - δ) ^ (n - T.card) :=
  mul_nonneg (pow_nonneg hδ0 _) (pow_nonneg (by linarith) _)

theorem condProb_mono (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (A B : Finset ℕ → Prop)
    (h : ∀ T, 0 ∈ T → A T → B T) : condProb n δ A ≤ condProb n δ B := by
  classical
  unfold condProb
  apply sum_le_sum
  intro T _
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd ⟨h1.1, h T h1.1 h1.2⟩ h2
  · exact weight_nonneg n δ hδ0 hδ1 T
  · exact le_rfl

theorem condProb_disjoint (n : ℕ) (δ : ℝ) (S : Finset ℕ) (hS : S ⊆ range n) (h0 : 0 ∉ S)
    (hn : 1 ≤ n) :
    condProb n δ (fun T => Disjoint S T) = (1 - δ) ^ S.card := by
  classical
  set U := (range n \ S).erase 0 with hU
  have h0U : 0 ∈ range n \ S := by simp [h0]; omega
  have hUcard : U.card = n - S.card - 1 := by
    rw [hU, card_erase_of_mem h0U, card_sdiff_of_subset hS, card_range]
  have hs1 : S.card + 1 ≤ n := by
    have hsub : S ⊆ (range n).erase 0 := fun x hx => mem_erase.2 ⟨fun h => h0 (h ▸ hx), hS hx⟩
    have := card_le_card hsub
    rw [card_erase_of_mem (by simp; omega), card_range] at this
    omega
  have key : ∑ T' ∈ U.powerset, δ ^ T'.card * (1 - δ) ^ (U.card - T'.card) = 1 := by
    rw [sum_pow_mul_eq_add_pow]; simp
  have step1 : condProb n δ (fun T => Disjoint S T) =
      ∑ T ∈ (range n).powerset.filter (fun T => 0 ∈ T ∧ Disjoint S T),
        δ ^ (T.card - 1) * (1 - δ) ^ (n - T.card) := by
    unfold condProb
    rw [sum_filter]
    refine sum_congr rfl (fun T _ => ?_)
    split_ifs <;> rfl
  have step2 : ∑ T ∈ (range n).powerset.filter (fun T => 0 ∈ T ∧ Disjoint S T),
        δ ^ (T.card - 1) * (1 - δ) ^ (n - T.card) =
      ∑ T' ∈ U.powerset, δ ^ T'.card * ((1 - δ) ^ S.card * (1 - δ) ^ (U.card - T'.card)) := by
    refine sum_nbij' (fun T => T.erase 0) (fun T' => insert 0 T') ?_ ?_ ?_ ?_ ?_
    · intro T hT
      simp only [mem_filter, mem_powerset] at hT ⊢
      obtain ⟨hTn, _, hST⟩ := hT
      intro x hx
      rw [mem_erase] at hx
      rw [hU, mem_erase, mem_sdiff]
      exact ⟨hx.1, hTn hx.2, fun hxS => disjoint_left.1 hST hxS hx.2⟩
    · intro T' hT'
      simp only [mem_filter, mem_powerset] at hT' ⊢
      refine ⟨?_, mem_insert_self _ _, ?_⟩
      · intro x hx
        rw [mem_insert] at hx
        rcases hx with rfl | hx
        · simp; omega
        · exact (mem_sdiff.1 (mem_of_mem_erase (hT' hx))).1
      · rw [disjoint_insert_right]
        refine ⟨h0, ?_⟩
        rw [disjoint_left]
        intro x hxS hxT
        exact (mem_sdiff.1 (mem_of_mem_erase (hT' hxT))).2 hxS
    · intro T hT
      simp only [mem_powerset, mem_filter] at hT
      exact insert_erase hT.2.1
    · intro T' hT'
      simp only [mem_powerset] at hT'
      apply erase_insert
      intro h
      have := hT' h
      rw [hU] at this
      exact (notMem_erase 0 _) this
    · intro T hT
      simp only [mem_filter, mem_powerset] at hT
      obtain ⟨hTn, h0T, hST⟩ := hT
      have hsub : T.erase 0 ⊆ U := by
        intro x hx
        rw [mem_erase] at hx
        rw [hU, mem_erase, mem_sdiff]
        exact ⟨hx.1, hTn hx.2, fun hxS => disjoint_left.1 hST hxS hx.2⟩
      have hc := card_le_card hsub
      rw [card_erase_of_mem h0T] at hc ⊢
      have hT1 : 1 ≤ T.card := card_pos.2 ⟨0, h0T⟩
      rw [← pow_add]
      congr 2
      omega
  rw [step1, step2]
  simp_rw [mul_left_comm _ ((1 - δ) ^ S.card)]
  rw [← mul_sum, key, mul_one]

theorem bad_bound (n : ℕ) (δ : ℝ) (G : ℕ) (hn : 2 ≤ n) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (i : ℕ) (hi : i < n) :
    condProb n δ (fun T => i ∈ T ∧ ∀ d, 1 ≤ d → d ≤ G → (i + d) % n ∉ T) ≤ (1 - δ) ^ G := by
  rcases lt_or_ge (i + G) n with hlt | hge
  · calc condProb n δ (fun T => i ∈ T ∧ ∀ d, 1 ≤ d → d ≤ G → (i + d) % n ∉ T)
        ≤ condProb n δ (fun T => Disjoint (Icc (i + 1) (i + G)) T) := by
          apply condProb_mono n δ hδ0 hδ1
          rintro T _ ⟨_, hT⟩
          rw [disjoint_left]
          intro x hx hxT
          rw [mem_Icc] at hx
          have := hT (x - i) (by omega) (by omega)
          rw [show i + (x - i) = x by omega, Nat.mod_eq_of_lt (by omega)] at this
          exact this hxT
      _ = (1 - δ) ^ (Icc (i + 1) (i + G)).card := by
          apply condProb_disjoint n δ _ _ _ (by omega)
          · intro x hx
            rw [mem_Icc] at hx
            rw [mem_range]
            omega
          · rw [mem_Icc]
            omega
      _ = (1 - δ) ^ G := by
          rw [Nat.card_Icc]
          congr 1
          omega
  · calc condProb n δ (fun T => i ∈ T ∧ ∀ d, 1 ≤ d → d ≤ G → (i + d) % n ∉ T)
        ≤ condProb n δ (fun _ => False) := by
          apply condProb_mono n δ hδ0 hδ1
          rintro T h0T ⟨_, hT⟩
          have := hT (n - i) (by omega) (by omega)
          rw [show i + (n - i) = n by omega, Nat.mod_self] at this
          exact this h0T
      _ = 0 := by
          unfold condProb
          simp
      _ ≤ (1 - δ) ^ G := pow_nonneg (by linarith) _

end TopsConditionalProbabilityBounds

open Finset TopsConditionalProbabilityBounds in
theorem tops_choice_part_c : TopsChoiceThirdBound := by
  intro n δ G hn hδ0 hδ1
  classical
  have hunion : condProb n δ (fun T => ¬ CondC n T G) ≤
      ∑ i ∈ range n, condProb n δ (fun T => i ∈ T ∧ ∀ d, 1 ≤ d → d ≤ G → (i + d) % n ∉ T) := by
    unfold condProb
    rw [sum_comm]
    apply sum_le_sum
    intro T hT
    rw [mem_powerset] at hT
    split_ifs with h
    · obtain ⟨h0T, hC⟩ := h
      unfold CondC at hC
      push Not at hC
      obtain ⟨i, hiT, hi⟩ := hC
      have hir : i ∈ range n := hT hiT
      refine le_trans (le_of_eq ?_) (single_le_sum ?_ hir)
      · exact (if_pos ⟨h0T, hiT, hi⟩).symm
      · intro j _
        split_ifs
        · exact weight_nonneg n δ hδ0 hδ1 T
        · exact le_rfl
    · apply sum_nonneg
      intro j _
      split_ifs
      · exact weight_nonneg n δ hδ0 hδ1 T
      · exact le_rfl
  calc _ ≤ _ := hunion
    _ ≤ ∑ _i ∈ range n, (1 - δ) ^ G :=
        sum_le_sum (fun i hi => bad_bound n δ G hn hδ0 hδ1 i (mem_range.1 hi))
    _ = n * (1 - δ) ^ G := by rw [sum_const, card_range, nsmul_eq_mul]

end Formalism.G0
