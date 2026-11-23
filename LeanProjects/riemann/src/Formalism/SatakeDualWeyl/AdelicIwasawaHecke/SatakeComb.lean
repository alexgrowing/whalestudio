import Mathlib

namespace Formalism.UG.P

open Finset

def satakeInv {α : Type} [LinearOrder α] (s S : Finset α) : ℕ :=
  ∑ a ∈ S, ((s \ S).filter (fun l => a < l)).card

theorem satakeInv_insert_not_mem {α : Type} [LinearOrder α] (s' S : Finset α) (m : α)
    (hm : ∀ x ∈ s', x < m) (hS : S ⊆ s') :
    satakeInv (insert m s') S = satakeInv s' S + S.card := by
  have hmS' : m ∉ s' := fun h => lt_irrefl m (hm m h)
  have hmS : m ∉ S := fun h => hmS' (hS h)
  unfold satakeInv
  rw [card_eq_sum_ones S, ← sum_add_distrib]
  apply sum_congr rfl
  intro a ha
  have e : (insert m s' \ S).filter (fun l => a < l)
      = insert m ((s' \ S).filter (fun l => a < l)) := by
    ext x
    by_cases hx : x = m
    · simp [hx, hmS, hm a (hS ha)]
    · simp [hx]
  rw [e, card_insert_of_notMem (by simp [hmS'])]

theorem satakeInv_insert_mem {α : Type} [LinearOrder α] (s' T : Finset α) (m : α)
    (hm : ∀ x ∈ s', x < m) (hT : T ⊆ s') :
    satakeInv (insert m s') (insert m T) = satakeInv s' T := by
  have hmS' : m ∉ s' := fun h => lt_irrefl m (hm m h)
  have hmT : m ∉ T := fun h => hmS' (hT h)
  unfold satakeInv
  rw [sum_insert hmT]
  have e : insert m s' \ insert m T = s' \ T := by
    ext x
    by_cases hx : x = m
    · simp [hx, hmS']
    · simp [hx]
  rw [e]
  have h0 : ((s' \ T).filter (fun l => m < l)).card = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    intro x hx
    exact not_lt.2 (le_of_lt (hm x (mem_sdiff.1 hx).1))
  rw [h0, zero_add]

theorem satake_qbinom (q : ℤ) {α : Type} [LinearOrder α] (s : Finset α) :
    ∀ j : ℕ, (∑ S ∈ s.powersetCard j, q ^ satakeInv s S) * ∏ i ∈ range j, (q ^ (i + 1) - 1) =
      ∏ i ∈ range j, (q ^ (s.card - i) - 1) := by
  induction s using Finset.induction_on_max
  next =>
    intro j
    cases j with
    | zero => simp [satakeInv]
    | succ k =>
      have h1 : powersetCard (k + 1) (∅ : Finset α) = ∅ := powersetCard_eq_empty.2 (by simp)
      rw [h1, sum_empty, zero_mul, prod_range_succ']
      simp
  next m s' hm ih =>
    have hmS' : m ∉ s' := fun h => lt_irrefl m (hm m h)
    intro j
    cases j with
    | zero => simp [satakeInv]
    | succ k =>
      have hdisj : Disjoint (powersetCard (k + 1) s') ((powersetCard k s').image (insert m)) := by
        rw [disjoint_left]
        intro S hS hS'
        obtain ⟨T, -, rfl⟩ := mem_image.1 hS'
        exact hmS' ((mem_powersetCard.1 hS).1 (mem_insert_self m T))
      have hinj : Set.InjOn (insert m) (powersetCard k s' : Set (Finset α)) := by
        intro T1 h1 T2 h2 h
        have h1' : m ∉ T1 := fun h' => hmS' ((mem_powersetCard.1 (mem_coe.1 h1)).1 h')
        have h2' : m ∉ T2 := fun h' => hmS' ((mem_powersetCard.1 (mem_coe.1 h2)).1 h')
        calc T1 = (insert m T1).erase m := (erase_insert h1').symm
          _ = (insert m T2).erase m := by rw [h]
          _ = T2 := erase_insert h2'
      rw [powersetCard_succ_insert hmS', sum_union hdisj, sum_image hinj]
      have e1 : ∑ S ∈ powersetCard (k + 1) s', q ^ satakeInv (insert m s') S
          = q ^ (k + 1) * ∑ S ∈ powersetCard (k + 1) s', q ^ satakeInv s' S := by
        rw [mul_sum]
        apply sum_congr rfl
        intro S hS
        obtain ⟨hsub, hcard⟩ := mem_powersetCard.1 hS
        rw [satakeInv_insert_not_mem s' S m hm hsub, hcard, pow_add]
        ring
      have e2 : ∑ T ∈ powersetCard k s', q ^ satakeInv (insert m s') (insert m T)
          = ∑ T ∈ powersetCard k s', q ^ satakeInv s' T :=
        sum_congr rfl (fun T hT => by
          rw [satakeInv_insert_mem s' T m hm (mem_powersetCard.1 hT).1])
      rw [e1, e2]
      have hP : ∏ i ∈ range (k + 1), (q ^ (i + 1) - 1)
          = (∏ i ∈ range k, (q ^ (i + 1) - 1)) * (q ^ (k + 1) - 1) := prod_range_succ _ _
      have hR : ∏ i ∈ range (k + 1), (q ^ (s'.card + 1 - i) - 1)
          = (∏ i ∈ range k, (q ^ (s'.card - i) - 1)) * (q ^ (s'.card + 1) - 1) := by
        rw [prod_range_succ']
        simp only [Nat.add_sub_add_right, Nat.sub_zero]
      have hRk : ∏ i ∈ range (k + 1), (q ^ (s'.card - i) - 1)
          = (∏ i ∈ range k, (q ^ (s'.card - i) - 1)) * (q ^ (s'.card - k) - 1) :=
        prod_range_succ _ _
      have hsplit :
          (q ^ (k + 1) * ∑ S ∈ powersetCard (k + 1) s', q ^ satakeInv s' S
              + ∑ T ∈ powersetCard k s', q ^ satakeInv s' T) * ∏ i ∈ range (k + 1), (q ^ (i + 1) - 1)
            = q ^ (k + 1) * ((∑ S ∈ powersetCard (k + 1) s', q ^ satakeInv s' S)
                * ∏ i ∈ range (k + 1), (q ^ (i + 1) - 1))
              + ((∑ T ∈ powersetCard k s', q ^ satakeInv s' T) * ∏ i ∈ range k, (q ^ (i + 1) - 1))
                * (q ^ (k + 1) - 1) := by
        rw [hP]; ring
      rw [card_insert_of_notMem hmS', hR, hsplit, ih (k + 1), ih k, hRk]
      by_cases hk : k ≤ s'.card
      · have hpow : q ^ (k + 1) * q ^ (s'.card - k) = q ^ (s'.card + 1) := by
          rw [← pow_add]; congr 1; omega
        linear_combination (∏ i ∈ range k, (q ^ (s'.card - i) - 1)) * hpow
      · have hz : ∏ i ∈ range k, (q ^ (s'.card - i) - 1) = 0 :=
          prod_eq_zero (i := s'.card) (mem_range.2 (by omega)) (by simp)
        rw [hz]; ring

private theorem satakeInv_insert_max_add_card {α : Type} [LinearOrder α] (s S : Finset α) (m : α)
    (hm : ∀ x ∈ S, x < m) (hms : m ∈ s) :
    satakeInv s (insert m S) + S.card = satakeInv s S + (s.filter (fun l => m < l)).card := by
  have hmS : m ∉ S := fun h => lt_irrefl m (hm m h)
  unfold satakeInv
  rw [sum_insert hmS]
  have h1 : (s \ insert m S).filter (fun l => m < l) = s.filter (fun l => m < l) := by
    ext x
    simp only [mem_filter, mem_sdiff, mem_insert]
    constructor
    · rintro ⟨⟨hx, -⟩, h⟩
      exact ⟨hx, h⟩
    · rintro ⟨hx, h⟩
      refine ⟨⟨hx, ?_⟩, h⟩
      rintro (rfl | hxS)
      · exact lt_irrefl _ h
      · exact lt_asymm h (hm x hxS)
  have h2 : ∀ a ∈ S, ((s \ S).filter (fun l => a < l)).card
      = ((s \ insert m S).filter (fun l => a < l)).card + 1 := by
    intro a ha
    have e : (s \ S).filter (fun l => a < l)
        = insert m ((s \ insert m S).filter (fun l => a < l)) := by
      ext x
      by_cases hx : x = m
      · simp [hx, hms, hmS, hm a ha]
      · simp [hx]
    rw [e, card_insert_of_notMem (by simp)]
  rw [h1, sum_congr rfl h2, sum_add_distrib, sum_const, smul_eq_mul, mul_one]
  ring

theorem satakeInv_two_mul {n : ℕ} (S : Finset (Fin n)) :
    2 * (satakeInv univ S : ℤ) =
      ∑ a ∈ S, ((n : ℤ) - 1 - 2 * (a : ℕ)) + (S.card : ℤ) * ((n : ℤ) - S.card) := by
  induction S using Finset.induction_on_max
  next => simp [satakeInv]
  next m S' hm ih =>
    have hmS' : m ∉ S' := fun h => lt_irrefl m (hm m h)
    have L := satakeInv_insert_max_add_card (univ : Finset (Fin n)) S' m hm (mem_univ m)
    have hc : ((univ : Finset (Fin n)).filter (fun l => m < l)).card = n - 1 - (m : ℕ) := by
      rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
    rw [hc] at L
    have hlt : (m : ℕ) < n := m.isLt
    have hsub : (((n - 1 - (m : ℕ) : ℕ)) : ℤ) = (n : ℤ) - 1 - (m : ℕ) := by omega
    have L' := congrArg (fun x : ℕ => (x : ℤ)) L
    simp only [Nat.cast_add] at L'
    rw [hsub] at L'
    rw [sum_insert hmS', card_insert_of_notMem hmS']
    push_cast
    linear_combination 2 * L' + ih

end Formalism.UG.P
