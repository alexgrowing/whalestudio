import Formalism.GrowthSums.StatementB

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.GrowthSums

open Formalism.G0

theorem next_even_top_holds : NextEvenTop := by
  intro n T L₂ K r u M₀ G' N₁ hr hu hn hG hT hgood i hi
  obtain ⟨_, hTiles, _⟩ := hgood
  set ℓ := (6 * r + 1) * u with hℓ
  have hℓpos : 0 < ℓ := Nat.mul_pos (by omega) (by omega)
  have h2u : 2 * u ≤ ℓ := by rw [hℓ]; nlinarith
  set t := n / ℓ with ht
  have htM : M₀ + 1 ≤ t := (Nat.le_div_iff_mul_le hℓpos).2 hn
  have hnt : n < t * ℓ + ℓ := by
    have h1 : ℓ * t + n % ℓ = n := Nat.div_add_mod n ℓ
    have h2 := Nat.mod_lt n hℓpos
    have h3 : t * ℓ = ℓ * t := Nat.mul_comm _ _
    omega
  obtain ⟨si, hsi_lt, hsi_le, hsi_case⟩ :
      ∃ si, si < t ∧ si * ℓ ≤ i ∧ (i < si * ℓ + ℓ ∨ si + 1 = t) := by
    by_cases hc : i < t * ℓ
    · refine ⟨i / ℓ, ?_, Nat.div_mul_le_self i ℓ, Or.inl ?_⟩
      · exact (Nat.div_lt_iff_lt_mul hℓpos).2 hc
      · exact Nat.lt_div_mul_add hℓpos
    · refine ⟨t - 1, by omega, ?_, Or.inr (by omega)⟩
      have : (t - 1) * ℓ ≤ t * ℓ := Nat.mul_le_mul_right _ (by omega)
      omega
  have htpos : 0 < t := by omega
  obtain ⟨j, hj, hM⟩ := hTiles ((si + 1) % t) (Nat.mod_lt _ htpos)
  rw [Nat.mod_add_mod] at hM
  obtain ⟨s, hs⟩ : ∃ s, s = (si + 1 + j) % t := ⟨_, rfl⟩
  rw [← hs] at hM
  have hslt : s < t := hs ▸ Nat.mod_lt _ htpos
  have hsc : s = si + 1 + j ∨ s + t = si + 1 + j := by
    by_cases hc : si + 1 + j < t
    · left; rw [hs, Nat.mod_eq_of_lt hc]
    · right
      rw [hs, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  obtain ⟨x, hx, hxe⟩ := (hM 2 (by omega) (by omega)).2 even_two
  have hxmem : x ∈ T ∩ cell r u s 2 := by rw [hx]; exact mem_singleton_self x
  rw [mem_inter] at hxmem
  obtain ⟨hxT, hxc⟩ := hxmem
  simp only [cell, mem_Ico] at hxc
  rw [← hℓ] at hxc
  have hxn : x < n := mem_range.1 (hT hxT)
  have hjl : j * ℓ ≤ M₀ * ℓ := Nat.mul_le_mul_right _ hj
  have hG5 : (M₀ + 5) * ℓ = M₀ * ℓ + 5 * ℓ := by ring
  have key : ∃ D, 1 ≤ D ∧ D ≤ G' ∧ (i + D) % n = x := by
    rcases hsc with hA | hB
    · have e : s * ℓ = si * ℓ + ℓ + j * ℓ := by rw [hA]; ring
      refine ⟨x - i, by omega, by omega, ?_⟩
      rw [show i + (x - i) = x by omega, Nat.mod_eq_of_lt hxn]
    · have e : s * ℓ + t * ℓ = si * ℓ + ℓ + j * ℓ := by rw [← add_mul, hB]; ring
      have hssi : s ≤ si := by omega
      have e2 : s * ℓ ≤ si * ℓ := Nat.mul_le_mul_right _ hssi
      by_cases hxi : i < x
      · refine ⟨x - i, by omega, by omega, ?_⟩
        rw [show i + (x - i) = x by omega, Nat.mod_eq_of_lt hxn]
      · refine ⟨x + n - i, by omega, by omega, ?_⟩
        rw [show i + (x + n - i) = x + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hxn]
  obtain ⟨D, hD1, hD2, hDx⟩ := key
  exact ⟨D, mem_Icc.2 ⟨hD1, hD2⟩, by rw [hDx]; exact ⟨hxT, hxe⟩⟩

theorem top_count_holds : TopCount := by
  intro n T L₂ K r u M₀ G' N₁ hr hu hn hG hT hgood
  have hnext := next_even_top_holds n T L₂ K r u M₀ G' N₁ hr hu hn hG hT hgood
  obtain ⟨_, _, hInt⟩ := hgood
  have hℓpos : 0 < (6 * r + 1) * u := Nat.mul_pos (by omega) (by omega)
  have hnpos : 0 < n := lt_of_lt_of_le (Nat.mul_pos (by omega) hℓpos) hn
  have hGpos : 0 < G' := lt_of_lt_of_le (Nat.mul_pos (by omega) hℓpos) hG
  constructor
  · have hsub : range n ⊆ (T ×ˢ Icc 1 G').image (fun p => (p.1 + n * G' - p.2) % n) := by
      intro i hi
      rw [mem_range] at hi
      obtain ⟨D, hD, hDT, -⟩ := hnext i hi
      rw [mem_Icc] at hD
      rw [mem_image]
      refine ⟨((i + D) % n, D), mem_product.2 ⟨hDT, mem_Icc.2 hD⟩, ?_⟩
      simp only
      have h1 := Nat.div_add_mod (i + D) n
      obtain ⟨q, hq⟩ : ∃ q, q = (i + D) / n := ⟨_, rfl⟩
      obtain ⟨x, hx⟩ : ∃ x, x = (i + D) % n := ⟨_, rfl⟩
      rw [← hq, ← hx] at h1
      rw [← hx]
      have hqG : q ≤ G' := by
        by_contra hc
        have : n * (G' + 1) ≤ n * q := Nat.mul_le_mul_left _ (by omega)
        have : n * (G' + 1) = n * G' + n := by ring
        have : G' ≤ n * G' := Nat.le_mul_of_pos_left _ hnpos
        omega
      have h2 : n * (G' - q) = n * G' - n * q := Nat.mul_sub n G' q
      have h3 : n * q ≤ n * G' := Nat.mul_le_mul_left _ hqG
      have h4 : x + n * G' - D = i + n * (G' - q) := by omega
      rw [h4, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
    calc n = (range n).card := (card_range n).symm
      _ ≤ _ := card_le_card hsub
      _ ≤ (T ×ˢ Icc 1 G').card := card_image_le
      _ = T.card * G' := by rw [card_product, Nat.card_Icc]; simp
  · have hcov : T ⊆ (T.image (fun p => p / G')).biUnion
        (fun c => T ∩ window n (c * G') G') := by
      intro p hp
      rw [mem_biUnion]
      refine ⟨p / G', mem_image_of_mem _ hp, mem_inter.2 ⟨hp, ?_⟩⟩
      have hpn : p < n := mem_range.1 (hT hp)
      unfold window
      rw [mem_image]
      have h1 := Nat.lt_div_mul_add (a := p) hGpos
      have h2 := Nat.div_mul_le_self p G'
      refine ⟨p - p / G' * G', mem_range.2 (by omega), ?_⟩
      rw [show p / G' * G' + (p - p / G' * G') = p by omega, Nat.mod_eq_of_lt hpn]
    have hcard : T.card ≤ (T.image (fun p => p / G')).card * N₁ := by
      calc T.card ≤ _ := card_le_card hcov
        _ ≤ ∑ c ∈ T.image (fun p => p / G'), (T ∩ window n (c * G') G').card :=
            card_biUnion_le
        _ ≤ ∑ c ∈ T.image (fun p => p / G'), N₁ := by
            apply sum_le_sum
            intro c hc
            obtain ⟨p, hp, rfl⟩ := mem_image.1 hc
            apply hInt
            have := Nat.div_mul_le_self p G'
            have := mem_range.1 (hT hp)
            omega
        _ = _ := by rw [sum_const, smul_eq_mul]
    have himg : (T.image (fun p => p / G')).card ≤ n / G' + 1 := by
      calc _ ≤ (range (n / G' + 1)).card := by
            apply card_le_card
            intro c hc
            obtain ⟨p, hp, rfl⟩ := mem_image.1 hc
            rw [mem_range]
            have := Nat.div_le_div_right (c := G') (mem_range.1 (hT hp)).le
            omega
        _ = _ := card_range _
    have h5 : (n / G' + 1) * G' ≤ n + G' := by
      have := Nat.div_mul_le_self n G'
      rw [add_mul, one_mul]; omega
    calc T.card * G' ≤ ((n / G' + 1) * N₁) * G' :=
          Nat.mul_le_mul_right _ (hcard.trans (Nat.mul_le_mul_right _ himg))
      _ = N₁ * ((n / G' + 1) * G') := by ring
      _ ≤ N₁ * (n + G') := Nat.mul_le_mul_left _ h5

end Formalism.GrowthSums
