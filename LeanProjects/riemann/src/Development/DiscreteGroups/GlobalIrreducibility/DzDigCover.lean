import Mathlib

namespace DiscreteGroups.sglob.DzDig

open Finset

theorem cover_bound (N e D : ℕ) :
    #((range N).filter (fun u => 0 < u * D % N ∧ u * D % N < e)) ≤ e - 1 := by
  rcases Nat.eq_zero_or_pos D with hD | hD0
  · subst hD; simp
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0; simp
  have hgpos : 0 < N.gcd D := Nat.gcd_pos_of_pos_right N hD0
  have hgN : N.gcd D ∣ N := Nat.gcd_dvd_left N D
  have hgD : N.gcd D ∣ D := Nat.gcd_dvd_right N D
  have hE : N / N.gcd D * N.gcd D = N := Nat.div_mul_cancel hgN
  have hEpos : 0 < N / N.gcd D := Nat.div_pos (Nat.le_of_dvd hNpos hgN) hgpos
  calc #((range N).filter (fun u => 0 < u * D % N ∧ u * D % N < e))
      ≤ #(((Ioc 0 (e - 1)).filter (fun a => N.gcd D ∣ a)) ×ˢ range (N.gcd D)) := by
        apply card_le_card_of_injOn (fun u => (u * D % N, u / (N / N.gcd D)))
        · intro u hu
          have hu' := mem_coe.mp hu
          rw [mem_filter, mem_range] at hu'
          simp only [mem_coe, mem_product, mem_filter, mem_Ioc, mem_range]
          refine ⟨⟨⟨hu'.2.1, by omega⟩, (Nat.dvd_mod_iff hgN).mpr (dvd_mul_of_dvd_right hgD u)⟩, ?_⟩
          rw [Nat.div_lt_iff_lt_mul hEpos, mul_comm, hE]
          exact hu'.1
        · intro u _ v _ huv
          simp only [Prod.mk.injEq] at huv
          have h1 : u * D ≡ v * D [MOD N] := huv.1
          have h2 : u % (N / N.gcd D) = v % (N / N.gcd D) := Nat.ModEq.cancel_right_div_gcd hNpos h1
          calc u = N / N.gcd D * (u / (N / N.gcd D)) + u % (N / N.gcd D) := (Nat.div_add_mod u _).symm
            _ = N / N.gcd D * (v / (N / N.gcd D)) + v % (N / N.gcd D) := by rw [huv.2, h2]
            _ = v := Nat.div_add_mod v _
    _ = (e - 1) / N.gcd D * N.gcd D := by
        rw [card_product, Nat.Ioc_filter_dvd_card_eq_div, card_range]
    _ ≤ e - 1 := Nat.div_mul_le_self _ _

theorem diff_mod {N a b u : ℕ} (hN : 0 < N) (hle : u * b % N ≤ u * a % N) :
    u * (a % N + (N - b % N)) % N = u * a % N - u * b % N := by
  have hb := Nat.mod_lt b hN
  have h1 : u * (a % N + (N - b % N)) + u * (b % N) = u * (a % N) + N * u := by
    have h0 : a % N + (N - b % N) + b % N = a % N + N := by omega
    calc u * (a % N + (N - b % N)) + u * (b % N) = u * (a % N + (N - b % N) + b % N) := by ring
      _ = u * (a % N + N) := by rw [h0]
      _ = u * (a % N) + N * u := by ring
  have h3 : (u * (a % N + (N - b % N)) + u * (b % N)) % N = u * a % N := by
    rw [h1, Nat.add_mul_mod_self_left, Nat.mul_mod_mod]
  rw [Nat.add_mod, Nat.mul_mod_mod] at h3
  have hr := Nat.mod_lt (u * (a % N + (N - b % N))) hN
  have hx := Nat.mod_lt (u * a) hN
  rcases Nat.lt_or_ge (u * (a % N + (N - b % N)) % N + u * b % N) N with h | h
  · rw [Nat.mod_eq_of_lt h] at h3; omega
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)] at h3; omega

theorem totient_le {N e n k k' p : ℕ} (hN : 0 < N) (he : 0 < e)
    (hno : ∀ j < n, ¬ k' ≡ k * p ^ j [MOD N])
    (hm : ∀ u < N, N.Coprime u → ∃ j < n, p ^ j * (u * k % N) % N / e = u * k' % N / e) :
    N.totient ≤ n * (2 * (e - 1)) := by
  have hsub : (range N).filter (fun a => N.Coprime a) ⊆ (range n).biUnion (fun j =>
      (range N).filter (fun u => 0 < u * (k' % N + (N - k * p ^ j % N)) % N
          ∧ u * (k' % N + (N - k * p ^ j % N)) % N < e)
      ∪ (range N).filter (fun u => 0 < u * (k * p ^ j % N + (N - k' % N)) % N
          ∧ u * (k * p ^ j % N + (N - k' % N)) % N < e)) := by
    intro u hu
    rw [mem_filter, mem_range] at hu
    obtain ⟨j, hj, hje⟩ := hm u hu.1 hu.2
    rw [mem_biUnion]
    refine ⟨j, mem_range.mpr hj, ?_⟩
    have hy : p ^ j * (u * k % N) % N = u * (k * p ^ j) % N := by
      rw [Nat.mul_mod_mod, show p ^ j * (u * k) = u * (k * p ^ j) by ring]
    rw [hy] at hje
    have hb1 := Nat.div_add_mod (u * k' % N) e
    have hb2 := Nat.div_add_mod (u * (k * p ^ j) % N) e
    have hm1 := Nat.mod_lt (u * k' % N) he
    have hm2 := Nat.mod_lt (u * (k * p ^ j) % N) he
    rw [hje] at hb2
    rw [mem_union, mem_filter, mem_filter, mem_range]
    rcases lt_trichotomy (u * (k * p ^ j) % N) (u * k' % N) with h | h | h
    · left
      rw [diff_mod hN h.le]
      exact ⟨hu.1, by omega, by omega⟩
    · exfalso
      apply hno j hj
      have h' : u * k' ≡ u * (k * p ^ j) [MOD N] := h.symm
      exact Nat.ModEq.cancel_left_of_coprime hu.2 h'
    · right
      rw [diff_mod hN h.le]
      exact ⟨hu.1, by omega, by omega⟩
  calc N.totient = #((range N).filter (fun a => N.Coprime a)) := Nat.totient_eq_card_coprime N
    _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_biUnion_le
    _ ≤ ∑ j ∈ range n, 2 * (e - 1) := by
        apply sum_le_sum
        intro j _
        calc _ ≤ _ := card_union_le _ _
          _ ≤ (e - 1) + (e - 1) := add_le_add (cover_bound _ _ _) (cover_bound _ _ _)
          _ = 2 * (e - 1) := by ring
    _ = n * (2 * (e - 1)) := by rw [sum_const, card_range, smul_eq_mul]

end DiscreteGroups.sglob.DzDig
