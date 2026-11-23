import Development.DiscreteGroups.GlobalIrreducibility.DzStickDigits

namespace DiscreteGroups.sglob.DzDig

open Finset

def ee (p n : ℕ) : ℕ := ∑ j ∈ range n, p ^ j

def cnt (p n x c : ℕ) : ℕ := #((range n).filter (fun i => c ≤ p ^ i * x % (p ^ n - 1) / ee p n))

theorem N_eq {p n : ℕ} (hp : 2 ≤ p) : p ^ n - 1 = (p - 1) * ee p n :=
  (Stick.geom_sum_mul_pred p n hp).symm

theorem ee_eq {p n : ℕ} (hp : 2 ≤ p) : (p ^ n - 1) / (p - 1) = ee p n := by
  rw [N_eq hp, Nat.mul_div_cancel_left _ (by omega : 0 < p - 1)]

theorem ee_pos {p n : ℕ} (hn : 1 ≤ n) : 0 < ee p n := by
  unfold ee
  calc 0 < 1 := one_pos
    _ = p ^ 0 := (pow_zero p).symm
    _ ≤ ∑ j ∈ range n, p ^ j :=
        single_le_sum (f := fun j => p ^ j) (fun j _ => Nat.zero_le _) (by simp; omega)

theorem N_pos {p n : ℕ} (hp : 2 ≤ p) (hn : 1 ≤ n) : 0 < p ^ n - 1 := by
  rw [N_eq hp]; exact Nat.mul_pos (by omega) (ee_pos hn)

theorem e_mul_dsum {p n a : ℕ} (hp : 2 ≤ p) (ha : a < p ^ n - 1) :
    ee p n * Stick.dsum p a = ∑ i ∈ range n, p ^ i * a % (p ^ n - 1) := by
  have h := Stick.dsum_frac hp ha
  have hpos : 0 < p - 1 := by omega
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h, N_eq hp]
  ring

theorem pow_mul_ee {p n : ℕ} (hp : 2 ≤ p) (i : ℕ) :
    p ^ i * ee p n = ee p n + (p ^ n - 1) * ee p i := by
  have h2 : p ^ i - 1 = (p - 1) * ee p i := N_eq hp
  have h3 : 0 < p ^ i := pow_pos (by omega) i
  have h4 : p ^ i = (p - 1) * ee p i + 1 := by omega
  rw [N_eq (n := n) hp, h4]
  ring

theorem mod_shift {p n x b : ℕ} (hp : 2 ≤ p) (i : ℕ) :
    p ^ i * ((x + b * ee p n) % (p ^ n - 1)) % (p ^ n - 1)
      = (p ^ i * x % (p ^ n - 1) + b * ee p n) % (p ^ n - 1) := by
  rw [Nat.mul_mod_mod, Nat.mod_add_mod]
  have h : p ^ i * (x + b * ee p n) = p ^ i * x + b * ee p n + (p ^ n - 1) * (b * ee p i) := by
    calc p ^ i * (x + b * ee p n) = p ^ i * x + b * (p ^ i * ee p n) := by ring
      _ = _ := by rw [pow_mul_ee hp i]; ring
  rw [h, Nat.add_mul_mod_self_left]

theorem shift_mod {M e r b : ℕ} (he : 0 < e) (hr : r < M * e) :
    (r + b * e) % (M * e) = ((r / e + b) % M) * e + r % e := by
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · simp [h] at hr
    · exact h
  have h1 := Nat.div_add_mod r e
  have h2 := Nat.div_add_mod (r / e + b) M
  have h3 : (r / e + b) % M < M := Nat.mod_lt _ hM
  have h4 : r % e < e := Nat.mod_lt _ he
  have h5 : r + b * e = (((r / e + b) % M) * e + r % e) + (M * e) * ((r / e + b) / M) := by
    have h6 : r + b * e = (r / e + b) * e + r % e := by
      rw [add_mul]; linarith [h1]
    rw [h6]
    conv_lhs => rw [← h2]
    ring
  rw [h5, Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  calc ((r / e + b) % M) * e + r % e < ((r / e + b) % M) * e + e := by omega
    _ = ((r / e + b) % M + 1) * e := by ring
    _ ≤ M * e := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt h3)

theorem point {M e r b : ℕ} (he : 0 < e) (hr : r < M * e) (hb : b < M) :
    (r + b * e) % (M * e) + M * e * (if M - b ≤ r / e then 1 else 0) = r + b * e := by
  rw [shift_mod he hr]
  have hq : r / e < M := Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hr)
  have h1 := Nat.div_add_mod r e
  split_ifs with h
  · obtain ⟨D, hD⟩ : ∃ D, r / e + b = D + M := ⟨r / e + b - M, by omega⟩
    have hm : (r / e + b) % M = D := by
      rw [hD, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hm]
    conv_rhs => rw [← h1]
    calc D * e + r % e + M * e * 1 = (D + M) * e + r % e := by ring
      _ = (r / e + b) * e + r % e := by rw [hD]
      _ = e * (r / e) + r % e + b * e := by ring
  · have hm : (r / e + b) % M = r / e + b := Nat.mod_eq_of_lt (by omega)
    rw [hm]
    conv_rhs => rw [← h1]
    ring

theorem count_shift {p n x b : ℕ} (hp : 2 ≤ p) (hn : 1 ≤ n) (hx : x < p ^ n - 1) (hb : b < p - 1) :
    Stick.dsum p ((x + b * ee p n) % (p ^ n - 1)) + (p - 1) * cnt p n x (p - 1 - b)
      = Stick.dsum p x + n * b := by
  have he := ee_pos (p := p) hn
  have hN := N_eq (n := n) hp
  have hNpos := N_pos hp hn
  have h1 := e_mul_dsum hp (Nat.mod_lt (x + b * ee p n) hNpos)
  have h2 := e_mul_dsum hp hx
  have h3 : ∑ i ∈ range n, p ^ i * ((x + b * ee p n) % (p ^ n - 1)) % (p ^ n - 1)
      + (p - 1) * ee p n * cnt p n x (p - 1 - b)
      = ∑ i ∈ range n, p ^ i * x % (p ^ n - 1) + n * (b * ee p n) := by
    unfold cnt
    rw [card_filter, mul_sum, ← sum_add_distrib]
    have : n * (b * ee p n) = ∑ i ∈ range n, b * ee p n := by simp
    rw [this, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rw [mod_shift hp i, hN]
    exact point he (Nat.mod_lt _ (by rw [← hN]; exact hNpos)) hb
  apply Nat.eq_of_mul_eq_mul_left he
  calc ee p n * (Stick.dsum p ((x + b * ee p n) % (p ^ n - 1)) + (p - 1) * cnt p n x (p - 1 - b))
      = ee p n * Stick.dsum p ((x + b * ee p n) % (p ^ n - 1))
          + (p - 1) * ee p n * cnt p n x (p - 1 - b) := by ring
    _ = ∑ i ∈ range n, p ^ i * x % (p ^ n - 1) + n * (b * ee p n) := by rw [h1, h3]
    _ = ee p n * Stick.dsum p x + n * (b * ee p n) := by rw [h2]
    _ = ee p n * (Stick.dsum p x + n * b) := by ring

theorem cnt_zero (p n y : ℕ) : cnt p n y 0 = n := by
  unfold cnt
  rw [filter_true_of_mem (fun i _ => Nat.zero_le _), card_range]

theorem cnt_top {p n y : ℕ} (hp : 2 ≤ p) (hn : 1 ≤ n) : cnt p n y (p - 1) = 0 := by
  unfold cnt
  have hNpos := N_pos hp hn
  rw [filter_false_of_mem, card_empty]
  intro i _ hle
  have hlt : p ^ i * y % (p ^ n - 1) < ee p n * (p - 1) := by
    rw [mul_comm (ee p n), ← N_eq hp]; exact Nat.mod_lt _ hNpos
  have := Nat.div_lt_of_lt_mul hlt
  omega

theorem exists_match {p n x x' : ℕ} (hx' : x' < p ^ n - 1)
    (h0 : cnt p n x (x' / ee p n) = cnt p n x' (x' / ee p n))
    (h1 : cnt p n x (x' / ee p n + 1) = cnt p n x' (x' / ee p n + 1)) (hn : 1 ≤ n) :
    ∃ j < n, p ^ j * x % (p ^ n - 1) / ee p n = x' / ee p n := by
  by_contra hne
  push_neg at hne
  have hA : (range n).filter (fun i => x' / ee p n ≤ p ^ i * x % (p ^ n - 1) / ee p n)
      = (range n).filter (fun i => x' / ee p n + 1 ≤ p ^ i * x % (p ^ n - 1) / ee p n) := by
    apply filter_congr
    intro i hi
    have := hne i (mem_range.mp hi)
    omega
  have hz : p ^ 0 * x' % (p ^ n - 1) = x' := by
    rw [pow_zero, one_mul, Nat.mod_eq_of_lt hx']
  have hB : (range n).filter (fun i => x' / ee p n + 1 ≤ p ^ i * x' % (p ^ n - 1) / ee p n)
      ⊆ ((range n).filter (fun i => x' / ee p n ≤ p ^ i * x' % (p ^ n - 1) / ee p n)).erase 0 := by
    intro i hi
    rw [mem_filter, mem_range] at hi
    rw [mem_erase, mem_filter, mem_range]
    refine ⟨?_, hi.1, by omega⟩
    rintro rfl
    have h2 := hi.2
    rw [hz] at h2
    omega
  have h0mem : 0 ∈ (range n).filter (fun i => x' / ee p n ≤ p ^ i * x' % (p ^ n - 1) / ee p n) := by
    rw [mem_filter, mem_range, hz]
    exact ⟨by omega, le_refl _⟩
  have hle := card_le_card hB
  rw [card_erase_of_mem h0mem] at hle
  have hpos := card_pos.mpr ⟨0, h0mem⟩
  unfold cnt at h0 h1
  rw [hA] at h0
  omega

theorem match_of_hyp {p n k k' u : ℕ} (hp : 2 ≤ p) (hn : 1 ≤ n)
    (H : ∀ b : ℕ, Stick.dsum p ((u * k + b * ee p n) % (p ^ n - 1)) + Stick.dsum p (u * k' % (p ^ n - 1))
        = Stick.dsum p ((u * k' + b * ee p n) % (p ^ n - 1)) + Stick.dsum p (u * k % (p ^ n - 1))) :
    ∃ j < n, p ^ j * (u * k % (p ^ n - 1)) % (p ^ n - 1) / ee p n = u * k' % (p ^ n - 1) / ee p n := by
  have hNpos := N_pos hp hn
  have hx : u * k % (p ^ n - 1) < p ^ n - 1 := Nat.mod_lt _ hNpos
  have hx' : u * k' % (p ^ n - 1) < p ^ n - 1 := Nat.mod_lt _ hNpos
  have hcnt : ∀ c, c ≤ p - 1 →
      cnt p n (u * k % (p ^ n - 1)) c = cnt p n (u * k' % (p ^ n - 1)) c := by
    intro c hc
    rcases Nat.eq_zero_or_pos c with rfl | hc0
    · rw [cnt_zero, cnt_zero]
    rcases Nat.eq_or_lt_of_le hc with rfl | hc1
    · rw [cnt_top hp hn, cnt_top hp hn]
    have hb : p - 1 - c < p - 1 := by omega
    have hcb : p - 1 - (p - 1 - c) = c := by omega
    have s1 := count_shift (b := p - 1 - c) hp hn hx hb
    have s2 := count_shift (b := p - 1 - c) hp hn hx' hb
    rw [hcb, Nat.mod_add_mod] at s1 s2
    have s3 := H (p - 1 - c)
    have key : (p - 1) * cnt p n (u * k % (p ^ n - 1)) c
        = (p - 1) * cnt p n (u * k' % (p ^ n - 1)) c := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) key
  have hlt : u * k' % (p ^ n - 1) / ee p n < p - 1 := by
    apply Nat.div_lt_of_lt_mul
    rw [mul_comm (ee p n), ← N_eq hp]; exact hx'
  exact exists_match hx' (hcnt _ hlt.le) (hcnt _ hlt) hn

end DiscreteGroups.sglob.DzDig
