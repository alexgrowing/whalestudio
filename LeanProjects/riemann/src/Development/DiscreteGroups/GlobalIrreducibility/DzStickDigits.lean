import Development.DiscreteGroups.GlobalIrreducibility.DzStickDefs

namespace DiscreteGroups.sglob.Stick

theorem dsum_rec {p : ℕ} (hp : 2 ≤ p) (a : ℕ) : dsum p a = a % p + dsum p (a / p) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [dsum]
  · unfold dsum
    rw [Nat.digits_def' (by omega) ha, List.sum_cons]

theorem dsum_zero (p : ℕ) : dsum p 0 = 0 := by simp [dsum]

theorem dsum_of_lt {p a : ℕ} (hp : 2 ≤ p) (ha : a < p) : dsum p a = a := by
  rw [dsum_rec hp, Nat.mod_eq_of_lt ha, Nat.div_eq_of_lt ha, dsum_zero, add_zero]

theorem dsum_legendre {p : ℕ} (hp : 2 ≤ p) (f : ℕ) : ∀ a : ℕ, a < p ^ f →
    (p - 1) * ∑ j ∈ Finset.range f, a / p ^ (j + 1) + dsum p a = a := by
  induction f with
  | zero =>
    intro a ha
    have : a = 0 := by simpa using ha
    subst this
    simp [dsum_zero]
  | succ f ih =>
    intro a ha
    have hx : a / p < p ^ f := by
      apply Nat.div_lt_of_lt_mul
      rwa [pow_succ, mul_comm] at ha
    have h1 := ih (a / p) hx
    have h2 : ∑ j ∈ Finset.range (f + 1), a / p ^ (j + 1)
        = ∑ j ∈ Finset.range f, a / p / p ^ (j + 1) + a / p := by
      rw [Finset.sum_range_succ']
      congr 1
      · apply Finset.sum_congr rfl
        intro j _
        rw [Nat.div_div_eq_div_mul, pow_succ p (j + 1), mul_comm]
      · simp
    rw [h2, dsum_rec hp a, mul_add]
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
    have h3 := Nat.div_add_mod a (k + 1)
    simp only [Nat.add_sub_cancel] at h1 ⊢
    have h4 : (k + 1) * (a / (k + 1)) = k * (a / (k + 1)) + a / (k + 1) := by ring
    omega

theorem dsum_modEq {p : ℕ} (hp : 2 ≤ p) (a : ℕ) : dsum p a ≡ a [MOD p - 1] := by
  have h := dsum_legendre hp a a (Nat.lt_pow_self (by omega))
  unfold Nat.ModEq
  conv_rhs => rw [← h]
  rw [Nat.mul_add_mod]

theorem dsum_compl {p : ℕ} (hp : 2 ≤ p) (f a : ℕ) (ha : a ≤ p ^ f - 1) :
    dsum p a + dsum p (p ^ f - 1 - a) = f * (p - 1) := by
  induction f generalizing a with
  | zero =>
    have : a = 0 := by simpa using ha
    subst this
    simp [dsum_zero]
  | succ f ih =>
    have hq : 0 < p ^ f := pow_pos (by omega) f
    have hpq : p ^ (f + 1) = p * p ^ f := by rw [pow_succ, mul_comm]
    have hpos : 0 < p * p ^ f := Nat.mul_pos (by omega) hq
    have hx : a / p < p ^ f := by
      apply Nat.div_lt_of_lt_mul
      omega
    have hr : a % p < p := Nat.mod_lt _ (by omega)
    have hc : p ^ (f + 1) - 1 - a = p * (p ^ f - 1 - a / p) + (p - 1 - a % p) := by
      have h3 := Nat.div_add_mod a p
      obtain ⟨y, hy⟩ : ∃ y, p ^ f = a / p + 1 + y := ⟨p ^ f - 1 - a / p, by omega⟩
      have h5 : p ^ f - 1 - a / p = y := by omega
      rw [h5, hpq, hy]
      have h6 : p * (a / p + 1 + y) = p * (a / p) + p + p * y := by ring
      omega
    have h1 := ih (a / p) (by omega)
    rw [dsum_rec hp a, dsum_rec hp (p ^ (f + 1) - 1 - a), hc, Nat.mul_add_mod,
      Nat.mod_eq_of_lt (by omega : p - 1 - a % p < p), Nat.mul_add_div (by omega),
      Nat.div_eq_of_lt (by omega : p - 1 - a % p < p), add_zero, add_mul, one_mul]
    omega

theorem mul_mod_pred_add {A B a : ℕ} (ha : a < A * B - 1) :
    A * a % (A * B - 1) + (A * B - 1) * (a / B) = A * a := by
  obtain ⟨M, hM⟩ : ∃ M, A * B = M + 1 := ⟨A * B - 1, by omega⟩
  have hA : 0 < A := by
    rcases Nat.eq_zero_or_pos A with rfl | h
    · simp at hM
    · exact h
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with rfl | h
    · simp at hM
    · exact h
  rw [hM, Nat.add_sub_cancel] at ha ⊢
  have hw : a / B < A := by
    apply Nat.div_lt_of_lt_mul
    rw [mul_comm]; omega
  have hu : a % B < B := Nat.mod_lt _ hB
  have h3 := Nat.div_add_mod a B
  set w := a / B
  set u := a % B
  have h4 : A * a = A * u + w + M * w := by
    rw [← h3]
    calc A * (B * w + u) = (A * B) * w + A * u := by ring
      _ = (M + 1) * w + A * u := by rw [hM]
      _ = A * u + w + M * w := by ring
  have h5 : A * u + A ≤ M + 1 := by
    rw [← hM]
    calc A * u + A = A * (u + 1) := by ring
      _ ≤ A * B := Nat.mul_le_mul_left _ hu
  have h6 : A * u + w < M := by
    by_contra hcon
    have e1 : w + 1 = A := by omega
    have e2 : A * (u + 1) = A * B := by
      rw [hM, mul_add, mul_one]; omega
    have e3 : u + 1 = B := Nat.eq_of_mul_eq_mul_left hA e2
    have e4 : a + 1 = M + 1 := by
      rw [← hM, ← h3, ← e1]
      calc B * w + u + 1 = B * w + (u + 1) := by ring
        _ = B * w + B := by rw [e3]
        _ = (w + 1) * B := by ring
    omega
  rw [h4, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h6]

theorem pow_mul_mod {p : ℕ} (hp : 2 ≤ p) {f a i : ℕ} (ha : a < p ^ f - 1) (hi : i ≤ f) :
    p ^ i * a % (p ^ f - 1) + (p ^ f - 1) * (a / p ^ (f - i)) = p ^ i * a := by
  have h : p ^ f = p ^ i * p ^ (f - i) := by rw [← pow_add, Nat.add_sub_cancel' hi]
  rw [h] at ha ⊢
  exact mul_mod_pred_add ha

theorem geom_sum_mul_pred (p f : ℕ) (hp : 2 ≤ p) :
    (p - 1) * ∑ i ∈ Finset.range f, p ^ i = p ^ f - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction f with
  | zero => simp
  | succ f ih =>
    have hq : 0 < (k + 1) ^ f := pow_pos (by omega) f
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    have : (k + 1) ^ f * (k + 1) = k * (k + 1) ^ f + (k + 1) ^ f := by ring
    omega

theorem dsum_frac {p : ℕ} (hp : 2 ≤ p) {f a : ℕ} (ha : a < p ^ f - 1) :
    (p - 1) * ∑ i ∈ Finset.range f, p ^ i * a % (p ^ f - 1) = (p ^ f - 1) * dsum p a := by
  have hS : ∑ i ∈ Finset.range f, a / p ^ (f - i) = ∑ j ∈ Finset.range f, a / p ^ (j + 1) := by
    rw [← Finset.sum_range_reflect (fun j => a / p ^ (j + 1)) f]
    apply Finset.sum_congr rfl
    intro j hj
    have := Finset.mem_range.mp hj
    congr 2
    omega
  have hT : ∑ i ∈ Finset.range f, p ^ i * a % (p ^ f - 1)
      + (p ^ f - 1) * ∑ j ∈ Finset.range f, a / p ^ (j + 1)
      = (∑ i ∈ Finset.range f, p ^ i) * a := by
    rw [← hS, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    exact pow_mul_mod hp ha (Finset.mem_range.mp hi).le
  have hL := dsum_legendre hp f a (by omega)
  have hG := geom_sum_mul_pred p f hp
  set T := ∑ i ∈ Finset.range f, p ^ i * a % (p ^ f - 1)
  set S := ∑ j ∈ Finset.range f, a / p ^ (j + 1)
  set G := ∑ i ∈ Finset.range f, p ^ i
  set M := p ^ f - 1
  set k := p - 1
  have key : k * T + M * (k * S) = M * dsum p a + M * (k * S) := by
    calc k * T + M * (k * S) = k * (T + M * S) := by ring
      _ = (k * G) * a := by rw [hT]; ring
      _ = M * (k * S + dsum p a) := by rw [hG, hL]
      _ = M * dsum p a + M * (k * S) := by ring
  exact Nat.add_right_cancel key

theorem dsum_frac_dvd {p : ℕ} (hp : 2 ≤ p) {f N d b : ℕ} (hN : N * d = p ^ f - 1) (hb : b < N) :
    (p - 1) * ∑ i ∈ Finset.range f, p ^ i * b % N = N * dsum p (d * b) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hf : f = 0 := by
      by_contra hf
      have : p ^ 1 ≤ p ^ f := Nat.pow_le_pow_right (by omega) (Nat.pos_of_ne_zero hf)
      simp at hN this
      omega
    subst hf
    simp [dsum_zero]
  · have ha : d * b < p ^ f - 1 := by
      rw [← hN, mul_comm N d]
      exact Nat.mul_lt_mul_of_pos_left hb hd
    have h := dsum_frac hp ha
    rw [← hN] at h
    have h2 : ∑ i ∈ Finset.range f, p ^ i * (d * b) % (N * d)
        = d * ∑ i ∈ Finset.range f, p ^ i * b % N := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_comm N d, mul_left_comm, Nat.mul_mod_mul_left]
    rw [h2] at h
    apply Nat.eq_of_mul_eq_mul_left hd
    calc d * ((p - 1) * ∑ i ∈ Finset.range f, p ^ i * b % N)
        = (p - 1) * (d * ∑ i ∈ Finset.range f, p ^ i * b % N) := by ring
      _ = N * d * dsum p (d * b) := h
      _ = d * (N * dsum p (d * b)) := by ring

end DiscreteGroups.sglob.Stick
