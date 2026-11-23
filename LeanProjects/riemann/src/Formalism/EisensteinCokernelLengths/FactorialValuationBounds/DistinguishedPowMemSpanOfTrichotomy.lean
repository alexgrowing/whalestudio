import Formalism.EisensteinCokernelLengths.ExponentChainBound

noncomputable section

namespace Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria

section Key

variable {A : Type} [CommRing A]

theorem rel_mem_of_le {X l : A} {M η E : ℕ} (c a i : ℕ) (h : E ≤ c) :
    l ^ c * X ^ a * (X + l) ^ i ∈ Ideal.span {l ^ E, X ^ M * (X + l) ^ η} := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have e : l ^ (E + d) * X ^ a * (X + l) ^ i = (l ^ d * X ^ a * (X + l) ^ i) * l ^ E := by ring
  rw [e]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _))

theorem rel_mem_of_ge {X l : A} {M η E : ℕ} (c a i : ℕ) (ha : M ≤ a) (hi : η ≤ i) :
    l ^ c * X ^ a * (X + l) ^ i ∈ Ideal.span {l ^ E, X ^ M * (X + l) ^ η} := by
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨i', rfl⟩ := Nat.exists_eq_add_of_le hi
  have e : l ^ c * X ^ (M + a') * (X + l) ^ (η + i') =
      (l ^ c * X ^ a' * (X + l) ^ i') * (X ^ M * (X + l) ^ η) := by ring
  rw [e]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem rel_key_high (X l : A) (M η E : ℕ) :
    ∀ j c i : ℕ, (E ≤ c ∨ η ≤ i ∨ E + η ≤ c + j + i + 1) →
      l ^ c * X ^ (M + j) * (X + l) ^ i ∈ Ideal.span {l ^ E, X ^ M * (X + l) ^ η} := by
  intro j
  induction j with
  | zero =>
    intro c i h
    by_cases hc : E ≤ c
    · exact rel_mem_of_le c _ i hc
    by_cases hi : η ≤ i
    · exact rel_mem_of_ge c _ i (Nat.le_add_right M 0) hi
    exfalso
    omega
  | succ j ih =>
    intro c i h
    by_cases hc : E ≤ c
    · exact rel_mem_of_le c _ i hc
    by_cases hi : η ≤ i
    · exact rel_mem_of_ge c _ i (Nat.le_add_right M (j + 1)) hi
    have e : l ^ c * X ^ (M + (j + 1)) * (X + l) ^ i =
        l ^ c * X ^ (M + j) * (X + l) ^ (i + 1) - l ^ (c + 1) * X ^ (M + j) * (X + l) ^ i := by
      ring
    rw [e]
    exact Ideal.sub_mem _ (ih c (i + 1) (by omega)) (ih (c + 1) i (by omega))

theorem rel_key (X l : A) (M η E : ℕ) :
    ∀ i a c : ℕ, (E ≤ c ∨ (M ≤ a ∧ η ≤ i) ∨ E + η + M ≤ c + a + i + 1) →
      l ^ c * X ^ a * (X + l) ^ i ∈ Ideal.span {l ^ E, X ^ M * (X + l) ^ η} := by
  intro i
  induction i with
  | zero =>
    intro a c h
    by_cases ha : M ≤ a
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le ha
      exact rel_key_high X l M η E j c 0 (by omega)
    · exact rel_mem_of_le c a 0 (by omega)
  | succ i ih =>
    intro a c h
    by_cases ha : M ≤ a
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le ha
      exact rel_key_high X l M η E j c (i + 1) (by omega)
    have e : l ^ c * X ^ a * (X + l) ^ (i + 1) =
        l ^ c * X ^ (a + 1) * (X + l) ^ i + l ^ (c + 1) * X ^ a * (X + l) ^ i := by ring
    rw [e]
    exact Ideal.add_mem _ (ih (a + 1) c (by omega)) (ih a (c + 1) (by omega))

end Key

theorem rel_ceil_le (m r K : ℕ) (hm : 1 ≤ m) (h : r * (m + 1) ≤ K * m) :
    ⌈(r : ℝ) * ((m + 1 : ℕ) : ℝ) / (m : ℝ)⌉₊ ≤ K := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  rw [Nat.ceil_le, div_le_iff₀ hm']
  exact_mod_cast h

theorem le_div_add_one_or_add_le (m r T L : ℕ) (hm : 1 ≤ m) (hL : ∀ K, r * (m + 1) ≤ K * m → L ≤ K) :
    L ≤ T / m + 1 ∨ L + T ≤ T / m + 1 + (m * r + r) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  by_cases h : L ≤ T / (n + 1) + 1
  · exact Or.inl h
  right
  have hT := Nat.div_add_mod T (n + 1)
  have ht := Nat.mod_lt T (show n + 1 > 0 by omega)
  set q := T / (n + 1) with hq0
  set t := T % (n + 1) with ht0
  have hq : (q + 1) * (n + 1) + 1 ≤ r * (n + 1 + 1) := by
    by_contra hc
    have := hL (q + 1) (by omega)
    omega
  have hK := Nat.div_add_mod (r * (n + 1 + 1) + n) (n + 1)
  have hKm := Nat.mod_lt (r * (n + 1 + 1) + n) (show n + 1 > 0 by omega)
  set K := (r * (n + 1 + 1) + n) / (n + 1) with hK0
  set ρ := (r * (n + 1 + 1) + n) % (n + 1) with hρ0
  have hLK : L ≤ K := hL K (by nlinarith)
  have a1 := Nat.mul_le_mul_left (n + 1) hLK
  have a2 := Nat.mul_le_mul_left (n + 1) (show t ≤ n by omega)
  have a3 := Nat.mul_le_mul_left n hq
  have a4 : (n + 1) * T = (n + 1) * ((n + 1) * q + t) := by rw [hT]
  apply le_of_mul_le_mul_left _ (show 0 < n + 1 by omega)
  nlinarith [a1, a2, a3, a4, hK]

theorem mul_succ_le_of_sq_mul_le (m r s b e : ℕ) (hm : 2 ≤ m) (hb : b < s * m ^ 2)
    (he : (m + 1) ^ 2 * r ≤ (m + 1) * e + b) : r * (m + 1) ≤ (s + e) * m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  apply le_of_mul_le_mul_left _ (show 0 < n + 2 + 1 by omega)
  nlinarith [Nat.zero_le (e * n * n), Nat.zero_le (e * n), Nat.zero_le (s * n), Nat.zero_le e,
    Nat.zero_le s]

theorem exponent_trichotomy (m r s b L k : ℕ) (hm : 2 ≤ m) (hb : b < s * m ^ 2)
    (hL : ∀ K, r * (m + 1) ≤ K * m → L ≤ K) (hL0 : r = 0 → L = 0) (hk : k ≤ m * r) :
    L ≤ s + k ∨ (1 ≤ r ∧ b ≤ m * r + (m + 1) * (m * r - k)) ∨
      L + b + 1 ≤ s + k + r + (m * r + (m + 1) * (m * r - k)) + 1 := by
  set D := m * r + (m + 1) * (m * r - k) with hD
  obtain ⟨j, hj⟩ : ∃ j, m * r = k + j := ⟨m * r - k, by omega⟩
  have hj' : m * r - k = j := by omega
  have h2 : m * (m * r) = m * (k + j) := by rw [hj]
  have key : (m + 1) ^ 2 * r = D + r + (m + 1) * k := by
    rw [hD, hj']
    nlinarith [hj, h2]
  by_cases hbig : r + D ≤ b
  · left
    exact hL _ (mul_succ_le_of_sq_mul_le m r s b k hm hb (by omega))
  · right; right
    set x := r + D - b with hx0
    have hx : x + b = r + D := by omega
    have hxm : x ≤ (m + 1) * x := by nlinarith [Nat.zero_le (m * x)]
    have he : (m + 1) ^ 2 * r ≤ (m + 1) * (k + x) + b := by nlinarith [hxm, key, hx]
    have := hL _ (mul_succ_le_of_sq_mul_le m r s b (k + x) hm hb he)
    omega

theorem linearFactorPowMemSpanXPow : FirstRelationModule := by
  intro A _ ℓ _ hℓ X u M η r hM
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
  have hm : 2 ≤ m := by omega
  have hcast : ((m + 1 : ℕ) : ℝ) - 1 = (m : ℝ) := by push_cast; ring
  have hfl : ⌊((M : ℝ) + η) / (m : ℝ)⌋₊ = (M + η) / m := by
    have := Nat.floor_div_eq_div (K := ℝ) (M + η) m
    push_cast at this
    exact this
  rw [hcast, hfl]
  simp only [Nat.add_sub_cancel]
  set L := ⌈(r : ℝ) * ((m + 1 : ℕ) : ℝ) / (m : ℝ)⌉₊ with hLdef
  have hL : ∀ K, r * (m + 1) ≤ K * m → L ≤ K := fun K h => rel_ceil_le m r K (by omega) h
  have e : ((m + 1 : ℕ) : A) ^ ((M + η) / m + 1) * (u * X * (X + ((m + 1 : ℕ) : A)) ^ m) ^ r =
      u ^ r * (((m + 1 : ℕ) : A) ^ ((M + η) / m + 1) * X ^ r *
        (X + ((m + 1 : ℕ) : A)) ^ (m * r)) := by
    rw [pow_mul]; ring
  rw [e]
  apply Ideal.mul_mem_left
  apply rel_key X _ M η L (m * r) r ((M + η) / m + 1)
  have := le_div_add_one_or_add_le m r (M + η) L (by omega) hL
  omega

theorem linearFactorPowMemSpan : FirstRelationTorsion := by
  intro A _ ℓ _ hℓ X u B r
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
  have hm : 2 ≤ m := by omega
  have hcast : ((m + 1 : ℕ) : ℝ) - 1 = (m : ℝ) := by push_cast; ring
  have hfl : ⌊(B : ℝ) / (m : ℝ)⌋₊ = B / m := Nat.floor_div_eq_div B m
  rw [hcast, hfl]
  simp only [Nat.add_sub_cancel]
  set L := ⌈(r : ℝ) * ((m + 1 : ℕ) : ℝ) / (m : ℝ)⌉₊ with hLdef
  have hL : ∀ K, r * (m + 1) ≤ K * m → L ≤ K := fun K h => rel_ceil_le m r K (by omega) h
  have e : ((m + 1 : ℕ) : A) ^ (B / m + 1) * (u * X * (X + ((m + 1 : ℕ) : A)) ^ m) ^ r =
      u ^ r * (((m + 1 : ℕ) : A) ^ (B / m + 1) * X ^ r * (X + ((m + 1 : ℕ) : A)) ^ (m * r)) := by
    rw [pow_mul]; ring
  rw [e]
  apply Ideal.mul_mem_left
  have key := rel_key X ((m + 1 : ℕ) : A) 1 B L (m * r) r (B / m + 1) (by
    have := le_div_add_one_or_add_le m r B L (by omega) hL
    omega)
  rwa [pow_one] at key

theorem distinguished_pow_mem_span_of_trichotomy {R : Type} [CommRing R] (Q l ε u' w : R) (ℓ b r σ L : ℕ)
    (hterm : ∀ k ≤ (ℓ - 1) * r, L ≤ σ + k ∨
      (1 ≤ r ∧ b ≤ (ℓ - 1) * r + ℓ * ((ℓ - 1) * r - k)) ∨
        L + b + 1 ≤ σ + k + r + ((ℓ - 1) * r + ℓ * ((ℓ - 1) * r - k)) + 1) :
    l ^ σ * (w * (Q - l) * Q ^ (ℓ - 1) * (l * ε + u' * Q ^ ℓ) ^ (ℓ - 1)) ^ r ∈
      Ideal.span {l ^ L, (Q - l) * Q ^ b} := by
  obtain ⟨n, hn⟩ : ∃ n, n = (ℓ - 1) * r := ⟨_, rfl⟩
  rw [← hn] at hterm
  have h1 : ∀ P : R, l ^ σ * (w * (Q - l) * Q ^ (ℓ - 1) * P ^ (ℓ - 1)) ^ r =
      w ^ r * (l ^ σ * (Q - l) ^ r * Q ^ n * P ^ n) := by
    intro P
    rw [hn, pow_mul, pow_mul, mul_pow, mul_pow, mul_pow]
    ring
  rw [h1, add_pow, Finset.mul_sum, Finset.mul_sum]
  apply Ideal.sum_mem
  intro k hk
  have hk' : k ≤ n := by simp at hk; omega
  have e : l ^ σ * (Q - l) ^ r * Q ^ n * ((l * ε) ^ k * (u' * Q ^ ℓ) ^ (n - k) * (n.choose k : R)) =
      (ε ^ k * u' ^ (n - k) * (n.choose k : R)) *
        (l ^ (σ + k) * (Q - l) ^ r * Q ^ (n + ℓ * (n - k))) := by
    rw [mul_pow, mul_pow, ← pow_mul, pow_add, pow_add]
    ring
  rw [e]
  have key := rel_key (Q - l) l 1 b L (n + ℓ * (n - k)) r (σ + k) (by
    have := hterm k hk'
    omega)
  rw [sub_add_cancel, pow_one] at key
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ key)

theorem distinguishedPowMemSpan : SecondRelationTorsion := by
  unfold SecondRelationTorsion
  intro O _ ℓ _ hℓ ε u' w b r
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
  have hden : ((m + 1 : ℕ) : ℝ) - 1 = (m : ℝ) := by push_cast; ring
  have hfl : ⌊(b : ℝ) / (m : ℝ) ^ 2⌋₊ = b / m ^ 2 := by
    rw [← Nat.cast_pow]
    exact Nat.floor_div_eq_div _ _
  rw [hden, hfl]
  have hL : ∀ K, r * (m + 1) ≤ K * m → ⌈(r : ℝ) * ((m + 1 : ℕ) : ℝ) / (m : ℝ)⌉₊ ≤ K :=
    fun K hK => rel_ceil_le m r K (by omega) hK
  have hL0 : r = 0 → ⌈(r : ℝ) * ((m + 1 : ℕ) : ℝ) / (m : ℝ)⌉₊ = 0 := by
    rintro rfl
    simp
  have hb : b < (b / m ^ 2 + 1) * m ^ 2 := by
    have h1 := Nat.div_add_mod b (m ^ 2)
    have h2 := Nat.mod_lt b (pow_pos (by omega : 0 < m) 2)
    nlinarith [h1, h2]
  simp only [map_pow, Formalism.WindowSums.p1]
  apply distinguished_pow_mem_span_of_trichotomy
  intro k hk
  simp only [Nat.add_sub_cancel] at hk ⊢
  exact exponent_trichotomy m r (b / m ^ 2 + 1) b _ k (by omega) hb hL hL0 hk

end Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria
