import Mathlib
open MvPolynomial

namespace GlobalTheory.DegreeBound

variable {K : Type} [Field K] {D : ℕ}

def Good (y : Fin D → K) (j : Fin D) (N : ℕ) (b : K) : Prop :=
  ∃ C : MvPolynomial (Fin D) ℤ, C.totalDegree ≤ N ∧ b * y j ^ N = aeval y C

lemma good_mono {y : Fin D → K} {j : Fin D} {N : ℕ} {b : K} (h : Good y j N b) (M : ℕ) :
    Good y j (N + M) b := by
  obtain ⟨C, hC, he⟩ := h
  refine ⟨C * X j ^ M, (totalDegree_mul _ _).trans (by rw [totalDegree_X_pow]; omega), ?_⟩
  rw [pow_add, ← mul_assoc, he, map_mul, map_pow, aeval_X]

lemma good_le {y : Fin D → K} {j : Fin D} {N N' : ℕ} {b : K} (h : Good y j N b) (hN : N ≤ N') :
    Good y j N' b := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hN
  exact good_mono h M

lemma good_add {y : Fin D → K} {j : Fin D} {N : ℕ} {b b' : K} (h : Good y j N b)
    (h' : Good y j N b') : Good y j N (b + b') := by
  obtain ⟨C, hC, he⟩ := h
  obtain ⟨C', hC', he'⟩ := h'
  exact ⟨C + C', (totalDegree_add _ _).trans (max_le hC hC'), by rw [add_mul, he, he', map_add]⟩

lemma good_mul {y : Fin D → K} {j : Fin D} {N N' : ℕ} {b b' : K} (h : Good y j N b)
    (h' : Good y j N' b') : Good y j (N + N') (b * b') := by
  obtain ⟨C, hC, he⟩ := h
  obtain ⟨C', hC', he'⟩ := h'
  refine ⟨C * C', (totalDegree_mul _ _).trans (add_le_add hC hC'), ?_⟩
  rw [map_mul, ← he, ← he', pow_add]; ring

lemma good_algebraMap (y : Fin D → K) (j : Fin D) (r : ℤ) : Good y j 0 (algebraMap ℤ K r) :=
  ⟨MvPolynomial.C r, by rw [totalDegree_C], by rw [pow_zero, mul_one, aeval_C]⟩

lemma aeval_good {ι : Type} {y : Fin D → K} {j : Fin D} {z : ι → K}
    (hz : ∀ i, ∃ N, Good y j N (z i)) (a : MvPolynomial ι ℤ) : ∃ N, Good y j N (aeval z a) := by
  refine MvPolynomial.induction_on (motive := fun a => ∃ N, Good y j N (aeval z a)) a ?_ ?_ ?_
  · intro r; exact ⟨0, by rw [aeval_C]; exact good_algebraMap y j r⟩
  · rintro p p' ⟨N, hN⟩ ⟨N', hN'⟩
    refine ⟨N + N', ?_⟩
    rw [map_add]
    exact good_add (good_mono hN N') (by rw [add_comm]; exact good_mono hN' N)
  · rintro p i ⟨N, hN⟩
    obtain ⟨M, hM⟩ := hz i
    exact ⟨N + M, by rw [map_mul, aeval_X]; exact good_mul hN hM⟩

lemma common_order {y : Fin D → K} {j : Fin D} (c : ℕ → K) (hc : ∀ k, ∃ N, Good y j N (c k))
    (n : ℕ) : ∃ N, ∀ k < n, Good y j N (c k) := by
  induction n with
  | zero => exact ⟨0, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨M, hM⟩ := hc n
    refine ⟨N + M, fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact good_mono (hN k hk) M
    · exact good_le hM (Nat.le_add_left _ _)

end GlobalTheory.DegreeBound

open GlobalTheory.DegreeBound in

theorem GlobalTheory.totalDegree_le_of_integral_at_infinity : ∀ {K : Type} [Field K] {D : ℕ} (y : Fin D → K),
    AlgebraicIndependent ℤ y → ∀ (j : Fin D), y j ≠ 0 → ∀ (T₀ : MvPolynomial (Fin D) ℤ) (q : ℕ)
    {ι : Type} (z : ι → K), (∀ i, ∃ (N : ℕ) (C : MvPolynomial (Fin D) ℤ), C.totalDegree ≤ N ∧
    z i * y j ^ N = aeval y C) → ∀ (f : Polynomial (MvPolynomial ι ℤ)), f.Monic →
    f.eval₂ (aeval z).toRingHom (aeval y T₀ / y j ^ q) = 0 → T₀.totalDegree ≤ q := by
  intro K _ D y hind j hu T₀ q ι z hz f hf heq
  by_contra hlt
  push_neg at hlt
  have hw : y j ^ q ≠ 0 := pow_ne_zero _ hu
  generalize hs : aeval y T₀ / y j ^ q = s at heq
  have ht : aeval y T₀ = s * y j ^ q := by rw [← hs, div_mul_cancel₀ _ hw]
  set c : ℕ → K := fun k => aeval z (f.coeff k) with hc
  have hsum : (∑ k ∈ Finset.range f.natDegree, c k * s ^ k) + s ^ f.natDegree = 0 := by
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hf.coeff_natDegree] at heq
    simpa [c] using heq
  generalize hn : f.natDegree = n at hsum
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0; simp at hsum
  obtain ⟨N, hN⟩ := common_order (y := y) (j := j) c (fun k => aeval_good hz (f.coeff k)) n
  have hC : ∀ k, ∃ C : MvPolynomial (Fin D) ℤ, k < n →
      C.totalDegree ≤ N ∧ c k * y j ^ N = aeval y C := by
    intro k
    by_cases hk : k < n
    · obtain ⟨C, h1, h2⟩ := hN k hk; exact ⟨C, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose Cf hCf using hC
  have hT0 : T₀ ≠ 0 := by rintro rfl; simp at hlt
  set A : MvPolynomial (Fin D) ℤ := X j ^ (N * n) * T₀ ^ n with hA
  set B : MvPolynomial (Fin D) ℤ :=
    ∑ k ∈ Finset.range n, Cf k * T₀ ^ k * X j ^ (q * (n - k) + N * (n - 1)) with hB
  have hP : aeval y (B + A) = aeval y (0 : MvPolynomial (Fin D) ℤ) := by
    rw [map_zero]
    have : aeval y (B + A) =
        y j ^ (q * n + N * n) * ((∑ k ∈ Finset.range n, c k * s ^ k) + s ^ n) := by
      rw [mul_add, Finset.mul_sum, map_add, map_sum]
      congr 1
      · refine Finset.sum_congr rfl fun k hk => ?_
        have hk' := Finset.mem_range.mp hk
        obtain ⟨m, hm⟩ : ∃ m, n = k + m + 1 := ⟨n - k - 1, by omega⟩
        have h1 : n - k = m + 1 := by omega
        have h2 : n - 1 = k + m := by omega
        rw [map_mul, map_mul, map_pow, map_pow, aeval_X, ht, ← (hCf k hk').2, h1, h2, hm]
        ring
      · rw [hA, map_mul, map_pow, map_pow, aeval_X, ht]
        ring
    rw [this, hsum, mul_zero]
  have hBA : B + A = 0 := algebraicIndependent_iff_injective_aeval.mp hind hP
  have hpow : ∀ m, (T₀ ^ m).totalDegree = m * T₀.totalDegree := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, totalDegree_mul_of_isDomain (pow_ne_zero _ hT0) hT0, ih]; ring
  have hAdeg : A.totalDegree = N * n + n * T₀.totalDegree := by
    rw [hA, totalDegree_mul_of_isDomain (pow_ne_zero _ (X_ne_zero _)) (pow_ne_zero _ hT0),
      totalDegree_X_pow, hpow]
  have hpos : 0 < N * n + n * T₀.totalDegree := by
    have := Nat.mul_pos hnpos (show 0 < T₀.totalDegree by omega); omega
  have hBdeg : B.totalDegree < N * n + n * T₀.totalDegree := by
    refine lt_of_le_of_lt (totalDegree_finset_sum _ _) ?_
    rw [Finset.sup_lt_iff (by simpa using hpos)]
    intro k hk
    have hk' := Finset.mem_range.mp hk
    obtain ⟨m, hm⟩ : ∃ m, n = k + m + 1 := ⟨n - k - 1, by omega⟩
    have h1 : n - k = m + 1 := by omega
    have h2 : n - 1 = k + m := by omega
    calc (Cf k * T₀ ^ k * X j ^ (q * (n - k) + N * (n - 1))).totalDegree
        ≤ N + k * T₀.totalDegree + (q * (n - k) + N * (n - 1)) := by
          refine (totalDegree_mul _ _).trans ?_
          rw [totalDegree_X_pow]
          have := (totalDegree_mul (Cf k) (T₀ ^ k)).trans
            (add_le_add (hCf k hk').1 (totalDegree_pow T₀ k))
          linarith
      _ < N * n + n * T₀.totalDegree := by
          rw [h1, h2, hm]
          have h3 : q * (m + 1) < T₀.totalDegree * (m + 1) :=
            Nat.mul_lt_mul_of_pos_right hlt (Nat.succ_pos m)
          nlinarith
  have hAB : A = -B := eq_neg_of_add_eq_zero_right hBA
  have := congrArg MvPolynomial.totalDegree hAB
  rw [totalDegree_neg, hAdeg] at this
  omega
