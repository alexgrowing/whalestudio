import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Integral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeMulBernoulliMem

open Finset GlobalTheory.KummerEisensteinGalois GlobalTheory.EisCong

namespace GlobalTheory.EisCongGen

variable {K : Type} [Field K] [CharZero K]
variable {p : ℕ} [Fact p.Prime]

lemma bernoulli_expansion_lvl (hp2 : p ≠ 2) (n m N : ℕ) (hN : 0 < N) (b : ℤ) :
    ∃ y ∈ pInt p K, ((N : K) * (p : K) ^ (n + 1)) ^ (m + 1) *
        (((Polynomial.bernoulli (m + 2)).eval ((b : ℚ) / ((N : ℚ) * (p : ℚ) ^ (n + 1))) / ((m + 2 : ℕ) : ℚ) : ℚ) : K) =
      (b : K) ^ (m + 2) / (((m : K) + 2) * ((N : K) * (p : K) ^ (n + 1))) - (b : K) ^ (m + 1) / 2 + (p : K) ^ n * y := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hN0 : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  have hm : (m : K) + 2 ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
  refine ⟨∑ i ∈ range (m + 1), ((p : K) * ((bernoulli (i + 2) : ℚ) : K)) * (b : K) ^ (m - i) *
    ((m + 1).choose (i + 1) : ℕ) * (((p : K) ^ (n + 1)) ^ i / ((i : K) + 2)) * (N : K) ^ (i + 1),
    sum_mem fun i _ => mul_mem (mul_mem (mul_mem (mul_mem (prime_mul_bernoulli_mem i)
      (pow_mem (intCast_mem _ _) _)) (natCast_mem _ _)) (pow_div_add_two_mem hp2 n i))
      (pow_mem (natCast_mem _ _) _), ?_⟩
  rw [Polynomial.bernoulli, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]
  push_cast
  rw [sum_div, mul_sum, sum_range_succ', sum_range_succ', mul_sum]
  have : ∀ i ∈ range (m + 1), ((N : K) * (p : K) ^ (n + 1)) ^ (m + 1) *
      (((bernoulli (i + 1 + 1) : ℚ) : K) * ((m + 2).choose (i + 1 + 1) : ℕ) *
        ((b : K) / ((N : K) * (p : K) ^ (n + 1))) ^ (m + 2 - (i + 1 + 1)) / ((m : K) + 2)) =
      (p : K) ^ n * (((p : K) * ((bernoulli (i + 2) : ℚ) : K)) * (b : K) ^ (m - i) *
        ((m + 1).choose (i + 1) : ℕ) * (((p : K) ^ (n + 1)) ^ i / ((i : K) + 2)) * (N : K) ^ (i + 1)) := by
    intro i hi
    obtain ⟨l, rfl⟩ : ∃ l, m = i + l := ⟨m - i, by have := mem_range.1 hi; omega⟩
    have hi2 : (i : K) + 2 ≠ 0 := by exact_mod_cast (show i + 2 ≠ 0 by omega)
    rw [show i + l + 2 - (i + 1 + 1) = l by omega, show i + l - i = l by omega,
      show i + 1 + 1 = i + 2 by omega, choose_cast, div_pow]
    field_simp
    ring
  rw [sum_congr rfl this]
  generalize (∑ i ∈ range (m + 1), _ : K) = S
  simp [div_pow]
  field_simp
  ring

lemma inv_pow_nat_mem {N : ℕ} (hpN : ¬ p ∣ N) (k : ℕ) : ((N : K)⁻¹) ^ k ∈ pInt p K :=
  pow_mem (inv_nat_mem hpN) k

lemma const_j (hp2 : p ≠ 2) {N : ℕ} (hN : 0 < N) (hpN : ¬ p ∣ N) (n m : ℕ) (ζ : K) (a a₂ x s : ℤ)
    (hb : a % ((N * p ^ (n + 1) : ℕ) : ℤ) = N * x + s * (p : ℤ) ^ (n + 1)) :
    ∃ y ∈ pInt p K, (p : K) ^ ((n + 1) * (m + 1)) * const0 (m + 2) (N * p ^ (n + 1)) ζ a a₂ =
      -((x : K) ^ (m + 2) / (((m : K) + 2) * (p : K) ^ (n + 1)) + s * (x : K) ^ (m + 1) / N
        - (x : K) ^ (m + 1) / 2) + (p : K) ^ n * y := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hN0 : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  have hm : (m : K) + 2 ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
  set b : ℤ := a % ((N * p ^ (n + 1) : ℕ) : ℤ) with hbdef
  have hbK : (b : K) = (N : K) * x + s * (p : K) ^ (n + 1) := by rw [hb]; push_cast; ring
  have f : frc (N * p ^ (n + 1)) a = (b : ℚ) / ((N : ℚ) * (p : ℚ) ^ (n + 1)) := by
    unfold frc; rw [← hbdef]; push_cast; ring
  obtain ⟨y1, hy1, E1⟩ := bernoulli_expansion_lvl (K := K) hp2 n m N hN b
  obtain ⟨y3, hy3, E3⟩ := binom_second (K := K) hp2 n m (N * x) s
  obtain ⟨y4, E4⟩ := binom_first (K := K) ((p : ℤ) ^ (n + 1)) (m + 1) (N * x) s
  push_cast at E3 E4
  rw [← hbK] at E3 E4
  have h2 : (2 : K)⁻¹ ∈ pInt p K := by
    simpa using inv_nat_mem (K := K) (p := p) (m := 2)
      fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  refine ⟨-(((N : K)⁻¹) ^ (m + 1) * (p * y3 * (N : K)⁻¹ - p * y4 * 2⁻¹ + y1)),
    neg_mem (mul_mem (inv_pow_nat_mem hpN _) (add_mem (sub_mem (mul_mem (mul_mem (natCast_mem _ _) hy3)
      (inv_nat_mem hpN)) (mul_mem (mul_mem (natCast_mem _ _) (intCast_mem _ _)) h2)) hy1)), ?_⟩
  simp only [const0, if_neg (show m + 2 ≠ 1 by omega), f]
  have hZ := (eq_div_iff (pow_ne_zero (m + 1) (mul_ne_zero hN0 (pow_ne_zero (n + 1) hp0)))).2 ((mul_comm _ _).trans E1)
  rw [hZ, E3, E4]
  rw [pow_mul]
  have hQ : (p : K) ^ n ≠ 0 := pow_ne_zero _ hp0
  simp only [pow_succ (p : K) n]
  generalize (p : K) ^ n = Q at hQ ⊢
  rw [inv_pow]
  field_simp
  ring

omit [Fact p.Prime] in
lemma exists_intMod_levelPrimePow_eq_add_mul {N : ℕ} (n : ℕ) (a x : ℤ) (h : a ≡ N * x [ZMOD (p : ℤ) ^ (n + 1)]) :
    ∃ s : ℤ, a % ((N * p ^ (n + 1) : ℕ) : ℤ) = N * x + s * (p : ℤ) ^ (n + 1) := by
  have h1 : a % ((N * p ^ (n + 1) : ℕ) : ℤ) ≡ a [ZMOD (N : ℤ) * (p : ℤ) ^ (n + 1)] := by
    have := Int.mod_modEq a ((N * p ^ (n + 1) : ℕ) : ℤ)
    push_cast at this ⊢
    exact this
  have h2 := (h1.of_mul_left _).trans h
  obtain ⟨s, hs⟩ := h2.symm.dvd
  exact ⟨s, by linear_combination hs⟩

lemma not_dvd_of_congr {N : ℕ} (hpN : ¬ p ∣ N) (n : ℕ) {a α : ℤ} (h0 : 0 < α) (h1 : α < (p : ℤ) ^ (n + 1))
    (ha : a ≡ N * α [ZMOD (p : ℤ) ^ (n + 1)]) : ¬ ((p : ℤ) ^ (n + 1) ∣ a) := by
  have hp : p.Prime := Fact.out
  intro hd1
  have hd2 : (p : ℤ) ^ (n + 1) ∣ N * α := (Int.ModEq.dvd ha).elim fun t ht => by
    refine ⟨t + a / (p : ℤ) ^ (n + 1), ?_⟩
    have := Int.ediv_mul_cancel hd1
    linear_combination ht - this
  have hcop : IsCoprime ((p : ℤ) ^ (n + 1)) (N : ℤ) :=
    IsCoprime.pow_left ((Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd.2
      (fun h => hpN (Int.natCast_dvd_natCast.1 h)))
  have := hcop.dvd_of_dvd_mul_left hd2
  exact absurd (Int.le_of_dvd h0 this) (not_le.2 h1)

lemma not_dvd_lvl {N : ℕ} (n : ℕ) {a : ℤ} (h : ¬ ((p : ℤ) ^ (n + 1) ∣ a)) :
    ¬ (((N * p ^ (n + 1) : ℕ) : ℤ) ∣ a) := fun hd => h (dvd_trans (by push_cast; exact dvd_mul_left _ _) hd)

lemma not_dvd_mul {n : ℕ} {c a : ℤ} (hc : ¬ (p : ℤ) ∣ c) (h : ¬ ((p : ℤ) ^ (n + 1) ∣ a)) :
    ¬ ((p : ℤ) ^ (n + 1) ∣ c * a) := fun hd => h <|
  IsCoprime.dvd_of_dvd_mul_left (IsCoprime.pow_left
    ((Nat.prime_iff_prime_int.1 (Fact.out : p.Prime)).irreducible.coprime_iff_not_dvd.2 hc)) hd

lemma const_congr_gen (hp2 : p ≠ 2) {N : ℕ} (hN : 0 < N) (hpN : ¬ p ∣ N) (n m : ℕ) (ζ : K) {c : ℤ}
    (hc : ¬ (p : ℤ) ∣ c) {α a₁ : ℤ} (a₂ : ℤ) (h0 : 0 ≤ α) (h1 : α < (p : ℤ) ^ (n + 1))
    (ha : a₁ ≡ N * α [ZMOD (p : ℤ) ^ (n + 1)]) :
    ∃ y ∈ pInt p K, (α : K) ^ (m + 1) * smF c 1 (N * p ^ (n + 1)) ζ a₁ a₂ 0 -
      (p : K) ^ ((n + 1) * (m + 1)) * smF c (m + 2) (N * p ^ (n + 1)) ζ a₁ a₂ 0 = (p : K) ^ n * y := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hN0 : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  have hm : (m : K) + 2 ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
  have hc0 : (c : K) ≠ 0 := by
    have : c ≠ 0 := by rintro rfl; exact hc (dvd_zero _)
    exact_mod_cast this
  have hca : c * a₁ ≡ N * (c * α) [ZMOD (p : ℤ) ^ (n + 1)] := by
    have := ha.mul_left c; rwa [mul_left_comm] at this
  obtain ⟨s₁, hs₁⟩ := exists_intMod_levelPrimePow_eq_add_mul n a₁ α ha
  obtain ⟨s₂, hs₂⟩ := exists_intMod_levelPrimePow_eq_add_mul n (c * a₁) (c * α) hca
  obtain ⟨y1, hy1, E1⟩ := const_j (K := K) hp2 hN hpN n m ζ a₁ a₂ α s₁ hs₁
  obtain ⟨y2, hy2, E2⟩ := const_j (K := K) hp2 hN hpN n m ζ (c * a₁) (c * a₂) (c * α) s₂ hs₂
  have hz : (c : K) ^ ((2 : ℤ) - ((m + 2 : ℕ) : ℤ)) = ((c : K) ^ m)⁻¹ := by
    rw [show (2 : ℤ) - ((m + 2 : ℕ) : ℤ) = -(m : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  have hS : (p : K) ^ ((n + 1) * (m + 1)) * smF c (m + 2) (N * p ^ (n + 1)) ζ a₁ a₂ 0 =
      (c : K) ^ 2 * ((p : K) ^ ((n + 1) * (m + 1)) * const0 (m + 2) (N * p ^ (n + 1)) ζ a₁ a₂) -
      ((c : K) ^ m)⁻¹ * ((p : K) ^ ((n + 1) * (m + 1)) * const0 (m + 2) (N * p ^ (n + 1)) ζ (c * a₁) (c * a₂)) := by
    simp only [smF, eisF, ↓reduceIte, hz]; ring
  have hci : ((c : K) ^ m)⁻¹ ∈ pInt p K := by rw [← inv_pow]; exact pow_mem (inv_int_mem hc) m
  refine ⟨-((c : K) ^ 2 * y1 - ((c : K) ^ m)⁻¹ * y2),
    neg_mem (sub_mem (mul_mem (pow_mem (intCast_mem _ _) _) hy1) (mul_mem hci hy2)), ?_⟩
  rw [hS, E1, E2]
  rcases h0.eq_or_lt with h | h
  · rw [← h]; simp; ring
  have d0 := not_dvd_of_congr hpN n h h1 ha
  have d1 := not_dvd_lvl (N := N) n d0
  have d2 := not_dvd_lvl (N := N) n (not_dvd_mul hc d0)
  have f1 : frc (N * p ^ (n + 1)) a₁ = ((N * α + s₁ * (p : ℤ) ^ (n + 1) : ℤ) : ℚ) / ((N : ℚ) * (p : ℚ) ^ (n + 1)) := by
    unfold frc; rw [hs₁]; push_cast; ring
  have f2 : frc (N * p ^ (n + 1)) (c * a₁) = ((N * (c * α) + s₂ * (p : ℤ) ^ (n + 1) : ℤ) : ℚ) /
      ((N : ℚ) * (p : ℚ) ^ (n + 1)) := by
    unfold frc; rw [hs₂]; push_cast; ring
  simp only [smF, eisF, ↓reduceIte, const0, if_neg d1, if_neg d2, f1, f2]
  push_cast
  have hQ : (p : K) ^ n ≠ 0 := pow_ne_zero _ hp0
  simp only [pow_succ (p : K) n]
  generalize (p : K) ^ n = Q at hQ ⊢
  field_simp
  ring

lemma term_congr_gen (hp0 : (p : K) ≠ 0) {N : ℕ} (hN : 0 < N) (hpN : ¬ p ∣ N) (n k : ℕ) {A a₁ a : ℤ}
    (h : A ≡ a₁ [ZMOD ((N * p ^ n : ℕ) : ℤ)]) (ha : a₁ ≡ N * a [ZMOD (p : ℤ) ^ n]) :
    ∃ y ∈ pInt p K, (p : K) ^ (n * k) * ((A : K) / ((N * p ^ n : ℕ) : K)) ^ k = (a : K) ^ k + (p : K) ^ n * y := by
  have h' : A ≡ N * a [ZMOD (p : ℤ) ^ n] := by
    have : A ≡ a₁ [ZMOD (N : ℤ) * (p : ℤ) ^ n] := by push_cast at h; exact h
    exact (this.of_mul_left _).trans ha
  obtain ⟨t, ht⟩ := h'.symm.dvd
  obtain ⟨y, hy⟩ := binom_first (K := K) ((p : ℤ) ^ n) k (N * a) t
  have hN' : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨(y : K) * ((N : K) ^ k)⁻¹, mul_mem (intCast_mem _ _) (by rw [← inv_pow]; exact pow_mem (inv_nat_mem hpN) k), ?_⟩
  have hA : (A : K) = N * a + t * (p : K) ^ n := by
    have := congrArg (Int.cast : ℤ → K) ht
    push_cast at this
    linear_combination this
  push_cast at hy ⊢
  rw [hA, div_pow, hy, pow_mul]
  have hQ : (p : K) ^ n ≠ 0 := pow_ne_zero _ hp0
  generalize (p : K) ^ n = Q at hQ ⊢
  field_simp
  ring

lemma coefPos_congr_gen {N : ℕ} (hN : 0 < N) (hpN : ¬ p ∣ N) (n k : ℕ) {ζ : K}
    (hζ : IsPrimitiveRoot ζ (N * p ^ n)) (a a₁ a₂ : ℤ) (ha : a₁ ≡ N * a [ZMOD (p : ℤ) ^ n]) (r : ℕ) :
    ∃ y ∈ pInt p K, (a : K) ^ k * coefPos 1 (N * p ^ n) ζ a₁ a₂ r -
      (p : K) ^ (n * k) * coefPos (k + 1) (N * p ^ n) ζ a₁ a₂ r = (p : K) ^ n * y := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hM : 0 < N * p ^ n := Nat.mul_pos hN (pow_pos hp.pos n)
  have key : ∀ (A e : ℤ), ∃ y ∈ pInt p K,
      (a : K) ^ k * (if A ≡ a₁ [ZMOD ((N * p ^ n : ℕ) : ℤ)] then ζ ^ e else 0) -
        (p : K) ^ (n * k) * (if A ≡ a₁ [ZMOD ((N * p ^ n : ℕ) : ℤ)] then
          ((A : K) / ((N * p ^ n : ℕ) : K)) ^ k * ζ ^ e else 0) = (p : K) ^ n * y := by
    intro A e
    split_ifs with h
    · obtain ⟨y, hy, hE⟩ := term_congr_gen hp0 hN hpN n k h ha
      refine ⟨-(y * ζ ^ e), neg_mem (mul_mem hy (root_zpow_mem hM hζ e)), ?_⟩
      rw [← mul_assoc, hE]; ring
    · exact ⟨0, zero_mem _, by simp⟩
  choose y hy hE using key
  refine ⟨∑ d ∈ r.divisors, (y ((r / d : ℕ) : ℤ) (a₂ * d) - y (-((r / d : ℕ) : ℤ)) (-(a₂ * d))),
    sum_mem fun d _ => sub_mem (hy _ _) (hy _ _), ?_⟩
  unfold coefPos
  rw [mul_sum, mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun d _ => ?_
  rw [mul_sub ((p : K) ^ n), ← hE, ← hE]
  simp only [Nat.sub_self, pow_zero, one_mul, Nat.add_sub_cancel, Int.cast_neg, Int.cast_natCast, neg_div]
  ring

theorem smF_congr_gen : ∀ (p : ℕ) [Fact p.Prime] (N n j : ℕ) (K : Type) [Field K] [CharZero K] (ζ : K), p ≠ 2 → IsPrimitiveRoot ζ (N * p ^ n) → 0 < N → ¬ p ∣ N → 2 ≤ j → j ^ 2 * p ≤ p ^ n → ∀ (c : ℤ), ¬ (p : ℤ) ∣ c → ∀ (α a₁ a₂ : ℤ), 0 ≤ α → α < (p : ℤ) ^ n → a₁ ≡ N * α [ZMOD (p : ℤ) ^ n] → ∀ r : ℕ, ∃ D : ℕ, ¬ p ∣ D ∧ IsIntegral ℤ ((D : K) * ((α : K) ^ (j - 1) * smF c 1 (N * p ^ n) ζ a₁ a₂ r - (p : K) ^ (n * (j - 1)) * smF c j (N * p ^ n) ζ a₁ a₂ r) / (p : K) ^ (n - 1)) := by
  intro p _ N n j K _ _ ζ hp2 hζ hN hpN hj hn c hc α a₁ a₂ h0 h1 ha r
  have hp : p.Prime := Fact.out
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := by
    rcases n with _ | n
    · exfalso; have := hp.two_le; rw [pow_zero] at hn; nlinarith
    · exact ⟨n, rfl⟩
  rw [show m + 2 - 1 = m + 1 from rfl, Nat.add_sub_cancel]
  suffices H : ∃ y ∈ pInt p K, (α : K) ^ (m + 1) * smF c 1 (N * p ^ (n + 1)) ζ a₁ a₂ r -
      (p : K) ^ ((n + 1) * (m + 1)) * smF c (m + 2) (N * p ^ (n + 1)) ζ a₁ a₂ r = (p : K) ^ n * y by
    obtain ⟨y, ⟨D, hD, hy⟩, E⟩ := H
    refine ⟨D, hD, ?_⟩
    rw [E, mul_left_comm, mul_div_cancel_left₀ _ (pow_ne_zero _ hp0)]
    exact hy
  rcases eq_or_ne r 0 with rfl | hr
  · exact const_congr_gen hp2 hN hpN n m ζ hc a₂ h0 h1 ha
  have hc0 : (c : K) ≠ 0 := by
    have : c ≠ 0 := by rintro rfl; exact hc (dvd_zero _)
    exact_mod_cast this
  have hca : c * a₁ ≡ N * (c * α) [ZMOD (p : ℤ) ^ (n + 1)] := by
    have := ha.mul_left c; rwa [mul_left_comm] at this
  obtain ⟨y1, hy1, E1⟩ := coefPos_congr_gen hN hpN (n + 1) (m + 1) hζ α a₁ a₂ ha r
  obtain ⟨y2, hy2, E2⟩ := coefPos_congr_gen hN hpN (n + 1) (m + 1) hζ (c * α) (c * a₁) (c * a₂) hca r
  have hz : (c : K) ^ ((2 : ℤ) - ((m + 2 : ℕ) : ℤ)) = ((c : K)⁻¹) ^ m := by
    rw [show (2 : ℤ) - ((m + 2 : ℕ) : ℤ) = -(m : ℤ) by push_cast; ring, zpow_neg, zpow_natCast, inv_pow]
  have hz1 : (c : K) ^ ((2 : ℤ) - ((1 : ℕ) : ℤ)) = c := by norm_num
  refine ⟨p * ((c : K) ^ 2 * y1 - ((c : K)⁻¹) ^ m * y2), mul_mem (natCast_mem _ _)
    (sub_mem (mul_mem (pow_mem (intCast_mem _ _) _) hy1) (mul_mem (pow_mem (inv_int_mem hc) m) hy2)), ?_⟩
  simp only [smF, eisF, if_neg hr, hz, hz1]
  have hcm : ((c : K)⁻¹) ^ m * ((c * α : ℤ) : K) ^ (m + 1) = c * (α : K) ^ (m + 1) := by
    push_cast; rw [inv_pow]; field_simp; ring
  linear_combination (c : K) ^ 2 * E1 - ((c : K)⁻¹) ^ m * E2 +
    coefPos 1 (N * p ^ (n + 1)) ζ (c * a₁) (c * a₂) r * hcm

end GlobalTheory.EisCongGen
