import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotZeroChi
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefficientCongruenceOfTwistedValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SeriesEqZeroOfValsTendstoZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CoefSup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralIffNormLeOne
open GlobalTheory.KZ GlobalTheory.Ord2 UpperTheory.V.HV Formalism.ConjugateSelfDual PowerSeries

namespace GlobalTheory.KZ.AutoPin

theorem norm_sub_le_max' {l : ℕ} [Fact l.Prime] (x y : Qbar l) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  have := IsUltrametricDist.norm_add_le_max x (-y)
  rwa [norm_neg, ← sub_eq_add_neg] at this

theorem root_bound (l : ℕ) [Fact l.Prime] (m : ℕ) (z : Qbar l) (hz : IsPrimitiveRoot z (l ^ m)) :
    ‖z - 1‖ ≤ 1 ∧ ‖(z - 1) ^ (l ^ m)‖ ≤ ‖((l : ℕ) : Qbar l)‖ := by
  have hp : l.Prime := Fact.out
  have hz1 : ‖z‖ = 1 := by
    have h := congrArg norm hz.pow_eq_one
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_pos hp.pos m).ne').1 h
  have h1 : ‖z - 1‖ ≤ 1 := le_trans (norm_sub_le_max' z 1) (by simp [hz1])
  refine ⟨h1, ?_⟩
  let x : integralClosure ℤ_[l] (Qbar l) := ⟨z - 1, (isIntegral_iff_norm_le_one _).2 h1⟩
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp x 1 m
  have hr' := congrArg Subtype.val hr
  have hrn : ‖(r : Qbar l)‖ ≤ 1 := (isIntegral_iff_norm_le_one _).1 r.2
  simp only [x] at hr'
  push_cast at hr'
  rw [sub_add_cancel, hz.pow_eq_one] at hr'
  have : (z - 1) ^ l ^ m = -((l : Qbar l) * ((z - 1) * r)) := by linear_combination -hr'
  rw [this, norm_neg, norm_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (mul_le_one₀ h1 (norm_nonneg _) hrn)

theorem norm_eval_le {l : ℕ} [Fact l.Prime] (p : Polynomial (Qbar l)) (N : ℕ) (x : Qbar l) (hx : ‖x‖ ≤ 1)
    (hp : ∀ n, ‖p.coeff n‖ ≤ 1) (h0 : ∀ n < N, p.coeff n = 0) : ‖p.eval x‖ ≤ ‖x‖ ^ N := by
  rw [Polynomial.eval_eq_sum_range]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun n _ => ?_
  by_cases h : n < N
  · rw [h0 n h, zero_mul, norm_zero]; positivity
  · rw [norm_mul, norm_pow]
    exact le_trans (mul_le_of_le_one_left (by positivity) (hp n))
      (pow_le_pow_of_le_one (norm_nonneg _) hx (not_lt.1 h))

theorem tval_eq_eval {l : ℕ} [Fact l.Prime] (P : PowerSeries (Qbar l)) (N : ℕ) (z : Qbar l) :
    tval P N z = (PowerSeries.trunc N P).eval (z - 1) := by
  rw [Polynomial.eval, PowerSeries.eval₂_trunc_eq_sum_range]; rfl

theorem norm_coeff_trunc_le {l : ℕ} [Fact l.Prime] (P : PowerSeries (Qbar l)) (N : ℕ) (hP : ∀ n, ‖P.coeff n‖ ≤ 1) (n : ℕ) :
    ‖(PowerSeries.trunc N P).coeff n‖ ≤ 1 := by
  rw [PowerSeries.coeff_trunc]
  split_ifs
  · exact hP n
  · simp

theorem tval_mul_le (l : ℕ) [Fact l.Prime] (P Q : PowerSeries (Qbar l)) (N : ℕ) (z : Qbar l) (hP : ∀ n, ‖P.coeff n‖ ≤ 1)
    (hQ : ∀ n, ‖Q.coeff n‖ ≤ 1) (hz : ‖z - 1‖ ≤ 1) :
    ‖tval (P * Q) N z - tval P N z * tval Q N z‖ ≤ ‖(z - 1) ^ N‖ := by
  rw [tval_eq_eval, tval_eq_eval, tval_eq_eval, ← Polynomial.eval_mul, ← Polynomial.eval_sub, norm_pow]
  refine norm_eval_le _ N _ hz (fun n => ?_) (fun n hn => ?_)
  · rw [Polynomial.coeff_sub]
    refine le_trans (norm_sub_le_max' _ _) (max_le (norm_coeff_trunc_le _ _ (fun n => ?_) n) ?_)
    · rw [PowerSeries.coeff_mul]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p _ => ?_
      rw [norm_mul]; exact mul_le_one₀ (hP _) (norm_nonneg _) (hQ _)
    · rw [Polynomial.coeff_mul]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p _ => ?_
      rw [norm_mul]
      exact mul_le_one₀ (norm_coeff_trunc_le _ _ hP _) (norm_nonneg _) (norm_coeff_trunc_le _ _ hQ _)
  · rw [Polynomial.coeff_sub, PowerSeries.coeff_trunc, if_pos hn, PowerSeries.coeff_mul, Polynomial.coeff_mul, sub_eq_zero]
    refine Finset.sum_congr rfl fun p hp => ?_
    have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_pos (by omega), if_pos (by omega)]

theorem exists_factor (l : ℕ) [Fact l.Prime] : ∃ R : Polynomial (Qbar l),
    ((Polynomial.X + 1) ^ l - 1 : Polynomial (Qbar l)) = Polynomial.X * R ∧ R.coeff 0 = (l : Qbar l) := by
  obtain ⟨R, hR⟩ : (Polynomial.X : Polynomial (Qbar l)) ∣ (Polynomial.X + 1) ^ l - 1 := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]; simp
  refine ⟨R, hR, ?_⟩
  have h := congrArg (fun p : Polynomial (Qbar l) => p.coeff (0 + 1)) hR
  simp only [Polynomial.coeff_X_mul, Polynomial.coeff_sub, Polynomial.coeff_X_add_one_pow] at h
  rw [← h]; simp [Polynomial.coeff_one]

theorem polyPow_coeff_lt {l : ℕ} [Fact l.Prime] {k n : ℕ} (h : n < k) :
    ((((Polynomial.X + 1) ^ l - 1 : Polynomial (Qbar l))) ^ k).coeff n = 0 := by
  obtain ⟨R, hR, -⟩ := exists_factor l
  rw [hR, mul_pow, Polynomial.coeff_X_pow_mul', if_neg (by omega)]

theorem polyPow_coeff_self {l : ℕ} [Fact l.Prime] (k : ℕ) :
    ((((Polynomial.X + 1) ^ l - 1 : Polynomial (Qbar l))) ^ k).coeff k = (l : Qbar l) ^ k := by
  obtain ⟨R, hR, h0⟩ := exists_factor l
  rw [hR, mul_pow, Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.eval_pow, ← Polynomial.coeff_zero_eq_eval_zero, h0]

theorem norm_term_le {l : ℕ} [Fact l.Prime] (B : PowerSeries (Qbar l)) (hB : ∀ n, ‖B.coeff n‖ ≤ 1) (k n : ℕ) :
    ‖B.coeff k * ((((Polynomial.X + 1) ^ l - 1 : Polynomial (Qbar l))) ^ k).coeff n‖ ≤ 1 := by
  obtain ⟨t, ht⟩ := polyPow_coeff_int (l := l) k n
  rw [ht, norm_mul]
  exact mul_le_one₀ (hB k) (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ t)

theorem tval_compPow_le (l : ℕ) [Fact l.Prime] (B : PowerSeries (Qbar l)) (N M : ℕ) (z : Qbar l)
    (hB : ∀ n, ‖B.coeff n‖ ≤ 1) (hz : ‖z - 1‖ ≤ 1) :
    ‖tval (compPow l B) N z - tval B M (z ^ l)‖ ≤ max ‖(z - 1) ^ N‖ ‖(z - 1) ^ M‖ := by
  have h2 : tval B M (z ^ l) = (∑ k ∈ Finset.range M, Polynomial.C (B.coeff k) *
      (((Polynomial.X + 1) ^ l - 1 : Polynomial (Qbar l))) ^ k).eval (z - 1) := by
    simp [tval, Polynomial.eval_finsetSum]
  rw [h2, tval_eq_eval, ← Polynomial.eval_sub]
  refine le_trans (norm_eval_le _ (min N M) _ hz (fun n => ?_) (fun n hn => ?_)) ?_
  · rw [Polynomial.coeff_sub]
    refine le_trans (norm_sub_le_max' _ _) (max_le (norm_coeff_trunc_le _ _ (fun n => ?_) n) ?_)
    · rw [compPow, PowerSeries.coeff_mk]
      exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => norm_term_le B hB k n
    · rw [Polynomial.finsetSum_coeff]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
      rw [Polynomial.coeff_C_mul]; exact norm_term_le B hB k n
  · have h1 : n < N := lt_of_lt_of_le hn (min_le_left _ _)
    have h3 : n < M := lt_of_lt_of_le hn (min_le_right _ _)
    rw [Polynomial.coeff_sub, PowerSeries.coeff_trunc, if_pos h1, compPow, PowerSeries.coeff_mk,
      Polynomial.finsetSum_coeff, sub_eq_zero]
    simp only [Polynomial.coeff_C_mul]
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun k _ hk => ?_
    rw [polyPow_coeff_lt (by simpa using hk), mul_zero]
  · rw [norm_pow, norm_pow]
    rcases min_choice N M with h | h <;> rw [h]
    · exact le_max_left _ _
    · exact le_max_right _ _

theorem compPow_low {l : ℕ} [Fact l.Prime] (B : PowerSeries (Qbar l)) (j : ℕ) (hB : ∀ i < j, B.coeff i = 0) :
    (∀ n < j, (compPow l B).coeff n = 0) ∧ (compPow l B).coeff j = (l : Qbar l) ^ j * B.coeff j := by
  refine ⟨fun n hn => ?_, ?_⟩
  · rw [compPow, PowerSeries.coeff_mk]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [hB k (by have := Finset.mem_range.1 hk; omega), zero_mul]
  · rw [compPow, PowerSeries.coeff_mk, Finset.sum_range_succ, polyPow_coeff_self, Finset.sum_eq_zero, zero_add, mul_comm]
    intro k hk
    rw [hB k (Finset.mem_range.1 hk), zero_mul]

theorem coeff_mul_low {l : ℕ} [Fact l.Prime] (P Q : PowerSeries (Qbar l)) (i j : ℕ) (hP : ∀ n < i, P.coeff n = 0)
    (hQ : ∀ n < j, Q.coeff n = 0) : (P * Q).coeff (i + j) = P.coeff i * Q.coeff j := by
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_single (i, j) (fun p hp hne => ?_) (fun h => (h (by simp)).elim)
  have h := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  by_cases h1 : p.1 < i
  · rw [hP _ h1, zero_mul]
  · have h2 : p.2 < j := by
      by_contra h2
      exact hne (Prod.ext (by simp only; omega) (by simp only; omega))
    rw [hQ _ h2, mul_zero]

theorem exists_low {l : ℕ} [Fact l.Prime] (A : PowerSeries (Qbar l)) (hA : A ≠ 0) :
    ∃ i, A.coeff i ≠ 0 ∧ ∀ n < i, A.coeff n = 0 := by
  classical
  have h : ∃ i, A.coeff i ≠ 0 := by
    by_contra h
    push Not at h
    exact hA (PowerSeries.ext fun n => by simpa using h n)
  exact ⟨Nat.find h, Nat.find_spec h, fun n hn => by simpa using Nat.find_min h hn⟩

theorem eq_one_of_compPow (l : ℕ) [Fact l.Prime] (A B : PowerSeries (Qbar l)) (u : Qbar l) (hA : A ≠ 0) (hB : B ≠ 0)
    (hu : ‖u‖ = 1) (h : A * compPow l B = u • (compPow l A * B)) : u = 1 := by
  obtain ⟨i, hi, hi0⟩ := exists_low A hA
  obtain ⟨j, hj, hj0⟩ := exists_low B hB
  obtain ⟨a1, a2⟩ := compPow_low A i hi0
  obtain ⟨b1, b2⟩ := compPow_low B j hj0
  have h1 := congrArg (PowerSeries.coeff (i + j)) h
  rw [PowerSeries.coeff_smul, smul_eq_mul, coeff_mul_low _ _ i j hi0 b1, coeff_mul_low _ _ i j a1 hj0, a2, b2] at h1
  have h2 : (l : Qbar l) ^ j = u * (l : Qbar l) ^ i :=
    mul_right_cancel₀ (mul_ne_zero hi hj) (by linear_combination h1)
  have h3 := congrArg norm h2
  rw [norm_mul, hu, one_mul, norm_pow, norm_pow] at h3
  have hij : j = i := pow_right_injective₀ norm_l_pos norm_l_lt_one.ne h3
  rw [hij] at h2
  have hl : (l : Qbar l) ^ i ≠ 0 := pow_ne_zero _ (norm_pos_iff.1 norm_l_pos)
  exact (mul_right_cancel₀ hl (by rw [one_mul]; exact h2)).symm

end GlobalTheory.KZ.AutoPin

namespace GlobalTheory.KZ.AutoPin

variable {l : ℕ} [Fact l.Prime]

theorem cg_sub' {k : ℕ} {a b a' b' : Qbar l} (h : Cg k a b) (h' : Cg k a' b') : Cg k (a - a') (b - b') := by
  unfold Cg at *
  calc ‖a - a' - (b - b')‖ = ‖(a - b) - (a' - b')‖ := by ring_nf
    _ ≤ max ‖a - b‖ ‖a' - b'‖ := norm_sub_le_max' _ _
    _ ≤ _ := max_le h h'

theorem cg_of_le {k : ℕ} {a b x : Qbar l} (h : ‖a - b‖ ≤ ‖x‖) (hx : ‖x‖ ≤ ‖((l : ℕ) : Qbar l) ^ k‖) : Cg k a b :=
  le_trans h hx

theorem cg_zero_of_cg {k : ℕ} {a b : Qbar l} (h : Cg k a b) : Cg k (a - b) 0 := by
  unfold Cg at *; rwa [sub_zero]

theorem coeff_mul_mem (O : Subalgebra ℤ_[l] (PadicAlgCl l)) (P Q : PowerSeries (Qbar l)) (hP : ∀ n, P.coeff n ∈ O)
    (hQ : ∀ n, Q.coeff n ∈ O) (n : ℕ) : (P * Q).coeff n ∈ O := by
  rw [PowerSeries.coeff_mul]
  exact sum_mem fun p _ => mul_mem (hP _) (hQ _)

theorem small_pow {m : ℕ} {z : Qbar l} (hz : IsPrimitiveRoot z (l ^ m)) {N K : ℕ} (hN : K * l ^ m ≤ N) :
    ‖(z - 1) ^ N‖ ≤ ‖((l : ℕ) : Qbar l) ^ K‖ := by
  obtain ⟨h1, h2⟩ := root_bound l m z hz
  rw [norm_pow] at h2 ⊢
  rw [norm_pow]
  calc ‖z - 1‖ ^ N ≤ ‖z - 1‖ ^ (K * l ^ m) := pow_le_pow_of_le_one (norm_nonneg _) h1 hN
    _ = (‖z - 1‖ ^ l ^ m) ^ K := by rw [← pow_mul, mul_comm]
    _ ≤ ‖((l : ℕ) : Qbar l)‖ ^ K := pow_le_pow_left₀ (by positivity) h2 K

theorem nat_bound (m : ℕ) (hm : 1 ≤ m) : m * l ^ (m + 1) ≤ l ^ (3 * m) := by
  have hl : 1 ≤ l := (Fact.out : l.Prime).one_lt.le
  have h1 : m ≤ l ^ m := (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le
  calc m * l ^ (m + 1) ≤ l ^ m * l ^ (m + 1) := Nat.mul_le_mul_right _ h1
    _ = l ^ (2 * m + 1) := by rw [← pow_add]; ring_nf
    _ ≤ l ^ (3 * m) := Nat.pow_le_pow_right (by omega) (by omega)

end GlobalTheory.KZ.AutoPin

open GlobalTheory.KZ.AutoPin in

theorem GlobalTheory.KZ.autoPin_congr : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (A B : PowerSeries (Qbar l)) (u : Qbar l) (w : ℕ → Qbar l) (c₀ m₀ : ℕ), (∀ n, A.coeff n ∈ c.O) → (∀ n, B.coeff n ∈ c.O) → B ≠ 0 → ‖u‖ = 1 → (∀ m, ‖w m‖ = 1 ∧ Cg m (w (m + 1)) (w m)) → (∀ m, m₀ ≤ m → ∀ z : Qbar l, IsPrimitiveRoot z (l ^ m) → Cg (m / 2 - c₀) (tval A (l ^ (3 * m)) z) (w m * u ^ m * tval B (l ^ (3 * m)) z)) → u = 1 ∧ ∀ k : ℕ, ∃ m₁ : ℕ, ∀ m, m₁ ≤ m → ∀ n, Cg k (A.coeff n) (w m * B.coeff n) := by
  intro l _ c A B u w c₀ m₀ hA hB hB0 hu hw hval
  have hAn : ∀ n, ‖A.coeff n‖ ≤ 1 := fun n => norm_le_one_of_mem c (hA n)
  have hBn : ∀ n, ‖B.coeff n‖ ≤ 1 := fun n => norm_le_one_of_mem c (hB n)
  have hwd : ∀ m d, Cg m (w (m + d)) (w m) := by
    intro m d
    induction d with
    | zero => simp only [add_zero, Cg, sub_self, norm_zero]; exact norm_nonneg _
    | succ d ih =>
      rw [show m + (d + 1) = m + d + 1 by omega]
      exact cg_trans (cg_mono (hw (m + d)).2 (by omega)) ih
  have hz1 : ∀ m (z : Qbar l), IsPrimitiveRoot z (l ^ m) → ‖z - 1‖ ≤ 1 := fun m z hz => (root_bound l m z hz).1

  have hA0 : A ≠ 0 := by
    rintro rfl
    apply hB0
    refine GlobalTheory.KZ.series_eq_zero_of_vals_tendsto_zero l c B hB fun k => ⟨m₀ + 2 * (k + c₀), fun m hm z hz => ?_⟩
    have h := hval m (by omega) z hz
    have ht : tval (0 : PowerSeries (Qbar l)) (l ^ (3 * m)) z = 0 := by simp [tval]
    rw [ht] at h
    unfold Cg at h ⊢
    rw [zero_sub, norm_neg, norm_mul, norm_mul, (hw m).1, norm_pow, hu, one_pow, one_mul, one_mul] at h
    rw [sub_zero]
    exact le_trans h (norm_lpow_anti (by omega))

  have hui : IsIntegral ℤ_[l] u := (isIntegral_iff_norm_le_one u).2 hu.le
  obtain ⟨c', hcc', huc'⟩ := (coefSup l).2.2.1 c u hui
  have hA' : ∀ n, A.coeff n ∈ c'.O := fun n => hcc' (hA n)
  have hB' : ∀ n, B.coeff n ∈ c'.O := fun n => hcc' (hB n)
  have hφA : ∀ n, ‖(compPow l A).coeff n‖ ≤ 1 := fun n => norm_le_one_of_mem c (compPow_coeff_mem c A hA n)
  have hφB : ∀ n, ‖(compPow l B).coeff n‖ ≤ 1 := fun n => norm_le_one_of_mem c (compPow_coeff_mem c B hB n)
  set F := A * compPow l B - u • (compPow l A * B) with hFdef
  have hF : ∀ n, F.coeff n ∈ c'.O := by
    intro n
    rw [hFdef, map_sub, PowerSeries.coeff_smul, smul_eq_mul]
    exact sub_mem (coeff_mul_mem _ _ _ hA' (compPow_coeff_mem c' B hB') n)
      (mul_mem huc' (coeff_mul_mem _ _ _ (compPow_coeff_mem c' A hA') hB' n))
  have hF0 : F = 0 := by
    refine GlobalTheory.KZ.series_eq_zero_of_vals_tendsto_zero l c' F hF fun k => ⟨m₀ + 2 * (k + c₀) + k + 2, fun L hL z hz => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
    have hy : IsPrimitiveRoot (z ^ l) (l ^ m) :=
      IsPrimitiveRoot.pow (pow_pos (Fact.out : l.Prime).pos _) hz (by ring)
    have hm1 : 1 ≤ m := by omega
    have hkm : k ≤ m := by omega
    set N := l ^ (3 * (m + 1))
    set M := l ^ (3 * m)
    have hzz := hz1 _ z hz
    have hyy := hz1 _ _ hy
    have hsN : ‖(z - 1) ^ N‖ ≤ ‖((l : ℕ) : Qbar l) ^ k‖ :=
      le_trans (small_pow hz (K := m) (le_trans (nat_bound m hm1) (Nat.pow_le_pow_right (Fact.out : l.Prime).pos (by omega))))
        (norm_lpow_anti hkm)
    have hsM : ‖(z - 1) ^ M‖ ≤ ‖((l : ℕ) : Qbar l) ^ k‖ :=
      le_trans (small_pow hz (K := m) (nat_bound m hm1)) (norm_lpow_anti hkm)
    have hmax : max ‖(z - 1) ^ N‖ ‖(z - 1) ^ M‖ ≤ ‖((l : ℕ) : Qbar l) ^ k‖ := max_le hsN hsM
    set a1 := tval A N z
    set b1 := tval B N z
    set a0 := tval A M (z ^ l)
    set b0 := tval B M (z ^ l)
    have na1 : ‖a1‖ ≤ 1 := norm_tval_le A N z hAn hzz
    have nb1 : ‖b1‖ ≤ 1 := norm_tval_le B N z hBn hzz
    have nb0 : ‖b0‖ ≤ 1 := norm_tval_le B M (z ^ l) hBn hyy
    have e1 : Cg k (tval (A * compPow l B) N z) (a1 * tval (compPow l B) N z) :=
      cg_of_le (tval_mul_le l A (compPow l B) N z hAn hφB hzz) hsN
    have e2 : Cg k (a1 * tval (compPow l B) N z) (a1 * b0) :=
      cg_mul na1 (le_trans (tval_compPow_le l B N M z hBn hzz) hmax)
    have e3 : Cg k (tval (compPow l A * B) N z) (tval (compPow l A) N z * b1) :=
      cg_of_le (tval_mul_le l (compPow l A) B N z hφA hBn hzz) hsN
    have e4 : Cg k (tval (compPow l A) N z * b1) (a0 * b1) := by
      have := cg_mul (n := k) nb1 (le_trans (tval_compPow_le l A N M z hAn hzz) hmax)
      rwa [mul_comm b1, mul_comm b1] at this
    have e5 : Cg k (a1 * b0) (w (m + 1) * u ^ (m + 1) * b1 * b0) := by
      have := cg_mul nb0 (cg_mono (k := k) (hval (m + 1) (by omega) z hz) (by omega))
      rwa [mul_comm b0, mul_comm b0] at this
    have e6 : Cg k (a0 * b1) (w m * u ^ m * b0 * b1) := by
      have := cg_mul nb1 (cg_mono (k := k) (hval m (by omega) (z ^ l) hy) (by omega))
      rwa [mul_comm b1, mul_comm b1] at this
    have e7 : Cg k (w (m + 1) * u ^ (m + 1) * b1 * b0) (w m * u ^ (m + 1) * b1 * b0) := by
      have hx : ‖u ^ (m + 1) * b1 * b0‖ ≤ 1 := by
        rw [norm_mul, norm_mul, norm_pow, hu, one_pow, one_mul]
        exact mul_le_one₀ nb1 (norm_nonneg _) nb0
      have := cg_mul hx (cg_mono (hw m).2 hkm)
      convert this using 1 <;> ring
    have eu : Cg k (u * (tval (compPow l A * B) N z)) (u * (w m * u ^ m * b0 * b1)) :=
      cg_mul hu.le (cg_trans e3 (cg_trans e4 e6))
    have etot := cg_sub' (cg_trans e1 (cg_trans e2 (cg_trans e5 e7))) eu
    have hid : w m * u ^ (m + 1) * b1 * b0 - u * (w m * u ^ m * b0 * b1) = 0 := by ring
    rw [hid] at etot
    have htF : tval F N z = tval (A * compPow l B) N z - u * tval (compPow l A * B) N z := by
      rw [hFdef, tval_sub, tval_smul]
    rw [htF]
    exact etot
  have hu1 : u = 1 := eq_one_of_compPow l A B u hA0 hB0 hu (sub_eq_zero.1 hF0)
  refine ⟨hu1, fun k => ⟨k, fun m hm n => ?_⟩⟩
  have hwi : IsIntegral ℤ_[l] (w m) := (isIntegral_iff_norm_le_one _).2 (hw m).1.le
  obtain ⟨cm, hccm, hwm⟩ := (coefSup l).2.2.1 c (w m) hwi
  set H := A - w m • B with hHdef
  have hH : ∀ n, H.coeff n ∈ cm.O := by
    intro n
    rw [hHdef, map_sub, PowerSeries.coeff_smul, smul_eq_mul]
    exact sub_mem (hccm (hA n)) (mul_mem hwm (hccm (hB n)))
  have key := GlobalTheory.KZ.CoefVal.coeff_cg_of_values l cm H k (max m₀ (max (2 * (k + c₀)) m)) hH (fun L hL z hz => by
    have hL1 : m₀ ≤ L := le_trans (le_max_left _ _) hL
    have hL2 : 2 * (k + c₀) ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
    have hL3 : m ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
    have hv := hval L hL1 z hz
    rw [hu1, one_pow, mul_one] at hv
    have nb : ‖tval B (l ^ (3 * L)) z‖ ≤ 1 := norm_tval_le B _ z hBn (hz1 L z hz)
    have h1 : Cg k (tval A (l ^ (3 * L)) z) (w L * tval B (l ^ (3 * L)) z) := cg_mono hv (by omega)
    have h2 : Cg k (w L * tval B (l ^ (3 * L)) z) (w m * tval B (l ^ (3 * L)) z) := by
      have := cg_mul nb (cg_mono (hwd m (L - m)) (by omega : k ≤ m))
      rw [show m + (L - m) = L by omega] at this
      rwa [mul_comm _ (w L), mul_comm _ (w m)] at this
    have h3 := cg_zero_of_cg (cg_trans h1 h2)
    rw [hHdef, tval_sub, tval_smul]
    exact h3) n
  have : H.coeff n = A.coeff n - w m * B.coeff n := by
    rw [hHdef, map_sub, PowerSeries.coeff_smul, smul_eq_mul]
  rw [this] at key
  unfold Cg at key ⊢
  rwa [sub_zero] at key
