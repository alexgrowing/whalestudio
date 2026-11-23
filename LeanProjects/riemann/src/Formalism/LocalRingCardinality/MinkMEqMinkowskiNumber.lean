import Formalism.LocalRingCardinality.DataMink
import Formalism.LocalRingCardinality.DataErr
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.MinkowskiNumberDvdFactorial

namespace Formalism.BasicNotions

open Formalism.HermitianLatticeCounting.S6 (minkowskiM minkowskiExp)

theorem minkM_pos (n : ℕ) : 0 < minkM n :=
  Finset.prod_pos fun _ hp => pow_pos (Finset.mem_filter.1 hp).2.pos _

theorem padicValNat_prod_primes (p : ℕ) (hp : p.Prime) (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (e : ℕ → ℕ) :
    padicValNat p (∏ q ∈ S, q ^ e q) = if p ∈ S then e p else 0 := by
  have := Fact.mk hp
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have hS' : ∀ q ∈ S, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hap : a.Prime := hS a (Finset.mem_insert_self _ _)
    have := Fact.mk hap
    have h1 : a ^ e a ≠ 0 := pow_ne_zero _ hap.ne_zero
    have h2 : ∏ q ∈ S, q ^ e q ≠ 0 := Finset.prod_ne_zero_iff.2 fun q hq => pow_ne_zero _ (hS' q hq).ne_zero
    rw [Finset.prod_insert ha, padicValNat.mul h1 h2, ih hS', padicValNat.pow]
    by_cases hpa : p = a
    · subst hpa
      simp [ha]
    · have h3 : padicValNat p a = 0 := padicValNat_primes hpa
      simp [h3, hpa]

theorem minkowskiExp_eq_zero {n p : ℕ} (h : n + 1 < p) : minkowskiExp n p = 0 := by
  unfold minkowskiExp
  refine Finset.sum_eq_zero fun i _ => Nat.div_eq_of_lt ?_
  have h1 : 0 < p ^ i := pow_pos (by omega) _
  calc n < p - 1 := by omega
    _ ≤ p ^ i * (p - 1) := Nat.le_mul_of_pos_left _ h1

theorem minkowskiExp_eq_sum {n p K : ℕ} (hp : 2 ≤ p) (hK : n + 1 ≤ K) :
    minkowskiExp n p = ∑ i ∈ Finset.range K, n / (p ^ i * (p - 1)) := by
  unfold minkowskiExp
  refine Finset.sum_subset (Finset.range_subset_range.2 hK) fun i _ hi => Nat.div_eq_of_lt ?_
  have hi' : n + 1 ≤ i := by simpa using hi
  have h1 : i < 2 ^ i := Nat.lt_two_pow_self
  have h2 : 2 ^ i ≤ p ^ i := Nat.pow_le_pow_left hp _
  calc n < p ^ i := by omega
    _ ≤ p ^ i * (p - 1) := Nat.le_mul_of_pos_right _ (by omega)

theorem padicValNat_minkM (n p : ℕ) (hp : p.Prime) :
    padicValNat p (minkM n) = ∑ i ∈ Finset.range (n + 1), n / (p ^ i * (p - 1)) := by
  have h := padicValNat_prod_primes p hp ((Finset.range (n + 2)).filter Nat.Prime)
    (fun q hq => (Finset.mem_filter.1 hq).2) (minkowskiExp n)
  have e : padicValNat p (minkM n) = if p ∈ (Finset.range (n + 2)).filter Nat.Prime then minkowskiExp n p else 0 := h
  rw [e]
  by_cases hm : p ∈ (Finset.range (n + 2)).filter Nat.Prime
  · rw [if_pos hm]; rfl
  · rw [if_neg hm]
    have hlt : n + 1 < p := by
      by_contra hc
      exact hm (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hp⟩)
    exact (minkowskiExp_eq_zero hlt).symm

theorem padicValNat_minkM' (n p K : ℕ) (hp : p.Prime) (hK : n + 1 ≤ K) :
    padicValNat p (minkM n) = ∑ i ∈ Finset.range K, n / (p ^ i * (p - 1)) :=
  (padicValNat_minkM n p hp).trans (minkowskiExp_eq_sum hp.two_le hK)

theorem prime_le_of_dvd_minkM {n p : ℕ} (hp : p.Prime) (h : p ∣ minkM n) : p ≤ n + 1 := by
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 h
  have hq' := Finset.mem_filter.1 hq
  have : p = q := (Nat.prime_dvd_prime_iff_eq hp hq'.2).1 (hp.dvd_of_dvd_pow hpq)
  have := Finset.mem_range.1 hq'.1
  omega

theorem minkM_dvd_minkM {n n' : ℕ} (h : n ≤ n') : minkM n ∣ minkM n' := by
  refine (Nat.factorization_prime_le_iff_dvd (minkM_pos n).ne' (minkM_pos n').ne').1 fun p hp => ?_
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp, padicValNat_minkM' n p (n' + 1) hp (by omega),
    padicValNat_minkM n' p hp]
  exact Finset.sum_le_sum fun i _ => Nat.div_le_div_right h

theorem minkM_dvd_factorial (n : ℕ) : minkM n ∣ (2 * n).factorial := Formalism.HermitianLatticeCounting.P.minkowski_number_dvd_factorial n

theorem log_minkM_le_two (n : ℕ) : Real.log (minkM n : ℝ) ≤ 2 * n * Real.log (2 * n) := by
  have h1 : minkM n ≤ (2 * n) ^ (2 * n) :=
    (Nat.le_of_dvd (Nat.factorial_pos _) (minkM_dvd_factorial n)).trans (Nat.factorial_le_pow _)
  have h2 : (minkM n : ℝ) ≤ ((2 * n : ℕ) : ℝ) ^ (2 * n) := by exact_mod_cast h1
  have h3 : (0 : ℝ) < minkM n := by exact_mod_cast minkM_pos n
  have h4 := Real.log_le_log h3 h2
  rw [Real.log_pow] at h4
  push_cast at h4
  exact h4

theorem Ranks.two_le_fN (R : Ranks) : 2 ≤ R.f * R.N R.m := by
  have hf : 2 ≤ R.f := by
    have h1 := R.two_le_m
    have h2 := R.m_le_f
    unfold Ranks.f Ranks.n; omega
  have hN : 1 ≤ R.N R.m := by
    have h1 := R.k_ge
    have h2 : R.k ≤ R.N R.m := Nat.le_add_right _ _
    omega
  calc 2 = 2 * 1 := rfl
    _ ≤ R.f * R.N R.m := Nat.mul_le_mul hf hN

theorem DGamMink.mem {D : D7} (h : DGamMink D) (hD : DGamDef D) (u : D.what₂.Word) :
    (D.mem u).C.DGam = minkM (2 * D.R.f * D.R.N D.R.m) := by
  rw [← hD.one u D.u₀ D.what₂.mu0, hD.one D.u₀ D.u₀ D.what₂.mu0]; exact h

theorem DGamMink.chTw {D : D7} (h : DGamMink D) (hD : DGamDef D) (u : D.what₂.Word) (μ : D.what₂.Tup) :
    (D.chTw u μ).DGam = minkM (2 * D.R.f * D.R.N D.R.m) :=
  (hD.one D.u₀ u μ).trans h

theorem DGamMink.padicValNat {D : D7} (h : DGamMink D) (hD : DGamDef D) (u : D.what₂.Word) (p : ℕ) (hp : p.Prime) :
    padicValNat p (D.mem u).C.DGam =
      ∑ i ∈ Finset.range (2 * D.R.f * D.R.N D.R.m + 1), 2 * D.R.f * D.R.N D.R.m / (p ^ i * (p - 1)) := by
  rw [h.mem hD u]; exact padicValNat_minkM _ p hp

theorem DGamMink.smooth {D : D7} (h : DGamMink D) (hD : DGamDef D) (u : D.what₂.Word) (p : ℕ) (hp : p.Prime)
    (hd : p ∣ (D.mem u).C.DGam) : p ≤ 2 * D.R.f * D.R.N D.R.m + 1 := by
  rw [h.mem hD u] at hd; exact prime_le_of_dvd_minkM hp hd

theorem DGamMink.fact {D : D7} (h : DGamMink D) (hD : DGamDef D) : FactDGam D 12 := by
  intro u
  rw [h.mem hD u]
  have hy : (2 : ℝ) ≤ (D.R.f : ℝ) * D.R.N D.R.m := by exact_mod_cast D.R.two_le_fN
  have h1 := log_minkM_le_two (2 * D.R.f * D.R.N D.R.m)
  have e : ((2 * D.R.f * D.R.N D.R.m : ℕ) : ℝ) = 2 * ((D.R.f : ℝ) * D.R.N D.R.m) := by push_cast; ring
  rw [e] at h1
  have e2 : (2 : ℝ) * (2 * ((D.R.f : ℝ) * D.R.N D.R.m)) = 2 * 2 * ((D.R.f : ℝ) * D.R.N D.R.m) := by ring
  have h2 : Real.log (2 * (2 * ((D.R.f : ℝ) * D.R.N D.R.m))) =
      Real.log 2 + Real.log 2 + Real.log ((D.R.f : ℝ) * D.R.N D.R.m) := by
    rw [e2, Real.log_mul (by norm_num) (by linarith), Real.log_mul (by norm_num) (by norm_num)]
  have h3 : Real.log 2 ≤ Real.log ((D.R.f : ℝ) * D.R.N D.R.m) := Real.log_le_log (by norm_num) hy
  rw [h2] at h1
  have h4 : 2 * (2 * ((D.R.f : ℝ) * D.R.N D.R.m)) * (Real.log 2 + Real.log 2 + Real.log ((D.R.f : ℝ) * D.R.N D.R.m)) ≤
      2 * (2 * ((D.R.f : ℝ) * D.R.N D.R.m)) * (3 * Real.log ((D.R.f : ℝ) * D.R.N D.R.m)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  calc Real.log (minkM (2 * D.R.f * D.R.N D.R.m) : ℝ)
      ≤ 2 * (2 * ((D.R.f : ℝ) * D.R.N D.R.m)) * (3 * Real.log ((D.R.f : ℝ) * D.R.N D.R.m)) := h1.trans h4
    _ = 12 * D.R.f * D.R.N D.R.m * Real.log ((D.R.f : ℝ) * D.R.N D.R.m) := by ring

end Formalism.BasicNotions
