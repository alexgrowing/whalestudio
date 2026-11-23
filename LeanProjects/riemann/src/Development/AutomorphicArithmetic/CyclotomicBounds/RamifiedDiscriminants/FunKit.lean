import Mathlib
import Formalism.LocalRingCardinality.HostCls
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsPrimeOfDifferentLe

open NumberField IsDedekindDomain Finset

noncomputable section

namespace UpperTheory.Ram.Fun

theorem sum_padicValNat_log_le {n : ℕ} (hn : n ≠ 0) (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) :
    ∑ l ∈ S, (padicValNat l n : ℝ) * Real.log l ≤ Real.log n := by
  classical
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  calc ∑ l ∈ S, (padicValNat l n : ℝ) * Real.log l
      = ∑ l ∈ S, (n.factorization l : ℝ) * Real.log l :=
        Finset.sum_congr rfl fun l hl => by rw [Nat.factorization_def n (hS l hl)]
    _ ≤ ∑ l ∈ S ∪ n.factorization.support, (n.factorization l : ℝ) * Real.log l :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun l _ _ =>
          mul_nonneg (by positivity) (Real.log_natCast_nonneg l)
    _ = ∑ l ∈ n.factorization.support, (n.factorization l : ℝ) * Real.log l := by
        refine (Finset.sum_subset Finset.subset_union_right fun l _ hl => ?_).symm
        rw [Finsupp.notMem_support_iff.1 hl]; simp

theorem sum_log_le_of_dvd {n : ℕ} (hn : n ≠ 0) (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime ∧ l ∣ n) :
    ∑ l ∈ S, Real.log l ≤ Real.log n := by
  refine le_trans (Finset.sum_le_sum fun l hl => ?_) (sum_padicValNat_log_le hn S fun l hl => (hS l hl).1)
  haveI := Fact.mk (hS l hl).1
  have h1 : (1 : ℝ) ≤ padicValNat l n := by exact_mod_cast one_le_padicValNat_of_dvd hn (hS l hl).2
  have := Real.log_natCast_nonneg l
  nlinarith

theorem sum_delta_log_le (E : Type) [Field E] [NumberField E] (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) :
    ∑ l ∈ S, (padicValInt l (discr E) : ℝ) / (Module.finrank ℚ E : ℝ) * Real.log l ≤
      Real.log (|(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) := by
  have hd : discr E ≠ 0 := discr_ne_zero E
  have hpos : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.2 (by exact_mod_cast hd)
  have hn : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  rw [Real.log_rpow hpos]
  have e : (((discr E).natAbs : ℕ) : ℝ) = |(discr E : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  have h := sum_padicValNat_log_le (Int.natAbs_ne_zero.2 hd) S hS
  rw [e] at h
  calc ∑ l ∈ S, (padicValInt l (discr E) : ℝ) / (Module.finrank ℚ E : ℝ) * Real.log l
      = (∑ l ∈ S, (padicValNat l (discr E).natAbs : ℝ) * Real.log l) / (Module.finrank ℚ E : ℝ) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun l _ => by
          rw [show padicValInt l (discr E) = padicValNat l (discr E).natAbs from rfl]; ring
    _ ≤ Real.log |(discr E : ℝ)| / (Module.finrank ℚ E : ℝ) := div_le_div_of_nonneg_right h hn.le
    _ = _ := by ring

theorem sum_ceil_nl_le (S : Finset ℕ) (n c t : ℕ → ℝ) {K k A B : ℝ} (hK : 0 ≤ K) (hk : 0 ≤ k)
    (hc : ∀ l ∈ S, 0 ≤ c l) (ht : ∀ l ∈ S, t l ≤ 3 / 2) (hn0 : ∀ l ∈ S, 0 ≤ n l)
    (hn : ∀ l ∈ S, n l = 0 ∨ n l = K * c l + k * (2 * c l + 1 + t l))
    (hA : ∑ l ∈ S, c l * Real.log l ≤ A) (hB : ∑ l ∈ S, Real.log l ≤ B) :
    ∑ l ∈ S, ((⌈n l⌉₊ : ℕ) : ℝ) * Real.log l ≤ (K + 2 * k) * A + (5 / 2 * k + 1) * B := by
  have h1 : ∀ l ∈ S, ((⌈n l⌉₊ : ℕ) : ℝ) * Real.log l ≤
      (K + 2 * k) * (c l * Real.log l) + (5 / 2 * k + 1) * Real.log l := by
    intro l hl
    have hl0 := Real.log_natCast_nonneg l
    have h2 := (Nat.ceil_lt_add_one (hn0 l hl)).le
    have h3 : n l + 1 ≤ (K + 2 * k) * c l + (5 / 2 * k + 1) := by
      have a := hc l hl
      have b := mul_le_mul_of_nonneg_left (ht l hl) hk
      rcases hn l hl with h | h <;> rw [h]
      · nlinarith [mul_nonneg hK a, mul_nonneg hk a]
      · nlinarith
    have := mul_le_mul_of_nonneg_right (h2.trans h3) hl0
    nlinarith
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have a := mul_le_mul_of_nonneg_left hA (by positivity : 0 ≤ K + 2 * k)
  have b := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ 5 / 2 * k + 1)
  linarith

open Formalism.BasicNotions

variable {R : Ranks} (H : Host R)

theorem coprime_condN_of_splitK {p : ℕ} (hp : p.Prime) (h : H.cls p = .splitK) : Nat.Coprime p (H.QS * H.q * H.d) :=
  (Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_of_splitK hp h)

theorem coprime_QSq_of_splitK {p : ℕ} (hp : p.Prime) (h : H.cls p = .splitK) : Nat.Coprime p (H.QS * H.q) :=
  (coprime_condN_of_splitK H hp h).coprime_dvd_right (dvd_mul_right _ _)

theorem exists_prime_of_different_le (v : HeightOneSpectrum (𝓞 H.F)) (hle : differentIdeal ℤ (𝓞 H.F) ≤ v.asIdeal) :
    ∃ p : ℕ, p.Prime ∧ p ∣ H.QS * H.q * H.d ∧ (p : 𝓞 H.F) ∈ v.asIdeal :=
  by apply _root_.UpperTheory.Reformulated.B.Qj12.exists_prime_of_different_le <;> assumption

end UpperTheory.Ram.Fun

end
