import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormMultisetSumLeOfForallLeUltrametric
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

open Polynomial

theorem not_dvd_den_of_padic_norm_le_one (p : ℕ) [Fact p.Prime] (c : ℚ)
    (hc : ‖(c : ℚ_[p])‖ ≤ 1) : ¬ p ∣ c.den := by
  intro hd
  have hden : ‖((c.den : ℤ) : ℚ_[p])‖ < 1 :=
    Padic.norm_intCast_lt_one_iff.2 (Int.natCast_dvd_natCast.2 hd)
  have hnum : ‖((c.num : ℤ) : ℚ_[p])‖ < 1 := by
    have h1 : ((c.num : ℤ) : ℚ_[p]) = (c : ℚ_[p]) * ((c.den : ℤ) : ℚ_[p]) := by
      have : (c.num : ℚ) = c * (c.den : ℤ) := by
        rw [Int.cast_natCast, Rat.mul_den_eq_num]
      exact_mod_cast congrArg (fun x : ℚ => (x : ℚ_[p])) this
    rw [h1, norm_mul]
    calc ‖(c : ℚ_[p])‖ * ‖((c.den : ℤ) : ℚ_[p])‖ ≤ 1 * ‖((c.den : ℤ) : ℚ_[p])‖ :=
          mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hden
  have hpn : (p : ℤ) ∣ c.num := Padic.norm_intCast_lt_one_iff.1 hnum
  have hcop := c.reduced
  have h2 : p ∣ c.num.natAbs := by
    rw [← Int.natCast_dvd_natCast, Int.natCast_natAbs]; exact (dvd_abs _ _).2 hpn
  have h3 := Nat.dvd_gcd h2 hd
  rw [hcop.gcd_eq_one] at h3
  exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.1 h3)

theorem padic_denom_coeff_of_roots_bounded :
    ∀ (p : ℕ) [Fact p.Prime] (q : Polynomial ℚ), q.Monic → ∀ k : ℕ,
      (∀ μ : PadicAlgCl p, (q.map (algebraMap ℚ (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ (p : ℝ) ^ k) →
      ∀ i, ∃ m : ℕ, m.Coprime p ∧ ∃ a : ℤ, ((p ^ (k * q.natDegree) * m : ℕ) : ℚ) * q.coeff i = a := by
  intro p _ q hq k hroot i
  have hp : p.Prime := Fact.out
  by_cases hi : q.natDegree < i
  · refine ⟨1, Nat.coprime_one_left _, 0, ?_⟩
    rw [coeff_eq_zero_of_natDegree_lt hi]; simp
  push_neg at hi
  have hQm : (q.map (algebraMap ℚ (PadicAlgCl p))).Monic := hq.map _
  have hQd : (q.map (algebraMap ℚ (PadicAlgCl p))).natDegree = q.natDegree := natDegree_map _
  have hB := GlobalTheory.norm_coeff_natDegree_sub_le_pow_of_roots_le (PadicAlgCl p) _ hQm ((p : ℝ) ^ k)
    hroot (q.natDegree - i) (by omega)
  rw [hQd, Nat.sub_sub_self hi, coeff_map] at hB
  have hn : ‖((q.coeff i : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (k * q.natDegree) := by
    have e : algebraMap ℚ (PadicAlgCl p) (q.coeff i) =
        algebraMap ℚ_[p] (PadicAlgCl p) ((q.coeff i : ℚ) : ℚ_[p]) := by
      rw [eq_ratCast, map_ratCast]
    rw [e, PadicAlgCl.norm_extends] at hB
    refine hB.trans ?_
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by exact_mod_cast hp.one_lt.le)
      (Nat.mul_le_mul_left k (Nat.sub_le _ _))
  set c : ℚ := ((p ^ (k * q.natDegree) : ℕ) : ℚ) * q.coeff i with hcdef
  have hc : ‖(c : ℚ_[p])‖ ≤ 1 := by
    have hp0 : (0 : ℝ) < (p : ℝ) ^ (k * q.natDegree) := by
      have : (0 : ℝ) < p := by exact_mod_cast hp.pos
      positivity
    rw [hcdef]
    push_cast
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
    calc ((p : ℝ) ^ (k * q.natDegree))⁻¹ * ‖((q.coeff i : ℚ) : ℚ_[p])‖
        ≤ ((p : ℝ) ^ (k * q.natDegree))⁻¹ * (p : ℝ) ^ (k * q.natDegree) :=
          mul_le_mul_of_nonneg_left hn (inv_nonneg.2 hp0.le)
      _ = 1 := inv_mul_cancel₀ hp0.ne'
  refine ⟨c.den, ?_, c.num, ?_⟩
  · exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2
      (not_dvd_den_of_padic_norm_le_one p c hc))
  · rw [← Rat.den_mul_eq_num c, hcdef]
    push_cast
    ring

end GlobalTheory
