import Mathlib
import Formalism.PeriodIntegrals.Minkowski
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiBound.PowerSumStep

namespace PI.Mk

open Finset

theorem term_eq (N p i : ℕ) : N / (p ^ i * (p - 1)) = (N / (p - 1)) / p ^ i := by
  rw [mul_comm, Nat.div_div_eq_div_mul]

theorem padicValNat_pow_mul_factorial (N ℓ : ℕ) (hℓ : ℓ.Prime) :
    padicValNat ℓ (ℓ ^ (N / (ℓ - 1)) * (N / (ℓ - 1)).factorial) = PI.minkowskiExp N ℓ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set m := N / (ℓ - 1) with hm
  have hmN : m ≤ N := Nat.div_le_self _ _
  have hlog : Nat.log ℓ m < N + 1 := lt_of_le_of_lt (Nat.log_le_self _ _) (Nat.lt_succ_of_le hmN)
  rw [padicValNat.mul (pow_ne_zero _ hℓ.ne_zero) (Nat.factorial_ne_zero _), padicValNat.prime_pow,
    padicValNat_factorial hlog]
  unfold PI.minkowskiExp
  simp_rw [term_eq, ← hm]
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos N)]
  simp

theorem minkowskiExp_eq_zero (N p : ℕ) (hp : N + 2 ≤ p) : PI.minkowskiExp N p = 0 := by
  unfold PI.minkowskiExp
  apply Finset.sum_eq_zero
  intro i _
  have h0 : N / (p - 1) = 0 := Nat.div_eq_of_lt (by omega)
  rw [term_eq, h0, Nat.zero_div]

theorem pow_minkowskiExp_dvd (N ℓ : ℕ) (hℓ : ℓ.Prime) :
    ℓ ^ PI.minkowskiExp N ℓ ∣ PI.minkowskiM N := by
  by_cases h : ℓ < N + 2
  · unfold PI.minkowskiM
    exact Finset.dvd_prod_of_mem (fun p => p ^ PI.minkowskiExp N p)
      (Finset.mem_filter.2 ⟨Finset.mem_range.2 h, hℓ⟩)
  · rw [minkowskiExp_eq_zero N ℓ (by omega), pow_zero]
    exact one_dvd _

theorem minkowskiBound_of (h : PGroupStep) : PI.MinkowskiBound := by
  intro N G hG
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro ℓ k hℓ hk
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime ℓ hk
  have hinj : Function.Injective G.subtype := G.subtype_injective
  have hcard : Nat.card (K.map G.subtype) = ℓ ^ k := by
    rw [Subgroup.card_map_of_injective hinj, hK]
  have hfin : Finite (K.map G.subtype) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hℓ.ne_zero)
  have hp : IsPGroup ℓ (K.map G.subtype) := IsPGroup.of_card hcard
  have hdvd := h N ℓ hℓ (K.map G.subtype) hfin hp
  rw [hcard] at hdvd
  have hne : ℓ ^ (N / (ℓ - 1)) * (N / (ℓ - 1)).factorial ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hℓ.ne_zero) (Nat.factorial_ne_zero _)
  have hle : k ≤ PI.minkowskiExp N ℓ := by
    rw [← padicValNat_pow_mul_factorial N ℓ hℓ]
    exact (padicValNat_dvd_iff_le hne).1 hdvd
  exact (pow_dvd_pow ℓ hle).trans (pow_minkowskiExp_dvd N ℓ hℓ)

end PI.Mk
