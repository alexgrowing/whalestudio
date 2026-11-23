import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

namespace UpperTheory.Small

open Formalism.BasicNotions

variable {R : Ranks} (H : Host R)

theorem two_mem : 2 ∈ H.small := by
  simp only [Formalism.HC.HostRaw.small, Nat.mem_primeFactors]
  refine ⟨Nat.prime_two, ?_, (H.QS_pos).ne'⟩
  have he : 2 ≤ R.e := H.two_le_e
  exact dvd_trans (dvd_pow_self 2 (by omega)) H.tower_dvd

theorem ne_two {l : ℕ} (h : l ∉ H.small) : l ≠ 2 := by
  rintro rfl
  exact h (two_mem H)

theorem not_mem_of_dvd_qd {l : ℕ} (hl : l ∣ H.q * H.d) : l ∉ H.small := by
  simp only [Formalism.HC.HostRaw.small, Nat.mem_primeFactors]
  rintro ⟨hp, hdq, -⟩
  have h1 : l ∣ Nat.gcd H.QS (H.q * H.d) := Nat.dvd_gcd hdq hl
  rw [H.QS_coprime.gcd_eq_one] at h1
  exact hp.one_lt.ne' (Nat.dvd_one.1 h1)

theorem q_not_mem : H.q ∉ H.small := not_mem_of_dvd_qd H (dvd_mul_right _ _)

theorem d_not_mem : H.d ∉ H.small := not_mem_of_dvd_qd H (dvd_mul_left _ _)

theorem not_mem_of_qd {l : ℕ} (hl : l = H.q ∨ l = H.d) : l ∉ H.small := by
  rcases hl with rfl | rfl
  · exact q_not_mem H
  · exact d_not_mem H

theorem not_mem_of_mod {l : ℕ} (h : l % (H.QS * H.q * H.d) = 1) : l ∉ H.small := by
  simp only [Formalism.HC.HostRaw.small, Nat.mem_primeFactors]
  rintro ⟨hp, hdq, -⟩
  have hm : l ∣ H.QS * H.q * H.d := dvd_trans hdq (by rw [mul_assoc]; exact dvd_mul_right _ _)
  have h1 : l ∣ l % (H.QS * H.q * H.d) := (Nat.dvd_mod_iff hm).2 dvd_rfl
  rw [h] at h1
  exact hp.one_lt.ne' (Nat.dvd_one.1 h1)

theorem factorization_eq_zero {l : ℕ} (h : l ∉ H.small) : H.QS.factorization l = 0 := by
  rw [Nat.factorization_eq_zero_iff]
  by_contra hc
  push_neg at hc
  apply h
  simp only [Formalism.HC.HostRaw.small, Nat.mem_primeFactors]
  exact ⟨hc.1, hc.2.1, hc.2.2⟩

variable {H} in
theorem localLevel_eq_one_of_not_mem_smallPrimes {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (h : N.l i ∉ H.small) : N.s0 i = 1 := by
  rw [N.restNLevelExponent_of_odd i (ne_two H h), factorization_eq_zero H h]; rfl

end UpperTheory.Small
