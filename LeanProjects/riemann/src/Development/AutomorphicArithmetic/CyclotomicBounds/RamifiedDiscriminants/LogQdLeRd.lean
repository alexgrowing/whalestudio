import Mathlib
import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
import Development.AutomorphicArithmetic.FrobeniusLocalisation.RadBounds2
import Development.AutomorphicArithmetic.FrobeniusLocalisation.RamEq
import Development.AutomorphicArithmetic.FrobeniusLocalisation.LogRdSum
import Development.AutomorphicArithmetic.FrobeniusLocalisation.VdTwo

open UpperTheory.HF
open NumberField Formalism.HC

theorem UpperTheory.KR.log_qd_le_rd :
    ∀ {φ : Frame} (H : HostAx φ), H.toHostRaw.PsQ → H.q ∈ H.ram ∧ Real.log H.q + Real.log H.d ≤ 2 * Real.log H.rd ∧ Real.sqrt ((H.q : ℝ) * H.d) ≤ H.rd ∧ 2 * Real.sqrt ((H.q : ℝ) * H.d) ≤ H.rd := by
  intro φ H hP
  have hq : H.q ∈ H.ram := (UpperTheory.HF.inert_q H).2.2.2.2 hP
  obtain ⟨hA, hB, -⟩ := UpperTheory.HF.ram_eq H
  have hd : H.d ∈ H.ram := (hA _).2 (Or.inr (Or.inr rfl))
  have h2 : 2 ∈ H.ram := (Finset.mem_inter.1 hB).2
  obtain ⟨hs, -, -, hrd⟩ := UpperTheory.HF.log_rd_sum H
  have vq : 1 / 2 ≤ H.vdH H.q := (UpperTheory.HF.mem_ram H H.q_prime).2.2.2.1 hq
  have vd : 1 / 2 ≤ H.vdH H.d := (UpperTheory.HF.mem_ram H H.d_prime).2.2.2.1 hd
  have v2 : 11 / 4 ≤ H.vdH 2 := (UpperTheory.HF.vd_two H).2.1
  have n2q : 2 ≠ H.q := fun h => H.q_notMem_small (h ▸ H.two_mem_small)
  have n2d : 2 ≠ H.d := fun h => H.d_notMem_small (h ▸ H.two_mem_small)
  have nqd : H.q ≠ H.d := H.q_ne_d
  have hsub : ({2, H.q, H.d} : Finset ℕ) ⊆ H.ram := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl <;> assumption
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun l : ℕ => H.vdH l * Real.log l) hsub
    (fun l _ _ => mul_nonneg (H.vdH_nonneg l) (Real.log_natCast_nonneg l))
  rw [← hs, Finset.sum_insert (by simp [n2q, n2d]), Finset.sum_pair nqd] at hle
  have lq := Real.log_natCast_nonneg H.q
  have ld := Real.log_natCast_nonneg H.d
  have l2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hq0 : (0 : ℝ) < H.q := Nat.cast_pos.2 H.q_prime.pos
  have hd0 : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
  push_cast at hle
  have key : Real.log 2 + (Real.log H.q + Real.log H.d) / 2 ≤ Real.log H.rd := by
    nlinarith [mul_le_mul_of_nonneg_right vq lq, mul_le_mul_of_nonneg_right vd ld,
      mul_le_mul_of_nonneg_right v2 l2.le]
  have hsq : 0 < Real.sqrt ((H.q : ℝ) * H.d) := Real.sqrt_pos.2 (mul_pos hq0 hd0)
  have h4 : 2 * Real.sqrt ((H.q : ℝ) * H.d) ≤ H.rd := by
    rw [← Real.log_le_log_iff (by positivity) hrd, Real.log_mul two_ne_zero hsq.ne',
      Real.log_sqrt (mul_pos hq0 hd0).le, Real.log_mul hq0.ne' hd0.ne']
    exact key
  exact ⟨hq, by linarith, by linarith, h4⟩
