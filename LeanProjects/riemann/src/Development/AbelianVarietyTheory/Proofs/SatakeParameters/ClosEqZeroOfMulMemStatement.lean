import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClosEqZeroOfMulMem
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LMulBeta
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_mem_clos_of_pow_mul_mul_mem_clos : ∀ {R : Type} [CommRing R] [IsDomain R] (p : ℕ), p.Prime → IsUnit ((p : ℕ) : R) → ∀ (π : R), π ≠ 0 →
  (∀ x : R, (∀ n : ℕ, π ^ n ∣ x) → x = 0) → ∀ (S : Subring R),
  (∀ s ∈ S, ∀ i : ℕ, π ^ i ∣ s → ∃ s' ∈ S, s = π ^ i * s') →
  (∀ y : R, (∀ k : ℕ, ∃ s ∈ S, π ∣ y - ((p : ℕ) : R) ^ k * s) → π ∣ y) →
  ∀ u : R, (∀ m : ℕ, 1 ≤ m → ∃ s ∈ S, ∃ e : R, (e = 1 ∨ e = -1) ∧
    π ^ (2 * p ^ m) ∣ ((p : ℕ) : R) * (((p : ℕ) : R) ^ (m - 1) * u - s) - e * π ^ (p ^ m)) →
  ∀ (a : R) (r : ℕ), a ∈ Clos S π → ((p : ℕ) : R) ^ r * a * u ∈ Clos S π → a = 0 := by
  first | exact @GlobalTheory.Pst.StLat.clos_eq_zero_of_mul_mem | exact GlobalTheory.Pst.StLat.clos_eq_zero_of_mul_mem | (intros; apply GlobalTheory.Pst.StLat.clos_eq_zero_of_mul_mem <;> assumption)
