import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc

open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.LocalSeries

theorem good_prime_local_series : E2a → E2b → ∀ (k N : ℕ) (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ), IsEig k N χ a → 1 ≤ k → ∀ p : ℕ, p.Prime → ∀ α β y s : ℂ, α ≠ 0 → β ≠ 0 → α + β = a p → α * β = χ p * (p : ℂ) ^ (k - 1) → ‖α / β‖ = 1 → ‖y‖ ≤ 1 → 0 < s.re → HasSum (fun j : ℕ => (χ p)⁻¹ ^ j * a (p ^ (2 * j)) * (y * (p : ℂ) ^ (-(s + k - 1))) ^ j) ((1 - (y * (p : ℂ) ^ (-s)) ^ 2) * ((1 - α / β * (y * (p : ℂ) ^ (-s)))⁻¹ * (1 - y * (p : ℂ) ^ (-s))⁻¹ * (1 - (α / β)⁻¹ * (y * (p : ℂ) ^ (-s)))⁻¹)) := by
  intro hE2a hE2b k N χ a hEig hk p hp α β y s hα hβ hsum hprod hr hy hs
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpos : 0 < p := hp.pos
  set c : ℂ := χ p with hc
  set P : ℂ := (p : ℂ) ^ (k - 1) with hP
  have hcP : c * P ≠ 0 := by rw [← hprod]; exact mul_ne_zero hα hβ
  have hc0 : c ≠ 0 := left_ne_zero_of_mul hcP
  have hP0 : P ≠ 0 := right_ne_zero_of_mul hcP

  have hX : ‖y * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hpos]
    have h1 : (p : ℝ) ^ (-s).re < 1 := by
      apply Real.rpow_lt_one_of_one_lt_of_neg
      · exact_mod_cast hp.one_lt
      · simpa using hs
    have h2 : 0 ≤ (p : ℝ) ^ (-s).re := by positivity
    calc ‖y‖ * (p : ℝ) ^ (-s).re ≤ 1 * (p : ℝ) ^ (-s).re := by gcongr
      _ < 1 := by simpa using h1

  have hpow : (p : ℂ) ^ (-(s + k - 1)) = (p : ℂ) ^ (-s) * P⁻¹ := by
    have hk1 : ((k : ℂ) - 1) = ((k - 1 : ℕ) : ℂ) := by
      rw [Nat.cast_sub hk]; simp
    have : -(s + k - 1) = -s + -(((k - 1 : ℕ) : ℂ)) := by
      rw [← hk1]; ring
    rw [this, Complex.cpow_add _ _ hp0, Complex.cpow_neg (p : ℂ) ((k - 1 : ℕ) : ℂ), Complex.cpow_natCast]
  have hmain := hE2b (α / β) (y * (p : ℂ) ^ (-s)) hr hX
  have hinv : c⁻¹ * β ^ 2 * P⁻¹ = (α / β)⁻¹ := by
    have h1 : c⁻¹ * P⁻¹ = (α * β)⁻¹ := by rw [hprod, mul_inv]
    calc c⁻¹ * β ^ 2 * P⁻¹ = (c⁻¹ * P⁻¹) * β ^ 2 := by ring
      _ = (α / β)⁻¹ := by rw [h1]; field_simp
  have hterm : ∀ j : ℕ, c⁻¹ ^ j * a (p ^ (2 * j)) * (y * (p : ℂ) ^ (-(s + k - 1))) ^ j =
      (∑ i ∈ Finset.range (2 * j + 1), (α / β) ^ i) * ((α / β)⁻¹ * (y * (p : ℂ) ^ (-s))) ^ j := by
    intro j
    have hcoef : a (p ^ (2 * j)) = β ^ (2 * j) * ∑ i ∈ Finset.range (2 * j + 1), (α / β) ^ i := by
      rw [(hE2a k N χ a hEig).2 p hp α β hsum hprod (2 * j), Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ 2 * j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hb : β ^ (2 * j) = β ^ (2 * j - i) * β ^ i := by
        rw [← pow_add, Nat.sub_add_cancel hi']
      rw [hb, div_pow]
      field_simp
    rw [hcoef, hpow, ← hinv, pow_mul β 2 j]
    simp only [mul_pow]
    ring
  rw [funext hterm]
  exact hmain

end GlobalTheory.CompanionTheory.LocalSeries
