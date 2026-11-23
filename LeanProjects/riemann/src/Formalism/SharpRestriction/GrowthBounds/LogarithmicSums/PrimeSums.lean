import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.Conclusion1OfGainBoundAll
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds

noncomputable section

open scoped BigOperators

namespace Formalism.MainNotions.AuxBlock8.Pf.G5

theorem sum_ite_mem_le {S R : Finset ℕ} (f : ℕ → ℝ) (hf : ∀ p ∈ R, 0 ≤ f p) :
    ∑ p ∈ S, (if p ∈ R then f p else 0) ≤ ∑ p ∈ R, f p := by
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp; exact (Finset.mem_filter.1 hp).2
  · intro p hp _; exact hf p hp

def prB (y : ℝ) : Finset ℕ := (Finset.range ⌈y⌉₊).filter Nat.Prime

theorem mem_prB {y : ℝ} {p : ℕ} : p ∈ prB y ↔ p.Prime ∧ (p : ℝ) < y := by
  simp [prB, Nat.lt_ceil, and_comm]

theorem card_prB_le (y : ℝ) (hy : 0 ≤ y) : ((prB y).card : ℝ) ≤ y + 1 := by
  have h1 : (prB y).card ≤ ⌈y⌉₊ := by
    have := Finset.card_filter_le (Finset.range ⌈y⌉₊) Nat.Prime
    simpa [prB] using this
  have h2 : ((prB y).card : ℝ) ≤ (⌈y⌉₊ : ℝ) := by exact_mod_cast h1
  have h3 := Nat.ceil_lt_add_one hy
  linarith

theorem sum_log_prB (y : ℝ) (hy : 0 ≤ y) : ∑ p ∈ prB y, Real.log p ≤ Real.log 4 * y := by
  refine le_trans ?_ (Chebyshev.theta_le_log4_mul_x hy)
  unfold Chebyshev.theta
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨h1, h2⟩ := mem_prB.1 hp
    exact Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨h1.pos, Nat.le_floor h2.le⟩, h1⟩
  · intro p hp _
    exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.1 hp).2.one_lt.le)

theorem sum_logdiv_prB (y : ℝ) (hy : 1 ≤ y) :
    ∑ p ∈ prB y, Real.log p / p ≤ Real.log y * (1 + Real.log y) := by
  have hly : 0 ≤ Real.log y := Real.log_nonneg hy
  have h1 : ∑ p ∈ prB y, Real.log p / p ≤ ∑ p ∈ prB y, Real.log y * ((p : ℝ))⁻¹ := by
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hp1, hp2⟩ := mem_prB.1 hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1.pos
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (Real.log_le_log hp0 hp2.le) (inv_nonneg.2 hp0.le)
  refine le_trans h1 ?_
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ hly
  have h2 : ∑ p ∈ prB y, ((p : ℝ))⁻¹ ≤ ∑ p ∈ Finset.Icc 1 ⌊y⌋₊, ((p : ℝ))⁻¹ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hp1, hp2⟩ := mem_prB.1 hp
      exact Finset.mem_Icc.2 ⟨hp1.pos, Nat.le_floor hp2.le⟩
    · intro p _ _
      positivity
  refine le_trans h2 ?_
  have h3 := harmonic_le_one_add_log ⌊y⌋₊
  rw [harmonic_eq_sum_Icc] at h3
  push_cast at h3
  refine le_trans h3 ?_
  have h4 : (1 : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast Nat.le_floor (by simpa using hy)
  have h5 : Real.log (⌊y⌋₊ : ℝ) ≤ Real.log y := Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
  linarith

end Formalism.MainNotions.AuxBlock8.Pf.G5

end
