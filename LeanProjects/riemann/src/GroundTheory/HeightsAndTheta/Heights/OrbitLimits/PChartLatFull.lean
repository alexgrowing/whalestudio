import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsChartLatFull
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZeroCocycleSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace ChartLatFull

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def ratSat [CharZero Ω] (R : Subalgebra ℤ Ω) : Subalgebra ℚ Ω where
  carrier := {t | ∃ n : ℕ, 0 < n ∧ (n : Ω) * t ∈ R}
  mul_mem' := by
    rintro t u ⟨n, hn, ht⟩ ⟨m, hm, hu⟩
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have : ((n * m : ℕ) : Ω) * (t * u) = ((n : Ω) * t) * ((m : Ω) * u) := by push_cast; ring
    rw [this]
    exact R.mul_mem ht hu
  one_mem' := ⟨1, one_pos, by simp⟩
  add_mem' := by
    rintro t u ⟨n, hn, ht⟩ ⟨m, hm, hu⟩
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have : ((n * m : ℕ) : Ω) * (t + u) = (m : Ω) * ((n : Ω) * t) + (n : Ω) * ((m : Ω) * u) := by push_cast; ring
    rw [this]
    exact R.add_mem (R.mul_mem (R.natCast_mem m) ht) (R.mul_mem (R.natCast_mem n) hu)
  zero_mem' := ⟨1, one_pos, by simp⟩
  algebraMap_mem' := by
    intro q
    refine ⟨q.den, q.den_pos, ?_⟩
    have hd : (q.den : Ω) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
    have : (q.den : Ω) * algebraMap ℚ Ω q = (q.num : Ω) := by
      rw [eq_ratCast, Rat.cast_def, mul_div_cancel₀ _ hd]
    rw [this]
    exact R.intCast_mem _

theorem exists_nat_mul_mem [NumberField Ω] {y : (Σ k, ι k) → Ω} (hy : Birational y) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (t : Ω) : ∃ n : ℕ, 0 < n ∧ (n : Ω) * t ∈ chartRingZ y c := by
  obtain ⟨d, g, h, hg, hh, hh0, hgt⟩ := hy t
  have hX : ∏ k, y ⟨k, c k⟩ ^ d k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have hG : aeval y g / ∏ k, y ⟨k, c k⟩ ^ d k ∈ ratSat (chartRingZ y c) :=
    ⟨1, one_pos, by simpa using HilbertSamuel.ZeroCocycleSection.aeval_div_mem y c hg⟩
  have hH : aeval y h / ∏ k, y ⟨k, c k⟩ ^ d k ∈ ratSat (chartRingZ y c) :=
    ⟨1, one_pos, by simpa using HilbertSamuel.ZeroCocycleSection.aeval_div_mem y c hh⟩
  have hinv : (aeval y h / ∏ k, y ⟨k, c k⟩ ^ d k)⁻¹ ∈ ratSat (chartRingZ y c) :=
    Subalgebra.inv_mem_of_algebraic (A := ratSat (chartRingZ y c)) (x := ⟨_, hH⟩)
      (Algebra.IsAlgebraic.isAlgebraic _)
  have ht : t = (aeval y g / ∏ k, y ⟨k, c k⟩ ^ d k) * (aeval y h / ∏ k, y ⟨k, c k⟩ ^ d k)⁻¹ := by
    rw [hgt, inv_div, div_mul_div_comm, mul_comm (∏ k, y ⟨k, c k⟩ ^ d k), mul_assoc,
      mul_div_assoc, div_self (mul_ne_zero hh0 hX), mul_one]
  have := (ratSat (chartRingZ y c)).mul_mem hG hinv
  rw [← ht] at this
  exact this

end ChartLatFull

theorem ChartLatFull.proof : ChartLatFull.Statement := by
  intro K _ ι _ Ω _ _ y hy a τ s
  classical
  let t : (∀ k, ι k) → Ω := fun c => s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k))
  let N : (∀ k, ι k) → ℕ := fun c =>
    if hc : ∀ k, y ⟨k, c k⟩ ≠ 0 then (ChartLatFull.exists_nat_mul_mem hy c hc (t c)).choose else 1
  have hNpos : ∀ c, 0 < N c := by
    intro c
    simp only [N]
    split_ifs with hc
    · exact (ChartLatFull.exists_nat_mul_mem hy c hc (t c)).choose_spec.1
    · exact one_pos
  refine ⟨∏ c, N c, Finset.prod_pos fun c _ => hNpos c, ?_⟩
  show ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → _
  intro c hc
  have hN : (N c : Ω) * t c ∈ chartRingZ y c := by
    simp only [N, dif_pos hc]
    exact (ChartLatFull.exists_nat_mul_mem hy c hc (t c)).choose_spec.2
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ c)
  have : ((∏ c, N c : ℕ) : Ω) * s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) = (m : Ω) * ((N c : Ω) * t c) := by
    rw [hm]; push_cast; simp only [t]; ring
  rw [this]
  exact (chartRingZ y c).mul_mem ((chartRingZ y c).natCast_mem m) hN

end

end GroundTheory.Heights₂.Heights.Targets
