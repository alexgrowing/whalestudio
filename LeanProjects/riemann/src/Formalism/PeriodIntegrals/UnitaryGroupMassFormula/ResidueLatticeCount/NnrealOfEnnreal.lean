import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.HeckeLower
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.UnderEqOfNotCoprime

namespace PI.Residue

open NumberField
open scoped ENNReal NNReal

noncomputable def wt (s : ℝ) : ℕ →* ℝ≥0∞ where
  toFun n := (((n : ℝ≥0) ^ (-s) : ℝ≥0) : ℝ≥0∞)
  map_one' := by simp
  map_mul' a b := by
    rw [Nat.cast_mul, NNReal.mul_rpow, ENNReal.coe_mul]

theorem wt_apply (s : ℝ) (n : ℕ) : wt s n = (((n : ℝ≥0) ^ (-s) : ℝ≥0) : ℝ≥0∞) := rfl

theorem nnreal_of_ennreal {β : Type*} (f : β → ℝ≥0) (g : ℕ → ℝ≥0) (m : ℕ) (hg : Summable g)
    (h : ∑' b, (f b : ℝ≥0∞) ≤ (∑' k, (g k : ℝ≥0∞)) ^ m) :
    Summable f ∧ ∑' b, f b ≤ (∑' k, g k) ^ m := by
  rw [← ENNReal.coe_tsum hg, ← ENNReal.coe_pow] at h
  have hf : Summable f :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp (ne_top_of_le_ne_top ENNReal.coe_ne_top h)
  refine ⟨hf, ?_⟩
  rw [← ENNReal.coe_tsum hf] at h
  exact_mod_cast h

theorem zetaLePow : ZetaLePow := by
  intro E _ _ s hs
  have h := tsum_ideal_le E (wt s)
  have h0 : wt s 0 = 0 := by
    rw [wt_apply, Nat.cast_zero, NNReal.zero_rpow (by linarith : -s ≠ 0), ENNReal.coe_zero]
  rw [tsum_eq_zero_add' ENNReal.summable, h0, zero_add] at h
  simp only [wt_apply] at h
  have hg : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ≥0) ^ (-s))) := by
    rw [← NNReal.summable_coe]
    have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -s < -1))
    simpa using this
  obtain ⟨hf, hle⟩ := nnreal_of_ennreal
    (fun I : {I : Ideal (𝓞 E) // I ≠ ⊥} => ((Ideal.absNorm I.1 : ℝ≥0) ^ (-s))) _ _ hg h
  constructor
  · have := NNReal.summable_coe.mpr hf
    simpa using this
  · have := NNReal.coe_le_coe.mpr hle
    rw [NNReal.coe_tsum, NNReal.coe_pow, NNReal.coe_tsum] at this
    simpa [idealZeta, zetaR] using this

end PI.Residue
