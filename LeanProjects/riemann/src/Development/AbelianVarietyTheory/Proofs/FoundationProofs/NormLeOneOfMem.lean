import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.MinkAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict

namespace GlobalTheory.IntegralElementNorm

theorem norm_algebraMap_le_one {l : ℕ} [Fact l.Prime] (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
  exact (PadicAlgCl.norm_extends (p := l) _).trans_le (PadicInt.norm_le_one a)

theorem norm_le_one_of_isIntegral {l : ℕ} [Fact l.Prime] {x : PadicAlgCl l} (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 := by
  obtain ⟨f, hmon, hf⟩ := hx
  by_contra hbig
  push Not at hbig

  have hn : f.natDegree ≠ 0 := by
    intro h0
    simp [Polynomial.eq_one_of_monic_natDegree_zero hmon h0] at hf
  have key : x ^ f.natDegree =
      -∑ i ∈ Finset.range f.natDegree, algebraMap ℤ_[l] (PadicAlgCl l) (f.coeff i) * x ^ i := by
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, Polynomial.Monic.coeff_natDegree hmon, map_one,
      one_mul] at hf
    linear_combination hf
  have hsum : ‖∑ i ∈ Finset.range f.natDegree,
      algebraMap ℤ_[l] (PadicAlgCl l) (f.coeff i) * x ^ i‖ ≤ ‖x‖ ^ (f.natDegree - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    have hi' : i ≤ f.natDegree - 1 := by
      have := Finset.mem_range.1 hi
      omega
    rw [norm_mul, norm_pow]
    calc ‖algebraMap ℤ_[l] (PadicAlgCl l) (f.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ i :=
          mul_le_mul_of_nonneg_right (norm_algebraMap_le_one _) (by positivity)
      _ ≤ ‖x‖ ^ (f.natDegree - 1) := by
          rw [one_mul]
          exact pow_le_pow_right₀ hbig.le hi'
  have hnorm : ‖x‖ ^ f.natDegree ≤ ‖x‖ ^ (f.natDegree - 1) := by
    rw [← norm_pow, key, norm_neg]
    exact hsum
  have hlt : ‖x‖ ^ (f.natDegree - 1) < ‖x‖ ^ f.natDegree := pow_lt_pow_right₀ hbig (by omega)
  linarith

theorem norm_le_one_of_mem {l : ℕ} [Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l) {x : Formalism.ConjugateSelfDual.Qbar l}
    (hx : x ∈ UpperTheory.V.HV.Coef.O c) : ‖x‖ ≤ (1 : ℝ) := by

  have : Module.Finite ℤ_[l] c.O := c.fin
  have hint : IsIntegral ℤ_[l] (⟨x, hx⟩ : c.O) := Algebra.IsIntegral.isIntegral _
  exact norm_le_one_of_isIntegral (hint.map c.O.val)

end GlobalTheory.IntegralElementNorm
