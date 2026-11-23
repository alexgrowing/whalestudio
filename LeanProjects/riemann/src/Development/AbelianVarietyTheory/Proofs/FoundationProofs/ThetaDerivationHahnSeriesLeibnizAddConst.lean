import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.Glue

theorem theta_coeff {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : ℚ) (φ : HahnSeries ℚ Ω) (r : ℚ) :
    (theta s φ).coeff r = algebraMap ℚ Ω (s * r) * φ.coeff r := rfl

theorem theta_leibniz_add_const :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : ℚ) (P Q : HahnSeries ℚ Ω),
      theta s (P * Q) = theta s P * Q + P * theta s Q ∧ theta s (P + Q) = theta s P + theta s Q ∧
        ∀ c : Ω, theta s (HahnSeries.C c) = 0 := by
  intro Ω _ _ s P Q
  refine ⟨?_, ?_, ?_⟩
  · ext r
    have h1 : (theta s P).support ⊆ P.support := fun t ht h => ht (by simp [theta_coeff, h])
    have h2 : (theta s Q).support ⊆ Q.support := fun t ht h => ht (by simp [theta_coeff, h])
    rw [HahnSeries.coeff_add, HahnSeries.coeff_mul_left' P.isPWO_support h1,
      HahnSeries.coeff_mul_right' Q.isPWO_support h2, theta_coeff, HahnSeries.coeff_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    have := (Finset.mem_addAntidiagonal.1 hij).2.2
    rw [← this, theta_coeff, theta_coeff, mul_add, map_add]; ring
  · ext r; simp [theta_coeff, mul_add]
  · intro c; ext r
    rw [theta_coeff]
    by_cases h : r = 0
    · simp [h]
    · simp [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne h]

end GlobalTheory.Glue
