import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.ReproCoreStatement

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.S0.Fdeg

open Formalism.QuantumDeterminants

theorem integral_normSq_coef (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (w : H) (d : ℝ) (μG : Measure (Mt k r)) (hw : ‖w‖ = 1)
    (hF : IsFdegB μG σ d) :
    ∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG = 1 / d := by
  obtain ⟨_, hS⟩ := hF
  have h1 := (hS w w w w).2
  have hww : ⟪w, w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw]; simp
  rw [hww] at h1
  have hfun : (fun g : Mt k r => ⟪w, σ (Matrix.of g) w⟫_ℂ * star ⟪w, σ (Matrix.of g) w⟫_ℂ) =
      fun g => ((‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    funext g
    rw [Complex.star_def, RCLike.mul_conj]
    push_cast; rfl
  rw [hfun, integral_complex_ofReal] at h1
  have h2 : ((∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG : ℝ) : ℂ) = ((1 / d : ℝ) : ℂ) := by
    rw [h1]; push_cast; ring
  exact_mod_cast h2

theorem fdegH_eq : FdegHEqStatement := by
  intro k r H _ _ σ w d μG hw hF
  unfold Formalism.MainNotions.S.fdegH
  rw [integral_normSq_coef k r H σ w d μG hw hF, hw]
  have hd : d ≠ 0 := ne_of_gt hF.1
  field_simp

end ReciprocityTheory.ChartRestriction.DS.Lap.S0.Fdeg
