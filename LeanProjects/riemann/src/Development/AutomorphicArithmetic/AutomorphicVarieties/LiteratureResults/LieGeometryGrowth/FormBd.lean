import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.DegreeHermitianFormula
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PtRetr
open UpperTheory.V.Lit.Geo Matrix

private theorem form_bd {d : ℕ} (G : Matrix (Fin d) (Fin d) ℂ) (x y : Fin d → ℂ) :
    ‖star x ⬝ᵥ G *ᵥ y‖ ≤ (∑ i, ∑ j, ‖G i j‖) * ‖x‖ * ‖y‖ := by
  simp only [dotProduct, Matrix.mulVec, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_mul, Pi.star_apply, norm_star]
  calc ‖x i‖ * (‖G i j‖ * ‖y j‖) = ‖G i j‖ * ‖x i‖ * ‖y j‖ := by ring
    _ ≤ ‖G i j‖ * ‖x‖ * ‖y‖ := by
      gcongr
      · exact norm_le_pi_norm x i
      · exact norm_le_pi_norm y j

theorem UpperTheory.V.Lit.Geo.ptBd :
    PtBd := by
  intro E _ _ _ a ha U hU Ξ r χ G n e hD q
  refine ⟨∑ I : Fin q → Fin n, (∑ i, ∑ j, ‖G i j‖) * (∏ i, ‖UpperTheory.V.Lit.Dr.hv (e (I i))‖) ^ 2,
    by positivity, fun α β hα hβ g M M' hM hM' h1 h2 => ?_⟩
  rw [ptRetr E a ha U hU Ξ r χ G n e hD q α β hα hβ g, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun I _ => ?_)
  refine (form_bd _ _ _).trans ?_
  have b1 := h1 fun i => e (I i)
  have b2 := h2 fun i => e (I i)
  have hP : 0 ≤ ∏ i, ‖UpperTheory.V.Lit.Dr.hv (e (I i))‖ := by positivity
  have hS : 0 ≤ ∑ i, ∑ j, ‖G i j‖ := by positivity
  refine (mul_le_mul (mul_le_mul_of_nonneg_left b1 hS) b2 (norm_nonneg _)
    (mul_nonneg hS (mul_nonneg hM hP))).trans_eq ?_
  ring
