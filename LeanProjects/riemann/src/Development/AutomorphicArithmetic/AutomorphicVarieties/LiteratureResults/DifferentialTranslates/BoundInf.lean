import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af

namespace UpperTheory.V.Lit.Dr

private theorem entry_sq_le {ι : Type} [Fintype ι] {a : ℕ} (A : Matrix (Fin a) (Fin a) (ι → ℂ)) (i j : Fin a) :
    ‖A i j‖ ≤ Real.sqrt ‖(A * star A) i i‖ := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun w => Real.le_sqrt_of_sq_le ?_
  refine le_trans ?_ (norm_le_pi_norm ((A * star A) i i) w)
  have h : (A * star A) i i w = ((∑ k, ‖A i k w‖ ^ 2 : ℝ) : ℂ) := by
    simp [Matrix.mul_apply, Finset.sum_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h, Complex.norm_real, Real.norm_eq_abs]
  exact le_trans (Finset.single_le_sum (f := fun k => ‖A i k w‖ ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ j)) (le_abs_self _)

theorem boundInf : BoundInf := by
  intro E _ _ a K hK hc
  obtain ⟨C₁, hC₁⟩ := hc.isBounded.exists_norm_le
  have hcont : ContinuousOn (fun p : HV E a => toL (Matrix.of p.1)⁻¹) K := by
    intro p hp
    obtain ⟨h, rfl⟩ := hK hp
    have hu : IsUnit (Matrix.of (sand h (hOne E a)).1).det := by
      rw [sand_val, hOne_val, mul_one, ← Matrix.isUnit_iff_isUnit_det]
      exact h.isUnit.mul h.isUnit.star
    have h1 : ContinuousAt (Inv.inv : Matrix (Fin a) (Fin a) (Cinf E) → _) (Matrix.of (sand h (hOne E a)).1) :=
      continuousAt_matrix_inv _ (by
        obtain ⟨u, hu⟩ := hu
        rw [← hu]
        exact NormedRing.inverse_continuousAt u)
    have h2 : Continuous (fun p : HV E a => (Matrix.of p.1 : Matrix (Fin a) (Fin a) (Cinf E))) :=
      continuous_subtype_val
    exact (ContinuousAt.comp (f := fun p : HV E a => (Matrix.of p.1 : Matrix (Fin a) (Fin a) (Cinf E))) h1
      h2.continuousAt).continuousWithinAt
  obtain ⟨C₂, hC₂⟩ := hc.exists_bound_of_continuousOn hcont
  refine ⟨a * (Real.sqrt C₁ * Real.sqrt C₂), fun g p hp hgp => ?_⟩
  obtain ⟨h, rfl⟩ := hK hp
  have hA : ∀ i j, ‖(g * h).val i j‖ ≤ Real.sqrt C₁ := fun i j => by
    refine (entry_sq_le _ i j).trans (Real.sqrt_le_sqrt (le_trans ?_ (hC₁ _ hgp)))
    have e : (g * h).val * star (g * h).val = Matrix.of (sand g (sand h (hOne E a))).1 := by
      rw [sand_val, sand_val, hOne_val]; simp only [Units.val_mul, star_mul, mul_assoc, one_mul]
    rw [e]
    exact (norm_le_pi_norm _ i).trans (norm_le_pi_norm (sand g (sand h (hOne E a))).1 i)
  have hB : ∀ i j, ‖(h⁻¹).val i j‖ ≤ Real.sqrt C₂ := fun i j => by
    have e0 : ‖(h⁻¹).val i j‖ = ‖(star (h⁻¹).val) j i‖ := by rw [Matrix.star_apply, norm_star]
    rw [e0]
    refine (entry_sq_le _ j i).trans (Real.sqrt_le_sqrt (le_trans ?_ (hC₂ _ hp)))
    have e : star (h⁻¹).val * star (star (h⁻¹).val) = (Matrix.of (sand h (hOne E a)).1)⁻¹ := by
      rw [sand_val, hOne_val, mul_one, star_star]
      refine (Matrix.inv_eq_left_inv ?_).symm
      rw [mul_assoc, ← mul_assoc (h⁻¹).val, Units.inv_mul, one_mul, ← star_mul, Units.mul_inv, star_one]
    rw [e]
    exact (norm_le_pi_norm _ j).trans (norm_le_pi_norm (toL (Matrix.of (sand h (hOne E a)).1)⁻¹) j)
  have h0 : (0 : ℝ) ≤ a * (Real.sqrt C₁ * Real.sqrt C₂) := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  have e : g.val = (g * h).val * (h⁻¹).val := by rw [← Units.val_mul, mul_inv_cancel_right]
  change ‖g.val i j‖ ≤ _
  rw [e, Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun k _ => (norm_mul_le _ _).trans
    (mul_le_mul (hA i k) (hB k j) (norm_nonneg _) (Real.sqrt_nonneg _))).trans ?_
  simp

end UpperTheory.V.Lit.Dr
