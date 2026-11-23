import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.OmG

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal

namespace PositivityTheory.KB.MomentRationality.Cz.Pk

variable {ι : Type} {N : ℕ}

theorem entry_mul_le {A B : Matrix (Fin N) (Fin N) ℂ} {a b : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ a)
    (hB : ∀ i j, ‖B i j‖ ≤ b) (i j : Fin N) : ‖(A * B) i j‖ ≤ N * (a * b) := by
  rw [mul_apply]
  calc ‖∑ k, A i k * B k j‖ ≤ ∑ k, ‖A i k * B k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin N, a * b := by
        gcongr with k
        rw [norm_mul]
        exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) ((norm_nonneg _).trans (hA i k))
    _ = N * (a * b) := by simp

theorem adj_le {A : Matrix (Fin N) (Fin N) ℂ} {M : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ M) (i j : Fin N) :
    ‖adjugate A i j‖ ≤ (N.factorial : ℝ) * (max M 1) ^ N := by
  rw [adjugate_apply]
  have hb : ∀ k l, (NormedField.toAbsoluteValue ℂ) (A.updateRow j (Pi.single i 1) k l) ≤ max M 1 := by
    intro k l
    show ‖A.updateRow j (Pi.single i 1) k l‖ ≤ max M 1
    rcases eq_or_ne k j with rfl | hk
    · rw [updateRow_self]
      by_cases hl : l = i
      · subst hl; simp
      · simp [hl]
    · rw [updateRow_ne hk]; exact (hA k l).trans (le_max_left _ _)
  have h := Matrix.det_le hb
  rw [nsmul_eq_mul, Fintype.card_fin] at h
  exact h

theorem tri (M : ℝ) : ∃ R0 : ℝ, ∀ (h p p' u : Matrix (Fin N) (Fin N) ℂ) (s s' : Fin N → ℝ),
    (∀ i, |s i - s' i| ≤ 1) → h.BlockTriangular id → p.BlockTriangular id → p'.BlockTriangular id →
    (∀ i j, ‖p i j‖ ≤ M) → (∀ i j, ‖p' i j‖ ≤ M) → p.det = 1 → p'.det = 1 → u ∈ unitaryGroup (Fin N) ℂ →
    h * p * diagonal (fun i => ((Real.exp (s i) : ℝ) : ℂ)) =
      p' * diagonal (fun i => ((Real.exp (s' i) : ℝ) : ℂ)) * u →
    ∀ i j, ‖h i j‖ ≤ R0 := by
  refine ⟨N * (N * (M * Real.exp 1) * ((N.factorial : ℝ) * (max M 1) ^ N)), ?_⟩
  intro h p p' u s s' hss hh hp hp' hpM hp'M hpd hp'd hu heq i j
  set a := diagonal (fun i => ((Real.exp (s i) : ℝ) : ℂ)) with ha
  set a' := diagonal (fun i => ((Real.exp (s' i) : ℝ) : ℂ)) with ha'
  set ai := diagonal (fun i => ((Real.exp (-s i) : ℝ) : ℂ)) with hai
  have haai : a * ai = 1 := by
    rw [ha, hai, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  have hpadj : p * adjugate p = 1 := by rw [mul_adjugate, hpd, one_smul]
  have hrec : h * p * a * ai * adjugate p = h := by
    rw [show h * p * a * ai * adjugate p = h * (p * (a * ai) * adjugate p) by simp only [Matrix.mul_assoc],
      haai, Matrix.mul_one, hpadj, Matrix.mul_one]
  rw [heq] at hrec
  have hdet' : IsUnit (p' * a').det := by
    rw [det_mul, hp'd, one_mul, ha', det_diagonal]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun k _ => by exact_mod_cast (Real.exp_pos _).ne')
  have hu_eq : u = (p' * a')⁻¹ * (h * p * a) := by
    rw [heq, Matrix.nonsing_inv_mul_cancel_left (A := p' * a') (B := u) hdet']
  have hut : u.BlockTriangular id := by
    haveI := invertibleOfIsUnitDet (p' * a') hdet'
    rw [hu_eq]
    exact (blockTriangular_inv_of_blockTriangular (hp'.mul (blockTriangular_diagonal _))).mul
      ((hh.mul hp).mul (blockTriangular_diagonal _))
  have hstar : star u * u = 1 := (mem_unitaryGroup_iff'.1 hu)
  have hinv : u⁻¹ = star u := Matrix.inv_eq_left_inv hstar
  have hut' : (star u).BlockTriangular id := by
    rw [← hinv]
    haveI : Invertible u := invertibleOfLeftInverse _ _ hstar
    exact blockTriangular_inv_of_blockTriangular hut
  have hoff : ∀ k l, k ≠ l → u k l = 0 := by
    intro k l hkl
    rcases lt_or_gt_of_ne hkl with h1 | h1
    · have := hut' (show id k < id l from h1)
      rw [star_apply] at this
      simpa using this
    · exact hut h1
  have hD : ∀ k l, ‖(a' * u * ai) k l‖ ≤ Real.exp 1 := by
    intro k l
    rw [ha', hai, mul_diagonal, diagonal_mul]
    by_cases hkl : k = l
    · subst hkl
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
      calc Real.exp (s' k) * ‖u k k‖ * Real.exp (-s k) ≤ Real.exp (s' k) * 1 * Real.exp (-s k) := by
            gcongr; exact entry_norm_bound_of_unitary hu k k
        _ = Real.exp (s' k - s k) := by rw [mul_one, ← Real.exp_add]; ring_nf
        _ ≤ Real.exp 1 := Real.exp_le_exp.2 (by have := hss k; rw [abs_le] at this; linarith)
    · rw [hoff k l hkl]; simp; positivity
  rw [← hrec, show p' * a' * u * ai * adjugate p = p' * (a' * u * ai) * adjugate p by
    simp only [Matrix.mul_assoc]]
  exact entry_mul_le (entry_mul_le hp'M hD) (adj_le hpM) i j

end PositivityTheory.KB.MomentRationality.Cz.Pk

end
