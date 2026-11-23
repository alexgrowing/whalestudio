import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SlmPhiCont

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem toL2_mem_smD_of_isSmoothL2 {ε : Fin n → Bool} {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : IsSmoothL2 ε F) :
    toL2 ε F ∈ smD ε (rreg ε) := by
  exact (mem_smD_iff ε (rreg ε) (toL2 ε F)).2 (slm_smooth hF)

private theorem cpart1_mem_inG (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.inG ε (S7.cpart1 ε Z) := by
  unfold Formalism.REAL.inG
  ext i j
  simp [S7.cpart1, Formalism.REAL.Jm, Jm, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.conjTranspose_apply, Complex.star_def]
  split_ifs <;> (try simp) <;> ring

private theorem cpart2_mem_inG (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.inG ε (S7.cpart2 ε Z) := by
  unfold Formalism.REAL.inG
  ext i j
  simp [S7.cpart2, Formalism.REAL.Jm, Jm, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.conjTranspose_apply, Complex.star_def]
  split_ifs <;> (try simp) <;> (try field_simp) <;> ring

private theorem cpart1_add_I_mul_cpart2 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) :
    S7.cpart1 ε Z c d + Complex.I * S7.cpart2 ε Z c d = Z c d := by
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  simp only [S7.cpart1, S7.cpart2, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
    smul_eq_mul]
  field_simp
  ring

theorem rightDerivative_toL2 {ε : Fin n → Bool} {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : IsSmoothL2 ε F) (a b : Fin n) :
    ((smE ε (rreg ε) a b ⟨toL2 ε F, toL2_mem_smD_of_isSmoothL2 hF⟩ : smD ε (rreg ε)) : L2 ε) =
      toL2 ε (Formalism.REAL.Eab ε a b F) := by
  rw [smE_apply (rreg_isURepOn ε), slm_dS hF (cpart1_mem_inG ε _), slm_dS hF (cpart2_mem_inG ε _)]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib, ← add_smul, cpart1_add_I_mul_cpart2]
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp [Matrix.single_apply]
  · intro d _ hd
    simp [Matrix.single_apply, Ne.symm hd]
  · intro h
    exact absurd (Finset.mem_univ b) h
  · intro c _ hc
    apply Finset.sum_eq_zero
    intro d _
    simp [Matrix.single_apply, Ne.symm hc]
  · intro h
    exact absurd (Finset.mem_univ a) h

end ReciprocityTheory.ChartRestriction.DS
