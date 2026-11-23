import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LevFUnitary

noncomputable section

open Matrix Complex

namespace PositivityTheory.Rg.Sw.Glob.VacI

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacB PositivityTheory.Rg.Sw.Glob.VacD PositivityTheory.Rg.Sw.Glob.VacG

variable {n : ℕ}

theorem blocks_kak (u u' : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) (hu' : u'ᴴ * u' = 1) (θ : Fin n → ℝ) :
    mM u * kth θ * mM u' = fromBlocks (u * (dR fun j => Real.cos (θ j)) * u') (u * (dR fun j => Real.sin (θ j)) * u')
      (-(u * (dR fun j => Real.sin (θ j)) * u')) (u * (dR fun j => Real.cos (θ j)) * u') := by
  have h1 : uᴴ⁻¹ = u := Matrix.inv_eq_right_inv hu
  have h2 : u'ᴴ⁻¹ = u' := Matrix.inv_eq_right_inv hu'
  simp only [mM, kth, dR, h1, h2, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, neg_zero, add_zero,
    zero_add, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

theorem det_mM_unitary (u : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) : (mM u).det = u.det * u.det := by
  rw [mM_unitary u hu, det_fromBlocks_zero₂₁]

private theorem det_kth_eq_one (θ : Fin n → ℝ) : (kth θ).det = 1 := by
  have hL : (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (I • (1 : Matrix (Fin n) (Fin n) ℂ))
      (0 : Matrix (Fin n) (Fin n) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ)).det = 1 := by
    rw [det_fromBlocks_zero₂₁]
    simp
  have hR : (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (-(I • (1 : Matrix (Fin n) (Fin n) ℂ)))
      (0 : Matrix (Fin n) (Fin n) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ)).det = 1 := by
    rw [det_fromBlocks_zero₂₁]
    simp
  have key : fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (I • (1 : Matrix (Fin n) (Fin n) ℂ))
        (0 : Matrix (Fin n) (Fin n) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ) * kth θ *
        fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (-(I • (1 : Matrix (Fin n) (Fin n) ℂ)))
        (0 : Matrix (Fin n) (Fin n) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ)
      = fromBlocks (diagonal fun j => (Real.cos (θ j) : ℂ) - I * Real.sin (θ j)) (0 : Matrix (Fin n) (Fin n) ℂ)
          (-diagonal fun j => (Real.sin (θ j) : ℂ))
          (diagonal fun j => (Real.cos (θ j) : ℂ) + I * Real.sin (θ j)) := by
    simp only [kth, fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul]
    congr 1 <;> ext i j <;> by_cases h : i = j <;> simp [h, diagonal_apply] <;>
      first
      | ring1
      | linear_combination Complex.sin ((θ j : ℝ) : ℂ) * I_sq
  have hprod : ∏ j, (((Real.cos (θ j) : ℂ) - I * Real.sin (θ j)) * ((Real.cos (θ j) : ℂ) + I * Real.sin (θ j))) = 1 := by
    apply Finset.prod_eq_one
    intro j _
    have hp := Real.sin_sq_add_cos_sq (θ j)
    generalize Real.cos (θ j) = c at *
    generalize Real.sin (θ j) = s at *
    have hp' : (s : ℂ) ^ 2 + (c : ℂ) ^ 2 = 1 := by exact_mod_cast hp
    linear_combination hp' - (s : ℂ) ^ 2 * I_sq
  have h := congrArg Matrix.det key
  rw [det_mul, det_mul, hL, hR, det_fromBlocks_zero₁₂, det_diagonal, det_diagonal, ← Finset.prod_mul_distrib,
    hprod, one_mul, mul_one] at h
  exact h

theorem det_kth (θ : Fin n → ℝ) (hθ : ∀ j, -(Real.pi / 2) < θ j ∧ θ j ≤ Real.pi / 2) : (kth θ).det = 1 := by
  exact det_kth_eq_one θ

theorem jF_kak (e : ℤ) (p q : ℕ) (k : GR n) (u u' : Matrix (Fin n) (Fin n) ℂ) (θ : Fin n → ℝ) (hu : uᴴ * u = 1)
    (hu' : u'ᴴ * u' = 1) (hθ : ∀ j, -(Real.pi / 2) < θ j ∧ θ j ≤ Real.pi / 2) (hkm : mR k = mM u * kth θ * mM u') :
    jF e p q k (I • (1 : Matrix (Fin n) (Fin n) ℂ)) =
      (u.det * u.det * (u'.det * u'.det)) ^ e * (u.det * (∏ j, cexp (-(I * (θ j : ℂ)))) * u'.det) ^ (-(p : ℤ)) *
        (u.det * (∏ j, cexp (I * (θ j : ℂ))) * u'.det) ^ (-(q : ℤ)) := by
  have hdet : (mR k).det = u.det * u.det * (u'.det * u'.det) := by
    rw [hkm, det_mul, det_mul, det_mM_unitary u hu, det_mM_unitary u' hu', det_kth θ hθ, mul_one]
  have hk2 := hkm.trans (blocks_kak u u' hu hu' θ)
  have hdm : diagonal (fun j => cexp (-(I * (θ j : ℂ)))) =
      (dR fun j => Real.cos (θ j)) - I • (dR fun j => Real.sin (θ j)) := by
    ext a b
    by_cases h : a = b
    · subst h
      simp only [dR, diagonal_apply_eq, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      rw [show -(I * (θ a : ℂ)) = (-(θ a : ℂ)) * I by ring, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      ring
    · simp [dR, diagonal_apply, h]
  have hdp : diagonal (fun j => cexp (I * (θ j : ℂ))) =
      (dR fun j => Real.cos (θ j)) + I • (dR fun j => Real.sin (θ j)) := by
    ext a b
    by_cases h : a = b
    · subst h
      simp only [dR, diagonal_apply_eq, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      rw [show I * (θ a : ℂ) = (θ a : ℂ) * I by ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      ring
    · simp [dR, diagonal_apply, h]
  have hA : toBlocks₂₁ (mR k) * (I • (1 : Matrix (Fin n) (Fin n) ℂ)) + toBlocks₂₂ (mR k) =
      u * diagonal (fun j => cexp (-(I * (θ j : ℂ)))) * u' := by
    rw [hk2, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, hdm]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_neg]
    abel
  have hZ : (I • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ = -(I • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, conj_I, neg_smul]
  have hB : toBlocks₂₁ (mR k) * (I • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ + toBlocks₂₂ (mR k) =
      u * diagonal (fun j => cexp (I * (θ j : ℂ))) * u' := by
    rw [hZ, hk2, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, hdp, Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_one]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_neg, neg_neg]
    abel
  simp only [jF, hdet, hA, hB, det_mul, det_diagonal]

end PositivityTheory.Rg.Sw.Glob.VacI
