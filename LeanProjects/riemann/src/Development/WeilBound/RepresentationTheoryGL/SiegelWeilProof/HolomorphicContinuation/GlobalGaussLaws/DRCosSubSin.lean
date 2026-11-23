import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DRConjTranspose
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ExistsCircleDetNe

noncomputable section

open Matrix Complex

namespace PositivityTheory.Rg.Sw.Glob.VacG

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacB PositivityTheory.Rg.Sw.Glob.VacD PositivityTheory.Rg.Sw.Glob.VacU

variable {n : ℕ}

theorem inK_blocks (k : M2 n) (hk : InK k) :
    k.toBlocks₂₁ = -k.toBlocks₁₂ ∧ k.toBlocks₂₂ = k.toBlocks₁₁ := by
  unfold InK InG at hk
  obtain ⟨hG, hU⟩ := hk
  have hU' : k * kᴴ = 1 := mul_eq_one_comm.mp hU
  have hc : JJ n * k = k * JJ n := by
    calc JJ n * k = (k * kᴴ) * JJ n * k := by rw [hU', Matrix.one_mul]
      _ = k * (kᴴ * JJ n * k) := by simp only [Matrix.mul_assoc]
      _ = k * JJ n := by rw [hG]
  rw [← fromBlocks_toBlocks k] at hc
  unfold JJ at hc
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at hc
  simp at hc
  exact ⟨hc.1, hc.2.1⟩

theorem mM_unitary (u : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) : mM u = fromBlocks u 0 0 u := by
  rw [mM, Matrix.inv_eq_right_inv hu]

theorem dR_cos_add_sin (θ : Fin n → ℝ) :
    (dR fun j => Real.cos (θ j)) + I • (dR fun j => Real.sin (θ j)) = diagonal fun j => cexp (I * (θ j : ℂ)) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [dR, Matrix.diagonal_apply_eq, Complex.ofReal_cos, Complex.ofReal_sin, mul_comm I, Complex.exp_mul_I]
  · simp [dR, Matrix.diagonal_apply_ne _ h]

theorem dR_cos_sub_sin (θ : Fin n → ℝ) :
    (dR fun j => Real.cos (θ j)) - I • (dR fun j => Real.sin (θ j)) = diagonal fun j => cexp (-(I * (θ j : ℂ))) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [dR, Matrix.diagonal_apply_eq, Complex.ofReal_cos, Complex.ofReal_sin, ← neg_mul, mul_comm I,
      Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  · simp [dR, Matrix.diagonal_apply_ne _ h]

theorem uni_I (A B : Matrix (Fin n) (Fin n) ℂ) (e11 : Aᴴ * A + Bᴴ * B = 1) (e12 : Aᴴ * B + -(Bᴴ * A) = 0) :
    (A + I • B)ᴴ * (A + I • B) = 1 := by
  have hs : star (I : ℂ) = -I := by rw [Complex.star_def, Complex.conj_I]
  simp only [conjTranspose_add, conjTranspose_smul, hs, add_mul, mul_add, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  rw [← e11, ← sub_eq_zero]
  have hI : I * (-I) = (1 : ℂ) := by rw [mul_neg, Complex.I_mul_I, neg_neg]
  have h2 : Aᴴ * B = Bᴴ * A := by rw [← sub_eq_zero, sub_eq_add_neg]; exact e12
  rw [hI, one_smul, h2, neg_smul]
  abel

theorem uni_mI (A B : Matrix (Fin n) (Fin n) ℂ) (e11 : Aᴴ * A + Bᴴ * B = 1) (e12 : Aᴴ * B + -(Bᴴ * A) = 0) :
    (A - I • B)ᴴ * (A - I • B) = 1 := by
  have hs : star (I : ℂ) = -I := by rw [Complex.star_def, Complex.conj_I]
  simp only [conjTranspose_sub, conjTranspose_smul, hs, sub_mul, mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  rw [← e11, ← sub_eq_zero]
  have hI : I * (-I) = (1 : ℂ) := by rw [mul_neg, Complex.I_mul_I, neg_neg]
  have h2 : Aᴴ * B = Bᴴ * A := by rw [← sub_eq_zero, sub_eq_add_neg]; exact e12
  rw [hI, one_smul, h2, neg_smul]
  abel

theorem kak (k : M2 n) (hk : InK k) :
    ∃ (u u' : Matrix (Fin n) (Fin n) ℂ) (θ : Fin n → ℝ), uᴴ * u = 1 ∧ u'ᴴ * u' = 1 ∧
      (∀ j, -(Real.pi / 2) < θ j ∧ θ j ≤ Real.pi / 2) ∧ k = mM u * kth θ * mM u' := by
  obtain ⟨h21, h22⟩ := inK_blocks k hk
  have hU : kᴴ * k = 1 := hk.2
  set A := k.toBlocks₁₁ with hA0
  set B := k.toBlocks₁₂ with hB0
  have hkA : k = fromBlocks A B (-B) A := by
    conv_lhs => rw [← fromBlocks_toBlocks k]
    rw [h21, h22]
  have hE : Aᴴ * A + Bᴴ * B = 1 ∧ Aᴴ * B + -(Bᴴ * A) = 0 := by
    rw [hkA, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at hU
    obtain ⟨h1, h2, -, -⟩ := hU
    refine ⟨?_, ?_⟩
    · simpa [conjTranspose_neg] using h1
    · simpa [conjTranspose_neg] using h2
  set W := A + I • B with hW0
  set V := A - I • B with hV0
  have hW : Wᴴ * W = 1 := uni_I A B hE.1 hE.2
  have hV : Vᴴ * V = 1 := uni_mI A B hE.1 hE.2
  have hV' : V * Vᴴ = 1 := mul_eq_one_comm.mp hV
  have hX : (W * Vᴴ)ᴴ * (W * Vᴴ) = 1 := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ, hW,
      Matrix.one_mul, hV']
  obtain ⟨P, w, hP, hP', hw, hXd⟩ := VacU.unitary_diag (W * Vᴴ) hX
  set θ : Fin n → ℝ := fun j => Complex.arg (w j) / 2 with hθ
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => cexp (I * (θ j : ℂ)) with hD
  set Db : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => cexp (-(I * (θ j : ℂ))) with hDb
  have hDDb : D * Db = 1 := by
    rw [hD, hDb, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext j
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hDbH : Dbᴴ = D := by
    rw [hD, hDb, diagonal_conjTranspose]
    congr 1; funext j
    simp only [Pi.star_apply]
    rw [Complex.star_def, ← Complex.exp_conj, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal,
      neg_mul, neg_neg]
  have hDb2 : Db * Db = (diagonal w)ᴴ := by
    rw [hDb, diagonal_mul_diagonal, diagonal_conjTranspose]
    congr 1; funext j
    simp only [Pi.star_apply]
    have hwj : w j = cexp (↑(Complex.arg (w j)) * I) := by
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (w j)]
      rw [hw j, Complex.ofReal_one, one_mul]
    rw [← Complex.exp_add]
    conv_rhs => rw [hwj]
    rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
    congr 1
    simp only [hθ]
    push_cast
    ring
  set u' := Db * Pᴴ * W with hu0
  have hu' : u'ᴴ * u' = 1 := by
    rw [hu0, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hDbH]
    calc Wᴴ * (P * D) * (Db * Pᴴ * W) = Wᴴ * (P * (D * Db) * Pᴴ) * W := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hDDb, Matrix.mul_one, hP', Matrix.mul_one, hW]
  have hPD : P * D * u' = W := by
    calc P * D * u' = P * (D * Db) * Pᴴ * W := by simp only [hu0, Matrix.mul_assoc]
      _ = W := by rw [hDDb, Matrix.mul_one, hP', Matrix.one_mul]
  have hPDb : P * Db * u' = V := by
    calc P * Db * u' = (P * (Db * Db) * Pᴴ) * W := by simp only [hu0, Matrix.mul_assoc]
      _ = (W * Vᴴ)ᴴ * W := by
          rw [hDb2, hXd, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
            Matrix.mul_assoc]
          simp only [Matrix.mul_assoc]
      _ = V := by
          rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, hW, Matrix.mul_one]
  have hCS := dR_cos_add_sin θ
  have hCSm := dR_cos_sub_sin θ
  rw [← hD] at hCS
  rw [← hDb] at hCSm
  set C := dR fun j => Real.cos (θ j) with hC0
  set S := dR fun j => Real.sin (θ j) with hS0
  have e1 : P * C * u' + I • (P * S * u') = W := by
    rw [← hPD, ← hCS, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  have e2 : P * C * u' - I • (P * S * u') = V := by
    rw [← hPDb, ← hCSm, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hXA : P * C * u' = A := by
    have h := congrArg₂ (· + ·) e1 e2
    simp only [hW0, hV0] at h
    have h2 : (2 : ℂ) • (P * C * u') = (2 : ℂ) • A := by
      rw [two_smul, two_smul]
      convert h using 1 <;> abel
    exact smul_right_injective _ two_ne_zero h2
  have hYB : P * S * u' = B := by
    have h := congrArg₂ (· - ·) e1 e2
    simp only [hW0, hV0] at h
    have h2 : (2 * I) • (P * S * u') = (2 * I) • B := by
      rw [mul_smul, mul_smul, two_smul, two_smul]
      convert h using 1 <;> abel
    exact smul_right_injective _ (mul_ne_zero two_ne_zero Complex.I_ne_zero) h2
  refine ⟨P, u', θ, hP, hu', fun j => ⟨?_, ?_⟩, ?_⟩
  · have := Complex.neg_pi_lt_arg (w j)
    simp only [hθ]
    linarith
  · have := Complex.arg_le_pi (w j)
    simp only [hθ]
    linarith
  · refine hkA.trans ?_
    rw [mM_unitary P hP, mM_unitary u' hu', kth_eq, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul]
    rw [← hC0, ← hS0]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_zero, add_zero, hXA, hYB]

end PositivityTheory.Rg.Sw.Glob.VacG
