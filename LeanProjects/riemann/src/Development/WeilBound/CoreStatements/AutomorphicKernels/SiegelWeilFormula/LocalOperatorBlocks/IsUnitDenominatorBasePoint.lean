import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.UnitDetOfUnitary

noncomputable section

open scoped Matrix
open MeasureTheory PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.KLI

variable {m n : ℕ}

open Complex

theorem herm_diag {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℝ), Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      Uᴴ * b * U = Matrix.diagonal fun j => (l j : ℂ) := by
  have hA : b.IsHermitian := hb
  refine ⟨(hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ), hA.eigenvalues, ?_, ?_, ?_⟩
  · rw [← Matrix.star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  · rw [← Matrix.star_eq_conjTranspose]; exact Unitary.coe_mul_star_self _
  · have := hA.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at this
    rw [← Matrix.star_eq_conjTranspose, this]
    rfl

theorem isUnit_denominator_base_point (sg : ℤˣ) (g : GR n) : IsUnit ((mR g).toBlocks₂₁ * Z0 sg + (mR g).toBlocks₂₂).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hG : InG (mR g) := g.2
  have key := inG_dot hG ((Z0 sg *ᵥ x) ⊕ᵥ x)
  have hMv : mR g *ᵥ ((Z0 sg *ᵥ x) ⊕ᵥ x) =
      ((mR g).toBlocks₁₁ *ᵥ (Z0 sg *ᵥ x) + (mR g).toBlocks₁₂ *ᵥ x) ⊕ᵥ 0 := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (mR g)]
    rw [← hx]
    simp only [Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.add_mulVec,
      Matrix.mulVec_mulVec]
  have hZx : Z0 sg *ᵥ x = (I * ((sg : ℤ) : ℂ)) • x := by
    rw [Z0, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hMv, dot_JJ, dot_JJ, hZx] at key
  simp at key
  have hs : star x ⬝ᵥ x ≠ 0 := by
    open scoped ComplexOrder in
    exact fun h0 => hx0 (dotProduct_star_self_eq_zero.mp h0)
  have hc : I * ((sg : ℤ) : ℂ) ≠ 0 :=
    mul_ne_zero I_ne_zero (Int.cast_ne_zero.mpr (Units.ne_zero sg))
  have hcs : I * ((sg : ℤ) : ℂ) * (star x ⬝ᵥ x) = 0 := by
    linear_combination key / 2
  exact mul_ne_zero hc hs hcs

theorem mobius_mul_base_point (sg : ℤˣ) (g h : GR n) : mob (mR (g * h)) (Z0 sg) = mob (mR g) (mob (mR h) (Z0 sg)) := by
  rw [mR_mul]; exact mob_mul _ _ _ (isUnit_denominator_base_point sg h)

theorem k_poly {sg : ℤˣ} {L : LOp m n} (h : LocHyp sg L) (k : GR n) (hk : InK (mR k)) (P : PX m n) :
    ∃ Q : PX m n, Q.totalDegree ≤ P.totalDegree ∧ L k (fP P) = fP Q := by
  obtain ⟨a, b, b', t, ha, hb, hb', hk'⟩ := all_eq k
  have hsw := isSw_fP P
  have h0 : IsPG sg P.totalDegree (Z0 sg) (fP P) := ⟨P, le_rfl, fP_eq_gZ sg P⟩
  have hT : ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ = (t : ℂ) • 1 := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  have hm1 : IsUnit (-1 : Matrix (Fin n) (Fin n) ℂ).det := isUnit_neg_one_det
  have hsq : ((sg : ℤ) : ℝ) * ((sg : ℤ) : ℝ) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  set w : ℂ := I * ((sg : ℤ) : ℂ) + t with hw
  have hwim : 0 < ((sg : ℤ) : ℝ) * w.im := by
    simp [hw, hsq]
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_im, mul_zero] at hwim
    exact lt_irrefl _ hwim
  set ω : ℂ := (-w)⁻¹ with hω
  have hωim : 0 < ((sg : ℤ) : ℝ) * ω.im := by
    have := im_neg_inv hwim
    rwa [neg_inv] at this
  have h1 := pg_nG h hT hsw h0
  have h2 := pg_mG h hm1 (h.sw _ _ hsw) h1
  have e2 : mob (mR (mG (-1 : Matrix (Fin n) (Fin n) ℂ))) (mob (mR (nG ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))))
      (Z0 sg)) = Matrix.diagonal fun _ : Fin n => w := by
    rw [mR_mG hm1, mR_nG hT, mob_nU, mob_mLc _ _ hm1]
    simp only [Matrix.conjTranspose_neg, Matrix.conjTranspose_one, neg_mul, one_mul, mul_neg, mul_one,
      neg_neg, Z0, hw, ← Matrix.smul_one_eq_diagonal, add_smul]
  rw [e2] at h2
  have h3 := pg_jG_diag h (fun _ => hwim) (h.sw _ _ (h.sw _ _ hsw)) h2
  rw [← e2] at h3
  have e3 : mob (mR (jG n)) (mob (mR (mG (-1 : Matrix (Fin n) (Fin n) ℂ)))
      (mob (mR (nG ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)))) (Z0 sg))) =
      Matrix.diagonal fun _ : Fin n => ω := by
    rw [e2, mR_jG, mob_JJ_diag _ (fun _ => hw0)]
  have h4 := pg_nG h hb' (h.sw _ _ (h.sw _ _ (h.sw _ _ hsw))) h3
  obtain ⟨U, l, hU1, hU2, hUb⟩ := herm_diag hb'
  have eU : Uᴴ * mob (mR (nG b')) (mob (mR (jG n)) (mob (mR (mG (-1 : Matrix (Fin n) (Fin n) ℂ)))
      (mob (mR (nG ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)))) (Z0 sg)))) * U =
      Matrix.diagonal fun j => ω + l j := by
    rw [mR_nG hb', mob_nU, e3, Matrix.mul_add, Matrix.add_mul, hUb, ← Matrix.smul_one_eq_diagonal,
      Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU1, Matrix.smul_one_eq_diagonal,
      Matrix.diagonal_add]
  have hz5 : ∀ j, 0 < ((sg : ℤ) : ℝ) * (ω + l j).im := by
    intro j
    simpa using hωim
  have h5 := pg_jG h hU1 hU2 eU hz5 (h.sw _ _ (h.sw _ _ (h.sw _ _ (h.sw _ _ hsw)))) h4
  have h6 := pg_nG h hb (h.sw _ _ (h.sw _ _ (h.sw _ _ (h.sw _ _ (h.sw _ _ hsw))))) h5
  have h7 := pg_mG h ha (h.sw _ _ (h.sw _ _ (h.sw _ _ (h.sw _ _ (h.sw _ _ (h.sw _ _ hsw)))))) h6
  have hL : L k (fP P) = L (mG a) (L (nG b) (L (jG n) (L (nG b') (L (jG n) (L (mG (-1))
      (L (nG ((t : ℂ) • 1)) (fP P))))))) := by
    rw [hk']
    simp only [mul_assoc]
    rw [h.mul _ _ _ hsw, h.mul _ _ _ hsw, h.mul _ _ _ hsw, h.mul _ _ _ hsw, h.mul _ _ _ hsw,
      h.mul _ _ _ hsw]
  have hZ : mob (mR k) (Z0 sg) = mob (mR (mG a)) (mob (mR (nG b)) (mob (mR (jG n)) (mob (mR (nG b'))
      (mob (mR (jG n)) (mob (mR (mG (-1))) (mob (mR (nG ((t : ℂ) • 1))) (Z0 sg))))))) := by
    rw [hk']
    simp only [mul_assoc]
    rw [mobius_mul_base_point, mobius_mul_base_point, mobius_mul_base_point, mobius_mul_base_point, mobius_mul_base_point, mobius_mul_base_point]
  have hK := mob_K sg (mR k) hk (isUnit_denominator_base_point sg k)
  rw [hZ] at hK
  rw [hK, ← hL] at h7
  obtain ⟨Q, hQ, hfeq⟩ := h7
  exact ⟨Q, hQ, by rw [hfeq, fP_eq_gZ sg Q]⟩

end PositivityTheory.SiegelWeilFormula.KLI

end
