import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocInstSt

noncomputable section

open Matrix Filter Topology
open scoped ComplexConjugate ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob.Vac

variable {n : ℕ}

theorem mR_mul (g h : GR n) : mR (g * h) = mR g * mR h := rfl

theorem mR_one : mR (1 : GR n) = 1 := rfl

theorem inG_mR (g : GR n) : InG (mR g) := g.2

theorem neg_one_blocks : (-1 : M2 n) = fromBlocks (-1) 0 0 (-1) := by
  rw [← fromBlocks_one, fromBlocks_neg, neg_zero]

theorem JJ_sq : JJ n * JJ n = -1 := by
  rw [neg_one_blocks]; simp [JJ, fromBlocks_multiply]

theorem JJ_conjTranspose : (JJ n)ᴴ = -JJ n := by
  simp [JJ, fromBlocks_conjTranspose, fromBlocks_neg]

theorem flip_of_inG {M : M2 n} (h : InG M) : M * JJ n * Mᴴ = JJ n := by
  have h' : Mᴴ * JJ n * M = JJ n := h
  have h1 : (Mᴴ * JJ n) * (-(M * JJ n)) = 1 := by
    rw [mul_neg, ← mul_assoc, h', JJ_sq, neg_neg]
  have h2 := mul_eq_one_comm.mp h1
  have h3 : M * JJ n * (Mᴴ * JJ n) = -1 := by
    rw [neg_mul] at h2
    exact neg_eq_iff_eq_neg.mp h2
  calc M * JJ n * Mᴴ = -(M * JJ n * (Mᴴ * JJ n) * JJ n) := by
        simp only [mul_assoc, JJ_sq, mul_neg, mul_one, neg_neg]
    _ = JJ n := by rw [h3]; simp

theorem lagr (g : GR n) :
    (mR g).toBlocks₂₁ * ((mR g).toBlocks₂₂)ᴴ = (mR g).toBlocks₂₂ * ((mR g).toBlocks₂₁)ᴴ := by
  have h := flip_of_inG (inG_mR g)
  have h22 := congrArg Matrix.toBlocks₂₂ h
  rw [← Matrix.fromBlocks_toBlocks (mR g)] at h22
  simp only [JJ, fromBlocks_multiply, fromBlocks_conjTranspose, toBlocks_fromBlocks₂₂, mul_zero, zero_add,
    add_zero, mul_one, mul_neg, neg_mul] at h22
  exact (neg_add_eq_zero.mp h22).symm

theorem vec_zero (g : GR n) (z : ℂ) (hz : z.im ≠ 0) (v : Fin n → ℂ)
    (hv : v ᵥ* (z • (mR g).toBlocks₂₁ + (mR g).toBlocks₂₂) = 0) : v = 0 := by
  have hl := lagr g
  rw [Matrix.vecMul_add, Matrix.vecMul_smul] at hv
  have hW : v ᵥ* (mR g).toBlocks₂₂ = -(z • (v ᵥ* (mR g).toBlocks₂₁)) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hv
  have key : ∀ A B : Matrix (Fin n) (Fin n) ℂ, (v ᵥ* A) ⬝ᵥ star (v ᵥ* B) = (v ᵥ* (A * Bᴴ)) ⬝ᵥ star v := by
    intro A B
    rw [Matrix.star_vecMul, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  have hsym : (v ᵥ* (mR g).toBlocks₂₁) ⬝ᵥ star (v ᵥ* (mR g).toBlocks₂₂) =
      (v ᵥ* (mR g).toBlocks₂₂) ⬝ᵥ star (v ᵥ* (mR g).toBlocks₂₁) := by
    rw [key, key, hl]
  rw [hW] at hsym
  simp only [star_neg, star_smul, dotProduct_neg, neg_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul] at hsym
  have hz' : z - star z ≠ 0 := by
    intro h0
    apply hz
    have := congrArg Complex.im h0
    simp at this
    linarith
  have hY0 : (v ᵥ* (mR g).toBlocks₂₁) ⬝ᵥ star (v ᵥ* (mR g).toBlocks₂₁) = 0 := by
    have : (z - star z) * ((v ᵥ* (mR g).toBlocks₂₁) ⬝ᵥ star (v ᵥ* (mR g).toBlocks₂₁)) = 0 := by
      linear_combination hsym
    exact (mul_eq_zero.mp this).resolve_left hz'
  have hY : v ᵥ* (mR g).toBlocks₂₁ = 0 := dotProduct_self_star_eq_zero.mp hY0
  have hD : v ᵥ* (mR g).toBlocks₂₂ = 0 := by
    rw [hW, hY, smul_zero, neg_zero]
  have hu : (Sum.elim 0 v : Fin n ⊕ Fin n → ℂ) ᵥ* mR g = 0 := by
    ext j
    cases j with
    | inl k =>
      have := congrFun hY k
      simpa [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, toBlocks₂₁] using this
    | inr k =>
      have := congrFun hD k
      simpa [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, toBlocks₂₂] using this
  have hinv : mR g * ((g : GL (Fin n ⊕ Fin n) ℂ)⁻¹ : GL (Fin n ⊕ Fin n) ℂ).val = 1 := by
    simp [mR]
  have hu0 : (Sum.elim 0 v : Fin n ⊕ Fin n → ℂ) = 0 := by
    have := congrArg (fun w => w ᵥ* ((g : GL (Fin n ⊕ Fin n) ℂ)⁻¹ : GL (Fin n ⊕ Fin n) ℂ).val) hu
    simp only [Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one, Matrix.zero_vecMul] at this
    exact this
  ext i
  simpa using congrFun hu0 (Sum.inr i)

theorem automorphy_first_det_ne_zero (g : GR n) : (u1 (mR g)).det ≠ 0 := by
  intro h
  obtain ⟨v, hv0, hv⟩ := (exists_vecMul_eq_zero_iff).mpr h
  exact hv0 (vec_zero g Complex.I (by simp) v (by simpa [u1] using hv))

theorem automorphy_second_det_ne_zero (g : GR n) : (u2 (mR g)).det ≠ 0 := by
  intro h
  obtain ⟨v, hv0, hv⟩ := (exists_vecMul_eq_zero_iff).mpr h
  exact hv0 (vec_zero g (-Complex.I) (by simp) v (by simpa [u2, neg_smul] using hv))

theorem det_ne (g : GR n) : (mR g).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp g.1.isUnit).ne_zero

theorem cont_mR : Continuous (mR : GR n → M2 n) := Units.continuous_val.comp continuous_subtype_val

theorem continuous_vacuum_lower_left_block : Continuous (fun g : GR n => (mR g).toBlocks₂₁) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (continuous_apply (Sum.inl j)).comp ((continuous_apply (Sum.inr i)).comp cont_mR)

theorem continuous_vacuum_lower_right_block : Continuous (fun g : GR n => (mR g).toBlocks₂₂) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (continuous_apply (Sum.inr j)).comp ((continuous_apply (Sum.inr i)).comp cont_mR)

theorem continuous_vacuum_section (p q : ℕ) (e : ℤ) : Continuous (F0 (n := n) p q e) := by
  have hdet : Continuous fun g : GR n => (mR g).det := cont_mR.matrix_det
  have h1 : Continuous fun g : GR n => (u1 (mR g)).det := by
    refine Continuous.matrix_det ?_
    unfold u1; exact (continuous_vacuum_lower_left_block.const_smul Complex.I).add continuous_vacuum_lower_right_block
  have h2 : Continuous fun g : GR n => (u2 (mR g)).det := by
    refine Continuous.matrix_det ?_
    unfold u2; exact (continuous_vacuum_lower_left_block.const_smul Complex.I).neg.add continuous_vacuum_lower_right_block
  have : F0 (n := n) p q e = fun g => (mR g).det ^ e * ((u1 (mR g)).det ^ (-(p : ℤ)) * (u2 (mR g)).det ^ (-(q : ℤ))) := rfl
  rw [this]
  exact (hdet.zpow₀ e fun g => Or.inl (det_ne g)).mul
    ((h1.zpow₀ _ fun g => Or.inl (automorphy_first_det_ne_zero g)).mul (h2.zpow₀ _ fun g => Or.inl (automorphy_second_det_ne_zero g)))

theorem lower_left_block_mul {Y G : M2 n} (hY : Y.toBlocks₂₁ = 0) : (Y * G).toBlocks₂₁ = Y.toBlocks₂₂ * G.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks Y, ← fromBlocks_toBlocks G]
  rw [fromBlocks_multiply, toBlocks_fromBlocks₂₁, hY, zero_mul, zero_add]

theorem lower_right_block_mul {Y G : M2 n} (hY : Y.toBlocks₂₁ = 0) : (Y * G).toBlocks₂₂ = Y.toBlocks₂₂ * G.toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks Y, ← fromBlocks_toBlocks G]
  rw [fromBlocks_multiply, toBlocks_fromBlocks₂₂, hY, zero_mul, zero_add]

theorem vacuum_section_mul_parabolic (p q : ℕ) (e : ℤ) (y g : GR n) (hy : (mR y).toBlocks₂₁ = 0) :
    F0 p q e (y * g) = F0 p q e y * F0 p q e g := by
  have e1 : u1 (mR y * mR g) = (mR y).toBlocks₂₂ * u1 (mR g) := by
    simp only [u1, lower_left_block_mul hy, lower_right_block_mul hy, Matrix.mul_add, Matrix.mul_smul]
  have e2 : u2 (mR y * mR g) = (mR y).toBlocks₂₂ * u2 (mR g) := by
    simp only [u2, lower_left_block_mul hy, lower_right_block_mul hy, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_neg]
  have e1' : u1 (mR y) = (mR y).toBlocks₂₂ := by
    simp [u1, hy]
  have e2' : u2 (mR y) = (mR y).toBlocks₂₂ := by
    simp [u2, hy]
  simp only [F0, f0, mR_mul, e1, e2, e1', e2', det_mul, mul_zpow]
  ring

theorem weight_factor_one (p q : ℕ) (e : ℤ) : F0 p q e (1 : GR n) = 1 := by
  have h21 : (1 : M2 n).toBlocks₂₁ = 0 := by rw [← fromBlocks_one, toBlocks_fromBlocks₂₁]
  have h22 : (1 : M2 n).toBlocks₂₂ = 1 := by rw [← fromBlocks_one, toBlocks_fromBlocks₂₂]
  simp [F0, f0, u1, u2, mR_one, h21, h22]

theorem JJ_nU (b : Matrix (Fin n) (Fin n) ℂ) : JJ n * nU b = fromBlocks 0 1 (-1) (-b) := by
  simp [JJ, nU, fromBlocks_multiply]

theorem det_JJ : (JJ n).det = 1 := by
  have : JJ n = fromBlocks 1 0 (-1) 1 * fromBlocks 1 1 0 1 * fromBlocks 1 0 (-1) 1 := by
    simp [JJ, fromBlocks_multiply]
  rw [this, det_mul, det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁]
  simp

theorem det_nU (b : Matrix (Fin n) (Fin n) ℂ) : (nU b).det = 1 := by
  rw [nU, det_fromBlocks_zero₂₁]; simp

theorem vacuum_section_big_cell (p q : ℕ) (e : ℤ) (h : GR n) (b : Matrix (Fin n) (Fin n) ℂ) (hh : mR h = JJ n * nU b) :
    F0 p q e h = ((-Complex.I) ^ n * (1 - Complex.I • b).det) ^ (-(p : ℤ)) *
      (Complex.I ^ n * (1 + Complex.I • b).det) ^ (-(q : ℤ)) := by
  have e1 : u1 (JJ n * nU b) = (-Complex.I) • (1 - Complex.I • b) := by
    rw [JJ_nU]
    ext i j
    simp [u1, Matrix.one_apply]
    split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  have e2 : u2 (JJ n * nU b) = Complex.I • (1 + Complex.I • b) := by
    rw [JJ_nU]
    ext i j
    simp [u2, Matrix.one_apply]
    split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  simp only [F0, f0, hh, det_mul, det_JJ, det_nU, one_mul, _root_.one_zpow, e1, e2, det_smul,
    Fintype.card_fin]

end PositivityTheory.Rg.Sw.Glob.Vac
