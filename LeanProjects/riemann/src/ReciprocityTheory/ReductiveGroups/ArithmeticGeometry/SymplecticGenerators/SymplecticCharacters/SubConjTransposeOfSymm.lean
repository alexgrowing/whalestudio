import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.Blocks

noncomputable section

open Complex Matrix ReciprocityTheory.PTheta

namespace ReciprocityTheory.ChartRestriction.G.Key.Chi

def imC {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  (τ.map Complex.im).map (fun x : ℝ => (x : ℂ))

theorem sub_conjTranspose_of_symm {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ.IsSymm) :
    τ - τᴴ = (2 * I) • imC τ := by
  ext i j
  have h : τ j i = τ i j := by simpa using congrFun (congrFun hτ i) j
  simp only [Matrix.sub_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, imC, Matrix.map_apply, h,
    smul_eq_mul]
  apply Complex.ext <;> simp <;> ring

theorem re_pos_of_posDef {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} (hY : Y.PosDef) {v : Fin g → ℂ}
    (hv : v ≠ 0) : 0 < (star v ⬝ᵥ (Y.map (fun x : ℝ => (x : ℂ)) *ᵥ v)).re := by
  set x : Fin g → ℝ := fun i => (v i).re with hxdef
  set y : Fin g → ℝ := fun i => (v i).im with hydef
  have key : (star v ⬝ᵥ (Y.map (fun x : ℝ => (x : ℂ)) *ᵥ v)).re = x ⬝ᵥ (Y *ᵥ x) + y ⬝ᵥ (Y *ᵥ y) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, Complex.re_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, hxdef, hydef]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.mul_re, Complex.mul_im]
  have hnn : ∀ z : Fin g → ℝ, 0 ≤ z ⬝ᵥ (Y *ᵥ z) := by
    intro z
    by_cases hz : z = 0
    · simp [hz]
    · have := hY.dotProduct_mulVec_pos hz
      simp only [star_trivial] at this
      exact this.le
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hv
    funext i
    apply Complex.ext
    · exact congrFun hc.1 i
    · exact congrFun hc.2 i
  rw [key]
  rcases hxy with h | h
  · have := hY.dotProduct_mulVec_pos h
    simp only [star_trivial] at this
    linarith [hnn y]
  · have := hY.dotProduct_mulVec_pos h
    simp only [star_trivial] at this
    linarith [hnn x]

theorem blk_conjTranspose₂₁ {g : ℕ} (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) :
    ((cMat γ).toBlocks₂₁)ᴴ = ((cMat γ).toBlocks₂₁)ᵀ := by
  ext i j
  simp [Matrix.conjTranspose_apply, cMat, Matrix.toBlocks₂₁]

theorem blk_conjTranspose₂₂ {g : ℕ} (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) :
    ((cMat γ).toBlocks₂₂)ᴴ = ((cMat γ).toBlocks₂₂)ᵀ := by
  ext i j
  simp [Matrix.conjTranspose_apply, cMat, Matrix.toBlocks₂₂]

theorem blk_conjTranspose₁₁ {g : ℕ} (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) :
    ((cMat γ).toBlocks₁₁)ᴴ = ((cMat γ).toBlocks₁₁)ᵀ := by
  ext i j
  simp [Matrix.conjTranspose_apply, cMat, Matrix.toBlocks₁₁]

theorem blk_conjTranspose₁₂ {g : ℕ} (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) :
    ((cMat γ).toBlocks₁₂)ᴴ = ((cMat γ).toBlocks₁₂)ᵀ := by
  ext i j
  simp [Matrix.conjTranspose_apply, cMat, Matrix.toBlocks₁₂]

theorem sp_keyH {g : ℕ} {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hγ : γ ∈ Matrix.symplecticGroup (Fin g) ℤ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    (jAut γ τ)ᴴ * nAut γ τ - (nAut γ τ)ᴴ * jAut γ τ = τ - τᴴ := by
  have h1 := SymplecticGroup.mem_iff'.mp hγ
  have h3 : (cMat γ)ᵀ * Matrix.J (Fin g) ℂ * cMat γ = Matrix.J (Fin g) ℂ := by
    have hJ : (Matrix.J (Fin g) ℤ).map (Int.castRingHom ℂ) = Matrix.J (Fin g) ℂ := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.J, Matrix.one_apply]
      all_goals (try split_ifs)
      all_goals (try simp_all)
    have := congrArg (fun M => M.map (Int.castRingHom ℂ)) h1
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hJ] at this
    exact this
  rw [← Matrix.fromBlocks_toBlocks (cMat γ), Matrix.J, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at h3
  obtain ⟨e11, e12, e21, e22⟩ := Matrix.fromBlocks_inj.mp h3
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, Matrix.zero_mul,
    Matrix.neg_mul, Matrix.one_mul] at e11 e12 e21 e22
  have hA := blk_conjTranspose₁₁ γ
  have hB := blk_conjTranspose₁₂ γ
  have hC := blk_conjTranspose₂₁ γ
  have hD := blk_conjTranspose₂₂ γ
  simp only [jAut, nAut]
  generalize (cMat γ).toBlocks₁₁ = A at e11 e12 e21 e22 hA hB hC hD ⊢
  generalize (cMat γ).toBlocks₁₂ = B at e11 e12 e21 e22 hA hB hC hD ⊢
  generalize (cMat γ).toBlocks₂₁ = C at e11 e12 e21 e22 hA hB hC hD ⊢
  generalize (cMat γ).toBlocks₂₂ = D at e11 e12 e21 e22 hA hB hC hD ⊢
  have e : (C * τ + D)ᴴ * (A * τ + B) - (A * τ + B)ᴴ * (C * τ + D) =
      τᴴ * (Cᵀ * A + -(Aᵀ * C)) * τ + τᴴ * (Cᵀ * B + -(Aᵀ * D) + 1) + (Dᵀ * A + -(Bᵀ * C) - 1) * τ +
        (Dᵀ * B + -(Bᵀ * D)) + (τ - τᴴ) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hA, hB, hC, hD]
    noncomm_ring
  rw [e, e11, e12, e21, e22]
  noncomm_ring

theorem sp_keyT {g : ℕ} {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hγ : γ ∈ Matrix.symplecticGroup (Fin g) ℤ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    (jAut γ τ)ᵀ * nAut γ τ - (nAut γ τ)ᵀ * jAut γ τ = τ - τᵀ := by
  have h1 := SymplecticGroup.mem_iff'.mp hγ
  have h3 : (cMat γ)ᵀ * Matrix.J (Fin g) ℂ * cMat γ = Matrix.J (Fin g) ℂ := by
    have hJ : (Matrix.J (Fin g) ℤ).map (Int.castRingHom ℂ) = Matrix.J (Fin g) ℂ := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.J, Matrix.one_apply]
      all_goals (try split_ifs)
      all_goals (try simp_all)
    have := congrArg (fun M => M.map (Int.castRingHom ℂ)) h1
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hJ] at this
    exact this
  rw [← Matrix.fromBlocks_toBlocks (cMat γ), Matrix.J, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at h3
  obtain ⟨e11, e12, e21, e22⟩ := Matrix.fromBlocks_inj.mp h3
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, Matrix.zero_mul,
    Matrix.neg_mul, Matrix.one_mul] at e11 e12 e21 e22
  set A := (cMat γ).toBlocks₁₁
  set B := (cMat γ).toBlocks₁₂
  set C := (cMat γ).toBlocks₂₁
  set D := (cMat γ).toBlocks₂₂
  have e : (jAut γ τ)ᵀ * nAut γ τ - (nAut γ τ)ᵀ * jAut γ τ =
      τᵀ * (Cᵀ * A + -(Aᵀ * C)) * τ + τᵀ * (Cᵀ * B + -(Aᵀ * D) + 1) + (Dᵀ * A + -(Bᵀ * C) - 1) * τ +
        (Dᵀ * B + -(Bᵀ * D)) + (τ - τᵀ) := by
    simp only [jAut, nAut, Matrix.transpose_add, Matrix.transpose_mul]
    noncomm_ring
  rw [e, e11, e12, e21, e22]
  noncomm_ring

theorem jAut_isUnit {g : ℕ} {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hγ : γ ∈ Matrix.symplecticGroup (Fin g) ℤ) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ SiegelH (Fin g)) : IsUnit (jAut γ τ).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hJv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hpos := re_pos_of_posDef hτ.2 hv
  have h0 : star v ⬝ᵥ (((jAut γ τ)ᴴ * nAut γ τ - (nAut γ τ)ᴴ * jAut γ τ) *ᵥ v) = 0 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hJv,
      Matrix.mulVec_zero, dotProduct_zero, sub_zero, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, hJv,
      star_zero, zero_dotProduct]
  rw [sp_keyH hγ τ, sub_conjTranspose_of_symm hτ.1, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    mul_eq_zero] at h0
  rcases h0 with h | h
  · simp at h
  · rw [show (τ.map Complex.im).map (fun x : ℝ => (x : ℂ)) = imC τ from rfl, h] at hpos
    simp at hpos

theorem spAct_isSymm {g : ℕ} {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hγ : γ ∈ Matrix.symplecticGroup (Fin g) ℤ) {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ.IsSymm)
    (hj : IsUnit (jAut γ τ).det) : (spAct γ τ).IsSymm := by
  show (nAut γ τ * (jAut γ τ)⁻¹)ᵀ = nAut γ τ * (jAut γ τ)⁻¹
  have hk := sp_keyT hγ τ
  rw [hτ.eq, sub_self, sub_eq_zero] at hk
  have hJt : IsUnit (jAut γ τ)ᵀ.det := by rwa [Matrix.det_transpose]
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
  calc ((jAut γ τ)ᵀ)⁻¹ * (nAut γ τ)ᵀ
      = ((jAut γ τ)ᵀ)⁻¹ * (nAut γ τ)ᵀ * (jAut γ τ * (jAut γ τ)⁻¹) := by
        rw [Matrix.mul_nonsing_inv _ hj, Matrix.mul_one]
    _ = ((jAut γ τ)ᵀ)⁻¹ * ((nAut γ τ)ᵀ * jAut γ τ) * (jAut γ τ)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = ((jAut γ τ)ᵀ)⁻¹ * ((jAut γ τ)ᵀ * nAut γ τ) * (jAut γ τ)⁻¹ := by rw [← hk]
    _ = nAut γ τ * (jAut γ τ)⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJt, Matrix.one_mul]

theorem real_quad {g : ℕ} (σ : Matrix (Fin g) (Fin g) ℂ) (x : Fin g → ℝ) :
    ((x ⬝ᵥ (σ.map Complex.im *ᵥ x) : ℝ) : ℂ) =
      star (fun i => (x i : ℂ)) ⬝ᵥ (imC σ *ᵥ fun i => (x i : ℂ)) := by
  simp only [dotProduct, Matrix.mulVec, imC, Matrix.map_apply, Pi.star_apply, Complex.star_def,
    Complex.conj_ofReal, Complex.ofReal_sum, Complex.ofReal_mul]

theorem spAct_mem {g : ℕ} {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hγ : γ ∈ Matrix.symplecticGroup (Fin g) ℤ) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ SiegelH (Fin g)) : spAct γ τ ∈ SiegelH (Fin g) := by
  have hj := jAut_isUnit hγ hτ
  have hs := spAct_isSymm hγ hτ.1 hj
  refine ⟨hs, ?_⟩
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    have h := congrFun (congrFun hs.eq i) j
    simp only [Matrix.transpose_apply] at h
    simp [Matrix.conjTranspose_apply, h]
  · intro x hx
    rw [star_trivial]
    have hJh : IsUnit (jAut γ τ)ᴴ.det := by rw [Matrix.det_conjTranspose]; exact hj.star
    have hk := sp_keyH hγ τ
    have e1 : spAct γ τ - (spAct γ τ)ᴴ = ((jAut γ τ)⁻¹)ᴴ * (τ - τᴴ) * (jAut γ τ)⁻¹ := by
      rw [← hk, show spAct γ τ = nAut γ τ * (jAut γ τ)⁻¹ from rfl, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_nonsing_inv, Matrix.mul_sub, Matrix.sub_mul]
      simp only [← Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul _ hJh, Matrix.one_mul]
      simp only [Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv _ hj, Matrix.mul_one]
    have e2 : imC (spAct γ τ) = ((jAut γ τ)⁻¹)ᴴ * imC τ * (jAut γ τ)⁻¹ := by
      have h2I : (2 * Complex.I) ≠ 0 := by simp
      apply smul_right_injective _ h2I
      show (2 * Complex.I) • imC (spAct γ τ) = (2 * Complex.I) • (((jAut γ τ)⁻¹)ᴴ * imC τ * (jAut γ τ)⁻¹)
      rw [← sub_conjTranspose_of_symm hs, e1, sub_conjTranspose_of_symm hτ.1, Matrix.mul_smul,
        Matrix.smul_mul]
    have hxc : (fun i => (x i : ℂ)) ≠ 0 := by
      intro h
      apply hx
      funext i
      have := congrFun h i
      simpa using this
    have hw : (jAut γ τ)⁻¹ *ᵥ (fun i => (x i : ℂ)) ≠ 0 := by
      intro h
      apply hxc
      have := congrArg (jAut γ τ *ᵥ ·) h
      simpa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hj] using this
    have hq := real_quad (spAct γ τ) x
    rw [e2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec (star fun i => (x i : ℂ)), ← Matrix.star_mulVec] at hq
    have hpos := re_pos_of_posDef hτ.2 hw
    have hre := congrArg Complex.re hq
    rw [Complex.ofReal_re] at hre
    rw [hre]
    exact hpos

theorem spAct_holds : SpActStatement := fun _ _ hγ _ hτ => ⟨jAut_isUnit hγ hτ, spAct_mem hγ hτ⟩

theorem sp_A {g : ℕ} {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hγ : γ ∈ Matrix.symplecticGroup (Fin g) ℤ) {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ.IsSymm)
    (hj : IsUnit (jAut γ τ).det) :
    (cMat γ).toBlocks₁₁ - spAct γ τ * (cMat γ).toBlocks₂₁ = ((jAut γ τ)⁻¹)ᵀ := by
  have hs := spAct_isSymm hγ hτ hj
  have hJt : IsUnit (jAut γ τ)ᵀ.det := by rwa [Matrix.det_transpose]
  have hσ : spAct γ τ = ((jAut γ τ)ᵀ)⁻¹ * (nAut γ τ)ᵀ := by
    rw [← hs.eq, show spAct γ τ = nAut γ τ * (jAut γ τ)⁻¹ from rfl, Matrix.transpose_mul,
      Matrix.transpose_nonsing_inv]
  have h1 := SymplecticGroup.mem_iff'.mp hγ
  have h3 : (cMat γ)ᵀ * Matrix.J (Fin g) ℂ * cMat γ = Matrix.J (Fin g) ℂ := by
    have hJ : (Matrix.J (Fin g) ℤ).map (Int.castRingHom ℂ) = Matrix.J (Fin g) ℂ := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.J, Matrix.one_apply]
      all_goals (try split_ifs)
      all_goals (try simp_all)
    have := congrArg (fun M => M.map (Int.castRingHom ℂ)) h1
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hJ] at this
    exact this
  rw [← Matrix.fromBlocks_toBlocks (cMat γ), Matrix.J, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at h3
  obtain ⟨e11, _, e21, _⟩ := Matrix.fromBlocks_inj.mp h3
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, Matrix.zero_mul,
    Matrix.neg_mul, Matrix.one_mul] at e11 e21
  have key : (jAut γ τ)ᵀ * ((cMat γ).toBlocks₁₁ - spAct γ τ * (cMat γ).toBlocks₂₁) = 1 := by
    rw [hσ, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJt,
      Matrix.one_mul]
    simp only [jAut, nAut]
    generalize (cMat γ).toBlocks₁₁ = A at e11 e21 ⊢
    generalize (cMat γ).toBlocks₁₂ = B at e11 e21 ⊢
    generalize (cMat γ).toBlocks₂₁ = C at e11 e21 ⊢
    generalize (cMat γ).toBlocks₂₂ = D at e11 e21 ⊢
    have e : (C * τ + D)ᵀ * A - (A * τ + B)ᵀ * C =
        τᵀ * (Cᵀ * A + -(Aᵀ * C)) + (Dᵀ * A + -(Bᵀ * C)) := by
      rw [Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul]
      noncomm_ring
    rw [e, e11, e21, Matrix.mul_zero, zero_add]
  rw [Matrix.transpose_nonsing_inv]
  calc (cMat γ).toBlocks₁₁ - spAct γ τ * (cMat γ).toBlocks₂₁
      = ((jAut γ τ)ᵀ)⁻¹ * ((jAut γ τ)ᵀ * ((cMat γ).toBlocks₁₁ - spAct γ τ * (cMat γ).toBlocks₂₁)) := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJt, Matrix.one_mul]
    _ = ((jAut γ τ)ᵀ)⁻¹ := by rw [key, Matrix.mul_one]

end ReciprocityTheory.ChartRestriction.G.Key.Chi
