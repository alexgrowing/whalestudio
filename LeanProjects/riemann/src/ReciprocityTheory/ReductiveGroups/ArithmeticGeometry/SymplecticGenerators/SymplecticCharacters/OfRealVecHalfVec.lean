import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.SubConjTransposeOfSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.GenBase

noncomputable section

open Complex Matrix ReciprocityTheory.PTheta

namespace ReciprocityTheory.ChartRestriction.G.Key.Chi

def ChiAtU (g : ℕ) (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) : Prop :=
  ∀ n n' : Fin g → ℤ, ∃ (k k' : Fin g → ℤ) (c : ℂ), c ^ 4 = 1 ∧
    ∀ τ ∈ SiegelH (Fin g), ∀ z : Fin g → ℂ,
      theta (halfVec k) (halfVec k') (zAct γ τ z) (spAct γ τ) ^ 2 =
        c * (jAut γ τ).det * eC (expArg γ τ z) * theta (halfVec n) (halfVec n') z τ ^ 2

theorem eC_pow (x : ℂ) (m : ℕ) : eC x ^ m = eC (m * x) := by
  unfold eC
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

theorem ofRealVec_halfVec {g : ℕ} (n : Fin g → ℤ) :
    ofRealVec (halfVec n) = (1 / 2 : ℂ) • ofIntVec n := by
  funext i
  simp only [ofRealVec, halfVec, ofIntVec, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem ofIntVec_dot {g : ℕ} (a b : Fin g → ℤ) : ofIntVec a ⬝ᵥ ofIntVec b = ((a ⬝ᵥ b : ℤ) : ℂ) := by
  simp only [dotProduct, ofIntVec, Int.cast_sum, Int.cast_mul]

theorem mulVec_halfVec {g : ℕ} (M : Matrix (Fin g) (Fin g) ℤ) (k : Fin g → ℤ) :
    M.map (fun x : ℤ => (x : ℝ)) *ᵥ halfVec k = halfVec (M *ᵥ k) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, halfVec, Matrix.map_apply]
  push_cast
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem theta_sq_red {g : ℕ} (k k' : Fin g → ℤ) (z : Fin g → ℂ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    theta (halfVec k) (halfVec k') z τ ^ 2 =
      theta (halfVec fun i => k i % 2) (halfVec fun i => k' i % 2) z τ ^ 2 := by
  have hsplit : ∀ m : Fin g → ℤ,
      halfVec m = halfVec (fun i => m i % 2) + fun i => ((m i / 2 : ℤ) : ℝ) := by
    intro m
    funext i
    have h0 : m i % 2 + 2 * (m i / 2) = m i := by omega
    have h : ((m i % 2 + 2 * (m i / 2) : ℤ) : ℝ) = (m i : ℝ) := by
      rw [h0]
    push_cast at h
    simp only [halfVec, Pi.add_apply]
    linarith
  have hE : ∀ a b : Fin g → ℤ, eC (ofRealVec (halfVec a) ⬝ᵥ ofIntVec b) ^ 2 = 1 := by
    intro a b
    rw [eC_pow, ofRealVec_halfVec, smul_dotProduct, ofIntVec_dot, smul_eq_mul]
    convert eC_int (a ⬝ᵥ b) using 2
    push_cast
    ring
  rw [hsplit k, hsplit k',
    thetaIntChar_holds (Fin g) _ _ (fun i => k i / 2) (fun i => k' i / 2), mul_pow, hE, one_mul]

theorem chiAt_of_U {g : ℕ} {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ} (h : ChiAtU g γ) :
    ChiAt g γ := by
  intro n n'
  obtain ⟨k, k', c, hc, h⟩ := h n n'
  refine ⟨fun i => k i % 2, fun i => k' i % 2, c, fun i => Int.emod_two_eq_zero_or_one _,
    fun i => Int.emod_two_eq_zero_or_one _, hc, ?_⟩
  intro τ hτ z
  rw [← theta_sq_red]
  exact h τ hτ z

theorem cMat_spTransl {g : ℕ} (S : Matrix (Fin g) (Fin g) ℤ) :
    cMat (spTransl S) = Matrix.fromBlocks 1 (S.map (fun x : ℤ => (x : ℂ))) 0 1 := by
  simp [cMat, spTransl, Matrix.fromBlocks_map]

theorem jAut_spTransl {g : ℕ} (S : Matrix (Fin g) (Fin g) ℤ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    jAut (spTransl S) τ = 1 := by
  simp [jAut, cMat_spTransl]

theorem spAct_spTransl {g : ℕ} (S : Matrix (Fin g) (Fin g) ℤ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    spAct (spTransl S) τ = τ + S.map (fun x : ℤ => (x : ℂ)) := by
  simp [spAct, jAut_spTransl, cMat_spTransl]

theorem chiU_spTransl {g : ℕ} (S : Matrix (Fin g) (Fin g) ℤ) (hS : S.IsSymm) :
    ChiAtU g (spTransl S) := by
  intro n n'
  have hA : ofRealVec (halfVec n) ⬝ᵥ (S.map (fun x : ℤ => (x : ℂ)) *ᵥ ofRealVec (halfVec n)) =
      ((n ⬝ᵥ (S *ᵥ n) : ℤ) : ℂ) / 4 := by
    rw [ofRealVec_halfVec, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
      ← ofIntVec_mulVec, ofIntVec_dot]
    simp only [smul_eq_mul]
    ring
  have hB : ofRealVec (halfVec n) ⬝ᵥ (fun i => ((S i i : ℤ) : ℂ) / 2) =
      ((n ⬝ᵥ (fun i => S i i) : ℤ) : ℂ) / 4 := by
    simp only [dotProduct, ofRealVec, halfVec, Int.cast_sum, Int.cast_mul]
    push_cast
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  refine ⟨n, n' - S *ᵥ n - (fun i => S i i),
    eC (-(ofRealVec (halfVec n) ⬝ᵥ (S.map (fun x : ℤ => (x : ℂ)) *ᵥ ofRealVec (halfVec n))) / 2 -
      ofRealVec (halfVec n) ⬝ᵥ (fun i => ((S i i : ℤ) : ℂ) / 2)) ^ 2, ?_, ?_⟩
  · rw [← pow_mul, eC_pow, hA, hB]
    convert eC_int (-(n ⬝ᵥ (S *ᵥ n)) - 2 * (n ⬝ᵥ (fun i => S i i))) using 2
    push_cast
    ring
  · intro τ _ z
    have hz : zAct (spTransl S) τ z = z := by simp [zAct, jAut_spTransl]
    have hx : expArg (spTransl S) τ z = 0 := by simp [expArg, cMat_spTransl]
    have hb : halfVec (n' - S *ᵥ n - fun i => S i i) +
        S.map (fun x : ℤ => (x : ℝ)) *ᵥ halfVec n + (fun i => ((S i i : ℤ) : ℝ) / 2) =
        halfVec n' := by
      rw [mulVec_halfVec]
      funext i
      simp only [halfVec, Pi.add_apply, Pi.sub_apply]
      push_cast
      ring
    rw [hz, hx, spAct_spTransl, jAut_spTransl, Matrix.det_one, eC_zero,
      thetaTranslTau_holds (Fin g) (halfVec n) _ z τ S hS, hb]
    ring

theorem cMat_spDiag {g : ℕ} (U : (Matrix (Fin g) (Fin g) ℤ)ˣ) :
    cMat (spDiag U) = Matrix.fromBlocks ((U : Matrix (Fin g) (Fin g) ℤ).map (fun x : ℤ => (x : ℂ))) 0 0
      (((U⁻¹ : (Matrix (Fin g) (Fin g) ℤ)ˣ) : Matrix (Fin g) (Fin g) ℤ).map (fun x : ℤ => (x : ℂ)))ᵀ := by
  simp [cMat, spDiag, Matrix.fromBlocks_map, Matrix.transpose_map]

theorem mapC_inv_mul {g : ℕ} (U : (Matrix (Fin g) (Fin g) ℤ)ˣ) :
    ((U⁻¹ : (Matrix (Fin g) (Fin g) ℤ)ˣ) : Matrix (Fin g) (Fin g) ℤ).map (fun x : ℤ => (x : ℂ)) *
      (U : Matrix (Fin g) (Fin g) ℤ).map (fun x : ℤ => (x : ℂ)) = 1 := by
  have h : (((U⁻¹ : (Matrix (Fin g) (Fin g) ℤ)ˣ) : Matrix (Fin g) (Fin g) ℤ) *
      (U : Matrix (Fin g) (Fin g) ℤ)).map (Int.castRingHom ℂ) = 1 := by
    rw [Units.inv_mul]
    simp
  exact (Matrix.map_mul (f := Int.castRingHom ℂ)).symm.trans h

theorem jAut_spDiag {g : ℕ} (U : (Matrix (Fin g) (Fin g) ℤ)ˣ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    jAut (spDiag U) τ =
      (((U⁻¹ : (Matrix (Fin g) (Fin g) ℤ)ˣ) : Matrix (Fin g) (Fin g) ℤ).map (fun x : ℤ => (x : ℂ)))ᵀ := by
  simp [jAut, cMat_spDiag]

theorem jAut_spDiag_inv {g : ℕ} (U : (Matrix (Fin g) (Fin g) ℤ)ˣ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    (jAut (spDiag U) τ)⁻¹ = ((U : Matrix (Fin g) (Fin g) ℤ).map (fun x : ℤ => (x : ℂ)))ᵀ := by
  rw [jAut_spDiag]
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.transpose_mul, mapC_inv_mul, Matrix.transpose_one]

theorem chiU_spDiag {g : ℕ} (U : (Matrix (Fin g) (Fin g) ℤ)ˣ) : ChiAtU g (spDiag U) := by
  intro n n'
  obtain ⟨e, he⟩ : ∃ e : ℂ,
      e = ((((U⁻¹ : (Matrix (Fin g) (Fin g) ℤ)ˣ) : Matrix (Fin g) (Fin g) ℤ).det : ℤ) : ℂ) := ⟨_, rfl⟩
  have hjd : ∀ τ, (jAut (spDiag U) τ).det = e := by
    intro τ
    rw [jAut_spDiag, Matrix.det_transpose, he]
    exact (RingHom.map_det (Int.castRingHom ℂ) _).symm
  have he2 : e * e = 1 := by
    have hu := (Matrix.isUnit_iff_isUnit_det _).1
      (Units.isUnit (U⁻¹ : (Matrix (Fin g) (Fin g) ℤ)ˣ))
    rcases Int.isUnit_iff.1 hu with h | h <;> rw [he, h] <;> norm_num
  refine ⟨((U⁻¹ : (Matrix (Fin g) (Fin g) ℤ)ˣ) : Matrix (Fin g) (Fin g) ℤ)ᵀ *ᵥ n,
    (U : Matrix (Fin g) (Fin g) ℤ) *ᵥ n', e, ?_, ?_⟩
  · calc e ^ 4 = (e * e) * (e * e) := by ring
      _ = 1 := by rw [he2, one_mul]
  · intro τ _ z
    have hz : zAct (spDiag U) τ z = (U : Matrix (Fin g) (Fin g) ℤ).map (fun x : ℤ => (x : ℂ)) *ᵥ z := by
      rw [zAct, jAut_spDiag_inv, Matrix.transpose_transpose]
    have hs : spAct (spDiag U) τ = (U : Matrix (Fin g) (Fin g) ℤ).map (fun x : ℤ => (x : ℂ)) * τ *
        ((U : Matrix (Fin g) (Fin g) ℤ).map (fun x : ℤ => (x : ℂ)))ᵀ := by
      rw [spAct, jAut_spDiag_inv, cMat_spDiag]
      simp
    have hx : expArg (spDiag U) τ z = 0 := by simp [expArg, cMat_spDiag]
    have ha : ((U : Matrix (Fin g) (Fin g) ℤ).map (fun x : ℤ => (x : ℝ)))ᵀ *ᵥ
        halfVec (((U⁻¹ : (Matrix (Fin g) (Fin g) ℤ)ˣ) : Matrix (Fin g) (Fin g) ℤ)ᵀ *ᵥ n) = halfVec n := by
      rw [← Matrix.transpose_map, mulVec_halfVec, Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
        Units.inv_mul, Matrix.transpose_one, Matrix.one_mulVec]
    have hb : ((U⁻¹ : (Matrix (Fin g) (Fin g) ℤ)ˣ) : Matrix (Fin g) (Fin g) ℤ).map (fun x : ℤ => (x : ℝ)) *ᵥ
        halfVec ((U : Matrix (Fin g) (Fin g) ℤ) *ᵥ n') = halfVec n' := by
      rw [mulVec_halfVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    rw [hz, hs, hx, hjd, eC_zero, thetaGL_holds (Fin g) U _ _ z τ, ha, hb]
    linear_combination (-(theta (halfVec n) (halfVec n') z τ ^ 2)) * he2

theorem cMat_J (g : ℕ) : cMat (Matrix.J (Fin g) ℤ) = Matrix.J (Fin g) ℂ := by
  unfold cMat
  ext (i | i) (j | j) <;> simp [Matrix.J, Matrix.one_apply]

theorem jAut_J {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) : jAut (Matrix.J (Fin g) ℤ) τ = τ := by
  rw [jAut, cMat_J]
  simp [Matrix.J]

theorem chiU_J {g : ℕ} (hInv : InversionStatement) : ChiAtU g (Matrix.J (Fin g) ℤ) := by
  intro n n'
  have hd : ofRealVec (halfVec (-n')) ⬝ᵥ ofRealVec (halfVec n) = (((-n') ⬝ᵥ n : ℤ) : ℂ) / 4 := by
    rw [ofRealVec_halfVec, ofRealVec_halfVec, smul_dotProduct, dotProduct_smul, ofIntVec_dot]
    simp only [smul_eq_mul]
    ring
  refine ⟨-n', n, (-I) ^ g * eC (2 * (ofRealVec (halfVec (-n')) ⬝ᵥ ofRealVec (halfVec n))), ?_, ?_⟩
  · have h4 : (-I) ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, neg_sq, I_sq]
      norm_num
    rw [mul_pow, ← pow_mul, mul_comm g 4, pow_mul, h4, one_pow, one_mul, eC_pow, hd]
    convert eC_int (2 * ((-n') ⬝ᵥ n)) using 2
    push_cast
    ring
  · intro τ hτ z
    have hsym : τᵀ = τ := hτ.1
    have hz : zAct (Matrix.J (Fin g) ℤ) τ z = τ⁻¹ *ᵥ z := by
      rw [zAct, jAut_J, Matrix.transpose_nonsing_inv, hsym]
    have hs : spAct (Matrix.J (Fin g) ℤ) τ = -τ⁻¹ := by
      rw [spAct, jAut_J, cMat_J]
      simp [Matrix.J]
    have hx : expArg (Matrix.J (Fin g) ℤ) τ z = z ⬝ᵥ (τ⁻¹ *ᵥ z) := by
      rw [expArg, jAut_J, cMat_J]
      simp [Matrix.J]
    have hneg : -halfVec (-n') = halfVec n' := by
      funext i
      simp [halfVec, neg_div]
    rw [hz, hs, hx, jAut_J, hInv g (halfVec (-n')) (halfVec n) τ hτ z, hneg]
    ring

theorem chiU_gen {g : ℕ} (hInv : InversionStatement) {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hγ : γ ∈ spGens g) : ChiAtU g γ := by
  simp only [spGens, Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff] at hγ
  rcases hγ with (⟨S, hS, rfl⟩ | ⟨U, rfl⟩) | rfl
  · exact chiU_spTransl S hS
  · exact chiU_spDiag U
  · exact chiU_J hInv

end ReciprocityTheory.ChartRestriction.G.Key.Chi
