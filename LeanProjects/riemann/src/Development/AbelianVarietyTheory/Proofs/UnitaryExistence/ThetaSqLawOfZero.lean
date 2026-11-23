import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods

noncomputable section

open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ThetaCharMult

variable {g : ℕ}

theorem sp_rel_transpose {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hγ : γ ∈ Matrix.symplecticGroup (Fin g) ℤ) :
    ((cMat γ).toBlocks₁₂ * (cMat γ).toBlocks₂₁ᵀ - (cMat γ).toBlocks₁₁ * (cMat γ).toBlocks₂₂ᵀ = -1) ∧
    ((cMat γ).toBlocks₂₂ * (cMat γ).toBlocks₂₁ᵀ - (cMat γ).toBlocks₂₁ * (cMat γ).toBlocks₂₂ᵀ = 0) := by
  obtain ⟨-, r2, -, r4⟩ := sp_rel (SymplecticGroup.transpose_mem hγ)
  exact ⟨r2, r4⟩

theorem sp_rel_int {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hγ : γ ∈ Matrix.symplecticGroup (Fin g) ℤ) :
    γ.toBlocks₁₁ * γ.toBlocks₂₂ᵀ = 1 + γ.toBlocks₁₂ * γ.toBlocks₂₁ᵀ := by
  have h := (sp_rel_transpose hγ).1
  have h' : (cMat γ).toBlocks₁₁ * (cMat γ).toBlocks₂₂ᵀ =
      1 + (cMat γ).toBlocks₁₂ * (cMat γ).toBlocks₂₁ᵀ := by
    rw [sub_eq_iff_eq_add] at h
    rw [h]; abel
  ext i j
  have := congrFun (congrFun h' i) j
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply, cMat, Matrix.toBlocks₁₁,
    Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.map_apply] at this ⊢
  exact_mod_cast this

theorem shift_algebra (A B C D τ σ J : Matrix (Fin g) (Fin g) ℂ) (hτ : τ.IsSymm) (hσ : σ.IsSymm)
    (h1 : J * (C * τ + D) = 1) (h2 : (C * τ + D) * J = 1) (hs : σ = (A * τ + B) * J)
    (hA : A - σ * C = Jᵀ) (hCD : D * Cᵀ - C * Dᵀ = 0) (a b z a' b' : Fin g → ℂ)
    (ha' : a' = Aᵀ *ᵥ a + Cᵀ *ᵥ b) (hb' : b' = Bᵀ *ᵥ a + Dᵀ *ᵥ b) :
    Jᵀ *ᵥ (z + τ *ᵥ a' + b') = Jᵀ *ᵥ z + σ *ᵥ a + b ∧
    (z + τ *ᵥ a' + b') ⬝ᵥ ((J * C) *ᵥ (z + τ *ᵥ a' + b')) +
        2 * (-(a' ⬝ᵥ (τ *ᵥ a')) / 2 - a' ⬝ᵥ (z + b')) =
      z ⬝ᵥ ((J * C) *ᵥ z) + (a ⬝ᵥ b - a' ⬝ᵥ b') +
        2 * (-(a ⬝ᵥ (σ *ᵥ a)) / 2 - a ⬝ᵥ (Jᵀ *ᵥ z + b)) := by
  set j := C * τ + D with hj
  have hjT : jᵀ = τ * Cᵀ + Dᵀ := by rw [hj, transpose_add, transpose_mul, hτ.eq]
  have hjσ : jᵀ * σ = τ * Aᵀ + Bᵀ := by
    conv_lhs => rw [← hσ.eq]
    rw [← transpose_mul, hs, Matrix.mul_assoc, h1, Matrix.mul_one, transpose_add, transpose_mul,
      hτ.eq]
  set p := σ *ᵥ a + b with hp
  set q := τ *ᵥ a' + b' with hq
  have hqp : jᵀ *ᵥ p = q := by
    rw [hp, hq, ha', hb', mulVec_add, mulVec_mulVec, hjσ, hjT]
    simp only [add_mulVec, mulVec_add, mulVec_mulVec]
    abel
  have hpq : Jᵀ *ᵥ q = p := by
    rw [← hqp, mulVec_mulVec, ← transpose_mul, h2, transpose_one, one_mulVec]
  have hM : (J * C).IsSymm := by
    have e : C * jᵀ = j * Cᵀ := by
      rw [hjT, hj, Matrix.mul_add, Matrix.add_mul, sub_eq_zero.mp hCD, Matrix.mul_assoc]
    show (J * C)ᵀ = J * C
    calc (J * C)ᵀ = (J * j) * Cᵀ * Jᵀ := by rw [h1, Matrix.one_mul, transpose_mul]
      _ = J * (C * jᵀ) * Jᵀ := by rw [e]; simp only [Matrix.mul_assoc]
      _ = J * C * (J * j)ᵀ := by rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = J * C := by rw [h1, transpose_one, Matrix.mul_one]
  have hq1 : ∀ x, q ⬝ᵥ ((J * C) *ᵥ x) = a' ⬝ᵥ x - a ⬝ᵥ (Jᵀ *ᵥ x) := by
    intro x
    have e1 : q ⬝ᵥ ((J * C) *ᵥ x) = p ⬝ᵥ (C *ᵥ x) := by
      rw [← hpq, ← mulVec_mulVec, dotProduct_mulVec, mulVec_transpose]
    have e2 : a' ⬝ᵥ x = a ⬝ᵥ (A *ᵥ x) + b ⬝ᵥ (C *ᵥ x) := by
      rw [ha', add_dotProduct, mulVec_transpose, mulVec_transpose, dotProduct_mulVec,
        dotProduct_mulVec]
    have e3 : (σ *ᵥ a) ⬝ᵥ (C *ᵥ x) = a ⬝ᵥ (σ *ᵥ (C *ᵥ x)) := by
      rw [dot_mulVec_symm hσ, dotProduct_comm]
    rw [e1, e2, ← hA, sub_mulVec, dotProduct_sub, hp, add_dotProduct, e3, mulVec_mulVec]
    ring
  have hz : z + τ *ᵥ a' + b' = z + q := by rw [hq, add_assoc]
  rw [hz]
  refine ⟨by rw [mulVec_add, hpq, hp, add_assoc], ?_⟩
  have e4 := dot_mulVec_symm hM q z
  have e5 := hq1 z
  have e6 := hq1 q
  rw [hpq] at e6
  have e7 : a' ⬝ᵥ q = a' ⬝ᵥ (τ *ᵥ a') + a' ⬝ᵥ b' := by rw [hq, dotProduct_add]
  have e8 : a ⬝ᵥ p = a ⬝ᵥ (σ *ᵥ a) + a ⬝ᵥ b := by rw [hp, dotProduct_add]
  simp only [mulVec_add, add_dotProduct, dotProduct_add]
  rw [e4, e5, e6, e7, e8]
  ring

theorem dvd_mulVec {M : Matrix (Fin g) (Fin g) ℤ} {k : ℤ} (h : ∀ i j, k ∣ M i j) (v : Fin g → ℤ)
    (i : Fin g) : k ∣ (M *ᵥ v) i := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.dvd_sum fun j _ => (h i j).mul_right _

theorem dvd_dot_left {k : ℤ} {u : Fin g → ℤ} (h : ∀ i, k ∣ u i) (v : Fin g → ℤ) : k ∣ u ⬝ᵥ v :=
  Finset.dvd_sum fun j _ => (h j).mul_right _

theorem dvd_dot_right {k : ℤ} {v : Fin g → ℤ} (h : ∀ i, k ∣ v i) (u : Fin g → ℤ) : k ∣ u ⬝ᵥ v :=
  Finset.dvd_sum fun j _ => (h j).mul_left _

theorem phase_dvd {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hγ : γ ∈ Matrix.symplecticGroup (Fin g) ℤ)
    (hB : ∀ i j, (8 : ℤ) ∣ γ.toBlocks₁₂ᵀ i j) (hC : ∀ i j, (8 : ℤ) ∣ γ.toBlocks₂₁ᵀ i j)
    (n n' : Fin g → ℤ) :
    (8 : ℤ) ∣ n ⬝ᵥ n' - (γ.toBlocks₁₁ᵀ *ᵥ n + γ.toBlocks₂₁ᵀ *ᵥ n') ⬝ᵥ
      (γ.toBlocks₁₂ᵀ *ᵥ n + γ.toBlocks₂₂ᵀ *ᵥ n') := by
  have e : (γ.toBlocks₁₁ᵀ *ᵥ n) ⬝ᵥ (γ.toBlocks₂₂ᵀ *ᵥ n') =
      n ⬝ᵥ n' + (γ.toBlocks₁₂ᵀ *ᵥ n) ⬝ᵥ (γ.toBlocks₂₁ᵀ *ᵥ n') := by
    rw [mulVec_transpose, mulVec_transpose γ.toBlocks₁₂, ← dotProduct_mulVec, ← dotProduct_mulVec,
      mulVec_mulVec, mulVec_mulVec, sp_rel_int hγ, add_mulVec, one_mulVec, dotProduct_add]
  have d1 := dvd_dot_left (dvd_mulVec hB n) (γ.toBlocks₂₁ᵀ *ᵥ n')
  have d2 := dvd_dot_right (dvd_mulVec hB n) (γ.toBlocks₁₁ᵀ *ᵥ n)
  have d3 := dvd_dot_left (dvd_mulVec hC n') (γ.toBlocks₁₂ᵀ *ᵥ n + γ.toBlocks₂₂ᵀ *ᵥ n')
  rw [add_dotProduct, dotProduct_add, e]
  omega

theorem half_mulVec (M : Matrix (Fin g) (Fin g) ℤ) (N : Matrix (Fin g) (Fin g) ℤ)
    (n n' : Fin g → ℤ) :
    ofRealVec (halfVec (M *ᵥ n + N *ᵥ n')) =
      M.map (fun x : ℤ => (x : ℂ)) *ᵥ ofRealVec (halfVec n) +
        N.map (fun x : ℤ => (x : ℂ)) *ᵥ ofRealVec (halfVec n') := by
  ext i
  simp [ofRealVec, halfVec, Matrix.mulVec, dotProduct, Finset.sum_div, mul_div_assoc, add_div]

theorem theta_zero_shift_sq (a b : Fin g → ℝ) (z : Fin g → ℂ) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ.IsSymm) :
    theta (halfVec 0) (halfVec 0) (z + τ *ᵥ ofRealVec a + ofRealVec b) τ ^ 2 =
      eC (2 * (-(ofRealVec a ⬝ᵥ (τ *ᵥ ofRealVec a)) / 2 - ofRealVec a ⬝ᵥ (z + ofRealVec b))) *
        theta a b z τ ^ 2 := by
  have h0 : halfVec (0 : Fin g → ℤ) = 0 := by ext i; simp [halfVec]
  have h00 : ofRealVec (0 : Fin g → ℝ) = 0 := by ext i; simp [ofRealVec]
  rw [h0, thetaRealTransl_holds (Fin g) 0 0 a b z τ hτ, mul_pow, eC_pow, h00, zero_add, zero_add,
    add_zero]
  norm_num

theorem theta_sq_law_of_zero : ∀ (g : ℕ) (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ), γ ∈ Matrix.symplecticGroup (Fin g) ℤ → (∀ i j, (8 : ℤ) ∣ γ (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ γ (Sum.inr i) (Sum.inl j)) → ∀ (c : ℂ) (n n' : Fin g → ℤ), (∀ τ ∈ SiegelH (Fin g), ∀ z : Fin g → ℂ, theta (halfVec 0) (halfVec 0) (zAct γ τ z) (spAct γ τ) ^ 2 = c * (jAut γ τ).det * eC (expArg γ τ z) * theta (halfVec 0) (halfVec 0) z τ ^ 2) → (∀ i, (2 : ℤ) ∣ (γ.toBlocks₁₁ᵀ *ᵥ n) i - n i) ∧ (∀ i, (2 : ℤ) ∣ (γ.toBlocks₂₂ᵀ *ᵥ n') i - n' i) → (∀ τ ∈ SiegelH (Fin g), ∀ z : Fin g → ℂ, theta (halfVec n) (halfVec n') (zAct γ τ z) (spAct γ τ) ^ 2 = c * (jAut γ τ).det * eC (expArg γ τ z) * theta (halfVec n) (halfVec n') z τ ^ 2) := by
  intro g γ hγ h8 c n n' h0 ⟨hn, hn'⟩ τ hτ z
  have hB : ∀ i j, (8 : ℤ) ∣ γ.toBlocks₁₂ᵀ i j := fun i j => (h8 j i).1
  have hC : ∀ i j, (8 : ℤ) ∣ γ.toBlocks₂₁ᵀ i j := fun i j => (h8 j i).2
  have hj := jAut_isUnit hγ hτ
  have hσ := spAct_isSymm hγ hτ.1 hj
  set m := γ.toBlocks₁₁ᵀ *ᵥ n + γ.toBlocks₂₁ᵀ *ᵥ n' with hm
  set m' := γ.toBlocks₁₂ᵀ *ᵥ n + γ.toBlocks₂₂ᵀ *ᵥ n' with hm'
  obtain ⟨k1, k2⟩ := shift_algebra (cMat γ).toBlocks₁₁ (cMat γ).toBlocks₁₂ (cMat γ).toBlocks₂₁
    (cMat γ).toBlocks₂₂ τ (spAct γ τ) (jAut γ τ)⁻¹ hτ.1 hσ (Matrix.nonsing_inv_mul _ hj)
    (Matrix.mul_nonsing_inv _ hj) rfl (sp_A hγ hτ.1 hj) (sp_rel_transpose hγ).2
    (ofRealVec (halfVec n)) (ofRealVec (halfVec n')) z (ofRealVec (halfVec m))
    (ofRealVec (halfVec m')) (half_mulVec _ _ n n') (half_mulVec _ _ n n')
  have h := h0 τ hτ (z + τ *ᵥ ofRealVec (halfVec m) + ofRealVec (halfVec m'))
  have hred : theta (halfVec m) (halfVec m') z τ ^ 2 = theta (halfVec n) (halfVec n') z τ ^ 2 := by
    rw [theta_sq_red m m', theta_sq_red n n']
    have e1 : (fun i => m i % 2) = fun i => n i % 2 := by
      funext i
      have a1 := hn i
      have a2 := dvd_mulVec hC n' i
      simp only [hm, Pi.add_apply]
      omega
    have e2 : (fun i => m' i % 2) = fun i => n' i % 2 := by
      funext i
      have a1 := hn' i
      have a2 := dvd_mulVec hB n i
      simp only [hm', Pi.add_apply]
      omega
    rw [e1, e2]
  obtain ⟨t, ht⟩ := phase_dvd hγ hB hC n n'
  have hph : ofRealVec (halfVec n) ⬝ᵥ ofRealVec (halfVec n') -
      ofRealVec (halfVec m) ⬝ᵥ ofRealVec (halfVec m') = ((2 * t : ℤ) : ℂ) := by
    have ht' : ((n ⬝ᵥ n' : ℤ) : ℂ) - ((m ⬝ᵥ m' : ℤ) : ℂ) = 8 * (t : ℂ) := by exact_mod_cast ht
    simp only [ofRealVec_halfVec, smul_dotProduct, dotProduct_smul, ofIntVec_dot, smul_eq_mul]
    push_cast
    linear_combination (1 / 4 : ℂ) * ht'
  rw [zAct, k1, theta_zero_shift_sq _ _ _ hσ, theta_zero_shift_sq _ _ _ hτ.1, hred, ← mul_assoc,
    mul_assoc (c * _), ← eC_add, expArg, k2, hph, eC_add, eC_add, eC_int, mul_one] at h
  have hne : ∀ x, eC x ≠ 0 := fun x => Complex.exp_ne_zero _
  refine mul_left_cancel₀ (hne _) (h.trans ?_)
  rw [expArg]
  ring

end GlobalTheory.ThetaCharMult
