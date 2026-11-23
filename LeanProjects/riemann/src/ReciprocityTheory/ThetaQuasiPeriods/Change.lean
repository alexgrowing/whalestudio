import ReciprocityTheory.ThetaQuasiPeriods.Transl

noncomputable section

open Complex Matrix

namespace ReciprocityTheory.PTheta

variable {ι : Type*} [Fintype ι]

theorem quad_diag_int (B : Matrix ι ι ℤ) (hB : B.IsSymm) (l : ι → ℤ) :
    ∃ k : ℤ, l ⬝ᵥ (B *ᵥ l) = l ⬝ᵥ (fun i => B i i) + 2 * k := by
  classical
  have hsq : ∀ x : ZMod 2, x * x = x := by decide
  have htwo : ∀ x : ZMod 2, x + x = 0 := by decide
  have key : ∀ f : ι → ι → ZMod 2, (∀ i j, f i j = f j i) →
      ∑ i, ∑ j, f i j = ∑ i, f i i := by
    intro f hf
    have h : ∑ p : ι × ι, (f p.1 p.2 - if p.1 = p.2 then f p.1 p.2 else 0) = 0 := by
      refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ (fun p _ => Finset.mem_univ _)
        (fun p _ => Prod.swap_swap p)
      · intro p _
        simp only [Prod.fst_swap, Prod.snd_swap]
        rw [hf p.2 p.1]
        by_cases hp : p.1 = p.2
        · simp [hp]
        · simp only [if_neg hp, if_neg (Ne.symm hp), sub_zero]
          exact htwo _
      · intro p _ hne heq
        apply hne
        have h12 : p.1 = p.2 := by
          have := congrArg Prod.fst heq
          simpa using this.symm
        simp only [if_pos h12, sub_self]
    rw [Fintype.sum_prod_type] at h
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
    exact sub_eq_zero.mp h
  suffices h2 : ((l ⬝ᵥ (B *ᵥ l) - l ⬝ᵥ (fun i => B i i) : ℤ) : ZMod 2) = 0 by
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h2
    exact ⟨k, by push_cast at hk; linarith⟩
  push_cast [dotProduct, Matrix.mulVec]
  simp_rw [Finset.mul_sum]
  rw [sub_eq_zero]
  refine (key (fun i j => (l i : ZMod 2) * ((B i j : ZMod 2) * (l j : ZMod 2))) ?_).trans ?_
  · intro i j
    show (l i : ZMod 2) * ((B i j : ZMod 2) * (l j : ZMod 2)) =
      (l j : ZMod 2) * ((B j i : ZMod 2) * (l i : ZMod 2))
    rw [hB.apply i j]
    ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    show (l i : ZMod 2) * ((B i i : ZMod 2) * (l i : ZMod 2)) = _
    rw [mul_comm (B i i : ZMod 2), ← mul_assoc, hsq]

theorem eC_eq_of_int (x y : ℂ) (k : ℤ) (h : x = y + k) : eC x = eC y := by
  rw [h]
  simp only [eC]
  rw [mul_add, Complex.exp_add]
  have hk : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) = 1 := by
    rw [show (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) = (k : ℂ) * (2 * Real.pi * Complex.I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I k
  rw [hk, mul_one]

theorem shiftVec_eq (a : ι → ℝ) (l : ι → ℤ) : shiftVec a l = ofIntVec l + ofRealVec a := by
  rfl

theorem ofRealVec_mulVec (M : Matrix ι ι ℤ) (a : ι → ℝ) :
    ofRealVec (M.map (fun x : ℤ => (x : ℝ)) *ᵥ a) = M.map (fun x : ℤ => (x : ℂ)) *ᵥ ofRealVec a := by
  funext i
  simp [ofRealVec, Matrix.mulVec, dotProduct]

theorem ofIntVec_mulVec (M : Matrix ι ι ℤ) (l : ι → ℤ) :
    ofIntVec (M *ᵥ l) = M.map (fun x : ℤ => (x : ℂ)) *ᵥ ofIntVec l := by
  funext i
  simp [ofIntVec, Matrix.mulVec, dotProduct]

theorem thetaTranslTau_holds : ThetaTranslTauStatement := by
  unfold ThetaTranslTauStatement
  intro ι _ a b z τ B hB
  have hadd : ∀ x y : ℂ, eC (x + y) = eC x * eC y := fun x y => by
    simp only [eC, mul_add, Complex.exp_add]
  have hb' : ofRealVec (b + B.map (fun x : ℤ => (x : ℝ)) *ᵥ a + fun i => ((B i i : ℤ) : ℝ) / 2) =
      ofRealVec b + B.map (fun x : ℤ => (x : ℂ)) *ᵥ ofRealVec a + fun i => ((B i i : ℤ) : ℂ) / 2 := by
    rw [← ofRealVec_mulVec]
    funext i
    simp [ofRealVec]
  have hBc : (B.map (fun x : ℤ => (x : ℂ)))ᵀ = B.map (fun x : ℤ => (x : ℂ)) := by
    ext i j
    simp [Matrix.transpose_apply, Matrix.map_apply, hB.apply i j]
  unfold theta
  rw [← tsum_mul_left]
  refine tsum_congr fun l => ?_
  obtain ⟨k, hk⟩ := quad_diag_int B hB l
  have hkC : ofIntVec l ⬝ᵥ (B.map (fun x : ℤ => (x : ℂ)) *ᵥ ofIntVec l) =
      ofIntVec l ⬝ᵥ (fun i => ((B i i : ℤ) : ℂ)) + 2 * (k : ℂ) := by
    have e1 : ofIntVec l ⬝ᵥ ofIntVec (B *ᵥ l) = ((l ⬝ᵥ (B *ᵥ l) : ℤ) : ℂ) := by
      simp [dotProduct, ofIntVec]
    have e2 : ofIntVec l ⬝ᵥ (fun i => ((B i i : ℤ) : ℂ)) = ((l ⬝ᵥ (fun i => B i i) : ℤ) : ℂ) := by
      simp [dotProduct, ofIntVec]
    rw [← ofIntVec_mulVec, e1, e2, hk]
    first
      | (push_cast; done)
      | (push_cast; ring)
  have hsA : ofRealVec a ⬝ᵥ (B.map (fun x : ℤ => (x : ℂ)) *ᵥ ofIntVec l) =
      ofIntVec l ⬝ᵥ (B.map (fun x : ℤ => (x : ℂ)) *ᵥ ofRealVec a) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hBc, dotProduct_comm]
  have hhL : ofIntVec l ⬝ᵥ (fun i => ((B i i : ℤ) : ℂ) / 2) =
      (ofIntVec l ⬝ᵥ fun i => ((B i i : ℤ) : ℂ)) / 2 := by
    simp only [dotProduct, Finset.sum_div, mul_div_assoc]
  unfold thetaTerm
  rw [← hadd]
  apply eC_eq_of_int _ _ k
  rw [hb', shiftVec_eq]
  simp only [Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  linear_combination (1 / 2 : ℂ) * hkC + (1 / 2 : ℂ) * hsA - hhL

def transpEquiv [DecidableEq ι] (U : (Matrix ι ι ℤ)ˣ) : (ι → ℤ) ≃ (ι → ℤ) where
  toFun l := (U : Matrix ι ι ℤ)ᵀ *ᵥ l
  invFun m := ((U⁻¹ : (Matrix ι ι ℤ)ˣ) : Matrix ι ι ℤ)ᵀ *ᵥ m
  left_inv l := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
      Matrix.one_mulVec]
  right_inv m := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one,
      Matrix.one_mulVec]

theorem thetaGL_holds : ThetaGLStatement := by
  unfold ThetaGLStatement
  intro ι _ _ U a b z τ
  have h1 : ((U⁻¹ : (Matrix ι ι ℤ)ˣ) : Matrix ι ι ℤ)ᵀ * (U : Matrix ι ι ℤ)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have hVt : ((U : Matrix ι ι ℤ).map (fun x : ℤ => (x : ℂ)))ᵀ =
      ((U : Matrix ι ι ℤ)ᵀ).map (fun x : ℤ => (x : ℂ)) := by
    rw [← Matrix.transpose_map]
  have hWT : (((U⁻¹ : (Matrix ι ι ℤ)ˣ) : Matrix ι ι ℤ).map (fun x : ℤ => (x : ℂ)))ᵀ *
      ((U : Matrix ι ι ℤ)ᵀ).map (fun x : ℤ => (x : ℂ)) = 1 := by
    ext i j
    have h2 := congrFun (congrFun h1 i) j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply] at h2 ⊢
    exact_mod_cast h2
  unfold theta
  conv_rhs => rw [← (transpEquiv U).tsum_eq]
  refine tsum_congr fun l => ?_
  have hs : shiftVec (((U : Matrix ι ι ℤ).map (fun x : ℤ => (x : ℝ)))ᵀ *ᵥ a)
      ((U : Matrix ι ι ℤ)ᵀ *ᵥ l) =
      ((U : Matrix ι ι ℤ)ᵀ).map (fun x : ℤ => (x : ℂ)) *ᵥ shiftVec a l := by
    rw [shiftVec_eq, shiftVec_eq, ← Matrix.transpose_map, ofIntVec_mulVec, ofRealVec_mulVec,
      Matrix.mulVec_add]
  have q : ∀ s : ι → ℂ, s ⬝ᵥ (((U : Matrix ι ι ℤ).map (fun x : ℤ => (x : ℂ)) * τ *
      ((U : Matrix ι ι ℤ).map (fun x : ℤ => (x : ℂ)))ᵀ) *ᵥ s) =
      (((U : Matrix ι ι ℤ)ᵀ).map (fun x : ℤ => (x : ℂ)) *ᵥ s) ⬝ᵥ
        (τ *ᵥ (((U : Matrix ι ι ℤ)ᵀ).map (fun x : ℤ => (x : ℂ)) *ᵥ s)) := by
    intro s
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, hVt]
  have lin : ∀ s : ι → ℂ,
      s ⬝ᵥ ((U : Matrix ι ι ℤ).map (fun x : ℤ => (x : ℂ)) *ᵥ z + ofRealVec b) =
      (((U : Matrix ι ι ℤ)ᵀ).map (fun x : ℤ => (x : ℂ)) *ᵥ s) ⬝ᵥ
        (z + ofRealVec (((U⁻¹ : (Matrix ι ι ℤ)ˣ) : Matrix ι ι ℤ).map (fun x : ℤ => (x : ℝ)) *ᵥ b)) := by
    intro s
    have hl1 : s ⬝ᵥ ((U : Matrix ι ι ℤ).map (fun x : ℤ => (x : ℂ)) *ᵥ z) =
        (((U : Matrix ι ι ℤ)ᵀ).map (fun x : ℤ => (x : ℂ)) *ᵥ s) ⬝ᵥ z := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hVt]
    have hl2 : (((U : Matrix ι ι ℤ)ᵀ).map (fun x : ℤ => (x : ℂ)) *ᵥ s) ⬝ᵥ
        (((U⁻¹ : (Matrix ι ι ℤ)ˣ) : Matrix ι ι ℤ).map (fun x : ℤ => (x : ℂ)) *ᵥ ofRealVec b) =
        s ⬝ᵥ ofRealVec b := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hWT,
        Matrix.one_mulVec]
    rw [ofRealVec_mulVec, dotProduct_add, dotProduct_add, hl1, hl2]
  simp only [transpEquiv, Equiv.coe_fn_mk]
  unfold thetaTerm
  rw [hs, q, lin]

end ReciprocityTheory.PTheta
