import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.HolomorphicSectionLoweringInvariant

noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.CR

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hasDerivAt_matrix_mul {A B : ℂ → Matrix (Fin n) (Fin n) ℂ} {A' B' : Matrix (Fin n) (Fin n) ℂ}
    (hA : HasDerivAt A A' 0) (hB : HasDerivAt B B' 0) :
    HasDerivAt (fun τ => A τ * B τ) (A' * B 0 + A 0 * B') 0 := by
  have hA' : HasDerivAt (fun τ => (A τ : Fin n → Fin n → ℂ)) (A' : Fin n → Fin n → ℂ) 0 := hA
  have hB' : HasDerivAt (fun τ => (B τ : Fin n → Fin n → ℂ)) (B' : Fin n → Fin n → ℂ) 0 := hB
  have h : HasDerivAt (fun τ => ((A τ * B τ : Matrix (Fin n) (Fin n) ℂ) : Fin n → Fin n → ℂ))
      ((A' * B 0 + A 0 * B' : Matrix (Fin n) (Fin n) ℂ) : Fin n → Fin n → ℂ) 0 := by
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
    simp only [Matrix.mul_apply, Matrix.add_apply]
    rw [← Finset.sum_add_distrib]
    refine HasDerivAt.fun_sum fun k _ => ?_
    exact (hasDerivAt_pi.1 (hasDerivAt_pi.1 hA' i) k).mul (hasDerivAt_pi.1 (hasDerivAt_pi.1 hB' k) j)
  exact h

theorem fderiv_zOfE_raise (x : M2 n) (h : (u1 x).det ≠ 0) (S : Matrix (Fin n) (Fin n) ℂ) :
    fderiv ℂ zOfE x (x * raiseR S) = WM x * S * (u1 x)⁻¹ := by
  let v := x * raiseR S
  have hl := ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x
  have hg := (da_zOfE x h).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hl (by simp)
  simp only [id_eq, one_smul, Function.comp_def] at hg
  have hu : ∀ τ : ℂ, u1 (x + τ • v) = u1 x + τ • (u2 x * S) := fun τ => by
    rw [line_raise, first_cayley_block_mul_block, Matrix.mul_one, Matrix.mul_smul]
  have hN : ∀ τ : ℂ, Nm (x + τ • v) = Nm x + τ • (Nm' x * S) := fun τ => by
    rw [line_raise, Nm_mX, Matrix.mul_one, Matrix.mul_smul]
  have hc : Continuous fun τ : ℂ => (u1 x + τ • (u2 x * S)).det :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  have hev : ∀ᶠ τ in 𝓝 (0 : ℂ), (u1 x + τ • (u2 x * S)).det ≠ 0 :=
    hc.continuousAt.eventually_ne (by simpa using h)
  have hB := ((hasDerivAt_id (0 : ℂ)).smul_const (u2 x * S)).const_add (u1 x)
  simp only [id_eq, one_smul] at hB
  have hL := hasDerivAt_matrix_mul hg hB
  have hR := ((hasDerivAt_id (0 : ℂ)).smul_const (Nm' x * S)).const_add (Nm x)
  simp only [id_eq, one_smul] at hR
  have heq : (fun τ : ℂ => zOfE (x + τ • v) * (u1 x + τ • (u2 x * S))) =ᶠ[𝓝 0]
      fun τ => Nm x + τ • (Nm' x * S) := by
    filter_upwards [hev] with τ hτ
    rw [← hu, zOfE_eq, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (by rwa [hu])), Matrix.mul_one, hN]
  have hfin := hL.unique (hR.congr_of_eventuallyEq heq)
  simp only [zero_smul, add_zero] at hfin
  have hu1 : IsUnit (u1 x).det := isUnit_iff_ne_zero.2 h
  have key : fderiv ℂ zOfE x v * u1 x = WM x * S := by
    refine (eq_sub_of_add_eq hfin).trans ?_
    rw [WM, show (-(Complex.I • x.toBlocks₁₁) + x.toBlocks₁₂) = Nm' x from rfl, Matrix.sub_mul, Matrix.mul_assoc (zOfE x)]
  calc fderiv ℂ zOfE x v = fderiv ℂ zOfE x v * u1 x * (u1 x)⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu1, Matrix.mul_one]
    _ = WM x * S * (u1 x)⁻¹ := congrArg (fun M => M * (u1 x)⁻¹) key

theorem toBlocks₁₁_mul' (A B : M2 n) :
    (A * B).toBlocks₁₁ = A.toBlocks₁₁ * B.toBlocks₁₁ + A.toBlocks₁₂ * B.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp

theorem toBlocks₁₂_mul' (A B : M2 n) :
    (A * B).toBlocks₁₂ = A.toBlocks₁₁ * B.toBlocks₁₂ + A.toBlocks₁₂ * B.toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp

theorem mul_cm₁₁ (x : M2 n) : (x * Cm n).toBlocks₁₁ = Nm x := by
  simp [toBlocks₁₁_mul', Cm, Nm, Matrix.mul_smul]

theorem mul_cm₁₂ (x : M2 n) : (x * Cm n).toBlocks₁₂ = Nm' x := by
  simp [toBlocks₁₂_mul', Cm, Nm', Matrix.mul_smul, Matrix.mul_neg]

theorem det_ne_of_inG {x : M2 n} (hx : InG x) : x.det ≠ 0 := by
  intro h0
  have h1 := congrArg Matrix.det hx
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h1
  have h2 : (JJ n).det ≠ 0 := by
    intro h3
    have := congrArg Matrix.det (JJ_mul_JJ (n := n))
    rw [Matrix.det_mul, h3, zero_mul, Matrix.det_neg] at this
    simp at this
  exact h2 h1.symm

theorem det_cm_ne : (Cm n).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (cm_mul_cmi (n := n))
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem wm_det (x : M2 n) (hx : InG x) (h : (u1 x).det ≠ 0) : (WM x).det ≠ 0 := by
  intro hW
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hW
  set w := -(((u1 x)⁻¹ * u2 x) *ᵥ v)
  have hu1 : IsUnit (u1 x).det := isUnit_iff_ne_zero.2 h
  have hM : (x * Cm n) *ᵥ Sum.elim w v = 0 := by
    rw [← fromBlocks_toBlocks (x * Cm n), fromBlocks_mulVec, mul_cm₁₁, mul_cm₁₂, mul_cm₂₁, mul_cm₂₂]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
    have e1 : Nm x *ᵥ w + Nm' x *ᵥ v = WM x *ᵥ v := by
      simp only [w, WM, Matrix.mulVec_neg, Matrix.mulVec_mulVec, zOfE_eq, Matrix.sub_mulVec, Matrix.mul_assoc]
      rw [show -(Complex.I • x.toBlocks₁₁) + x.toBlocks₁₂ = Nm' x from rfl]; abel
    have e2 : u1 x *ᵥ w + u2 x *ᵥ v = 0 := by
      simp only [w, Matrix.mulVec_neg, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu1,
        Matrix.one_mul, neg_add_cancel]
    rw [e1, e2, hv]
    funext i; cases i <;> simp
  have hdet : (x * Cm n).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero (det_ne_of_inG hx) det_cm_ne
  have h0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hM
  exact hv0 (funext fun i => by simpa using congrFun h0 (Sum.inr i))

theorem cra2 : CauchyRiemannFacts := by
  refine ⟨fun n m e y => orbital_function_eq_weighted m e y, fun n x h0 h => ⟨da_zOfE x h, fun m e => da_F0E m e x h0 h, fun Q =>
    ⟨fderiv_zOfE_low x h Q, fun m e => fderiv_F0E_low m e x h0 h Q⟩, fun R => ?_, fun hx => wm_det x hx h⟩⟩
  rw [sig_low]
  exact fderiv_zOfE_raise x h Rᴴ

end PositivityTheory.Rg.Sw.HSt.CR
