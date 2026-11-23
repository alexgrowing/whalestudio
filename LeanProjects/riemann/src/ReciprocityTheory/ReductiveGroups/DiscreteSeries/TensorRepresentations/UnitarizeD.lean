import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.UnitarizeC

noncomputable section

open Finset MeasureTheory
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS.UnitB

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool}

theorem Jm_mul_Jm' (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  rw [Jm_eq, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  exact sg_mul_self ε a

theorem Jm_conjT (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  rw [Jm_eq, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  exact star_sg ε a

theorem Jm_Jm_mul (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Jm ε * (Jm ε * X) = X := by
  rw [← Matrix.mul_assoc, Jm_mul_Jm', Matrix.one_mul]

theorem inG_sub (Y : Matrix (Fin n) (Fin n) ℂ) : inG ε (Y - Jm ε * Yᴴ * Jm ε) := by
  unfold inG
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Jm_conjT,
    Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, Jm_mul_Jm', Jm_Jm_mul, Matrix.mul_one]
  abel

theorem inG_add (Y : Matrix (Fin n) (Fin n) ℂ) : inG ε (Complex.I • (Y + Jm ε * Yᴴ * Jm ε)) := by
  have h := inG_sub (ε := ε) (Complex.I • Y)
  rwa [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_I, Matrix.mul_smul, Matrix.smul_mul,
    neg_smul, sub_neg_eq_add, ← smul_add] at h

section Mx

variable {W : Type*} [AddCommGroup W] [Module ℂ W] (T : Fin n → Fin n → Module.End ℂ W)

theorem mx_add (X X' : Matrix (Fin n) (Fin n) ℂ) : mx T (X + X') = mx T X + mx T X' := by
  simp [mx, add_smul, Finset.sum_add_distrib]

theorem mx_smul (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) : mx T (c • X) = c • mx T X := by
  simp [mx, smul_smul, Finset.smul_sum]

theorem mx_single (a b : Fin n) : mx T (Matrix.single a b 1) = T a b := by
  simp [mx, Matrix.single_apply, ite_smul, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem mat_decomp (Y Z : Matrix (Fin n) (Fin n) ℂ) :
    Y = (1 / 2 : ℂ) • (Y - Z) + (-(Complex.I / 2)) • (Complex.I • (Y + Z)) := by
  rw [smul_smul, show -(Complex.I / 2) * Complex.I = 1 / 2 by
    rw [neg_mul, div_mul_eq_mul_div, Complex.I_mul_I]; ring, ← smul_add, sub_add_add_cancel,
    ← two_smul ℂ Y, smul_smul]
  norm_num

theorem single_conj (a b : Fin n) :
    Jm ε * (Matrix.single a b (1 : ℂ))ᴴ * Jm ε = adjSign ε a b • Matrix.single b a 1 := by
  ext i j
  rw [Jm_eq, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_single, Matrix.smul_apply,
    Matrix.single_apply, Matrix.single_apply]
  unfold adjSign sg
  split_ifs <;> simp_all

end Mx

section Inj

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem vec_zero {x : Matrix (Fin n) (Fin n) ℂ} (hx : x ∈ UJset ε) {b : Fin n → ℂ}
    (h : ∀ ξ, ∑ c, x ξ c * b c = 0) : b = 0 := by
  have hxb : x *ᵥ b = 0 := funext fun ξ => h ξ
  have hL := (Formalism.REAL.indefinite_unitary_inv_closed n ε x hx).2
  calc b = (Formalism.REAL.Jm ε * xᴴ * Formalism.REAL.Jm ε * x) *ᵥ b := by rw [hL, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, hxb, Matrix.mulVec_zero]

theorem coef_zero (dual : Bool) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x ∈ UJset ε) {a : Fin n → ℂ}
    (h : ∀ ξ, ∑ c, wt dual ε ξ x c * a c = 0) : a = 0 := by
  cases dual
  · exact vec_zero hx h
  · have hb := vec_zero hx (b := fun c => sg ε c * star (a c)) fun ξ => by
      have := congrArg star (h ξ)
      simp only [wt, cond_true, star_sum, star_mul', star_star, star_sg, star_zero] at this
      rw [← this]
      exact Finset.sum_congr rfl fun c _ => by ring
    funext c
    have h1 := congrFun hb c
    have h2 : sg ε c * (sg ε c * star (a c)) = star (a c) := by
      rw [← mul_assoc, sg_mul_self, one_mul]
    simp only [Pi.zero_apply] at h1 ⊢
    rw [h1, mul_zero] at h2
    exact star_eq_zero.1 h2.symm

def perpPerp (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ D) :
    Submodule ℂ D where
  carrier := {v | ∀ u : H, (∀ g : Formalism.REAL.UJ ε, ∀ y ∈ V, inner ℂ u (σ (Formalism.MainNotions.S.umat g) ((y : D) : H)) = 0) →
    inner ℂ u (v : H) = 0}
  add_mem' {v w} hv hw u hu := by
    rw [Submodule.coe_add, inner_add_right, hv u hu, hw u hu, add_zero]
  zero_mem' u _ := by simp
  smul_mem' c v hv u hu := by
    rw [Submodule.coe_smul, inner_smul_right, hv u hu, mul_zero]

theorem actM_mem_perpPerp (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (V : Submodule ℂ D)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {v : D} (hv : v ∈ perpPerp ε σ V) :
    actM E X v ∈ perpPerp ε σ V := by
  intro u hu
  have hz : ∀ t : ℝ, inner ℂ u (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)) = 0 := by
    intro t
    rw [← umat_ex hX t, inner_sig hσ]
    refine hv _ fun g y hy => ?_
    rw [← sig_inner hσ (ex X hX t), sig_inv_apply hσ, ← ContinuousLinearMap.comp_apply, ← sig_mul hσ]
    exact hu _ y hy
  have hd : HasDerivAt (fun t : ℝ => inner ℂ u (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)))
      (inner ℂ u ((actM E X v : D) : H)) 0 := by
    exact ((innerSL ℂ u).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hD.deriv X hX v)
  have hf : (fun t : ℝ => inner ℂ u (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H))) = fun _ => 0 :=
    funext hz
  rw [hf] at hd
  exact hd.unique (hasDerivAt_const 0 0)

theorem genSub_le_perpPerp (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (V : Submodule ℂ D) :
    genSub E V ≤ perpPerp ε σ V := by
  refine sInf_le ⟨fun y hy u hu => ?_, fun a b v hv => ?_⟩
  · have := hu 1 y hy
    rw [umat_one, hσ.1.1] at this
    exact this
  · have hE : E a b = (1 / 2 : ℂ) • actM E (Matrix.single a b 1 - Jm ε * (Matrix.single a b 1)ᴴ * Jm ε) +
        (-(Complex.I / 2)) • actM E (Complex.I • (Matrix.single a b 1 + Jm ε * (Matrix.single a b 1)ᴴ * Jm ε)) := by
      have h1 : actM E = mx E := rfl
      rw [h1, ← mx_smul, ← mx_smul, ← mx_add, ← mat_decomp, mx_single]
    rw [hE, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply]
    exact add_mem (Submodule.smul_mem _ _ (actM_mem_perpPerp hσ hD V (inG_sub _) hv))
      (Submodule.smul_mem _ _ (actM_mem_perpPerp hσ hD V (inG_add _) hv))

theorem cf_inj (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {V : Submodule ℂ D} (dual : Bool)
    {f : Fin n → D} (hf : ∀ c, f c ∈ genSub E V)
    (h0 : ∀ y ∈ V, ∀ ξ x, cf dual ε σ ((y : D) : H) ξ (fun c => ((f c : D) : H)) x = 0) : f = 0 := by
  have ha : ∀ (x : Formalism.REAL.UJ ε), ∀ y ∈ V, ∀ c,
      inner ℂ ((y : D) : H) (σ (Formalism.MainNotions.S.umat x) ((f c : D) : H)) = 0 := by
    intro x y hy c
    have := coef_zero dual x.2 (a := fun c => inner ℂ ((y : D) : H) (σ (Formalism.MainNotions.S.umat x) ((f c : D) : H)))
      fun ξ => h0 y hy ξ x
    exact congrFun this c
  funext c
  have hmem := genSub_le_perpPerp hσ hD V (hf c)
  have hself := hmem ((f c : D) : H) fun g y hy => by
    have := ha g⁻¹ y hy c
    rw [inner_sig hσ, inv_inv] at this
    rw [inner_eq_zero_symm]
    exact this
  rw [inner_self_eq_zero] at hself
  simp only [Pi.zero_apply]
  exact_mod_cast hself

end Inj

end ReciprocityTheory.ChartRestriction.DS.UnitB
