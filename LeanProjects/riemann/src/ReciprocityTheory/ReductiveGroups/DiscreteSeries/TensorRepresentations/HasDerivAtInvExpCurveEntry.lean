import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CoefOfEmb
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.IsSmoothL2OfCasimirEigen
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IntegrableComplexContinuousBoundedSupport
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Mat

variable {ε : Fin n → Bool}

theorem J_mul_J_eq_one (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem unitary_group_inv_eq_conj {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : g⁻¹ = Jm ε * gᴴ * Jm ε := by
  apply Matrix.inv_eq_left_inv
  unfold inUJ at hg
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg, J_mul_J_eq_one]

theorem J_conj_entry (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) (d c : Fin n) :
    (Jm ε * A * Jm ε) d c = (if ε d then 1 else -1) * A d c * (if ε c then 1 else -1) := by
  simp [Jm, Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem J_conj_neg_mul_inv {g X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    Jm ε * (g * X)ᴴ * Jm ε = -(X * (Jm ε * gᴴ * Jm ε)) := by
  unfold inG at hX
  have h1 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left hX
  have h2 : Jm ε * Xᴴ * Jm ε = -X := by
    rw [Matrix.mul_assoc, h1, Matrix.mul_neg, ← Matrix.mul_assoc, J_mul_J_eq_one, Matrix.one_mul]
  have h3 : Jm ε * (g * X)ᴴ * Jm ε = (Jm ε * Xᴴ * Jm ε) * (Jm ε * gᴴ * Jm ε) := by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Jm ε) (Jm ε), J_mul_J_eq_one, Matrix.one_mul]
  rw [h3, h2, Matrix.neg_mul]

theorem hasDerivAt_exp_curve_entry (g X : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) :
    HasDerivAt (fun t : ℝ => (g * NormedSpace.exp ((t : ℂ) • X)) c d) ((g * X) c d) 0 := by
  have h := Formalism.REAL.hasDerivAt_mul_exp_smul_zero g X
  exact hasDerivAt_pi.1 (hasDerivAt_pi.1 h c) d

theorem hasDerivAt_inv_exp_curve_entry {g X : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hX : inG ε X) (d c : Fin n) :
    HasDerivAt (fun t : ℝ => (g * NormedSpace.exp ((t : ℂ) • X))⁻¹ d c) (-(X * g⁻¹) d c) 0 := by
  have hcur : ∀ t : ℝ, inUJ ε (g * NormedSpace.exp ((t : ℂ) • X)) := fun t =>
    smd_inUJ_mul hg (exp_smul_mem_UJset hX t)
  have hfun : (fun t : ℝ => (g * NormedSpace.exp ((t : ℂ) • X))⁻¹ d c) = fun t : ℝ =>
      (if ε d then 1 else -1) * star ((g * NormedSpace.exp ((t : ℂ) • X)) c d) * (if ε c then 1 else -1) := by
    funext t
    rw [unitary_group_inv_eq_conj (hcur t), J_conj_entry, Matrix.conjTranspose_apply]
  have e : (-(X * g⁻¹)) d c = (if ε d then 1 else -1) * star ((g * X) c d) * (if ε c then 1 else -1) := by
    have e1 := J_conj_neg_mul_inv (g := g) hX
    rw [unitary_group_inv_eq_conj hg, ← e1, J_conj_entry, Matrix.conjTranspose_apply]
  rw [hfun]
  exact ((((hasDerivAt_exp_curve_entry g X c d).star).const_mul _).mul_const _).congr_deriv e.symm

end Mat

section Coef

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem hasDerivAt_inner_rep_exp (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {g X : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hX : inG ε X) (w : H) (v : D) :
    HasDerivAt (fun t : ℝ => inner ℂ w (σ (g * NormedSpace.exp ((t : ℂ) • X)) (v : H)))
      (inner ℂ w (σ g ((actM E X v : D) : H))) 0 := by
  set L : H →L[ℝ] ℂ := ((innerSL ℂ w).comp (σ g)).restrictScalars ℝ with hL
  have h1 : (fun t : ℝ => inner ℂ w (σ (g * NormedSpace.exp ((t : ℂ) • X)) (v : H))) =
      fun t : ℝ => L (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)) := by
    funext t
    rw [hσ.1.2 _ hg _ (exp_smul_mem_UJset hX t)]
    simp [hL, innerSL_apply_apply]
  rw [h1]
  have h2 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hD.deriv X hX v)
  exact h2.congr_deriv (by simp [hL, innerSL_apply_apply])

def oa1Phi (dual : Bool) (g : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) : ℂ := cond dual ((g⁻¹) d c) (g c d)

def oa1DPhi (dual : Bool) (g X : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) : ℂ :=
  cond dual ((-(X * g⁻¹)) d c) ((g * X) c d)

theorem hasDerivAt_tensor_phi {g X : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hX : inG ε X) (dual : Bool)
    (c d : Fin n) :
    HasDerivAt (fun t : ℝ => oa1Phi dual (g * NormedSpace.exp ((t : ℂ) • X)) c d) (oa1DPhi dual g X c d) 0 := by
  cases dual
  · exact hasDerivAt_exp_curve_entry g X c d
  · exact hasDerivAt_inv_exp_curve_entry hg hX d c

theorem tensor_coef_expand (dual : Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (η f : Fin n → H)
    (g : Matrix (Fin n) (Fin n) ℂ) :
    ∑ c, inner ℂ (η c) (tensGrp dual σ g f c) = ∑ c, ∑ d, oa1Phi dual g c d * inner ℂ (η c) (σ g (f d)) := by
  simp [tensGrp, oa1Phi, inner_sum]

theorem hasDerivAt_tensor_coef (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {g X : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hX : inG ε X) (dual : Bool) (η : Fin n → H)
    (f : Fin n → D) :
    HasDerivAt (fun t : ℝ => ∑ c, inner ℂ (η c)
        (tensGrp dual σ (g * NormedSpace.exp ((t : ℂ) • X)) (fun d => (f d : H)) c))
      (∑ c, ∑ d, (oa1DPhi dual g X c d * inner ℂ (η c) (σ g (f d : H)) +
        oa1Phi dual g c d * inner ℂ (η c) (σ g ((actM E X (f d) : D) : H)))) 0 := by
  have h := HasDerivAt.fun_sum (u := univ) (fun c _ => HasDerivAt.fun_sum (u := univ) (fun d _ =>
    (hasDerivAt_tensor_phi hg hX dual c d).mul (hasDerivAt_inner_rep_exp hσ hD hg hX (η c) (f d))))
  simp only [Formalism.REAL.mul_exp_zero_smul_eq] at h
  have e : (fun t : ℝ => ∑ c, inner ℂ (η c)
        (tensGrp dual σ (g * NormedSpace.exp ((t : ℂ) • X)) (fun d => (f d : H)) c)) =
      fun t : ℝ => ∑ c, ∑ d, oa1Phi dual (g * NormedSpace.exp ((t : ℂ) • X)) c d *
        inner ℂ (η c) (σ (g * NormedSpace.exp ((t : ℂ) • X)) (f d : H)) := by
    funext t
    exact tensor_coef_expand dual σ η _ _
  rw [e]
  exact h

end Coef

section Eab

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem tensor_dphi_complex_comb (dual : Bool) (g : Matrix (Fin n) (Fin n) ℂ) (a b c d : Fin n) :
    oa1DPhi dual g (Formalism.REAL.cpart1 ε (Matrix.single a b 1)) c d +
        Complex.I * oa1DPhi dual g (Formalism.REAL.cpart2 ε (Matrix.single a b 1)) c d =
      cond dual (-(if d = a then (g⁻¹) b c else 0)) (if d = b then g c a else 0) := by
  have hZ := (Formalism.REAL.complex_parts_mem_lie_algebra_holds _ ε (Matrix.single a b (1 : ℂ))).2.2.1
  set X1 := Formalism.REAL.cpart1 ε (Matrix.single a b (1 : ℂ))
  set X2 := Formalism.REAL.cpart2 ε (Matrix.single a b (1 : ℂ))
  cases dual
  · have h3 : g * X1 + Complex.I • (g * X2) = g * Matrix.single a b 1 := by
      rw [hZ, Matrix.mul_add, Matrix.mul_smul]
    have h4 := congrFun (congrFun h3 c) d
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h4
    simp only [oa1DPhi, cond_false]
    rw [h4]
    by_cases h : d = b
    · subst h; simp [Matrix.mul_apply, Matrix.single_apply]
    · simp [Matrix.mul_apply, Matrix.single_apply, h, Ne.symm h]
  · have h3 : X1 * g⁻¹ + Complex.I • (X2 * g⁻¹) = Matrix.single a b 1 * g⁻¹ := by
      rw [hZ, Matrix.add_mul, Matrix.smul_mul]
    have h4 := congrFun (congrFun h3 d) c
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h4
    simp only [oa1DPhi, cond_true, Matrix.neg_apply]
    rw [show -(X1 * g⁻¹) d c + Complex.I * -(X2 * g⁻¹) d c = -((X1 * g⁻¹) d c + Complex.I * (X2 * g⁻¹) d c) by
      ring, h4]
    by_cases h : d = a
    · subst h; simp [Matrix.mul_apply, Matrix.single_apply]
    · simp [Matrix.mul_apply, h, Ne.symm h]

theorem tensor_coef_Eab_action (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (η : Fin n → H)
    (f : Fin n → D) (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Eab ε a b (fun x => ∑ c, inner ℂ (η c) (tensGrp dual σ x (fun d => (f d : H)) c)) g =
      ∑ c, inner ℂ (η c) (tensGrp dual σ g (fun d => (tensF dual E a b f d : H)) c) := by
  have hg' : inUJ ε g := hg
  rw [Formalism.REAL.lie_derivative_def]
  unfold Formalism.REAL.Rd
  rw [(hasDerivAt_tensor_coef hσ hD hg' (Formalism.REAL.real_part_single_mem ε a b) dual η f).deriv,
    (hasDerivAt_tensor_coef hσ hD hg' (Formalism.REAL.imaginary_part_single_mem ε a b) dual η f).deriv]
  have hZ := (Formalism.REAL.complex_parts_mem_lie_algebra_holds _ ε (Matrix.single a b (1 : ℂ))).2.2.1
  have key : E a b = actM E (Formalism.REAL.cpart1 ε (Matrix.single a b 1)) +
      Complex.I • actM E (Formalism.REAL.cpart2 ε (Matrix.single a b 1)) := by
    rw [← actM_single' E a b, ← actM_smul', ← actM_add', ← hZ]
  have hterm : ∀ c d,
      (oa1DPhi dual g (Formalism.REAL.cpart1 ε (Matrix.single a b 1)) c d * inner ℂ (η c) (σ g (f d : H)) +
        oa1Phi dual g c d * inner ℂ (η c) (σ g ((actM E (Formalism.REAL.cpart1 ε (Matrix.single a b 1)) (f d) : D) : H))) +
      Complex.I * (oa1DPhi dual g (Formalism.REAL.cpart2 ε (Matrix.single a b 1)) c d * inner ℂ (η c) (σ g (f d : H)) +
        oa1Phi dual g c d * inner ℂ (η c) (σ g ((actM E (Formalism.REAL.cpart2 ε (Matrix.single a b 1)) (f d) : D) : H))) =
      cond dual (-(if d = a then (g⁻¹) b c else 0)) (if d = b then g c a else 0) * inner ℂ (η c) (σ g (f d : H)) +
        oa1Phi dual g c d * inner ℂ (η c) (σ g ((E a b (f d) : D) : H)) := by
    intro c d
    rw [← tensor_dphi_complex_comb dual g a b c d, key]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, map_add,
      map_smul, inner_add_right, inner_smul_right]
    ring
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, hterm]
  rw [tensor_coef_expand]
  refine Finset.sum_congr rfl fun c _ => ?_
  cases dual
  · simp only [cond_false, tensF, tensV_coord, oa1Phi, Submodule.coe_add, map_add, inner_add_right, mul_add,
      Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [add_comm]
    congr 1
    rw [Finset.sum_eq_single a (fun d _ hd => by simp [hd]) (by simp)]
    simp
  · have hR : ∀ d, oa1Phi true g c d * inner ℂ (η c) (σ g ((tensF true E a b f d : D) : H)) =
        oa1Phi true g c d * inner ℂ (η c) (σ g ((E a b (f d) : D) : H)) -
          (if d = b then oa1Phi true g c b * inner ℂ (η c) (σ g (f a : H)) else 0) := by
      intro d
      simp only [tensF, cond_true, tensVd_coord]
      by_cases h : d = b
      · subst h; simp [mul_sub, inner_sub_right]
      · simp [h]
    have hL : ∀ d, cond true (-(if d = a then (g⁻¹) b c else 0)) (if d = b then g c a else 0) *
        inner ℂ (η c) (σ g (f d : H)) = -(if d = a then (g⁻¹) b c * inner ℂ (η c) (σ g (f a : H)) else 0) := by
      intro d
      by_cases h : d = a
      · subst h; simp
      · simp [h]
    simp only [hL, hR]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, oa1Phi, cond_true]
    ring

end Eab

end ReciprocityTheory.ChartRestriction.DS
