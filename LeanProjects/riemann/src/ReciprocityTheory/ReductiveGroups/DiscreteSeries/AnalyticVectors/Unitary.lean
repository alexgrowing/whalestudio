import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem actM_add' {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (X Y : Matrix (Fin n) (Fin n) ℂ) : actM E (X + Y) = actM E X + actM E Y := by
  simp [actM, add_smul, Finset.sum_add_distrib]

theorem actM_smul' {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) : actM E (c • X) = c • actM E X := by
  simp [actM, Finset.smul_sum, mul_smul]

theorem inner_map_map_of_isURep (hσ : IsURepOn (UJset ε) σ) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) (x y : H) : inner ℂ (σ g x) (σ g y) = inner ℂ x y := by
  unfold IsURepOn at hσ
  let L : H →ₗᵢ[ℂ] H := { toLinearMap := (σ g).toLinearMap, norm_map' := hσ.2.1 g hg }
  exact L.inner_map_map x y

theorem inner_actM_add_inner_actM (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (v w : D) :
    inner ℂ (actM E X v) w + inner ℂ v (actM E X w) = 0 := by
  have hσ' := hσ
  unfold IsURepOn at hσ'
  obtain ⟨-, -, hder⟩ := hD
  have hd := (hder X hX v).inner ℂ (hder X hX w)
  have hc : HasDerivAt (fun t : ℝ => inner ℂ ((σ (NormedSpace.exp ((t : ℂ) • X))) (v : H))
      ((σ (NormedSpace.exp ((t : ℂ) • X))) (w : H))) 0 0 := by
    have e : (fun t : ℝ => inner ℂ ((σ (NormedSpace.exp ((t : ℂ) • X))) (v : H))
        ((σ (NormedSpace.exp ((t : ℂ) • X))) (w : H))) = fun _ => inner ℂ (v : H) (w : H) := by
      funext t
      exact inner_map_map_of_isURep hσ (exp_smul_mem_UJset hX t) _ _
    rw [e]
    exact hasDerivAt_const _ _
  have h0 := hd.unique hc
  simp [hσ'.1.1] at h0
  first
    | (rw [Submodule.coe_inner, Submodule.coe_inner]; linear_combination h0)
    | (simpa [add_comm] using h0)

theorem actM_single' {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (a b : Fin n) : actM E (Matrix.single a b 1) = E a b := by
  simp [actM, Matrix.single_apply, ite_smul]
  rw [Finset.sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  simp

theorem Jm_conjTranspose (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  ext i j
  simp [Jm, Matrix.diagonal_apply, Matrix.conjTranspose_apply] <;> split_ifs <;> simp_all

theorem Jm_mul_Jm (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  ext i j
  simp [Jm, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp_all

theorem Jm_mul_Jm_mul (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Jm ε * (Jm ε * X) = X := by
  rw [← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]

theorem inG_sub_theta (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    inG ε (M - Jm ε * Mᴴ * Jm ε) := by
  unfold inG
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Jm_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, Jm_mul_Jm,
    Jm_mul_Jm_mul, Matrix.mul_one] <;> abel

theorem inG_add_theta (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    inG ε ((-Complex.I) • (M + Jm ε * Mᴴ * Jm ε)) := by
  unfold inG
  have hs : star (-Complex.I) = Complex.I := by simp
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Jm_conjTranspose, Matrix.conjTranspose_conjTranspose, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc, Jm_mul_Jm, Jm_mul_Jm_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul]
  rw [hs, neg_smul, smul_add, smul_add]
  abel

theorem inner_actM_eq (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (M : Matrix (Fin n) (Fin n) ℂ) (x y : D) :
    inner ℂ (actM E M x) y = inner ℂ x (actM E (Jm ε * Mᴴ * Jm ε) y) := by
  have skA := inner_actM_add_inner_actM hσ hD (inG_sub_theta ε M) x y
  have skB := inner_actM_add_inner_actM hσ hD (inG_add_theta ε M) x y
  have hc : Complex.I / 2 * -Complex.I = 1 / 2 := by
    rw [div_mul_eq_mul_div, mul_neg, Complex.I_mul_I]
    norm_num
  have hM : M = (1 / 2 : ℂ) • (M - Jm ε * Mᴴ * Jm ε) +
      (Complex.I / 2) • ((-Complex.I) • (M + Jm ε * Mᴴ * Jm ε)) := by
    rw [smul_smul, hc]
    first
      | module
      | (ext i j; simp; ring)
  have hT : Jm ε * Mᴴ * Jm ε = (-(1 / 2) : ℂ) • (M - Jm ε * Mᴴ * Jm ε) +
      (Complex.I / 2) • ((-Complex.I) • (M + Jm ε * Mᴴ * Jm ε)) := by
    rw [smul_smul, hc]
    first
      | module
      | (ext i j; simp; ring)
  rw [hT]
  conv_lhs => rw [hM]
  rw [actM_add', actM_add', actM_smul' E (1 / 2 : ℂ), actM_smul' E (-(1 / 2) : ℂ),
    actM_smul' E (Complex.I / 2)]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, map_div₀, map_one, map_ofNat, Complex.conj_I]
  linear_combination (1 / 2 : ℂ) * skA - (Complex.I / 2) * skB

theorem theta_single (ε : Fin n → Bool) (a b : Fin n) :
    Jm ε * (Matrix.single a b (1 : ℂ))ᴴ * Jm ε = adjSign ε a b • Matrix.single b a 1 := by
  ext i j
  simp [Jm, adjSign, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply,
    Matrix.conjTranspose_apply, Matrix.smul_apply] <;> split_ifs <;> simp_all

theorem isInfUnitary_of_isDerivedOn (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) :
    IsInfUnitary ε E := by
  unfold IsInfUnitary
  intro a b v w
  rw [← actM_single' E a b, inner_actM_eq hσ hD, theta_single, actM_smul', actM_single']
  rw [LinearMap.smul_apply, inner_smul_right]

end Rep

end ReciprocityTheory.ChartRestriction.DS
