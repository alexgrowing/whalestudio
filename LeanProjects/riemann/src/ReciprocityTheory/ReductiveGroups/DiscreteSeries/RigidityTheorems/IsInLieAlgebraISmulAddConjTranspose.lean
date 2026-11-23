import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem rq_JJ (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem rq_JH (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a = true <;> simp [h]

theorem rq_actM_add {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (X Y : Matrix (Fin n) (Fin n) ℂ) : actM E (X + Y) = actM E X + actM E Y := by
  simp [actM, add_smul, Finset.sum_add_distrib]

theorem rq_actM_smul {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) : actM E (c • X) = c • actM E X := by
  simp [actM, Finset.smul_sum, mul_smul]

theorem rq_K_unit {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    kᴴ * k = 1 ∧ k * kᴴ = 1 := by
  obtain ⟨hu, -⟩ := hk
  exact ⟨Matrix.mem_unitaryGroup_iff'.mp hu, Matrix.mem_unitaryGroup_iff.mp hu⟩

theorem rq_K_JH {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    kᴴ * Jm ε = Jm ε * kᴴ := by
  obtain ⟨h1, h2⟩ := rq_K_unit hk
  have hc : k * Jm ε = Jm ε * k := hk.2
  calc kᴴ * Jm ε = kᴴ * Jm ε * (k * kᴴ) := by rw [h2, mul_one]
    _ = kᴴ * (Jm ε * k) * kᴴ := by simp only [mul_assoc]
    _ = kᴴ * (k * Jm ε) * kᴴ := by rw [hc]
    _ = kᴴ * k * Jm ε * kᴴ := by simp only [mul_assoc]
    _ = Jm ε * kᴴ := by rw [h1, one_mul]

theorem rq_K_UJ {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    k ∈ UJset ε := by
  have hc : k * Jm ε = Jm ε * k := hk.2
  show kᴴ * Jm ε * k = Jm ε
  rw [mul_assoc, ← hc, ← mul_assoc, (rq_K_unit hk).1, one_mul]

theorem rq_KH {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    kᴴ ∈ Kset ε := by
  refine ⟨?_, rq_K_JH hk⟩
  rw [Matrix.mem_unitaryGroup_iff]
  show kᴴ * kᴴᴴ = 1
  rw [Matrix.conjTranspose_conjTranspose]
  exact (rq_K_unit hk).1

theorem rq_UJ_mul {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UJset ε)
    (hb : b ∈ UJset ε) : a * b ∈ UJset ε := by
  have ha' : aᴴ * Jm ε * a = Jm ε := ha
  have hb' : bᴴ * Jm ε * b = Jm ε := hb
  show (a * b)ᴴ * Jm ε * (a * b) = Jm ε
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by simp only [mul_assoc]
    _ = Jm ε := by rw [ha', hb']

theorem rq_inG_conj {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) : inG ε (k * X * kᴴ) := by
  have hX' : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  have hc : k * Jm ε = Jm ε * k := hk.2
  have hc' := rq_K_JH hk
  show (k * X * kᴴ)ᴴ * Jm ε + Jm ε * (k * X * kᴴ) = 0
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc _ = k * (Xᴴ * Jm ε + Jm ε * X) * kᴴ := by
        rw [mul_add, add_mul]
        simp only [mul_assoc]
        rw [hc', ← mul_assoc (Jm ε) k, ← hc, mul_assoc]
    _ = 0 := by rw [hX', mul_zero, zero_mul]

theorem rq_exp_mem (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) (hX : inG ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ UJset ε := by
  have hJJ := rq_JJ ε
  have hJinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJJ
  have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJJ, hJJ⟩, rfl⟩
  have hX' : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  have hXH : Xᴴ = -(Jm ε * X * Jm ε) := by
    calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [mul_assoc, hJJ, mul_one]
      _ = -(Jm ε * X * Jm ε) := by rw [eq_neg_of_add_eq_zero_left hX', neg_mul]
  have hAH : ((t : ℂ) • X)ᴴ = Jm ε * (-((t : ℂ) • X)) * (Jm ε)⁻¹ := by
    rw [hJinv, Matrix.conjTranspose_smul, hXH]
    simp only [Complex.star_def, Complex.conj_ofReal, mul_neg, neg_mul, Matrix.mul_smul, Matrix.smul_mul,
      smul_neg]
  have hEu : IsUnit (NormedSpace.exp ((t : ℂ) • X)) := Matrix.isUnit_exp _
  show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Jm ε * NormedSpace.exp ((t : ℂ) • X) = Jm ε
  rw [← Matrix.exp_conjTranspose, hAH, Matrix.exp_conj _ _ hJu, hJinv, Matrix.exp_neg]
  simp only [mul_assoc]
  rw [← mul_assoc (Jm ε) (Jm ε), hJJ, one_mul,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hEu), mul_one]

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem rq_main_G {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ)
    {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D} (hD : IsDerivedOn ε σ D E)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    (v : D) :
    σ k ((actM E X v : D) : H) =
      ((actM E (k * X * kᴴ) ⟨σ k (v : H), hD.kStable k hk v v.2⟩ : D) : H) := by
  have hkU := rq_K_unit hk
  have hkUJ := rq_K_UJ hk
  have hkHUJ := rq_K_UJ (rq_KH hk)
  have hkinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv hkU.1
  have hku : IsUnit k := ⟨⟨k, kᴴ, hkU.2, hkU.1⟩, rfl⟩
  have h2 := hD.deriv (k * X * kᴴ) (rq_inG_conj hk hX) ⟨σ k (v : H), hD.kStable k hk v v.2⟩
  have h1 : HasDerivAt (fun t : ℝ => σ k (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)))
      (σ k ((actM E X v : D) : H)) 0 := by
    have := ((σ k).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hD.deriv X hX v)
    simpa [Function.comp_def] using this
  have hfun : (fun t : ℝ => σ k (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H))) =
      fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • (k * X * kᴴ))) (σ k (v : H)) := by
    funext t
    have heUJ := rq_exp_mem ε X hX t
    have hexp : NormedSpace.exp ((t : ℂ) • (k * X * kᴴ)) = k * NormedSpace.exp ((t : ℂ) • X) * kᴴ := by
      rw [← hkinv, ← Matrix.exp_conj _ _ hku, Matrix.mul_smul, Matrix.smul_mul]
    rw [hexp]
    have e1 : σ (k * NormedSpace.exp ((t : ℂ) • X) * kᴴ * k) =
        (σ (k * NormedSpace.exp ((t : ℂ) • X) * kᴴ)).comp (σ k) :=
      hσ.1.2 _ (rq_UJ_mul (rq_UJ_mul hkUJ heUJ) hkHUJ) k hkUJ
    rw [mul_assoc (k * NormedSpace.exp ((t : ℂ) • X)), hkU.1, mul_one, hσ.1.2 k hkUJ _ heUJ] at e1
    exact congrArg (fun L : H →L[ℂ] H => L (v : H)) e1
  rw [hfun] at h1
  exact h1.unique h2

end Rep

theorem rq_inG_S (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inG ε (X - Jm ε * Xᴴ * Jm ε) := by
  have hJJ := rq_JJ ε
  have hJH := rq_JH ε
  show (X - Jm ε * Xᴴ * Jm ε)ᴴ * Jm ε + Jm ε * (X - Jm ε * Xᴴ * Jm ε) = 0
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hJH, Matrix.conjTranspose_conjTranspose,
    sub_mul, mul_sub, mul_assoc, hJJ, mul_one]
  rw [← mul_assoc (Jm ε) (Jm ε), hJJ, one_mul]
  abel

theorem isInLieAlgebra_I_smul_add_conjTranspose (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inG ε (Complex.I • (X + Jm ε * Xᴴ * Jm ε)) := by
  have hJJ := rq_JJ ε
  have hJH := rq_JH ε
  show (Complex.I • (X + Jm ε * Xᴴ * Jm ε))ᴴ * Jm ε + Jm ε * (Complex.I • (X + Jm ε * Xᴴ * Jm ε)) = 0
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hJH,
    Matrix.conjTranspose_conjTranspose, Complex.star_def, Complex.conj_I, Matrix.smul_mul, Matrix.mul_smul,
    add_mul, mul_add, mul_assoc, hJJ, mul_one]
  rw [← mul_assoc (Jm ε) (Jm ε), hJJ, one_mul, neg_smul, add_comm (Jm ε * X) (Xᴴ * Jm ε), neg_add_cancel]

theorem rq_decomp (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    (1 / 2 : ℂ) • (X - Jm ε * Xᴴ * Jm ε) + (-(Complex.I / 2)) • (Complex.I • (X + Jm ε * Xᴴ * Jm ε))
      = X := by
  have h : -(Complex.I / 2) * Complex.I = 1 / 2 := by
    rw [neg_mul, div_mul_eq_mul_div, Complex.I_mul_I]
    ring
  rw [smul_smul, h, ← smul_add, sub_add_add_cancel, ← two_smul ℂ X, smul_smul]
  norm_num

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem rq_lin {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D} (hD : IsDerivedOn ε σ D E)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (v : D) (a b : ℂ)
    {S T : Matrix (Fin n) (Fin n) ℂ}
    (hS : σ k ((actM E S v : D) : H) =
      ((actM E (k * S * kᴴ) ⟨σ k (v : H), hD.kStable k hk v v.2⟩ : D) : H))
    (hT : σ k ((actM E T v : D) : H) =
      ((actM E (k * T * kᴴ) ⟨σ k (v : H), hD.kStable k hk v v.2⟩ : D) : H)) :
    σ k ((actM E (a • S + b • T) v : D) : H) =
      ((actM E (k * (a • S + b • T) * kᴴ) ⟨σ k (v : H), hD.kStable k hk v v.2⟩ : D) : H) := by
  have e1 : k * (a • S + b • T) * kᴴ = a • (k * S * kᴴ) + b • (k * T * kᴴ) := by
    simp only [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [e1, rq_actM_add, rq_actM_add, rq_actM_smul, rq_actM_smul, rq_actM_smul, rq_actM_smul]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, map_add, map_smul,
    hS, hT]

end Rep

theorem derived_adK {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D} (hD : IsDerivedOn ε σ D E)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (X : Matrix (Fin n) (Fin n) ℂ) (v : D) :
    σ k ((actM E X v : D) : H) =
      ((actM E (k * X * kᴴ) ⟨σ k (v : H), hD.kStable k hk v v.2⟩ : D) : H) := by
  have hS := rq_main_G hσ hD hk (rq_inG_S ε X) v
  have hT := rq_main_G hσ hD hk (isInLieAlgebra_I_smul_add_conjTranspose ε X) v
  have := rq_lin hD hk v (1 / 2 : ℂ) (-(Complex.I / 2)) hS hT
  rwa [rq_decomp] at this

end ReciprocityTheory.ChartRestriction.DS
