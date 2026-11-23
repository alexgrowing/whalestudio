import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExHua

noncomputable section

namespace HcInf

open HcS.BasicNotions Matrix

section MatDet

variable {n : Type} [Fintype n] [DecidableEq n]

theorem det_mulRight_mat (B : Matrix n n ℂ) :
    LinearMap.det (LinearMap.mulRight ℂ B : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) =
      B.det ^ Fintype.card n := by
  classical
  let e : Matrix n n ℂ ≃ₗ[ℂ] (n → n → ℂ) :=
    { toFun := fun X i j => X i j
      invFun := fun v => Matrix.of v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let g : (n → n → ℂ) →ₗ[ℂ] (n → n → ℂ) :=
    LinearMap.pi fun i => (Matrix.toLin' Bᵀ).comp (LinearMap.proj i)
  have key : (LinearMap.mulRight ℂ B : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) =
      (e.symm : (n → n → ℂ) →ₗ[ℂ] Matrix n n ℂ).comp
        (g.comp (e.symm.symm : Matrix n n ℂ →ₗ[ℂ] (n → n → ℂ))) := by
    refine LinearMap.ext fun X => ?_
    refine Matrix.ext fun i j => ?_
    rw [LinearMap.mulRight_apply, Matrix.mul_apply]
    change ∑ k, X i k * B k j = ∑ k, B k j * X i k
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [key, LinearMap.det_conj, LinearMap.det_pi]
  simp [LinearMap.det_toLin', Matrix.det_transpose]

theorem det_mulLeft_mat (A : Matrix n n ℂ) :
    LinearMap.det (LinearMap.mulLeft ℂ A : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) =
      A.det ^ Fintype.card n := by
  classical
  let e : Matrix n n ℂ ≃ₗ[ℂ] Matrix n n ℂ := Matrix.transposeLinearEquiv n n ℂ ℂ
  have key : (LinearMap.mulLeft ℂ A : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) =
      (e : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ).comp
        ((LinearMap.mulRight ℂ Aᵀ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ).comp
          (e.symm : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)) := by
    refine LinearMap.ext fun X => ?_
    simp [e, Matrix.transpose_mul]
  rw [key, LinearMap.det_conj, det_mulRight_mat, Matrix.det_transpose]

end MatDet

section Real

variable {P Q : ℕ}

local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ

def sigJ (W : Mat) : Mat := HcS.UG.Jpq P Q * Wᴴ * HcS.UG.Jpq P Q

theorem Jpq_mul_mul (X : Mat) : HcS.UG.Jpq P Q * (HcS.UG.Jpq P Q * X) = X := by
  rw [← Matrix.mul_assoc]
  simp [HcS.UG.Jpq, Matrix.fromBlocks_multiply]

theorem sigJ_add (V W : Mat) : sigJ (V + W) = sigJ V + sigJ W := by
  simp only [sigJ, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]

theorem sigJ_smul (c : ℂ) (W : Mat) : sigJ (c • W) = star c • sigJ W := by
  simp only [sigJ, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem sigJ_sigJ (W : Mat) : sigJ (sigJ W) = W := by
  have hJ : (HcS.UG.Jpq P Q)ᴴ = HcS.UG.Jpq P Q := by
    simp [HcS.UG.Jpq, Matrix.fromBlocks_conjTranspose]
  have hJJ : HcS.UG.Jpq P Q * HcS.UG.Jpq P Q = 1 := by
    simpa using Jpq_mul_mul (P := P) (Q := Q) 1
  simp only [sigJ, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ,
    Matrix.mul_assoc, Jpq_mul_mul, hJJ, Matrix.mul_one]

theorem mem_lieU_iff_sigJ (X : Mat) : X ∈ lieU P Q ↔ sigJ X = -X := by
  show Xᴴ * HcS.UG.Jpq P Q + HcS.UG.Jpq P Q * X = 0 ↔ HcS.UG.Jpq P Q * Xᴴ * HcS.UG.Jpq P Q = -X
  constructor
  · intro h
    have h' : Xᴴ * HcS.UG.Jpq P Q = -(HcS.UG.Jpq P Q * X) := eq_neg_of_add_eq_zero_left h
    rw [Matrix.mul_assoc, h', Matrix.mul_neg, Jpq_mul_mul]
  · intro h
    have e1 : HcS.UG.Jpq P Q * (Xᴴ * HcS.UG.Jpq P Q) = -X := by
      rw [← Matrix.mul_assoc]
      exact h
    calc Xᴴ * HcS.UG.Jpq P Q + HcS.UG.Jpq P Q * X
        = HcS.UG.Jpq P Q * (HcS.UG.Jpq P Q * (Xᴴ * HcS.UG.Jpq P Q)) + HcS.UG.Jpq P Q * X := by
          rw [Jpq_mul_mul]
      _ = 0 := by rw [e1, Matrix.mul_neg, neg_add_cancel]

def cplx : (lieU P Q × lieU P Q) →ₗ[ℝ] Mat where
  toFun p := ((p.1 : lieU P Q) : Mat) + Complex.I • ((p.2 : lieU P Q) : Mat)
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, smul_add]
    abel
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, RingHom.id_apply, smul_add]
    rw [smul_comm c Complex.I]

theorem cplx_apply (p : lieU P Q × lieU P Q) :
    cplx p = ((p.1 : lieU P Q) : Mat) + Complex.I • ((p.2 : lieU P Q) : Mat) := rfl

theorem cplx_injective : Function.Injective (cplx (P := P) (Q := Q)) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨⟨Y, hY⟩, ⟨Z, hZ⟩⟩ h
  have h1 : Y + Complex.I • Z = 0 := h
  have hY' : sigJ Y = -Y := (mem_lieU_iff_sigJ Y).1 hY
  have hZ' : sigJ Z = -Z := (mem_lieU_iff_sigJ Z).1 hZ
  have hs : star Complex.I = -Complex.I := by simp [Complex.star_def]
  have h2 : -Y + Complex.I • Z = 0 := by
    have h3 : sigJ (Y + Complex.I • Z) = 0 := by
      rw [h1]; simp [sigJ]
    rw [sigJ_add, sigJ_smul, hY', hZ', hs, neg_smul_neg] at h3
    exact h3
  have hY0 : Y = 0 := by
    have h4 : (2 : ℂ) • Y = 0 := by
      rw [two_smul]
      calc Y + Y = (Y + Complex.I • Z) - (-Y + Complex.I • Z) := by abel
        _ = 0 := by rw [h1, h2, sub_zero]
    exact (smul_eq_zero.1 h4).resolve_left two_ne_zero
  have hZ0 : Z = 0 := by
    rw [hY0, zero_add] at h1
    exact (smul_eq_zero.1 h1).resolve_left Complex.I_ne_zero
  subst hY0
  subst hZ0
  rfl

theorem cplx_surjective : Function.Surjective (cplx (P := P) (Q := Q)) := by
  intro W
  have hsub : ∀ V U : Mat, sigJ (V - U) = sigJ V - sigJ U := by
    intro V U
    simp only [sigJ, Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
  have hh : star ((1 : ℂ) / 2) = 1 / 2 := by simp
  have hi : star (-Complex.I / 2) = Complex.I / 2 := by simp [Complex.star_def]
  have hI2 : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    rw [mul_div_assoc', mul_neg, Complex.I_mul_I, neg_neg]
  have hY : ((1 : ℂ) / 2) • (W - sigJ W) ∈ lieU P Q := by
    rw [mem_lieU_iff_sigJ, sigJ_smul, hsub, sigJ_sigJ, hh, ← smul_neg, neg_sub]
  have hZ : (-Complex.I / 2) • (W + sigJ W) ∈ lieU P Q := by
    rw [mem_lieU_iff_sigJ, sigJ_smul, sigJ_add, sigJ_sigJ, hi, ← neg_smul, add_comm (sigJ W)]
    congr 1
    ring
  refine ⟨(⟨_, hY⟩, ⟨_, hZ⟩), ?_⟩
  rw [cplx_apply]
  show ((1 : ℂ) / 2) • (W - sigJ W) + Complex.I • ((-Complex.I / 2) • (W + sigJ W)) = W
  rw [smul_smul, hI2, ← smul_add,
    show W - sigJ W + (W + sigJ W) = (2 : ℂ) • W by rw [two_smul]; abel, smul_smul]
  norm_num

def cplxE : (lieU P Q × lieU P Q) ≃ₗ[ℝ] Mat :=
  LinearEquiv.ofBijective cplx ⟨cplx_injective, cplx_surjective⟩

theorem cplxE_apply (p : lieU P Q × lieU P Q) : cplxE p = cplx p := rfl

end Real

theorem det_ayb : DetAYB := by
  intro P Q A B L hL
  classical
  let M : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ →ₗ[ℂ] Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
    (LinearMap.mulLeft ℂ A).comp (LinearMap.mulRight ℂ B)
  have hM : LinearMap.det M = (A.det * B.det) ^ (P + Q) := by
    rw [LinearMap.det_comp, det_mulLeft_mat, det_mulRight_mat, mul_pow, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
  have key : ((cplxE (P := P) (Q := Q) : (lieU P Q × lieU P Q) →ₗ[ℝ] _).comp
      ((L.prodMap L).comp ((cplxE (P := P) (Q := Q)).symm :
        Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ →ₗ[ℝ] (lieU P Q × lieU P Q)))) =
      M.restrictScalars ℝ := by
    refine LinearMap.ext fun W => ?_
    obtain ⟨p, rfl⟩ := (cplxE (P := P) (Q := Q)).surjective W
    show cplxE ((L.prodMap L) ((cplxE (P := P) (Q := Q)).symm (cplxE p))) = A * (cplxE p * B)
    rw [LinearEquiv.symm_apply_apply, cplxE_apply, cplxE_apply, cplx_apply, cplx_apply]
    show ((L p.1 : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
        Complex.I • ((L p.2 : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) =
      A * ((((p.1 : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
        Complex.I • ((p.2 : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) * B)
    rw [hL, hL, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_assoc, Matrix.mul_assoc]
  have h2 : LinearMap.det (L.prodMap L) = Algebra.norm ℝ (LinearMap.det M) := by
    rw [← LinearMap.det_conj (L.prodMap L) (cplxE (P := P) (Q := Q)), key,
      LinearMap.det_restrictScalars]
  rw [LinearMap.det_prodMap, hM, Algebra.norm_complex_apply] at h2
  have h3 : |LinearMap.det L| ^ 2 = (‖A.det‖ ^ (P + Q) * ‖B.det‖ ^ (P + Q)) ^ 2 := by
    rw [sq_abs, sq, h2, Complex.normSq_eq_norm_sq, norm_pow, norm_mul]
    ring
  exact (pow_left_inj₀ (abs_nonneg _) (by positivity) two_ne_zero).1 h3

theorem huaInv_of_tauDeriv (h2 : TauDeriv) : HuaInv := huaInv_of det_ayb h2

end HcInf
