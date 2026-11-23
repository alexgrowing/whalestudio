import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOfTrivialInteger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRightTranslation

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.R
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.RSKernel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def mt (r₁ r₃ : Fin 2 → F) : Matrix (Fin 2) (Fin 2) F := !![r₁ 0, r₃ 0; r₁ 1, r₃ 1]

def sw (D : F) : Matrix (Fin 2) (Fin 2) F := !![0, D; -D, 0]

theorem mt_det (r₁ r₃ : Fin 2 → F) : (mt r₁ r₃).det = dt r₁ r₃ := by
  simp [mt, det_fin_two, dt]; ring

theorem sw_det (D : F) : (sw D).det = D * D := by
  simp [sw, det_fin_two]

theorem sw_zero (D : F) (v : Fin 2 → F) : (sw D *ᵥ v) 0 = D * v 1 := by
  simp [sw, mulVec, dotProduct, Fin.sum_univ_two]

theorem sw_one (D : F) (v : Fin 2 → F) : (sw D *ᵥ v) 1 = -D * v 0 := by
  simp [sw, mulVec, dotProduct, Fin.sum_univ_two]

theorem dt_left (r₁ r₃ v : Fin 2 → F) : dt r₁ (mt r₁ r₃ *ᵥ v) = (sw (dt r₁ r₃) *ᵥ v) 0 := by
  rw [sw_zero]
  simp [mt, mulVec, dotProduct, Fin.sum_univ_two, dt]; ring

theorem dt_right (r₁ r₃ v : Fin 2 → F) : dt r₃ (mt r₁ r₃ *ᵥ v) = (sw (dt r₁ r₃) *ᵥ v) 1 := by
  rw [sw_one]
  simp [mt, mulVec, dotProduct, Fin.sum_univ_two, dt]; ring

theorem dt_both (r₁ r₃ v' v : Fin 2 → F) : dt (mt r₁ r₃ *ᵥ v') (mt r₁ r₃ *ᵥ v) =
    v' 0 * (sw (dt r₁ r₃) *ᵥ v) 0 + v' 1 * (sw (dt r₁ r₃) *ᵥ v) 1 := by
  rw [sw_zero, sw_one]
  simp [mt, mulVec, dotProduct, Fin.sum_univ_two, dt]; ring

theorem chF_zero (c : Fˣ →* ℂˣ) (s : ℂ) : chF c s (0 : F) = 0 := by
  simp [chF]

theorem chF_unit (c : Fˣ →* ℂˣ) (s : ℂ) (u : Fˣ) : chF c s (u : F) = ((c u : ℂˣ) : ℂ) * mp u s := by
  simp [chF]

theorem chF_mul (c : Fˣ →* ℂˣ) (s : ℂ) (a b : F) : chF c s (a * b) = chF c s a * chF c s b := by
  by_cases ha : a = 0
  · simp [chF, ha]
  by_cases hb : b = 0
  · simp [chF, hb]
  have h : a * b = ((Units.mk0 a ha * Units.mk0 b hb : Fˣ) : F) := rfl
  have ha' : a = ((Units.mk0 a ha : Fˣ) : F) := rfl
  have hb' : b = ((Units.mk0 b hb : Fˣ) : F) := rfl
  rw [h, chF_unit]
  conv_rhs => rw [ha', hb', chF_unit, chF_unit]
  rw [map_mul, Units.val_mul, GlobalTheory.CompanionTheory.WhittakerTrans.mp_mul']
  ring

theorem mp_neg_one (s : ℂ) : mp (-1 : Fˣ) s = 1 := by
  simp [mp, modulus_neg_eq]

theorem chF_neg (c : Fˣ →* ℂˣ) (s : ℂ) (x : F) : chF c s (-x) = ((c (-1) : ℂˣ) : ℂ) * chF c s x := by
  have h : -x = ((-1 : Fˣ) : F) * x := by simp
  rw [h, chF_mul, chF_unit, mp_neg_one, mul_one]

theorem mp_add (u : Fˣ) (a b : ℂ) : mp u (a + b) = mp u a * mp u b := by
  have h : ((modulus (u : F) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast modulus_ne_zero u.ne_zero
  exact Complex.cpow_add _ _ h

theorem const_eq (ν c : Fˣ →* ℂˣ) (s : ℂ) (u : Fˣ) :
    ((modulus (u : F) : ℝ) : ℂ) * (chF (ν * c) (s - 1) (u : F) * chF (ν⁻¹ * c) (s - 1) (u : F) *
      chF c⁻¹ (-s) (u : F)) = chF c (s - 1) (u : F) := by
  simp only [chF_unit]
  have e : (((ν * c) u : ℂˣ) : ℂ) * (((ν⁻¹ * c) u : ℂˣ) : ℂ) * ((c⁻¹ u : ℂˣ) : ℂ) = ((c u : ℂˣ) : ℂ) := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
    rw [mul_mul_mul_comm, mul_inv_cancel, one_mul, mul_inv_cancel_right]
  have e2 : ((modulus (u : F) : ℝ) : ℂ) * mp u (s - 1) * mp u (-s) = 1 := by
    have h1 : mp u 1 = ((modulus (u : F) : ℝ) : ℂ) := by simp [mp]
    rw [← h1, ← mp_add, ← mp_add]
    have : (1 + (s - 1) + -s : ℂ) = 0 := by ring
    rw [this]
    simp [mp]
  calc _ = ((((ν * c) u : ℂˣ) : ℂ) * (((ν⁻¹ * c) u : ℂˣ) : ℂ) * ((c⁻¹ u : ℂˣ) : ℂ)) *
        (((modulus (u : F) : ℝ) : ℂ) * mp u (s - 1) * mp u (-s)) * mp u (s - 1) := by ring
    _ = _ := by rw [e, e2, mul_one]

theorem sign_eq (ν c : Fˣ →* ℂˣ) :
    (((ν * c) (-1) : ℂˣ) : ℂ) * (((ν⁻¹ * c) (-1) : ℂˣ) : ℂ) = 1 := by
  rw [← Units.val_mul]
  have h : (c (-1)) * (c (-1)) = 1 := by rw [← map_mul]; simp
  have : (ν * c) (-1) * (ν⁻¹ * c) (-1) = 1 := by
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
    rw [mul_mul_mul_comm, mul_inv_cancel, one_mul, h]
  rw [this, Units.val_one]

theorem isUnit1_mul {μ ν : Fˣ →* ℂˣ} (h₁ : IsUnit1 μ) (h₂ : IsUnit1 ν) : IsUnit1 (μ * ν) :=
  ⟨h₁.1.mul h₂.1, fun x => by simp [h₁.2, h₂.2]⟩

theorem isUnit1_inv {μ : Fˣ →* ℂˣ} (h : IsUnit1 μ) : IsUnit1 μ⁻¹ :=
  ⟨h.1.inv, fun x => by simp [h.2]⟩

theorem kr_left (ν c : Fˣ →* ℂˣ) (s : ℂ) (r₁ r₃ v : Fin 2 → F) :
    Kr ν c⁻¹ (1 - s) r₁ (mt r₁ r₃ *ᵥ v) r₃ = chF c (s - 1) (dt r₁ r₃) *
      (chF (ν⁻¹ * c)⁻¹ (-s) ((sw (dt r₁ r₃) *ᵥ v) 0) * chF (ν * c)⁻¹ (-s) ((sw (dt r₁ r₃) *ᵥ v) 1)) := by
  have e1 : (ν⁻¹ * c)⁻¹ = ν * c⁻¹ := by rw [mul_inv, inv_inv]
  have e2 : (ν * c)⁻¹ = ν⁻¹ * c⁻¹ := mul_inv ν c
  have e3 : (1 - s - 1 : ℂ) = -s := by ring
  have e4 : (-(1 - s) : ℂ) = s - 1 := by ring
  simp only [Kr, dt_left, dt_right, e1, e2, e3, e4, inv_inv]
  ring

theorem kr_right (ν c : Fˣ →* ℂˣ) (s : ℂ) (r₁ r₃ v : Fin 2 → F) :
    Kr ν c s r₁ (mt r₁ r₃ *ᵥ v) r₃ = (((ν⁻¹ * c) (-1) : ℂˣ) : ℂ) *
      (chF (ν * c) (s - 1) (dt r₁ r₃) * chF (ν⁻¹ * c) (s - 1) (dt r₁ r₃) * chF c⁻¹ (-s) (dt r₁ r₃)) *
      (chF (ν⁻¹ * c) (s - 1) (v 0) * chF (ν * c) (s - 1) (v 1)) := by
  simp only [Kr, dt_left, dt_right, sw_zero, sw_one, chF_mul, neg_mul, chF_neg]
  ring

variable [MeasurableSpace F] [BorelSpace F]

theorem integral_eq_mulVec (ψ : AddChar F Circle) (M : Matrix (Fin 2) (Fin 2) F) (hM : M.det ≠ 0)
    (f : (Fin 2 → F) → ℂ) :
    ∫ x, f x ∂m2 ψ = ((modulus M.det : ℝ) : ℂ) * ∫ x, f (M *ᵥ x) ∂m2 ψ := by
  set g := GeneralLinearGroup.mkOfDetNeZero M hM with hg
  have hgM : (g : Matrix (Fin 2) (Fin 2) F) = M := rfl
  have h := GlobalTheory.CompanionTheory.JSBound.setIntegral_image_mulVec (selfDualMeasure ψ) g Set.univ f
  have hs : (fun x => (g : Matrix (Fin 2) (Fin 2) F) *ᵥ x) '' Set.univ = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ⟨((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ y, trivial, ?_⟩
    simp only [Matrix.mulVec_mulVec]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  rw [hs, Measure.restrict_univ, hgM] at h
  have hu : Measures.modulus M.det = modulus M.det := by
    have := Measures.modulus_units (Units.mk0 M.det hM)
    rw [distribHaarChar_eq_modulus] at this
    exact this
  rw [hu] at h
  exact h

theorem sF_comp (ψ : AddChar F Circle) (Ψ : (Fin 2 → F) → ℂ) (r₁ r₃ v : Fin 2 → F)
    (hD : dt r₁ r₃ ≠ 0) :
    sF ψ Ψ (mt r₁ r₃ *ᵥ v) = ((modulus (dt r₁ r₃) : ℝ) : ℂ) *
      ∫ r', Ψ (mt r₁ r₃ *ᵥ r') * (ψ (r' 0 * (sw (dt r₁ r₃) *ᵥ v) 0 + r' 1 * (sw (dt r₁ r₃) *ᵥ v) 1) : ℂ) ∂m2 ψ := by
  have hM : (mt r₁ r₃).det ≠ 0 := by rwa [mt_det]
  rw [sF, integral_eq_mulVec ψ _ hM, mt_det]
  simp only [dt_both]

theorem kernel_local_functional_equation : A7 → A8 := by
  intro hA F _ _ _ _ _ _ ψ hψ ν c hν hc Ψ hΨ s hs r₁ r₃
  by_cases hD : dt r₁ r₃ = 0
  · simp only [Kr, hD, chF_zero, mul_zero, integral_zero]
  have hM : (mt r₁ r₃).det ≠ 0 := by rwa [mt_det]
  have hS : (sw (dt r₁ r₃)).det ≠ 0 := by rw [sw_det]; exact mul_ne_zero hD hD
  have hf : SB (fun v => Ψ (mt r₁ r₃ *ᵥ v)) := by
    have hT : (mt r₁ r₃)ᵀ.det ≠ 0 := by rwa [det_transpose]
    have h := GlobalTheory.CompanionTheory.WhittakerTrans.rt_mem hΨ (GeneralLinearGroup.mkOfDetNeZero _ hT)
    have e : (fun v => Ψ (mt r₁ r₃ *ᵥ v)) = Ad3.SchwartzSpaceL2.rt Ψ (GeneralLinearGroup.mkOfDetNeZero _ hT) := by
      funext v
      show _ = Ψ (v ᵥ* (mt r₁ r₃)ᵀ)
      rw [vecMul_transpose]
    rw [e]
    exact h
  have h1 : IsUnit1 (ν⁻¹ * c) := isUnit1_mul (isUnit1_inv hν) hc
  have h2 : IsUnit1 (ν * c) := isUnit1_mul hν hc
  have h7 : ∫ r, (∫ r', Ψ (mt r₁ r₃ *ᵥ r') * (ψ (r' 0 * r 0 + r' 1 * r 1) : ℂ) ∂m2 ψ) *
        (chF (ν⁻¹ * c)⁻¹ (-s) (r 0) * chF (ν * c)⁻¹ (-s) (r 1)) ∂m2 ψ =
      gam ψ (ν⁻¹ * c) s * gam ψ (ν * c) s * ∫ r, Ψ (mt r₁ r₃ *ᵥ r) *
        (chF (ν⁻¹ * c) (s - 1) (r 0) * chF (ν * c) (s - 1) (r 1)) ∂m2 ψ :=
    hA F ψ hψ (ν⁻¹ * c) (ν * c) h1 h2 _ hf s hs
  have hSm : ((modulus (sw (dt r₁ r₃)).det : ℝ) : ℂ) =
      ((modulus (dt r₁ r₃) : ℝ) : ℂ) * ((modulus (dt r₁ r₃) : ℝ) : ℂ) := by
    rw [sw_det, modulus_mul]
    push_cast
    rfl
  rw [integral_eq_mulVec ψ _ hS, hSm] at h7
  rw [integral_eq_mulVec ψ _ hM, integral_eq_mulVec ψ (f := fun r => Ψ r * Kr ν c s r₁ r r₃) _ hM, mt_det]
  simp only [sF_comp ψ Ψ r₁ r₃ _ hD, kr_left]
  simp only [kr_right]
  have hK := const_eq ν c s (Units.mk0 _ hD)
  simp only [Units.val_mk0] at hK
  have hτ := sign_eq ν c
  generalize ((modulus (dt r₁ r₃) : ℝ) : ℂ) = A at h7 hK ⊢
  generalize chF c (s - 1) (dt r₁ r₃) = C at hK ⊢
  generalize chF (ν * c) (s - 1) (dt r₁ r₃) * chF (ν⁻¹ * c) (s - 1) (dt r₁ r₃) *
    chF c⁻¹ (-s) (dt r₁ r₃) = K at hK ⊢
  generalize (((ν * c) (-1) : ℂˣ) : ℂ) = τ at hτ ⊢
  generalize (((ν⁻¹ * c) (-1) : ℂˣ) : ℂ) = σ at hτ ⊢
  have eL : ∀ (J P : (Fin 2 → F) → ℂ), ∫ v, A * J v * (C * P v) ∂m2 ψ = A * C * ∫ v, J v * P v ∂m2 ψ := by
    intro J P
    rw [← integral_const_mul]
    congr 1
    funext v
    ring
  have eR : ∀ (J P : (Fin 2 → F) → ℂ), ∫ v, J v * (σ * K * P v) ∂m2 ψ = σ * K * ∫ v, J v * P v ∂m2 ψ := by
    intro J P
    rw [← integral_const_mul]
    congr 1
    funext v
    ring
  rw [eL (fun v => ∫ r', Ψ (mt r₁ r₃ *ᵥ r') *
      (ψ (r' 0 * (sw (dt r₁ r₃) *ᵥ v) 0 + r' 1 * (sw (dt r₁ r₃) *ᵥ v) 1) : ℂ) ∂m2 ψ)
      (fun v => chF (ν⁻¹ * c)⁻¹ (-s) ((sw (dt r₁ r₃) *ᵥ v) 0) * chF (ν * c)⁻¹ (-s) ((sw (dt r₁ r₃) *ᵥ v) 1)),
    eR (fun v => Ψ (mt r₁ r₃ *ᵥ v))
      (fun v => chF (ν⁻¹ * c) (s - 1) (v 0) * chF (ν * c) (s - 1) (v 1))]
  generalize (∫ v, (∫ r', Ψ (mt r₁ r₃ *ᵥ r') *
      (ψ (r' 0 * (sw (dt r₁ r₃) *ᵥ v) 0 + r' 1 * (sw (dt r₁ r₃) *ᵥ v) 1) : ℂ) ∂m2 ψ) *
      (chF (ν⁻¹ * c)⁻¹ (-s) ((sw (dt r₁ r₃) *ᵥ v) 0) * chF (ν * c)⁻¹ (-s) ((sw (dt r₁ r₃) *ᵥ v) 1)) ∂m2 ψ) = X at h7 ⊢
  generalize (∫ v, Ψ (mt r₁ r₃ *ᵥ v) *
      (chF (ν⁻¹ * c) (s - 1) (v 0) * chF (ν * c) (s - 1) (v 1)) ∂m2 ψ) = I at h7 ⊢
  generalize gam ψ (ν⁻¹ * c) s = g₁ at h7 ⊢
  generalize gam ψ (ν * c) s = g₂ at h7 ⊢
  linear_combination C * h7 - g₁ * g₂ * I * τ * σ * hK - g₁ * g₂ * I * C * hτ

end GlobalTheory.CompanionTheory.RSKernel

end
