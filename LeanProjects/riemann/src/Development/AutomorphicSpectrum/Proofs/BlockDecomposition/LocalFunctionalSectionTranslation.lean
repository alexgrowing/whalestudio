import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.SSmoothW
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFTrans

open Ad3 Ad3.LFS

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

noncomputable def rightMulHomeo (h : GL (Fin 3) F) :
    Matrix (Fin 2) (Fin 3) F ≃ₜ Matrix (Fin 2) (Fin 3) F where
  toFun X := X * (h : Matrix (Fin 3) (Fin 3) F)
  invFun X := X * ((h⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  left_inv X := by
    show X * (h : Matrix (Fin 3) (Fin 3) F) * ((h⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = X
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  right_inv X := by
    show X * ((h⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (h : Matrix (Fin 3) (Fin 3) F) = X
    rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  continuous_toFun := Continuous.matrix_mul continuous_id continuous_const
  continuous_invFun := Continuous.matrix_mul continuous_id continuous_const

theorem mp_mul_one (x y : Fˣ) : mp (x * y) 1 = mp x 1 * mp y 1 := by
  simp [mp, modulus_mul]

theorem rtr_mem_SB (h : GL (Fin 3) F) {Φ : Matrix (Fin 2) (Fin 3) F → ℂ} (hΦ : Φ ∈ SB F) :
    rtr h Φ ∈ SB F := by
  obtain ⟨hl, hc⟩ := hΦ
  have hc' : HasCompactSupport (Φ ∘ rightMulHomeo h) :=
    hc.comp_homeomorph (rightMulHomeo h)
  refine ⟨?_, ?_⟩
  · have h1 : IsLocallyConstant (fun X : Matrix (Fin 2) (Fin 3) F =>
        Φ (X * (h : Matrix (Fin 3) (Fin 3) F))) :=
      hl.comp_continuous (Continuous.matrix_mul continuous_id continuous_const)
    exact h1.comp (fun z => mp (GeneralLinearGroup.det h) 1 * z)
  · exact HasCompactSupport.mul_left (f := fun _ => mp (GeneralLinearGroup.det h) 1) hc'

theorem inn_rtr (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ)
    (h : GL (Fin 3) F) (k : GL (Fin 2) F) (g : GL (Fin 3) F) :
    inn ψ (rtr h Φ) k g = mp (GeneralLinearGroup.det h) 1 * inn ψ Φ k (g * h) := by
  unfold inn rtr
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Units.val_mul, Matrix.mul_assoc, mul_assoc]

theorem Wp_mul_right (ψ : AddChar F Circle) (W' : GL (Fin 2) F → ℂ)
    (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (h g : GL (Fin 3) F) :
    Wp ψ W' Φ (g * h) = Wp ψ W' (rtr h Φ) g := by
  unfold Wp
  have h1 : (fun k : GL (Fin 2) F => W' k⁻¹ * mp (GeneralLinearGroup.det k) (3 / 2) * inn ψ (rtr h Φ) k g)
      = fun k => mp (GeneralLinearGroup.det h) 1 *
        (W' k⁻¹ * mp (GeneralLinearGroup.det k) (3 / 2) * inn ψ Φ k (g * h)) := by
    funext k
    rw [inn_rtr]
    ring
  rw [h1, integral_const_mul, map_mul, mp_mul_one]
  ring

theorem sTrans : Ad3.LFS.STrans := by
  intro F _ _ _ _ _ _ ψ W' Φ h hΦ
  exact ⟨rtr_mem_SB h hΦ, funext fun g => Wp_mul_right ψ W' Φ h g⟩

end GlobalTheory.CompanionTheory.LFTrans
