import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitInducedRepresentationHypothesis
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitCentre

open GlobalTheory.CompanionTheory.SplitRep GlobalTheory.CompanionTheory.SplitPi

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace F] [BorelSpace F] in

theorem mp_sq_half (a : Fˣ) : mp (a * a) (1 / 2) = ((modulus (a : F) : ℝ) : ℂ) := by
  have h : ((modulus (a : F) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (by exact_mod_cast modulus_ne_zero a.ne_zero)
  simp only [mp, Units.val_mul, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _), ← Complex.cpow_add _ _ h]
  norm_num

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem det_scalar_val (a : Fˣ) : ((dg2 a a : GL (Fin 2) F).val).det = (a : F) * a := by
  simp [dg2, Matrix.det_fin_two]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem det_scalar (a : Fˣ) : GeneralLinearGroup.det (dg2 a a : GL (Fin 2) F) = a * a := by
  ext
  simp [dg2, GeneralLinearGroup.det, Matrix.det_fin_two]

theorem piS_scalar (χ : AddChar F Circle) (c₁ : Fˣ →* ℂˣ) (a : Fˣ) (Ψ : F × F → ℂ) (x : F × F) :
    piS χ c₁ (dg2 a a) Ψ x =
      ((c₁ a : ℂˣ) : ℂ) * ((c₁ a : ℂˣ) : ℂ) * Ψ ((a : F) * x.1, ((a⁻¹ : Fˣ) : F) * x.2) := by
  have ha : (a : F) ≠ 0 := a.ne_zero
  have hM : ((modulus (a : F) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (by exact_mod_cast modulus_ne_zero ha)
  have e00 : one1 (dg2 a a : GL (Fin 2) F) 0 0 = (a : F)⁻¹ := by
    simp only [one1, det_scalar_val]
    simp [dg2]
  have e01 : one1 (dg2 a a : GL (Fin 2) F) 0 1 = 0 := by
    simp [one1, dg2]
  have e10 : one1 (dg2 a a : GL (Fin 2) F) 1 0 = 0 := by
    simp [one1, dg2]
  rw [piS_eq]
  simp only []
  rw [rWS_zero χ (det_normalized_determinant_one _) e10, e00, e01, det_scalar_val]
  simp only [cst, det_scalar, mp_sq_half, map_mul, Units.val_mul, modulus_inv, mul_zero, zero_mul,
    AddChar.map_zero_eq_one, Circle.coe_one, one_mul]
  have e : (((a : F)⁻¹ * x.1, (a : F)⁻¹ * x.2) * ((a : F) * a, 1) : F × F) =
      ((a : F) * x.1, ((a⁻¹ : Fˣ) : F) * x.2) := by
    ext
    · simp only [Prod.fst_mul]
      field_simp
    · simp
  rw [e]
  push_cast
  field_simp

def torusInt (c₁ c₂ : Fˣ →* ℂˣ) (Ψ : F × F → ℂ) : ℂ :=
  ∫ u : Fˣ, Ψ ((u : F), ((u⁻¹ : Fˣ) : F)) * ((c₁ u : ℂˣ) : ℂ) * (((c₂ u)⁻¹ : ℂˣ) : ℂ) ∂multHaar F

theorem wcS_scalar (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ) (a : Fˣ) (Ψ : F × F → ℂ) :
    WcS χ c₁ c₂ Ψ (dg2 a a) = ((c₁ a * c₂ a : ℂˣ) : ℂ) * torusInt c₁ c₂ Ψ := by
  set f : Fˣ → ℂ := fun u => Ψ ((u : F), ((u⁻¹ : Fˣ) : F)) * ((c₁ u : ℂˣ) : ℂ) * (((c₂ u)⁻¹ : ℂˣ) : ℂ) with hf
  rw [wcS_eq, torusInt, ← integral_mul_left_eq_self f a, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [piS_scalar, hf]
  have e1 : (a : F) * (u : F) = ((a * u : Fˣ) : F) := by simp
  have e2 : ((a⁻¹ : Fˣ) : F) * ((u⁻¹ : Fˣ) : F) = (((a * u)⁻¹ : Fˣ) : F) := by
    rw [_root_.mul_inv_rev, mul_comm]; simp
  rw [e1, e2]
  have hc : ((c₁ a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hd : ((c₂ a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hd' : ((c₂ u : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  simp only [map_mul, mul_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem diag_one_one_eq_identity : (dg2 1 1 : GL (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2]

theorem sCen : SCen := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 c₁ c₂ h₁ h₂ Φ hΦ a g
  have hrep := sPiRep F χ hχ hχ1 c₁ c₂ h₁ h₂ Φ hΦ
  have h1 : WcS χ c₁ c₂ Φ (dg2 a a * g) = WcS χ c₁ c₂ (piS χ c₁ g Φ) (dg2 a a) := (hrep _ g).1
  have h2 : WcS χ c₁ c₂ Φ g = WcS χ c₁ c₂ (piS χ c₁ g Φ) 1 := by
    have := (hrep 1 g).1
    rwa [one_mul] at this
  have h3 : WcS χ c₁ c₂ (piS χ c₁ g Φ) 1 = torusInt c₁ c₂ (piS χ c₁ g Φ) := by
    have := wcS_scalar χ c₁ c₂ 1 (piS χ c₁ g Φ)
    rw [diag_one_one_eq_identity] at this
    simpa using this
  rw [h1, h2, h3, wcS_scalar]

end GlobalTheory.CompanionTheory.SplitCentre
