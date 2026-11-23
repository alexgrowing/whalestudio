import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RSZeta

theorem det_dia (γ : GL (Fin 2) ℚ) : GeneralLinearGroup.det (dia2 γ) = pri (GeneralLinearGroup.det γ) := by
  ext
  simp only [pri, dia2, AdelicGLn.diagonal]
  simpa using (RingHom.map_det (algebraMap ℚ 𝔸[ℚ]) (γ : Matrix (Fin 2) (Fin 2) ℚ)).symm

theorem Dt_pos (g : G2) : 0 < Dt g := (IdeleGroup.ideleModule ℚ (GeneralLinearGroup.det g)).2

theorem Dt_ne (g : G2) : ((Dt g : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Dt_pos g).ne'

theorem md_mul (a b : Jd) : md (a * b) = md a * md b := by
  simp [md, map_mul]

theorem md_inv (a : Jd) : md a⁻¹ = (md a)⁻¹ := by
  simp [md, map_inv]

theorem Dt_mul (g h : G2) : Dt (g * h) = Dt g * Dt h := by
  simp [Dt, md_mul, map_mul]

theorem md_pri (α : ℚˣ) : md (pri α) = 1 := by
  have : pri α = IdeleGroup.diagonal ℚ α := rfl
  rw [md, this, IdeleGroup.ideleModule_diagonal]; rfl

theorem toIdele_pri (c : HeckeCharacter ℚ) (α : ℚˣ) : c.toIdele (pri α) = 1 := by
  have : pri α = IdeleGroup.diagonal ℚ α := rfl
  rw [this, HeckeCharacter.toIdele_diagonal]

theorem det_dg (z : Jd) : GeneralLinearGroup.det (dg2 z z : G2) = z * z := by
  ext
  simp [dg2, Matrix.det_fin_two]

theorem continuous_Dt : Continuous Dt :=
  continuous_subtype_val.comp (IdeleGroup.continuous_ideleModule.comp (AdelicGLn.continuous_det ℚ 2))

theorem measurable_Dt : Measurable Dt := continuous_Dt.measurable

theorem continuous_cdet (c : HeckeCharacter ℚ) : Continuous (cdet c) :=
  continuous_induced_dom.comp ((c.continuous_toIdele).comp (AdelicGLn.continuous_det ℚ 2))

theorem measurable_cdet (c : HeckeCharacter ℚ) : Measurable (cdet c) := (continuous_cdet c).measurable

theorem norm_cdet (c : HeckeCharacter ℚ) (g : G2) : ‖cdet c g‖ = 1 := by
  simp [cdet, Circle.norm_coe]

theorem Dt_dia (γ : GL (Fin 2) ℚ) (g : G2) : Dt (dia2 γ * g) = Dt g := by
  rw [Dt_mul, Dt, det_dia, md_pri, one_mul]

theorem Dt_dg (z : Jd) (g : G2) : Dt (dg2 z z * g) = md z ^ 2 * Dt g := by
  rw [Dt_mul, Dt, det_dg, md_mul, sq]

theorem cdet_mul (c : HeckeCharacter ℚ) (g h : G2) : cdet c (g * h) = cdet c g * cdet c h := by
  simp [cdet, map_mul]

theorem cdet_dia (c : HeckeCharacter ℚ) (γ : GL (Fin 2) ℚ) (g : G2) : cdet c (dia2 γ * g) = cdet c g := by
  rw [cdet_mul, cdet, det_dia, toIdele_pri]; simp

theorem cdet_dg (c : HeckeCharacter ℚ) (z : Jd) (hz : c.toIdele z = 1) (g : G2) : cdet c (dg2 z z * g) = cdet c g := by
  rw [cdet_mul, cdet, det_dg, map_mul, hz]; simp

theorem dg_mul (a b : Jd) : (dg2 a a * dg2 b b : G2) = dg2 (a * b) (a * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]

theorem dg_one : (dg2 1 1 : G2) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2]

theorem det_det_inverse_twist (g : G2) : GeneralLinearGroup.det (inv2 g) = (GeneralLinearGroup.det g)⁻¹ := by
  rw [inv2, map_mul, det_dg]
  group

theorem det_inverse_twist_involutive (g : G2) : inv2 (inv2 g) = g := by
  rw [inv2, det_det_inverse_twist, inv_inv, inv2, ← mul_assoc, dg_mul]
  simp [dg_one]

theorem module_det_inverse_twist (g : G2) : Dt (inv2 g) = (Dt g)⁻¹ := by
  rw [Dt, det_det_inverse_twist, md_inv]; rfl

theorem character_det_inverse_twist (c : HeckeCharacter ℚ) (g : G2) : cdet c (inv2 g) = cdet c⁻¹ g := by
  simp only [cdet, det_det_inverse_twist, map_inv]
  rfl

theorem module_cpow_det_inverse_twist (s : ℂ) (g : G2) : ((Dt (inv2 g) : ℝ) : ℂ) ^ s = ((Dt g : ℝ) : ℂ) ^ (-s) := by
  rw [module_det_inverse_twist, Complex.ofReal_inv, Complex.cpow_neg,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg (Dt_pos g).le]; exact Real.pi_pos.ne)]

theorem cpow_dg (s : ℂ) (z : Jd) (g : G2) :
    ((Dt (dg2 z z * g) : ℝ) : ℂ) ^ s = ((md z ^ 2 : ℝ) : ℂ) ^ s * ((Dt g : ℝ) : ℂ) ^ s := by
  rw [Dt_dg, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (Dt_pos g).le]

theorem Aut.inv2 {H : G2 → ℂ} (hH : Aut H) (g : G2) : H (Ad3.R.inv2 g) = H g := hH.cen _ _

def Zp (μ : Measure G2) (𝓕 : Set G2) (H : G2 → ℂ) (c : HeckeCharacter ℚ) (Φ : (Fin 2 → 𝔸[ℚ]) → ℂ) (s : ℂ) : ℂ :=
  ∫ g in 𝓕 ∩ {g | 1 ≤ Dt g}, H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s * th Φ g ∂μ

def Bd (μ : Measure G2) (𝓕 : Set G2) (H : G2 → ℂ) (c : HeckeCharacter ℚ) (s : ℂ) : ℂ :=
  ∫ g in 𝓕 ∩ band, H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s ∂μ

def Jl (μ : Measure G2) (𝓕 : Set G2) (H : G2 → ℂ) (c : HeckeCharacter ℚ) (s : ℂ) : ℂ :=
  ∫ g in 𝓕 ∩ {g | Dt g < 1}, H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s ∂μ

theorem measurable_w {H : G2 → ℂ} (hH : Aut H) (c : HeckeCharacter ℚ) (s : ℂ) :
    Measurable fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s :=
  (hH.cont.measurable.mul (measurable_cdet c)).mul
    ((Complex.measurable_ofReal.comp measurable_Dt).pow_const s)

theorem linv_w {H : G2 → ℂ} (hH : Aut H) (c : HeckeCharacter ℚ) (s : ℂ) :
    LInv fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s := fun γ g => by
  simp only [hH.left γ g, cdet_dia, Dt_dia]

theorem linv_ind {X : Type} [Zero X] {F : G2 → X} (hF : LInv F) (A : Set ℝ) :
    LInv (Set.indicator {g | Dt g ∈ A} F) := fun γ g => by
  simp only [Set.indicator, Set.mem_setOf_eq, Dt_dia, hF γ g]

end GlobalTheory.CompanionTheory.RSZeta
