import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.RightBilinearApply
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.PolyVHasTemperateGrowth
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SigmaFinitePosRealMeasure

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap ContDiff
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem Phi_eq (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : Fin 2 → Ad F) :
    Phi c v = archS F (vInf v) * finRow c v := by
  rw [archS_apply]; rfl

theorem PhiH_eq (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : Fin 2 → Ad F) :
    PhiH c v = archS F (vInf v) * finCol c v := by
  rw [archS_apply]; rfl

theorem finRow_congr {c : HeightOneSpectrum (𝓞 F) → ℕ} {v v' : Fin 2 → Ad F}
    (h : ∀ i, pFin F (v i) = pFin F (v' i)) : finRow c v = finRow c v' := by
  unfold finRow; rw [h 0, h 1]

theorem finCol_congr {c : HeightOneSpectrum (𝓞 F) → ℕ} {v v' : Fin 2 → Ad F}
    (h : ∀ i, pFin F (v i) = pFin F (v' i)) : finCol c v = finCol c v' := by
  unfold finCol; rw [h 0, h 1]

theorem map_pFin_infGL (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    ((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map (pFin F) = 1 :=
  congrArg Units.val (UpperTheory.V.TR.pFin_infGL y)

theorem map_pInf_infGL (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    ((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) =
      (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) :=
  congrArg Units.val (UpperTheory.V.TR.pInf_infGL y)

theorem pFin_vecMul_infGL (v : Fin 2 → Ad F) (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) (i : Fin 2) :
    pFin F ((v ᵥ* ((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) i) = pFin F (v i) := by
  rw [RingHom.map_vecMul, map_pFin_infGL, Matrix.vecMul_one]; rfl

theorem vInf_vecMul_infGL (v : Fin 2 → Ad F) (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    vInf (v ᵥ* ((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) =
      vInf v ᵥ* (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) := by
  funext i
  simp only [vInf]
  rw [RingHom.map_vecMul, map_pInf_infGL]; rfl

theorem pFin_infGL_mulVec (v : Fin 2 → Ad F) (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) (i : Fin 2) :
    pFin F ((((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ v) i) = pFin F (v i) := by
  rw [RingHom.map_mulVec, map_pFin_infGL, Matrix.one_mulVec]; rfl

theorem vInf_infGL_mulVec (v : Fin 2 → Ad F) (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    vInf (((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ v) =
      (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) *ᵥ vInf v := by
  funext i
  simp only [vInf]
  rw [RingHom.map_mulVec, map_pInf_infGL]; rfl

theorem tsum_Xi (f : {ξ : Fin 2 → F // ξ ≠ 0} → ℂ) :
    (∑' ξ : Xi F, f ξ) = ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, f ξ := rfl

theorem row_term (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (a : Ideles F) (ξ : Fin 2 → F)
    (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    Phi c (rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * (g * UpperTheory.V.TR.infGL F 2 y) : GA F 2) :
        Matrix (Fin 2) (Fin 2) (Ad F))) =
      archS F (B1 (vInf (rowv g a ξ)) (UpperTheory.V.TR.toL y.val)) * finRow c (rowv g a ξ) := by
  have hv : rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * (g * UpperTheory.V.TR.infGL F 2 y) : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F)) =
      rowv g a ξ ᵥ* ((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) := by
    simp only [rowv, Mrow, Units.val_mul, Matrix.vecMul_vecMul, mul_assoc]
  rw [hv, Phi_eq, finRow_congr (pFin_vecMul_infGL _ _), vInf_vecMul_infGL, left_bilinear_apply]
  rfl

theorem col_term (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (a : Ideles F) (ξ : Fin 2 → F)
    (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    PhiH c ((((Matrix.GeneralLinearGroup.scalar (Fin 2) a * (g * UpperTheory.V.TR.infGL F 2 y))⁻¹ : GA F 2) :
        Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ) =
      archS F (B2 (vInf (colv g a ξ)) (UpperTheory.V.TR.toL (y⁻¹).val)) * finCol c (colv g a ξ) := by
  have hinv : (Matrix.GeneralLinearGroup.scalar (Fin 2) a * (g * UpperTheory.V.TR.infGL F 2 y))⁻¹ =
      UpperTheory.V.TR.infGL F 2 y⁻¹ * Mcol g a := by
    simp only [Mcol, mul_inv_rev, map_inv, mul_assoc]
  have hv : (((Matrix.GeneralLinearGroup.scalar (Fin 2) a * (g * UpperTheory.V.TR.infGL F 2 y))⁻¹ : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ =
      ((UpperTheory.V.TR.infGL F 2 y⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ colv g a ξ := by
    rw [hinv, Units.val_mul, ← Matrix.mulVec_mulVec]; rfl
  rw [hv, PhiH_eq, finCol_congr (pFin_infGL_mulVec _ _), vInf_infGL_mulVec, right_bilinear_apply]
  rfl

theorem eisInt_row (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2)
    (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) :
    eisInt χ (Phi c) (g * UpperTheory.V.TR.infGL F 2 y) t u =
      (∑' ξ : Xi F, kap1 χ c g ((t, u), ξ) * archS F (B1 (w1 g ((t, u), ξ)) (UpperTheory.V.TR.toL y.val))) *
        ((absD (g * UpperTheory.V.TR.infGL F 2 y) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) := by
  have h : ∀ ξ : Xi F, kap1 χ c g ((t, u), ξ) * archS F (B1 (w1 g ((t, u), ξ)) (UpperTheory.V.TR.toL y.val)) =
      Phi c (rowA ξ.1 ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) *
        (g * UpperTheory.V.TR.infGL F 2 y) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) *
        (((χ.1 (moduleSection (w0 F) t * (u : Ideles F)) : ℂˣ) : ℂ)⁻¹ * ((t : ℝ) : ℂ)) := by
    intro ξ
    rw [row_term]
    simp only [kap1, w1, av]
    ring
  have e : (∑' ξ : Xi F, Phi c (rowA ξ.1 ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2)
      (moduleSection (w0 F) t * (u : Ideles F)) * (g * UpperTheory.V.TR.infGL F 2 y) : GA F 2) :
        Matrix (Fin 2) (Fin 2) (Ad F)))) =
      thetaS (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) *
        (g * UpperTheory.V.TR.infGL F 2 y)) := rfl
  rw [tsum_congr h, tsum_mul_right, e]
  simp only [eisInt]
  ring

theorem eisInt_col (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) {C : ℂ}
    (hC : ∀ h : GA F 2, thetaS (Phi c) h = C * ((absD h)⁻¹ : ℝ) * thetaT (PhiH c) h)
    (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) :
    eisInt χ (Phi c) (g * UpperTheory.V.TR.infGL F 2 y) t u =
      C * ((absD (g * UpperTheory.V.TR.infGL F 2 y))⁻¹ : ℝ) * ((absD (g * UpperTheory.V.TR.infGL F 2 y) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) *
        ∑' ξ : Xi F, kap2 χ c g ((t, u), ξ) * archS F (B2 (w2 g ((t, u), ξ)) (UpperTheory.V.TR.toL (y⁻¹).val)) := by
  have h : ∀ ξ : Xi F, kap2 χ c g ((t, u), ξ) * archS F (B2 (w2 g ((t, u), ξ)) (UpperTheory.V.TR.toL (y⁻¹).val)) =
      PhiH c ((((Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) *
        (g * UpperTheory.V.TR.infGL F 2 y))⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ.1) *
        (((χ.1 (moduleSection (w0 F) t * (u : Ideles F)) : ℂˣ) : ℂ)⁻¹ * ((t : ℝ) : ℂ)⁻¹) := by
    intro ξ
    rw [col_term]
    simp only [kap2, w2, av]
    ring
  have e : (∑' ξ : Xi F, PhiH c ((((Matrix.GeneralLinearGroup.scalar (Fin 2)
      (moduleSection (w0 F) t * (u : Ideles F)) * (g * UpperTheory.V.TR.infGL F 2 y))⁻¹ : GA F 2) :
        Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ.1)) =
      thetaT (PhiH c) (Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) *
        (g * UpperTheory.V.TR.infGL F 2 y)) := rfl
  rw [tsum_congr h, tsum_mul_right, e]
  simp only [eisInt]
  rw [hC, absD_scalar_mul]
  have ht : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr t.2.ne'
  push_cast
  field_simp

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
