import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

namespace GlobalTheory

theorem pluriharmonic_dz_differentiable : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f : V → ℝ), ContDiff ℝ ∞ f →
    (∀ z a w : V, fderiv ℝ (fun y => fderiv ℝ f y (Complex.I • a)) z w =
      fderiv ℝ (fun y => fderiv ℝ f y (Complex.I • w)) z a) →
    ∀ a : V, Differentiable ℂ (fun z => ((fderiv ℝ f z a : ℝ) : ℂ) -
      Complex.I * ((fderiv ℝ f z (Complex.I • a) : ℝ) : ℂ)) := by
  intro V _ _ f hf hh a z
  have hf1 : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hf2 : Differentiable ℝ (fderiv ℝ f) := hf1.differentiable (by simp)
  set B := fderiv ℝ (fderiv ℝ f) z with hB
  have hsym : ∀ x y, B x y = B y x := fun x y =>
    (hf.contDiffAt.isSymmSndFDerivAt (by simp; exact WithTop.coe_le_coe.mpr le_top)) x y
  have hdc : ∀ c : V, DifferentiableAt ℝ (fun y => fderiv ℝ f y c) z := fun c =>
    (hf2 z).clm_apply (differentiableAt_const c)
  have hS : ∀ c x, fderiv ℝ (fun y => fderiv ℝ f y c) z x = B x c := by
    intro c x
    rw [fderiv_clm_apply (hf2 z) (differentiableAt_const c)]
    simp [hB]
  have hH : ∀ a w : V, B w (Complex.I • a) = B a (Complex.I • w) := by
    intro a w; have := hh z a w; rwa [hS, hS] at this
  set D : V →L[ℝ] ℂ := Complex.ofRealCLM.comp (fderiv ℝ (fun y => fderiv ℝ f y a) z) -
    Complex.I • Complex.ofRealCLM.comp (fderiv ℝ (fun y => fderiv ℝ f y (Complex.I • a)) z) with hD
  have hder : HasFDerivAt (fun z => ((fderiv ℝ f z a : ℝ) : ℂ) -
      Complex.I * ((fderiv ℝ f z (Complex.I • a) : ℝ) : ℂ)) D z := by
    have h1 := Complex.ofRealCLM.hasFDerivAt.comp z (hdc a).hasFDerivAt
    have h2 := (Complex.ofRealCLM.hasFDerivAt.comp z (hdc (Complex.I • a)).hasFDerivAt).const_mul
      Complex.I
    exact h1.sub h2
  have hDval : ∀ w, D w = ((B w a : ℝ) : ℂ) - Complex.I * ((B w (Complex.I • a) : ℝ) : ℂ) := by
    intro w; simp [hD, hS]
  have hDI : ∀ w, D (Complex.I • w) = Complex.I * D w := by
    intro w
    have e1 : B (Complex.I • w) a = B w (Complex.I • a) := by rw [hsym, hH]
    have e2 : B (Complex.I • w) (Complex.I • a) = - B w a := by
      rw [hH, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg, hsym]
    rw [hDval, hDval, e1, e2]
    push_cast
    linear_combination ((B w (Complex.I • a) : ℝ) : ℂ) * Complex.I_sq
  let L : V →L[ℂ] ℂ :=
    { toFun := fun w => D w
      map_add' := fun x y => D.map_add x y
      map_smul' := by
        intro c w
        simp only [RingHom.id_apply, smul_eq_mul]
        have hc : c • w = c.re • w + c.im • (Complex.I • w) := by
          conv_lhs => rw [← Complex.re_add_im c]
          rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
        rw [hc, D.map_add, D.map_smul, D.map_smul, hDI, Complex.real_smul, Complex.real_smul]
        conv_rhs => rw [← Complex.re_add_im c]
        ring
      cont := D.continuous }
  have hL : L.restrictScalars ℝ = D := by ext w; rfl
  exact (hasFDerivAt_of_restrictScalars ℝ hder hL).differentiableAt

end GlobalTheory
