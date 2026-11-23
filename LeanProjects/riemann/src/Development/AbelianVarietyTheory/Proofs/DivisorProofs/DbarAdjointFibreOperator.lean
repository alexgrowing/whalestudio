import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff

set_option autoImplicit false

namespace GlobalTheory.TorsionForm.FlatAcyc

section ConstAlongBase
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [SMul ℂ W]

theorem fderiv_comp_snd_apply' {F : (Fin g → ℂ) → W} {b : E} {z : Fin g → ℂ}
    (hF : DifferentiableAt ℝ F z) (v : Pt E g) :
    fderiv ℝ (fun P : Pt E g => F P.2) (b, z) v = fderiv ℝ F z v.2 := by
  have : HasFDerivAt (fun P : Pt E g => F P.2)
      ((fderiv ℝ F z).comp (ContinuousLinearMap.snd ℝ E (Fin g → ℂ))) (b, z) :=
    hF.hasFDerivAt.comp (b, z) hasFDerivAt_snd
  rw [this.fderiv]; rfl

theorem dbar_comp_snd_vertical {F : (Fin g → ℂ) → W} {b : E} {z : Fin g → ℂ}
    (hF : DifferentiableAt ℝ F z) (v : Fin g → ℂ) :
    d01 (fun P : Pt E g => F P.2) (b, z) ((0 : E), v) = d01 F z v := by
  simp only [d01, fderiv_comp_snd_apply' hF, Prod.smul_mk, smul_zero]

theorem dholo_comp_snd_vertical {F : (Fin g → ℂ) → W} {b : E} {z : Fin g → ℂ}
    (hF : DifferentiableAt ℝ F z) (v : Fin g → ℂ) :
    d10 (fun P : Pt E g => F P.2) (b, z) ((0 : E), v) = d10 F z v := by
  simp only [d10, fderiv_comp_snd_apply' hF, Prod.smul_mk, smul_zero]

theorem fderiv_fibre_apply {φ : Pt E g → W} {b : E} {z : Fin g → ℂ}
    (hφ : DifferentiableAt ℝ φ (b, z)) (v : Fin g → ℂ) :
    fderiv ℝ (fun z' => φ (b, z')) z v = fderiv ℝ φ (b, z) ((0 : E), v) := by
  have : HasFDerivAt (fun z' => φ (b, z'))
      ((fderiv ℝ φ (b, z)).comp (ContinuousLinearMap.inr ℝ E (Fin g → ℂ))) z :=
    hφ.hasFDerivAt.comp z (hasFDerivAt_prodMk_right b z)
  rw [this.fderiv]; rfl

theorem dholo_fibre_vertical {φ : Pt E g → W} {b : E} {z : Fin g → ℂ}
    (hφ : DifferentiableAt ℝ φ (b, z)) (v : Fin g → ℂ) :
    d10 φ (b, z) ((0 : E), v) = d10 (fun z' => φ (b, z')) z v := by
  simp only [d10, fderiv_fibre_apply hφ, Prod.smul_mk, smul_zero]

end ConstAlongBase

theorem dbarV_add_dbarAdj_const_eq_fibreOp : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (b : E) (z : Fin g → ℂ)
    (f : (Fin g → ℂ) → Ext (0 + 0 + g)) (hf : Differentiable ℝ f)
    (hh : DifferentiableAt ℝ h (b, z)) (hpos : 0 < h (b, z)),
    dbarV (fun P : Pt E g => f P.2) (b, z) + dbarAdj τ h (fun P : Pt E g => f P.2) (b, z) =
      fibreOp ((2 : ℂ) • imPart τ b) (fun z' => (Real.log (h (b, z')) : ℂ)) f z := by
  intro E _ _ g τ h b z f hf hh hpos
  have hlog : DifferentiableAt ℝ (fun Q : Pt E g => (Real.log (h Q) : ℂ)) (b, z) :=
    Complex.ofRealCLM.differentiableAt.comp (b, z) (hh.log hpos.ne')
  have e1 : ∀ a, d01 (fun P : Pt E g => f P.2) (b, z) (vert E a) = d01 f z (ev a) :=
    fun a => dbar_comp_snd_vertical (hf z) (ev a)
  have e2 : ∀ a, d10 (fun P : Pt E g => f P.2) (b, z) (vert E a) = d10 f z (ev a) :=
    fun a => dholo_comp_snd_vertical (hf z) (ev a)
  have e3 : ∀ a, d10 (fun Q : Pt E g => (Real.log (h Q) : ℂ)) (b, z) (vert E a) =
      d10 (fun z' => (Real.log (h (b, z')) : ℂ)) z (ev a) :=
    fun a => dholo_fibre_vertical hlog (ev a)
  simp only [dbarV, dbarAdj, pointDifference, fibreOp, dbarF, dbarAdjF, e1, e2, e3, Matrix.smul_apply,
    smul_eq_mul]

end GlobalTheory.TorsionForm.FlatAcyc
