import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TorsionForm.FlatAcyc

theorem dd_real_hessian {g : ℕ} (ψ : (Fin g → ℂ) → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (Ω : (Fin g → ℂ) → (Fin g → ℂ) → ℝ) (z : Fin g → ℂ)
    (hΩ : ∀ v w, fderiv ℝ (fun z' => fderiv ℝ ψ z' (Complex.I • w)) z v -
      fderiv ℝ (fun z' => fderiv ℝ ψ z' (Complex.I • v)) z w = 4 * π * Ω v w)
    (a c : Fin g) :
    d10 (fun z' => d01 (fun z'' => (ψ z'' : ℂ)) z' (ev c)) z (ev a) =
      -(π : ℂ) * Ω (ev a) (Complex.I • ev c) + (π : ℂ) * Complex.I * Ω (ev a) (ev c) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ ψ) := hψ.fderiv_right (by norm_num)
  have hd1 : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ ψ) := h1.differentiable (by norm_num)
  set D2 := fderiv ℝ (fderiv ℝ ψ) z with hD2
  have hsymm : ∀ v w, D2 v w = D2 w v := fun v w =>
    (hψ.contDiffAt.isSymmSndFDerivAt (by simp)) v w
  have hA : ∀ y, HasFDerivAt (fun z' => fderiv ℝ ψ z' y)
      ((ContinuousLinearMap.apply ℝ ℝ y).comp D2) z := fun y =>
    (ContinuousLinearMap.apply ℝ ℝ y).hasFDerivAt.comp z (hd2 z).hasFDerivAt
  have hAe : ∀ v y, fderiv ℝ (fun z' => fderiv ℝ ψ z' y) z v = D2 v y := fun v y => by
    rw [(hA y).fderiv]; rfl
  have hF : (fun z' => d01 (fun z'' => (ψ z'' : ℂ)) z' (ev c)) =
      fun z' => (1 / 2 : ℂ) • (((fderiv ℝ ψ z' (ev c) : ℝ) : ℂ) +
        Complex.I • ((fderiv ℝ ψ z' (Complex.I • ev c) : ℝ) : ℂ)) := by
    funext z'
    have : fderiv ℝ (fun z'' => (ψ z'' : ℂ)) z' = Complex.ofRealCLM.comp (fderiv ℝ ψ z') :=
      (Complex.ofRealCLM.hasFDerivAt.comp z' (hd1 z').hasFDerivAt).fderiv
    simp only [d01, this, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
  have hFd : HasFDerivAt (fun z' => (1 / 2 : ℂ) • (((fderiv ℝ ψ z' (ev c) : ℝ) : ℂ) +
        Complex.I • ((fderiv ℝ ψ z' (Complex.I • ev c) : ℝ) : ℂ)))
      ((1 / 2 : ℂ) • (Complex.ofRealCLM.comp ((ContinuousLinearMap.apply ℝ ℝ (ev c)).comp D2) +
        Complex.I • Complex.ofRealCLM.comp
          ((ContinuousLinearMap.apply ℝ ℝ (Complex.I • ev c)).comp D2))) z :=
    ((Complex.ofRealCLM.hasFDerivAt.comp z (hA (ev c))).add
      ((Complex.ofRealCLM.hasFDerivAt.comp z (hA (Complex.I • ev c))).const_smul Complex.I)).const_smul
      (1 / 2 : ℂ)
  rw [hF]
  simp only [d10, hFd.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, Complex.ofRealCLM_apply,
    smul_eq_mul]
  have E1 := hΩ (ev a) (ev c)
  have E2 := hΩ (ev a) (Complex.I • ev c)
  rw [hAe, hAe] at E1 E2
  simp only [smul_smul, Complex.I_mul_I, neg_one_smul, map_neg] at E1 E2
  rw [hsymm (ev c) (Complex.I • ev a)] at E1
  rw [hsymm (Complex.I • ev c) (Complex.I • ev a)] at E2
  have E1' : (4 : ℂ) * π * Ω (ev a) (ev c) = (D2 (ev a) (Complex.I • ev c) : ℂ) -
      (D2 (Complex.I • ev a) (ev c) : ℂ) := by exact_mod_cast E1.symm
  have E2' : (4 : ℂ) * π * Ω (ev a) (Complex.I • ev c) = -(D2 (ev a) (ev c) : ℂ) -
      (D2 (Complex.I • ev a) (Complex.I • ev c) : ℂ) := by exact_mod_cast E2.symm
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (-Complex.I / 4) * E1' + (1 / 4 : ℂ) * E2' +
    (-(D2 (Complex.I • ev a) (Complex.I • ev c) : ℂ) / 4) * hI

end GlobalTheory.TorsionForm.FlatAcyc
