import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff

namespace GlobalTheory.TorsionForm.FlatAcyc.DivId

theorem d10_sum_scalar {g : ℕ} {ι : Type} (s : Finset ι) {F : ι → (Fin g → ℂ) → ℂ}
    {P : Fin g → ℂ} (hF : ∀ i ∈ s, DifferentiableAt ℝ (F i) P) (v : Fin g → ℂ) :
    d10 (fun Q => ∑ i ∈ s, F i Q) P v = ∑ i ∈ s, d10 (F i) P v := by
  simp only [d10, fderiv_fun_sum hF, ContinuousLinearMap.sum_apply, Finset.smul_sum,
    ← Finset.sum_sub_distrib]

theorem d10_const_mul {g : ℕ} (c : ℂ) {F : (Fin g → ℂ) → ℂ}
    {P : Fin g → ℂ} (hF : DifferentiableAt ℝ F P) (v : Fin g → ℂ) :
    d10 (fun Q => c * F Q) P v = c * d10 F P v := by
  rw [dz_mul_leibniz (differentiableAt_const c) hF]
  simp [d10]

theorem d10_ofReal_eq_mul_log {g : ℕ} {H : (Fin g → ℂ) → ℝ} {z : Fin g → ℂ}
    (hH : DifferentiableAt ℝ H z) (h0 : H z ≠ 0) (v : Fin g → ℂ) :
    d10 (fun z' => (H z' : ℂ)) z v = (H z : ℂ) * d10 (fun z' => (Real.log (H z') : ℂ)) z v := by
  have h1 : fderiv ℝ (fun z' => (H z' : ℂ)) z = Complex.ofRealCLM.comp (fderiv ℝ H z) :=
    (Complex.ofRealCLM.hasFDerivAt.comp z hH.hasFDerivAt).fderiv
  have h2 : fderiv ℝ (fun z' => (Real.log (H z') : ℂ)) z =
      Complex.ofRealCLM.comp ((H z)⁻¹ • fderiv ℝ H z) :=
    (Complex.ofRealCLM.hasFDerivAt.comp z (hH.hasFDerivAt.log h0)).fderiv
  have h0' : (H z : ℂ) ≠ 0 := by exact_mod_cast h0
  simp only [d10, h1, h2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Complex.ofRealCLM_apply, Complex.ofReal_mul, Complex.ofReal_inv]
  field_simp

theorem differentiableAt_d01 {g : ℕ} {u : (Fin g → ℂ) → ℂ} (hu : ContDiff ℝ ∞ u)
    (v z : Fin g → ℂ) : DifferentiableAt ℝ (fun z' => d01 u z' v) z := by
  have h := (contDiff_infty_iff_fderiv.1 hu).2
  have h1 : ∀ w : Fin g → ℂ, DifferentiableAt ℝ (fun z' => fderiv ℝ u z' w) z := fun w =>
    ((h.clm_apply contDiff_const).differentiable (by simp)) z
  simp only [d01, smul_eq_mul]
  exact ((h1 _).add ((h1 _).const_mul _)).const_mul _

theorem divergence_identity : ∀ {g : ℕ} (G : Matrix (Fin g) (Fin g) ℂ) (H : (Fin g → ℂ) → ℝ), ContDiff ℝ ∞ H → (∀ z, 0 < H z) → ∀ (u : (Fin g → ℂ) → ℂ), ContDiff ℝ ∞ u → ∀ z : Fin g → ℂ, ∑ a, d10 (fun z' => (H z' : ℂ) * starRingEnd ℂ (u z') * ∑ c, G a c * d01 u z' (ev c)) z (ev a) = (H z : ℂ) * starRingEnd ℂ (u z) * (∑ a, ∑ c, G a c * (d10 (fun z' => d01 u z' (ev c)) z (ev a) + d10 (fun z' => (Real.log (H z') : ℂ)) z (ev a) * d01 u z (ev c))) + (H z : ℂ) * ∑ a, ∑ c, G a c * (starRingEnd ℂ (d01 u z (ev a)) * d01 u z (ev c)) := by
  intro g G H hH hpos u hu z
  have hHd : DifferentiableAt ℝ H z := (hH.differentiable (by simp)) z
  have hud : DifferentiableAt ℝ u z := (hu.differentiable (by simp)) z
  have hHc : DifferentiableAt ℝ (fun z' => (H z' : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z hHd
  have huc : DifferentiableAt ℝ (fun z' => starRingEnd ℂ (u z')) z :=
    Complex.conjCLE.toContinuousLinearMap.differentiableAt.comp z hud
  have hterm : ∀ a c, DifferentiableAt ℝ (fun z' => G a c * d01 u z' (ev c)) z := fun a c =>
    (differentiableAt_d01 hu _ z).const_mul _
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hs : DifferentiableAt ℝ (fun z' => ∑ c, G a c * d01 u z' (ev c)) z :=
    DifferentiableAt.fun_sum fun c _ => hterm a c
  rw [dz_mul_leibniz (φ := fun z' => (H z' : ℂ) * starRingEnd ℂ (u z')) (hHc.mul huc) hs,
    dz_mul_leibniz hHc huc, dz_conj_eq_conj_dbar hud, d10_ofReal_eq_mul_log hHd (hpos z).ne',
    d10_sum_scalar _ (fun c _ => hterm a c)]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [d10_const_mul _ (differentiableAt_d01 hu _ z)]
  ring

end GlobalTheory.TorsionForm.FlatAcyc.DivId
