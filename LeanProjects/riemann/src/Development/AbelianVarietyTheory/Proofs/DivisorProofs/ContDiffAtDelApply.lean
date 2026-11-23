import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CurveDens
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem angleForm_smul (n : ℕ) (a a' : E → ℝ) (q : E → ℂ) (ξ z : E) (c : ℂ) :
    angleForm n a a' q (c • ξ) z = c * angleForm n a a' q ξ z := by
  simp only [angleForm, ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smulₛₗ, smul_eq_mul,
    map_sub, map_mul, Complex.conj_conj, RingHom.id_apply]
  ring

theorem contDiffAt_del_apply {q : E → ℂ} {z : E} (hq : ContDiffAt ℝ 2 q z) (ξ : E) :
    ContDiffAt ℝ 1 (fun x => del q x ξ) z ∧ ContDiffAt ℝ 1 (fun x => dbar q x ξ) z := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ q) z := hq.fderiv_right (by norm_num)
  have hv : ∀ w : E, ContDiffAt ℝ 1 (fun x => fderiv ℝ q x w) z := fun w =>
    h1.clm_apply contDiffAt_const
  constructor
  · simp only [del_apply, smul_eq_mul]
    exact contDiffAt_const.mul ((hv ξ).sub (contDiffAt_const.mul (hv _)))
  · simp only [dbar_apply, smul_eq_mul]
    exact contDiffAt_const.mul ((hv ξ).add (contDiffAt_const.mul (hv _)))

theorem contDiffAt_angleForm (n : ℕ) {a a' : E → ℝ} {q : E → ℂ} (ξ : E) {z : E}
    (ha : ContDiffAt ℝ 2 a z) (ha' : ContDiffAt ℝ 2 a' z) (hq : ContDiffAt ℝ 2 q z)
    (h0 : 0 < a z) (h0' : 0 < a' z) : ContDiffAt ℝ 1 (angleForm n a a' q ξ) z := by
  have hla : ContDiffAt ℝ 2 (fun x => (Real.log (a x) : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z (ha.log h0.ne')
  have hla' : ContDiffAt ℝ 2 (fun x => (Real.log (a' x) : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z (ha'.log h0'.ne')
  have hq1 : ContDiffAt ℝ 1 q z := hq.of_le (by norm_num)
  have hA : ContDiffAt ℝ 1 (fun x => a x * a' x) z := (ha.mul ha').of_le (by norm_num)
  have hA0 : a z * a' z ≠ 0 := (mul_pos h0 h0').ne'
  have hN : ContDiffAt ℝ 1 (fun x => ‖q x‖ ^ 2) z := hq1.norm_sq ℝ
  have hR : ContDiffAt ℝ 1 (fun x => (((‖q x‖ ^ 2 / (a x * a' x)) ^ n : ℝ) : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z ((hN.div hA hA0).pow n)
  have hD : ContDiffAt ℝ 1 (fun x => ((a x * a' x : ℝ) : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z hA
  have hconj : ∀ {f : E → ℂ}, ContDiffAt ℝ 1 f z →
      ContDiffAt ℝ 1 (fun x => starRingEnd ℂ (f x)) z :=
    fun hf => Complex.conjCLE.contDiff.contDiffAt.comp z hf
  have e1 := contDiffAt_del_apply hq ξ
  have e2 := contDiffAt_del_apply hla ξ
  have e3 := contDiffAt_del_apply hla' ξ
  have hD0 : ((a z * a' z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hA0
  have key : ContDiffAt ℝ 1 (fun x => (((‖q x‖ ^ 2 / (a x * a' x)) ^ n : ℝ) : ℂ) *
      (starRingEnd ℂ (q x) * (del q x ξ - q x * del (fun x => (Real.log (a' x) : ℂ)) x ξ) -
        q x * starRingEnd ℂ (dbar q x ξ - q x * dbar (fun x => (Real.log (a x) : ℂ)) x ξ)) *
      (((a x * a' x : ℝ) : ℂ))⁻¹) z :=
    (hR.mul (((hconj hq1).mul (e1.1.sub (hq1.mul e3.1))).sub
      (hq1.mul (hconj (e1.2.sub (hq1.mul e2.2)))))).mul (hD.inv hD0)
  unfold angleForm
  simpa only [div_eq_mul_inv] using key

theorem angleForm_comp_holo (n : ℕ) (a a' : E → ℝ) (q : E → ℂ) (ξ z : E) (φ : E → E)
    (hφ : DifferentiableAt ℂ φ z) (ha : DifferentiableAt ℝ a (φ z))
    (ha' : DifferentiableAt ℝ a' (φ z)) (hq : DifferentiableAt ℝ q (φ z))
    (h0 : 0 < a (φ z)) (h0' : 0 < a' (φ z)) :
    angleForm n (fun x => a (φ x)) (fun x => a' (φ x)) (fun x => q (φ x)) ξ z =
      angleForm n a a' q (fderiv ℂ φ z ξ) (φ z) := by
  have hla : DifferentiableAt ℝ (fun y => (Real.log (a y) : ℂ)) (φ z) :=
    Complex.ofRealCLM.differentiableAt.comp _ (ha.log h0.ne')
  have hla' : DifferentiableAt ℝ (fun y => (Real.log (a' y) : ℂ)) (φ z) :=
    Complex.ofRealCLM.differentiableAt.comp _ (ha'.log h0'.ne')
  unfold angleForm
  rw [del_comp_holo (u := q) hq hφ, dbar_comp_holo (u := q) hq hφ,
    del_comp_holo (u := fun y => (Real.log (a' y) : ℂ)) hla' hφ,
    dbar_comp_holo (u := fun y => (Real.log (a y) : ℂ)) hla hφ]

theorem angleForm_props : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (n : ℕ) (a a' : E → ℝ) (q : E → ℂ) (ξ z : E), (∀ c : ℂ, angleForm n a a' q (c • ξ) z = c * angleForm n a a' q ξ z) ∧ (ContDiffAt ℝ 2 a z → ContDiffAt ℝ 2 a' z → ContDiffAt ℝ 2 q z → 0 < a z → 0 < a' z → ContDiffAt ℝ 1 (angleForm n a a' q ξ) z) ∧ ∀ φ : E → E, DifferentiableAt ℂ φ z → DifferentiableAt ℝ a (φ z) → DifferentiableAt ℝ a' (φ z) → DifferentiableAt ℝ q (φ z) → 0 < a (φ z) → 0 < a' (φ z) → angleForm n (fun x => a (φ x)) (fun x => a' (φ x)) (fun x => q (φ x)) ξ z = angleForm n a a' q (fderiv ℂ φ z ξ) (φ z) :=
  fun _ _ _ _ _ n a a' q ξ z => ⟨angleForm_smul n a a' q ξ z,
    fun ha ha' hq h0 h0' => contDiffAt_angleForm n ξ ha ha' hq h0 h0',
    fun φ hφ ha ha' hq h0 h0' => angleForm_comp_holo n a a' q ξ z φ hφ ha ha' hq h0 h0'⟩

end GlobalTheory.CurveDens
