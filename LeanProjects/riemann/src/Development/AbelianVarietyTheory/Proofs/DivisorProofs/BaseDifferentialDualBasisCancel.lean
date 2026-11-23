import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DBaseApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorialFormPullbackSplit
open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge GlobalTheory.TorsionForm.Fibrewise
open scoped ContDiff

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TorsionForm.Fibrewise.SqZero
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}

theorem d_one_zero_eq_dEps_neg_I (f : E → ℂ) (b y : E) :
    d10 f b y = (1/2 : ℂ) * (fderiv ℝ f b y - Complex.I * fderiv ℝ f b (Complex.I • y)) := rfl

theorem d_zero_one_eq_dEps_I (f : E → ℂ) (b y : E) :
    d01 f b y = (1/2 : ℂ) * (fderiv ℝ f b y + Complex.I * fderiv ℝ f b (Complex.I • y)) := rfl

theorem hasFDerivAt_apply (ψ : E → ℂ) (b : E) (hψ : DifferentiableAt ℝ (fderiv ℝ ψ) b) (x : E) :
    HasFDerivAt (fun b' => fderiv ℝ ψ b' x)
      ((ContinuousLinearMap.apply ℝ ℂ x).comp (fderiv ℝ (fderiv ℝ ψ) b)) b :=
  ((ContinuousLinearMap.apply ℝ ℂ x).hasFDerivAt).comp b hψ.hasFDerivAt

theorem fderiv_d10 (ψ : E → ℂ) (b : E) (hψ : DifferentiableAt ℝ (fderiv ℝ ψ) b) (x y : E) :
    fderiv ℝ (fun b' => d10 ψ b' x) b y = (1/2 : ℂ) * (fderiv ℝ (fderiv ℝ ψ) b y x -
      Complex.I * fderiv ℝ (fderiv ℝ ψ) b y (Complex.I • x)) := by
  have h := ((hasFDerivAt_apply ψ b hψ x).sub
    ((hasFDerivAt_apply ψ b hψ (Complex.I • x)).const_mul Complex.I)).const_mul (1/2 : ℂ)
  have e : (fun b' => d10 ψ b' x) = fun b' => (1/2 : ℂ) * (fderiv ℝ ψ b' x -
      Complex.I * fderiv ℝ ψ b' (Complex.I • x)) := rfl
  have h' : fderiv ℝ (fun b' => (1/2 : ℂ) * (fderiv ℝ ψ b' x -
      Complex.I * fderiv ℝ ψ b' (Complex.I • x))) b = _ := h.fderiv
  rw [e, h']
  simp

theorem fderiv_d01 (ψ : E → ℂ) (b : E) (hψ : DifferentiableAt ℝ (fderiv ℝ ψ) b) (x y : E) :
    fderiv ℝ (fun b' => d01 ψ b' x) b y = (1/2 : ℂ) * (fderiv ℝ (fderiv ℝ ψ) b y x +
      Complex.I * fderiv ℝ (fderiv ℝ ψ) b y (Complex.I • x)) := by
  have h := ((hasFDerivAt_apply ψ b hψ x).add
    ((hasFDerivAt_apply ψ b hψ (Complex.I • x)).const_mul Complex.I)).const_mul (1/2 : ℂ)
  have e : (fun b' => d01 ψ b' x) = fun b' => (1/2 : ℂ) * (fderiv ℝ ψ b' x +
      Complex.I * fderiv ℝ ψ b' (Complex.I • x)) := rfl
  have h' : fderiv ℝ (fun b' => (1/2 : ℂ) * (fderiv ℝ ψ b' x +
      Complex.I * fderiv ℝ ψ b' (Complex.I • x))) b = _ := h.fderiv
  rw [e, h']
  simp
  ring

section Coeff
variable (ψ : E → ℂ) (b : E) (hψ : ContDiff ℝ 2 ψ)
include hψ

theorem diff_fderiv : DifferentiableAt ℝ (fderiv ℝ ψ) b :=
  ((hψ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) b

theorem symm2 (v w : E) : fderiv ℝ (fderiv ℝ ψ) b v w = fderiv ℝ (fderiv ℝ ψ) b w v :=
  hψ.contDiffAt.isSymmSndFDerivAt (by simp) v w

theorem d10_d10_symm (x y : E) :
    d10 (fun b' => d10 ψ b' x) b y = d10 (fun b' => d10 ψ b' y) b x := by
  have hd := diff_fderiv ψ b hψ
  rw [d_one_zero_eq_dEps_neg_I, d_one_zero_eq_dEps_neg_I, fderiv_d10 ψ b hd, fderiv_d10 ψ b hd, fderiv_d10 ψ b hd, fderiv_d10 ψ b hd,
    symm2 ψ b hψ y x, symm2 ψ b hψ y (Complex.I • x), symm2 ψ b hψ (Complex.I • y) x,
    symm2 ψ b hψ (Complex.I • y) (Complex.I • x)]
  ring

theorem d01_d01_symm (x y : E) :
    d01 (fun b' => d01 ψ b' x) b y = d01 (fun b' => d01 ψ b' y) b x := by
  have hd := diff_fderiv ψ b hψ
  rw [d_zero_one_eq_dEps_I, d_zero_one_eq_dEps_I, fderiv_d01 ψ b hd, fderiv_d01 ψ b hd, fderiv_d01 ψ b hd, fderiv_d01 ψ b hd,
    symm2 ψ b hψ y x, symm2 ψ b hψ y (Complex.I • x), symm2 ψ b hψ (Complex.I • y) x,
    symm2 ψ b hψ (Complex.I • y) (Complex.I • x)]
  ring

theorem d01_d10_swap (x y : E) :
    d01 (fun b' => d10 ψ b' x) b y = d10 (fun b' => d01 ψ b' y) b x := by
  have hd := diff_fderiv ψ b hψ
  rw [d_zero_one_eq_dEps_I, d_one_zero_eq_dEps_neg_I, fderiv_d10 ψ b hd, fderiv_d10 ψ b hd, fderiv_d01 ψ b hd, fderiv_d01 ψ b hd,
    symm2 ψ b hψ y x, symm2 ψ b hψ y (Complex.I • x), symm2 ψ b hψ (Complex.I • y) x,
    symm2 ψ b hψ (Complex.I • y) (Complex.I • x)]
  ring

end Coeff

theorem sum_sum_antisymm {M : Type} [AddCommGroup M] [Module ℂ M] (T : Fin n → Fin n → M)
    (hT : ∀ i j, T j i = -T i j) : ∑ i, ∑ j, T i j = 0 := by
  have h : ∑ i, ∑ j, T i j = -∑ i, ∑ j, T i j := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => hT i j
  have h2 : (2 : ℂ) • ∑ i, ∑ j, T i j = 0 := by
    rw [two_smul]; nth_rewrite 1 [h]; exact neg_add_cancel _
  have := congrArg (fun v => (1/2 : ℂ) • v) h2
  simpa [smul_smul] using this

theorem d_sq_zero (β : Fin n → E) (ψ : E → ℂ) (b : E) (w : Ext (n + n + g)) (hψ : ContDiff ℝ 2 ψ) :
    ∑ i, (dBase β (fun b' => d10 ψ b' (β i)) b (wedge (dt g i) w) +
      dBase β (fun b' => d01 ψ b' (β i)) b (wedge (dtb g i) w)) = 0 := by
  simp only [dBase_apply, ← Finset.sum_add_distrib]
  apply sum_sum_antisymm
  intro i j
  rw [GlobalTheory.TorsionForm.Pullback.Tensorial.wedge_anticomm (dt g i) (dt g j),
    GlobalTheory.TorsionForm.Pullback.Tensorial.wedge_anticomm (dtb g i) (dt g j),
    GlobalTheory.TorsionForm.Pullback.Tensorial.wedge_anticomm (dt g i) (dtb g j),
    GlobalTheory.TorsionForm.Pullback.Tensorial.wedge_anticomm (dtb g i) (dtb g j),
    d10_d10_symm ψ b hψ (β j) (β i), d01_d01_symm ψ b hψ (β j) (β i),
    d01_d10_swap ψ b hψ (β j) (β i), ← d01_d10_swap ψ b hψ (β i) (β j)]
  module

end GlobalTheory.TorsionForm.Fibrewise.SqZero
