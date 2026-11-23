import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinRealAdSmulAlt
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.LrhoPf

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

def ev (w : Vw d) (z : ℂ) (u : Vw d) : ℂ :=
  2 * Real.pi * Complex.I * z.re * z.im * ((‖w‖ ^ 2 : ℝ) : ℂ) -
    4 * Real.pi * Complex.I * z.im * (⟪w, u⟫_ℝ + z.re * ((‖w‖ ^ 2 : ℝ) : ℂ)) +
    ((-(2 * Real.pi * (‖u‖ ^ 2 + 2 * z.re * ⟪w, u⟫_ℝ + z.re ^ 2 * ‖w‖ ^ 2)) : ℝ) : ℂ)

def bv (w : Vw d) (z : ℂ) (u : Vw d) : ℂ := star (Complex.exp (ev w z u))

theorem norm_add_smul_sq (w u : Vw d) (x : ℝ) :
    ‖u + x • w‖ ^ 2 = ‖u‖ ^ 2 + 2 * x * ⟪w, u⟫_ℝ + x ^ 2 * ‖w‖ ^ 2 := by
  rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, real_inner_comm]
  ring

theorem T_vline (hH : THeis) (R : RD d) {g : Yf d → ℂ} {Ω : d.Fn} (hΩ : Ω ∈ d.sch) (hTΩ : d.T Ω = vac R g)
    {W : Mx F E d.m d.n} (hW : finOne F • W = 0) (z : ℂ) (X : Mx F E d.m d.n) :
    d.T (d.dd.rho d.B.ψ (vline R W z) Ω) X = bv (arc R W) z (arc R X) * g (fin d X) := by
  unfold vline
  rw [T_rho_sum' hH hΩ, psi_sp R hW, psi_tw R hW, hTΩ]
  simp only [vac]
  rw [gau_eq, arc_add, arc_realAd, fin_add_of R (fin_realAd_smul hW z.re)]
  simp only [bv, ev]
  rw [show star (Complex.exp _) = Complex.exp (conj _) from (Complex.exp_conj _).symm, Complex.ofReal_exp,
    ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, norm_add_smul_sq]
  simp only [map_add, map_sub, map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem continuous_bv (w : Vw d) (z : ℂ) : Continuous (bv w z) := by
  unfold bv ev
  refine continuous_star.comp (Complex.continuous_exp.comp ?_)
  fun_prop

theorem norm_bv_le (w : Vw d) (z : ℂ) (u : Vw d) : ‖bv w z u‖ ≤ 1 := by
  unfold bv
  rw [norm_star, Complex.norm_exp]
  apply Real.exp_le_one_iff.2
  have h : ‖u‖ ^ 2 + 2 * z.re * ⟪w, u⟫_ℝ + z.re ^ 2 * ‖w‖ ^ 2 ≥ 0 := by
    rw [← norm_add_smul_sq]
    positivity
  simp only [ev, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, Complex.add_im, Complex.mul_im]
  nlinarith [Real.pi_pos]

end PositivityTheory.SiegelWeilFormula.KFP

end
