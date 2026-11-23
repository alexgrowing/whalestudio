import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.NormAddSmulSq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.THeisK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpGeo
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpLrho
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpLrhoPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpLineC

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
def ev_k (w : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) (z : ℂ) (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) : ℂ :=
  2 * Real.pi * Complex.I * z.re * z.im * ((‖w‖ ^ 2 : ℝ) : ℂ) -
    4 * Real.pi * Complex.I * z.im * (⟪w, u⟫_ℝ + z.re * ((‖w‖ ^ 2 : ℝ) : ℂ)) +
    ((-(2 * Real.pi * (‖u‖ ^ 2 + 2 * z.re * ⟪w, u⟫_ℝ + z.re ^ 2 * ‖w‖ ^ 2)) : ℝ) : ℂ)
def bv_k (w : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) (z : ℂ) (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) : ℂ := star (Complex.exp (_root_.PositivityTheory.SiegelWeilFormula.KFP.ev_k w z u))
theorem norm_add_smul_sq_k (w u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) (x : ℝ) :
    ‖u + x • w‖ ^ 2 = ‖u‖ ^ 2 + 2 * x * ⟪w, u⟫_ℝ + x ^ 2 * ‖w‖ ^ 2 := by
  rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, real_inner_comm]
  ring
theorem T_vline_k (hH : _root_.PositivityTheory.SiegelWeilFormula.THeis_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {g : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → ℂ} {Ω : d.Fn} (hΩ : Ω ∈ d.sch) (hTΩ : d.T Ω = _root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k R g)
    {W : Mx F E d.m d.n} (hW : finOne F • W = 0) (z : ℂ) (X : Mx F E d.m d.n) :
    d.T (d.dd.rho d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.KFP.vline_k R W z) Ω) X = _root_.PositivityTheory.SiegelWeilFormula.KFP.bv_k (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R W) z (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) * g (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X) := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.KFP.vline_k
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.T_rho_sum'_k hH hΩ, _root_.PositivityTheory.SiegelWeilFormula.KFP.psi_sp_k R hW, _root_.PositivityTheory.SiegelWeilFormula.KFP.psi_tw_k R hW, hTΩ]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.gau_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_add_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_realAd_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_add_of_k R (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_realAd_smul_k hW z.re)]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.bv_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.ev_k]
  rw [show star (Complex.exp _) = Complex.exp (conj _) from (Complex.exp_conj _).symm, Complex.ofReal_exp,
    ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, _root_.PositivityTheory.SiegelWeilFormula.KFP.norm_add_smul_sq_k]
  simp only [map_add, map_sub, map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring
theorem continuous_bv_k (w : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) (z : ℂ) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.KFP.bv_k w z) := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.KFP.bv_k _root_.PositivityTheory.SiegelWeilFormula.KFP.ev_k
  refine continuous_star.comp (Complex.continuous_exp.comp ?_)
  fun_prop
theorem norm_bv_le_k (w : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) (z : ℂ) (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) : ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.bv_k w z u‖ ≤ 1 := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.KFP.bv_k
  rw [norm_star, Complex.norm_exp]
  apply Real.exp_le_one_iff.2
  have h : ‖u‖ ^ 2 + 2 * z.re * ⟪w, u⟫_ℝ + z.re ^ 2 * ‖w‖ ^ 2 ≥ 0 := by
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KFP.norm_add_smul_sq_k]
    positivity
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.ev_k, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, Complex.add_im, Complex.mul_im]
  nlinarith [Real.pi_pos]
end PositivityTheory.SiegelWeilFormula.KFP
end
end
