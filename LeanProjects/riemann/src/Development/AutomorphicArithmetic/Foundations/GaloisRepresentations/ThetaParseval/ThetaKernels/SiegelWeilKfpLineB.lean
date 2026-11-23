import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.ExpAlg
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.THeisK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpGeo
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpLineC
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpLineD

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem B_vline_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.TUnit_k) (hH : _root_.PositivityTheory.SiegelWeilFormula.THeis_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) :
    ∃ (C : ℂ) (c s : ℝ) (ν : Measure (Mx F E d.m d.n)) (νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)), C ≠ 0 ∧ s ≠ 0 ∧
      ν.IsAddHaarMeasure ∧ νf.IsAddHaarMeasure ∧
      ∀ g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), ∀ Ω ∈ d.sch, d.T Ω = _root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k R g → ∀ Φ ∈ d.sch, ∀ W : Mx F E d.m d.n, finOne F • W = 0 → ∀ z : ℂ,
        _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k ν Φ (d.dd.rho d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.KFP.vline_k R W z) Ω) = C * Real.exp (-(c * ‖z‖ ^ 2 * ‖s • _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R W‖ ^ 2)) *
          (Complex.exp (-(z ^ 2 * ‖s • _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R W‖ ^ 2 / (16 * Real.pi))) *
            ∫ u, _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf (d.T Φ) g u * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2)) *
              Complex.exp (z * ⟪s • _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R W, u⟫_ℝ)) := by
  obtain ⟨νf, hνf, hν⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFP.exists_nuf_k R
  refine ⟨1, 1 / (16 * Real.pi), -(4 * Real.pi), Measure.map (_root_.PositivityTheory.SiegelWeilFormula.KFP.jnp_k R) ((volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf), νf,
    one_ne_zero, neg_ne_zero.2 (by positivity), hν, hνf, ?_⟩
  intro g hg' Ω hΩ hTΩ Φ hΦ W hW z
  set w := _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R W with hw
  let e : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d → ℂ := _root_.PositivityTheory.SiegelWeilFormula.KFP.ev_k w z
  let b : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d → ℂ := _root_.PositivityTheory.SiegelWeilFormula.KFP.bv_k w z
  have hTv : ∀ X, d.T (d.dd.rho d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.KFP.vline_k R W z) Ω) X = b (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) * g (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X) :=
    _root_.PositivityTheory.SiegelWeilFormula.KFP.T_vline_k hH R hΩ hTΩ hW z
  have hb : Continuous b := _root_.PositivityTheory.SiegelWeilFormula.KFP.continuous_bv_k w z
  have hb1 : ∀ u, ‖b u‖ ≤ 1 := _root_.PositivityTheory.SiegelWeilFormula.KFP.norm_bv_le_k w z
  have hTΦ : d.T Φ ∈ d.schM := (hT.1 F E σ d).1 Φ hΦ
  have e1 : _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k (Measure.map (_root_.PositivityTheory.SiegelWeilFormula.KFP.jnp_k R) ((volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf)) Φ (d.dd.rho d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.KFP.vline_k R W z) Ω) =
      ∫ u, star (b u) * _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf (d.T Φ) g u := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.B_k, hTv]
    exact _root_.PositivityTheory.SiegelWeilFormula.KFP.integral_jnp_k R hνf hTΦ hg' hb hb1
  rw [e1]
  have key : ∀ u, star (b u) * _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf (d.T Φ) g u =
      ((Real.exp (-(1 / (16 * Real.pi) * ‖z‖ ^ 2 * ‖(-(4 * Real.pi)) • w‖ ^ 2)) : ℝ) : ℂ) *
        Complex.exp (-(z ^ 2 * (‖(-(4 * Real.pi)) • w‖ ^ 2 : ℝ) / (16 * Real.pi))) *
          (_root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf (d.T Φ) g u * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2)) *
            Complex.exp (z * ⟪(-(4 * Real.pi)) • w, u⟫_ℝ)) := by
    intro u
    have hz : z = z.re + z.im * Complex.I := (Complex.re_add_im z).symm
    have h1 := exp_alg z.re z.im (‖w‖ ^ 2) ⟪w, u⟫_ℝ (‖u‖ ^ 2)
    rw [← hz] at h1
    have hn : ‖(-(4 * Real.pi)) • w‖ ^ 2 = 16 * Real.pi ^ 2 * ‖w‖ ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring
    have hi : ⟪(-(4 * Real.pi)) • w, u⟫_ℝ = -(4 * Real.pi) * ⟪w, u⟫_ℝ := real_inner_smul_left _ _ _
    have hzn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
    simp only [b, _root_.PositivityTheory.SiegelWeilFormula.KFP.bv_k, star_star, hn, hi, hzn]
    have h2 : _root_.PositivityTheory.SiegelWeilFormula.KFP.ev_k w z u = 2 * Real.pi * Complex.I * z.re * z.im * ((‖w‖ ^ 2 : ℝ) : ℂ) -
        4 * Real.pi * Complex.I * z.im * (⟪w, u⟫_ℝ + z.re * ((‖w‖ ^ 2 : ℝ) : ℂ)) +
        ((-(2 * Real.pi * (‖u‖ ^ 2 + 2 * z.re * ⟪w, u⟫_ℝ + z.re ^ 2 * ‖w‖ ^ 2)) : ℝ) : ℂ) := by
      rfl
    rw [h2, h1]
    ring
  simp_rw [key]
  rw [integral_const_mul]
  simp only [one_mul, Complex.ofReal_exp]
  push_cast
  ring
end PositivityTheory.SiegelWeilFormula.KFP
end
end
