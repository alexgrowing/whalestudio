import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinRealAdSmulAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfinpolybNufH
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpArcPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpGeo
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpPsiPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpLrho

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
def jnp_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) : Mx F E d.m d.n := _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2
theorem exists_nuf_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : ∃ νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), νf.IsAddHaarMeasure ∧
    (Measure.map (_root_.PositivityTheory.SiegelWeilFormula.KFP.jnp_k R) ((volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf)).IsAddHaarMeasure := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KFPB.exists_nuf'_k R
theorem integral_jnp_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)} (hνf : νf.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ d.schM) {g : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → ℂ} (hg' : g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)) {b : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d → ℂ} (hb : Continuous b) (hb1 : ∀ u, ‖b u‖ ≤ 1) :
    ∫ X, f X * star (b (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) * g (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)) ∂(Measure.map (_root_.PositivityTheory.SiegelWeilFormula.KFP.jnp_k R) ((volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf)) =
      ∫ u, star (b u) * _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf f g u := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KFPB.integral_jnp'_k R hνf hf hg' hb hb1
theorem arc_add_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X Y : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R (X + Y) = _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X + _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R Y := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_add'_k R X Y
theorem arc_realAd_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (t : ℝ) (X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R (realAd F t • X) = t • _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_realAd'_k R t X
theorem fin_add_of_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {Z : Mx F E d.m d.n} (hZ : finOne F • Z = 0) (X : Mx F E d.m d.n) :
    _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d (X + Z) = _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_add_of'_k R hZ X
theorem fin_realAd_smul_k {Z : Mx F E d.m d.n} (hZ : finOne F • Z = 0) (t : ℝ) : finOne F • (realAd F t • Z) = 0 := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_realAd_smul'_k hZ t
theorem gau_eq_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.gau_k R X = (Real.exp (-(2 * Real.pi * ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X‖ ^ 2)) : ℂ) := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KFP.gau_eq'_k R X
theorem psi_tw_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {W : Mx F E d.m d.n} (hW : finOne F • W = 0) (t : ℝ) (X : Mx F E d.m d.n) :
    d.B.ψ (d.tt (d.gram (realAd F t • _root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) X)) =
      Complex.exp (4 * Real.pi * Complex.I * t * ⟪_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R W, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X⟫_ℝ) := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KFP.psi_tw'_k R hW t X
theorem psi_sp_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {W : Mx F E d.m d.n} (hW : finOne F • W = 0) (s t : ℝ) :
    d.B.ψ (-(⅟(2 : AF F) * _root_.PositivityTheory.SiegelWeilFormula.KFP.spf_k d ((realAd F s • W) * (incM F d.b.1.toCols₂)ᵀ)
      ((realAd F t • _root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) * (incM F d.b.1.toCols₁)ᵀ))) =
      Complex.exp (-(2 * Real.pi * Complex.I * s * t * ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R W‖ ^ 2)) := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KFP.psi_sp'_k R hW s t
end PositivityTheory.SiegelWeilFormula.KFP
end
end
