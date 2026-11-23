import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinOneMulEqZeroIff
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.Spf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.PolynomialGaussianIntegrals.IntegralJnp
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinRealAdSmul
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FrameArchimedeanPairing

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

def jnp (R : RD d) (p : Vw d × Yf d) : Mx F E d.m d.n := jn R p.1 p.2

theorem exists_nuf (R : RD d) : ∃ νf : Measure (Yf d), νf.IsAddHaarMeasure ∧
    (Measure.map (jnp R) ((volume : Measure (Vw d)).prod νf)).IsAddHaarMeasure := by
  exact KFPB.exists_nuf' R

theorem integral_jnp (R : RD d) {νf : Measure (Yf d)} (hνf : νf.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ d.schM) {g : Yf d → ℂ} (hg' : g ∈ SB (Yf d)) {b : Vw d → ℂ} (hb : Continuous b) (hb1 : ∀ u, ‖b u‖ ≤ 1) :
    ∫ X, f X * star (b (arc R X) * g (fin d X)) ∂(Measure.map (jnp R) ((volume : Measure (Vw d)).prod νf)) =
      ∫ u, star (b u) * hg R νf f g u := by
  exact KFPB.integral_jnp' R hνf hf hg' hb hb1

theorem arc_add (R : RD d) (X Y : Mx F E d.m d.n) : arc R (X + Y) = arc R X + arc R Y := by
  exact arc_add' R X Y

theorem arc_realAd (R : RD d) (t : ℝ) (X : Mx F E d.m d.n) : arc R (realAd F t • X) = t • arc R X := by
  exact arc_realAd' R t X

theorem fin_add_of (R : RD d) {Z : Mx F E d.m d.n} (hZ : finOne F • Z = 0) (X : Mx F E d.m d.n) :
    fin d (X + Z) = fin d X := by
  exact fin_add_of' R hZ X

theorem fin_realAd_smul {Z : Mx F E d.m d.n} (hZ : finOne F • Z = 0) (t : ℝ) : finOne F • (realAd F t • Z) = 0 := by
  exact fin_realAd_smul' hZ t

theorem gau_eq (R : RD d) (X : Mx F E d.m d.n) : gau R X = (Real.exp (-(2 * Real.pi * ‖arc R X‖ ^ 2)) : ℂ) := by
  exact gau_eq' R X

theorem psi_tw (R : RD d) {W : Mx F E d.m d.n} (hW : finOne F • W = 0) (t : ℝ) (X : Mx F E d.m d.n) :
    d.B.ψ (d.tt (d.gram (realAd F t • tw R W) X)) =
      Complex.exp (4 * Real.pi * Complex.I * t * ⟪arc R W, arc R X⟫_ℝ) := by
  exact psi_tw' R hW t X

theorem psi_sp (R : RD d) {W : Mx F E d.m d.n} (hW : finOne F • W = 0) (s t : ℝ) :
    d.B.ψ (-(⅟(2 : AF F) * spf d ((realAd F s • W) * (incM F d.b.1.toCols₂)ᵀ)
      ((realAd F t • tw R W) * (incM F d.b.1.toCols₁)ᵀ))) =
      Complex.exp (-(2 * Real.pi * Complex.I * s * t * ‖arc R W‖ ^ 2)) := by
  exact psi_sp' R hW s t

end PositivityTheory.SiegelWeilFormula.KFP

end
