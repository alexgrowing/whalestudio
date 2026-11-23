import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.GoodModelAll
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.AnalyticTransOfAdd
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Several
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CurveIntegerMultiplicationSeries
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.InVarAddInVarNeZero

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.A (logSer expSer wpReg)
open Formalism.G (unitBall)

namespace KJ

theorem phC_eq (p : ℕ) [Fact p.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[p]) :
    phC p L ι = Formalism.L2.Th1.E.phL p L ι := by
  unfold phC Formalism.L2.Th1.E.phL
  rw [Formalism.L2.Th1.E.wpBridge p L ι]

theorem phSum_one {K : Type} [Field K] {n : Type} [Fintype n] (ph : PowerSeries K) :
    Formalism.L2.Th1.G.phSum (fun _ : n => (1 : K)) ph = Formalism.L2.Th1.E.phSum ph := by
  unfold Formalism.L2.Th1.G.phSum Formalism.L2.Th1.E.phSum Formalism.InvariantFactorPaths.G7.at1
  exact Finset.sum_congr rfl fun i _ => one_smul _ _

theorem toZ_thetaProd {K : Type} [Field K] {κ n : Type} [Fintype κ] [Fintype n] {linv : PowerSeries K}
    (h0 : PowerSeries.constantCoeff linv = 0) (r : κ → K) (H : κ → n → PowerSeries K) :
    Formalism.L2.Th1.G.toZ linv (Formalism.L2.Th1.E.thetaProd r H) =
      Formalism.L2.Th1.E.thetaProd r (fun k i => PowerSeries.subst linv (H k i)) := by
  unfold Formalism.L2.Th1.E.thetaProd Formalism.InvariantFactorPaths.G7.at1
  rw [← Formalism.L2.Th1.G.toZHom_apply h0, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_prod]
  congr 1
  · rw [MvPowerSeries.c_eq_algebraMap, AlgHom.commutes]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Formalism.L2.Th1.G.toZHom_apply, Formalism.L2.Th1.G.toZ_subst_X h0]

end KJ

theorem kernel_bounds_joint : KernelJoint := by
  intro p _ L ι hp2 hW n _ ω₀ hω hω2 κ _ r s N hr hN hpN hs
  have hlp := Formalism.L2.Th1.C.WeierstrassCurveSeries.logPair (curveL p L ι)
  obtain ⟨hl0, -, hv0, -, hlv⟩ := hlp
  have hph : PowerSeries.constantCoeff (Formalism.L2.Th1.E.phL p L ι) = 0 :=
    Formalism.L2.Th1.E.AnaSys.cc_phL p L ι
  have hT := (Formalism.L2.Th1.E.th0Analytic p L ι hp2 hW ω₀ hω hω2).2
  obtain ⟨e1, hInt⟩ := Formalism.L2.Th1.E.prodInt ℂ_[p] κ n (Formalism.L2.Th1.E.phL p L ι) r
    (fun k i => Formalism.L2.Th1.B.fExp (Formalism.L2.Th1.E.phL p L ι) *
      Formalism.L2.Th1.E.inU p L ι (Formalism.L2.Th1.F.opU L (s k i) (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))
    hph hr (fun k i => (hT (s k i) N hN hpN (hs k i)).1)
  refine ⟨_, fun d => hInt d, ?_⟩
  rw [KJ.phC_eq, KJ.phSum_one]
  change _ = Formalism.L2.Th1.G.toZ _ (Formalism.DworkPowerSeriesWeights.mvExp _ * _)
  rw [← e1, KJ.toZ_thetaProd hv0]
  unfold thetaZ
  congr 1
  funext k i
  change _ = PowerSeries.subst _ (Formalism.L2.Th1.B.fExp (-(Formalism.L2.Th1.E.phL p L ι)) * _)
  rw [← mul_assoc, ← Formalism.L2.Th1.B.fExp_add (by rw [map_neg]; exact neg_eq_zero.2 hph) hph,
    neg_add_cancel, Formalism.L2.Th1.B.ParO.fExp_zero, one_mul]
  unfold Formalism.L2.Th1.E.inU
  rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hl0)
    (PowerSeries.HasSubst.of_constantCoeff_zero' hv0), hlv]
  exact (PowerSeries.X_subst _).symm

end Formalism.L2.Th1.Top
