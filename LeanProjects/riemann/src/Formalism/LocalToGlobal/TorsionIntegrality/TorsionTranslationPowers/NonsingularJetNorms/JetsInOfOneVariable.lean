import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormFromDatum
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ConstantCoeffInVarEqZero
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Hurwitz
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.HurwitzB

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.E

open Formalism.DworkPowerSeriesWeights (Integral mvExp mfact)
open Formalism.InvariantFactorPaths.G7 (at1)
open Formalism.L2.Th1.C (IsLogPair IsOneUnit jet)
open Formalism.L2.Th1.G (JetsIn JetsIn1)
open CompatibleChartOperations

namespace JetIntegrality

variable {K : Type} [Field K] {n : Type}

theorem subst_single_var [Finite n] {linv : PowerSeries K} (h0 : PowerSeries.constantCoeff linv = 0) (i : n)
    (g : PowerSeries K) :
    MvPowerSeries.subst (fun j : n => (at1 j linv : MvPowerSeries n K)) (at1 i g) =
      at1 i (PowerSeries.subst linv g) := by
  have ha : ∀ j : n, MvPowerSeries.constantCoeff (at1 j linv : MvPowerSeries n K) = 0 :=
    fun j => constantCoeff_inVar_eq_zero j h0
  have h := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  unfold at1 at ha h ⊢
  rw [Formalism.L2.Th1.C.Pts.substMv_subst (MvPowerSeries.constantCoeff_X i) ha, MvPowerSeries.subst_X h,
    Formalism.L2.Th1.C.Pts.subst_subst h0 (MvPowerSeries.constantCoeff_X i)]

end JetIntegrality

end Formalism.L2.Th1.E
