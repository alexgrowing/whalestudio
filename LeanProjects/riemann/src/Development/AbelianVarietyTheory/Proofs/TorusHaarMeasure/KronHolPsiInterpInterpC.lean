import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfB
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureStatements
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.UnfoldPoincareOnto
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetFderivNeZeroOrbit
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.KronHolPsiOf
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContinuousOnOfCharts
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableIndicatorOfContOn
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralLtTopOfCutoff
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.WeightContDiffOn
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.VanishOfSimpleZero
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.StrictMargin

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.InterpolationClosed

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem kronHolPsi : KronHolPsiStatement (E := E) :=
  GlobalTheory.KronAssembly.kronHolPsi_of
    GlobalTheory.FrameMeasureClosed.measure_statements.2.2.2
    (GlobalTheory.OrbitCoord.det_fderiv_ne_zero_orbit GlobalTheory.FrameMeasureClosed.measure_statements.1)
    (GlobalTheory.KronMetric.kronMetric GlobalTheory.NormFactor.nfac_transform)
    GlobalTheory.kronSolve
    (GlobalTheory.KronOff.vanish_off GlobalTheory.FrameMeasureClosed.measure_statements.2.1
      GlobalTheory.vanishAtS_holds GlobalTheory.NormFactor.nfac_transform)
    (GlobalTheory.KronValue.value_and_integrability GlobalTheory.vanishAtS_holds)

theorem interp : InterpStatement (E := E) :=
  interp_of GlobalTheory.PoincareClosed.unfold_poincare_onto.2.2.2.1 kronHolPsi

theorem interpC : InterpCStatement (E := E) :=
  GlobalTheory.InterpC.main GlobalTheory.PoincareClosed.unfold_poincare_onto.2.2.2.1 kronHolPsi

theorem kronHolPsi_interp_interpC :
    (KronHolPsiStatement (E := E)) ∧ (InterpStatement (E := E)) ∧ (InterpCStatement (E := E)) :=
  ⟨kronHolPsi, interp, interpC⟩

end GlobalTheory.InterpolationClosed
