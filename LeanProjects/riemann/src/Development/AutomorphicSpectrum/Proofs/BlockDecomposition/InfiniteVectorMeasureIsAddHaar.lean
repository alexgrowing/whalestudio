import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.CutOff

variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (k : ℕ)

noncomputable def rowInfEquiv : (Fin k → InfiniteAdeleRing E) ≃+ (Fin k → Cinf E) :=
  AddEquiv.piCongrRight fun _ => (infEq E).symm.toAddEquiv

theorem nuInf_isAddHaarMeasure : (nuInf E k).IsAddHaarMeasure := by
  have hc : Continuous (rowInfEquiv E k) :=
    continuous_pi fun i => (GASplit.continuous_infEq_symm E).comp (continuous_apply i)
  have hc' : Continuous (rowInfEquiv E k).symm :=
    continuous_pi fun i => (continuous_infEq E).comp (continuous_apply i)
  have hp : (Measure.pi fun _ : Fin k => GroundTheory.Global.infiniteAdeleMeasure E).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  exact AddEquiv.isAddHaarMeasure_map _ (rowInfEquiv E k) hc hc'

end GlobalTheory.CompanionTheory.CutOff
