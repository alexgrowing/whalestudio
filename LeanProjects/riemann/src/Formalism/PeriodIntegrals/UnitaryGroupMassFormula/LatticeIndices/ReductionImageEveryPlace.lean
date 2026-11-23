import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MatRMulMatC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ReductionImageOfBasis

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

theorem stAdaptBasisA_holds {D : D7} (X : HidaSetting D) (p : TypX X) : StAdaptBasisA X p :=
  adaptA_holds X p

theorem reduction_image_every_place {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (p : TypX X) : LevelReductionImage X hb p :=
  reduction_image_of_basis X p hb (stAdaptBasisA_holds X p)

end MassDataIdxSteps
