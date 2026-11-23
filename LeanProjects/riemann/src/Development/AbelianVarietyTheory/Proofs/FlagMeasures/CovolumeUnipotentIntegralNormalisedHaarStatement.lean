import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeUnipotentIntegralNormalisedHaar
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBCovN
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_unipotentIntegral_normalisedHaar : Formalism.L2.SG.Pf.LoopBCovN.CovNFormula := by
  first | exact @GlobalTheory.CovNFormulaPf.main | exact GlobalTheory.CovNFormulaPf.main | (intros; apply GlobalTheory.CovNFormulaPf.main <;> assumption)
