import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedTypePrimePlacesChoiceOnePerConjugatePair
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsReductionActionChosenPlaces
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedTypePrimePlaces_choice_one_per_conjugate_pair : ∀ (D : D7) (X : HidaSetting D), GlobalTheory.RowLev.IsChoice X.B.I D.host.g D.nd.PlG (fun k v => Formalism.L2.SG.Pf.RowDictPf.wB X (D.naut.plGw k v)) := by
  first | exact @GlobalTheory.RowLev.FixedChoice.isChoice_wB_plGw | exact GlobalTheory.RowLev.FixedChoice.isChoice_wB_plGw | (intros; apply GlobalTheory.RowLev.FixedChoice.isChoice_wB_plGw <;> assumption)
