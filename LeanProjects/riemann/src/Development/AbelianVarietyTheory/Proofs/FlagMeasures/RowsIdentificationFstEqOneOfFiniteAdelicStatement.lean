import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsIdentificationFstEqOneOfFiniteAdelic
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsReductionActionChosenPlaces
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowsIdentification_fst_eq_one_of_finiteAdelic : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (g : Formalism.L2.Theta.GA D (D.sp.Y 0)), g ∈ GfC (D.sp.Y 0) → (Formalism.L2.SG.RowsJoinPinned.iotaX X h g).1 = 1 := by
  first | exact @GlobalTheory.RealTrivIota.iotaX_fst_eq_one_of_mem_GfC | exact GlobalTheory.RealTrivIota.iotaX_fst_eq_one_of_mem_GfC | (intros; apply GlobalTheory.RealTrivIota.iotaX_fst_eq_one_of_mem_GfC <;> assumption)
