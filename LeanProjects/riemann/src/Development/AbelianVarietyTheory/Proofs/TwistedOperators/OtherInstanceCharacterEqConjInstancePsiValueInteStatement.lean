import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OtherInstanceCharacterEqConjInstancePsiValueInte
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CPAsIdeal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChiSRfl
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.otherInstanceCharacter_eq_conjInstancePsiValue_integral : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (κ : GA D (Yc D 0)), ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset → GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ X.chi2 ((iotaX X h).toMulEquiv κ).2 = GlobalTheory.SeeConjChar.chiS X h (GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ)) := by
  first | exact @GlobalTheory.SeeConjChar.argT_mem_intAf_and_chi2_eq_chiS_of_mem_Kset | exact GlobalTheory.SeeConjChar.argT_mem_intAf_and_chi2_eq_chiS_of_mem_Kset | (intros; apply GlobalTheory.SeeConjChar.argT_mem_intAf_and_chi2_eq_chiS_of_mem_Kset <;> assumption)
