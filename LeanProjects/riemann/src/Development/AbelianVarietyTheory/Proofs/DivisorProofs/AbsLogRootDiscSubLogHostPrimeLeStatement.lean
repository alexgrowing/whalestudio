import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLogRootDiscSubLogHostPrimeLe
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abs_logRootDisc_sub_log_hostPrime_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E - Real.log H.d| ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E := by
  first | exact @GlobalTheory.abs_lrd_sub_log_d_le_lrd | exact GlobalTheory.abs_lrd_sub_log_d_le_lrd | (intros; apply GlobalTheory.abs_lrd_sub_log_d_le_lrd <;> assumption)
