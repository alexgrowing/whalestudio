import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LowerTwistedCompatibleOfEvaluationBranching
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
import Formalism.SharpRestriction.Divisibility.HookProducts.AdmPtTw
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerTwistedCompatible_of_evaluationBranching : ∀ (D : D7) (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup), GlobalTheory.PerQ.LowerTieTwAt D T u μ → Formalism.MainNotions.DIV.HookProducts.AdmPtTw.LowerTieTwAt D T u μ := by
  first | exact @GlobalTheory.PerQ.lowerTieTwAt_to_lib | exact GlobalTheory.PerQ.lowerTieTwAt_to_lib | (intros; apply GlobalTheory.PerQ.lowerTieTwAt_to_lib <;> assumption)
