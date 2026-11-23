import Formalism.PieriBlockIdeals.StatementDown
import Formalism.PieriBlockIdeals.PieriColumnMinors.WeightBounds
import Formalism.PieriBlockIdeals.PieriColumnMinors.ColumnsPieriSkeleton
import Formalism.PieriBlockIdeals.PieriColumnMinors.RealOfSkeleton
import Formalism.PieriBlockIdeals.PieriColumnMinors.IrreducibleGeneration

namespace Formalism.CohomologicalDescent.Down

theorem hG : LD.LemmaDGraded :=
  LR.real_of_pieri LPR.pieri_real_form (ColumnMinorsFromPieri.columns_real_of_pieri_real LPR.pieri_real_form)

theorem hLG : LD.LemmaDLastGraded := LD.last_graded_of_graded_alone hG

theorem hL : LD.LemmaDLast := by
  unfold LD.LemmaDLast
  intro l p q w M lam2 hl ha hb eL hE i μ hμ
  exact hLG l p q w M lam2 (fun _ => 0) hl ha hb antitone_const _ eL (fun μ2 _ => hE μ2) i μ hμ le_rfl

theorem hD : LD.LemmaD := by
  unfold LD.LemmaD LD.LemmaDAt
  intro l p q w lam2 hl ha hb eL hE i μ hμ
  exact hG l p q w lam2 (fun _ => 0) hl ha hb antitone_const _ eL (fun μ2 _ => hE μ2) i μ hμ le_rfl

theorem inclusion_w_real_holds : InclWReal := ShortWeightBounds.inclusion_w_real_holds hG

end Formalism.CohomologicalDescent.Down
