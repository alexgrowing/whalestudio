import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.FrameStatement : SmallSt → FrameSt := by
  first | exact @GlobalTheory.FrameOf.frameSt_of_smallSt | exact GlobalTheory.FrameOf.frameSt_of_smallSt | (intros; apply GlobalTheory.FrameOf.frameSt_of_smallSt <;> assumption)
