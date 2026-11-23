import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.EmbeddingPermutesLetters
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.EmbPerm
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CharExtend
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.EmbTraceSum

namespace Formalism.MainNotions.Ext

theorem permEmb_holds : PermEmb := embedding_permutation

theorem embedding_permutes_letters_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.StandardLatticesGL3.EmbeddingPermutesTypes D := embedding_permutes_letters permEmb_holds D

theorem charExt_holds : CharExt := PI.character_extension_exists

theorem traceSum_holds : TraceSum := sumEqTrace_holds

theorem trace_sum_over_letters_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.StandardLatticesGL3.TraceMapNormalisation D := trace_sum_over_letters traceSum_holds D

theorem induced_type_from_K_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.StandardLatticesGL3.admG1 D := ⟨Formalism.MainNotions.GL3Theta.induced_cm_type D, trace_sum_over_letters_holds D⟩

end Formalism.MainNotions.Ext
