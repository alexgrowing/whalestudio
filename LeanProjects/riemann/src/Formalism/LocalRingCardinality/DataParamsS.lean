import Formalism.LocalRingCardinality.DataParams₂
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

noncomputable section

namespace Formalism.BasicNotions.SizeData₂

def hsSq {D : Formalism.BasicNotions.D7} (_L : Formalism.BasicNotions.SizeData₂ D) (u u' : D.what₂.Word) : ℝ := Formalism.MainNotions.S.hsSqD D u u'

def hsDiag {D : Formalism.BasicNotions.D7} (_L : Formalism.BasicNotions.SizeData₂ D) (u : D.what₂.Word) : ℝ := Formalism.MainNotions.S.hsDiagD D u

end Formalism.BasicNotions.SizeData₂

end
