import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

open MeasureTheory

noncomputable section

namespace PI

def AdUnimod : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (μf : Measure I.Gf), μf.IsHaarMeasure → μf.IsMulRightInvariant

end PI

end
