import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

noncomputable section

namespace PI.AdelFinVol

open MeasureTheory

def AdelFinVol : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (μf : Measure I.Gf) [SigmaFinite μf], μf.IsHaarMeasure →
    ∀ fund : Set I.GA, I.IsFundDom (I.muA μf) fund → I.muA μf fund ≠ ⊤

end PI.AdelFinVol
