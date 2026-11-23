import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.NormalizedHeckeData

noncomputable section

open Formalism.BasicNotions Formalism.L2

namespace GlobalTheory.HeightCounting

structure NTiedGPlaceholder (D : D7) : Type

def NTiedGPlaceholder.liftToGlobalDescentData {D : D7} (_T : NormalizedHeckeDataPlaceholder D) : NTiedGPlaceholder D := ⟨⟩

end GlobalTheory.HeightCounting

end
