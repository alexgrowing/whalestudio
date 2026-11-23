import Formalism.SharpRestriction.InertJacobiLevels.AsmRec

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField

def bTop2 (sc : Scale) (C : FC) (R : Ranks) : ℝ :=
  sc.b' + 2 * (R.n : ℝ) * sc.delta1 * sc.x ^ sc.eps * G.La C.GK sc * sc.b' / (R.k : ℝ)

end Formalism.MainNotions.Inhab

end
