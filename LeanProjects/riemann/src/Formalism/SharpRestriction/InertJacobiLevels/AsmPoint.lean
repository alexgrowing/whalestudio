import Formalism.SharpRestriction.InertJacobiLevels.AsmTie

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField

abbrev wtOf (D : D7) (a : ℕ → ℤ) : D.host.TT → ℤ := fun t => a (t : D.R.A).val

abbrev kapX (sc : Scale) (C : FC) (X : Core) (Del : ℝ) : KapI := kapIOf X.1 sc ((X.1.k : ℝ) * (4 * Del)) C.GK

abbrev epX (sc : Scale) (C : FC) (X : Core) : ℕ → ℕ := epOf C.cX.Ce X.1 sc

end Formalism.MainNotions.Inhab

end
