import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan

noncomputable section

namespace Formalism.MainNotions.DIV.Align

open Formalism.BasicNotions Formalism.MainNotions

def SmallFirstModulusBelowScale {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), ((AbsolutelyIrreducibleSpan.q0 (Fm.D x i) : ℕ) : ℝ) < (Fm.L x i).sc.X'

end Formalism.MainNotions.DIV.Align

end
