import Formalism.WachLatticeTwists.TorsionKernelSplitting.Statement
import Formalism.WachLatticeTwists.StatementSplit
import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.Bridge

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JS

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR

section Congr
variable {O Cs : Type} [CommRing O] [AddCommGroup Cs] [Module O Cs]

theorem len_congr {P Q : Submodule O Cs} (h : P = Q) (Im : Submodule O Cs) :
    Module.length O (Q ⧸ Im.comap Q.subtype) = Module.length O (P ⧸ Im.comap P.subtype) := by
  subst h; rfl

end Congr

end Formalism.RepresentationBoundsCohomology.JS
