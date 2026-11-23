import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

noncomputable section

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf

def NOCocompact {D : D7} (X : HidaSetting D) (u : D.what₂.Word) : Prop :=
  ∃ C : Set X.B.I.Ginf, IsCompact C ∧ ∀ x ∈ X.NinfU u, ∃ s ∈ NOinf X u, ∃ c ∈ C, x = s * c

def NOCocompactC : Prop := ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), NOCocompact X u

end Formalism.L2.SG.Pf
