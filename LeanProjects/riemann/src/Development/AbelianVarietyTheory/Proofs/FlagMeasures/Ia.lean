import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub

noncomputable section

open NumberField

namespace GlobalTheory.RowLatXS

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T : E}

def Ia (Λ : Submodule (𝓞 E) S.V) (F : Formalism.MainNotions.S.FlagG S r T) (a : Fin r) : Submodule (𝓞 E) E :=
  Submodule.span (𝓞 E) {t | ∃ x ∈ Λ, x ∈ F.Xa (a.val + 1) ∧ F.coefX x a = t}

end GlobalTheory.RowLatXS
