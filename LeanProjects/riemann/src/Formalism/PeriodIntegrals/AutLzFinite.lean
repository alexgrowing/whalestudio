import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic

noncomputable section

open scoped Classical

namespace PI.AutLzFinite

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def AutLzFin : Prop :=
  (VS D).SigOK → ∀ (Tn : ℕ), 0 < Tn → ∀ (F0 : FlagG (VS D) D.R.rS ((Tn : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → (autLz D F0 Λ).Finite

end PI.AutLzFinite
