import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef

noncomputable section

open scoped Classical

namespace PI.NormRepLift

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7) (u u' : D.what₂.Word)

def NormRepStep : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → ∀ t : TermsOf D u' F0 Λ,
      IsRel Λ (lf D F0) (PD D Λ (lf D F0) u') D.host.F t → IsGen Λ (lf D F0) (PD D Λ (lf D F0) u') (gS D) t →
        ∃ F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E),
          Formalism.L2.SG.TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F' ∧ AdmWit Λ (gS D) (lf D F0) F' 1

end PI.NormRepLift
