import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Saturated

namespace PI.SplitRow

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SplitRow : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → Formalism.L2.SG.Saturated.IsSplitRow D F0 Λ

end PI.SplitRow
