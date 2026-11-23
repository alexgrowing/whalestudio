import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef

noncomputable section

open scoped Classical

namespace PI.ScalarPairDr

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ScalarDr (D : D7) (u u' : D.what₂.Word) : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
    IsRowReps D F0 what₂ → ∀ Λ ∈ what₂, ∀ x y : Carrier (PD D Λ (lf D F0) u'),
      Gval (lf D F0) x.1 ≠ 0 → Gval (lf D F0) y.1 ≠ 0 → ∀ β : (VS D).V ≃ₗ[D.host.E] (VS D).V,
        IsPair Λ (lf D F0) x.1 y.1 β (gS D) → Formalism.MainNotions.S.Lat.s0 Λ (lf D F0) x.1 y.1 β D.R.k = 1 →
          IsScalar Λ (lf D F0) x.1 y.1 β → (Dr (lf D F0) x.1 = 0 ↔ Dr (lf D F0) y.1 = 0)

end D7

end PI.ScalarPairDr
