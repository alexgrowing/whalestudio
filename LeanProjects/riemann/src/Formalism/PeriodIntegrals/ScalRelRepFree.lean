import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef

noncomputable section

open scoped Classical

namespace PI.ScalRelRepFree

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

def ScalRel {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
    (Λ : Submodule (𝓞 E) S.V) (g k : ℕ) {T T' : E} (F : LFlag S r T) (F' F'' : LFlag S r T') : Prop :=
  ∃ β : S.V ≃ₗ[E] S.V, IsPair Λ F F' F'' β g ∧ Formalism.MainNotions.S.Lat.s0 Λ F F' F'' β k = 1 ∧ IsScalar Λ F F' F'' β

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ScalRelD (D : D7) {u : D.what₂.Word} (u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (x y : {x : Carrier (PD D Λ (lf D F0) u') // Gval (lf D F0) x.1 ≠ 0}) : Prop :=
  ScalRel Λ (gS D) D.R.k (lf D F0) x.1.1 y.1.1

def ScalarRepFree (D : D7) (u u' : D.what₂.Word) : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → ∀ x y y' : {x : Carrier (PD D Λ (lf D F0) u') // Gval (lf D F0) x.1 ≠ 0},
      Rel Λ (lf D F0) (PD D Λ (lf D F0) u') y.1 y'.1 → ScalRelD D u' F0 Λ x y → ScalRelD D u' F0 Λ x y'

end D7

end PI.ScalRelRepFree
