import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo

noncomputable section

open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace UpperTheory.KN

variable {G O : Type} (LL : Type) [Group G] [CommRing O] [Field LL] [Algebra O LL]

def actN {ι : Type} {n : ℕ} (N : ι → (G →* Matrix (Fin n) (Fin n) O)) (g : G) (v : ι → Fin n → LL) :
    ι → Fin n → LL := fun j => ((N j g).map (algebraMap O LL)).mulVec (v j)

def HasPres {X : Type} {n : ℕ} (N : X → (G →* Matrix (Fin n) (Fin n) O)) {Q : Type} [AddCommGroup Q] [Module O Q]
    (actQ : G → Q → Q) (f : G → Q) : Prop :=
  ∃ (a : ℕ) (x : Fin a → X) (E : Fin a → Fin n → LL) (Y : Submodule O (Fin a → Fin n → LL)) (_ : Y.FG)
    (hst : ∀ g, ∀ y ∈ Y, actN LL (fun j => N (x j)) g y ∈ Y)
    (hE : ∀ g, actN LL (fun j => N (x j)) g E - E ∈ Y) (φ : ↥Y →ₗ[O] Q),
    (∀ (g : G) (y : ↥Y), φ ⟨_, hst g y.1 y.2⟩ = actQ g (φ y)) ∧ ∀ g, f g = φ ⟨_, hE g⟩

end UpperTheory.KN

end
