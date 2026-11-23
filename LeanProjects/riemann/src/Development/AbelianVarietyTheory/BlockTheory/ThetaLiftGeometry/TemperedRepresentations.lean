import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

namespace GlobalTheory.IndefiniteRowSideFullHecke.TemperedRepresentations

open Formalism.BasicNotions Formalism.MainNotions.N

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

def TemperedRank (N : NData R H what₂) (A : NAut N) (a : ℕ) : Prop :=
  ∀ π : A.CG a, A.csd π → A.ralg π → ∀ w : PlE H, A.tempered (A.locG π w)

def Tempered (N : NData R H what₂) (A : NAut N) : Prop :=
  ∀ (a : ℕ), 1 ≤ a → ∀ π : A.CG a, A.csd π → A.ralg π →
    ∀ w : PlE H, A.tempered (A.locG π w)

end GlobalTheory.IndefiniteRowSideFullHecke.TemperedRepresentations
