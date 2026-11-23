import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec

noncomputable section

open Classical

namespace GlobalTheory.LevelVecNorm

def locH {E : Type} [Field E] [NumberField E] (Pg : Finset (Formalism.L2.DIV.Pl E)) {r : ℕ}
    (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (Formalism.L2.DIV.kP PP.1))) (PP : Formalism.L2.DIV.Pl E) :
    Subgroup (GL (Fin r) (Formalism.L2.DIV.kP PP)) :=
  if h : PP ∈ Pg then Hl ⟨PP, h⟩ else ⊤

open Classical in

def suppInd {k : Type} [CommRing k] (r : ℕ) {b a : ℕ} (H : Subgroup (GL (Fin r) k)) (z : Matrix (Fin b) (Fin a) k) : ℝ :=
  if Formalism.IndefR.Datum.LowZero r z ∧ ∃ g ∈ H, ((g : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) = Formalism.IndefR.Datum.topL r z then 1 else 0

end GlobalTheory.LevelVecNorm

end
