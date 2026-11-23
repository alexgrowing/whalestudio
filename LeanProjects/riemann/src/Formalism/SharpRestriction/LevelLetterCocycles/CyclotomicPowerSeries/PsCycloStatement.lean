import Mathlib

noncomputable section

namespace LevelStatements.Lv

open PowerSeries

def PsCycloStatement : Prop :=
  ∀ (O : Type) [CommRing O] (l : ℕ), l.Prime → ∀ (φ : PowerSeries O →ₐ[O] PowerSeries O),
    φ X = (1 + X) ^ l - 1 → ∀ (q : PowerSeries O) (w : (PowerSeries O)ˣ),
    q = (w : PowerSeries O) * (((Polynomial.cyclotomic l O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) →
    ∀ s : ℕ, ∃ w' : (PowerSeries O)ˣ, (⇑φ)^[s] q = (w' : PowerSeries O) *
      (((Polynomial.cyclotomic (l ^ (s + 1)) O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O)

end LevelStatements.Lv
