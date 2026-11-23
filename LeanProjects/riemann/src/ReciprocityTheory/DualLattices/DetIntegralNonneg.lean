import ReciprocityTheory.DualLattices.FrobeniusOfGroupDivisorsRank
import ReciprocityTheory.DualLattices.KilledGen
import ReciprocityTheory.DualLattices.IdemGen

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

namespace Cons

def lenCoker {R : Type*} [CommRing R] (v : AddValuation R (WithTop ℝ)) {m h : ℕ}
    (B : Matrix (Fin m) (Fin h) R) : WithTop ℝ :=
  Finset.univ.inf fun g : Fin m → Fin h => v (B.submatrix id g).det

def ThmAiii {R : Type*} [CommRing R] (v : AddValuation R (WithTop ℝ)) {m h : ℕ}
    (α : Matrix (Fin m) (Fin h) R) (l1 : ℝ) : Prop :=
  lenCoker v α = (l1 : WithTop ℝ)

end Cons

section Bridge

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

def IsLogVal (v : Valuation C NNReal) (b : ℝ) (vA : AddValuation R (WithTop ℝ)) : Prop :=
  ∀ r : R, r ≠ 0 → vA r = ((Real.logb b (v (algebraMap R C r)) : ℝ) : WithTop ℝ)

end Bridge

end ReciprocityTheory.PGsh.Up
