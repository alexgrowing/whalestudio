import Mathlib
import Formalism.HermitianLattices.StatementMaj
import Formalism.HermitianLattices.HermitianLatticesProofs.OpBound

open NumberField Matrix

noncomputable section

namespace Formalism.HermitianLatticesTheory

section MajBasicAux

variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

theorem majBasic_majAt (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (x y : V) :
    majAt b X v x y = star (vecAt b v x) ⬝ᵥ ((((X v)⁻¹)ᴴ * (X v)⁻¹) *ᵥ vecAt b v y) := by
  unfold majAt
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  rfl

end MajBasicAux

end Formalism.HermitianLatticesTheory
