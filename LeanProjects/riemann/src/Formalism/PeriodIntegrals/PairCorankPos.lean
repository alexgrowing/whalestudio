import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub

noncomputable section

open scoped Classical

namespace PI.PairCorankPos

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

def CorankPosG : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r k : ℕ),
    finrank E S.V = k + 2 * r + 1 →
    ∀ Λ : Submodule (𝓞 E) S.V, Submodule.IsLattice E Λ →
    ∀ (T T' : E) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V),
      IsLift Λ F → IsLift Λ F' → Gval F F' ≠ 0 → 1 ≤ Formalism.MainNotions.S.Lat.s0 Λ F F' F'' β k

end PI.PairCorankPos
