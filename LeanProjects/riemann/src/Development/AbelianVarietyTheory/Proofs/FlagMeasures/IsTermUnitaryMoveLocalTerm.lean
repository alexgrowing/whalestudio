import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTermLocalTermMoveOfIsometry

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

namespace GlobalTheory.LocOver

theorem isTerm_unitary_move {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    (r : ℕ) (g : V ≃ₗ[E] V) (t : Term V M r) (hg : IsUnitary H g) (ht : H.IsTerm t) :
    H.IsTerm (GlobalTheory.LocOver.move g t) :=
  GlobalTheory.LocOver.MoveTerm.isTerm_move H g t hg ht

end GlobalTheory.LocOver
