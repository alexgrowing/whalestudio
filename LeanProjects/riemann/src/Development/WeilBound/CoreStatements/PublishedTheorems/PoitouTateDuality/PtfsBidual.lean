import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs

noncomputable section

open CategoryTheory GroundTheory.ProfCoh

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem bidualCmp {G : Type} [Group G] (D A : Rep.{0} (ULift.{0} ℤ) G) (N : ℕ) [NeZero N]
    (hD : Nonempty (D ≃+ ZMod N)) [Finite A] (hA : ∀ m : A, N • m = 0) :
    ∃ eB : A.V ≃+ (dualRep D (dualRep D A)).V,
      ∀ g a, eB (A.ρ g a) = (dualRep D (dualRep D A)).ρ g (eB a) := by
  have hb := bijective_toDualDual (D := D) (M := A) hD hA
  let f : A.V →+ (dualRep D (dualRep D A)).V :=
    { toFun := (toDualDual D A).hom, map_zero' := map_zero _, map_add' := map_add _ }
  refine ⟨AddEquiv.ofBijective f hb, fun g a => ?_⟩
  exact Rep.hom_comm_apply (toDualDual D A) g a

end PositivityTheory.Lit1.PTN
