import Mathlib
import GroundTheory.TateCohomology.CoresRes
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem tateCores_app_tateRes_app_apply (S : Subgroup G) [Fintype S] (A : Rep.{u} k G) (n : ℤ)
    (x : tateCohomology A n) :
    ((tateCores S n).app A).hom (((tateRes S n).app A).hom x) = S.index • x := by
  have h := congrArg (fun f => f.hom x) (tateRes_app_comp_tateCores_app S A n)
  simpa using h

end GroundTheory.GroupCoh
