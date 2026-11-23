import Mathlib
import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality
import GroundTheory.ProfiniteCohomology.TorsionDualDefs
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section ResLE

omit [IsTopologicalGroup G] in

theorem continuous_subgroup_inclusion {U V : Subgroup G} (h : V ≤ U) :
    Continuous (Subgroup.inclusion h) :=
  continuous_induced_rng.2 continuous_subtype_val

variable (A : Rep.{u} k G)

def resResHom {U V : Subgroup G} (h : V ≤ U) :
    Rep.res (Subgroup.inclusion h) (Rep.res U.subtype A) ⟶ Rep.res V.subtype A :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem resResHom_hom_apply {U V : Subgroup G} (h : V ≤ U) (a : A) :
    (resResHom A h).hom a = a :=
  rfl

variable [IsDiscreteRep A]

noncomputable def cohomologyResLE {U V : Subgroup G} (h : V ≤ U) (n : ℕ) :
    cohomology (Rep.res U.subtype A) n ⟶ cohomology (Rep.res V.subtype A) n :=
  cohomologyMapAlong (Subgroup.inclusion h) (continuous_subgroup_inclusion h) (resResHom A h) n

theorem cohomologyResLE_eq {U V : Subgroup G} (h : V ≤ U) (n : ℕ) :
    cohomologyResLE A h n = cohomologyMapAlong (Subgroup.inclusion h)
      (continuous_subgroup_inclusion h) (resResHom A h) n :=
  rfl

instance isDiscreteRep_res_quotientToInvariants (W : Subgroup G) (N : Subgroup W) [N.Normal] :
    IsDiscreteRep ((Rep.res W.subtype A).quotientToInvariants N) :=
  isDiscreteRep_quotientToInvariants_of_normal _ _

end ResLE

noncomputable abbrev H2Open (C : Rep.{u} k G) [IsDiscreteRep C] (U : OpenSubgroup G) : Type u :=
  cohomology (Rep.res (U : Subgroup G).subtype C) 2

structure PreClassFormation (C : Rep.{u} k G) [IsDiscreteRep C] where

  inv : ∀ U : OpenSubgroup G, H2Open C U →+ QZ

  isZero_H1_open_subgroups : ∀ U : OpenSubgroup G,
    Limits.IsZero (cohomology (Rep.res (U : Subgroup G).subtype C) 1)

  inv_res : ∀ (U V : OpenSubgroup G) (h : V ≤ U) (x : H2Open C U),
    inv V ((cohomologyResLE C (show (V : Subgroup G) ≤ U from h) 2).hom x) =
      (V : Subgroup G).relIndex U • inv U x

structure ClassFormation (C : Rep.{u} k G) [IsDiscreteRep C] extends PreClassFormation C where

  inv_bijective : ∀ U : OpenSubgroup G, Function.Bijective (inv U)

structure ClassFormationAt (P : Set Nat.Primes) (C : Rep.{u} k G) [IsDiscreteRep C]
    extends PreClassFormation C where

  inv_injective : ∀ U : OpenSubgroup G, Function.Injective (inv U)

  primaryComponent_le_range : ∀ (U : OpenSubgroup G), ∀ p ∈ P,
    ∀ x ∈ AddCommMonoid.primaryComponent QZ (p : ℕ), x ∈ (inv U).range

namespace PreClassFormation

variable {C : Rep.{u} k G} [IsDiscreteRep C] (F : PreClassFormation C)

noncomputable abbrev H2Quotient (C : Rep.{u} k G) [IsDiscreteRep C] (U V : OpenSubgroup G)
    [((V : Subgroup G).subgroupOf U).Normal] : Type u :=
  cohomology ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants
    ((V : Subgroup G).subgroupOf U)) 2

noncomputable def fundamentalClass (U V : OpenSubgroup G)
    [((V : Subgroup G).subgroupOf U).Normal] : H2Quotient C U V :=
  haveI : Nonempty (H2Quotient C U V) := ⟨0⟩
  Function.invFun
    (fun x : H2Quotient C U V =>
      F.inv U ((cohomologyInfl (Rep.res (U : Subgroup G).subtype C)
        ((V : Subgroup G).subgroupOf U) 2).hom x))
    (QZ.mk (1 / ((V : Subgroup G).relIndex U : ℚ)))

end PreClassFormation

end GroundTheory.ProfCoh
