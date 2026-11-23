import Mathlib
import GroundTheory.ProfiniteCohomology.Shapiro
import GroundTheory.ProfiniteCohomology.ClassFormations.IsIsoCohomologyMapAlongResSubgroupOfHom
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section SubgroupOf

variable {U V : Subgroup G} (h : V ≤ U) (A : Rep.{u} k G)

def resSubgroupOfInvHom :
    Rep.res (Subgroup.subgroupOfEquivOfLe h).toMonoidHom (Rep.res V.subtype A) ⟶
      Rep.res (V.subgroupOf U).subtype (Rep.res U.subtype A) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

variable [IsDiscreteRep A]

@[reassoc]
theorem cohomologyMapAlong_resSubgroupOfHom_comp (n : ℕ) :
    cohomologyMapAlong (Subgroup.subgroupOfEquivOfLe h).symm.toMonoidHom
        (continuous_subgroupOfEquivOfLe_symm h) (resSubgroupOfHom h A) n ≫
      cohomologyMapAlong (Subgroup.subgroupOfEquivOfLe h).toMonoidHom
        (continuous_subgroupOfEquivOfLe h) (resSubgroupOfInvHom h A) n = 𝟙 _ := by
  rw [← cohomologyMapAlong_comp]
  exact cohomologyMapAlong_eq_id _ _ (by ext; rfl) (fun _ => rfl) n

end SubgroupOf

abbrev openSubgroupOf (U V : OpenSubgroup G) : OpenSubgroup (U : Subgroup G) where
  toSubgroup := (V : Subgroup G).subgroupOf U
  isOpen' := V.isOpen.preimage continuous_subtype_val

variable [CompactSpace G] (C : Rep.{u} k G) [IsDiscreteRep C]

noncomputable def cohomologyCoresLE {U V : OpenSubgroup G} (h : V ≤ U) (n : ℕ) :
    cohomology (Rep.res (V : Subgroup G).subtype C) n ⟶
      cohomology (Rep.res (U : Subgroup G).subtype C) n :=
  cohomologyMapAlong (Subgroup.subgroupOfEquivOfLe (show (V : Subgroup G) ≤ U from h)).toMonoidHom
      (continuous_subgroupOfEquivOfLe _) (resSubgroupOfInvHom _ C) n ≫
    cohomologyCores (openSubgroupOf U V) (Rep.res (U : Subgroup G).subtype C) n

theorem cohomologyCoresLE_eq {U V : OpenSubgroup G} (h : V ≤ U) (n : ℕ) :
    cohomologyCoresLE C h n =
      cohomologyMapAlong (Subgroup.subgroupOfEquivOfLe (show (V : Subgroup G) ≤ U from h)).toMonoidHom
          (continuous_subgroupOfEquivOfLe _) (resSubgroupOfInvHom _ C) n ≫
        cohomologyCores (openSubgroupOf U V) (Rep.res (U : Subgroup G).subtype C) n :=
  rfl

theorem cohomologyResLE_comp_cohomologyCoresLE {U V : OpenSubgroup G} (h : V ≤ U) (n : ℕ) :
    cohomologyResLE C (show (V : Subgroup G) ≤ U from h) n ≫ cohomologyCoresLE C h n =
      (V : Subgroup G).relIndex U • 𝟙 _ := by
  rw [cohomologyResLE_eq_cohomologyRes_comp, cohomologyCoresLE, Category.assoc,
    cohomologyMapAlong_resSubgroupOfHom_comp_assoc]
  exact cohomologyRes_comp_cohomologyCores (openSubgroupOf U V) (Rep.res (U : Subgroup G).subtype C) n

theorem cohomologyCoresLE_cohomologyResLE {U V : OpenSubgroup G} (h : V ≤ U) (n : ℕ)
    (x : cohomology (Rep.res (U : Subgroup G).subtype C) n) :
    (cohomologyCoresLE C h n).hom ((cohomologyResLE C (show (V : Subgroup G) ≤ U from h) n).hom x) =
      (V : Subgroup G).relIndex U • x := by
  have := congrArg (fun φ => φ.hom x) (cohomologyResLE_comp_cohomologyCoresLE C h n)
  simpa using this

end GroundTheory.ProfCoh
