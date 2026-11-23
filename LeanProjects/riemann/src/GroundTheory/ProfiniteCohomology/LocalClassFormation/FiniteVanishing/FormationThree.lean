import Mathlib
import GroundTheory.ProfiniteCohomology.ClassFormations
import GroundTheory.ProfiniteCohomology.Colimit
import GroundTheory.ProfiniteCohomology.ShapiroDefs
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.TateThree
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in

theorem exists_openSubgroup_subgroupOf_eq (U : OpenSubgroup G) (N : Subgroup (U : Subgroup G))
    (hN : IsOpen (N : Set (U : Subgroup G))) :
    ∃ V : OpenSubgroup G, V ≤ U ∧ (V : Subgroup G).subgroupOf U = N := by
  refine ⟨⟨N.map (U : Subgroup G).subtype, ?_⟩, Subgroup.map_subtype_le N, ?_⟩
  · exact U.isOpen.isOpenMap_subtype_val _ hN
  · exact Subgroup.comap_map_eq_self_of_injective (U : Subgroup G).subtype_injective N

variable {C : Rep.{0} (ULift.{0} ℤ) G} [IsDiscreteRep C] (F : ClassFormation C)

include F in

theorem ClassFormation.subsingleton_groupCohomology_three_quot (U : OpenSubgroup G)
    (N : Subgroup (U : Subgroup G)) [N.Normal] (hN : IsOpen (N : Set (U : Subgroup G))) :
    Subsingleton (groupCohomology
      ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants N) 3) := by
  obtain ⟨V, hVU, rfl⟩ := exists_openSubgroup_subgroupOf_eq U N hN
  have : ((V : Subgroup G).subgroupOf U).FiniteIndex :=
    finiteIndex_openSubgroup (⟨_, hN⟩ : OpenSubgroup (U : Subgroup G))
  have : Finite ((U : Subgroup G) ⧸ (V : Subgroup G).subgroupOf U) :=
    Subgroup.finite_quotient_of_finiteIndex
  let : Fintype ((U : Subgroup G) ⧸ (V : Subgroup G).subgroupOf U) := Fintype.ofFinite _
  exact subsingleton_groupCohomology_three_of_tate _ (F.groupFundamentalClass U V)
    (fun S => (F.tate_hypotheses hVU S).1) (fun S => (F.tate_hypotheses hVU S).2.1)
    (fun S => (F.tate_hypotheses hVU S).2.2)

include F in

theorem ClassFormation.subsingleton_cohomology_three (U : OpenSubgroup G) :
    Subsingleton (cohomology (Rep.res (U : Subgroup G).subtype C) 3) := by
  have h0 : ∀ z : cohomology (Rep.res (U : Subgroup G).subtype C) 3, z = 0 := fun z => by
    obtain ⟨W, w, rfl⟩ := exists_inflation_eq (Rep.res (U : Subgroup G).subtype C) 3 z
    have := F.subsingleton_groupCohomology_three_quot U (W : Subgroup (U : Subgroup G)) W.isOpen
    rw [Subsingleton.elim w 0, map_zero]
  exact ⟨fun x y => by rw [h0 x, h0 y]⟩

end GroundTheory.ProfCoh
