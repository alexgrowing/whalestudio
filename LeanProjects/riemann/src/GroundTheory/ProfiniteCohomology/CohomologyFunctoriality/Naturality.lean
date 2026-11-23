import Mathlib
import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality
import GroundTheory.ProfiniteCohomology.ContinuousCochains.Functoriality
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Identity

variable {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B]

theorem cochainsMapAlong_id_eq_cochainsMap (f : A ⟶ B) :
    cochainsMapAlong (MonoidHom.id G) continuous_id f = cochainsMap f := by
  ext n x : 3
  rfl

theorem cohomologyMapAlong_id_eq_cohomologyMap (f : A ⟶ B) (n : ℕ) :
    cohomologyMapAlong (MonoidHom.id G) continuous_id f n = cohomologyMap f n := by
  rw [cohomologyMapAlong, cochainsMapAlong_id_eq_cochainsMap]
  rfl

end Identity

section Comparison

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {A : Rep.{u} k G} {B : Rep.{u} k H} [IsDiscreteRep A] [IsDiscreteRep B]

end Comparison

section Restriction

variable (A : Rep.{u} k G) [IsDiscreteRep A]

@[reassoc]
theorem cohomologyMap_comp_cohomologyRes {A' : Rep.{u} k G} [IsDiscreteRep A'] (g : A ⟶ A')
    (S : Subgroup G) (n : ℕ) :
    cohomologyMap g n ≫ cohomologyRes A' S n =
      cohomologyRes A S n ≫ cohomologyMap ((Rep.resFunctor S.subtype).map g) n := by
  rw [← cohomologyMapAlong_id_eq_cohomologyMap, ← cohomologyMapAlong_id_eq_cohomologyMap]
  exact cohomologyRes_naturality A g S n

@[reassoc]
theorem cohomologyRes_comp_cohomologyToGroupCohomology (S : Subgroup G) (n : ℕ) :
    cohomologyRes A S n ≫ cohomologyToGroupCohomology (Rep.res S.subtype A) n =
      cohomologyToGroupCohomology A n ≫ groupCohomology.map S.subtype (𝟙 _) n :=
  cohomologyRes_comp_homologyMap_cochainsComplexι A S n

end Restriction

section Inflation

variable (A : Rep.{u} k G) [IsDiscreteRep A] (N : Subgroup G) [N.Normal]

instance isDiscreteRep_quotientToInvariantsFunctor_obj :
    IsDiscreteRep ((Rep.quotientToInvariantsFunctor k N).obj A) :=
  isDiscreteRep_quotientToInvariants_of_normal A N

@[reassoc]
theorem cohomologyInfl_comp_cohomologyToGroupCohomology (n : ℕ) :
    cohomologyInfl A N n ≫ cohomologyToGroupCohomology A n =
      cohomologyToGroupCohomology (A.quotientToInvariants N) n ≫
        groupCohomology.map (QuotientGroup.mk' N) (Rep.ofHom (A.ρ.quotientToInvariants_lift N)) n :=
  cohomologyInfl_comp_homologyMap_cochainsComplexι A N n

end Inflation

end GroundTheory.ProfCoh
