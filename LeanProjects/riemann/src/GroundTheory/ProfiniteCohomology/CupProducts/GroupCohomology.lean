import Mathlib
import GroundTheory.ProfiniteCohomology.CupProducts.Functoriality
import GroundTheory.ProfiniteCohomology.ColimitDefs
import GroundTheory.TateCohomology.CupProduct
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory TensorProduct

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Comparison

variable {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] {p q n : ℕ}

theorem cohomologyToGroupCohomology_cohomologyπ (x : cocycles A p) :
    cohomologyToGroupCohomology A p (cohomologyπ A p x) =
      groupCohomology.π A p (HomologicalComplex.cyclesMap (cochainsComplexι A) p x) :=
  ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality (cochainsComplexι A) p) x

theorem iCocycles_cyclesMap_cochainsComplexι (x : cocycles A p) :
    groupCohomology.iCocycles A p (HomologicalComplex.cyclesMap (cochainsComplexι A) p x) =
      cochainOf A (cocycleι A p x) :=
  ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i (cochainsComplexι A) p) x

end Comparison

section Levels

variable (U : OpenNormalSubgroup G) {p q n : ℕ}

theorem inflation_π (A : Rep.{u} k G) [IsDiscreteRep A]
    (z : groupCohomology.cocycles (A.quotientToInvariants (U : Subgroup G)) p) :
    inflation A U p (groupCohomology.π _ p z) =
      cohomologyπ A p (HomologicalComplex.cyclesMap (inflationCochains A U) p z) :=
  ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality (inflationCochains A U) p) z

theorem cochainOf_cocycleι_cyclesMap_inflationCochains (A : Rep.{u} k G) [IsDiscreteRep A]
    (z : groupCohomology.cocycles (A.quotientToInvariants (U : Subgroup G)) p) :
    cochainOf A (cocycleι A p (HomologicalComplex.cyclesMap (inflationCochains A U) p z)) =
      fun g => (groupCohomology.iCocycles (A.quotientToInvariants (U : Subgroup G)) p z
        (fun i => (g i : G ⧸ (U : Subgroup G))) : A) :=
  congrArg (fun ψ => cochainOf A (ψ.hom z))
    (HomologicalComplex.cyclesMap_i (inflationCochains A U) p)

theorem inflationCochains_comp_cochainsMap {A A' : Rep.{u} k G} [IsDiscreteRep A]
    [IsDiscreteRep A'] (f : A ⟶ A') :
    inflationCochains A U ≫ cochainsMap f =
      groupCohomology.cochainsMap (MonoidHom.id _)
        ((Rep.quotientToInvariantsFunctor k (U : Subgroup G)).map f) ≫ inflationCochains A' U := by
  ext n x : 3
  rfl

theorem inflation_comp_cohomologyMap {A A' : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep A']
    (f : A ⟶ A') (n : ℕ) :
    inflation A U n ≫ cohomologyMap f n =
      groupCohomology.map (MonoidHom.id _)
        ((Rep.quotientToInvariantsFunctor k (U : Subgroup G)).map f) n ≫ inflation A' U n := by
  have h := congrArg (fun φ => HomologicalComplex.homologyMap φ n)
    (inflationCochains_comp_cochainsMap U f)
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact h

theorem cohomologyMap_inflation {A A' : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep A']
    (f : A ⟶ A') (x : groupCohomology (A.quotientToInvariants (U : Subgroup G)) n) :
    cohomologyMap f n (inflation A U n x) =
      inflation A' U n (groupCohomology.map (MonoidHom.id _)
        ((Rep.quotientToInvariantsFunctor k (U : Subgroup G)).map f) n x) :=
  ConcreteCategory.congr_hom (inflation_comp_cohomologyMap U f n) x

variable (A B : Rep.{u} k G) [IsDiscreteRep A] [IsDiscreteRep B]

theorem cup_inflation (h : p + q = n)
    (x : groupCohomology (A.quotientToInvariants (U : Subgroup G)) p)
    (y : groupCohomology (B.quotientToInvariants (U : Subgroup G)) q) :
    cup h (inflation A U p x) (inflation B U q y) =
      inflation (A ⊗ B) U n (groupCohomology.map (MonoidHom.id _)
        (invariantsTensorHom A B (U : Subgroup G)) n (GroundTheory.GroupCoh.cupH h x y)) := by
  refine groupCohomology_induction_on x fun x => ?_
  refine groupCohomology_induction_on y fun y => ?_
  rw [inflation_π, inflation_π, cup_cohomologyπ, GroundTheory.GroupCoh.cupH_π,
    GroundTheory.GroupCoh.map_π_apply, inflation_π]
  congr 1
  apply cocycles_ext
  rw [cocycleι_cupCocycles, cochainOf_cupLocallyConstant,
    cochainOf_cocycleι_cyclesMap_inflationCochains, cochainOf_cocycleι_cyclesMap_inflationCochains,
    cochainOf_cocycleι_cyclesMap_inflationCochains, GroundTheory.GroupCoh.iCocycles_cocyclesMap,
    GroundTheory.GroupCoh.iCocycles_cupCocycles]
  funext g
  simp only [GroundTheory.GroupCoh.cupCochain_apply]
  have hP : Fin.partialProd (fun i => (g i : G ⧸ (U : Subgroup G))) ⟨p, by omega⟩ =
      ((Fin.partialProd g ⟨p, by omega⟩ : G) : G ⧸ (U : Subgroup G)) :=
    partialProd_comp_monoidHom (QuotientGroup.mk' (U : Subgroup G)) g _
  rw [hP]
  rfl

end Levels

end GroundTheory.ProfCoh
