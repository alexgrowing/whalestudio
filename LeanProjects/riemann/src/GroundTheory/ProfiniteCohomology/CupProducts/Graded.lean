import Mathlib
import GroundTheory.ProfiniteCohomology.CupProducts.GroupCohomology
import GroundTheory.ProfiniteCohomology.Colimit
import GroundTheory.TateCohomology.CupGraded
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory TensorProduct

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Invariants

variable (N : Subgroup G) [N.Normal]

def invariantsMap {A A' : Rep.{u} k G} (f : A ⟶ A') :
    A.quotientToInvariants N ⟶ A'.quotientToInvariants N :=
  (Rep.quotientToInvariantsFunctor k N).map f

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem invariantsTensorHom_braiding (A B : Rep.{u} k G) :
    (β_ (A.quotientToInvariants N) (B.quotientToInvariants N)).hom ≫ invariantsTensorHom B A N =
      invariantsTensorHom A B N ≫ invariantsMap N (β_ A B).hom := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.toLinearMap_injective
  exact TensorProduct.ext' fun a b => rfl

theorem cohomologyMap_inflation' (U : OpenNormalSubgroup G) {A A' : Rep.{u} k G}
    [IsDiscreteRep A] [IsDiscreteRep A'] (f : A ⟶ A') {n : ℕ}
    (x : groupCohomology (A.quotientToInvariants (U : Subgroup G)) n) :
    cohomologyMap f n (inflation A U n x) =
      inflation A' U n (groupCohomology.map (MonoidHom.id _) (invariantsMap (U : Subgroup G) f) n x) :=
  cohomologyMap_inflation U f x

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem map_invariantsMap_braiding_map_invariantsTensorHom_cupH {A B : Rep.{u} k G} {p q n : ℕ}
    (h : p + q = n) (h' : q + p = n) (x : groupCohomology (A.quotientToInvariants N) p)
    (y : groupCohomology (B.quotientToInvariants N) q) :
    groupCohomology.map (MonoidHom.id _) (invariantsMap N (β_ A B).hom) n
        (groupCohomology.map (MonoidHom.id _) (invariantsTensorHom A B N) n
          (GroundTheory.GroupCoh.cupH h x y)) =
      (-1 : k) ^ (p * q) • groupCohomology.map (MonoidHom.id _) (invariantsTensorHom B A N) n
        (GroundTheory.GroupCoh.cupH h' y x) := by
  rw [← ConcreteCategory.comp_apply, ← groupCohomology.map_id_comp, ← invariantsTensorHom_braiding,
    groupCohomology.map_id_comp, ConcreteCategory.comp_apply, GroundTheory.GroupCoh.map_braiding_cupH h h',
    map_smul]

end Invariants

variable [CompactSpace G] [TotallyDisconnectedSpace G]
  {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] {p q n : ℕ}

theorem cohomologyMap_braiding_cup (h : p + q = n) (h' : q + p = n) (x : cohomology A p)
    (y : cohomology B q) :
    cohomologyMap (β_ A B).hom n (cup h x y) = (-1 : k) ^ (p * q) • cup h' y x := by
  obtain ⟨U, x₀, rfl⟩ := exists_inflation_eq A p x
  obtain ⟨V, y₀, rfl⟩ := exists_inflation_eq B q y
  have hx := ConcreteCategory.congr_hom (transition_comp_inflation A (inf_le_left : U ⊓ V ≤ U) p) x₀
  have hy := ConcreteCategory.congr_hom (transition_comp_inflation B (inf_le_right : U ⊓ V ≤ V) q) y₀
  rw [ConcreteCategory.comp_apply] at hx hy
  rw [← hx, ← hy]
  generalize (transition A (inf_le_left : U ⊓ V ≤ U) p) x₀ = x₁
  generalize (transition B (inf_le_right : U ⊓ V ≤ V) q) y₀ = y₁
  rw [cup_inflation (U ⊓ V) A B h, cup_inflation (U ⊓ V) B A h', cohomologyMap_inflation',
    map_invariantsMap_braiding_map_invariantsTensorHom_cupH _ h h', map_smul]

end GroundTheory.ProfCoh
