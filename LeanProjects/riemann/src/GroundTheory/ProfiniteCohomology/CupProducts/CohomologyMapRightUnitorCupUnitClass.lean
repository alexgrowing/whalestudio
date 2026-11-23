import Mathlib
import GroundTheory.ProfiniteCohomology.CupProducts
import GroundTheory.ProfiniteCohomology.CupProducts.Cocycles
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory groupCohomology GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Associativity

variable {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]

end Associativity

section Unit

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem d_oneCochain :
    (inhomogeneousCochains.d (𝟙_ (Rep.{u} k G)) 0).hom (oneCochain (k := k) (G := G)) = 0 := by
  funext g
  simp [inhomogeneousCochains.d_hom_apply, oneCochain]
  rfl

def unitCocycle : cocycles (𝟙_ (Rep.{u} k G)) 0 :=
  (cochainsComplex (𝟙_ (Rep.{u} k G))).cyclesMk
    (mkCochain (𝟙_ (Rep.{u} k G)) oneCochain (IsLocallyConstant.const _)) 1 (by simp) (by
      apply cochainOf_injective (A := 𝟙_ (Rep.{u} k G))
      exact (cochainOf_d (A := 𝟙_ (Rep.{u} k G)) _).trans d_oneCochain)

@[simp]
theorem cochainOf_cocycleι_unitCocycle :
    cochainOf _ (cocycleι _ 0 (unitCocycle (k := k) (G := G))) = oneCochain :=
  congrArg (cochainOf _) ((cochainsComplex (𝟙_ (Rep.{u} k G))).i_cyclesMk _ _ _ _)

def unitClass : cohomology (𝟙_ (Rep.{u} k G)) 0 :=
  cohomologyπ _ 0 unitCocycle

variable {A : Rep.{u} k G} [IsDiscreteRep A]

theorem cohomologyMap_leftUnitor_unitClass_cup {q : ℕ} (x : cohomology A q) :
    cohomologyMap (λ_ A).hom q (cup (zero_add q) unitClass x) = x := by
  refine cohomology_induction_on x fun x => ?_
  rw [unitClass, cup_cohomologyπ, cohomologyMap_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cyclesMap]
  simp only [cocycleι_cupCocycles, cochainOf_cupLocallyConstant, cochainOf_cocycleι_unitCocycle]
  funext g
  exact leftUnitor_oneCochain_cupCochain _ g

theorem cohomologyMap_rightUnitor_cup_unitClass {p : ℕ} (x : cohomology A p) :
    cohomologyMap (ρ_ A).hom p (cup (add_zero p) x unitClass) = x := by
  refine cohomology_induction_on x fun x => ?_
  rw [unitClass, cup_cohomologyπ, cohomologyMap_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cyclesMap]
  simp only [cocycleι_cupCocycles, cochainOf_cupLocallyConstant, cochainOf_cocycleι_unitCocycle]
  funext g
  exact rightUnitor_cupCochain_oneCochain _ g

end Unit

end GroundTheory.ProfCoh
