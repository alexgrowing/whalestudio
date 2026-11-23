import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ClassFormationGlobal
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleInvariants
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.SubsingletonCohomologyThreeInfiniteDecomposition
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain

noncomputable section

theorem sumInvRestriction : SumInvRestriction :=
  fun _ _ _ ιK ιF y => idelesSumInv_idelesResField ιK ιF y

theorem idelesToClasses_surjective (K : FiniteSubfield) : Function.Surjective (idelesToClasses K 2).hom :=
  idelesToClasses_surjective_of sumInvRestriction K (Classical.choice (nonempty_localEmbeddings K))

def globalClassFormation (K : FiniteSubfield) : ClassFormation (classLimitRep K) :=
  globalClassFormationOf sumInvRestriction K

theorem subsingleton_cohomology_three_unitsLimitRep (K : FiniteSubfield) :
    Subsingleton (cohomology (unitsLimitRep K) 3) := by
  have h3 := subsingleton_cohomology_three_limitRep (K := K)
  refine ⟨fun x x' => ?_⟩
  have hz : ∀ x : cohomology (unitsLimitRep K) 3, x = 0 := by
    intro x
    obtain ⟨c, rfl⟩ := exists_classesToUnits_eq K 2 x (Subsingleton.elim _ _)
    obtain ⟨y, rfl⟩ := idelesToClasses_surjective K c
    exact congrArg (fun f => f.hom y) (comp_δ (idelesShortComplexRes_shortExact K) 2 3 rfl)
  rw [hz x, hz x']

end

end GroundTheory.ProfCoh
