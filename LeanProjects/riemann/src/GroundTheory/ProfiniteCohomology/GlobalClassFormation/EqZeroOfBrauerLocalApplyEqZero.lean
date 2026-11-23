import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ClassLevels
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalInvariants
import GroundTheory.ProfiniteCohomology.ContinuousCochains.LongExactSequence
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField GroundTheory.Global FiniteSubfield

open scoped DirectSum

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable (K : FiniteSubfield)

instance isDiscreteRep_idelesShortComplexRes_X₁ : IsDiscreteRep (idelesShortComplexRes K).X₁ :=
  inferInstanceAs (IsDiscreteRep (unitsLimitRep K))

instance isDiscreteRep_idelesShortComplexRes_X₂ : IsDiscreteRep (idelesShortComplexRes K).X₂ :=
  inferInstanceAs (IsDiscreteRep (limitRep K))

instance isDiscreteRep_idelesShortComplexRes_X₃ : IsDiscreteRep (idelesShortComplexRes K).X₃ :=
  inferInstanceAs (IsDiscreteRep (classLimitRep K))

abbrev unitsToIdeles (n : ℕ) : cohomology (unitsLimitRep K) n ⟶ cohomology (limitRep K) n :=
  cohomologyMap (idelesShortComplexRes K).f n

abbrev idelesToClasses (n : ℕ) : cohomology (limitRep K) n ⟶ cohomology (classLimitRep K) n :=
  cohomologyMap (idelesShortComplexRes K).g n

abbrev classesToUnits (n : ℕ) : cohomology (classLimitRep K) n ⟶ cohomology (unitsLimitRep K) (n + 1) :=
  δ (idelesShortComplexRes_shortExact K) n (n + 1) rfl

theorem exists_unitsToIdeles_eq (n : ℕ) (y : cohomology (limitRep K) n)
    (hy : (idelesToClasses K n).hom y = 0) : ∃ x, (unitsToIdeles K n).hom x = y :=
  ((ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
    (cohomology_exact₂ (idelesShortComplexRes_shortExact K) n)) hy

theorem exists_idelesToClasses_eq (n : ℕ) (c : cohomology (classLimitRep K) n)
    (hc : (classesToUnits K n).hom c = 0) : ∃ y, (idelesToClasses K n).hom y = c :=
  ((ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
    (cohomology_exact₃ (idelesShortComplexRes_shortExact K) n (n + 1) rfl)) hc

theorem exists_classesToUnits_eq (n : ℕ) (x : cohomology (unitsLimitRep K) (n + 1))
    (hx : (unitsToIdeles K (n + 1)).hom x = 0) : ∃ c, (classesToUnits K n).hom c = x :=
  ((ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
    (cohomology_exact₁ (idelesShortComplexRes_shortExact K) n (n + 1) rfl)) hx

theorem injective_cohomologyMap_units_ideles : Function.Injective (unitsToIdeles K 2).hom := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨c, rfl⟩ := exists_classesToUnits_eq K 1 x hx
  have h0 := isZero_cohomology_one_classLimitRep K
  rw [ModuleCat.isZero_iff_subsingleton] at h0
  rw [Subsingleton.elim c 0, map_zero]

variable {K}

def brauerLocal (ι : LocalEmbeddings K) :
    cohomology (unitsLimitRep K) 2 →+ ⨁ v : Place K.1, localGaloisCohomology K 2 v :=
  (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).toAddMonoidHom.comp
    (unitsToIdeles K 2).hom.toAddMonoidHom

theorem brauerLocal_apply (ι : LocalEmbeddings K) (x : cohomology (unitsLimitRep K) 2) :
    brauerLocal ι x = idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2) ((unitsToIdeles K 2).hom x) :=
  rfl

theorem brauerLocal_injective (ι : LocalEmbeddings K) : Function.Injective (brauerLocal ι) :=
  (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).injective.comp
    (injective_cohomologyMap_units_ideles K)

theorem eq_zero_of_brauerLocal_apply_eq_zero (ι : LocalEmbeddings K) (x : cohomology (unitsLimitRep K) 2)
    (hx : ∀ v, brauerLocal ι x v = 0) : x = 0 :=
  brauerLocal_injective ι ((DFinsupp.ext hx).trans (map_zero _).symm)

def brauerSumInv (ι : LocalEmbeddings K) : cohomology (unitsLimitRep K) 2 →+ QZ :=
  (sumPlaceInv K).comp (brauerLocal ι)

end

end GroundTheory.ProfCoh
