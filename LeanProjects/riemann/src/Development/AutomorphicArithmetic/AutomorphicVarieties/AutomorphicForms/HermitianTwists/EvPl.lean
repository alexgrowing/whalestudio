import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.RepNewformOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CharEq

open private normV_inj normV_surj from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CharEq

open Formalism.ConjugateSelfDual UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd UpperTheory.V.Br.CharacterEquality in
theorem UpperTheory.V.Af.Rn.evPl :
    UpperTheory.V.Af.Rn.EvPl := by
  refine ⟨fun P => ⟨fun h => ?_, fun h => ?_⟩, fun M hM => ?_⟩
  · refine Filter.eventually_cofinite.2
      (((Filter.eventually_cofinite.1 h).image fun w => normV w).subset fun p hp => ?_)
    obtain ⟨hp, hne⟩ := Classical.not_imp.1 hp
    obtain ⟨w, rfl⟩ := normV_surj hp
    exact ⟨w, hne, rfl⟩
  · filter_upwards [normV_inj.tendsto_cofinite.eventually h] with w hw
    exact hw (places w).1
  · filter_upwards [normV_inj.tendsto_cofinite.eventually (Set.finite_le_nat M).eventually_cofinite_notMem] with w hw
    exact fun h => hw (Nat.le_of_dvd hM h)
