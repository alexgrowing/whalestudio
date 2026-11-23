import Mathlib
import GroundTheory.ProfiniteCohomology.ClassFormations.SubsingletonCohomologyTopOfThreeLeInt
import GroundTheory.ProfiniteCohomology.LocalClassFormationAlt
import GroundTheory.ProfiniteCohomology.GlobalClassFormation
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

section Local

variable (K Ksep : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

theorem subsingleton_cohomology_galUnits_of_three_le {r : ℕ} (hr : 3 ≤ r) :
    Subsingleton (cohomology (galUnits.{0} K Ksep) r) :=
  (localClassFormationOfIsSepClosure K Ksep).subsingleton_cohomology_top_of_three_le hr

end Local

section Global

open GroundTheory.Global

theorem subsingleton_cohomology_classLimitRep_of_three_le (K : FiniteSubfield) {r : ℕ}
    (hr : 3 ≤ r) : Subsingleton (cohomology (classLimitRep K) r) :=
  (globalClassFormation K).subsingleton_cohomology_top_of_three_le_int hr

end Global

end GroundTheory.ProfCoh
