import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.LocalHerbrand
import GroundTheory.ProfiniteCohomology.LocalClassFormation.Unramified
import GroundTheory.ProfiniteCohomology.ContinuousCochains.Functoriality
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits IsDedekindDomain NumberField GroundTheory.Global

open scoped Pointwise

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

include v in
open AdicLiesOver in

theorem isZero_groupCohomology_decomposition_integerUnits
    (he : w.asIdeal.ramificationIdx (𝓞 K) = 1) {n : ℕ} (hn : 1 ≤ n) :
    IsZero (groupCohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal)
      (w.adicCompletionIntegers L)ˣ) n) := by
  have := isUnramified_adicCompletion v w he
  have : FiniteDimensional (v.adicCompletion K) (w.adicCompletion L) := finite_adicCompletion v w
  refine (isZero_groupCohomology_integerUnits (v.adicCompletion K) (w.adicCompletion L) hn).of_iso
    (groupCohomology.mapIso (decompositionMulEquiv v w) (integerUnitsAddEquiv w).toIntLinearEquiv
      (fun σ => LinearMap.ext fun x => integerUnitsAddEquiv_decomposition v w σ x) n)

include v in

theorem isZero_cohomology_decomposition_integerUnits
    (he : w.asIdeal.ramificationIdx (𝓞 K) = 1) {n : ℕ} (hn : 1 ≤ n) :
    IsZero (cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal)
      (w.adicCompletionIntegers L)ˣ) n) :=
  (isZero_groupCohomology_decomposition_integerUnits v w he hn).of_iso
    (cohomologyIsoGroupCohomology _ n)

end GroundTheory.ProfCoh
