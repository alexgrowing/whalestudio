import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaLift
import GroundTheory.PAdicHodge.ExtRobbaUnits
import GroundTheory.PAdicHodge.ExtRobbaNewton
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace ExtRobba

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (normInteger K)] [CharZero K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP (IsLocalRing.ResidueField (normInteger K)) p]
  [PerfectRing (IsLocalRing.ResidueField (normInteger K)) p]
variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [CharP L p] [PerfectRing L p]
variable (ι : IsLocalRing.ResidueField (normInteger K) →+* L) {ϖ : normInteger K}
  (hϖ : Irreducible ϖ) (hι : ∀ a, ‖ι a‖ ≤ 1)

abbrev EDagger : Subring (gammaTeichLift p ι hϖ hι).B := (gammaTeichLift p ι hϖ hι).Edag

abbrev RobbaR (ρ0 : Set.Ioo (0 : ℝ) 1) := (gammaTeichLift p ι hϖ hι).RobbaExt ρ0

abbrev RobbaTildeL := (gammaTeichLift p ι hϖ hι).RobbaTilde

example : IsDomain (RobbaTildeL p ι hϖ hι) := inferInstance

example (ρ0 : Set.Ioo (0 : ℝ) 1) : IsDomain (RobbaR p ι hϖ hι ρ0) := inferInstance

def frobenius (σ : K →+* K) (hσn : ∀ x, ‖σ x‖ = ‖x‖) (a : ℕ)
    (hσr : ∀ x : K, ‖x‖ ≤ 1 → ‖σ x - x ^ p ^ a‖ < 1) :
    RobbaTildeL p ι hϖ hι ≃+* RobbaTildeL p ι hϖ hι :=
  (gammaTeichFrob p σ hσn a hσr hϖ ι hι).tildeEquiv

end ExtRobba

end GroundTheory.PAdicHodge
