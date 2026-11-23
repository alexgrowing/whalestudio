import Mathlib
import GroundTheory.PAdicHodge.ConvergesAtOfNormLeSeq
import GroundTheory.PAdicHodge.BoundOfEventuallyAntitone
import GroundTheory.PAdicHodge.ExtRobba
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
  [IsAlgClosed L] [CompleteSpace L]

theorem rootExists : T.RootExists := fun _ _ hx _ hr0 hrρ hm => T.exists_point_dvd hx hr0 hrρ hm

theorem isBezout_robbaTilde : IsBezout T.RobbaTilde := T.isBezout_of_rootExists T.rootExists

end TeichLift

namespace ExtRobba

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (normInteger K)] [CharZero K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP (IsLocalRing.ResidueField (normInteger K)) p]
  [PerfectRing (IsLocalRing.ResidueField (normInteger K)) p]
variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [CharP L p] [PerfectRing L p] [IsAlgClosed L]
variable (ι : IsLocalRing.ResidueField (normInteger K) →+* L) {ϖ : normInteger K}
  (hϖ : Irreducible ϖ) (hι : ∀ a, ‖ι a‖ ≤ 1)

end ExtRobba

end GroundTheory.PAdicHodge
