import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialInfinitePlaceOfUnramified
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nontrivial_infinite_place_of_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → Nontrivial (InfinitePlace E) := by
  first | exact @GlobalTheory.CompanionTheory.UnrCM.nontrivial_infinitePlace | exact GlobalTheory.CompanionTheory.UnrCM.nontrivial_infinitePlace | (intros; apply GlobalTheory.CompanionTheory.UnrCM.nontrivial_infinitePlace <;> assumption)
