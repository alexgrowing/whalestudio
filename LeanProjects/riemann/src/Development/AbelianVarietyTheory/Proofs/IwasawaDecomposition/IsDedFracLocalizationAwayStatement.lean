import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDedFracLocalizationAway
import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDedFrac_localization_away : ∀ (O F : Type) [CommRing O] [Field F] (β : O →+* F) (x : O), β x ≠ 0 → IsDedFrac β → ∀ (ω : Localization.Away x →+* F), ω.comp (algebraMap O (Localization.Away x)) = β → IsDedFrac ω := by
  first | exact @GlobalTheory.Member.isDedFrac_away | exact GlobalTheory.Member.isDedFrac_away | (intros; apply GlobalTheory.Member.isDedFrac_away <;> assumption)
