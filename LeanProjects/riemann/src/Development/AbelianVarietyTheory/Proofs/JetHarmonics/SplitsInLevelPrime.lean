import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HalfPrincipalAndSplit
open NumberField Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.PtTie

namespace GlobalTheory.LevelSplit

theorem splitsIn_level_prime : ∀ (D : D7) (i : Fin 2), SplitsIn D.host.E (D.host.g i) := fun D i =>
  GlobalTheory.HalfGen.factors_of_ncard_places D.host.E (D.host.g i) (D.host.g_prime i) (D.nd.g_split i)

end GlobalTheory.LevelSplit
