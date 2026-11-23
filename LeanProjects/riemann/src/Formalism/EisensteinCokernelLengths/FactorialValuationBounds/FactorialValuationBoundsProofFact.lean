import Mathlib
import Formalism.FrobeniusContraction.HighestWeightResidueAvoids
import Formalism.WindowSums.PowerSeriesRelationList
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.ContractBij
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.FiniteCocyclesLeCocycles
import Formalism.FrobeniusContraction.EulerC
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.LemmaS

namespace Formalism.ZetaNonvanishing.ARCV

open Polynomial

theorem range_sdiff_range (H : ℕ) : Finset.range (2 * H) \ Finset.range H = Finset.Ico H (2 * H) := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ico]
  omega

end Formalism.ZetaNonvanishing.ARCV
