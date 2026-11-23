import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootDiscrGeThreeHalvesOfIsTotallyComplex
import Formalism.HermitianLattices.StatementMass
open MeasureTheory NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootDiscr_ge_three_halves_of_isTotallyComplex : ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → Module.finrank ℚ K = 2 * Formalism.HermitianLatticesTheory.fDeg K ∧ 1 ≤ Formalism.HermitianLatticesTheory.fDeg K ∧ (3 / 2 : ℝ) ≤ 2 * Formalism.HermitianLatticesTheory.vInv K ∧ Real.sqrt |(discr K : ℝ)| = (2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K := by
  first | exact @GlobalTheory.rootDiscr_ge_three_halves_of_totallyComplex | exact GlobalTheory.rootDiscr_ge_three_halves_of_totallyComplex | (intros; apply GlobalTheory.rootDiscr_ge_three_halves_of_totallyComplex <;> assumption)
