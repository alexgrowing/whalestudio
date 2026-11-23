import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TsumLeOfLatticeCoordsQuadraticDecay
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerAlong
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_le_of_lattice_coords_quadraticDecay : ∀ {Y : Type} (n N : ℕ), 0 < N → ∀ (a : Y → ENNReal) (T : Fin n → Y → ℝ), (∀ y y', a y ≠ 0 → a y' ≠ 0 → (∀ j, T j y = T j y') → y = y') → (∀ y, a y ≠ 0 → ∀ j, ∃ c : ℤ, (N : ℝ) * T j y = c) → ∀ S : ENNReal, (∀ y, a y * ∏ j, ENNReal.ofReal (1 + T j y ^ 2) ≤ S) → ∑' y, a y ≤ S * ENNReal.ofReal ((5 * (N : ℝ) ^ 2) ^ n) := by
  first | exact @GlobalTheory.TwBoundFour.tsum_le | exact GlobalTheory.TwBoundFour.tsum_le | (intros; apply GlobalTheory.TwBoundFour.tsum_le <;> assumption)
