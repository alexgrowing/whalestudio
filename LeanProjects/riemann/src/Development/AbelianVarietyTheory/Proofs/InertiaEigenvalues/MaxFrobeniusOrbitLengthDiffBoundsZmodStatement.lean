import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxFrobeniusOrbitLengthDiffBoundsZmod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maxFrobeniusOrbitLengthDiff_bounds_zmod : ∀ (l e a : ℕ), l.Prime → 1 ≤ a → e + 1 = l ^ a → ∀ (Sig : Finset (ZMod e)) (N : ℕ), (∀ c ∈ Sig, (l : ZMod e) * c ∈ Sig) → (0 : ZMod e) ∈ Sig → Sig.card ≤ N → 2 ≤ N → 1 ≤ maxPeriod l Sig ∧ 4 * maxPeriod l Sig ≤ N ^ 2 ∧ ∀ c ∈ Sig, frobPeriod l c ≤ maxPeriod l Sig := by
  first | exact @GlobalTheory.BK.maxPeriod_bounds | exact GlobalTheory.BK.maxPeriod_bounds | (intros; apply GlobalTheory.BK.maxPeriod_bounds <;> assumption)
