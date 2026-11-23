import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesCoeffNormLeOneRootCoprimePadic
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeriesCoeffNormLeOne_root_coprime_padic : ∀ (p : ℕ) [Fact p.Prime] (N : ℕ), 0 < N → Nat.Coprime N p →
    ∀ s : PowerSeries ℂ_[p], PowerSeries.constantCoeff s = 1 →
      GlobalTheory.EvenTheta.IntSer (s ^ N) → GlobalTheory.EvenTheta.IntSer s := by
  first | exact @GlobalTheory.RootInt.intSer_root | exact GlobalTheory.RootInt.intSer_root | (intros; apply GlobalTheory.RootInt.intSer_root <;> assumption)
