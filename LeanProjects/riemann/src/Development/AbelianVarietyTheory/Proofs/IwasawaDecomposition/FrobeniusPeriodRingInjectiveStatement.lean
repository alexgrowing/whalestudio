import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_period_ring_injective : ∀ (l : ℕ) [Fact l.Prime], Function.Injective (Per.φB l) := by
  first | exact @GlobalTheory.MemLoc.phiB_injective | exact GlobalTheory.MemLoc.phiB_injective | (intros; apply GlobalTheory.MemLoc.phiB_injective <;> assumption)
