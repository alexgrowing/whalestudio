import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_localPeriodRingsData : ∀ (l : ℕ) [Fact l.Prime], Nonempty (Core l) := by
  first | exact @GlobalTheory.MemLoc.nonempty_core | exact GlobalTheory.MemLoc.nonempty_core | (intros; apply GlobalTheory.MemLoc.nonempty_core <;> assumption)
