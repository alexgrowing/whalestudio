import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsBdRPlusSectionOfTheta
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isBdRPlusSectionOfTheta : ∀ (l : ℕ) [Fact l.Prime], ∃ o : Om l →+* Per.BdRp l, IsSec o := by
  first | exact @GlobalTheory.MemLoc.SecEx.exists_isSec | exact GlobalTheory.MemLoc.SecEx.exists_isSec | (intros; apply GlobalTheory.MemLoc.SecEx.exists_isSec <;> assumption)
