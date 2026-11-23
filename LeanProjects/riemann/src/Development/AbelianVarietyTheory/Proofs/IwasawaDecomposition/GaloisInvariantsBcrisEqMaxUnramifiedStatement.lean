import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisInvariantsBcrisEqMaxUnramified
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisInvariants_Bcris_eq_maxUnramified : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (K : FinExt l) (b : Per.Bcris l), (∀ g ∈ GK K, Per.σB g b = b) → ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 ∧ C.u c = b := by
  first | exact @GlobalTheory.MemLoc.InvCris.invariants_Bcris | exact GlobalTheory.MemLoc.InvCris.invariants_Bcris | (intros; apply GlobalTheory.MemLoc.InvCris.invariants_Bcris <;> assumption)
