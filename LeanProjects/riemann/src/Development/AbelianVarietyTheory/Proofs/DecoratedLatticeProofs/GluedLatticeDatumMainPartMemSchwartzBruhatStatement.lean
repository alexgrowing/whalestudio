import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedLatticeDatumMainPartMemSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum)
open GlobalTheory.FinPl.Comm (fpair)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedLatticeDatum_mainPart_mem_schwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) (P : Pair k n') (Q : Pair k n), mainDatum q χ ε P Q ∈ SB (Matrix n n' k) := by
  first | exact @GlobalTheory.FinPl.Comm.mainDatum_mem_SB | exact GlobalTheory.FinPl.Comm.mainDatum_mem_SB | (intros; apply GlobalTheory.FinPl.Comm.mainDatum_mem_SB <;> assumption)
