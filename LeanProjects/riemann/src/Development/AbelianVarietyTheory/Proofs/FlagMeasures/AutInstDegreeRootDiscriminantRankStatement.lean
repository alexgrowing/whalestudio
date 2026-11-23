import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutInstDegreeRootDiscriminantRank
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.autInst_degree_rootDiscriminant_rank : ∀ I : AutInst, Formalism.HermitianLatticesTheory.fDeg I.E = I.f ∧ 2 * Formalism.HermitianLatticesTheory.vInv I.E = I.rd ∧ 1 ≤ I.rd ∧ 1 ≤ I.f ∧ Fintype.card (InfinitePlace I.F) = I.f ∧ ∀ p q, HasSig I p q → p + q = I.n := by
  first | exact @GlobalTheory.FlagMeas.instance_numbers | exact GlobalTheory.FlagMeas.instance_numbers | (intros; apply GlobalTheory.FlagMeas.instance_numbers <;> assumption)
