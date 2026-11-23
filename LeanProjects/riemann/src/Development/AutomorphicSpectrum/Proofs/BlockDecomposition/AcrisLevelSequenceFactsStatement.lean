import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisLevelSequenceFacts
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_level_sequence_facts : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.RAcrSeq l := by
  first | exact @GlobalTheory.CompanionTheory.LSeq.racrSeq | exact GlobalTheory.CompanionTheory.LSeq.racrSeq | (intros; apply GlobalTheory.CompanionTheory.LSeq.racrSeq <;> assumption)
