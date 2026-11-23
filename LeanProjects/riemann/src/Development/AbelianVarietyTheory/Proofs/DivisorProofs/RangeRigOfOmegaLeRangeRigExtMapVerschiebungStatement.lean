import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeRigOfOmegaLeRangeRigExtMapVerschiebung
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.range_rigOfOmega_le_range_rigExtMap_verschiebung' : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), LinearMap.range (frobTwist h G).rigOfOmega ≤ LinearMap.range (rigExtMap (verschiebung h G)) := by
  first | exact @GlobalTheory.PDivGroup.range_rigOfOmega_le_range_rigExtMap_verschiebung | exact GlobalTheory.PDivGroup.range_rigOfOmega_le_range_rigExtMap_verschiebung | (intros; apply GlobalTheory.PDivGroup.range_rigOfOmega_le_range_rigExtMap_verschiebung <;> assumption)
