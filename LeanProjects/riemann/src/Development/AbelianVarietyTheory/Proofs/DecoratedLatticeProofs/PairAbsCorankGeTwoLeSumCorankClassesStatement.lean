import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairAbsCorankGeTwoLeSumCorankClasses
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopEvaluationThresholdZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairAbs_corank_ge_two_le_sum_corankClasses : ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (k : ℕ) (B : ℕ → ℝ), X.AbsConv → (∀ p ∈ X.big X.nzSet, X.s0 p.1 p.2 ≤ k) → (∀ s, 2 ≤ s → s ≤ k → Formalism.L2.SG.LoopsCut.ClassLe X (Formalism.L2.SG.LoopsCut.bigS X s) (B s)) → X.pairAbs (X.big X.nzSet) ≤ ∑ s ∈ Finset.Icc 2 k, B s := by
  first | exact @GlobalTheory.Core.Deg.pairAbs_big_le_sum_classes | exact GlobalTheory.Core.Deg.pairAbs_big_le_sum_classes | (intros; apply GlobalTheory.Core.Deg.pairAbs_big_le_sum_classes <;> assumption)
