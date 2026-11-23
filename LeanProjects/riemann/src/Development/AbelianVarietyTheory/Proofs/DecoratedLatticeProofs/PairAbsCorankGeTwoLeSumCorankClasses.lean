import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopEvaluationThresholdZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem pairAbs_big_le_sum_classes : ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (k : ℕ) (B : ℕ → ℝ), X.AbsConv → (∀ p ∈ X.big X.nzSet, X.s0 p.1 p.2 ≤ k) → (∀ s, 2 ≤ s → s ≤ k → Formalism.L2.SG.LoopsCut.ClassLe X (Formalism.L2.SG.LoopsCut.bigS X s) (B s)) → X.pairAbs (X.big X.nzSet) ≤ ∑ s ∈ Finset.Icc 2 k, B s := by
  intro τ Rw I H H₁ _ _ _ _ _ X k B hA hk hS
  have hG : 0 ≤ X.Gam1 := hA.2.2.le
  have hv : Summable (fun t => ‖X.vec t‖) := hA.2.1
  have hcov : X.big X.nzSet ⊆
      (⋃ s ∈ Finset.Icc 2 k, Formalism.L2.SG.LoopsCut.bigS X s) ∪ (∅ : Set (τ × τ)) := by
    intro p hp
    left
    exact Set.mem_iUnion₂.2 ⟨X.s0 p.1 p.2, Finset.mem_Icc.2 ⟨hp.2, hk p hp⟩, ⟨hp.1, rfl⟩⟩
  have hc := Formalism.L2.SG.LoopsCut.ampSum_cover X hv (Finset.Icc 2 k) (Formalism.L2.SG.LoopsCut.bigS X) ∅
    (X.big X.nzSet) hcov
  have h0 : Formalism.L2.SG.RowsOther.ampSum X (∅ : Set (τ × τ)) = 0 := by
    unfold Formalism.L2.SG.RowsOther.ampSum; simp
  rw [h0, add_zero] at hc
  calc X.pairAbs (X.big X.nzSet)
      ≤ X.Gam1 * Formalism.L2.SG.RowsOther.ampSum X (X.big X.nzSet) :=
        Formalism.L2.SG.RowsOther.pairAbs_le_ampSum X hG _ (Formalism.L2.SG.LoopsCut.amp_summable X hv _)
    _ ≤ X.Gam1 * ∑ s ∈ Finset.Icc 2 k, Formalism.L2.SG.RowsOther.ampSum X (Formalism.L2.SG.LoopsCut.bigS X s) :=
        mul_le_mul_of_nonneg_left hc hG
    _ = ∑ s ∈ Finset.Icc 2 k, X.Gam1 * Formalism.L2.SG.RowsOther.ampSum X (Formalism.L2.SG.LoopsCut.bigS X s) :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ s ∈ Finset.Icc 2 k, B s :=
        Finset.sum_le_sum fun s hs => hS s (Finset.mem_Icc.1 hs).1 (Finset.mem_Icc.1 hs).2

end GlobalTheory.Core.Deg
