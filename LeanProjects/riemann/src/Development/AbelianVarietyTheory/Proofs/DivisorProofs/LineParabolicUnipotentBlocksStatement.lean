import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineParabolicUnipotentBlocks
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocIdeleEqIdl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.CuspBlock GlobalTheory.JacLineSplit
open GlobalTheory.LineFrame

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_parabolic_unipotent_blocks : ∀ (k : Type) [Field k] (N m : ℕ) (hr : N = m + 2) (h2 : 2 ≤ N) (n : GL (Fin N) k),
    n ∈ unipRad k (linePlace h2) →
      ∃ (X : Matrix (Fin 1) (Fin m ⊕ Fin 1) k) (Y : Matrix (Fin m) (Fin 1) k),
        (n : Matrix (Fin N) (Fin N) k).submatrix (GlobalTheory.LineFrame.frameEquiv hr) (GlobalTheory.LineFrame.frameEquiv hr) =
          Matrix.fromBlocks 1 X 0 (Matrix.fromBlocks 1 Y 0 1) := by
  first | exact @GlobalTheory.LineFrame.unipRad_frame_blocks | exact GlobalTheory.LineFrame.unipRad_frame_blocks | (intros; apply GlobalTheory.LineFrame.unipRad_frame_blocks <;> assumption)
