import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeJacquetRepEquivRow
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothColRep
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SmGL.RowOneCell Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relative_jacquet_rep_equiv_row : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ), Nonempty (Representation.Equiv ((relJac (rowPart u v) ((extTensor (detRep (Fin u) χ₁)
      (detRep (Fin (v + 1)) χ₂)).comp (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom)).comp
        (swapBlocks k fun i j => Fin (sz u v i j))) (piTensor (colRep χ₁ χ₂ u v))) := by
  first | exact @GlobalTheory.SmGL.RowOneCell.rowJac_swap_equiv | exact GlobalTheory.SmGL.RowOneCell.rowJac_swap_equiv | (intros; apply GlobalTheory.SmGL.RowOneCell.rowJac_swap_equiv <;> assumption)
