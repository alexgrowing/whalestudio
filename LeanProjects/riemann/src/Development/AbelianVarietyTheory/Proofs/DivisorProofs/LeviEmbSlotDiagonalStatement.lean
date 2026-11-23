import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbBlockDiagonal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviEmb_position_diagonal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n i : ℕ) (hi : i + 1 ≤ n) (ϖ : kˣ),
    ((GlobalTheory.SmGL.leviEmb k (blockIndex hi) (blockScalar₂ k n i ϖ)) : Matrix (Fin n) (Fin n) k) =
      Matrix.diagonal (Function.update 1 (⟨i, by omega⟩ : Fin n) (ϖ : k)) := by
  first | exact @GlobalTheory.LeviBlockExponent.leviEmb_positionElt_eq_diagonal | exact GlobalTheory.LeviBlockExponent.leviEmb_positionElt_eq_diagonal | (intros; apply GlobalTheory.LeviBlockExponent.leviEmb_positionElt_eq_diagonal <;> assumption)
