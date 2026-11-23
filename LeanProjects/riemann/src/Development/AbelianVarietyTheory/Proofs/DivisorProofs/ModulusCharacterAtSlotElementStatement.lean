import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusCharacterAtBlockElement
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_character_at_position_element : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n i : ℕ), i + 1 ≤ n → ∀ (ϖ : kˣ),
      ((deltaHalf k (fun j : Fin (i + 2) => Fin (blockSizes₂ n i j)) (blockScalar₂ k n i ϖ) : ℂˣ) : ℂ) =
        ((nabs k ϖ ^ (((n : ℝ) - 1) / 2 - (i : ℝ)) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.LeviBlockExponent.deltaHalf_positionElt | exact GlobalTheory.LeviBlockExponent.deltaHalf_positionElt | (intros; apply GlobalTheory.LeviBlockExponent.deltaHalf_positionElt <;> assumption)
