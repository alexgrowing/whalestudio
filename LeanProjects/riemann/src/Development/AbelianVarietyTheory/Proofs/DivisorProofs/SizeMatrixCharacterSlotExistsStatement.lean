import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeMatrixCharacterLeviBlockExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFunctorOfCharCentral
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.LeviBlockExponentLocal GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_size_matrix_character : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N i : ℕ) (b : Fin 2 → ℕ) (χ : Fin 2 → kˣ →* ℂˣ), (∀ j y, ‖((χ j y : ℂˣ) : ℂ)‖ = 1) → ∀ (ϖ : kˣ)
    (bm : SizeMatrix (fun j : Fin 2 => Fin (b j)) (fun j : Fin (i + 2) => Fin (blockSizes₂ N i j)))
    (f : ∀ r, (Σ j, Fin (bm.1 r j)) ≃ Fin (b r)) (g : ∀ j, (Σ r, Fin (bm.1 r j)) ≃ Fin (blockSizes₂ N i j)),
    ∃ (r : Fin 2) (l : ℕ), l ≤ i ∧
      ‖((cellScalar f g (pairChar k b χ) ⟨blockScalar₂ k N i ϖ, blockScalar_mem_relParab N i ϖ g⟩ : ℂˣ) : ℂ)‖ =
        nabs k ϖ ^ ((1 - (b r : ℝ)) / 2 + l) := by
  first | exact @GlobalTheory.LeviBlockExponentLocal.norm_cellScalar_positionElt | exact GlobalTheory.LeviBlockExponentLocal.norm_cellScalar_positionElt | (intros; apply GlobalTheory.LeviBlockExponentLocal.norm_cellScalar_positionElt <;> assumption)
