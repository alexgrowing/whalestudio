import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeMatrixRelativeModulus
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.size_matrix_relative_modulus : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N l d : ℕ) (b : Fin 2 → ℕ) (χ : Fin 2 → kˣ →* ℂˣ)
    (M : GlobalTheory.SmGL.SizeMatrix (fun i : Fin 2 => Fin (b i)) (fun j : Fin 3 => Fin (GlobalTheory.CuspBlock.tripSizes l d N j)))
    (f : ∀ i, (Σ j, Fin (M.1 i j)) ≃ Fin (b i)) (z : GlobalTheory.SmGL.Levi k (fun i : Fin 2 => Fin (M.1 i 1))),
    (((GlobalTheory.SmGL.relDeltaHalf k (fun i j => Fin (M.1 i j)))⁻¹ * (GlobalTheory.LeviBlockExponent.pairChar k b χ).comp (GlobalTheory.SmGL.relEmb k f))
        (GlobalTheory.SmGL.swapBlocks k (fun i j => Fin (M.1 i j)) (Pi.mulSingle (1 : Fin 3) z)) : ℂˣ) =
      GlobalTheory.LeviBlockExponent.pairChar k (fun i => M.1 i 1)
        (fun i => χ i * GlobalTheory.SmGL.absPow k ((M.1 i 0 : ℂ) + ((M.1 i 1 : ℂ) - b i) / 2)) z := by
  first | exact @GlobalTheory.CellExp.jacquetChar_middleColumn | exact GlobalTheory.CellExp.jacquetChar_middleColumn | (intros; apply GlobalTheory.CellExp.jacquetChar_middleColumn <;> assumption)
