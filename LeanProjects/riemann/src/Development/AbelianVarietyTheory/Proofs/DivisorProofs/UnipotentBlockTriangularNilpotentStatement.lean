import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentBlockTriangularNilpotent
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_block_triangular_nilpotent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n n₁ : ℕ) (Y : Spc F E n) (H : Plane E n n₁) (R : Matrix (Fin (1 + n₁ + 1)) (Fin n) E), frame H * R = 1 → R * frame H = 1 →
    ∀ u : UA σ Y.J, (∀ i j, blk n₁ j < blk n₁ i + 1 → (incM F R * (mat u - 1 : Matrix (Fin n) (Fin n) (AE F E)) * incM F (frame H) :
        Matrix (Fin (1 + n₁ + 1)) (Fin (1 + n₁ + 1)) (AE F E)) i j = 0) →
      u ∈ unip σ Y H := by
  first | exact @GlobalTheory.LeviHC.UnipFrame.mem_unip_of_strictBlockTri | exact GlobalTheory.LeviHC.UnipFrame.mem_unip_of_strictBlockTri | (intros; apply GlobalTheory.LeviHC.UnipFrame.mem_unip_of_strictBlockTri <;> assumption)
