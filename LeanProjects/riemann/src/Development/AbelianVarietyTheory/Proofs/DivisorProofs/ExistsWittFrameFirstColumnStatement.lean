import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWittFrameFirstColumn
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_witt_frame_first_column : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n n₁ : ℕ) (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (V₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n₁)
    (r s i₀ i₁ : ℕ) (H : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane E n n₁), B.IsGood σ → V.IsHerm σ B r s → H.IsAdapted σ B V V₁ i₀ i₁ →
    ∃ (m : ℕ) (X Y : Matrix (Fin n) (Fin (m + 1)) E), IsWittFrame σ V.Jᵀ X Y ∧
      col0 X = Matrix.of (fun i (_ : Fin 1) => H.x i) := by
  first | exact @GlobalTheory.PlaneWitt.exists_isWittFrame_col0 | exact GlobalTheory.PlaneWitt.exists_isWittFrame_col0 | (intros; apply GlobalTheory.PlaneWitt.exists_isWittFrame_col0 <;> assumption)
