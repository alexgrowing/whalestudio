import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedMatrixDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtVecMulVecRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianSetAdditiveSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviMapPreservesRationalPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianDeterminantNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrAEMixedNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTraceOrth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumThreeComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensEqTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensVmvLeft
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch GlobalTheory.ArchSchB

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_adapted_matrix_decomposition : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E)
    {n d n₁ : ℕ} (X : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ),
    X.IsHerm σ B r s → H.IsAdapted σ B X X₁ i₀ i₁ → ∀ w : Matrix (Fin n) (Fin d) (AE F E), At (evI F) w →
    ∃ (α β : Fin d → AE F E) (C : Matrix (Fin n₁) (Fin d) (AE F E)), At (evI F) α ∧ At (evI F) β ∧ At (evI F) C ∧
      w = Matrix.vecMulVec (incV F H.x) α + incM F H.ι * C + Matrix.vecMulVec (incV F H.y) β := by
  first | exact @GlobalTheory.ThK.DecX.decompose | exact GlobalTheory.ThK.DecX.decompose | (intros; apply GlobalTheory.ThK.DecX.decompose <;> assumption)
