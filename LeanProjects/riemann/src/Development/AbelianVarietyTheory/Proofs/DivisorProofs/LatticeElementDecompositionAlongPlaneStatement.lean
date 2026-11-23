import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeElementDecompositionAlongPlane
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_element_decomposition_along_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ),
    H.IsAdapted σ B X X₁ j₀ j₁ → ∀ (v : Pl F), ∀ γ ∈ latAtV X W v,
      ∃ (a b : Fin d → AE F E) (z : Matrix (Fin n₁) (Fin d) (AE F E)), z ∈ latAtV X₁ W v ∧
        Matrix.vecMulVec (incV F H.x) a ∈ latAtV X W v ∧ Matrix.vecMulVec (incV F H.y) b ∈ latAtV X W v ∧
        γ = Matrix.vecMulVec (incV F H.x) a + incM F H.ι * z + Matrix.vecMulVec (incV F H.y) b := by
  first | exact @GlobalTheory.LatPlaneSplit.latAtV_split | exact GlobalTheory.LatPlaneSplit.latAtV_split | (intros; apply GlobalTheory.LatPlaneSplit.latAtV_split <;> assumption)
