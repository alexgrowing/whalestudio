import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSignatureDropsByPlane
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_signature_drops_by_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n n₁ : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ r s : ℕ),
    X.IsHerm σ B r s → H.IsAdapted σ B X X₁ j₀ j₁ → X₁.IsHerm σ B (r - 1) (s - 1) := by
  first | exact @GlobalTheory.isHerm_plane_complement | exact GlobalTheory.isHerm_plane_complement | (intros; apply GlobalTheory.isHerm_plane_complement <;> assumption)
