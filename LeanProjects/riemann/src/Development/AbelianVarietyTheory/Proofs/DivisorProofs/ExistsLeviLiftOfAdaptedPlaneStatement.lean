import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviLiftOfAdaptedPlane
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levi_lift_of_adapted_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ), B.IsGood σ → X.IsHerm σ B r s → H.IsAdapted σ B X X₁ i₀ i₁ → ∀ (l : (AE F E)ˣ) (g₀ : UA σ X₁.J), ∃ m : UA σ X.J, IsLevi (W₁ := X₁) H l g₀ m := by
  first | exact @GlobalTheory.LeviFrameH.exists_levi_herm | exact GlobalTheory.LeviFrameH.exists_levi_herm | (intros; apply GlobalTheory.LeviFrameH.exists_levi_herm <;> assumption)
