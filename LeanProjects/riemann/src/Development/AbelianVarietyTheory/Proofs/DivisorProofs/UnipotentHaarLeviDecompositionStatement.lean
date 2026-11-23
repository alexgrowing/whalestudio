import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentHaarLeviDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_haar_levi_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X Y : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ), B.IsGood σ → X.IsHerm σ B r s → (reS X Y).IsHerm σ B r s → H.IsAdapted σ B (reS X Y) X₁ i₀ i₁ → ∀ m : (AE F E)ˣ → UA σ X₁.J → UA σ X.J, (∀ l g₀, IsLevi (W₁ := X₁) H l g₀ (m l g₀)) → ∀ μN : Measure (unip σ X H), μN.IsHaarMeasure → ∀ (g₀ : UA σ X₁.J) (f : UA σ X.J → ℝ≥0∞), Measurable f → ∫⁻ u, f (u.1 * m 1 g₀) ∂μN = ∫⁻ u, f (m 1 g₀ * u.1) ∂μN := by
  first | exact @GlobalTheory.LeviConjOne.lintegral_mul_levi_one | exact GlobalTheory.LeviConjOne.lintegral_mul_levi_one | (intros; apply GlobalTheory.LeviConjOne.lintegral_mul_levi_one <;> assumption)
