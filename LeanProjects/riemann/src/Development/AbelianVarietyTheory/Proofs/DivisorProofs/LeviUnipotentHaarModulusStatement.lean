import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviUnipotentHaarModulus
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_unipotent_haar_modulus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n n₁ : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (r s r₁ s₁ i₀ i₁ : ℕ) (H : Plane E n n₁), B.IsGood σ → X.IsHerm σ B r s →
    X₁.IsHerm σ B r₁ s₁ → H.IsAdapted σ B X X₁ i₀ i₁ → ∀ m : (AE F E)ˣ → UA σ X₁.J → UA σ X.J, (∀ l g₀, IsLevi H l g₀ (m l g₀)) →
    ∀ (μN : Measure (unip σ X H)), μN.IsHaarMeasure → ∀ l g₀ (f : UA σ X.J → ENNReal), Measurable f →
      ∫⁻ u, f (m l g₀ * u.1 * (m l g₀)⁻¹) ∂μN = ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - (n : ℝ))) * ∫⁻ u, f u.1 ∂μN := by
  first | exact @GlobalTheory.LeviModulus.lintegral_conj_levi | exact GlobalTheory.LeviModulus.lintegral_conj_levi | (intros; apply GlobalTheory.LeviModulus.lintegral_conj_levi <;> assumption)
