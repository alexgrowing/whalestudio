import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviHaarStabilizerMeasure
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_haar_stabilizer_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X Y : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ), B.IsGood σ → X.IsHerm σ B r s → (reS X Y).IsHerm σ B r s → H.IsAdapted σ B (reS X Y) X₁ i₀ i₁ → ∀ (μX : Measure (UA σ X.J)) (μ₁ : Measure (UA σ X₁.J)), μX.IsHaarMeasure → μ₁.IsHaarMeasure → ∀ (K : Subgroup (UA σ X.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab (X := X) B K → μK.IsHaarMeasure → μ.IsHaarMeasure → ∀ m : (AE F E)ˣ → UA σ X₁.J → UA σ X.J, (∀ l g₀, IsLevi (W₁ := X₁) H l g₀ (m l g₀)) → ∃ (μN : Measure (unip σ X H)) (c : ℝ≥0∞), μN.IsHaarMeasure ∧ c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ : UA σ X.J → ℝ≥0∞, Measurable φ → ∫⁻ g, φ g ∂μX = c * ∫⁻ k, ∫⁻ l, ∫⁻ g₀, ∫⁻ u, φ (u.1 * m l g₀ * k.1) * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - (n : ℝ))) ∂μN ∂μ₁ ∂μ ∂μK := by
  first | exact @GlobalTheory.IwasawaAdapted.iwasawa_formula_adapted | exact GlobalTheory.IwasawaAdapted.iwasawa_formula_adapted | (intros; apply GlobalTheory.IwasawaAdapted.iwasawa_formula_adapted <;> assumption)
