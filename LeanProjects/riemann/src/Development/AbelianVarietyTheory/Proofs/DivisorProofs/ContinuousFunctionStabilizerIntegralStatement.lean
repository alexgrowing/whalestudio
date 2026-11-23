import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFunctionStabilizerIntegral
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_function_stabilizer_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n₁ : ℕ) (X : Spc F E (n₁ + 2)) (X₁ : Spc F E n₁) (H : Plane E (n₁ + 2) n₁) (i₀ i₁ r s : ℕ), B.IsGood σ →
    X.IsHerm σ B r s → H.IsAdapted σ B X X₁ i₀ i₁ → ∀ K : Subgroup (UA σ X.J), IsStab B K →
    ∀ μK : Measure (KAt K (evI F)), μK.IsHaarMeasure → ∀ Ψ : UA σ X.J → ℂ, ContinuousOn Ψ (UAt σ X (evI F)) →
    (∀ p ∈ UAt σ X (evI F), ∀ g ∈ UAt σ X (evI F), ∀ t : (AE F E)ˣ, mat p *ᵥ incV F H.x = t.1 • incV F H.x →
      Ψ (p * g) = (((absE F E t : ℝ) ^ (n₁ + 1) : ℝ) : ℂ) * Ψ g) →
    ∀ g ∈ UAt σ X (evI F), ∫ k, Ψ (k.1 * g) ∂μK = ∫ k, Ψ k.1 ∂μK := by
  first | exact @GlobalTheory.KAvg.kInf_integral_mul_right | exact GlobalTheory.KAvg.kInf_integral_mul_right | (intros; apply GlobalTheory.KAvg.kInf_integral_mul_right <;> assumption)
