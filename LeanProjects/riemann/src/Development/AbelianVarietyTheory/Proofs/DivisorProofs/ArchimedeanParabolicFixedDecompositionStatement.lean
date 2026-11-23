import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanParabolicFixedDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_parabolic_fixed_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n₁ : ℕ) (X : Spc F E (n₁ + 2)) (X₁ : Spc F E n₁) (H : Plane E (n₁ + 2) n₁) (i₀ i₁ r s r₁ s₁ : ℕ), B.IsGood σ →
    X.IsHerm σ B r s → X₁.IsHerm σ B r₁ s₁ → H.IsAdapted σ B X X₁ i₀ i₁ →
    ∀ p ∈ UAt σ X (evI F), mat p *ᵥ incV F H.x = incV F H.x →
    ∃ n ∈ unip σ X H, n ∈ UAt σ X (evI F) ∧ ∃ g₀ : UA σ X₁.J, g₀ ∈ UAt σ X₁ (evI F) ∧
      ∃ g' : UA σ X.J, IsLevi H 1 g₀ g' ∧ g' ∈ UAt σ X (evI F) ∧ p = n * g' := by
  first | exact @GlobalTheory.ThK.LemF.stab_eq_unip_mul_levi_inf | exact GlobalTheory.ThK.LemF.stab_eq_unip_mul_levi_inf | (intros; apply GlobalTheory.ThK.LemF.stab_eq_unip_mul_levi_inf <;> assumption)
