import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalHomeomorphHeisenberg
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCA
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LeviModulus
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_radical_homeomorph_heisenberg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n n₁ : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (r s r₁ s₁ i₀ i₁ : ℕ) (H : Plane E n n₁),
    B.IsGood σ → X.IsHerm σ B r s → X₁.IsHerm σ B r₁ s₁ → H.IsAdapted σ B X X₁ i₀ i₁ →
    ∃ (Ψ : (Fin n₁ → AE F E) × imA σ ≃ₜ unip σ X H) (ω : (Fin n₁ → AE F E) → (Fin n₁ → AE F E) → imA σ),
      Continuous (fun p : (Fin n₁ → AE F E) × (Fin n₁ → AE F E) => ω p.1 p.2) ∧
      (∀ a b a' b', Ψ (a, b) * Ψ (a', b') = Ψ (a + a', b + b' + ω a a')) ∧
      ∀ (l : (AE F E)ˣ) (g₀ : UA σ X₁.J) (m : UA σ X.J), IsLevi H l g₀ m → ∀ a b,
        ∃ p : (Fin n₁ → AE F E) × imA σ, m * ((Ψ (a, b) : unip σ X H) : UA σ X.J) * m⁻¹ = ((Ψ p : unip σ X H) : UA σ X.J) ∧
          p.1 = cA σ l • (mat g₀ *ᵥ a) ∧ ((p.2 : imA σ) : AE F E) = l * cA σ l * b := by
  first | exact @GlobalTheory.LeviModulus.HCoord.heis_coords | exact GlobalTheory.LeviModulus.HCoord.heis_coords | (intros; apply GlobalTheory.LeviModulus.HCoord.heis_coords <;> assumption)
