import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsNormEmbId

noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace

namespace PositivityTheory.RgHe.A

def EigA : Prop := ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (d : ℝ), IsU σ → IsU ρ →
    IsFd ν σ d → ∀ w₀ : A, ‖w₀‖ = 1 → Integrable (fun g => ⟪w₀, σ g w₀⟫_ℂ) ν → ∀ i : A →L[ℂ] B, IsIsoMap σ ρ i →
    ∀ v : B, Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν →
    ∃ (w : A) (c : ℝ), w ≠ 0 ∧ ‖ContinuousLinearMap.adjoint i v‖ ^ 2 / (2 * d) ≤ c ∧
      ∀ b : A, Integrable (fun g => star ⟪v, ρ g v⟫_ℂ * ⟪b, σ g w⟫_ℂ) ν ∧
        ∫ g, star ⟪v, ρ g v⟫_ℂ * ⟪b, σ g w⟫_ℂ ∂ν = c * ⟪b, w⟫_ℂ

def TMap : Prop := ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (d : ℝ), IsU σ → IsU ρ →
    IsFd ν σ d → ∀ v : B, Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν → ∀ (w : A) (c : ℝ), c ≠ 0 →
    (∀ b : A, ∫ g, star ⟪v, ρ g v⟫_ℂ * ⟪b, σ g w⟫_ℂ ∂ν = c * ⟪b, w⟫_ℂ) →
    ∃ T : B →L[ℂ] A, IsMap ρ σ T ∧ T v = w

end PositivityTheory.RgHe.A
