import Mathlib
import Formalism.PeriodIntegrals.UMultOne

noncomputable section

namespace PI.UnitaryGroupMassFormula.GelfCpt

open MeasureTheory Matrix

def intMat {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) {N : ℕ}
    (ρ : G →* GL (Fin N) ℂ) (f : G → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => ∫ g, f g * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ

def AvgStep : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] (H : Subgroup G), IsClosed (H : Set G) →
    ∀ (N : ℕ) (ρ : G →* GL (Fin N) ℂ), PI.UMultOne.Cont ρ →
    ∀ f : G → ℂ, Continuous f →
      (∀ h ∈ H, ((ρ h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * intMat μ ρ f =
        intMat μ ρ f * ((ρ h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) →
      ∃ f' : G → ℂ, Continuous f' ∧ (∀ h ∈ H, ∀ x, f' (h * x * h⁻¹) = f' x) ∧
        intMat μ ρ f' = intMat μ ρ f

def MulStep : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] (N : ℕ) (ρ : G →* GL (Fin N) ℂ), PI.UMultOne.Cont ρ →
    ∀ f₁ f₂ : G → ℂ, Continuous f₁ → Continuous f₂ →
      intMat μ ρ f₁ * intMat μ ρ f₂ = intMat μ ρ (fun z => ∫ x, f₁ x * f₂ (x⁻¹ * z) ∂μ)

end PI.UnitaryGroupMassFormula.GelfCpt
