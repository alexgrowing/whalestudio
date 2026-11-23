import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0

def RealTest : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (P : Submodule ℝ V)
    (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ x y, b x y = b y x) →
    ∃ f₀ : SchwartzMap V ℂ, ∀ T : SchwartzMap V ℂ →L[ℂ] ℂ,
      (∀ p ∈ P, ∀ f g : SchwartzMap V ℂ,
        (∀ x, g x = Complex.exp (2 * Real.pi * Complex.I * ((b x p + b p p / 2 : ℝ) : ℂ)) * f (x + p)) → T g = T f) →
      (∀ l : V →ₗ[ℝ] ℝ, (∀ p ∈ P, l p = 0) → ∀ f g : SchwartzMap V ℂ,
        (∀ x, g x = Complex.exp (2 * Real.pi * Complex.I * ((l x : ℝ) : ℂ)) * f x) → T g = T f) →
      T f₀ = 0 → T = 0

def LagLine : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (L : Submodule F ((κ → F) × (κ → F))), (∀ a, a ∈ L ↔ ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) →
    ∀ l₁ ∈ (adeleClass F).adm κ, ∀ l₂ ∈ (adeleClass F).adm κ,
    (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l₁ (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l₁ φ) →
    (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l₂ (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l₂ φ) →
    (∃ φ ∈ schA F κ, l₂ φ ≠ 0) → ∃ c : ℂ, ∀ φ ∈ schA F κ, l₁ φ = c * l₂ φ

end PositivityTheory.ThKF0
