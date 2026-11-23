import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist

noncomputable section

open scoped Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel

namespace PositivityTheory.Rg.Rsw

def HeckeEta : Prop := ∀ (D : D7) (k : ℕ), ∃ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ ∧ ResEta D χ k

def RightId : Prop :=
  ∀ (U : Set ℂ) (h g : ℂ → ℂ) (c σ : ℝ), IsOpen U → IsRightDomain U → DifferentiableOn ℂ h U →
    DifferentiableOn ℂ g {z : ℂ | c < z.re} → (∀ z : ℂ, σ < z.re → h z = g z) → ∀ z ∈ U, c < z.re → h z = g z

def PoleReal : Prop :=
  ∀ (h : ℂ → ℂ) (d : Polynomial ℂ) (s₀ ε : ℝ), 0 < ε → d ≠ 0 → DifferentiableOn ℂ h (Metric.closedBall (s₀ : ℂ) ε) →
    (∀ z ∈ Metric.sphere (s₀ : ℂ) ε, DifferentiableAt ℂ h z) →
    (∀ z ∈ Metric.closedBall (s₀ : ℂ) ε, z ≠ s₀ → d.eval z ≠ 0) →
    ((∃ B : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s₀, ‖((σ - s₀ : ℝ) : ℂ) * (h σ / d.eval (σ : ℂ))‖ ≤ B) →
      (∀ k : ℕ, 2 ≤ k → ∮ z in C((s₀ : ℂ), ε), (z - s₀) ^ (k - 1) * (h z / d.eval z) = 0) ∧
      Tendsto (fun σ : ℝ => ((σ - s₀ : ℝ) : ℂ) * (h σ / d.eval (σ : ℂ))) (𝓝[>] s₀)
        (𝓝 ((2 * Real.pi * Complex.I)⁻¹ * ∮ z in C((s₀ : ℂ), ε), (z - s₀) ^ (1 - 1) * (h z / d.eval z)))) ∧
    ((∃ B : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s₀, ‖h σ / d.eval (σ : ℂ)‖ ≤ B) →
      ∀ k : ℕ, 1 ≤ k → ∮ z in C((s₀ : ℂ), ε), (z - s₀) ^ (k - 1) * (h z / d.eval z) = 0)

end PositivityTheory.Rg.Rsw

end
