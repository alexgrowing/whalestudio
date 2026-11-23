import Formalism.HermitianCurvature.StatementQ

open Matrix MeasureTheory
open scoped ContDiff

noncomputable section

namespace QnRdSkewW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def SmoothOnSet {n : ℕ} (G : Set (Matrix (Fin n) (Fin n) ℂ)) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∀ g₀ ∈ G, ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → ℂ),
    IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ g ∈ U, g ∈ G → f g = F g

def StepGroup : Prop :=
  ∀ (k r : ℕ) (i : Fin (r + 1)) (X : Mx k r), inLieLev k r i X →
    IsClosed (Glev k r i) ∧ (∀ g ∈ Glev k r i, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i) ∧
      ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i

def StepAnalytic : Prop :=
  ∀ (n : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℂ)) (μ : Measure (Fin n → Fin n → ℂ)) (X : Matrix (Fin n) (Fin n) ℂ)
    (f₁ f₂ : Matrix (Fin n) (Fin n) ℂ → ℂ),
    IsClosed G → (∀ g ∈ G, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ G) → μ Gᶜ = 0 →
    (∀ t : ℝ, μ.map (B.rmulF (NormedSpace.exp ((t : ℂ) • X))) = μ) →
    (∀ K : Set (Fin n → Fin n → ℂ), IsCompact K → μ K < ⊤) →
    SmoothOnSet G f₁ → SmoothOnSet G f₂ →
    (∃ K : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact K ∧ ∀ g ∈ G, g ∉ K → f₁ g = 0) →
    (∃ K : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact K ∧ ∀ g ∈ G, g ∉ K → f₂ g = 0) →
    (∫ x, RdV X f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ) =
      -∫ x, f₁ (Matrix.of x) * star (RdV X f₂ (Matrix.of x)) ∂μ

theorem rdSkew_of (h1 : StepGroup) (h2 : StepAnalytic) : RdSkew := by
  intro k r i μ hμ X f₁ f₂ hX hs₁ hs₂ hc₁ hc₂
  obtain ⟨hcl, hfl, hexp⟩ := h1 k r i X hX
  exact h2 (2 * r + k + 1) (Glev k r i) μ X f₁ f₂ hcl hfl hμ.conc
    (fun t => hμ.right _ (hexp t)) hμ.finite_compact
    (fun g₀ hg₀ => hs₁ g₀ ⟨hg₀, Set.mem_univ _⟩) (fun g₀ hg₀ => hs₂ g₀ ⟨hg₀, Set.mem_univ _⟩) hc₁ hc₂

end QnRdSkewW
