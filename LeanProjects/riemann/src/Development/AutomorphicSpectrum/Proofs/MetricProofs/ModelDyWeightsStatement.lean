import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ModelDyWeights
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_dy_weights : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (n : Ψ ⊕ Ψ → ℕ) (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (m : Ψ ⊕ Ψ → ℕ) (h : ModelOK A x₀ m) (τ : Ψ) (i : Fin (p + q)), (∀ k, (model A x₀ m h).dy (τ, i) (.inl k) = -((rkW i * m (.inl τ) + rkO i * m (.inr τ) : ℕ) : ℤ)) ∧ ∀ t : StepIx Ψ p q, ((t = stepOf Ψ p q (τ, i) ∨ (t.1 = .inl τ ∧ (t.2 : ℕ) + 1 = p ∧ p ≤ (i : ℕ))) → (model A x₀ m h).dy (τ, i) (.inr t) = 1) ∧ (¬ (t = stepOf Ψ p q (τ, i) ∨ (t.1 = .inl τ ∧ (t.2 : ℕ) + 1 = p ∧ p ≤ (i : ℕ))) → (model A x₀ m h).dy (τ, i) (.inr t) = 0) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Dy.dy_flag | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.Dy.dy_flag | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.Dy.dy_flag <;> assumption)
