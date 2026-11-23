import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsNonzeroXbOfLeftInverse
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_xb_of_left_inverse : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (n : Ψ ⊕ Ψ → ℕ) (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω), (∀ k, ∃ i, x₀ ⟨k, i⟩ ≠ 0) → (∀ s, ∃ B : Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω, B * A s = 1) → ∀ k, ∃ i, xb A x₀ ⟨k, i⟩ ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.BasePt.xb_block_ne | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.BasePt.xb_block_ne | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.BasePt.xb_block_ne <;> assumption)
