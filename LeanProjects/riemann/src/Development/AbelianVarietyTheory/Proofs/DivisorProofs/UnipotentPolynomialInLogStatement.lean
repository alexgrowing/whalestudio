import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentPolynomialInLog
import Mathlib

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_polynomial_in_log : ∀ (G : Type) [CommGroup G] [TopologicalSpace G] (H : Set G) (L : G → ℂ), (∀ φ : G → ℂ, Continuous φ → (∀ s t, φ (s * t) = φ s + φ t) → (∀ γ ∈ H, φ γ = 0) → ∃ A : ℂ, ∀ t, φ t = A * L t) → ∀ (d : ℕ) (u : G →* Matrix (Fin d) (Fin d) ℂ), (∀ s, IsNilpotent (u s - 1)) → (∀ γ ∈ H, u γ = 1) → (∀ i j, Continuous fun s => u s i j) → ∃ (K : ℕ) (M : ℕ → Matrix (Fin d) (Fin d) ℂ), ∀ s, u s = ∑ k ∈ Finset.range K, L s ^ k • M k := by
  first | exact @GlobalTheory.UnipotentLog.main | exact GlobalTheory.UnipotentLog.main | (intros; apply GlobalTheory.UnipotentLog.main <;> assumption)
