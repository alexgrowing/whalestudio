import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplierExponentialHolomorphicLocal
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplier_exponential_holomorphic_local : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} (u : Fl g → Pt E g → ℂ) (a : Fin g ⊕ Fin g → Pt E g → ℂ), (∀ i, ∀ P ∈ cov U g, u (Pi.single i 1) P = Complex.exp (2 * π * Complex.I * a i P)) → (∀ i, ContinuousOn (a i) (cov U g)) → (∀ b ∈ U, ∃ f : Fl g → (Fin g → ℂ) → ℂ, (∀ l ∈ stdLat g, Differentiable ℂ (f l) ∧ ∀ z, u l (b, z) = Complex.exp (2 * π * Complex.I * f l z)) ∧ ∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ z, f l (z + per (τ b) l') + f l' z - f l' (z + per (τ b) l) - f l z = 0) → ∀ i j, ∀ P ∈ cov U g, a i (transl τ (Pi.single j 1) P) + a j P = a j (transl τ (Pi.single i 1) P) + a i P := by
  first | exact @GlobalTheory.degZero_log_comm | exact GlobalTheory.degZero_log_comm | (intros; apply GlobalTheory.degZero_log_comm <;> assumption)
