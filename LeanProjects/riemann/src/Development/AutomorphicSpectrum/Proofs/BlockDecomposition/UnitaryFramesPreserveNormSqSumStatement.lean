import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryFramesPreserveNormSqSum
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_frames_preserve_norm_sq_sum : ∀ (m : ℕ), 1 ≤ m → ∀ (J : Matrix (Fin m) (Fin m) ℂ) (fr fr' : GL (Fin m) ℂ) (ζ ζ' : ℂ) (s s' : ℤˣ), (ζ = 1 ∨ ζ = Complex.I) → (ζ' = 1 ∨ ζ' = Complex.I) → ζ • (fr.1ᵀ * J * fr.1.map star) = ((s : ℤ) : ℂ) • 1 → ζ' • (fr'.1ᵀ * J * fr'.1.map star) = ((s' : ℤ) : ℂ) • 1 → ∀ v : Fin m → ℂ, ∑ a, ‖((fr⁻¹).1 *ᵥ v) a‖ ^ 2 = ∑ a, ‖((fr'⁻¹).1 *ᵥ v) a‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.UnitFrame.normSq_eq_of_unit_frames | exact GlobalTheory.CompanionTheory.UnitFrame.normSq_eq_of_unit_frames | (intros; apply GlobalTheory.CompanionTheory.UnitFrame.normSq_eq_of_unit_frames <;> assumption)
