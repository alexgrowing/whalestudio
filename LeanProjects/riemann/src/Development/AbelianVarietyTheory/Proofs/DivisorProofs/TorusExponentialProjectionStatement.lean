import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExponentialProjection
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open Matrix GlobalTheory.TorFin
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_exponential_projection : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), Jᴴ = J → ∀ x y : Fin n → ℂ, (star x ᵥ* J) ⬝ᵥ x = 0 → (star y ᵥ* J) ⬝ᵥ y = 0 → (star x ᵥ* J) ⬝ᵥ y = 1 → ∀ ζ : ℂ, IsSkew J (ζ • projL J x y - star ζ • projL J y x) ∧ NormedSpace.exp (ζ • projL J x y - star ζ • projL J y x) = torMat J x y (Complex.exp ζ) := by
  first | exact @GlobalTheory.TorFin.TorusExp.exp_torus | exact GlobalTheory.TorFin.TorusExp.exp_torus | (intros; apply GlobalTheory.TorFin.TorusExp.exp_torus <;> assumption)
