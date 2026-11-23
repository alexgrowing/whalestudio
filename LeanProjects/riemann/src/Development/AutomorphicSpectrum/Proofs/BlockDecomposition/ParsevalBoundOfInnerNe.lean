import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParsevalBoundMax

noncomputable section
open MeasureTheory Complex Ad3 Ad3.LR Ad3.LR.C

namespace GlobalTheory.CompanionTheory.Parseval

theorem parseval_bound : Ad3.LR.C.ParsB := fun Φ N => by
  obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.Parseval.Max.parseval_bound_max Φ N
  exact ⟨C, fun ε hε hε1 h v hdet => by simpa [Dk] using hC ε hε hε1 h v hdet⟩

theorem parseval_bound_of_inner_ne (Φ : Sw) (N : ℕ) : ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (h : M22) (v : ℝ),
    (Matrix.of h).det ≠ 0 → h 0 0 * h 0 1 + h 1 0 * h 1 1 ≠ 0 → ‖Ae Φ ε h v‖ ≤ C * Dk N h := by
  obtain ⟨C, hC⟩ := parseval_bound Φ N
  exact ⟨C, fun ε hε hε1 h v hdet _ => hC ε hε hε1 h v hdet⟩

example : Ad3.LR.C.ParsB := parseval_bound

end GlobalTheory.CompanionTheory.Parseval
