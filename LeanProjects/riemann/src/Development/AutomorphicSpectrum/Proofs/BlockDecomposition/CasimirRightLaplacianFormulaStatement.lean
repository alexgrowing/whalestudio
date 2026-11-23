import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirRightLaplacianFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_right_laplacian_formula : ∀ {n : ℕ} (E : KMod n), ∃ A : E.V →L[ℂ] E.V, ∀ f ∈ CE E, ∀ g ∈ GLs n, Om f g = (1 / 4 : ℂ) • ∑ p : Ix n, Rd (hm p) (Rd (hm p) f) g + A (f g) := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.om_section | exact GlobalTheory.CompanionTheory.WaveSpd.om_section | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.om_section <;> assumption)
