import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicStabilizerBlockUnit
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
open Matrix Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_algebra_star_closed_bracket : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G → ∀ 𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), (∀ X, X ∈ 𝔤 ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G) → (∀ X ∈ 𝔤, Xᴴ ∈ 𝔤) ∧ ∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤 := by
  first | exact @GlobalTheory.CompanionTheory.LieStable.lieAlg_stable | exact GlobalTheory.CompanionTheory.LieStable.lieAlg_stable | (intros; apply GlobalTheory.CompanionTheory.LieStable.lieAlg_stable <;> assumption)
