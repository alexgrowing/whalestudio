import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CartanLocalToGlobal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
open Matrix Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartan_local_to_global : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G → ∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, (∀ᶠ g in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), g ∈ G → ∃ k ∈ GlobalTheory.LinRed.maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id) → ∀ g ∈ G, ∃ k ∈ GlobalTheory.LinRed.maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id := by
  first | exact @GlobalTheory.CompanionTheory.LinRedFactor.factor_of_local | exact GlobalTheory.CompanionTheory.LinRedFactor.factor_of_local | (intros; apply GlobalTheory.CompanionTheory.LinRedFactor.factor_of_local <;> assumption)
