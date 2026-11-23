import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianPushforwardDensity
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_pushforward_density : ∀ (ι : Type) [Fintype ι] (n : ℕ) (ε : ι → Fin n → Bool) (G : (ι → ℝ) → ℂ), Continuous G → (∀ S : Set (ι → ℝ), IsCompact S → ∫ y in (fun (y : ι → Fin n → ℂ) (v : ι) => qEps (ε v) (y v)) ⁻¹' S, ((∏ v, gauss (y v) : ℝ) : ℂ) = ∫ b in S, G b) → ∀ b : ι → ℝ, (∀ v, b v ≠ 0) → G b = ((∏ v, gaussDens (ε v) (b v) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.GaussMean.ProdDensity.density_eq_prod | exact GlobalTheory.GaussMean.ProdDensity.density_eq_prod | (intros; apply GlobalTheory.GaussMean.ProdDensity.density_eq_prod <;> assumption)
