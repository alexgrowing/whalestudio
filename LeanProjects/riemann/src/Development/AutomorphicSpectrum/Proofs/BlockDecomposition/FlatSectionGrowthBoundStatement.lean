import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatSectionGrowthBound
import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_section_growth_bound : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n} (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsCompact (K : Set (G2 σ Y)) → IsHgt K a → (∀ x, 0 < a x) → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → ∃ C : ℝ, ∀ (s : ℂ) (x : G2 σ Y), ‖flat a f s₁ s x‖ ≤ C * a x ^ (s.re + (n : ℝ) / 2) := by
  first | exact @GlobalTheory.CompanionTheory.EisTerm.flat_norm_le_height_rpow | exact GlobalTheory.CompanionTheory.EisTerm.flat_norm_le_height_rpow | (intros; apply GlobalTheory.CompanionTheory.EisTerm.flat_norm_le_height_rpow <;> assumption)
