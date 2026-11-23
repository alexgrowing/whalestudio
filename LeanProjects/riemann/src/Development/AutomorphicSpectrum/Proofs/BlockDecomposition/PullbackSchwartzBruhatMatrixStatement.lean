import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackSchwartzBruhatMatrix
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lpart
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_schwartz_bruhat_matrix : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (Φ : Matrix (Fin 2) (Fin 3) F → ℂ), Φ ∈ LFS.SB F → ∀ h z : GL (Fin 2) F, SB2 (Pf Φ h z) := by
  first | exact @GlobalTheory.CompanionTheory.GL2DualWhittakerPair.pullback_schwartz_bruhat_M2 | exact GlobalTheory.CompanionTheory.GL2DualWhittakerPair.pullback_schwartz_bruhat_M2 | (intros; apply GlobalTheory.CompanionTheory.GL2DualWhittakerPair.pullback_schwartz_bruhat_M2 <;> assumption)
