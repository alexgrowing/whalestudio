import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSchwartzZetaSeparatingCharacter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GTil
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_schwartz_zeta_separating_character : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (η : Fˣ →* ℂˣ), Continuous η → ∀ t : Fˣ, η t = -1 → ∃ g : F → ℂ, g ∈ schwartzBruhat F ∧ g 0 = 0 ∧ localZeta g 1 (1 / 2) = 0 ∧ localZeta g η (1 / 2) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.GaussLam.TestFn.exists_test | exact GlobalTheory.CompanionTheory.GaussLam.TestFn.exists_test | (intros; apply GlobalTheory.CompanionTheory.GaussLam.TestFn.exists_test <;> assumption)
