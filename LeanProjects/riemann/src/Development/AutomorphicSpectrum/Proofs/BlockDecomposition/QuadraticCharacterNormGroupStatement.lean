import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticCharacterNormGroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GTil
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_character_norm_group : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (η : Fˣ →* ℂˣ), Continuous η → (∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) → ∀ g : F → ℂ, g ∈ schwartzBruhat F → g 0 = 0 → GlobalTheory.CompanionTheory.GaussLam.gTil E g ∈ schwartzBruhat F ∧ ∀ c : Fˣ →* ℂˣ, localZeta (GlobalTheory.CompanionTheory.GaussLam.gTil E g) c (1 / 2) = ((c (-1) : ℂˣ) : ℂ) * localZeta g (η * c⁻¹) (1 / 2) := by
  first | exact @GlobalTheory.CompanionTheory.GaussLam.gTil_schwartzBruhat_zeta | exact GlobalTheory.CompanionTheory.GaussLam.gTil_schwartzBruhat_zeta | (intros; apply GlobalTheory.CompanionTheory.GaussLam.gTil_schwartzBruhat_zeta <;> assumption)
