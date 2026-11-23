import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharacterUniformizerPower
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_character_uniformizer_power : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (m t : ℤ), Ad3.mp (uniformizerUnit F ^ m) ((t : ℂ) / 2) = sqrtQ F ^ (-(t * m)) := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.mp_uniformizerUnit_zpow_half | exact GlobalTheory.CompanionTheory.LFUDom.mp_uniformizerUnit_zpow_half | (intros; apply GlobalTheory.CompanionTheory.LFUDom.mp_uniformizerUnit_zpow_half <;> assumption)
