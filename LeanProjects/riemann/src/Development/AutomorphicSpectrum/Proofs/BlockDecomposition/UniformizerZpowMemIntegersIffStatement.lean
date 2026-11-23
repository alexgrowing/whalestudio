import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerZpowMemIntegersIff
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizer_zpow_mem_integers_iff' : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (z : ℤ), (GLnLocal.uniformizer F : F) ^ z ∈ 𝒪[F] ↔ 0 ≤ z := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.uniformizer_zpow_mem_integers_iff | exact GlobalTheory.CompanionTheory.LFUDom.uniformizer_zpow_mem_integers_iff | (intros; apply GlobalTheory.CompanionTheory.LFUDom.uniformizer_zpow_mem_integers_iff <;> assumption)
