import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeVolumeGlTwoTranslate
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_volume_gl_two_translate : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), Ad3.IsStd ψ → ∀ A : GL (Fin 2) F,
  (Ad3.LFS.vol2 ψ).real {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} = (modulus ((GeneralLinearGroup.det A : Fˣ) : F) : ℝ)⁻¹ * (Ad3.LFS.vol2 ψ).real {x : Fin 2 → F | ∀ i, x i ∈ 𝒪[F]} := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.latvol | exact GlobalTheory.CompanionTheory.LFUDom.latvol | (intros; apply GlobalTheory.CompanionTheory.LFUDom.latvol <;> assumption)
