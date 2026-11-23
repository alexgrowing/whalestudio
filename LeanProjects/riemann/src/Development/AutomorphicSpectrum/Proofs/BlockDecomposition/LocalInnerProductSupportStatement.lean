import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInnerProductSupport
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_inner_product_support : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) (h : GL (Fin 2) F) (l : Fin 3 → ℤ),
  ((¬ ∀ a b, ((h * torusPow F 2 ![l 0, l 1] : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) a b ∈ 𝒪[F]) →
    Ad3.LFS.inn ψ (Ad3.LFS.Φ0 F) h (torusPow F 3 l) = 0) ∧
  ((∀ a b, ((h * torusPow F 2 ![l 0, l 1] : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) a b ∈ 𝒪[F]) →
    Ad3.LFS.inn ψ (Ad3.LFS.Φ0 F) h (torusPow F 3 l) =
      ∫ x, Set.indicator {x : Fin 2 → F | ∀ i, (((torusPow F 2 ![l 2, l 2] * h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ)) x ∂Ad3.LFS.vol2 ψ) := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.innred | exact GlobalTheory.CompanionTheory.LFUDom.innred | (intros; apply GlobalTheory.CompanionTheory.LFUDom.innred <;> assumption)
