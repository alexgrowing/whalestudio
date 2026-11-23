import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeCharacterIntegralZero
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_character_integral_zero : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), Ad3.IsStd ψ → ∀ A : GL (Fin 2) F,
  (¬ ∀ b, ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 b ∈ 𝒪[F]) →
  ∫ x, Set.indicator {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ)) x ∂Ad3.LFS.vol2 ψ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.integral_lattice_char_eq_zero | exact GlobalTheory.CompanionTheory.LFUDom.integral_lattice_char_eq_zero | (intros; apply GlobalTheory.CompanionTheory.LFUDom.integral_lattice_char_eq_zero <;> assumption)
