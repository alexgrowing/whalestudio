import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DigitCharacterSumValues
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.digit_character_sum_values : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), Ad3.IsStd ψ → ∀ (j : ℕ) (m : ℤ),
  (0 ≤ m → ∑ c : Fin j → 𝓀[F], ((ψ (-(digitSum F j c) * (GLnLocal.uniformizer F : F) ^ m) : Circle) : ℂ) = (qF F : ℂ) ^ j) ∧
  (m < 0 → -m ≤ j → ∑ c : Fin j → 𝓀[F], ((ψ (-(digitSum F j c) * (GLnLocal.uniformizer F : F) ^ m) : Circle) : ℂ) = 0) := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.charsum | exact GlobalTheory.CompanionTheory.LFUDom.charsum | (intros; apply GlobalTheory.CompanionTheory.LFUDom.charsum <;> assumption)
