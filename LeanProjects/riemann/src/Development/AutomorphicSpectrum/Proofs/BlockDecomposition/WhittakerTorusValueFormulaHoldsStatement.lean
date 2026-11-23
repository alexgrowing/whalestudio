import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTorusValueFormulaHolds
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_torus_value_formula_holds : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), Ad3.IsStd ψ → ∀ (ν : Fˣ →* ℂˣ) (a b : ℤ),
  (b ≤ a → Ad3.LFS.s2 ψ ν (torusPow F 2 ![a, b]) =
    sqrtQ F ^ (-(a - b)) * evalAt ![ν (unifUnit F), (ν (unifUnit F))⁻¹] (schur ![a, b])) ∧
  (a < b → Ad3.LFS.s2 ψ ν (torusPow F 2 ![a, b]) = 0) := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.whittaker_torus_value_formula | exact GlobalTheory.CompanionTheory.LFUDom.whittaker_torus_value_formula | (intros; apply GlobalTheory.CompanionTheory.LFUDom.whittaker_torus_value_formula <;> assumption)
