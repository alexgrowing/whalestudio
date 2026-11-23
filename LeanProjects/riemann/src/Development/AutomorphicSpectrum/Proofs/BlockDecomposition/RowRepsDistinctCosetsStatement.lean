import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowRepsDistinctCosets
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_reps_distinct_cosets : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (a b : Σ _ : ℕ, Σ j : ℕ, (Fin j → 𝓀[F])),
  rowRep a.1 a.2.1 a.2.2 * (rowRep b.1 b.2.1 b.2.2)⁻¹ ∈ integralGL F 2 → a = b := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.rowRep_unique | exact GlobalTheory.CompanionTheory.LFUDom.rowRep_unique | (intros; apply GlobalTheory.CompanionTheory.LFUDom.rowRep_unique <;> assumption)
