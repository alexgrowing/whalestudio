import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralMatrixRowRepExists
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_matrix_row_rep_exists : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (g : GL (Fin 2) F), (∀ a b, (g : Matrix (Fin 2) (Fin 2) F) a b ∈ 𝒪[F]) →
  ∃ (i j : ℕ) (c : Fin j → 𝓀[F]), g * (rowRep i j c)⁻¹ ∈ integralGL F 2 := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.exists_mul_rowRep_inv_mem | exact GlobalTheory.CompanionTheory.LFUDom.exists_mul_rowRep_inv_mem | (intros; apply GlobalTheory.CompanionTheory.LFUDom.exists_mul_rowRep_inv_mem <;> assumption)
