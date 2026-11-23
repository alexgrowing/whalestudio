import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraRepDerivationMatrix
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_algebra_rep_derivation_matrix : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), Aᴴ = A → IsUnit A.det → ∀ (B : Type) [Ring B] [Algebra ℂ B]
    (ρ : Matrix (Fin n) (Fin n) ℂ → B),
    (∀ X X', Xᴴ * A + A * X = 0 → X'ᴴ * A + A * X' = 0 → ρ (X + X') = ρ X + ρ X') →
    (∀ (c : ℝ) X, Xᴴ * A + A * X = 0 → ρ (c • X) = (c : ℂ) • ρ X) →
    (∀ X X', Xᴴ * A + A * X = 0 → X'ᴴ * A + A * X' = 0 → ρ (X * X' - X' * X) = ρ X * ρ X' - ρ X' * ρ X) →
    ∃ D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] B, (∀ X X', D (X * X' - X' * X) = D X * D X' - D X' * D X) ∧
      ∀ X, Xᴴ * A + A * X = 0 → D X = ρ X := by
  first | exact @GlobalTheory.LeviHC.exists_complexLinear_bracket_ext | exact GlobalTheory.LeviHC.exists_complexLinear_bracket_ext | (intros; apply GlobalTheory.LeviHC.exists_complexLinear_bracket_ext <;> assumption)
