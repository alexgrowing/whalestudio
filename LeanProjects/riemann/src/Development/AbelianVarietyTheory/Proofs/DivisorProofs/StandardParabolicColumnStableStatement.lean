import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicColumnStable
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_parabolic_column_stable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X : Matrix (Fin n) (Fin r) E)
    (S : Finset (Fin r)), (∀ k ∈ S, ∀ i ≤ k, i ∈ S) → ∀ i ∈ S, ∀ h : GAd σ J,
    (∀ h' ∈ ({h, h⁻¹} : Set (GAd σ J)),
      (∀ j : Fin r, (matHom _ σ J h').1 *ᵥ (adMat F X)ᵀ j - (adMat F X)ᵀ j ∈ GlobalTheory.StdPar.colSpan F X {l | l < j ∧ l ≤ i}) ∧
      ∀ y ∈ GlobalTheory.StdPar.colPerp σ J X {l | l ≤ i}, (matHom _ σ J h').1 *ᵥ y - y ∈ GlobalTheory.StdPar.colSpan F X {l | l ≤ i}) →
    h ∈ GlobalTheory.StdPar.unip σ J X S := by
  first | exact @GlobalTheory.StdPar.UnipCrit.mem_unip | exact GlobalTheory.StdPar.UnipCrit.mem_unip | (intros; apply GlobalTheory.StdPar.UnipCrit.mem_unip <;> assumption)
