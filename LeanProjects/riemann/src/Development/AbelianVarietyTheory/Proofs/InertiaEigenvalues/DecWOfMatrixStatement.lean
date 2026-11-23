import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecWOfMatrix
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decW_of_matrix_criterion : ∀ (S : Sit) (E : S.Comparison₂), (∀ (d : ℕ) (Pm : Matrix (Fin d) (Fin d) S.W.EE), (∀ y : Fin d → S.RW, (∀ i, ∀ g ∈ Hker S, S.gR g (y i) = y i) → ∃ z : Fin d → S.RW, (∀ i, ∀ g ∈ Hker S, S.gR g (z i) = z i) ∧ ∀ i, ∃ e, y i - (∑ k, E.ioE (Pm i k) * S.φR (z k) - z i) = E.ioE e) ∧ (∀ z : Fin d → S.RW, (∀ i, ∀ g ∈ Hker S, S.gR g (z i) = z i) → (∀ i, ∃ e, ∑ k, E.ioE (Pm i k) * S.φR (z k) - z i = E.ioE e) → ∀ i, ∃ e, z i = E.ioE e)) → DecW S E := by
  first | exact @GlobalTheory.DecomplRed.decW_of_matrix | exact GlobalTheory.DecomplRed.decW_of_matrix | (intros; apply GlobalTheory.DecomplRed.decW_of_matrix <;> assumption)
