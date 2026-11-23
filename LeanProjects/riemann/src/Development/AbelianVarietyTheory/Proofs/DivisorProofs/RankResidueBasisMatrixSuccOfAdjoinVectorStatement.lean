import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankResidueBasisMatrixSuccOfAdjoinVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_residue_basis_matrix_succ_of_adjoin_vector : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : ℕ) (ϖ : O) (Ac As : Matrix (Fin n) (Fin n) O) (x : Fin n → O), Irreducible ϖ → (∀ y : Fin n → O, ∃ u, Ac *ᵥ u = fun a => ϖ * y a) → (∀ w, ∃ u c, As *ᵥ w = Ac *ᵥ u + fun a => c * x a) → (∃ w, As *ᵥ w = x) → (∀ u, ∃ w, As *ᵥ w = Ac *ᵥ u) → (¬ ∃ u, Ac *ᵥ u = x) → (As.map (residue O)).rank = (Ac.map (residue O)).rank + 1 := by
  first | exact @GlobalTheory.rank_residue_succ_of_adjoin | exact GlobalTheory.rank_residue_succ_of_adjoin | (intros; apply GlobalTheory.rank_residue_succ_of_adjoin <;> assumption)
