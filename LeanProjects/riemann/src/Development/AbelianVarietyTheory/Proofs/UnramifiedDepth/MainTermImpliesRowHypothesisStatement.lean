import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MainTermImpliesRowHypothesis
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
open Formalism.L2.FormalSeriesBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mainTerm_implies_rowHypothesis : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.MtoHM := by
  first | exact @GlobalTheory.mainTerm_to_rowHypothesis | exact GlobalTheory.mainTerm_to_rowHypothesis | (intros; apply GlobalTheory.mainTerm_to_rowHypothesis <;> assumption)
