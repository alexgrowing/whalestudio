import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFamilyRelabelledSigns
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSub
open NumberField MvPolynomial
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_family_relabelled_signs : ∀ (D : D7) (O : Setup D), (∀ i, GlobalTheory.RelabDR.sg O i = 1 ∨ GlobalTheory.RelabDR.sg O i = -1) ∧ ∀ (R : ℝ) (i : GlobalTheory.EigWhole.Var O), (∃ z, GlobalTheory.RelabDR.ix O i = .inl z ∧ GlobalTheory.EigWhole.fam O ∅ R i = Finsupp.single (ArIn.ind ∅, some R, .inl (z.1, (z.2 : ℕ))) (GlobalTheory.RelabDR.sg O i)) ∨ ∃ z k, GlobalTheory.RelabDR.ix O i = .inr z ∧ (letters O.S.Dw)[k]? = some z ∧ GlobalTheory.EigWhole.fam O ∅ R i = Finsupp.single (ArIn.ind ∅, some R, .inr k) (GlobalTheory.RelabDR.sg O i) := by
  first | exact @GlobalTheory.RelabDR.fam_eq_single | exact GlobalTheory.RelabDR.fam_eq_single | (intros; apply GlobalTheory.RelabDR.fam_eq_single <;> assumption)
