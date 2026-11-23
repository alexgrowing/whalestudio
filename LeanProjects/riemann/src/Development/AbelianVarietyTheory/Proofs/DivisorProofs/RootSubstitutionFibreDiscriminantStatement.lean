import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSubstitutionFibreDiscriminant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSub
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
open NumberField MvPolynomial
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_substitution_fibre_discriminant : ∀ (D : D7) (O : Setup D), GlobalTheory.GoodMetric.antisymm (aeval (GlobalTheory.RelabDR.rootSub O) (fibPt D.what₂.Tau O.N O.j)) = GlobalTheory.GoodMetric.rootDiscr O.S.Dw.mult := by
  first | exact @GlobalTheory.RelabDR.antisymm_fibPt | exact GlobalTheory.RelabDR.antisymm_fibPt | (intros; apply GlobalTheory.RelabDR.antisymm_fibPt <;> assumption)
