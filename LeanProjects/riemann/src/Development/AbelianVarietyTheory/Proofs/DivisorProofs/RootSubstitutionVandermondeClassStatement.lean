import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSubstitutionVandermondeClass
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSub
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
open NumberField MvPolynomial
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_substitution_vandermonde_class : ∀ (D : D7) (O : Setup D), GlobalTheory.GoodMetric.antisymm (aeval (GlobalTheory.RelabDR.rootSub O) (GlobalTheory.CovTestDR.vdmCl D.what₂.Tau O.N O.j)) = GlobalTheory.GoodMetric.rootDiscr O.S.Dw.mult := by
  first | exact @GlobalTheory.RelabDRVdm.antisymm_vdmCl | exact GlobalTheory.RelabDRVdm.antisymm_vdmCl | (intros; apply GlobalTheory.RelabDRVdm.antisymm_vdmCl <;> assumption)
