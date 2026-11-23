import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyGroupAlgebraCentreLatticeAction
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_groupAlgebraCentreLatticeAction : ∀ D : D7, (∀ i, Nonempty (Sec D i)) → ZLStable D → CenInt D → OnMtPreservesTypeV D → Nonempty (CenO D) := by
  first | exact @GlobalTheory.CenOAct.cenO_nonempty | exact GlobalTheory.CenOAct.cenO_nonempty | (intros; apply GlobalTheory.CenOAct.cenO_nonempty <;> assumption)
