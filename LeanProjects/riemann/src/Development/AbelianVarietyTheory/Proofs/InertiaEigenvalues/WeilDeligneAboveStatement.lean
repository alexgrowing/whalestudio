import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneAbove
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_deligne_above : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → WDAbove D := by
  first | exact @GlobalTheory.WDAboveProof.main | exact GlobalTheory.WDAboveProof.main | (intros; apply GlobalTheory.WDAboveProof.main <;> assumption)
