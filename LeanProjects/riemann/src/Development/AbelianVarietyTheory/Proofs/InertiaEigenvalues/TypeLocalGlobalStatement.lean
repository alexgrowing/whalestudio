import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeLocalGlobal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_local_global : ∀ (D : D7) (P : PairedCharacterCondition.Pend D), PairedCharacterCondition.admDZ P → SumRepresentations.tie0 D → WDAbove D → TypeLGC P := by
  first | exact @GlobalTheory.TypeAbove.main | exact GlobalTheory.TypeAbove.main | (intros; apply GlobalTheory.TypeAbove.main <;> assumption)
