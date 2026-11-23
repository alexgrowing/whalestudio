import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowClosureLinking
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.ElevenLe
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_closure_linking : Hypotheses₂ → ∀ (Q : GlobalTheory.Mem.Top.V4.Slot) (Lk : GlobalTheory.Fc.LkT GlobalTheory.Fc.Bundle) (C : ℝ) (CT : ℕ), 0 ≤ C → GlobalTheory.Fc.RowE Q Lk (fun _ D O _ _ => GlobalTheory.NFacts.Facts D O.ex.nch ∧ Extra D C CT) → GlobalTheory.Fc.R1.PredicateAtBundlePoints Q Lk (fun 𝒞 => Closed 𝒞 fun Fm _ => BoundAtTwoAndThreeForFamily Fm) → GlobalTheory.Fc.R1.PredicateAtBundlePoints Q Lk (fun 𝒞 => Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm) := by
  first | exact @GlobalTheory.NLink.linkN_row | exact GlobalTheory.NLink.linkN_row | (intros; apply GlobalTheory.NLink.linkN_row <;> assumption)
