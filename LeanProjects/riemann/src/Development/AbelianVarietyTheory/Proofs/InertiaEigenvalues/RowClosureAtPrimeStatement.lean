import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowClosureAtPrime
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.ElevenLe
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_closure_at_prime : Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : GlobalTheory.Mem.Top.Bl.Prm hL) (C : ℝ) (CT : ℕ), 0 ≤ C → GlobalTheory.Fc.RL.At p (fun S L => GlobalTheory.Fc.RowE S L fun _ D O _ _ => GlobalTheory.NFacts.Facts D O.ex.nch) → GlobalTheory.Fc.RL.At p (fun S L => GlobalTheory.Fc.RowE S L fun _ D _ _ _ => Extra D C CT) → GlobalTheory.Fc.RL.At p (fun S L => GlobalTheory.Fc.R1.PredicateAtBundlePoints S L fun 𝒞 => Closed 𝒞 fun Fm _ => BoundAtTwoAndThreeForFamily Fm) → GlobalTheory.Fc.RL.At p (fun S L => GlobalTheory.Fc.R1.PredicateAtBundlePoints S L fun 𝒞 => Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm) := by
  first | exact @GlobalTheory.NLink.linkN_at | exact GlobalTheory.NLink.linkN_at | (intros; apply GlobalTheory.NLink.linkN_at <;> assumption)
