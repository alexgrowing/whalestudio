import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenTwistAnnihilatesSelmerGroups
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chosenTwist_annihilates_selmerGroups : ∀ (D : D7) (C : NChoice D) (I : TwIn D) (ρ : FamilyRepresentationConstants.RhoFam D), NChTie D C → TwGoodAt D C I → KillingConditions.SignatureChoiceCondition ρ C → KillingConditions.KillAt ρ := by
  first | exact @GlobalTheory.NLink.twist_kills_selmer | exact GlobalTheory.NLink.twist_kills_selmer | (intros; apply GlobalTheory.NLink.twist_kills_selmer <;> assumption)
