import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorRootSubOneLengthLeTameValue
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.LocalRingCardinality.DataNChTie
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conductorRoot_sub_one_length_le_tameValue : ∀ (D : D7) (C : NChoice D), NChTie D C → ∀ i : D.nd.Loc, ∀ v ∈ D.nd.Q i, ((lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i v - 1}) : ℚ) : ℝ) ≤ BlochKatoReduction.Gen.tameVal (D.ntw.l (C.twI (D.nd.w i))) (KillingConditions.psiW C (D.nd.w i)) (D.nd.plOm.1 v) := by
  first | exact @GlobalTheory.CondTieChoice.conductor_le_tameVal | exact GlobalTheory.CondTieChoice.conductor_le_tameVal | (intros; apply GlobalTheory.CondTieChoice.conductor_le_tameVal <;> assumption)
