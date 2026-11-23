import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeConjugation_properties_cmField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : Pl E, Continuous (cj w) ∧ (∀ x, cj w (cj w x) = x) ∧ (∀ x, Valued.v (cj w x) = Valued.v x) ∧ (¬ IsSplitAt w → (∀ x : E, cj w (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧ (∃ ϖ q, IsUnramInv ϖ (cj w) q ∧ qV E w = q ^ 2) ∧ (∀ x : Af E, pLoc E w (conjFin (IsCMField.complexConj E).toRingEquiv x) = cj w (pLoc E w x)) ∧ ∀ (s : w.adicCompletion E →+* w.adicCompletion E), (∀ x, Valued.v (s x) = Valued.v x) → (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → s = cj w) ∧ ∀ (s : w.adicCompletion E →+* w.adicCompletion E), (∀ x, Valued.v (s x) = Valued.v x) → (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → ¬ IsSplitAt w := by
  first | exact @GlobalTheory.ConjAtPlace.main | exact GlobalTheory.ConjAtPlace.main | (intros; apply GlobalTheory.ConjAtPlace.main <;> assumption)
