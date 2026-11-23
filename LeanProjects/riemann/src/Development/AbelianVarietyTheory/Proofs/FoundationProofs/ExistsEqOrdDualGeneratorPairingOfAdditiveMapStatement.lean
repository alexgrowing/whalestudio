import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqOrdDualGeneratorPairingOfAdditiveMap
import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DvdOfMemIk
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_eq_ordDualGeneratorPairing_of_additiveMap : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ) (φ : Qn c n →+ ZMod (l ^ n)), ∃ b : Qn c n, ∀ a : Qn c n, φ a = GlobalTheory.Ord2.SelPerp.tbA c n (a * b) := by
  first | exact @GlobalTheory.Ord2.SelPerp.exists_eq_tbA_mul | exact GlobalTheory.Ord2.SelPerp.exists_eq_tbA_mul | (intros; apply GlobalTheory.Ord2.SelPerp.exists_eq_tbA_mul <;> assumption) | exact @GlobalTheory.Ord2.SelPerp.coef_free_pairSurj | exact GlobalTheory.Ord2.SelPerp.coef_free_pairSurj | (intros; apply GlobalTheory.Ord2.SelPerp.coef_free_pairSurj <;> assumption)
