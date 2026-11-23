import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdDualGeneratorPairingModPowNondegenerate
import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DvdOfMemIk
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

theorem _root_.GlobalTheory.T.ordDualGeneratorPairing_modPow_nondegenerate : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ) (b : Qn c n), (∀ a : Qn c n, GlobalTheory.Ord2.SelPerp.tbA c n (a * b) = 0) → b = 0 := by
  first | exact @GlobalTheory.Ord2.SelPerp.pair_nondeg | exact GlobalTheory.Ord2.SelPerp.pair_nondeg | (intros; apply GlobalTheory.Ord2.SelPerp.pair_nondeg <;> assumption) | exact @GlobalTheory.Ord2.SelPerp.tau_mul_dvd | exact GlobalTheory.Ord2.SelPerp.tau_mul_dvd | (intros; apply GlobalTheory.Ord2.SelPerp.tau_mul_dvd <;> assumption)
