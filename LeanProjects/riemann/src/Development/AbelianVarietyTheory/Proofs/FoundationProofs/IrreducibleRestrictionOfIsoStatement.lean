import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IrreducibleRestrictionOfIso
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_restriction_of_iso : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (l : ℕ) [Fact l.Prime] (W W' : R2 Ω l), RepIso W W' → IsIrr (W.comp (H0g W).subtype) → IsIrr (W'.comp (H0g W').subtype) := by
  first | exact @GlobalTheory.IrrConj.irr_of_repIso | exact GlobalTheory.IrrConj.irr_of_repIso | (intros; apply GlobalTheory.IrrConj.irr_of_repIso <;> assumption)
