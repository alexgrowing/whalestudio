import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeFieldStrictlyHenselian
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sH_of_isField_finiteType_of_isAlgClosed : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B], IsField B → SH B := by
  first | (exact @GlobalTheory.field_finiteType_algClosed_SH) | (exact GlobalTheory.field_finiteType_algClosed_SH) | (intros; apply GlobalTheory.field_finiteType_algClosed_SH  <;> assumption)
