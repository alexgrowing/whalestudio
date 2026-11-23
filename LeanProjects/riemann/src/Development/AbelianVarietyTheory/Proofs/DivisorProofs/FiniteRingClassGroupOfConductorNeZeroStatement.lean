import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZero
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_ringClassGroup_of_conductor_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → Finite (PicO c) := by
  first | exact @GlobalTheory.CMVal.PicFin.finite_picO | exact GlobalTheory.CMVal.PicFin.finite_picO | (intros; apply GlobalTheory.CMVal.PicFin.finite_picO <;> assumption)
