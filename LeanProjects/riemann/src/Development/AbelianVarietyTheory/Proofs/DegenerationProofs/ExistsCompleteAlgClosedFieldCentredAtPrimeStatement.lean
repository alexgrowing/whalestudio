import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteAlgClosedFieldCentredAtPrime

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complete_algClosed_field_centred_at_prime : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [FaithfulSMul R K] [Algebra.IsAlgebraic R K] (P : Ideal R), P.IsPrime → P ≠ ⊥ → ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (gam : K →+* C), (∀ r, ‖gam (algebraMap R K r)‖ ≤ 1) ∧ ∀ r ∈ P, ‖gam (algebraMap R K r)‖ < 1 := by
  first | exact @GlobalTheory.Ex.exists_complete_isAlgClosed_centred_at_prime | exact GlobalTheory.Ex.exists_complete_isAlgClosed_centred_at_prime | (intros; apply GlobalTheory.Ex.exists_complete_isAlgClosed_centred_at_prime <;> assumption)
