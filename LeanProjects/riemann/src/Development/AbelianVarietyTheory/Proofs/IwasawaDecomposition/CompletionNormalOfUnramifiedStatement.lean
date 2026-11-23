import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionNormalOfUnramified
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
open IsLocalRing GlobalTheory.Toroidal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_normal_of_unramified : ∀ (D T : Type) [CommRing D] [IsDomain D] [IsLocalRing D] [IsIntegrallyClosed D] [CharZero D] [Algebra.EssFiniteType ℤ D] [CommRing T] [IsLocalRing T] (h : D →+* T), IsNoetherianRing T → IsLocalHom h → h.Flat → (maximalIdeal D).map h = maximalIdeal T → ((residue T).comp h).Finite → ((residue T).comp h).FormallyUnramified → IsDomain (AdicCompletion (maximalIdeal T) T) ∧ IsIntegrallyClosed (AdicCompletion (maximalIdeal T) T) := by
  first | exact @GlobalTheory.EtaleCompletionCharZero.completion_isDomain_and_isIntegrallyClosed | exact GlobalTheory.EtaleCompletionCharZero.completion_isDomain_and_isIntegrallyClosed | (intros; apply GlobalTheory.EtaleCompletionCharZero.completion_isDomain_and_isIntegrallyClosed <;> assumption)
