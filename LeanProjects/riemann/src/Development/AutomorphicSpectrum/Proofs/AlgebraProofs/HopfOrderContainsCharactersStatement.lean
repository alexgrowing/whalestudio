import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderContainsCharacters
import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hopf_order_contains_characters : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] [IsIntegrallyClosed R] (A : Subalgebra R (T → R)), IsHopfOrder A → ∀ χ : T →* Rˣ, (fun t => ((χ t : Rˣ) : R)) ∈ A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.char_mem_hopfOrder | exact GlobalTheory.CompanionTheory.Ar.BT.char_mem_hopfOrder | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.char_mem_hopfOrder <;> assumption)
