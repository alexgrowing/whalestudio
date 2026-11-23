import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderInductionId
import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hopf_order_induction_id : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (A : Subalgebra R (T → R)), IsHopfOrder A → indOrder (MonoidHom.id T) A = A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.indOrder_id_eq_of_isHopfOrder | exact GlobalTheory.CompanionTheory.Ar.BT.indOrder_id_eq_of_isHopfOrder | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.indOrder_id_eq_of_isHopfOrder <;> assumption)
