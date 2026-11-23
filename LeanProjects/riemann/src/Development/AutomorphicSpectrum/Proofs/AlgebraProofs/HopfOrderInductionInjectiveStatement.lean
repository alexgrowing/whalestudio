import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderInductionInjective
import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hopf_order_induction_injective : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (H : Type) [CommGroup H] (ι : H →* T), Function.Injective ι → ∀ A : Subalgebra R (H → R), IsHopfOrder A → IsHopfOrder (indOrder ι A) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.Induced.isHopfOrder_indOrder | exact GlobalTheory.CompanionTheory.Ar.BT.Induced.isHopfOrder_indOrder | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.Induced.isHopfOrder_indOrder <;> assumption)
