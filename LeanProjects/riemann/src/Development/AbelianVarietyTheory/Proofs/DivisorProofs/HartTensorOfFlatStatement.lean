import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HartTensorOfFlat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeOver
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hart_baseChange_of_flat : ∀ (A R M O : Type) [CommRing A] [IsNoetherianRing A] [CommRing R] [Algebra A R]
    [AddCommGroup M] [Module R M] [CommRing O] [Algebra R O] [Algebra A O] [IsScalarTower A R O]
    [Module.Flat R O], GlobalTheory.GoodEtale.Hart A R M → GlobalTheory.GoodEtale.Hart A O (O ⊗[R] M) := by
  first | (exact @GlobalTheory.GoodEtale.hart_tensor_of_flat) | (exact GlobalTheory.GoodEtale.hart_tensor_of_flat) | (intros; apply GlobalTheory.GoodEtale.hart_tensor_of_flat  <;> assumption)
