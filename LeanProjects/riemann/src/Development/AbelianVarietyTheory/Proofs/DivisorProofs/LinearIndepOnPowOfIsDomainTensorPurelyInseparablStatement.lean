import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndepOnPowOfIsDomainTensorPurelyInseparabl
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndepOn_frob_pow_of_isDomain_tensor_insep : ∀ (k B : Type) [Field k] [CommRing B] [IsDomain B] [Algebra k B] (p : ℕ), p.Prime → CharP k p → (∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K → IsDomain (K ⊗[k] B)) → ∀ s : Finset (FractionRing B), LinearIndepOn k _root_.id (s : Set (FractionRing B)) → LinearIndepOn k (· ^ p) (s : Set (FractionRing B)) := by
  first | exact @GlobalTheory.linearIndepOn_pow_of_isDomain_tensor_purelyInseparable | exact GlobalTheory.linearIndepOn_pow_of_isDomain_tensor_purelyInseparable | (intros; apply GlobalTheory.linearIndepOn_pow_of_isDomain_tensor_purelyInseparable <;> assumption)
