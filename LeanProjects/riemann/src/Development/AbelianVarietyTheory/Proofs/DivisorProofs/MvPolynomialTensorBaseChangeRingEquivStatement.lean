import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPolynomialTensorBaseChangeRingEquiv
import Mathlib
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPolynomial_tensor_baseChange_ringEquiv' : ∀ (S B K τ : Type) [CommRing S] [CommRing B] [CommRing K] [Algebra S B] [Algebra S K] [Algebra (MvPolynomial τ S) K] [IsScalarTower S (MvPolynomial τ S) K], letI : Algebra (MvPolynomial τ S) (MvPolynomial τ B) := (MvPolynomial.map (algebraMap S B)).toAlgebra; Nonempty (MvPolynomial τ B ⊗[MvPolynomial τ S] K ≃+* B ⊗[S] K) := by
  first | exact @GlobalTheory.mvPolynomial_tensor_baseChange_ringEquiv | exact GlobalTheory.mvPolynomial_tensor_baseChange_ringEquiv | (intros; apply GlobalTheory.mvPolynomial_tensor_baseChange_ringEquiv <;> assumption)
