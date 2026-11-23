import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderScalarExtension
import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hopf_order_scalar_extension : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (A : Subalgebra R (T → R)), IsHopfOrder A → (∃ d : R, algebraMap R R' d ≠ 0 ∧ ∀ f : T → R, d • f ∈ A) → IsHopfOrder (extOrder (algebraMap R R') A) ∧ ∃ e : R' ⊗[R] A ≃ₐ[R'] extOrder (algebraMap R R') A, ∀ (a : A) (t : T), (e (1 ⊗ₜ a)).1 t = algebraMap R R' (a.1 t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.ext_tensor_base_change | exact GlobalTheory.CompanionTheory.Ar.BT.ext_tensor_base_change | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.ext_tensor_base_change <;> assumption)
