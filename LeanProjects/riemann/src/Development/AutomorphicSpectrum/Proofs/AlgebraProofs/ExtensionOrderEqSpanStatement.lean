import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExtensionOrderEqSpan
import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extension_order_eq_span : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (R' : Type) [CommRing R'] (φ : R →+* R') (A : Subalgebra R (T → R)) (g : T → R'), g ∈ extOrder φ A ↔ g ∈ Submodule.span R' {g : T → R' | ∃ f ∈ A, g = fun t => φ (f t)} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.ExtSpan.extOrder_eq_span | exact GlobalTheory.CompanionTheory.Ar.BT.ExtSpan.extOrder_eq_span | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.ExtSpan.extOrder_eq_span <;> assumption)
