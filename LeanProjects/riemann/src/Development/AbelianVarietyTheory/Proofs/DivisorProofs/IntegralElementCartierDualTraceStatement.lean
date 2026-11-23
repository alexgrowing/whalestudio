import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralElementCartierDualTrace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_element_cartier_dual_trace : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (H : Type) [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [FiniteDimensional K H] (F : CartierDual K H →ₐc[K] H) (Λ : CartierDual K H) (y : K), (∀ d : CartierDual K H, d * Λ = algebraMap K _ (Coalgebra.counit (R := K) d) * Λ) → Coalgebra.counit (R := K) Λ = y → y ^ 2 = (Nat.card (H →ₐ[K] K) : K) → Function.Injective F → ∀ a : H, F (toConv (Λ.ofConv ∘ₗ LinearMap.mulLeft K ((CartierDual.bidual K H).symm (CartierDual.map F (toConv (Λ.ofConv ∘ₗ LinearMap.mulLeft K (HopfAlgebra.antipode K a))))))) = a := by
  first | exact @GlobalTheory.FourierInv.inversion_field | exact GlobalTheory.FourierInv.inversion_field | (intros; apply GlobalTheory.FourierInv.inversion_field <;> assumption)
