import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualityTensorPairingCompat
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
theorem _root_.GlobalTheory.T.exists_map_one_tmul_cartierDual_eq_one_tmul : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (A : Type) [CommRing A] [HopfAlgebra R A] [IsCocomm R A] [Module.Finite R A] [Module.Projective R A] (F : K ⊗[R] CartierDual R A →ₗ[K] K ⊗[R] A) (T : A ⊗[R] A), (∀ s s' : A →ₐ[R] R, algebraMap R K (Algebra.TensorProduct.lift s s' (fun _ _ => .all _ _) T) = Algebra.TensorProduct.lift (AlgHom.id K K) ((Algebra.ofId R K).comp s') (fun _ _ => .all _ _) (F ((1 : K) ⊗ₜ[R] (toConv s.toLinearMap : CartierDual R A)))) → ∀ l : CartierDual R A, ∃ a : A, F ((1 : K) ⊗ₜ[R] l) = (1 : K) ⊗ₜ[R] a := by
  first | exact @GlobalTheory.HopfPoints.integral_of_integral_tensor | exact GlobalTheory.HopfPoints.integral_of_integral_tensor | (intros; apply GlobalTheory.HopfPoints.integral_of_integral_tensor <;> assumption)
