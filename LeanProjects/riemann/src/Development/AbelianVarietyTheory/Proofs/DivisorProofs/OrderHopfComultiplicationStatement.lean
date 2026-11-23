import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderHopfComultiplication
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
theorem _root_.GlobalTheory.T.order_hopf_comultiplication : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (M : Type) [CommGroup M] [Finite M] (O : Subalgebra R (M → K)), Module.Finite R O → Module.Projective R O → (∀ f : M → K, ∃ r : R, r ≠ 0 ∧ r • f ∈ O) → (∀ f ∈ O, ∃ T : O ⊗[R] O, ∀ a b : M, Algebra.TensorProduct.lift ((Pi.evalAlgHom R (fun _ : M => K) a).comp O.val) ((Pi.evalAlgHom R (fun _ : M => K) b).comp O.val) (fun _ _ => .all _ _) T = f (a * b)) → (∀ f ∈ O, (fun a => f a⁻¹) ∈ O) → (∀ f ∈ O, ∃ c : R, algebraMap R K c = f 1) → ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra R A) (_ : IsCocomm R A) (io : A ≃ₐ[R] O), ∀ a b : M, toConv (((Pi.evalAlgHom R (fun _ : M => K) (a * b)).comp O.val).comp io.toAlgHom) = toConv (((Pi.evalAlgHom R (fun _ : M => K) a).comp O.val).comp io.toAlgHom) * toConv (((Pi.evalAlgHom R (fun _ : M => K) b).comp O.val).comp io.toAlgHom) := by
  first | exact @GlobalTheory.HopfFn.exists_hopfAlgebra_of_subalgebra_fun | exact GlobalTheory.HopfFn.exists_hopfAlgebra_of_subalgebra_fun | (intros; apply GlobalTheory.HopfFn.exists_hopfAlgebra_of_subalgebra_fun <;> assumption)
