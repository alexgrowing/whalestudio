import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionOrderComultiplication
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
theorem _root_.GlobalTheory.T.torsion_order_comultiplication : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → (∀ f ∈ ord G N K, ∃ T : ord G N K ⊗[R] ord G N K, ∀ a b : Tors G N K, Algebra.TensorProduct.lift ((Pi.evalAlgHom R (fun _ : Tors G N K => K) a).comp (ord G N K).val) ((Pi.evalAlgHom R (fun _ : Tors G N K => K) b).comp (ord G N K).val) (fun _ _ => .all _ _) T = f (a * b)) ∧ (∀ f ∈ ord G N K, (fun a => f a⁻¹) ∈ ord G N K) ∧ ∀ f ∈ ord G N K, ∃ c : R, algebraMap R K c = f 1 := by
  first | exact @GlobalTheory.GroupBplus.Aff.ord_hopf_closed | exact GlobalTheory.GroupBplus.Aff.ord_hopf_closed | (intros; apply GlobalTheory.GroupBplus.Aff.ord_hopf_closed <;> assumption)
