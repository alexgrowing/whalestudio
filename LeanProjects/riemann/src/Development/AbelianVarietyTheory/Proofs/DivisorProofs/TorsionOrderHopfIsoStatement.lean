import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionOrderHopfIso
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
theorem _root_.GlobalTheory.T.torsion_order_hopf_iso : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → ∀ (A : Type) [CommRing A] [HopfAlgebra R A] (io : A ≃ₐ[R] ord G N K), (∀ a b : Tors G N K, toConv (((Pi.evalAlgHom R (fun _ : Tors G N K => K) (a * b)).comp (ord G N K).val).comp io.toAlgHom) = toConv (((Pi.evalAlgHom R (fun _ : Tors G N K => K) a).comp (ord G N K).val).comp io.toAlgHom) * toConv (((Pi.evalAlgHom R (fun _ : Tors G N K => K) b).comp (ord G N K).val).comp io.toAlgHom)) → ∃ θ : TorsPt G N A, ∀ (x : Tors G N K) (a : A), θ.pt K x a = (io a : Tors G N K → K) x := by
  first | exact @GlobalTheory.GroupBplus.Aff.exists_torsPt_of_ord | exact GlobalTheory.GroupBplus.Aff.exists_torsPt_of_ord | (intros; apply GlobalTheory.GroupBplus.Aff.exists_torsPt_of_ord <;> assumption)
