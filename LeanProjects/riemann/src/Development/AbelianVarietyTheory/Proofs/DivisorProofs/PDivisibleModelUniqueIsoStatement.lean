import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleModelUniqueIso
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
theorem _root_.GlobalTheory.T.p_divisible_model_unique_iso : ∀ (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (G₀ : Over (Sp K)) [GrpObj G₀] [IsCommMonObj G₀] (F : G₀.left ⟶ G.left), IsGrpPullback G₀ G (spMap (algebraMap R K)) F → ∀ (GG : PDivGroup p R) (θ : TorsionMap G GG), IsModel K θ → ∀ (GG₀ : PDivGroup p K) (θ₀ : TorsionMap G₀ GG₀), (∀ (n : ℕ) (B : Type) [CommRing B] [Algebra K B], Function.Bijective (θ₀.pt n B)) → ∃ e : GG₀ ≅ GG.baseChange K, GenCompat F θ θ₀ e := by
  first | exact @GlobalTheory.GroupBplus.Aff.GenIso.model_generic_iso | exact GlobalTheory.GroupBplus.Aff.GenIso.model_generic_iso | (intros; apply GlobalTheory.GroupBplus.Aff.GenIso.model_generic_iso <;> assumption)
