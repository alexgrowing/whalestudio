import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleModelGenericFibre
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
theorem _root_.GlobalTheory.T.card_tors_generic_fibre_eq_pow_mul_height : ∀ (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], ∀ (G₀ : Over (Sp K)) [GrpObj G₀] [IsCommMonObj G₀] (F : G₀.left ⟶ G.left), IsGrpPullback G₀ G (spMap (algebraMap R K)) F → ∀ (GG₀ : PDivGroup p K) (θ₀ : TorsionMap G₀ GG₀), (∀ (n : ℕ) (B : Type) [CommRing B] [Algebra K B], Function.Bijective (θ₀.pt n B)) → ∀ n : ℕ, Nat.card (Tors G (p ^ n) K) = p ^ (n * GG₀.height) := by
  first | exact @GlobalTheory.GroupBplus.Aff.CardTors.card_tors_eq | exact GlobalTheory.GroupBplus.Aff.CardTors.card_tors_eq | (intros; apply GlobalTheory.GroupBplus.Aff.CardTors.card_tors_eq <;> assumption)
