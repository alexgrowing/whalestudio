import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePDivisibleEndomorphism
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
theorem _root_.GlobalTheory.T.exists_unique_p_divisible_endomorphism : ∀ (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (GG : PDivGroup p R) (θ : TorsionMap G GG), IsModel K θ → ∀ f : G ⟶ G, IsMonHom f → ∃! g : GG ⟶ GG, θ.Intertwines f g := by
  first | exact @GlobalTheory.GroupBplus.Aff.existsUnique_intertwines | exact GlobalTheory.GroupBplus.Aff.existsUnique_intertwines | (intros; apply GlobalTheory.GroupBplus.Aff.existsUnique_intertwines <;> assumption)
