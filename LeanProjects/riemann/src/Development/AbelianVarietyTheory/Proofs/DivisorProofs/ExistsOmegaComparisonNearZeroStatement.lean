import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOmegaComparisonNearZero
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
theorem _root_.GlobalTheory.T.exists_omega_comparison_near_zero : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [CharZero R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (GG : PDivGroup p R) (θ : TorsionMap G GG), θ.IsOpenNearZero → ∃ c : Pdiv.omega G →ₗ[R] GG.omega, θ.IsOmega c := by
  first | exact @GlobalTheory.OpenOmega.exists_isOmega_of_isOpenNearZero | exact GlobalTheory.OpenOmega.exists_isOmega_of_isOpenNearZero | (intros; apply GlobalTheory.OpenOmega.exists_isOmega_of_isOpenNearZero <;> assumption)
