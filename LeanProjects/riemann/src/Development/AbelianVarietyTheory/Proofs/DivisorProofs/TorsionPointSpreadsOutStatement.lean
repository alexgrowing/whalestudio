import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointSpreadsOut
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
theorem _root_.GlobalTheory.T.torsion_point_spreads_out : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → ∀ (k : Type) [Field k] [Algebra R k] (z : Tors G N k), ∃ (r : R) (ψ : Localization.Away r →ₐ[R] k) (z' : Tors G N (Localization.Away r)), torsMap ψ z' = z := by
  first | exact @GlobalTheory.GroupBplus.Aff.exists_tors_lift_away | exact GlobalTheory.GroupBplus.Aff.exists_tors_lift_away | (intros; apply GlobalTheory.GroupBplus.Aff.exists_tors_lift_away <;> assumption)
