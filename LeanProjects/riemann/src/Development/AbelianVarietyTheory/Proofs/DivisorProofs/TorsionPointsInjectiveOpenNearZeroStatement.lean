import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsInjectiveOpenNearZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpOverFstComp
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
open GlobalTheory.SqZeroPt
open scoped GlobalTheory.SqZeroPt
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.OpenOmega

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_points_injective_open_near_zero : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (GG : PDivGroup p R) (θ : TorsionMap G GG), θ.IsOpenNearZero → ∀ n, PtInj θ n := by
  first | exact @GlobalTheory.OpenOmega.ptInj_of_isOpenNearZero | exact GlobalTheory.OpenOmega.ptInj_of_isOpenNearZero | (intros; apply GlobalTheory.OpenOmega.ptInj_of_isOpenNearZero <;> assumption)
