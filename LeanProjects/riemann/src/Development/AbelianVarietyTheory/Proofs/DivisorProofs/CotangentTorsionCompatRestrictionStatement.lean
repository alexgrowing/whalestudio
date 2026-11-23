import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentTorsionCompatRestriction
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
theorem _root_.GlobalTheory.T.cotangent_torsion_compat_restriction : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (GG : PDivGroup p R) (θ : TorsionMap G GG) (n : ℕ) (hs : PtSurj θ n) (hs' : PtSurj θ (n + 1)), SpecProp θ (n + 1) hs' → ∀ w : Wmod G, cotMap (GG.res n) (cnθ θ (n + 1) hs' w) = cnθ θ n hs w := by
  first | exact @GlobalTheory.OpenOmega.cotMap_res_cnθ | exact GlobalTheory.OpenOmega.cotMap_res_cnθ | (intros; apply GlobalTheory.OpenOmega.cotMap_res_cnθ <;> assumption)
