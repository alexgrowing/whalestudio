import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentTorsionMapSurjective
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
theorem _root_.GlobalTheory.T.cotangent_torsion_map_surjective : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (GG : PDivGroup p R) (θ : TorsionMap G GG) (n : ℕ) (hs : PtSurj θ n), (∀ (M : Type) [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (z z' : TM R M ⟶ G) (h : zeroSec R M ≫ z = η[G]) (h' : zeroSec R M ≫ z' = η[G]), (∀ w, Phi z h w = Phi z' h' w) → z = z') → SpecProp θ n hs → Function.Surjective (cnθ θ n hs) := by
  first | exact @GlobalTheory.OpenOmega.cnθ_surjective | exact GlobalTheory.OpenOmega.cnθ_surjective | (intros; apply GlobalTheory.OpenOmega.cnθ_surjective <;> assumption)
