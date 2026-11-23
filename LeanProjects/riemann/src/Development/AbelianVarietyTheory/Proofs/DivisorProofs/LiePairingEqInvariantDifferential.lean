import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpOverFstComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSurjectiveOntoDual
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

namespace GlobalTheory.OpenOmega

theorem phi_tangent_eq_toOmega : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [QuasiSeparated G.hom] (x : Pdiv.LieG G) (h : zeroSec R R ≫ x.1 = η[G]) (w : Wmod G), Phi x.1 h w = (GlobalTheory.LieVB.toOmega G w).1 x :=
  fun R _ _ _ _ _ _ _ => GlobalTheory.SqZeroPt.kappa_eq_epsIso R _

end GlobalTheory.OpenOmega
