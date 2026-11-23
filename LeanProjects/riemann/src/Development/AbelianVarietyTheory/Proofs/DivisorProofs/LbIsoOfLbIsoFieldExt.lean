import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedAVIsoDescendsOfRationalThreeTorsion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UCanon.lbIso_of_lbIso_fieldExt : ∀ (k₀ K : Type) [Field k₀] [Field K] (i₀ : k₀ →+* K) (B : Over (Sp k₀)) [GrpObj B], IsAbelianScheme B → ∀ L L' : LB B.left, L.IsLB → L'.IsLB → LBIso (L.pull (pullback.fst B.hom (spMap i₀))) (L'.pull (pullback.fst B.hom (spMap i₀))) → LBIso L L' := by
  intro k₀ K _ _ i₀ B _ hB L L' hL hL' h
  exact GlobalTheory.PolIsoDescent.lbIso_descend GlobalTheory.globalFns_holds (spMap i₀) B hB hL hL' h
