import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSectionNonvanishingClosedFibre
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecCarried
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_section_nonvanishing_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β), ∀ θ : U'.LG.L.Sec, (∃ g' : G'.left, G'.hom g' = closedPoint R' ∧ g' ∈ secNz θ) → ∃ O : G.left.Opens, (∃ g ∈ O, G.hom g = closedPoint R) ∧ ∀ g' : G'.left, β g' ∈ O → G.hom (β g') = closedPoint R → g' ∈ secNz θ := by
  first | exact @GlobalTheory.Mum.exists_open_secNz_closedFibre | exact GlobalTheory.Mum.exists_open_secNz_closedFibre | (intros; apply GlobalTheory.Mum.exists_open_secNz_closedFibre <;> assumption)
