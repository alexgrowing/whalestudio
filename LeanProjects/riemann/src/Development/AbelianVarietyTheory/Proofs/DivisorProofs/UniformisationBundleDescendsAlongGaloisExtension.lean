import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedGenericFibreDescendsGaloisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationLineBundleDescendsGaloisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalStructureDescendedLineBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricOfGaloisPullbackUniformisationBundleStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalBundleOfSymmetricSemiAbelian
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GaloisPackageDescent

theorem exists_cp : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∃ P : GlobalTheory.UU.CP G, LBIso U'.LG.L (P.L.L.pull β) := by
  intro R _ _ _ hR R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hinv
  obtain ⟨L, hL, hLi⟩ := GlobalTheory.T.uniformisation_lineBundle_descends_galois R hR R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hinv
  obtain ⟨rig, hrig⟩ := ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_isLB_local (V := R) (L.pull (eSec G))
    (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB L hL _ _)
  obtain ⟨c⟩ := GlobalTheory.T.exists_cubicalStructure_descendedLineBundle R hR R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hinv L hL hLi rig hrig
  have hsym := GlobalTheory.T.isSymmetric_of_galoisPullback_uniformisationBundle R hR R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hinv L hL hLi rig hrig
  obtain ⟨A, gen, κ, hgen, -, -⟩ := GlobalTheory.T.polarised_generic_fibre_descends_galois R hR R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hinv
  have : IsNoetherianRing R := hR.1.1
  obtain ⟨hLaws, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨P, hP, -⟩ := GlobalTheory.UU.exists_cp_of_isSymmetric hLaws R A G hS gen hgen ⟨L, rig, hL, hrig⟩ c hsym
  refine ⟨P, ?_⟩
  rw [hP]
  exact hLi

end GlobalTheory.GaloisPackageDescent
