import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVGenericFibreOfTriple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalBundleOfSymmetricSemiAbelian
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalNormalPrime
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalNormalDomain
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionOfPolarisedGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianGenericFibrePolarizationIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonzeroOnClosedFibreCompleteLocalStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.LN

noncomputable section
namespace GlobalTheory.ThetaNormal

theorem thetaNZ_of_polAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.admitted R (IsLocalRing.maximalIdeal R) → ∀ (t : SAB H (Sp R)), GlobalTheory.LN.PolAt t (jK R) → GlobalTheory.LN.SplitOver t.G (IsLocalRing.maximalIdeal R) → GlobalTheory.LN.ThetaNZ t.G t.PP.L := by
  intro E _ _ _ H R _ _ _ hA t hpol hs
  obtain ⟨h1, h2, -⟩ := GlobalTheory.allSixLaws
  obtain ⟨A, -, gen, hgen, hL, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt h1 h2 E H R t hpol
  have := hA.1.1
  obtain ⟨P, hPL, -⟩ := GlobalTheory.UU.exists_cp_of_isSymmetric h1 R A t.G t.semi gen hgen t.PP t.cub t.sym
  have hσ : ∃ (σ : LB.Sec P.L.L) (k : P.L.L.ι), σ.f k ≠ 0 := by
    rw [hPL]; exact GlobalTheory.T.exists_nonzero_section_of_polarised_generic_fibre E H R t hpol
  obtain ⟨D, U, hUL, -⟩ := GlobalTheory.T.semiabelian_generic_fibre_polarization_iso R hA t.G P t.semi (hPL ▸ GlobalTheory.LN.UnifPrime.hypW_of_triple t) hs A gen hgen
    (hPL ▸ hL) hσ
  have key := GlobalTheory.T.exists_section_nonzero_on_closed_fibre_complete_local R hA.1.1 hA.1.2.2.1 hA.2.1 hA.2.2.1 D A t.G t.semi U
  rw [hUL, hPL] at key
  have := t.semi.smooth
  exact GlobalTheory.UnifNormal.thetaNZ_of_closedPoint t.G _ key

end GlobalTheory.ThetaNormal
end
