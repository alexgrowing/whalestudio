import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.LineBundleSpreadsOutStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.AbelianSchemeSpreadsOutFiniteTypeSubringImports
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem exists_model_abelian_lb : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → ∀ L : LB A.left, L.IsLB →
      ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (φ : A.left ⟶ B.left) (M : LB B.left),
        Algebra.FiniteType ℤ S ∧ IsAbelianScheme B ∧ IsGrpPullback A B (spMap S.subtype) φ ∧
          M.IsLB ∧ LBIso L (M.pull φ) := by
  intro R _ A _ hA L hL
  obtain ⟨S0, B, gB, φ, -, hft, hB, hpb⟩ := GlobalTheory.T.abelianScheme_spreads_out_finiteType_subring R A ∅ hA
  have hpb' : IsGrpPullback A B (spMap (algebraMap S0 R)) φ := hpb
  haveI : IsProper B.hom := IsAbelianScheme.proper (A := B)
  have hqc : QuasiCompact B.hom := inferInstance
  have hsep : IsSeparated B.hom := inferInstance
  obtain ⟨R', hR', M, hM, hσ⟩ :=
    GlobalTheory.T.line_bundle_spreads_out S0 R B.left A.left B.hom A.hom φ hqc hsep hpb'.1 L hL
  obtain ⟨gB', φ₁, hB'B, hAB', hφ₁⟩ := GlobalTheory.T.abelianScheme_model_baseChange_subalgebra S0 R A B φ hpb' R'
  refine ⟨R'.toSubring, Over.mk (pullback.snd B.hom (spMap (algebraMap S0 R'))), gB', φ₁, M,
    ?_, ?_, hAB', hM, ?_⟩
  · have h1 : Algebra.FiniteType S0 R' := (Subalgebra.fg_iff_finiteType R').mp hR'
    have h2 : Algebra.FiniteType ℤ R' := Algebra.FiniteType.trans hft h1
    exact h2
  · exact GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB hB'B
  · exact hσ φ₁ hφ₁ hAB'.1.w

end GlobalTheory.CompanionTheory.Ar.Approx
