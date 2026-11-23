import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPreimageSupOfStalkKrullDimLeOneFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatPreimageContainsCodimLeOnePointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardExtendOfLocallyTrivialNormalCodimTwoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardClassLocallyTrivialOfTrivialSmoothNormalCoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardTwoNsmulPullbackEqZeroOnTripleParameteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParameterSchemeTriplesAbelianSchemeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DoubleClassExtension

theorem two_smul_extends : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : S.Opens) (V : A.left.Opens), (U : Set S).Nonempty → (∀ s : S, ∃ x ∈ V, A.hom x = s) → ∀ c : Pic (A.hom ⁻¹ᵁ U ⊔ V).toScheme, GlobalTheory.CechPic.pull (A.left.homOfLE (le_sup_right : V ≤ A.hom ⁻¹ᵁ U ⊔ V)) c = 0 → ∃ c' : Pic A.left, GlobalTheory.CechPic.pull (A.hom ⁻¹ᵁ U ⊔ V).ι c' = 2 • c := by
  intro S _ _ hS A _ hA U V hU hV c hc
  haveI : Smooth A.hom := hA.smooth
  haveI : GeometricallyConnected A.hom := hA.geomConnected
  haveI : GeometricallyIntegral A.hom := GlobalTheory.geometricallyIntegral_of_smooth A.hom
  haveI : GlobalTheory.IsNormalScheme S := GlobalTheory.IsNormalScheme.of_pred hS
  haveI : GlobalTheory.IsNormalScheme A.left := GlobalTheory.isNormalScheme_of_smooth A.hom
  haveI : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have hbig := GlobalTheory.T.mem_preimage_sup_of_stalk_krullDim_le_one_flat A.left S A.hom V U hV hU
  obtain ⟨Y, x, a, v, p, e, _, hxs, hxsurj, hpv, hmem, hsm2, hgi2, he⟩ := GlobalTheory.T.exists_parameterScheme_triples_abelianScheme S A hA V hV
  haveI := hxs
  haveI := hxsurj
  have h2 := GlobalTheory.T.cechPicard_two_nsmul_pullback_eq_zero_on_tripleParameterScheme S hS A hA U V (A.hom ⁻¹ᵁ U ⊔ V) le_sup_right hU hV le_sup_left le_rfl c hc
    Y x a v p e hpv hmem hsm2 hgi2 he
  haveI : GlobalTheory.IsNormalScheme Y.left := GlobalTheory.isNormalScheme_of_smooth x.left
  have hbigY := GlobalTheory.T.flat_preimage_contains_codim_le_one_points A.left Y.left x.left _ hbig
  have hloc := GlobalTheory.T.picardClass_locally_trivial_of_trivial_smooth_normal_cover A.left Y.left x.left (GlobalTheory.IsNormalScheme.pred _) _ hbigY (2 • c) h2
  exact GlobalTheory.T.cechPicard_extend_of_locally_trivial_normal_codimTwo A.left (GlobalTheory.IsNormalScheme.pred _) _ hbig (2 • c) hloc

end GlobalTheory.DoubleClassExtension
