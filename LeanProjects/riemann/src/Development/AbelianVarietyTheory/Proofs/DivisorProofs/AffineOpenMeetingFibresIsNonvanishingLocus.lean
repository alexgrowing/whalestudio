import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPreimageSupOfStalkKrullDimLeOneFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusExtendFromBigOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoSmulPicardClassExtendsAbelianSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusPullbackAndVanishIntoLocusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierLocusOverDenseOpenBaseStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AffineLocus

theorem isLocus_of_isAffineOpen_of_meets_fibres : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, IsAffineOpen V → (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) → ∃ c : Pic A.left, IsLocus c V := by
  intro R _ _ _ _ A _ hA V hV hfib
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have hnS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) := GlobalTheory.IsNormalScheme.pred (Sp R)
  obtain ⟨U, c, hU, hc⟩ := GlobalTheory.T.exists_cartier_locus_over_dense_open_base R A hA V hV hfib
  have hVW : V ≤ A.hom ⁻¹ᵁ U ⊔ V := le_sup_right
  have h0 : GlobalTheory.CechPic.pull (A.left.homOfLE hVW) c = 0 := by
    refine GlobalTheory.T.nonvanishingLocus_pullback_and_vanish_into_locus.2 _ _ _ c _ hc fun y => ?_
    show (A.left.homOfLE hVW ≫ (A.hom ⁻¹ᵁ U ⊔ V).ι) y ∈ V
    rw [Scheme.homOfLE_ι]
    exact y.2
  obtain ⟨c', hc'⟩ := GlobalTheory.T.two_smul_picardClass_extends_abelianScheme (Sp R) hnS A hA U V hU hfib c h0
  have h2 : IsLocus (GlobalTheory.CechPic.pull (A.hom ⁻¹ᵁ U ⊔ V).ι c') ((A.hom ⁻¹ᵁ U ⊔ V).ι ⁻¹ᵁ V) := by
    rw [hc', two_nsmul, ← inf_idem ((A.hom ⁻¹ᵁ U ⊔ V).ι ⁻¹ᵁ V)]
    exact hc.add hc
  have : Flat A.hom := inferInstance
  have : GeometricallyIntegral A.hom := GlobalTheory.geometricallyIntegral_of_smooth _
  have hbig := GlobalTheory.T.mem_preimage_sup_of_stalk_krullDim_le_one_flat A.left (Sp R) A.hom V U hfib hU
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : A.left.IsSeparated := by
    have : IsSeparated (terminal.from A.left) := by rw [← terminal.comp_from A.hom]; infer_instance
    exact ⟨this⟩
  have : GlobalTheory.IsNormalScheme A.left := GlobalTheory.isNormalScheme_of_smooth A.hom
  exact ⟨c', GlobalTheory.T.nonvanishingLocus_extend_from_big_open A.left (GlobalTheory.IsNormalScheme.pred _) V _ hV hVW hbig c' h2⟩

end GlobalTheory.AffineLocus
