import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndRelDimOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeTorusCompare
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SplitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureCohomologyResidueFieldFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSpecialFibreCohomologyLiftArtinianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFunctionsConstantAfterBaseChangeOfAbelianSStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgePropertyFromFibresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupSelfZeroAbelianH1Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyStructureSheafCohomologyAnyFieldStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AbCohRing

theorem rankAtStalk_eq_finrank_residueField {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (p : PrimeSpectrum R) :
    Module.rankAtStalk M p = Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M) := by
  rw [Module.rankAtStalk_eq_finrank_tensorProduct]
  haveI : Module.Free (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⊗[R] M) :=
    Module.free_of_flat_of_isLocalRing
  have e := (AlgebraTensorModule.cancelBaseChange R (Localization.AtPrime p.asIdeal)
    p.asIdeal.ResidueField p.asIdeal.ResidueField M)
  rw [← e.finrank_eq]
  exact (Module.finrank_baseChange (S := Localization.AtPrime p.asIdeal) (R := p.asIdeal.ResidueField)
    (M' := Localization.AtPrime p.asIdeal ⊗[R] M)).symm

theorem exists_grpObj_of_isPullback {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R')
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) {X' : Scheme.{0}} (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left)
    (h : IsPullback φ s' A.hom (spMap f)) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) :
    ∃ _ : GrpObj (Over.mk s'), IsAbelianScheme (Over.mk s') ∧ SmoothOfRelativeDimension g s' := by
  letI : GrpObj ((Over.pullback (spMap f)).obj A) := Functor.grpObjObj
  have hP := isGrpPullback_pullback A (spMap f)
  obtain ⟨hPA, -⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback f A
    ((Over.pullback (spMap f)).obj A) (pullback.fst A.hom (spMap f)) g hP hA hg
  let e : Over.mk s' ≅ (Over.pullback (spMap f)).obj A := Over.isoMk h.isoPullback (by simp)
  letI gr : GrpObj (Over.mk s') := GrpObj.ofIso e.symm
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
  refine ⟨gr, GlobalTheory.Compare.AbelianSchemeTorusCompare.isAbelianScheme_of_iso e ?_ hPA,
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) h hg⟩
  haveI : IsMonHom e.symm.hom := inferInstance
  exact isMonHom_inv_of_iso e.symm

end GlobalTheory.AbCohRing

namespace GlobalTheory.AbCohRing

theorem fp_and_bc (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    (Module.Finite R (HO1 A.hom) ∧ Module.Projective R (HO1 A.hom)) ∧
      (Module.Finite R (HO2 A.hom) ∧ Module.Projective R (HO2 A.hom)) ∧ StructureSheafH1BaseChange A.hom ∧ StructureSheafH2BaseChange A.hom := by
  have := hA.proper
  have := hA.smooth
  refine GlobalTheory.T.structure_cohomology_residue_field_fibre R A.left A.hom inferInstance inferInstance (GlobalTheory.T.globalFunctionsConstantAfterBaseChange_of_abelianScheme R A hA) ?_
  intro R' _ _ _ _ k _ _ α hα X' s' φ X₀ s₀ ψ hφ w
  obtain ⟨_, hA', hg'⟩ := exists_grpObj_of_isPullback (algebraMap R R') A g s' φ hφ hA hg
  exact GlobalTheory.T.abelianSchemeSpecialFibre_cohomology_lift_artinian R' (Over.mk s') g hA' hg' k α hα X₀ s₀ ψ w

theorem rankAtStalk_HO1 (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) [Module.Finite R (HO1 A.hom)]
    [Module.Projective R (HO1 A.hom)] (hb : StructureSheafH1BaseChange A.hom) (p : PrimeSpectrum R) :
    Module.rankAtStalk (HO1 A.hom) p = g := by
  let κ := p.asIdeal.ResidueField
  have hpb := IsPullback.of_hasPullback A.hom (spMap (algebraMap R κ))
  obtain ⟨e, -⟩ := hb κ _ _ _ hpb
  obtain ⟨_, hA', hg'⟩ := exists_grpObj_of_isPullback (algebraMap R κ) A g _ _ hpb hA hg
  have hκ := (GlobalTheory.T.abelianVariety_structureSheaf_cohomology_anyField κ _ g hA' hg').2.1
  rw [rankAtStalk_eq_finrank_residueField, ← hκ]
  exact e.finrank_eq

theorem oStr_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    FP R (HO1 A.hom) g ∧ WedgeO (OAff A.hom) ∧ StructureSheafH1BaseChange A.hom ∧ StructureSheafH2BaseChange A.hom := by
  intro R _ _ A _ g hA hg
  obtain ⟨⟨h1f, h1p⟩, ⟨h2f, h2p⟩, hb1, hb2⟩ := fp_and_bc R A g hA hg
  refine ⟨⟨h1f, h1p, rankAtStalk_HO1 R A g hA hg hb1⟩, ?_, hb1, hb2⟩
  refine GlobalTheory.T.wedge_property_from_fibres R A.left A.hom h1f h1p h2f h2p hb1 hb2 (GlobalTheory.T.cup_self_zero_abelian_h1 R A g hA hg) ?_
  intro k _ _ X' s' φ h
  obtain ⟨_, hA', hg'⟩ := exists_grpObj_of_isPullback (algebraMap R k) A g s' φ h hA hg
  exact (GlobalTheory.T.abelianVariety_structureSheaf_cohomology_anyField k (Over.mk s') g hA' hg').2.2.1

end GlobalTheory.AbCohRing
