import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracMapAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedMemRangeFractionFieldMapGaloisInvariantsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionFieldMapFiniteOfFiniteInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackGenericFibreFractionFieldMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleGaloisDescentAbelianVarietyFinitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisConjugateGenericBundleIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedSymmetricOfSymmetricFieldExtensionPullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarisationOfGroupSchemeIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianOfFieldExtensionPullbackProperStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.GenDesc

open GlobalTheory.Mum

theorem polarisedGeneric : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∃ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A) (κ : pullback G'.hom (jK R') ⟶ pullback G.hom (jK R)), IsMonHom gen.hom ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β ∧ LBIso (U'.LG.L.pull (pullback.fst G'.hom (jK R'))) (A.L.pull (κ ≫ gen.hom.left)) := by
  intro R _ _ _ _ R' _ _ _ ρ hfin hgal D D' hD A' G' _ _ _ U' a G _ _ β hG hpb hinv
  have hρ : Function.Injective ρ := hfin.2.1
  haveI := hgal.1
  have hκ := GlobalTheory.T.isGrpPullback_genericFibre_fractionFieldMap R R' ρ hρ G' G β hpb
  let L' := U'.LG.L.pull (pullback.fst G'.hom (jK R'))
  have hL' : L'.IsLB := pull_isLB U'.LG.isLB _
  have hiso : LBIso L' (A'.L.pull U'.gen.hom.left) := LBIso.symm U'.ext
  have := U'.gen_hom
  obtain ⟨hP', hdim', hsym', hamp', hkt'⟩ := GlobalTheory.T.principalPolarisation_of_groupScheme_iso _ A' _ U'.gen U'.gen_hom L' hL' hiso
  have hsemi : IsSemiAbelian ((Over.pullback (jK R)).obj G) := Geo.Tor.IsSemiAbelian.pullback (jK R) G hG
  obtain ⟨hab, hdim⟩ := GlobalTheory.T.abelian_of_fieldExtension_pullback_proper _ _ (fracMap ρ hρ) ((Over.pullback (jK R)).obj G) _ _ A'.g hsemi hκ hP' hdim'
  obtain ⟨L, hL, hLL⟩ := GlobalTheory.T.exists_lineBundle_galoisDescent_abelianVariety_finite (FractionRing R) (FractionRing R') (fracMap ρ hρ)
    (GlobalTheory.T.fractionFieldMap_finite_of_finite_injective R R' ρ hρ hfin.2.2) (Gal ρ) (fun σ => fracAut σ.1) (fun σ x => fracAut_fracMap hρ σ x)
    (GlobalTheory.T.fixed_mem_range_fractionFieldMap_galoisInvariants R R' ρ hρ hgal) ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R')).obj G') _ hab hκ L' hL'
    (GlobalTheory.T.exists_galoisConjugate_genericBundle_iso R R' ρ hρ D D' hD A' G' U' a G β hpb.1.w hinv)
  obtain ⟨hrig, hsym⟩ := GlobalTheory.T.rigidified_symmetric_of_symmetric_fieldExtension_pullback _ _ (fracMap ρ hρ) _ _ _ hab hκ L L' hL hL' hLL hsym'
  have := hsemi.quasiCompact
  have := hsemi.separated
  have := hsemi.smooth
  obtain ⟨-, hamp, hkt⟩ := GlobalTheory.AmpleDescent.proper_relAmple_kTriv_of_fieldExtension (FractionRing R) (FractionRing R')
    (fracMap ρ hρ) ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R')).obj G') _ hκ L L' hL hL' hLL hP' hamp' hkt'
  let P : PolAV (Sp (FractionRing R)) :=
    { A := (Over.pullback (jK R)).obj G
      isAb := hab
      g := A'.g
      smoothDim := hdim
      L := L
      isLB := hL
      rigid := hrig
      sym := hsym
      ample := hamp
      ktriv := hkt }
  refine ⟨P, Iso.refl _, genMap hρ β hpb.1.w, ?_, genMap_fst _ _ _, ?_⟩
  · show IsMonHom (𝟙 _)
    infer_instance
  · simpa using hLL

end GlobalTheory.Mum.GenDesc
