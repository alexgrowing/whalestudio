import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationCompleteLocalEvenOnTorusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinExtTqClosedFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullDegUniqueAndComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTrans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationTransferIsPullDegIdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPullFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataPullbackInjectiveLocalHom
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamilyFibreEqUniformisedPullbackGenericFibre
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCpPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfGenericAbelianOfClosedIsGt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnifTrait
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitUniformisationPullbackFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenCubicalTrivialisationOfTraitUniformisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisedAbelianGenericFibreTraitUniformisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPullDegTraitAndBaseUniformisationStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.Ident

theorem finExt_isLocalHom {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R']
    {ρ : R →+* R'} (h : FinExt ρ) : IsLocalHom ρ := by
  letI := ρ.toAlgebra
  have hi : Algebra.IsIntegral R R' := ⟨fun x => h.2.2.to_isIntegral x⟩
  have hm : (maximalIdeal R').comap ρ = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (maximalIdeal R'))
  exact ((IsLocalRing.local_hom_TFAE ρ).out 0 4).2 hm

theorem finExt_comp {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] [CommRing R₂]
    [IsDomain R₂] [IsLocalRing R₂] {ρ : R →+* R₁} {ρ' : R₁ →+* R₂} (h : FinExt ρ) (h' : FinExt ρ') :
    FinExt (ρ'.comp ρ) :=
  ⟨h'.1, h'.2.1.comp h.2.1, h'.2.2.comp h.2.2⟩

theorem unif_along_finExt : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (ρ : R →+* R'), Base R → FinExt ρ → ∀ (D₂ : DegData R (maximalIdeal R))
    (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (U₂ : Unif (maximalIdeal R) D₂ A G) (D₃ : DegData R' (maximalIdeal R')), Nonempty (IsPullDeg ρ D₂.toPre D₃.toPre) →
    ∃ (G₃ : Over (Sp R')) (_ : GrpObj G₃) (_ : IsCommMonObj G₃) (β₃ : G₃.left ⟶ G.left) (A₃ : PolAV (Sp (FractionRing R')))
      (U₃ : Unif (maximalIdeal R') D₃ A₃ G₃), IsSemiAbelian G₃ ∧ IsGrpPullback G₃ G (spMap ρ) β₃ ∧
        LBIso U₃.LG.L (U₂.LG.L.pull β₃) := by
  intro R R' _ _ _ _ _ _ ρ hR hf D₂ A G _ _ hG U₂ D₃ h23
  have := hR.2
  haveI := finExt_isLocalHom hf
  obtain ⟨hL, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨D', hD, A', U', hP⟩ := GlobalTheory.UT.EndBaseChange.exists_pull hL.polBaseChange h4.unifBaseChange h5.psiOnExists
    hR.1 hf.1 ρ hf.2.1 (map_maximalIdeal_le ρ) hG U₂
  have h3' : Nonempty (IsPullDeg (RingHom.id R') D₃.toPre D'.toPre) :=
    GlobalTheory.Mum.isPullDeg_unique_and_comp.1 R R' ρ hf.2.1 D₂.toPre D₃.toPre D'.toPre h23 ⟨hD⟩
  have hG' : IsSemiAbelian ((Over.pullback (specOf ρ)).obj G) := IsSemiAbelian.pullback _ G hG
  obtain ⟨U₃, hU₃, -⟩ := (GlobalTheory.T.uniformisation_transfer_isPullDeg_id R' (maximalIdeal R') hf.1 D₃ D' h3' A' _ hG').1 U'
  have hb : (Iso.refl ((Over.pullback (specOf ρ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf ρ) =
      pullback.fst G.hom (specOf ρ) := Category.id_comp _
  refine ⟨(Over.pullback (specOf ρ)).obj G, inferInstance, inferInstance,
    (Iso.refl ((Over.pullback (specOf ρ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf ρ), A', U₃, hG', ?_, ?_⟩
  · exact (isGrpPullback_pullback G (spMap ρ)).congr rfl hb.symm
  · rw [hU₃]
    exact ⟨hP.lg.choose, hP.lg.choose_spec.1⟩

theorem exists_finExt_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G), IsSemiAbelian G → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (β : G'.left ⟶ G.left) (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G'), IsGrpPullback G' G (spMap φ) β → LBIso U'.LG.L (P.L.L.pull β) → Nonempty (IsPullDeg φ D.toPre D'.toPre) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ : DegData R' (maximalIdeal R')) (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β₁ : G₁.left ⟶ G.left) (A₁ : PolAV (Sp (FractionRing R'))) (U₁ : Unif (maximalIdeal R') D₁ A₁ G₁), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ IsGrpPullback G₁ G (spMap ρ) β₁ ∧ LBIso U₁.LG.L (P.L.L.pull β₁) := by
  intro R _ _ _ hR D G _ _ P hG W _ _ _ hW φ hφ hloc G' _ _ β D' A' U' hβ hL hD
  have hT : UnifTrait D G P.L.L := ⟨W, _, _, _, φ, G', _, _, β, D', A', U', hW, hφ, hloc, hβ, hL, hD⟩
  obtain ⟨R₁, _, _, _, ρ₁, G₁, _, _, β₁, X, _, _, _, hf₁, hβ₁, hQ⟩ := GlobalTheory.Mum.exists_finExt_tq_closedFibre R hR G hG
  haveI hloc₁ : IsLocalHom ρ₁ := finExt_isLocalHom hf₁
  obtain ⟨D₁, hD₁⟩ := GlobalTheory.MumPull.exists_pull R R₁ ρ₁ hf₁.2.1 hloc₁ D
  have hR₁ : Base R₁ := ⟨hf₁.1, by haveI := hR.2; exact charZero_of_injective_ringHom hf₁.2.1⟩
  have hG₁ : IsSemiAbelian G₁ := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso hβ₁ (isGrpPullback_pullback G (spMap ρ₁))
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback _ G hG)
  obtain ⟨P₁, w₁, hP₁L, hP₁⟩ := GlobalTheory.UU.exists_cp_pull _ _ (spMap ρ₁) G G₁ β₁ hβ₁.1.w
    (fun T x y => Over.OverMorphism.ext (hβ₁.2 T x y _ _ rfl rfl).symm) P
  have hT₁ : UnifTrait D₁ G₁ P₁.L.L := by
    rw [hP₁L]; exact GlobalTheory.T.traitUniformisation_pullback_finiteExtension R R₁ ρ₁ hR hf₁ D D₁ hD₁ G G₁ β₁ hG hβ₁ P.L.L P.L.isLB hT
  have hE : EvenOn P₁ := GlobalTheory.T.evenCubicalTrivialisation_of_trait_uniformisation R₁ hR₁ D₁ G₁ P₁ hG₁ hT₁ X hQ
  obtain ⟨A, gen, hgen, hA⟩ := GlobalTheory.T.exists_polarisedAbelian_generic_fibre_trait_uniformised R₁ hR₁ D₁ G₁ P₁ hG₁ hT₁
  obtain ⟨D₂, U₂, hU₂, -⟩ := GlobalTheory.T.exists_uniformisation_completeLocal_evenOnTorus R₁ hR₁ G₁ P₁ hG₁ hE A gen hgen hA
  obtain ⟨V, _, _, ψ, D', hψ, h1, h2⟩ := GlobalTheory.T.exists_common_pullDeg_trait_and_base_uniformisation R₁ hR₁ D₁ G₁ P₁.L.L P₁.L.isLB hG₁ hT₁ D₂ A U₂ (by rw [hU₂])
  obtain ⟨R', _, _, _, ρ₂, D₃, hf₂, h13, h23⟩ :=
    GlobalTheory.MumRig.exists_common_pull_finite R₁ hR₁ D₁ D₂ V ψ hψ D' h1 h2
  obtain ⟨G₃, _, _, β₃, A₃, U₃, -, hβ₃, hL₃⟩ := unif_along_finExt R₁ R' ρ₂ hR₁ hf₂ D₂ A G₁ hG₁ U₂ D₃ h23
  refine ⟨R', _, _, _, ρ₂.comp ρ₁, D₃, G₃, _, _, β₃ ≫ β₁, A₃, U₃, finExt_comp hf₁ hf₂, ?_, ?_, ?_⟩
  · obtain ⟨a⟩ := hD₁
    obtain ⟨b⟩ := h13
    exact GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hf₁.2.1 hf₂.2.1 a b
  · refine (hβ₃.comp hβ₁).congr ?_ rfl
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]; rfl
  · rw [hU₂] at hL₃
    have hPP : LBIso P₁.L.L (P.L.L.pull β₁) := ⟨w₁, hP₁.gen⟩
    exact LBIso.trans U₃.LG.isLB (pull_isLB P₁.L.isLB _) (pull_isLB P.L.isLB _) hL₃
      (GlobalTheory.Ex.GenericFibre.lbIso_pull hPP β₃ rfl)

end GlobalTheory.Mum.Ident
