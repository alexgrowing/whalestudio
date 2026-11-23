import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnifTrait
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCompleteTraitExtensionOfBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullDegSquareFourthSideStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfGenericAbelianOfClosedIsGt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoAlgebraisation
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamilyFibreEqUniformisedPullbackGenericFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TraitExt

theorem exists_fracHom {R R₁ M : Type} [CommRing R] [IsDomain R] [CommRing R₁] [IsDomain R₁] [Field M] [IsAlgClosed M]
    (ρ : R →+* R₁) (hρ : Function.Injective ρ) (hfin : ρ.Finite) (g : R →+* M) (hg : Function.Injective g) :
    ∃ e : FractionRing R₁ →+* M, ∀ r, e (algebraMap R₁ (FractionRing R₁) (ρ r)) = g r := by
  letI : Algebra R R₁ := ρ.toAlgebra
  letI : Algebra R M := g.toAlgebra
  have hinj : Function.Injective (algebraMap R (FractionRing R₁)) := by
    rw [IsScalarTower.algebraMap_eq R R₁ (FractionRing R₁)]
    exact (IsFractionRing.injective R₁ (FractionRing R₁)).comp hρ
  haveI : Module.IsTorsionFree R (FractionRing R₁) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hinj
  haveI : Module.IsTorsionFree R M := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hg
  haveI : Algebra.IsIntegral R R₁ := ⟨fun x => hfin.to_isIntegral x⟩
  haveI : Algebra.IsAlgebraic R R₁ := Algebra.IsIntegral.isAlgebraic
  haveI : Algebra.IsAlgebraic R (FractionRing R₁) :=
    (IsFractionRing.isAlgebraic_iff' R R₁ (FractionRing R₁)).1 inferInstance
  refine ⟨(IsAlgClosed.lift : FractionRing R₁ →ₐ[R] M).toRingHom, fun r => ?_⟩
  have h := (IsAlgClosed.lift : FractionRing R₁ →ₐ[R] M).commutes r
  rw [IsScalarTower.algebraMap_apply R R₁ (FractionRing R₁)] at h
  exact h

end GlobalTheory.Mum.TraitExt

namespace GlobalTheory.Mum.TraitExt

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem unifTrait_pull : ∀ (R R₁ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁]
    (ρ : R →+* R₁), Base R → FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D₁ : DegData R₁ (maximalIdeal R₁)),
    Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G₁ : Over (Sp R₁))
    [GrpObj G₁] [IsCommMonObj G₁] (β₁ : G₁.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G₁ G (spMap ρ) β₁ →
    ∀ L : LB G.left, L.IsLB → UnifTrait D G L → UnifTrait D₁ G₁ (L.pull β₁) := by
  intro R R₁ _ _ _ _ _ _ ρ hR hfin D D₁ hρD G _ _ G₁ _ _ β₁ hG hpb L hL hU
  obtain ⟨hρD⟩ := hρD
  obtain ⟨W, _, _, _, φ, G', _, _, β, D', A', U', hW, hφi, hφl, hpb', hLB, ⟨hD⟩⟩ := hU
  have hgi : Function.Injective
      ((algebraMap (FractionRing W) (Kb W)).comp ((algebraMap W (FractionRing W)).comp φ)) :=
    (algebraMap (FractionRing W) (Kb W)).injective.comp ((IsFractionRing.injective W (FractionRing W)).comp hφi)
  obtain ⟨e, he⟩ := exists_fracHom ρ hfin.2.1 hfin.2.2 _ hgi
  obtain ⟨W₁, _, _, _, iw, φ₁, -, hW₁, hiwi, -, hiwl, hφ₁i, hφ₁l, hcomm, -, -⟩ :=
    GlobalTheory.T.exists_finite_complete_trait_extension_of_base R W R₁ hW φ hφi hφl ρ hfin (Kb W) e he
  have hAW : AdmBase W (maximalIdeal W) := by
    haveI := hW.1; exact ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hAW₁ : AdmBase W₁ (maximalIdeal W₁) := by
    haveI := hW₁.1; exact ⟨inferInstance, inferInstance, inferInstance, hW₁.2.1⟩
  have hG' : IsSemiAbelian G' := by
    obtain ⟨eI, heI, -⟩ := grpPullback_iso hpb' (isGrpPullback_pullback G (spMap φ))
    haveI := heI
    exact GlobalTheory.isSemiAbelian_of_grpIso eI (IsSemiAbelian.pullback _ G hG)
  obtain ⟨hL5, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨D'', hD'', A'', U'', hP⟩ := GlobalTheory.UT.EndBaseChange.exists_pull hL5.polBaseChange h4.unifBaseChange
    h5.psiOnExists hAW hAW₁ iw hiwi (map_maximalIdeal_le iw) hG' U'
  have hpb1 : IsGrpPullback ((Over.pullback (specOf iw)).obj G') G' (spMap iw) (pullback.fst G'.hom (specOf iw)) :=
    isGrpPullback_pullback G' (spMap iw)
  have hsp : spMap iw ≫ spMap φ = spMap φ₁ ≫ spMap ρ := by
    rw [spMap_comp, spMap_comp, hcomm]
  have hpb2 := hpb1.comp hpb'
  have hsq : (pullback.fst G'.hom (specOf iw) ≫ β) ≫ G.hom =
      ((Over.pullback (specOf iw)).obj G').hom ≫ spMap φ₁ ≫ spMap ρ := by
    rw [← hsp, Category.assoc, hpb'.1.w, ← Category.assoc, pullback.condition]
    rfl
  set β'' : ((Over.pullback (specOf iw)).obj G').left ⟶ G₁.left :=
    hpb.1.lift (pullback.fst G'.hom (specOf iw) ≫ β) (((Over.pullback (specOf iw)).obj G').hom ≫ spMap φ₁) hsq
    with hβ''
  have hβ1 : β'' ≫ β₁ = pullback.fst G'.hom (specOf iw) ≫ β := hpb.1.lift_fst _ _ _
  have hβ2 : β'' ≫ G₁.hom = ((Over.pullback (specOf iw)).obj G').hom ≫ spMap φ₁ := hpb.1.lift_snd _ _ _
  have hpb3 : IsGrpPullback ((Over.pullback (specOf iw)).obj G') G₁ (spMap φ₁) β'' :=
    hpb.cancel (hpb2.congr hsp hβ1.symm) hβ2
  obtain ⟨h, -, -⟩ := GlobalTheory.T.isPullDeg_square_fourth_side R R₁ W W₁ _ _ _ _ hR.1 hfin.1 hAW hAW₁ ρ φ iw φ₁ hcomm hφ₁i hfin.2.1 hφi hiwi
    D D₁ D' D'' hρD hD hD''
  have hw1 : LBIso U''.LG.L
      (U'.LG.L.pull ((Iso.refl ((Over.pullback (specOf iw)).obj G')).hom.left ≫ pullback.fst G'.hom (specOf iw))) :=
    ⟨hP.lg.choose, hP.lg.choose_spec.1⟩
  have hw2 : LBIso (U'.LG.L.pull ((Iso.refl ((Over.pullback (specOf iw)).obj G')).hom.left ≫
      pullback.fst G'.hom (specOf iw))) (L.pull (pullback.fst G'.hom (specOf iw) ≫ β)) :=
    GlobalTheory.Ex.GenericFibre.lbIso_pull hLB _ (by simp)
  have hw3 : LBIso (L.pull (pullback.fst G'.hom (specOf iw) ≫ β)) ((L.pull β₁).pull β'') :=
    GlobalTheory.AlgUniq.lbIso_pull_comp hL β₁ β'' _ hβ1
  have hw : LBIso U''.LG.L ((L.pull β₁).pull β'') :=
    LBIso.trans U''.LG.isLB (pull_isLB U'.LG.isLB _) (pull_isLB (pull_isLB hL _) _) hw1
      (LBIso.trans (pull_isLB U'.LG.isLB _) (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) hw2 hw3)
  exact ⟨W₁, inferInstance, inferInstance, inferInstance, φ₁, (Over.pullback (specOf iw)).obj G', inferInstance,
    inferInstance, β'', D'', A'', U'', hW₁, hφ₁i, hφ₁l, hpb3, hw, ⟨h⟩⟩

end GlobalTheory.Mum.TraitExt
