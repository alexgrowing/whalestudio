import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteTypeSubringAdjoin
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsProjectiveAbelianModel
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RelAmpleSubring
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFinsetKTrivOfSubring
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RigidifiedSymDescendToSubring
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.KeyTf

private theorem spMap_subtype_comp_inclusion' {S : Type} [CommRing S] {R R' : Subring S} (h : R ≤ R') :
    spMap R'.subtype ≫ spMap (Subring.inclusion h) = spMap R.subtype := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

private theorem exists_lift_to_pullback_grpPullback {S : Type} [CommRing S] {R R' : Subring S} (h : R ≤ R') (A : Over (Sp S))
    [GrpObj A] (A₀ : Over (Sp R)) [GrpObj A₀] (φ : A.left ⟶ A₀.left) (H : IsGrpPullback A A₀ (spMap R.subtype) φ) :
    ∃ φ₁ : A.left ⟶ ((Over.pullback (spMap (Subring.inclusion h))).obj A₀).left,
      φ₁ ≫ pullback.fst A₀.hom (spMap (Subring.inclusion h)) = φ ∧
      IsGrpPullback A ((Over.pullback (spMap (Subring.inclusion h))).obj A₀) (spMap R'.subtype) φ₁ := by
  have w : φ ≫ A₀.hom = (A.hom ≫ spMap R'.subtype) ≫ spMap (Subring.inclusion h) := by
    rw [Category.assoc, spMap_subtype_comp_inclusion' h]
    exact H.1.w
  refine ⟨pullback.lift φ (A.hom ≫ spMap R'.subtype) w, pullback.lift_fst _ _ _, ?_⟩
  refine IsGrpPullback.cancel (isGrpPullback_pullback A₀ (spMap (Subring.inclusion h))) ?_ ?_
  · exact H.congr (spMap_subtype_comp_inclusion' h).symm (pullback.lift_fst _ _ _).symm
  · exact pullback.lift_snd _ _ _

theorem exists_model_of_le {S : Type} [CommRing S] {R R' : Subring S} (h : R ≤ R') (A : Over (Sp S)) [GrpObj A]
    (A₀ : Over (Sp R)) [GrpObj A₀] (φ : A.left ⟶ A₀.left) (H : IsGrpPullback A A₀ (spMap R.subtype) φ) :
    ∃ (A₁ : Over (Sp R')) (_ : GrpObj A₁) (φ₁ : A.left ⟶ A₁.left) (π : A₁.left ⟶ A₀.left), φ₁ ≫ π = φ ∧
      IsGrpPullback A₁ A₀ (spMap (Subring.inclusion h)) π ∧ IsGrpPullback A A₁ (spMap R'.subtype) φ₁ := by
  obtain ⟨φ₁, e, H₁⟩ := exists_lift_to_pullback_grpPullback h A A₀ φ H
  exact ⟨_, inferInstance, φ₁, _, e, isGrpPullback_pullback A₀ _, H₁⟩

private theorem lbIso_pull_comp_theta_law {X Y Z : Scheme.{0}} {L : LB Z} (hL : L.IsLB) (φ₁ : X ⟶ Y) (π : Y ⟶ Z) :
    LBIso (L.pull (φ₁ ≫ π)) ((L.pull π).pull φ₁) := by
  refine LBLimit.lbIso_of_refinement _ _ (pull_isLB hL _) (fun a _ => a ⟨⟩ ⟨⟩) ?_ ?_
  · intro a y hy
    have h1 := (mem_pull (L := L.pull π)).1 hy
    have h2 := (mem_pull (L := L)).1 h1
    exact (mem_pull (L := L)).2 h2
  · intro a b y ha hb
    have ha' := (mem_pull (L := L)).1 ((mem_pull (L := L.pull π)).1 ha)
    have hb' := (mem_pull (L := L)).1 ((mem_pull (L := L.pull π)).1 hb)
    rw [gm_pull_g (L.pull π) φ₁ (𝟙 X) y a b ha hb, gm_pull_g L π (𝟙 X ≫ φ₁) y (a ⟨⟩) (b ⟨⟩)
      ((mem_pull (L := L.pull π)).1 ha) ((mem_pull (L := L.pull π)).1 hb),
      gm_pull_g L (φ₁ ≫ π) (𝟙 X) y (fun _ => a ⟨⟩ ⟨⟩) (fun _ => b ⟨⟩ ⟨⟩) ((mem_pull (L := L)).2 ha')
      ((mem_pull (L := L)).2 hb')]
    simp only [Category.assoc]

theorem lbIso_pull_pull_of_comp {X Y Z : Scheme.{0}} {M : LB X} {L : LB Z} (hM : M.IsLB) (hL : L.IsLB)
    {φ : X ⟶ Z} {φ₁ : X ⟶ Y} {π : Y ⟶ Z} (e : φ₁ ≫ π = φ) (H : LBIso M (L.pull φ)) :
    LBIso M ((L.pull π).pull φ₁) := by
  subst e
  exact LBIso.trans hM (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) H (lbIso_pull_comp_theta_law hL φ₁ π)

private theorem exists_intermediate_abelian_model_factorization {S : Type} [CommRing S] {g : ℕ} {R R' : Subring S} (h : R ≤ R') (A : Over (Sp S))
    [GrpObj A] (A₀ : Over (Sp R)) [GrpObj A₀] (φ : A.left ⟶ A₀.left) (H : IsGrpPullback A A₀ (spMap R.subtype) φ)
    (hab : IsAbelianScheme A₀) (hpr : IsProjOver A₀.hom) (hsm : SmoothOfRelativeDimension g A₀.hom) :
    ∃ (A₁ : Over (Sp R')) (_ : GrpObj A₁) (φ₁ : A.left ⟶ A₁.left) (π : A₁.left ⟶ A₀.left), φ₁ ≫ π = φ ∧
      IsGrpPullback A₁ A₀ (spMap (Subring.inclusion h)) π ∧ IsGrpPullback A A₁ (spMap R'.subtype) φ₁ ∧
      IsAbelianScheme A₁ ∧ IsProjOver A₁.hom ∧ SmoothOfRelativeDimension g A₁.hom := by
  obtain ⟨φ₁, e, H₁⟩ := exists_lift_to_pullback_grpPullback h A A₀ φ H
  have hp := isGrpPullback_pullback A₀ (spMap (Subring.inclusion h))
  refine ⟨_, inferInstance, φ₁, _, e, hp, H₁, ?_, ?_, ?_⟩
  · exact Out.TLinPf.isAb_pullback _ A₀ hab
  · exact ProjSpace.isProjOver_of_isPullback_spMap (Subring.inclusion h) hp.1 hpr
  · exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hp.1 hsm

theorem exists_polAV_finiteType_subring :
    ∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] (P : Out.PolAV (Sp S)), ∃ (R : Subring S) (P₀ : Out.PolAV (Sp R)) (φ : P.A.left ⟶ P₀.A.left), Algebra.FiniteType ℤ R ∧ P₀.g = P.g ∧ IsGrpPullback P.A P₀.A (spMap R.subtype) φ ∧ LBIso P.L (P₀.L.pull φ) := by
  classical
  intro S _ _ _ P
  obtain ⟨R₀, A₀, _, φ₀, hR₀, hab₀, hsm₀, hpr₀, H₀⟩ := exists_projective_abelian_model S P
  have := hab₀.proper
  obtain ⟨F₁, hF₁⟩ := LBLimit.lb_descends_to_fg_subring S R₀ P.A.left A₀.left P.A.hom A₀.hom φ₀ P.L H₀.1 P.isLB
  obtain ⟨R₁, hle₁, hsub₁, hR₁⟩ := exists_finiteType_subring_adjoin S R₀ F₁ hR₀
  obtain ⟨A₁, _, φ₁, π₁, e₁, Hπ₁, H₁, hab₁, hpr₁, hsm₁⟩ := exists_intermediate_abelian_model_factorization hle₁ P.A A₀ φ₀ H₀ hab₀ hpr₀ hsm₀
  obtain ⟨L₁, hL₁, hiso₁⟩ := hF₁ R₁ hle₁ hsub₁ A₁.left A₁.hom π₁ φ₁ Hπ₁.1 e₁ H₁.1.w
  have : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing ℤ R₁
  obtain ⟨F₂, hF₂⟩ := AmpleSubring.relAmple_subring S R₁ P A₁ φ₁ L₁ hab₁ hpr₁ hL₁ H₁ hiso₁
  obtain ⟨F₃, hF₃⟩ := rigidified_sym_descend_to_subring S R₁ P A₁ φ₁ L₁ hab₁ hL₁ H₁ hiso₁
  obtain ⟨R₂, hle₂, hsub₂, hR₂⟩ := exists_finiteType_subring_adjoin S R₁ (F₂ ∪ F₃) hR₁
  rw [Finset.coe_union, Set.union_subset_iff] at hsub₂
  obtain ⟨A₂, _, φ₂, π₂, e₂, Hπ₂, H₂, hab₂, hpr₂, hsm₂⟩ := exists_intermediate_abelian_model_factorization hle₂ P.A A₁ φ₁ H₁ hab₁ hpr₁ hsm₁
  have ha₂ := hF₂ R₂ hle₂ hsub₂.1 A₂ π₂ Hπ₂
  have hrs₂ := hF₃ R₂ hle₂ hsub₂.2 A₂ π₂ Hπ₂
  have hL₂ := pull_isLB hL₁ π₂
  have hiso₂ := lbIso_pull_pull_of_comp P.isLB hL₁ e₂ hiso₁
  have : IsNoetherianRing R₂ := Algebra.FiniteType.isNoetherianRing ℤ R₂
  obtain ⟨F₄, hF₄⟩ := exists_finset_kTriv_of_subring S R₂ P A₂ φ₂ (L₁.pull π₂) hab₂ hL₂ ha₂ H₂ hiso₂
  obtain ⟨R₃, hle₃, hsub₃, hR₃⟩ := exists_finiteType_subring_adjoin S R₂ F₄ hR₂
  obtain ⟨A₃, _, φ₃, π₃, e₃, Hπ₃, H₃, hab₃, hpr₃, hsm₃⟩ := exists_intermediate_abelian_model_factorization hle₃ P.A A₂ φ₂ H₂ hab₂ hpr₂ hsm₂
  have hk₃ := hF₄ R₃ hle₃ hsub₃ A₃ π₃ Hπ₃
  have hL₃ := pull_isLB hL₂ π₃
  have hpol := pol_pull _ _ A₂ A₃ _ π₃ _ _ hL₂ hL₃ hab₂ Hπ₃ (PolBaseChange.lbIso_refl hL₃)
  have hiso₃ := lbIso_pull_pull_of_comp P.isLB hL₂ e₃ hiso₂
  refine ⟨R₃,
    { A := A₃
      isAb := hab₃
      g := P.g
      smoothDim := hsm₃
      L := (L₁.pull π₂).pull π₃
      isLB := hL₃
      rigid := PolBaseChange.rigidified_pull Hπ₃ hrs₂.1
      sym := PolBaseChange.sym_pull Hπ₃ hrs₂.2
      ample := hpol.2.1 ha₂
      ktriv := hk₃ }, φ₃, hR₃, rfl, H₃, hiso₃⟩

end GlobalTheory.KeyTf
