import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LineBundleIsoDescendsToSubringOfFinset
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MorphismDescendsToSubring
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubring
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsNoethModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrincipalObjectDescendsLargeSubfield
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RigSymDescent

theorem axes_sq {S' S : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] {f : S' ⟶ S}
    {ψ : G'.left ⟶ G.left} {ψ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (hG : IsGrpPullback G' G f ψ)
    (sq : Geo.Tor.IsSquare ψ ψ₂) :
    (lift (1 : G' ⟶ G') (𝟙 G')).left ≫ ψ₂ = ψ ≫ (lift (1 : G ⟶ G) (𝟙 G)).left ∧
    (lift (𝟙 G') (1 : G' ⟶ G')).left ≫ ψ₂ = ψ ≫ (lift (𝟙 G) (1 : G ⟶ G)).left ∧
    (lift (snd G' G') (fst G' G')).left ≫ ψ₂ = ψ₂ ≫ (lift (snd G G) (fst G G)).left := by
  let U : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk ψ hG.1.w
  have o₁ : (1 : G' ⟶ G').left ≫ ψ = ψ ≫ (1 : G ⟶ G).left :=
    congrArg (fun q => q.left) ((map_one (pushHom hG G')).trans (MonObj.comp_one U).symm)
  have e : ∀ (x y : G' ⟶ G') (x₀ y₀ : G ⟶ G), x.left ≫ ψ = ψ ≫ x₀.left → y.left ≫ ψ = ψ ≫ y₀.left →
      (lift x y).left ≫ ψ₂ = ψ ≫ (lift x₀ y₀).left := fun x y x₀ y₀ hx hy =>
    (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (G'.hom ≫ f)) (𝟙 G'.left) x y ψ x₀ y₀
      ((Category.id_comp _).trans hx) ((Category.id_comp _).trans hy))
  refine ⟨e _ _ _ _ o₁ (by simp), e _ _ _ _ (by simp) o₁, ?_⟩
  exact (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk ((G' ⊗ G').hom ≫ f))
    (𝟙 (G' ⊗ G').left) _ _ ψ₂ _ _ ((Category.id_comp _).trans sq.2.symm) ((Category.id_comp _).trans sq.1.symm))

end GlobalTheory.RigSymDescent

namespace GlobalTheory

open GlobalTheory.CechPic in

theorem rigSym_descends_to_subring_containing_finset : ∀ (R : Type) [CommRing R] (R₁ : Subring R) (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (φ : A.left ⟶ A₁.left) (φ₂ : (A ⊗ A).left ⟶ (A₁ ⊗ A₁).left), IsAbelianScheme A₁ → P.IsLB → P₁.IsLB → IsGrpPullback A A₁ (spMap R₁.subtype) φ → Geo.Tor.IsSquare φ φ₂ → LBIso P (P₁.pull φ₂) → IsTrivial (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → IsTrivial (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∃ F : Finset R, ∀ (R₂ : Subring R) (h : R₁ ≤ R₂), (F : Set R) ⊆ R₂ → ∀ (A₂ : Over (Sp R₂)) [GrpObj A₂] (π : A₂.left ⟶ A₁.left) (π₂ : (A₂ ⊗ A₂).left ⟶ (A₁ ⊗ A₁).left), IsGrpPullback A₂ A₁ (spMap (Subring.inclusion h)) π → Geo.Tor.IsSquare π π₂ → IsTrivial ((P₁.pull π₂).pull (lift (1 : A₂ ⟶ A₂) (𝟙 A₂)).left) ∧ IsTrivial ((P₁.pull π₂).pull (lift (𝟙 A₂) (1 : A₂ ⟶ A₂)).left) ∧ LBIso (P₁.pull π₂) ((P₁.pull π₂).pull (lift (snd A₂ A₂) (fst A₂ A₂)).left) := by
  intro R _ R₁ A _ P A₁ _ P₁ φ φ₂ hab hP hP₁ hA sq hiso h1 h2 hs
  classical
  have := hab.proper
  haveI : QuasiCompact (A₁ ⊗ A₁).hom := inferInstanceAs (QuasiCompact (pullback.fst A₁.hom A₁.hom ≫ A₁.hom))
  haveI : QuasiSeparated (A₁ ⊗ A₁).hom :=
    inferInstanceAs (QuasiSeparated (pullback.fst A₁.hom A₁.hom ≫ A₁.hom))
  obtain ⟨e₁, e₂, e₃⟩ := GlobalTheory.RigSymDescent.axes_sq hA sq
  have hc : cls P hP = pull φ₂ (cls P₁ hP₁) := (cls_eq_iff hP (pull_isLB hP₁ _)).2 hiso
  have hT := LB.isLB_triv A₁.left
  have z : ∀ {Y : Scheme.{0}} (g : Y ⟶ A₁.left), pull g (cls _ hT) = 0 := fun g => map_zero (pull g)

  have d₁ : LBIso ((P₁.pull (lift (1 : A₁ ⟶ A₁) (𝟙 A₁)).left).pull φ) ((LB.triv A₁.left).pull φ) := by
    refine (cls_eq_iff (pull_isLB (pull_isLB hP₁ _) _) (pull_isLB hT _)).1 ?_
    rw [cls_pull (pull_isLB hP₁ _), cls_pull hP₁, cls_pull hT, z, ← pull_comp, ← e₁, pull_comp, ← hc,
      ← cls_pull hP _ (pull_isLB hP _)]
    exact (cls_eq_zero_iff _).2 h1
  have d₂ : LBIso ((P₁.pull (lift (𝟙 A₁) (1 : A₁ ⟶ A₁)).left).pull φ) ((LB.triv A₁.left).pull φ) := by
    refine (cls_eq_iff (pull_isLB (pull_isLB hP₁ _) _) (pull_isLB hT _)).1 ?_
    rw [cls_pull (pull_isLB hP₁ _), cls_pull hP₁, cls_pull hT, z, ← pull_comp, ← e₂, pull_comp, ← hc,
      ← cls_pull hP _ (pull_isLB hP _)]
    exact (cls_eq_zero_iff _).2 h2
  have d₃ : LBIso (P₁.pull φ₂) ((P₁.pull (lift (snd A₁ A₁) (fst A₁ A₁)).left).pull φ₂) := by
    refine (cls_eq_iff (pull_isLB hP₁ _) (pull_isLB (pull_isLB hP₁ _) _)).1 ?_
    rw [cls_pull hP₁, cls_pull (pull_isLB hP₁ _), cls_pull hP₁, ← pull_comp, ← e₃, pull_comp, ← hc,
      ← cls_pull hP _ (pull_isLB hP _)]
    exact (cls_eq_iff hP (pull_isLB hP _)).2 hs
  obtain ⟨F₁, H₁⟩ := lbIso_descends_to_subring_containing_finset R R₁ A.left A₁.left A.hom A₁.hom φ _ _ hA.1
    (pull_isLB hP₁ _) hT d₁
  obtain ⟨F₂, H₂⟩ := lbIso_descends_to_subring_containing_finset R R₁ A.left A₁.left A.hom A₁.hom φ _ _ hA.1
    (pull_isLB hP₁ _) hT d₂
  obtain ⟨F₃, H₃⟩ := lbIso_descends_to_subring_containing_finset R R₁ (A ⊗ A).left (A₁ ⊗ A₁).left (A ⊗ A).hom
    (A₁ ⊗ A₁).hom φ₂ _ _ (SiegDesc.isPullback_of_isSquare hA.1 sq) hP₁ (pull_isLB hP₁ _) d₃
  refine ⟨F₁ ∪ F₂ ∪ F₃, fun R₂ h hF A₂ _ π π₂ hB sqB => ?_⟩
  simp only [Finset.coe_union, Set.union_subset_iff] at hF
  obtain ⟨f₁, f₂, f₃⟩ := GlobalTheory.RigSymDescent.axes_sq hB sqB
  have k₁ := H₁ R₂ h hF.1.1 A₂.left A₂.hom π hB.1
  have k₂ := H₂ R₂ h hF.1.2 A₂.left A₂.hom π hB.1
  have k₃ := H₃ R₂ h hF.2 (A₂ ⊗ A₂).left (A₂ ⊗ A₂).hom π₂ (SiegDesc.isPullback_of_isSquare hB.1 sqB)
  refine ⟨(cls_eq_zero_iff (pull_isLB (pull_isLB hP₁ _) _)).1 ?_, (cls_eq_zero_iff (pull_isLB (pull_isLB hP₁ _) _)).1 ?_,
    (cls_eq_iff (pull_isLB hP₁ _) (pull_isLB (pull_isLB hP₁ _) _)).1 ?_⟩
  · have := (cls_eq_iff (pull_isLB (pull_isLB hP₁ _) _) (pull_isLB hT _)).2 k₁
    rw [cls_pull (pull_isLB hP₁ _), cls_pull hP₁, cls_pull hT, z, ← pull_comp] at this
    rw [cls_pull (pull_isLB hP₁ _), cls_pull hP₁, ← pull_comp, f₁]
    exact this
  · have := (cls_eq_iff (pull_isLB (pull_isLB hP₁ _) _) (pull_isLB hT _)).2 k₂
    rw [cls_pull (pull_isLB hP₁ _), cls_pull hP₁, cls_pull hT, z, ← pull_comp] at this
    rw [cls_pull (pull_isLB hP₁ _), cls_pull hP₁, ← pull_comp, f₂]
    exact this
  · have := (cls_eq_iff (pull_isLB hP₁ _) (pull_isLB (pull_isLB hP₁ _) _)).2 k₃
    rw [cls_pull hP₁, cls_pull (pull_isLB hP₁ _), cls_pull hP₁, ← pull_comp] at this
    rw [cls_pull hP₁, cls_pull (pull_isLB hP₁ _), cls_pull hP₁, ← pull_comp, f₃]
    exact this

end GlobalTheory
