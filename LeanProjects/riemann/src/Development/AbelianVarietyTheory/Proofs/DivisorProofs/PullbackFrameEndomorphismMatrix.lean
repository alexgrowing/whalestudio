import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsometryPullIdComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDivPullEqVPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEquivariantToBidual
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasicoherentOfLocallyIso

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory

namespace GlobalTheory.SectionPull

theorem canonical_app_pullbackSections {X T : Scheme.{0}} (c : T ⟶ X) (t : X ⟶ T) (h : t ≫ c = 𝟙 X)
    (F : X.Modules) (s : Γ(F, ⊤)) :
    ((Scheme.Modules.pullbackComp t c).hom.app F ≫ (Scheme.Modules.pullbackCongr h).hom.app F ≫
        (Scheme.Modules.pullbackId _).hom.app F).app ⊤
      (QCoh.pullbackSections t _ (le_refl (⊤ : X.Opens))
        (QCoh.pullbackSections c F (le_refl (⊤ : T.Opens)) s)) = s := by
  have H {j j' : X ⟶ X} (w : j = j') (hj : (⊤ : X.Opens) ≤ j ⁻¹ᵁ ⊤) (hj' : (⊤ : X.Opens) ≤ j' ⁻¹ᵁ ⊤) :
      ((Scheme.Modules.pullbackCongr w).hom.app F).app ⊤ (QCoh.pullbackSections j F hj s) =
        QCoh.pullbackSections j' F hj' s := by
    subst w; rfl
  have e1 := PullPull.pullbackComp_hom_app t c F (U := ⊤) (V := ⊤) (T := ⊤) (le_refl _) (le_refl _)
    (le_refl (⊤ : X.Opens)) s
  have e2 := H h (le_refl (⊤ : X.Opens)) (le_refl (⊤ : X.Opens))
  have e3 := PullPull.pullbackId_hom_app F (U := ⊤) (V := ⊤) (le_refl _) (le_refl _) s
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [e1, e2, e3, Twist.resM_self]

theorem pullback_map_comp_canonical : ∀ (X T : Scheme.{0}) (c : T ⟶ X) (t : X ⟶ T) (h : t ≫ c = 𝟙 X) (F : X.Modules) (κ : Type) [Fintype κ] (e : κ → Γ(F, ⊤)), VB.IsFrame e → ∀ (Φ : (Scheme.Modules.pullback c).obj F ⟶ (Scheme.Modules.pullback c).obj F) (B : Matrix κ κ Γ(T, ⊤)), (∀ i, Φ.app ⊤ (QCoh.pullbackSections c F (le_refl (⊤ : T.Opens)) (e i)) = ∑ j, B j i • QCoh.pullbackSections c F (le_refl (⊤ : T.Opens)) (e j)) → ∀ (ψ : F ⟶ F), (∀ i, ψ.app ⊤ (e i) = ∑ j, t.appTop (B j i) • e j) → (Scheme.Modules.pullback t).map Φ ≫ (Scheme.Modules.pullbackComp t c).hom.app F ≫ (Scheme.Modules.pullbackCongr h).hom.app F ≫ (Scheme.Modules.pullbackId _).hom.app F = ((Scheme.Modules.pullbackComp t c).hom.app F ≫ (Scheme.Modules.pullbackCongr h).hom.app F ≫ (Scheme.Modules.pullbackId _).hom.app F) ≫ ψ := by
  intro X T c t h F κ _ e he Φ B hΦ ψ hψ
  haveI := he.isVB.isQuasicoherent
  have hc := he.pullback c
  have ht : VB.IsFrame fun i => QCoh.pullbackSections t ((Scheme.Modules.pullback c).obj F)
      (le_refl (⊤ : X.Opens)) (QCoh.pullbackSections c F (le_refl (⊤ : T.Opens)) (e i)) :=
    hc.pullback t
  refine LieVB.hom_ext_of_isFrame ht fun i => ?_
  rw [Scheme.Modules.Hom.comp_app ((Scheme.Modules.pullback t).map Φ), Scheme.Modules.Hom.comp_app _ ψ,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, canonical_app_pullbackSections, hψ]
  have e1 := QCoh.pullback_map_app_pullbackSections t Φ (U := ⊤) (V := ⊤) (le_refl _)
    (QCoh.pullbackSections c F (le_refl (⊤ : T.Opens)) (e i))
  erw [e1]
  rw [hΦ, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e2 := QCoh.pullbackSections_smul t ((Scheme.Modules.pullback c).obj F) (U := ⊤) (V := ⊤)
    (le_refl _) (B j i) (QCoh.pullbackSections c F (le_refl (⊤ : T.Opens)) (e j))
  erw [e2, Scheme.Modules.Hom.app_smul, canonical_app_pullbackSections]
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

end GlobalTheory.SectionPull
