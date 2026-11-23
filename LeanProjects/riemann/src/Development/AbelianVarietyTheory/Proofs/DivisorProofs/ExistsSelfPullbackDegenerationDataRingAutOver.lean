import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationDeterminedByDegenerationDataNormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullDegUniqueAndComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SelfPull

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

theorem exists_cast {R₀ R₁ : Type} [CommRing R₀] [IsDomain R₀] [CommRing R₁] [IsDomain R₁] {f₀ f₁ : R₀ →+* R₁}
    {D₀ : DegPre R₀} {D₁ : DegPre R₁} (e : f₀ = f₁) (h : IsPullDeg f₀ D₀ D₁) :
    ∃ h' : IsPullDeg f₁ D₀ D₁, proj h' = proj h ∧ h'.xe = h.xe := by
  subst e; exact ⟨h, rfl, rfl⟩

theorem proj_def {R₀ R₁ : Type} [CommRing R₀] [IsDomain R₀] [CommRing R₁] [IsDomain R₁] {f : R₀ →+* R₁}
    {D₀ : DegPre R₀} {D₁ : DegPre R₁} (h : IsPullDeg f D₀ D₁) :
    proj h = h.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf f) := rfl

theorem exists_self_of_comp {R₀ R₁ : Type} [CommRing R₀] [IsDomain R₀] [CommRing R₁] [IsDomain R₁]
    {α : R₀ →+* R₁} {β : R₁ →+* R₁} (hα : Function.Injective α) (hβ : Function.Injective β)
    {D₀ : DegPre R₀} {D : DegPre R₁} (h₁ : IsPullDeg α D₀ D) (h : IsPullDeg (β.comp α) D₀ D)
    (hp : proj h = proj h₁) (hx : h.xe = h₁.xe) :
    ∃ h' : IsPullDeg β D D, proj h' ≫ proj h₁ = proj h₁ ∧ ∀ x, h'.xe x = x := by
  have p₁ : IsGrpPullback D.P.A D₀.P.A (spMap α) (proj h₁) := pull_grp h₁
  have sc : spMap β ≫ spMap α = spMap (β.comp α) := (spMap_comp α β).symm
  have p : IsGrpPullback D.P.A D₀.P.A (spMap β ≫ spMap α) (proj h) := (pull_grp h).congr sc.symm rfl
  obtain ⟨Φ, e₁, e₂⟩ : ∃ Φ : D.P.A.left ⟶ D.P.A.left, Φ ≫ proj h₁ = proj h ∧ Φ ≫ D.P.A.hom = D.P.A.hom ≫ spMap β :=
    ⟨p₁.1.lift (proj h) (D.P.A.hom ≫ spMap β) (p.1.w.trans (Category.assoc _ _ _).symm), p₁.1.lift_fst _ _ _,
      p₁.1.lift_snd _ _ _⟩
  have gp : IsGrpPullback D.P.A D.P.A (spMap β) Φ := IsGrpPullback.cancel p₁ (p.congr rfl e₁.symm) e₂
  obtain ⟨w, hw, hr, T⟩ := FieldPull.exists_cancel_of_eq e₁ D₀.P.isLB D.P.isLB D.P.isLB h₁.w h.w
    ((isGen_iff _).1 h₁.w_gen) ((isGen_iff _).1 h.w_gen) sc (cubeMapOf gp).e_comm (FieldPull.pmaps_rig h₁)
    (FieldPull.pmaps_rig h)
  let xe : D.X ≃+ D.X := h.xe.trans h₁.xe.symm
  have hxe : ∀ x, h₁.xe (xe x) = h.xe x := fun x => h₁.xe.apply_symm_apply _
  have hc : ∀ x, (D.c x).left ≫ Φ = spMap β ≫ (D.c (xe x)).left := fun x => by
    apply p₁.1.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, h₁.c_pr, hxe]
      exact (h.c_pr x).trans ((congrArg (· ≫ _) sc.symm).trans (Category.assoc _ _ _))
    · rw [Category.assoc, e₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨ψW⟩ := GlobalTheory.PullDegUniq.nonempty_psiOn_pull h₁
  obtain ⟨s, hs⟩ := GlobalTheory.PullDegUniq.exists_generic_section h₁
  obtain ⟨hD, hD₁, hD₂, -⟩ := GalMul.exists_isPullDeg_of_val hβ D D ψW s hs gp w hw hr xe hc (fun x z J₁ J hJ₁ hJ => by
    obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' D₀.P.isLB z
    have sβ : jK R₁ ≫ spMap β = genMap hβ ≫ jK R₁ :=
      (Category.id_comp _).symm.trans (fracMap_sq hβ)
    have sα : jK R₁ ≫ spMap α = genMap hα ≫ jK R₀ :=
      (Category.id_comp _).symm.trans (fracMap_sq hα)
    have q₁ : genMap hβ ≫ jK R₁ ≫ spMap α = (genMap hβ ≫ genMap hα) ≫ jK R₀ :=
      (congrArg (_ ≫ ·) sα).trans (Category.assoc _ _ _).symm
    have q : 𝟙 (TK R₁).left ≫ jK R₁ ≫ spMap (β.comp α) = (genMap hβ ≫ genMap hα) ≫ jK R₀ :=
      (Category.id_comp _).trans ((congrArg (_ ≫ ·) sc.symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) sβ).trans ((Category.assoc _ _ _).trans q₁))))
    have v := psi_val h _ _ q hJ₀ hJ x
    have v₁ := psi_val h₁ _ _ q₁ hJ₀ hJ₁ (xe x)
    have hx : D.xK x ≫ Φ = genMap hβ ≫ D.xK (xe x) := by
      show (jK R₁ ≫ (D.c x).left) ≫ Φ = genMap hβ ≫ jK R₁ ≫ (D.c (xe x)).left
      rw [Category.assoc, hc, ← Category.assoc, sβ, Category.assoc]
    rw [hxe, v, Category.id_comp, T _ z J₀ J₁ J hJ₀ hJ₁ hJ, hx, mul_inv, _root_.mul_assoc] at v₁
    exact (mul_left_cancel v₁).symm)
  refine ⟨hD, by rw [hD₁, e₁, hp], fun x => ?_⟩
  rw [hD₂]
  show h₁.xe.symm (h.xe x) = x
  rw [hx]; exact h₁.xe.symm_apply_apply x

theorem exists_isPullDeg_self_pullOver : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R'), Function.Injective ρ →
    ∀ (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg ρ D D') (σ : Gal ρ),
      ∃ h : IsPullDeg (Gal.hom σ) D' D', PullOver hD h := by
  intro R R' _ _ _ _ ρ hρ D D' hD σ
  have eq : ρ = (Gal.hom σ).comp ρ := RingHom.ext fun r => (σ.2 r).symm
  obtain ⟨h₀, cp, cx⟩ := exists_cast eq hD
  obtain ⟨h, h₁, h₂⟩ := exists_self_of_comp hρ σ.1.injective hD h₀ cp cx
  refine ⟨h, h₂, fun b c hb hc => ?_⟩
  rw [hb, hc, ← proj_def, ← proj_def]
  exact h₁

end GlobalTheory.Mum.SelfPull
