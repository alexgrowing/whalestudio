import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullDegUniqueAndComp
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullDegUniqAny

open GlobalTheory.ArcPull GlobalTheory.ArcQ GlobalTheory.PullDegUniq
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem nonempty_isPullDeg_id {φ : R →+* R'} {D : DegPre R} {D₁ D₂ : DegPre R'} (h₁ : IsPullDeg φ D D₁)
    (h₂ : IsPullDeg φ D D₂) : Nonempty (IsPullDeg (RingHom.id R') D₁ D₂) := by
  have hβ : Function.Injective (RingHom.id R') := Function.injective_id
  have h : IsPullDeg ((RingHom.id R').comp φ) D D₂ := (RingHom.id_comp φ).symm ▸ h₂
  have p₁ : IsGrpPullback D₁.P.A D.P.A (spMap φ) (proj h₁) := pull_grp h₁
  have sc : spMap (RingHom.id R') ≫ spMap φ = spMap ((RingHom.id R').comp φ) := (spMap_comp φ _).symm
  have p : IsGrpPullback D₂.P.A D.P.A (spMap (RingHom.id R') ≫ spMap φ) (proj h) := (pull_grp h).congr sc.symm rfl
  obtain ⟨Φ, e₁, e₂⟩ : ∃ Φ : D₂.P.A.left ⟶ D₁.P.A.left, Φ ≫ proj h₁ = proj h ∧
      Φ ≫ D₁.P.A.hom = D₂.P.A.hom ≫ spMap (RingHom.id R') :=
    ⟨p₁.1.lift (proj h) (D₂.P.A.hom ≫ spMap (RingHom.id R')) (p.1.w.trans (Category.assoc _ _ _).symm),
      p₁.1.lift_fst _ _ _, p₁.1.lift_snd _ _ _⟩
  have gp : IsGrpPullback D₂.P.A D₁.P.A (spMap (RingHom.id R')) Φ :=
    IsGrpPullback.cancel p₁ (p.congr rfl e₁.symm) e₂
  obtain ⟨w, hw, hr, T⟩ := FieldPull.exists_cancel_of_eq e₁ D.P.isLB D₁.P.isLB D₂.P.isLB h₁.w h.w
    ((isGen_iff _).1 h₁.w_gen) ((isGen_iff _).1 h.w_gen) sc (cubeMapOf gp).e_comm (FieldPull.pmaps_rig h₁)
    (FieldPull.pmaps_rig h)
  let xe : D₂.X ≃+ D₁.X := h.xe.trans h₁.xe.symm
  have hxe : ∀ x, h₁.xe (xe x) = h.xe x := fun x => h₁.xe.apply_symm_apply _
  have hc : ∀ x, (D₂.c x).left ≫ Φ = spMap (RingHom.id R') ≫ (D₁.c (xe x)).left := fun x => by
    apply p₁.1.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, h₁.c_pr, hxe]
      exact (h.c_pr x).trans ((congrArg (· ≫ _) sc.symm).trans (Category.assoc _ _ _))
    · rw [Category.assoc, e₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨ψW⟩ := nonempty_psiOn_pull h₁
  obtain ⟨s, hs⟩ := exists_generic_section h₁
  obtain ⟨hD, -⟩ := DvrDeg.exists_isPullDeg_of_val hβ D₁ D₂ ψW s hs gp w hw hr xe hc (fun x z J₁ J hJ₁ hJ => by
    obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' D.P.isLB z
    have sβ : jK R' ≫ spMap (RingHom.id R') = genMap hβ ≫ jK R' :=
      (Category.id_comp _).symm.trans (fracMap_sq hβ)
    have v := PsiEvenPull.psi_pull h x (𝟙 _) z hJ₀ hJ
    have v₁ := PsiEvenPull.psi_pull h₁ (xe x) (genMap hβ) z hJ₀ hJ₁
    have ag : val (h₁.psiW.psi (h.xe x)) (genMap hβ ≫ h₁.g) z J₀ = val (h.psiW.psi (h.xe x)) (𝟙 _ ≫ h.g) z J₀ :=
      ArcSpecialise.psiOn_agree h₁.psiW h.psiW _ _ _ (by
        rw [Category.assoc, h₁.g_comm, Category.assoc, h.g_comm, Category.id_comp, ← Category.assoc, ← sβ,
          Category.assoc]
        exact congrArg (jK R' ≫ ·) sc) hJ₀
    have hx : D₂.xK x ≫ Φ = genMap hβ ≫ D₁.xK (xe x) := by
      show (jK R' ≫ (D₂.c x).left) ≫ Φ = genMap hβ ≫ jK R' ≫ (D₁.c (xe x)).left
      rw [Category.assoc, hc, ← Category.assoc, sβ, Category.assoc]
    change _ = (om h₁.w z J₀ J₁ (genMap hβ ≫ D₁.xK (xe x)))⁻¹ * _ at v₁
    change _ = (om h.w z J₀ J (𝟙 _ ≫ D₂.xK x))⁻¹ * _ at v
    rw [hxe, ag, v, Category.id_comp, T _ z J₀ J₁ J hJ₀ hJ₁ hJ, hx, mul_inv, _root_.mul_assoc] at v₁
    exact (mul_left_cancel v₁).symm)
  exact ⟨hD⟩

end GlobalTheory.PullDegUniqAny

namespace GlobalTheory.Mum

theorem isPullDeg_unique_any : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D₁ D₂ : DegPre R'), Nonempty (IsPullDeg φ D D₁) → Nonempty (IsPullDeg φ D D₂) → Nonempty (IsPullDeg (RingHom.id R') D₁ D₂) :=
  fun _ _ _ _ _ _ _ _ _ _ ⟨h₁⟩ ⟨h₂⟩ => GlobalTheory.PullDegUniqAny.nonempty_isPullDeg_id h₁ h₂

end GlobalTheory.Mum
