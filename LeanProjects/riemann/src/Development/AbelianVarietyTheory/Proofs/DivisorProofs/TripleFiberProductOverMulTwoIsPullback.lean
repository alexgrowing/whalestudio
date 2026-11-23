import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulIncl

set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwoTors.TripleProd

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

def pt {T : Over S} (a b c : T ⟶ A) (h₁ : a ≫ sq A = b ≫ sq A) (h₂ : b ≫ sq A = c ≫ sq A) : T ⟶ tripO A :=
  Over.homMk (GlobalTheory.PolRoot.tri (sq A).left a.left b.left c.left (congrArg CommaMorphism.left h₁)
    (congrArg CommaMorphism.left h₂)) (by
      show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫ A.hom = _
      rw [GlobalTheory.PolRoot.tri, pullback.lift_fst_assoc, pullback.lift_fst_assoc, Over.w])

theorem pt_t₁ {T : Over S} (a b c : T ⟶ A) (h₁ h₂) : pt a b c h₁ h₂ ≫ t₁ A = a :=
  Over.OverMorphism.ext (by
    show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ = _
    rw [GlobalTheory.PolRoot.tri, pullback.lift_fst_assoc, pullback.lift_fst])

theorem pt_t₂ {T : Over S} (a b c : T ⟶ A) (h₁ h₂) : pt a b c h₁ h₂ ≫ t₂ A = b :=
  Over.OverMorphism.ext (by
    show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _ = _
    rw [GlobalTheory.PolRoot.tri, pullback.lift_fst_assoc, pullback.lift_snd])

theorem pt_t₃ {T : Over S} (a b c : T ⟶ A) (h₁ h₂) : pt a b c h₁ h₂ ≫ t₃ A = c :=
  Over.OverMorphism.ext (by
    show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.snd _ _ ≫ pullback.snd _ _ = _
    rw [GlobalTheory.PolRoot.tri, pullback.lift_snd_assoc, pullback.lift_snd])

theorem ext₃ {T : Over S} {m n : T ⟶ tripO A} (h₁ : m ≫ t₁ A = n ≫ t₁ A) (h₂ : m ≫ t₂ A = n ≫ t₂ A)
    (h₃ : m ≫ t₃ A = n ≫ t₃ A) : m = n := by
  have e₁ : m.left ≫ pullback.fst _ _ ≫ pullback.fst _ _ = n.left ≫ pullback.fst _ _ ≫ pullback.fst _ _ :=
    congrArg CommaMorphism.left h₁
  have e₂ : m.left ≫ pullback.fst _ _ ≫ pullback.snd _ _ = n.left ≫ pullback.fst _ _ ≫ pullback.snd _ _ :=
    congrArg CommaMorphism.left h₂
  have e₃ : m.left ≫ pullback.snd _ _ ≫ pullback.snd _ _ = n.left ≫ pullback.snd _ _ ≫ pullback.snd _ _ :=
    congrArg CommaMorphism.left h₃
  have e₄ := e₂
  rw [pullback.condition] at e₄
  refine Over.OverMorphism.ext (pullback.hom_ext (pullback.hom_ext ?_ ?_) (pullback.hom_ext ?_ ?_))
  · exact (Category.assoc _ _ _).trans (e₁.trans (Category.assoc _ _ _).symm)
  · exact (Category.assoc _ _ _).trans (e₂.trans (Category.assoc _ _ _).symm)
  · exact (Category.assoc _ _ _).trans (e₄.trans (Category.assoc _ _ _).symm)
  · exact (Category.assoc _ _ _).trans (e₃.trans (Category.assoc _ _ _).symm)

theorem comp_ψ_fst {T : Over S} (m : T ⟶ tripO A) :
    ((m ≫ ψ A) ≫ fst _ _) ≫ incl A = (m ≫ t₁ A)⁻¹ * (m ≫ t₂ A) := by
  rw [Category.assoc, Category.assoc, ψ, lift_fst_assoc, dif_incl, MonObj.comp_mul, GrpObj.comp_inv]

theorem comp_ψ_snd {T : Over S} (m : T ⟶ tripO A) :
    ((m ≫ ψ A) ≫ snd _ _) ≫ incl A = (m ≫ t₂ A)⁻¹ * (m ≫ t₃ A) := by
  rw [Category.assoc, Category.assoc, ψ, lift_snd_assoc, dif_incl, MonObj.comp_mul, GrpObj.comp_inv]

theorem ext₂ {T : Over S} {m n : T ⟶ tripO A} (h₁ : m ≫ t₁ A = n ≫ t₁ A) (h : m ≫ ψ A = n ≫ ψ A) : m = n := by
  have e₂ := comp_ψ_fst m
  have e₃ := comp_ψ_snd m
  rw [h, comp_ψ_fst, h₁] at e₂
  have h₂ : m ≫ t₂ A = n ≫ t₂ A := (mul_left_cancel e₂).symm
  rw [h, comp_ψ_snd, h₂] at e₃
  exact ext₃ h₁ h₂ (mul_left_cancel e₃).symm

theorem mul_sq {T : Over S} (a : T ⟶ A) (x : T ⟶ Two A) : a ≫ sq A = (a * (x ≫ incl A)) ≫ sq A := by
  rw [comp_sq, comp_sq, mul_pow, incl_sq, _root_.mul_one]

theorem exists_pt {T : Over S} (a : T ⟶ A) (q : T ⟶ Two A ⊗ Two A) :
    ∃ m : T ⟶ tripO A, m ≫ t₁ A = a ∧ m ≫ ψ A = q := by
  refine ⟨pt a (a * ((q ≫ fst _ _) ≫ incl A)) ((a * ((q ≫ fst _ _) ≫ incl A)) * ((q ≫ snd _ _) ≫ incl A))
    (mul_sq _ _) (mul_sq _ _), pt_t₁ _ _ _ _ _, ?_⟩
  refine CartesianMonoidalCategory.hom_ext _ _ (two_ext ?_) (two_ext ?_)
  · rw [comp_ψ_fst, pt_t₁, pt_t₂, inv_mul_cancel_left]
  · rw [comp_ψ_snd, pt_t₂, pt_t₃, inv_mul_cancel_left]

theorem isPullback {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] :
    IsPullback (t₁ A).left (ψ A).left A.hom (Two A ⊗ Two A).hom := by
  have w : (t₁ A).left ≫ A.hom = (ψ A).left ≫ (Two A ⊗ Two A).hom := (Over.w _).trans (Over.w _).symm
  have key : ∀ s : PullbackCone A.hom (Two A ⊗ Two A).hom, ∃ l : s.pt ⟶ (tripO A).left,
      l ≫ (t₁ A).left = s.fst ∧ l ≫ (ψ A).left = s.snd := fun s => by
    obtain ⟨m, h₁, h₂⟩ := exists_pt (T := Over.mk (s.fst ≫ A.hom)) (Over.homMk s.fst rfl)
      (Over.homMk s.snd s.condition.symm)
    exact ⟨m.left, congrArg CommaMorphism.left h₁, congrArg CommaMorphism.left h₂⟩
  choose l hl₁ hl₂ using key
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk w l hl₁ hl₂ fun s m h₁ h₂ => ?_⟩⟩
  have hw : ∀ k : s.pt ⟶ (tripO A).left, k ≫ (t₁ A).left = s.fst → k ≫ (tripO A).hom = s.fst ≫ A.hom :=
    fun k hk => by rw [← hk, Category.assoc, Over.w]
  have e : (Over.homMk m (hw m h₁) : Over.mk (s.fst ≫ A.hom) ⟶ tripO A) = Over.homMk (l s) (hw _ (hl₁ s)) :=
    ext₂ (Over.OverMorphism.ext (h₁.trans (hl₁ s).symm)) (Over.OverMorphism.ext (h₂.trans (hl₂ s).symm))
  exact congrArg CommaMorphism.left e

end GlobalTheory.TwoTors.TripleProd
