import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusEndOfPadd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.GrpCancel

theorem exists_cancel_square : ∀ (SA SB SC : Scheme.{0}) (A : Over SA) [GrpObj A] (B : Over SB) [GrpObj B] (C : Over SC) [GrpObj C] (g : SA ⟶ SB) (f : SB ⟶ SC) (a : A.left ⟶ C.left) (b : B.left ⟶ C.left) (a₂ : (G2 A).left ⟶ (G2 C).left) (b₂ : (G2 B).left ⟶ (G2 C).left), IsGrpPullback A C (g ≫ f) a → IsGrpPullback B C f b → IsSquare a a₂ → IsSquare b b₂ → ∃ (β : A.left ⟶ B.left) (β₂ : (G2 A).left ⟶ (G2 B).left), IsGrpPullback A B g β ∧ IsSquare β β₂ ∧ β ≫ b = a ∧ β₂ ≫ b₂ = a₂ := by
  intro SA SB SC A _ B _ C _ g f a b a₂ b₂ ha hb sa sb
  let β : A.left ⟶ B.left := hb.1.lift a (A.hom ≫ g) (by rw [Category.assoc]; exact ha.1.w)
  have e : β ≫ b = a := hb.1.lift_fst _ _ _
  have w : β ≫ B.hom = A.hom ≫ g := hb.1.lift_snd _ _ _
  have hβ : IsGrpPullback A B g β := IsGrpPullback.cancel hb (e.symm ▸ ha) w
  let β₂ : (G2 A).left ⟶ (G2 B).left := (lift (pushPt w (fst A A)) (pushPt w (snd A A))).left
  have s : IsSquare β β₂ :=
    ⟨congrArg (fun z => z.left) (lift_fst (pushPt w (fst A A)) (pushPt w (snd A A))),
      congrArg (fun z => z.left) (lift_snd (pushPt w (fst A A)) (pushPt w (snd A A)))⟩
  refine ⟨β, β₂, hβ, s, e, ?_⟩
  have h₁ : (β₂ ≫ b₂) ≫ (fst C C).left = a₂ ≫ (fst C C).left := by
    rw [Category.assoc, sb.1, ← Category.assoc, s.1, Category.assoc, e, sa.1]
  have h₂ : (β₂ ≫ b₂) ≫ (snd C C).left = a₂ ≫ (snd C C).left := by
    rw [Category.assoc, sb.2, ← Category.assoc, s.2, Category.assoc, e, sa.2]
  exact pullback.hom_ext h₁ h₂

end GlobalTheory.GrpCancel
