import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacter

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolRoot

def Root {S T : Scheme.{0}} (A : Over S) [GrpObj A] (P : LB (G2 A).left) (t : T ⟶ S) : Prop :=
  ∃ (B : Over T) (_ : GrpObj B) (_ : IsCommMonObj B) (β : B.left ⟶ A.left) (β₂ : (G2 B).left ⟶ (G2 A).left),
    IsGrpPullback B A t β ∧ IsSquare β β₂ ∧ ∃ L : LB B.left, L.IsLB ∧ LBIso (abelian₂ B L) (P.pull β₂)

theorem Root.comp {S T T' : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) {P : LB (G2 A).left}
    {t : T ⟶ S} (h : Root A P t) (σ : T' ⟶ T) : Root A P (σ ≫ t) := by
  obtain ⟨A', _, _, β, β₂, hβ, hsq, L, hL, H⟩ := h
  have hA' : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hβ
  obtain ⟨B', _, φ, hφ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A' σ
  have hB' : IsAbelianScheme B' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA' hφ
  haveI : IsCommMonObj B' := hB'.comm
  let V := lift (pushPt hφ.1.w (fst B' B')) (pushPt hφ.1.w (snd B' B'))
  have hV : IsSquare φ V.left := GlobalTheory.LamPull.exists_isSquare hφ.1.w
  refine ⟨B', inferInstance, inferInstance, φ ≫ β, V.left ≫ β₂, hφ.comp hβ,
    GlobalTheory.ZM.SiegPull.isSquare_comp hV hsq, L.pull φ, pull_isLB hL φ, ?_⟩
  refine LBIso.chartPull
    (chartPullLinComb L φ _ _ _ V.left fun I => psum_push hφ _ _ V (fun i => ?_) I.down)
    (chartPullSame P (fun _ : PUnit => V.left ≫ β₂) (fun _ => β₂) (fun _ => 1) V.left fun _ => rfl) H
  fin_cases i <;> simp [V, x2]

def tri {X Y T : Scheme.{0}} (f : X ⟶ Y) (a b c : T ⟶ X) (h₁ : a ≫ f = b ≫ f) (h₂ : b ≫ f = c ≫ f) :
    T ⟶ GlobalTheory.LBDescent.Triple f :=
  pullback.lift (pullback.lift a b h₁) (pullback.lift b c h₂) (by rw [pullback.lift_snd, pullback.lift_fst])

def TriCocycle {X Y : Scheme.{0}} (f : X ⟶ Y) (D : Γ(GlobalTheory.LBDescent.Triple f, ⊤)ˣ) : Prop :=
  ∀ (T : Scheme.{0}) (a b c d : T ⟶ X) (h₁ : a ≫ f = b ≫ f) (h₂ : b ≫ f = c ≫ f) (h₃ : c ≫ f = d ≫ f),
    GlobalTheory.CharKer.pullTop (tri f a b c h₁ h₂) D * GlobalTheory.CharKer.pullTop (tri f a c d (h₁.trans h₂) h₃) D =
      GlobalTheory.CharKer.pullTop (tri f b c d h₂ h₃) D * GlobalTheory.CharKer.pullTop (tri f a b d h₁ (h₂.trans h₃)) D

def KillsSq {X Y : Scheme.{0}} (f : X ⟶ Y) (D : Γ(GlobalTheory.LBDescent.Triple f, ⊤)ˣ) (u : Γ(pullback f f, ⊤)ˣ) : Prop :=
  D ^ 2 * GlobalTheory.CharKer.pullTop (pullback.fst (pullback.snd f f) (pullback.fst f f)) u *
      GlobalTheory.CharKer.pullTop (pullback.snd (pullback.snd f f) (pullback.fst f f)) u =
    GlobalTheory.CharKer.pullTop (GlobalTheory.LBDescent.pr13 f) u

end GlobalTheory.PolRoot
