import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.PullAction

section
open MonObj

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem exists_lift_end (h : IsGrpPullback G' G f φ) (u : G ⟶ G) [IsMonHom u] :
    ∃ v : G' ⟶ G', IsMonHom v ∧ v.left ≫ φ = φ ≫ u.left := by
  let v : G' ⟶ G' := Over.homMk (h.1.lift (φ ≫ u.left) G'.hom (by rw [Category.assoc, Over.w u, h.1.w]))
    (h.1.lift_snd _ _ _)
  have hv : v.left ≫ φ = φ ≫ u.left := h.1.lift_fst _ _ _
  have inj : ∀ (T : Over S') (x y : T ⟶ G'), pushPt h.1.w x = pushPt h.1.w y → x = y := fun T x y e =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun z => z.left) e) (by rw [Over.w x, Over.w y]))
  have pa : ∀ (T : Over S') (x : T ⟶ G'), pushPt h.1.w (x ≫ v) = pushPt h.1.w x ≫ u := fun T x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hv, Category.assoc])
  have pm : ∀ (T : Over S') (x y : T ⟶ G'), pushPt h.1.w (x * y) = pushPt h.1.w x * pushPt h.1.w y := fun T x y =>
    Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm
  have p1 : ∀ (T : Over S'), pushPt h.1.w (1 : T ⟶ G') = 1 := fun T => by
    have := pm T 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  have hm : ∀ (T : Over S') (x y : T ⟶ G'), (x * y) ≫ v = (x ≫ v) * (y ≫ v) := fun T x y => inj T _ _ (by
    rw [pa, pm, pm, pa, pa, MonObj.mul_comp])
  have h1 : ∀ (T : Over S'), (1 : T ⟶ G') ≫ v = 1 := fun T => inj T _ _ (by
    rw [pa, p1, MonObj.one_comp])
  refine ⟨v, ⟨?_, ?_⟩, hv⟩
  · have := h1 (𝟙_ _)
    simpa [Hom.one_def] using this
  · have := hm (G' ⊗ G') (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at this
    rw [this]
    congr 1

end

theorem exists_action_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (W : Scheme.{0}) (w : W ⟶ Xo.XF c) (G₀ : Over W) [GrpObj G₀] (β₀ : G₀.left ⟶ Xo.univ.t.G.left), IsGrpPullback G₀ Xo.univ.t.G (w ≫ pullback.fst _ _) β₀ → ∃ f₀ : 𝓞 E → (G₀ ⟶ G₀), (∀ a, IsMonHom (f₀ a) ∧ (f₀ a).left ≫ β₀ = β₀ ≫ (Xo.univ.t.act.act a).left) ∧ ∀ (T : Scheme.{0}) (x : T ⟶ W) (tT : SAB H T) (mm : SABMap tT Xo.univ.t ((x ≫ w) ≫ pullback.fst _ _)), ∃ γ : tT.G.left ⟶ G₀.left, IsGrpPullback tT.G G₀ x γ ∧ γ ≫ β₀ = mm.φ ∧ LBIso tT.PP.L ((Xo.univ.t.PP.L.pull β₀).pull γ) ∧ ∀ a, (tT.act.act a).left ≫ γ = γ ≫ (f₀ a).left := by
  intro E _ _ _ H Dw l Xo c W w G₀ _ β₀ hβ
  have key : ∀ a : 𝓞 E, ∃ v : G₀ ⟶ G₀, IsMonHom v ∧ v.left ≫ β₀ = β₀ ≫ (Xo.univ.t.act.act a).left := fun a =>
    haveI := Xo.univ.t.act.hom a
    exists_lift_end hβ _
  choose f₀ hf₀ using key
  refine ⟨f₀, hf₀, fun T x tT mm => ?_⟩
  have hp := hβ.1
  let γ : tT.G.left ⟶ G₀.left := hp.lift mm.φ (tT.G.hom ≫ x)
    (mm.cart.1.w.trans (by simp only [Category.assoc]))
  have hγ : γ ≫ β₀ = mm.φ := hp.lift_fst _ _ _
  have hw : γ ≫ G₀.hom = tT.G.hom ≫ x := hp.lift_snd _ _ _
  have hL : LBIso tT.PP.L (Xo.univ.t.PP.L.pull mm.φ) := mm.lin.imp fun _ h => h.1
  have hU := Xo.univ.t.PP.isLB
  refine ⟨γ, hβ.cancel (by rw [hγ, ← Category.assoc]; exact mm.cart) hw, hγ,
    LBIso.trans tT.PP.isLB (pull_isLB hU _) (pull_isLB (pull_isLB hU _) _) hL
      (GlobalTheory.GenSpread.lbIso_pull_pull hU γ hγ.symm), fun a => ?_⟩
  apply hp.hom_ext
  · rw [Category.assoc, hγ, mm.act, Category.assoc γ, (hf₀ a).2, ← Category.assoc γ, hγ]
  · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w, hw]

end GlobalTheory.PullAction
