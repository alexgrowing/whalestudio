import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult.LevelPull

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

theorem toUnit_left {S : Scheme.{0}} {T : Over S} (u : T ⟶ 𝟙_ (Over S)) : u.left = T.hom := by
  simpa using Over.w u

theorem push_inj {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {b : S' ⟶ S}
    {φ : X'.A.left ⟶ X.A.left} (hg : IsGrpPullback X'.A X.A b φ) {T : Over S'} {x y : T ⟶ X'.A}
    (e : pushPt hg.1.w x = pushPt hg.1.w y) : x = y := by
  apply Over.OverMorphism.ext
  apply hg.1.hom_ext
  · exact congrArg (fun z => z.left) e
  · rw [Over.w, Over.w]

def liftPt {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {b : S' ⟶ S}
    {φ : X'.A.left ⟶ X.A.left} (hg : IsGrpPullback X'.A X.A b φ) (p : 𝟙_ (Over S) ⟶ X.A) :
    𝟙_ (Over S') ⟶ X'.A :=
  Over.homMk (hg.1.lift (b ≫ p.left) (𝟙_ (Over S')).hom (by
    rw [Category.assoc, Over.w p]; simp)) (hg.1.lift_snd _ _ _)

theorem liftPt_push {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {b : S' ⟶ S}
    {φ : X'.A.left ⟶ X.A.left} (hg : IsGrpPullback X'.A X.A b φ) (p : 𝟙_ (Over S) ⟶ X.A) :
    (liftPt hg p).left ≫ φ = b ≫ p.left :=
  hg.1.lift_fst _ _ _

theorem push_liftPt_act {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {b : S' ⟶ S}
    {φ : X'.A.left ⟶ X.A.left} (h : X'.IsPullBy X b φ) (p : 𝟙_ (Over S) ⟶ X.A) {T : Over S'}
    (u : T ⟶ 𝟙_ (Over S')) (a : 𝓞 F) :
    pushPt h.grp.1.w (u ≫ liftPt h.grp p ≫ X'.rm.act a) =
      toUnit (Over.mk (T.hom ≫ b)) ≫ p ≫ X.rm.act a := by
  apply Over.OverMorphism.ext
  show (u ≫ liftPt h.grp p ≫ X'.rm.act a).left ≫ φ = (toUnit (Over.mk (T.hom ≫ b)) ≫ p ≫ X.rm.act a).left
  simp only [Over.comp_left, Category.assoc]
  rw [h.act a, ← Category.assoc (liftPt h.grp p).left, liftPt_push, toUnit_left, toUnit_left]
  simp

section
variable {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {b : S' ⟶ S}
    {φ : X'.A.left ⟶ X.A.left} (hg : IsGrpPullback X'.A X.A b φ) {T : Over S'}

theorem push_mul (x y : T ⟶ X'.A) : pushPt hg.1.w (x * y) = pushPt hg.1.w x * pushPt hg.1.w y :=
  map_mul (pushHom hg T) x y

theorem push_one : pushPt hg.1.w (1 : T ⟶ X'.A) = 1 := map_one (pushHom hg T)

theorem push_pow (x : T ⟶ X'.A) (n : ℕ) : pushPt hg.1.w (x ^ n) = pushPt hg.1.w x ^ n :=
  map_pow (pushHom hg T) x n
end

theorem exists_level_pull : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {b : S' ⟶ S}
    {φ : X'.A.left ⟶ X.A.left}, X'.IsPullBy X b φ → ∀ {N : ℕ} (α : X.Level N),
    ∃ α' : X'.Level N, ∀ i, (α'.pt i).left ≫ φ = b ≫ (α.pt i).left := by
  intro F _ _ 𝔠 S S' X X' b φ h N α
  refine ⟨⟨fun i => liftPt h.grp (α.pt i), ?_, ?_, ?_⟩, fun i => liftPt_push h.grp _⟩
  · intro i
    apply push_inj h.grp
    have e2 : pushPt h.grp.1.w (liftPt h.grp (α.pt i)) =
        toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ b)) ≫ α.pt i := by
      apply Over.OverMorphism.ext
      show (liftPt h.grp (α.pt i)).left ≫ φ = (toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ b)) ≫ α.pt i).left
      rw [liftPt_push, Over.comp_left, toUnit_left]
      simp
    have e3 : (toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ b)) ≫ α.pt i) ^ N =
        toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ b)) ≫ α.pt i ^ N :=
      (map_pow (preHom (G := X.A) (toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ b)))) (α.pt i) N).symm
    rw [push_pow h.grp, e2, e3, α.tors i, push_one h.grp]
    exact MonObj.comp_one _
  · intro Ω _ _ t a c hyp
    apply α.inj Ω (t ≫ b) a c
    have e := congrArg (pushPt h.grp.1.w) hyp
    rw [push_mul h.grp, push_one h.grp, push_liftPt_act h (α.pt 0), push_liftPt_act h (α.pt 1)] at e
    exact e
  · intro Ω _ _ t y hy
    obtain ⟨a, c, hac⟩ := α.surj Ω (t ≫ b) (pushPt h.grp.1.w y) (by
      rw [← push_pow h.grp, hy, push_one h.grp])
    refine ⟨a, c, push_inj h.grp ?_⟩
    rw [push_mul h.grp, push_liftPt_act h (α.pt 0), push_liftPt_act h (α.pt 1)]
    exact hac

end GlobalTheory.RealMult.LevelPull
