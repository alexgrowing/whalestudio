import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBundleGenericFibreDescent

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj.GenPull

theorem pull_comp_iso {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {F : Y ⟶ X} (H : LBIso M (L.pull F)) (h : Z ⟶ Y) :
    LBIso (M.pull h) (L.pull (h ≫ F)) :=
  LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M h h rfl) (chartPullSame L _ _ _ h fun _ => rfl) H

theorem pull_congr_iso {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {a b : Y ⟶ X} (e : a = b) :
    LBIso (L.pull a) (L.pull b) := e ▸ GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hL a)

theorem pull_pull_iso {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (b : Z ⟶ Y) :
    LBIso ((L.pull a).pull b) (L.pull (b ≫ a)) :=
  pull_comp_iso (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hL a)) b

theorem pull_id_iso {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L (L.pull (𝟙 X)) :=
  LBIso.chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) (GlobalTheory.PolBaseChange.lbIso_refl hL)

end GlobalTheory.TInj.GenPull

open GlobalTheory.TInj.GenPull in

theorem GlobalTheory.TInj.overPt_genPull : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (J' : Ideal V) (D₀ : DegData R J) (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (U₀ : Unif J D₀ A₀ G₀) (f : R →+* V) (D : DegData V J') (hD : IsPullDeg f D₀.toPre D.toPre) (A : PolAV (Sp (FractionRing V))) (U : Unif J' D A ((Over.pullback (specOf f)).obj G₀)), IsPullUnif f hD (Iso.refl _) U₀ U → ∀ (y₀ : Sp (FractionRing R) ⟶ X) (α₀ : A₀.A.left ⟶ c.A.left), OverPt c A₀ y₀ α₀ → ∀ κ : Sp (FractionRing V) ⟶ Sp (FractionRing R), κ ≫ jK R = jK V ≫ spMap f → ∃ α : A.A.left ⟶ c.A.left, OverPt c A (κ ≫ y₀) α ∧ ∀ (Z : Scheme.{0}) (x : Z ⟶ A.A.left) (x₀ : Z ⟶ A₀.A.left), x ≫ U.gen.inv.left ≫ pullback.fst ((Over.pullback (specOf f)).obj G₀).hom (jK V) ≫ pullback.fst G₀.hom (specOf f) = x₀ ≫ U₀.gen.inv.left ≫ pullback.fst G₀.hom (jK R) → x ≫ α = x₀ ≫ α₀ := by
  intro X g n B _ ζ sX c R _ _ V _ _ J J' D₀ A₀ G₀ _ _ U₀ f D hD A U hU y₀ α₀ hO κ hκ
  let G := (Over.pullback (specOf f)).obj G₀
  let p := pullback.fst G.hom (jK V)
  let q := pullback.fst G₀.hom (specOf f)
  let p₀ := pullback.fst G₀.hom (jK R)
  have hsq : jK V ≫ specOf f = κ ≫ jK R := hκ.symm
  let κG : pullback G.hom (jK V) ⟶ pullback G₀.hom (jK R) :=
    pullback.lift (p ≫ q) (pullback.snd _ _ ≫ κ) (by
      have c1 : q ≫ G₀.hom = G.hom ≫ specOf f := pullback.condition
      have c2 : p ≫ G.hom = pullback.snd G.hom (jK V) ≫ jK V := pullback.condition
      rw [Category.assoc, c1, ← Category.assoc, c2, Category.assoc, hsq, Category.assoc])
  have hκf : κG ≫ p₀ = p ≫ q := pullback.lift_fst _ _ _
  have w : κG ≫ ((Over.pullback (jK R)).obj G₀).hom = ((Over.pullback (jK V)).obj G).hom ≫ κ :=
    pullback.lift_snd _ _ _
  have hκG : IsGrpPullback ((Over.pullback (jK V)).obj G) ((Over.pullback (jK R)).obj G₀) κ κG :=
    (isGrpPullback_pullback G₀ (jK R)).cancel
      (((isGrpPullback_pullback G (jK V)).comp (isGrpPullback_pullback G₀ (specOf f))).congr hsq hκf.symm) w
  have : IsMonHom U.gen.hom := U.gen_hom
  have : IsMonHom U₀.gen.hom := U₀.gen_hom
  have : IsMonHom U.gen.symm.hom := show IsMonHom U.gen.inv by infer_instance
  have hu : IsGrpPullback A.A ((Over.pullback (jK V)).obj G) (𝟙 _) U.gen.inv.left := isGrpPullback_of_iso U.gen.symm
  have hg : IsGrpPullback ((Over.pullback (jK R)).obj G₀) A₀.A (𝟙 _) U₀.gen.hom.left := isGrpPullback_of_iso U₀.gen
  let π : A.A.left ⟶ A₀.A.left := U.gen.inv.left ≫ κG ≫ U₀.gen.hom.left
  have hπ : IsGrpPullback A.A A₀.A κ π := (hu.comp (hκG.comp hg)).congr (by simp) rfl
  obtain ⟨hO₁, α₀₂, sα₀, hΛ₀⟩ := hO

  have hLG : U.LG.L.IsLB := U.LG.isLB
  have hLG₀ : U₀.LG.L.IsLB := U₀.LG.isLB
  obtain ⟨wL, hwL, -⟩ := hU.lg
  have E1 : LBIso (A.L.pull U.gen.hom.left) (U.LG.L.pull p) := U.ext
  have E2 : LBIso (U.LG.L.pull p) (U₀.LG.L.pull (p ≫ (Iso.refl G).hom.left ≫ q)) := pull_comp_iso ⟨wL, hwL⟩ p
  have E4 : LBIso (U₀.LG.L.pull (p ≫ (Iso.refl G).hom.left ≫ q)) (U₀.LG.L.pull (κG ≫ p₀)) :=
    pull_congr_iso hLG₀ (by rw [hκf, Iso.refl_hom, Over.id_left, Category.id_comp])
  have E3 : LBIso ((A₀.L.pull U₀.gen.hom.left).pull κG) (U₀.LG.L.pull (κG ≫ p₀)) := pull_comp_iso U₀.ext κG
  have E5 := pull_pull_iso A₀.isLB U₀.gen.hom.left κG
  have hA₀g := pull_isLB A₀.isLB U₀.gen.hom.left
  have X1 : LBIso (A.L.pull U.gen.hom.left) (A₀.L.pull (κG ≫ U₀.gen.hom.left)) :=
    LBIso.trans (pull_isLB A.isLB _) (pull_isLB hLG _) (pull_isLB A₀.isLB _) E1
      (LBIso.trans (pull_isLB hLG _) (pull_isLB hLG₀ _) (pull_isLB A₀.isLB _) E2
        (LBIso.trans (pull_isLB hLG₀ _) (pull_isLB hLG₀ _) (pull_isLB A₀.isLB _) E4
          (LBIso.trans (pull_isLB hLG₀ _) (pull_isLB hA₀g _) (pull_isLB A₀.isLB _) E3.symm E5)))
  have X2 : LBIso ((A.L.pull U.gen.hom.left).pull U.gen.inv.left) (A₀.L.pull π) := pull_comp_iso X1 _
  have X3 : LBIso A.L ((A.L.pull U.gen.hom.left).pull U.gen.inv.left) :=
    LBIso.trans A.isLB (pull_isLB A.isLB _) (pull_isLB (pull_isLB A.isLB _) _) (pull_id_iso A.isLB)
      (LBIso.trans (pull_isLB A.isLB _) (pull_isLB A.isLB _) (pull_isLB (pull_isLB A.isLB _) _)
        (pull_congr_iso A.isLB (by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]))
        (pull_pull_iso A.isLB _ _).symm)
  have hA : LBIso A.L (A₀.L.pull π) :=
    LBIso.trans A.isLB (pull_isLB (pull_isLB A.isLB _) _) (pull_isLB A₀.isLB _) X3 X2
  have sπ := GlobalTheory.LamPull.exists_isSquare hπ.1.w
  have hΛ := GlobalTheory.LamPull.lbIso_lam_pull hπ A₀.isLB A.isLB hA sπ
  have hΛA : (abelian₂ A.A A.L).IsLB := DVR.linComb_isLB _ A.isLB _ _
  have hΛA₀ : (abelian₂ A₀.A A₀.L).IsLB := DVR.linComb_isLB _ A₀.isLB _ _
  refine ⟨π ≫ α₀, ⟨hπ.comp hO₁, _ ≫ α₀₂, ⟨?_, ?_⟩,
    LBIso.trans hΛA (pull_isLB hΛA₀ _) (pull_isLB c.isLB _) hΛ (pull_comp_iso hΛ₀ _)⟩, ?_⟩
  · rw [Category.assoc, sα₀.1, ← Category.assoc, sπ.1, Category.assoc]
  · rw [Category.assoc, sα₀.2, ← Category.assoc, sπ.2, Category.assoc]
  · intro Z x x₀ hx
    have : Mono (jK R) := GlobalTheory.GenericBundleDescent.mono_jK R
    have : Mono p₀ := pullback.fst_of_mono
    have h1 : x ≫ U.gen.inv.left ≫ κG = x₀ ≫ U₀.gen.inv.left := by
      apply (cancel_mono p₀).1
      simp only [Category.assoc, hκf]
      exact hx
    show x ≫ (U.gen.inv.left ≫ κG ≫ U₀.gen.hom.left) ≫ α₀ = x₀ ≫ α₀
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc, Category.assoc x, h1]
    simp only [Category.assoc]
    rw [← Category.assoc U₀.gen.inv.left, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.id_comp]
