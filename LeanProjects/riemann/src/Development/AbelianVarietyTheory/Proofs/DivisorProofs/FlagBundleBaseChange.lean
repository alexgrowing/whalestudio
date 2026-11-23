import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCoverOfAlterationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFlag
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBaseChangeStable

open Limits (pullback)

set_option backward.isDefEq.respectTransparency false in

theorem comp_assoc_app {X Y Z W : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (E : W.Modules) :
    (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj E) ≫
      (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app E =
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app E) ≫
      (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app E ≫ eqToHom (by rw [Category.assoc]) := by
  have e := congrArg (fun t => NatTrans.app t E) (Scheme.Modules.pseudofunctor_associativity f g h)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, eqToHom_app, Category.id_comp] at e
  calc _ = (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app E) ≫
      (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app E ≫ ((Scheme.Modules.pullbackComp f (g ≫ h)).inv.app E ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app E) ≫
        (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj E) ≫
      (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app E) := by
        simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
        erw [CategoryTheory.Functor.map_id, Category.id_comp]
    _ = _ := by rw [e]

set_option backward.isDefEq.respectTransparency false in

theorem comp_congr_app {X Y Z : Scheme.{0}} (f : X ⟶ Y) {u v : Y ⟶ Z} (w : u = v) (E : Z.Modules) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackCongr w).hom.app E) ≫
      (Scheme.Modules.pullbackComp f v).hom.app E =
    (Scheme.Modules.pullbackComp f u).hom.app E ≫ (Scheme.Modules.pullbackCongr (congrArg (f ≫ ·) w)).hom.app E := by
  subst w
  simp [Scheme.Modules.pullbackCongr]

set_option backward.isDefEq.respectTransparency false in

theorem congr_refl_app {X Y : Scheme.{0}} (f : X ⟶ Y) (h : f = f) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app M = 𝟙 _ := by
  simp [Scheme.Modules.pullbackCongr]

variable {B Y B' : Scheme.{0}} (π : Y ⟶ B) (g : B' ⟶ B)

set_option backward.isDefEq.respectTransparency false in

theorem bcIso_coh {T : Scheme.{0}} (h : T ⟶ pullback π g) (E : B.Modules) :
    (Scheme.Modules.pullbackComp h (pullback.fst π g)).hom.app ((Scheme.Modules.pullback π).obj E) ≫
      (Scheme.Modules.pullbackComp (h ≫ pullback.fst π g) π).hom.app E ≫
        (Scheme.Modules.pullbackCongr (show (h ≫ pullback.fst π g) ≫ π = (h ≫ pullback.snd π g) ≫ g by
          rw [Category.assoc, Category.assoc, pullback.condition])).hom.app E =
    (Scheme.Modules.pullback h).map (FlagBaseChange.bcIso π g E).hom ≫
      (Scheme.Modules.pullbackComp h (pullback.snd π g)).hom.app ((Scheme.Modules.pullback g).obj E) ≫
        (Scheme.Modules.pullbackComp (h ≫ pullback.snd π g) g).hom.app E := by
  rw [reassoc_of% (comp_assoc_app h (pullback.fst π g) π E), comp_assoc_app h (pullback.snd π g) g E,
    ← Functor.map_comp_assoc]
  have e : (FlagBaseChange.bcIso π g E).hom ≫ (Scheme.Modules.pullbackComp (pullback.snd π g) g).hom.app E =
      (Scheme.Modules.pullbackComp (pullback.fst π g) π).hom.app E ≫
        (Scheme.Modules.pullbackCongr pullback.condition).hom.app E := by
    simp [FlagBaseChange.bcIso]
  rw [e, Functor.map_comp_assoc, reassoc_of% (comp_congr_app h (pullback.condition (f := π) (g := g)) E)]
  simp [Scheme.Modules.pullbackCongr]

set_option backward.isDefEq.respectTransparency false in

theorem bcIso_coh_map {T : Scheme.{0}} (h : T ⟶ pullback π g) (E : B.Modules) {F : Y.Modules}
    (j : F ⟶ (Scheme.Modules.pullback π).obj E) (w : (h ≫ pullback.fst π g) ≫ π = (h ≫ pullback.snd π g) ≫ g) :
    (Scheme.Modules.pullbackComp h (pullback.fst π g)).hom.app F ≫
      (Scheme.Modules.pullback (h ≫ pullback.fst π g)).map j ≫
        (Scheme.Modules.pullbackComp (h ≫ pullback.fst π g) π).hom.app E ≫
          (Scheme.Modules.pullbackCongr w).hom.app E =
    (Scheme.Modules.pullback h).map
        ((Scheme.Modules.pullback (pullback.fst π g)).map j ≫ (FlagBaseChange.bcIso π g E).hom) ≫
      (Scheme.Modules.pullbackComp h (pullback.snd π g)).hom.app ((Scheme.Modules.pullback g).obj E) ≫
        (Scheme.Modules.pullbackComp (h ≫ pullback.snd π g) g).hom.app E := by
  have n := (Scheme.Modules.pullbackComp h (pullback.fst π g)).hom.naturality j
  simp only [Functor.comp_map] at n
  rw [← reassoc_of% n, bcIso_coh, Functor.map_comp_assoc]

set_option backward.isDefEq.respectTransparency false in

theorem match_lift {T : Scheme.{0}} (h : T ⟶ pullback π g) {g' : T ⟶ Y} {t : T ⟶ B'}
    (h₁ : h ≫ pullback.fst π g = g') (h₂ : h ≫ pullback.snd π g = t) (w : g' ≫ π = t ≫ g)
    (E : B.Modules) {F : Y.Modules} (j : F ⟶ (Scheme.Modules.pullback π).obj E) {F' : T.Modules}
    (j' : F' ⟶ (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback g).obj E))
    (e : (Scheme.Modules.pullback g').obj F ≅ F')
    (he : e.hom ≫ j' ≫ (Scheme.Modules.pullbackComp t g).hom.app E =
      (Scheme.Modules.pullback g').map j ≫ (Scheme.Modules.pullbackComp g' π).hom.app E ≫
        (Scheme.Modules.pullbackCongr w).hom.app E) :
    ∃ e' : (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback (pullback.fst π g)).obj F) ≅ F',
      e'.hom ≫ j' = (Scheme.Modules.pullback h).map
          ((Scheme.Modules.pullback (pullback.fst π g)).map j ≫ (FlagBaseChange.bcIso π g E).hom) ≫
        (Scheme.Modules.pullbackComp h (pullback.snd π g)).hom.app ((Scheme.Modules.pullback g).obj E) ≫
          (Scheme.Modules.pullbackCongr h₂).hom.app ((Scheme.Modules.pullback g).obj E) := by
  subst h₁ h₂
  refine ⟨(Scheme.Modules.pullbackComp h (pullback.fst π g)).app F ≪≫ e, ?_⟩
  rw [← cancel_mono ((Scheme.Modules.pullbackComp (h ≫ pullback.snd π g) g).hom.app E)]
  simp only [Iso.trans_hom, Iso.app_hom, Category.assoc, he]
  rw [bcIso_coh_map]
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in

theorem match_fst {T : Scheme.{0}} (h : T ⟶ pullback π g) {t : T ⟶ B'}
    (h₂ : h ≫ pullback.snd π g = t) (w : (h ≫ pullback.fst π g) ≫ π = t ≫ g)
    (E : B.Modules) {F : Y.Modules} (j : F ⟶ (Scheme.Modules.pullback π).obj E) {F' : T.Modules}
    (j' : F' ⟶ (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback g).obj E))
    (e : (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback (pullback.fst π g)).obj F) ≅ F')
    (he : e.hom ≫ j' = (Scheme.Modules.pullback h).map
          ((Scheme.Modules.pullback (pullback.fst π g)).map j ≫ (FlagBaseChange.bcIso π g E).hom) ≫
        (Scheme.Modules.pullbackComp h (pullback.snd π g)).hom.app ((Scheme.Modules.pullback g).obj E) ≫
          (Scheme.Modules.pullbackCongr h₂).hom.app ((Scheme.Modules.pullback g).obj E)) :
    ∃ e' : (Scheme.Modules.pullback (h ≫ pullback.fst π g)).obj F ≅ F',
      e'.hom ≫ j' ≫ (Scheme.Modules.pullbackComp t g).hom.app E =
        (Scheme.Modules.pullback (h ≫ pullback.fst π g)).map j ≫
          (Scheme.Modules.pullbackComp (h ≫ pullback.fst π g) π).hom.app E ≫
            (Scheme.Modules.pullbackCongr w).hom.app E := by
  subst h₂
  refine ⟨((Scheme.Modules.pullbackComp h (pullback.fst π g)).app F).symm ≪≫ e, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Category.assoc, reassoc_of% he]
  rw [congr_refl_app, Category.id_comp, ← bcIso_coh_map π g h E j w, Iso.inv_hom_id_app_assoc]

set_option backward.isDefEq.respectTransparency false in

theorem isFlagBundle_pullback : ∀ (B Y B' : Scheme.{0}) (π : Y ⟶ B) (ι : Type) (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∀ g : B' ⟶ B, IsFlagBundle (Limits.pullback.snd π g) (fun a => (Scheme.Modules.pullback g).obj (E a)) r (fun a => FlagBaseChange.pullFlag π g (fl a)) := by
  intro B Y B' π ι E r fl hfl g T t fl'
  obtain ⟨g', ⟨w, hw⟩, huniq⟩ :=
    hfl T (t ≫ g) (fun a => (fl' a).ofIso ((Scheme.Modules.pullbackComp t g).app (E a)))
  refine ⟨pullback.lift g' t w, ⟨pullback.lift_snd _ _ _, fun a i => ?_⟩, ?_⟩
  · obtain ⟨e, he⟩ := hw a i
    exact match_lift π g (pullback.lift g' t w) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) w (E a)
      ((fl a).ι i) ((fl' a).ι i) e he
  · rintro h ⟨w₀, hm⟩
    have w₁ : (h ≫ pullback.fst π g) ≫ π = t ≫ g := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, w₀]
    have e₁ : h ≫ pullback.fst π g = g' := huniq _ ⟨w₁, fun a i => by
      obtain ⟨e, he⟩ := hm a i
      exact match_fst π g h w₀ w₁ (E a) ((fl a).ι i) ((fl' a).ι i) e he⟩
    exact pullback.hom_ext (e₁.trans (pullback.lift_fst _ _ _).symm)
      (w₀.trans (pullback.lift_snd _ _ _).symm)

end GlobalTheory.FlagBaseChangeStable
