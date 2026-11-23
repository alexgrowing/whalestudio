import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcFlag
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CovTest GlobalTheory.Published

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTest.BCFlag

theorem pc_assoc {X Y Z W : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (M : W.Modules) :
    (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
        (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M =
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) ≫
        (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M ≫
          (Scheme.Modules.pullbackCongr (Category.assoc f g h).symm).hom.app M := by
  have := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity f g h) M
  simp at this
  have e2 := congrArg (fun x => (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) ≫
    (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M ≫ x) this
  simp only [Iso.hom_inv_id_app_assoc, ← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app] at e2
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at e2
  rw [e2]
  simp [Scheme.Modules.pullbackCongr, eqToHom_app]

theorem pc_congr {T P B : Scheme.{0}} (f : T ⟶ P) {u v : P ⟶ B} (c : u = v) {k : T ⟶ B} (h₁ : f ≫ u = k)
    (h₂ : f ≫ v = k) (M : B.Modules) :
    (Scheme.Modules.pullbackComp f u).hom.app M ≫ (Scheme.Modules.pullbackCongr h₁).hom.app M =
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackCongr c).hom.app M) ≫
        (Scheme.Modules.pullbackComp f v).hom.app M ≫ (Scheme.Modules.pullbackCongr h₂).hom.app M := by
  subst c h₁
  simp [Scheme.Modules.pullbackCongr]

theorem congr_trans' {T B : Scheme.{0}} {u v k : T ⟶ B} (c : u = v) (d : v = k) (M : B.Modules) :
    (Scheme.Modules.pullbackCongr c).hom.app M ≫ (Scheme.Modules.pullbackCongr d).hom.app M =
      (Scheme.Modules.pullbackCongr (c.trans d)).hom.app M := by
  subst c d
  simp [Scheme.Modules.pullbackCongr]

theorem pc_coh {T P Y B' B : Scheme.{0}} (f : T ⟶ P) (a : P ⟶ Y) (b : P ⟶ B') (π : Y ⟶ B) (g : B' ⟶ B)
    (cond : a ≫ π = b ≫ g) (h : T ⟶ Y) (t : T ⟶ B') (ha : f ≫ a = h) (hb : f ≫ b = t) (w : h ≫ π = t ≫ g)
    (E : B.Modules) :
    (Scheme.Modules.pullbackComp f a).hom.app ((Scheme.Modules.pullback π).obj E) ≫
        (Scheme.Modules.pullbackCongr ha).hom.app ((Scheme.Modules.pullback π).obj E) ≫
          (Scheme.Modules.pullbackComp h π).hom.app E ≫ (Scheme.Modules.pullbackCongr w).hom.app E =
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp a π).hom.app E ≫
          (Scheme.Modules.pullbackCongr cond).hom.app E ≫ (Scheme.Modules.pullbackComp b g).inv.app E) ≫
        (Scheme.Modules.pullbackComp f b).hom.app ((Scheme.Modules.pullback g).obj E) ≫
          (Scheme.Modules.pullbackCongr hb).hom.app ((Scheme.Modules.pullback g).obj E) ≫
            (Scheme.Modules.pullbackComp t g).hom.app E := by
  subst ha hb
  have e1 : (Scheme.Modules.pullbackCongr (rfl : f ≫ a = f ≫ a)).hom.app ((Scheme.Modules.pullback π).obj E) = 𝟙 _ := by
    simp [Scheme.Modules.pullbackCongr]
  have e2 : (Scheme.Modules.pullbackCongr (rfl : f ≫ b = f ≫ b)).hom.app ((Scheme.Modules.pullback g).obj E) = 𝟙 _ := by
    simp [Scheme.Modules.pullbackCongr]
  rw [e1, e2, Category.id_comp, Category.id_comp, reassoc_of% (pc_assoc f a π E), pc_assoc f b g E,
    congr_trans']
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc (Scheme.Modules.pullback f) ((Scheme.Modules.pullbackComp b g).inv.app E)]
  erw [Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [pc_congr f cond _ (Category.assoc f b g).symm]

theorem step_key {T Y B' B : Scheme.{0}} (π : Y ⟶ B) (g : B' ⟶ B) (f : T ⟶ pullback π g) (h : T ⟶ Y) (t : T ⟶ B')
    (ha : f ≫ pullback.fst π g = h) (hb : f ≫ pullback.snd π g = t) (w : h ≫ π = t ≫ g) (E : B.Modules)
    (F : Y.Modules) (ιF : F ⟶ (Scheme.Modules.pullback π).obj E) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback (pullback.fst π g)).map ιF ≫ (bcIso π g E).hom) ≫
        (Scheme.Modules.pullbackComp f (pullback.snd π g)).hom.app ((Scheme.Modules.pullback g).obj E) ≫
          (Scheme.Modules.pullbackCongr hb).hom.app ((Scheme.Modules.pullback g).obj E) ≫
            (Scheme.Modules.pullbackComp t g).hom.app E =
      (Scheme.Modules.pullbackComp f (pullback.fst π g)).hom.app F ≫
        (Scheme.Modules.pullbackCongr ha).hom.app F ≫ (Scheme.Modules.pullback h).map ιF ≫
          (Scheme.Modules.pullbackComp h π).hom.app E ≫ (Scheme.Modules.pullbackCongr w).hom.app E := by
  rw [← (Scheme.Modules.pullbackCongr ha).hom.naturality_assoc,
    ← (Scheme.Modules.pullbackComp f (pullback.fst π g)).hom.naturality_assoc,
    pc_coh f (pullback.fst π g) (pullback.snd π g) π g pullback.condition h t ha hb w E]
  simp only [bcIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, CategoryTheory.Functor.map_comp,
    Category.assoc, Functor.comp_map]

theorem step_exists {T Y B' B : Scheme.{0}} (π : Y ⟶ B) (g : B' ⟶ B) (f : T ⟶ pullback π g) (h : T ⟶ Y) (t : T ⟶ B')
    (ha : f ≫ pullback.fst π g = h) (hb : f ≫ pullback.snd π g = t) (w : h ≫ π = t ≫ g) (E : B.Modules)
    (F : Y.Modules) (ιF : F ⟶ (Scheme.Modules.pullback π).obj E) (G : T.Modules)
    (ιG : G ⟶ (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback g).obj E))
    (e : (Scheme.Modules.pullback h).obj F ≅ G)
    (hee : e.hom ≫ ιG ≫ (Scheme.Modules.pullbackComp t g).hom.app E =
      (Scheme.Modules.pullback h).map ιF ≫ (Scheme.Modules.pullbackComp h π).hom.app E ≫
        (Scheme.Modules.pullbackCongr w).hom.app E) :
    ((Scheme.Modules.pullbackComp f (pullback.fst π g)).app F ≪≫
        (Scheme.Modules.pullbackCongr ha).app F ≪≫ e).hom ≫ ιG =
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback (pullback.fst π g)).map ιF ≫ (bcIso π g E).hom) ≫
        (Scheme.Modules.pullbackComp f (pullback.snd π g)).hom.app ((Scheme.Modules.pullback g).obj E) ≫
          (Scheme.Modules.pullbackCongr hb).hom.app ((Scheme.Modules.pullback g).obj E) := by
  rw [← cancel_mono ((Scheme.Modules.pullbackComp t g).hom.app E)]
  simp only [Iso.trans_hom, Iso.app_hom, Category.assoc]
  rw [hee, step_key π g f h t ha hb w E F ιF]

theorem step_unique {T Y B' B : Scheme.{0}} (π : Y ⟶ B) (g : B' ⟶ B) (f : T ⟶ pullback π g) (t : T ⟶ B')
    (hb : f ≫ pullback.snd π g = t) (w : (f ≫ pullback.fst π g) ≫ π = t ≫ g) (E : B.Modules)
    (F : Y.Modules) (ιF : F ⟶ (Scheme.Modules.pullback π).obj E) (G : T.Modules)
    (ιG : G ⟶ (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback g).obj E))
    (e : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback (pullback.fst π g)).obj F) ≅ G)
    (hee : e.hom ≫ ιG =
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback (pullback.fst π g)).map ιF ≫ (bcIso π g E).hom) ≫
        (Scheme.Modules.pullbackComp f (pullback.snd π g)).hom.app ((Scheme.Modules.pullback g).obj E) ≫
          (Scheme.Modules.pullbackCongr hb).hom.app ((Scheme.Modules.pullback g).obj E)) :
    (((Scheme.Modules.pullbackComp f (pullback.fst π g)).app F).symm ≪≫ e).hom ≫ ιG ≫
        (Scheme.Modules.pullbackComp t g).hom.app E =
      (Scheme.Modules.pullback (f ≫ pullback.fst π g)).map ιF ≫
        (Scheme.Modules.pullbackComp (f ≫ pullback.fst π g) π).hom.app E ≫
          (Scheme.Modules.pullbackCongr w).hom.app E := by
  have k := step_key π g f _ t rfl hb w E F ιF
  have e1 : (Scheme.Modules.pullbackCongr (rfl : f ≫ pullback.fst π g = f ≫ pullback.fst π g)).hom.app F = 𝟙 _ := by
    simp [Scheme.Modules.pullbackCongr]
  have hee' := congrArg (· ≫ (Scheme.Modules.pullbackComp t g).hom.app E) hee
  simp only [Category.assoc] at hee'
  rw [e1, Category.id_comp, ← hee'] at k
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Category.assoc] at k ⊢
  rw [k]
  simp

theorem isFlagBundle_baseChange : ∀ (B Y B' : Scheme.{0}) (π : Y ⟶ B) (g : B' ⟶ B) (ι : Type) (E : ι → B.Modules) (n : ι → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)), IsFlagBundle π E n fl →
    IsFlagBundle (pullback.snd π g) (fun a => (Scheme.Modules.pullback g).obj (E a)) n (fun a => bcFlag π g (fl a)) := by
  intro B Y B' π g ι E n fl H T t fl''
  obtain ⟨h, ⟨w, he⟩, hu⟩ := H T (t ≫ g) (fun a => (fl'' a).ofIso ((Scheme.Modules.pullbackComp t g).app (E a)))
  refine ⟨pullback.lift h t w, ⟨pullback.lift_snd _ _ _, fun a i => ?_⟩, ?_⟩
  · obtain ⟨e, hee⟩ := he a i
    exact ⟨_, step_exists π g (pullback.lift h t w) h t (pullback.lift_fst h t w) (pullback.lift_snd h t w) w (E a)
      ((fl a).F i) ((fl a).ι i) ((fl'' a).F i) ((fl'' a).ι i) e hee⟩
  · rintro y ⟨w'', he''⟩
    have w₁ : (y ≫ pullback.fst π g) ≫ π = t ≫ g := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, w'']
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      refine hu _ ⟨w₁, fun a i => ?_⟩
      obtain ⟨e, hee⟩ := he'' a i
      exact ⟨_, step_unique π g y t w'' w₁ (E a) ((fl a).F i) ((fl a).ι i) ((fl'' a).F i) ((fl'' a).ι i) e hee⟩
    · rw [pullback.lift_snd, w'']

end GlobalTheory.CovTest.BCFlag

end
