import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeHomSections

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

section FreeYoneda
variable {R : Type} [CommRing R]

theorem freeYoneda_secMap_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (s : Sec F U) :
    Sec.map φ (Sec.res g s) = Sec.res g (Sec.map φ s) := by
  have h := congrArg (fun k => k.hom s) (φ.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

theorem freeYoneda_res_res {F : Shv R} {W V U : Scheme.{0}} (g : W ⟶ V) (x : V ⟶ U) (s : Sec F U) :
    Sec.res g (Sec.res x s) = Sec.res (g ≫ x) s := by
  change (F.obj.map g.op).hom ((F.obj.map x.op).hom s) = (F.obj.map (g ≫ x).op).hom s
  rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem freeYoneda_res_id {F : Shv R} {U : Scheme.{0}} (s : Sec F U) : Sec.res (𝟙 U) s = s := by
  change (F.obj.map (𝟙 U).op).hom s = s
  rw [op_id, CategoryTheory.Functor.map_id, ModuleCat.hom_id, LinearMap.id_apply]

theorem freeYoneda_secMap_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (s : Sec F U) :
    Sec.map (φ ≫ ψ) s = Sec.map ψ (Sec.map φ s) := rfl

variable (R) in

theorem freeYoneda_gen {Y U : Scheme.{0}} (x : U ⟶ Y) :
    freeGen R (yoneda.obj Y) U x = Sec.res x (freeGen R (yoneda.obj Y) Y (𝟙 Y)) := by
  rw [(free_hom_sections R (yoneda.obj Y) ((free R).obj (yoneda.obj Y))).2.2.1]
  simp

variable (R) in

theorem freeYoneda_ev_bijective {Y : Scheme.{0}} (F : Shv R) :
    Function.Bijective fun h : (free R).obj (yoneda.obj Y) ⟶ F => Sec.map h (freeGen R (yoneda.obj Y) Y (𝟙 Y)) := by
  obtain ⟨hex, hext, -, -⟩ := free_hom_sections R (yoneda.obj Y) F
  constructor
  · intro φ ψ e
    apply hext
    intro U x
    rw [freeYoneda_gen R (x : U ⟶ Y), freeYoneda_secMap_res, freeYoneda_secMap_res]
    exact congrArg (Sec.res (x : U ⟶ Y)) e
  · intro s
    obtain ⟨φ, hφ⟩ := hex (fun U x => Sec.res (x : U ⟶ Y) s) (fun V U g x => by
      simp only [yoneda_obj_map]
      exact freeYoneda_res_res g x s)
    exact ⟨φ, (hφ Y (𝟙 Y)).trans (freeYoneda_res_id s)⟩

variable (R) in

theorem freeYoneda_ev_pre {Y X : Scheme.{0}} (f : Y ⟶ X) {F : Shv R} (h : (free R).obj (yoneda.obj X) ⟶ F) :
    Sec.map ((free R).map (yoneda.map f) ≫ h) (freeGen R (yoneda.obj Y) Y (𝟙 Y)) =
      Sec.res f (Sec.map h (freeGen R (yoneda.obj X) X (𝟙 X))) := by
  rw [freeYoneda_secMap_comp, (free_hom_sections R (yoneda.obj Y) F).2.2.2, ← freeYoneda_secMap_res,
    ← freeYoneda_gen R f]
  congr 2

end FreeYoneda

theorem freeYoneda_desc_isIso : ∀ (R : Type) [CommRing R] {Y₁ Y₂ X : Scheme.{0}} (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X),
    (∀ F : Shv R, Function.Bijective fun s : Sec F X => (Sec.res f₁ s, Sec.res f₂ s)) →
    IsIso (biprod.desc ((free R).map (yoneda.map f₁)) ((free R).map (yoneda.map f₂))) := by
  intro R _ Y₁ Y₂ X f₁ f₂ hb
  rw [isIso_iff_coyoneda_map_bijective]
  intro F
  have key : Function.Bijective fun h : (free R).obj (yoneda.obj X) ⟶ F =>
      ((free R).map (yoneda.map f₁) ≫ h, (free R).map (yoneda.map f₂) ≫ h) := by
    have e12 := (freeYoneda_ev_bijective R (Y := Y₁) F).prodMap (freeYoneda_ev_bijective R (Y := Y₂) F)
    refine (e12.of_comp_iff' _).1 ?_
    have comm : (Prod.map (fun h : (free R).obj (yoneda.obj Y₁) ⟶ F => Sec.map h (freeGen R (yoneda.obj Y₁) Y₁ (𝟙 Y₁)))
        (fun h : (free R).obj (yoneda.obj Y₂) ⟶ F => Sec.map h (freeGen R (yoneda.obj Y₂) Y₂ (𝟙 Y₂)))) ∘
        (fun h : (free R).obj (yoneda.obj X) ⟶ F =>
          ((free R).map (yoneda.map f₁) ≫ h, (free R).map (yoneda.map f₂) ≫ h)) =
        (fun s : Sec F X => (Sec.res f₁ s, Sec.res f₂ s)) ∘
          (fun h : (free R).obj (yoneda.obj X) ⟶ F => Sec.map h (freeGen R (yoneda.obj X) X (𝟙 X))) := by
      funext h
      simp only [Function.comp_apply, Prod.map_apply]
      rw [freeYoneda_ev_pre R f₁ h, freeYoneda_ev_pre R f₂ h]
    rw [comm]
    exact (hb F).comp (freeYoneda_ev_bijective R F)
  have hβ : Function.Bijective fun g : ((free R).obj (yoneda.obj Y₁) ⊞ (free R).obj (yoneda.obj Y₂)) ⟶ F =>
      (biprod.inl ≫ g, biprod.inr ≫ g) := by
    constructor
    · intro g g' e
      simp only [Prod.mk.injEq] at e
      exact biprod.hom_ext' _ _ e.1 e.2
    · rintro ⟨a, b⟩
      exact ⟨biprod.desc a b, by simp⟩
  refine (hβ.of_comp_iff' _).1 ?_
  convert key using 1
  funext h
  simp

end GlobalTheory.EtC
