import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleModuleSheafHomEquivNaturalSections
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.CechPts

variable {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) {Z : Scheme.{0}} (x : Z ⟶ X) (y : Fin (k + 1) → (Z ⟶ Y))
  (h : ∀ i, y i ≫ f = x)

def cmp : yoneda.obj Z ⟶ widePullback (yoneda.obj X) (fun _ : Fin (k + 1) => yoneda.obj Y) (fun _ => yoneda.map f) :=
  WidePullback.lift (yoneda.map x) (fun i => yoneda.map (y i)) (fun i => by rw [← yoneda.map_comp, h i])

theorem cechPt_eq : cechPt f k x y h = (cmp f k x y h).app (op Z) (𝟙 Z) := rfl

theorem map_cechPt {U : Scheme.{0}} (g : U ⟶ Z) :
    ((cech f).obj (op ⦋k⦌)).map g.op (cechPt f k x y h) = (cmp f k x y h).app (op U) g := by
  rw [cechPt_eq]
  refine (FunctorToTypes.naturality (cmp f k x y h) g.op (𝟙 Z)).symm.trans ?_
  congr 1

theorem app_eq {U : Scheme.{0}} (g : U ⟶ Z) :
    (cmp f k x y h).app (op U) g = yonedaEquiv (yoneda.map g ≫ cmp f k x y h) := by
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]

theorem bij (hc : IsLimit (WidePullbackCone.mk (f := fun _ : Fin (k + 1) => f) x y h)) (U : Scheme.{0}) :
    Function.Bijective ((cmp f k x y h).app (op U)) := by
  constructor
  · intro g g' hg
    rw [app_eq, app_eq] at hg
    have hm := yonedaEquiv.injective hg
    apply WidePullbackCone.IsLimit.hom_ext hc
    · apply yoneda.map_injective
      have := hm =≫ WidePullback.base _
      simp only [cmp, Category.assoc, WidePullback.lift_base] at this
      exact (yoneda.map_comp _ _).trans (this.trans (yoneda.map_comp _ _).symm)
    · intro i
      apply yoneda.map_injective
      have := hm =≫ WidePullback.π _ i
      simp only [cmp, Category.assoc, WidePullback.lift_π] at this
      exact (yoneda.map_comp _ _).trans (this.trans (yoneda.map_comp _ _).symm)
  · intro v
    obtain ⟨m, rfl⟩ := yonedaEquiv.surjective v
    have w : ∀ i, yonedaEquiv (m ≫ WidePullback.π (fun _ : Fin (k + 1) => yoneda.map f) i) ≫ f =
        yonedaEquiv (m ≫ WidePullback.base (fun _ : Fin (k + 1) => yoneda.map f)) := by
      intro i
      rw [← WidePullback.π_arrow (fun _ : Fin (k + 1) => yoneda.map f) i, ← Category.assoc, yonedaEquiv_comp]
      rfl
    refine ⟨WidePullbackCone.IsLimit.lift hc _ _ w, (app_eq f k x y h _).trans ?_⟩
    congr 1
    apply WidePullback.hom_ext
    · intro i
      apply yonedaEquiv.injective
      have := WidePullbackCone.IsLimit.lift_π hc _ _ w i
      simp only [WidePullbackCone.mk_π] at this
      rw [Category.assoc]
      simp only [cmp, WidePullback.lift_π]
      exact (congrArg yonedaEquiv (yoneda.map_comp _ _).symm).trans ((yonedaEquiv_yoneda_map _).trans this)
    · apply yonedaEquiv.injective
      have := WidePullbackCone.IsLimit.lift_base hc _ _ w
      simp only [WidePullbackCone.mk_base] at this
      rw [Category.assoc]
      simp only [cmp, WidePullback.lift_base]
      exact (congrArg yonedaEquiv (yoneda.map_comp _ _).symm).trans ((yonedaEquiv_yoneda_map _).trans this)

end GlobalTheory.EtC.CechPts

open GlobalTheory.EtC.CechPts in

theorem GlobalTheory.EtC.CechPts.main : ∀ (R : Type) [CommRing R] (F : Shv R) (Y X : Scheme.{0}) (f : Y ⟶ X) (k : ℕ) (Z : Scheme.{0}) (x : Z ⟶ X) (y : Fin (k + 1) → (Z ⟶ Y)) (h : ∀ i, y i ≫ f = x), IsLimit (WidePullbackCone.mk (f := fun _ : Fin (k + 1) => f) x y h) → Function.Bijective (fun s : (free R).obj ((cech f).obj (op ⦋k⦌)) ⟶ F => val s Z (cechPt f k x y h)) := by
  intro R _ F Y X f k Z x y h hc
  have e : ∀ U : Scheme.{0}, Function.Bijective
      (fun g : U ⟶ Z => ((cech f).obj (op ⦋k⦌)).map g.op (cechPt f k x y h)) := by
    intro U
    have hb := bij f k x y h hc U
    refine ⟨fun g g' hg => hb.1 ((map_cechPt f k x y h g).symm.trans (hg.trans (map_cechPt f k x y h g'))), fun v => ?_⟩
    obtain ⟨g, hg⟩ := hb.2 v
    exact ⟨g, (map_cechPt f k x y h g).trans hg⟩
  obtain ⟨hext, hex, hnat, -⟩ := GlobalTheory.EtC.FreeHom.main R ((cech f).obj (op ⦋k⦌)) F
  constructor
  · intro s s' hs
    change val s Z (cechPt f k x y h) = val s' Z (cechPt f k x y h) at hs
    apply hext
    intro U v
    obtain ⟨g, rfl⟩ := (e U).2 v
    dsimp only
    rw [hnat s U Z g, hnat s' U Z g, hs]
  · intro a
    choose c hc0 using fun (U : Scheme.{0}) (v : ((cech f).obj (op ⦋k⦌)).obj (op U)) => (e U).2 v
    have hc' : ∀ (U : Scheme.{0}) (v : ((cech f).obj (op ⦋k⦌)).obj (op U)),
        ((cech f).obj (op ⦋k⦌)).map (c U v).op (cechPt f k x y h) = v := hc0
    obtain ⟨s, hs⟩ := hex (fun U v => Sec.res (c U v) a) (by
      intro V U g v
      have h1 : c V (((cech f).obj (op ⦋k⦌)).map g.op v) = g ≫ c U v := by
        apply (e V).1
        change ((cech f).obj (op ⦋k⦌)).map (c V _).op (cechPt f k x y h) =
          ((cech f).obj (op ⦋k⦌)).map (g ≫ c U v).op (cechPt f k x y h)
        rw [hc' V, op_comp, FunctorToTypes.map_comp_apply, hc' U v]
      dsimp only
      rw [h1]
      simp [Sec.res])
    refine ⟨s, ?_⟩
    change val s Z (cechPt f k x y h) = a
    rw [hs]
    have h2 : c Z (cechPt f k x y h) = 𝟙 Z := by
      apply (e Z).1
      change ((cech f).obj (op ⦋k⦌)).map (c Z _).op (cechPt f k x y h) =
        ((cech f).obj (op ⦋k⦌)).map (𝟙 Z).op (cechPt f k x y h)
      rw [hc' Z, op_id, FunctorToTypes.map_id_apply]
    rw [h2]
    simp [Sec.res]
