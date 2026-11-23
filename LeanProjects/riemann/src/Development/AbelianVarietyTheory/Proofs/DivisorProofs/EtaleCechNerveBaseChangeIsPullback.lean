import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.CechBC

universe v u

theorem widePullback_isPullback {C : Type u} [Category.{v} C] {Y X Y' X' : C}
    {a : Y' ⟶ Y} {f' : Y' ⟶ X'} {f : Y ⟶ X} {b : X' ⟶ X} (hP : IsPullback a f' f b) (n : ℕ)
    [HasWidePullback X' (fun _ : Fin (n + 1) => Y') (fun _ => f')]
    [HasWidePullback X (fun _ : Fin (n + 1) => Y) (fun _ => f)] :
    IsPullback
      (WidePullback.lift (WidePullback.base (fun _ : Fin (n + 1) => f') ≫ b)
        (fun i => WidePullback.π (fun _ : Fin (n + 1) => f') i ≫ a)
        (fun i => by rw [Category.assoc, hP.w, ← Category.assoc, WidePullback.π_arrow]))
      (WidePullback.base (fun _ : Fin (n + 1) => f')) (WidePullback.base (fun _ : Fin (n + 1) => f)) b := by
  refine IsPullback.of_isLimit' ⟨WidePullback.lift_base _ _ _ _⟩ (PullbackCone.IsLimit.mk _
    (fun s => WidePullback.lift s.snd
      (fun i => hP.lift (s.fst ≫ WidePullback.π _ i) s.snd
        (by rw [Category.assoc, WidePullback.π_arrow, s.condition]))
      (fun i => hP.lift_snd _ _ _)) ?_ ?_ ?_)
  · intro s
    apply WidePullback.hom_ext
    · intro j
      rw [Category.assoc, WidePullback.lift_π, ← Category.assoc, WidePullback.lift_π, IsPullback.lift_fst]
    · rw [Category.assoc, WidePullback.lift_base, ← Category.assoc, WidePullback.lift_base, s.condition]
  · intro s
    exact WidePullback.lift_base _ _ _ _
  · intro s m h1 h2
    apply WidePullback.hom_ext
    · intro j
      apply hP.hom_ext
      · rw [WidePullback.lift_π, IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, WidePullback.lift_π]
      · rw [WidePullback.lift_π, IsPullback.lift_snd, Category.assoc, WidePullback.π_arrow, h2]
    · rw [WidePullback.lift_base, h2]

theorem lift_comp_lift {C : Type u} [Category.{v} C] {Y X Y' X' : C}
    {a : Y' ⟶ Y} {f' : Y' ⟶ X'} {f : Y ⟶ X} {b : X' ⟶ X} (w : a ≫ f = f' ≫ b) (n : ℕ)
    [HasWidePullback X' (fun _ : Fin (n + 1) => Y') (fun _ => f')]
    [HasWidePullback X (fun _ : Fin (n + 1) => Y) (fun _ => f)] {T : C}
    (g : T ⟶ X') (e : Fin (n + 1) → (T ⟶ Y')) (he : ∀ i, e i ≫ f' = g)
    (g₂ : T ⟶ X) (e₂ : Fin (n + 1) → (T ⟶ Y)) (he₂ : ∀ i, e₂ i ≫ f = g₂)
    (hg : g ≫ b = g₂) (hh : ∀ i, e i ≫ a = e₂ i) :
    WidePullback.lift g e he ≫
      WidePullback.lift (WidePullback.base (fun _ : Fin (n + 1) => f') ≫ b)
        (fun i => WidePullback.π (fun _ : Fin (n + 1) => f') i ≫ a)
        (fun i => by rw [Category.assoc, w, ← Category.assoc, WidePullback.π_arrow]) =
      WidePullback.lift g₂ e₂ he₂ := by
  apply WidePullback.hom_ext
  · intro j
    rw [Category.assoc, WidePullback.lift_π, ← Category.assoc, WidePullback.lift_π, WidePullback.lift_π, hh]
  · rw [Category.assoc, WidePullback.lift_base, ← Category.assoc, WidePullback.lift_base, WidePullback.lift_base, hg]

end GlobalTheory.CechBC

open GlobalTheory.CechBC in

theorem GlobalTheory.cech_baseChange : ∀ (Y X Y' X' : Scheme.{0}) (a : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (b : X' ⟶ X), IsPullback a f' f b → ∃ m : cech f' ⟶ cech f, IsPullback m (cechAug f') (cechAug f) (sch.map b) ∧ ∀ (k : ℕ) (U : Scheme.{0}) (x : U ⟶ X') (y : Fin (k + 1) → (U ⟶ Y')) (h : ∀ i, y i ≫ f' = x), ∃ h', (m.app (op (SimplexCategory.mk (k)))).app (op U) (cechPt f' k x y h) = cechPt f k (x ≫ b) (fun i => y i ≫ a) h' := by
  intro Y X Y' X' a f' f b hP
  have hw : yoneda.map a ≫ yoneda.map f = yoneda.map f' ≫ yoneda.map b := by
    rw [← yoneda.map_comp, ← yoneda.map_comp, hP.w]
  have hY : IsPullback (yoneda.map a) (yoneda.map f') (yoneda.map f) (yoneda.map b) := hP.map yoneda
  refine ⟨Arrow.mapCechNerve (Arrow.homMk' (f := yoneda.map f') (g := yoneda.map f) (yoneda.map a) (yoneda.map b) hw), ?_, ?_⟩
  · refine IsPullback.of_forall_isPullback_app (fun n => ?_)
    exact widePullback_isPullback hY n.unop.len
  · intro k U x y h
    have h' : ∀ i, (y i ≫ a) ≫ f = x ≫ b := fun i => by rw [Category.assoc, hP.w, ← Category.assoc, h i]
    refine ⟨h', ?_⟩
    have key : WidePullback.lift (arrows := fun _ : Fin (k + 1) => yoneda.map f') (yoneda.map x) (fun i => yoneda.map (y i))
        (fun i => by rw [← yoneda.map_comp, h i]) ≫
        (Arrow.mapCechNerve (Arrow.homMk' (f := yoneda.map f') (g := yoneda.map f) (yoneda.map a) (yoneda.map b) hw)).app (op (SimplexCategory.mk k)) =
        WidePullback.lift (arrows := fun _ : Fin (k + 1) => yoneda.map f) (yoneda.map (x ≫ b)) (fun i => yoneda.map (y i ≫ a))
        (fun i => by rw [← yoneda.map_comp, h' i]) := by
      exact lift_comp_lift hw k _ _ _ _ _ _ (yoneda.map_comp x b).symm (fun i => (yoneda.map_comp (y i) a).symm)
    unfold cechPt
    erw [← FunctorToTypes.comp]
    exact congrArg (fun φ : yoneda.obj U ⟶ (cech f).obj (op (SimplexCategory.mk k)) => φ.app (op U) (𝟙 U)) key
