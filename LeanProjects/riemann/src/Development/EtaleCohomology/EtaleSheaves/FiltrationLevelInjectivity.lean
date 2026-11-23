import Development.EtaleCohomology.EtaleSheaves.RelDescPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.FiltrationLevelInjectivity

def gN {D Y' E Y'' : CommRingCat.{0}} (φ' : D ⟶ Y') (e : D ⟶ E) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'')
    (h : φ' ≫ u = e ≫ φ'') : cech (Spec.map u) ⟶ cech (Spec.map e) :=
  Arrow.mapCechNerve (f := Arrow.mk (yoneda.map (Spec.map u))) (g := Arrow.mk (yoneda.map (Spec.map e)))
    ⟨yoneda.map (Spec.map φ''), yoneda.map (Spec.map φ'), by
      simp only [Arrow.mk_hom, Functor.id_map, Functor.id_obj, Arrow.mk_left, Arrow.mk_right,
        ← Functor.map_comp, ← Spec.map_comp, h]⟩

def iN {Y X : Scheme.{0}} (f : Y ⟶ X) : sch.obj Y ⟶ cech f where
  app _ := WidePullback.lift (yoneda.map f) (fun _ => 𝟙 _) (fun _ => Category.id_comp _)
  naturality := by
    intro x y θ
    apply WidePullback.hom_ext
    · intro j
      erw [Category.assoc, WidePullback.lift_π, Category.assoc, WidePullback.lift_π, WidePullback.lift_π]
      exact Category.id_comp _
    · erw [Category.assoc, WidePullback.lift_base, Category.assoc, WidePullback.lift_base, WidePullback.lift_base]
      exact Category.id_comp _

theorem iN_aug {Y X : Scheme.{0}} (f : Y ⟶ X) : iN f ≫ cechAug f = sch.map f := by
  refine NatTrans.ext (funext fun x => ?_)
  erw [NatTrans.comp_app, WidePullback.lift_base]
  rfl

theorem iN_app_zero_iso {Y X : Scheme.{0}} (f : Y ⟶ X) : IsIso ((iN f).app (op ⦋0⦌)) := by
  refine ⟨⟨WidePullback.π (fun _ : Fin 1 => yoneda.map f) 0, ?_, ?_⟩⟩
  · erw [WidePullback.lift_π]
  · apply WidePullback.hom_ext
    · intro j
      have hj : j = 0 := Fin.fin_one_eq_zero j
      subst hj
      erw [Category.assoc, WidePullback.lift_π, Category.id_comp]
      exact Category.comp_id _
    · erw [Category.assoc, WidePullback.lift_base, Category.id_comp]
      exact WidePullback.π_arrow _ _

theorem gN_aug {D Y' E Y'' : CommRingCat.{0}} (φ' : D ⟶ Y') (e : D ⟶ E) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'')
    (h : φ' ≫ u = e ≫ φ'') :
    gN φ' e u φ'' h ≫ cechAug (Spec.map e) = cechAug (Spec.map u) ≫ sch.map (Spec.map φ') := by
  refine NatTrans.ext (funext fun x => ?_)
  erw [NatTrans.comp_app, WidePullback.lift_base]
  rfl

theorem gN_iN {D Y' E Y'' : CommRingCat.{0}} (φ' : D ⟶ Y') (e : D ⟶ E) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'')
    (h : φ' ≫ u = e ≫ φ'') :
    sch.map (Spec.map φ'') ≫ iN (Spec.map e) = iN (Spec.map u) ≫ gN φ' e u φ'' h := by
  have hw : yoneda.map (Spec.map φ'') ≫ yoneda.map (Spec.map e) = yoneda.map (Spec.map u) ≫ yoneda.map (Spec.map φ') := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Spec.map_comp, ← Spec.map_comp, h]
  refine NatTrans.ext (funext fun x => ?_)
  apply WidePullback.hom_ext
  · intro j
    erw [Category.assoc, WidePullback.lift_π, Category.assoc, WidePullback.lift_π, ← Category.assoc,
      WidePullback.lift_π, Category.id_comp]
    exact Category.comp_id _
  · erw [Category.assoc, WidePullback.lift_base, Category.assoc, WidePullback.lift_base, ← Category.assoc,
      WidePullback.lift_base]
    exact hw

def Filt : Prop := Hyp → ∀ (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {Z' Z : PSh} {X' X : Spc} (g : X' ⟶ X)
  (h : Z' ⟶ Z) (a : disc.obj Z ⟶ X) (b : disc.obj Z' ⟶ X') (comm : disc.map h ≫ a = b ≫ g),
  IsIso (a.app (op ⦋0⦌)) → IsIso (b.app (op ⦋0⦌)) →
  (∀ p : ℕ, 1 ≤ p → ∀ m : ℤ, m < n → Function.Injective (pull R (disc.map (g.app (op ⦋p⦌))) F m) ∧
    Function.Surjective (pull R (disc.map (g.app (op ⦋p⦌))) F (m - 1))) →
  Function.Injective (rpull R g (disc.map h) b a comm F n)

def LvlRel : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''),
    Et e → SpS e → P E (d ≫ e) → ∀ hpo : IsPushout φ' e u φ'',
  ∀ p : ℕ, 1 ≤ p → ∀ m : ℤ, m < n →
    Function.Injective (pull (ZMod q) (disc.map ((gN φ' e u φ'' hpo.w).app (op ⦋p⦌))) (tw q i) m) ∧
    Function.Surjective (pull (ZMod q) (disc.map ((gN φ' e u φ'' hpo.w).app (op ⦋p⦌))) (tw q i) (m - 1))

theorem LevelInj_of (hF : Filt) (hL : LvlRel) : LateralTheory.E.RelDescPf.LevelInj := by
  intro hH q _ i n A Y φ hq P hP hE hB D d hD Y' w φ' hpo E e Y'' u φ'' he hs hPE hpo'
  refine ⟨gN φ' e u φ'' hpo'.w, gN_aug _ _ _ _ _, iN (Spec.map e), iN (Spec.map u), gN_iN _ _ _ _ _,
    iN_aug _, iN_aug _, ?_⟩
  exact hF hH (ZMod q) (tw q i) n (gN φ' e u φ'' hpo'.w) (yoneda.map (Spec.map φ'')) (iN (Spec.map e))
    (iN (Spec.map u)) (gN_iN _ _ _ _ _) (iN_app_zero_iso _) (iN_app_zero_iso _)
    (hL hH q i n φ hq P hP hE hB D d hD Y' w φ' hpo E e Y'' u φ'' he hs hPE hpo')

end LateralTheory.E.FiltrationLevelInjectivity
