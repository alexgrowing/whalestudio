import Development.EtaleCohomology.EtaleSheaves.LocalDescent.DescLocOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf Opposite

namespace LateralTheory.E.TruncCokPf

def sq {D E Y' Y'' : CommRingCat.{0}} (e : D ⟶ E) (φ' : D ⟶ Y') (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'') (h : φ' ≫ u = e ≫ φ'') :
    Arrow.mk (yoneda.map (Spec.map u)) ⟶ Arrow.mk (yoneda.map (Spec.map e)) :=
  Arrow.homMk (yoneda.map (Spec.map φ'')) (yoneda.map (Spec.map φ')) (by
    simp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom]
    rw [← Functor.map_comp, ← Functor.map_comp, ← Spec.map_comp, ← Spec.map_comp, h])

def LevelLow (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {D E Y' Y'' : CommRingCat.{0}} (e : D ⟶ E) (φ' : D ⟶ Y')
    (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'') (h : φ' ≫ u = e ≫ φ'') : Prop :=
  ∀ (p : ℕ) (m : ℤ), m < n →
    (∀ k : ℤ, k + 1 = m → Function.Surjective (pull R (disc.map ((Arrow.mapCechNerve (sq e φ' u φ'' h)).app (op (SimplexCategory.mk p)))) F k)) ∧
    Function.Injective (pull R (disc.map ((Arrow.mapCechNerve (sq e φ' u φ'' h)).app (op (SimplexCategory.mk p)))) F m)

def Desc : Prop := Hyp → ∀ (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {D E Y' Y'' : CommRingCat.{0}} (e : D ⟶ E) (φ' : D ⟶ Y')
    (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'') (hpo : IsPushout φ' e u φ''), Et e → SpS e →
    LevelLow R F n e φ' u φ'' hpo.w →
    ∀ m : ℤ, m + 1 = n → ∀ y : H R (sch.obj (Spec Y')) F m,
      pull R (sch.map (Spec.map u)) F m y ∈ Set.range (pull R (sch.map (Spec.map φ'')) F m) →
      y ∈ Set.range (pull R (sch.map (Spec.map φ')) F m)

def Levels : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'')
    (hpo : IsPushout φ' e u φ''), Et e → SpS e → P E (d ≫ e) →
    LevelLow (ZMod q) (tw q i) n e φ' u φ'' hpo.w

theorem TruncCok_of (hD : Desc) (hL : Levels) : LateralTheory.E.DescLocPf.Fine.TruncCok := by
  intro hH q _ i n A Y φ hq P hpush het hlow D d hD' Y' w φ' hpo E e Y'' u φ'' he hs hE hpo' m hm y hy
  exact hD hH (ZMod q) (tw q i) n e φ' u φ'' hpo' he hs
    (hL hH q i n φ hq P hpush het hlow D d hD' Y' w φ' hpo E e Y'' u φ'' hpo' he hs hE) m hm y hy

end LateralTheory.E.TruncCokPf
