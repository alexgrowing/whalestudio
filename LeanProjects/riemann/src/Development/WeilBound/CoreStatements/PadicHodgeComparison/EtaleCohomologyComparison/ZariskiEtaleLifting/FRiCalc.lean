import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

lemma rc_pull_comp {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {C'' : Type u''} [Category.{v''} C''] {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w} R}
    {F'' : C'' ⥤ ModuleCat.{w} R} (m : Mor F F' (RingHom.id R)) (m' : Mor F' F'' (RingHom.id R)) (n : ℕ) :
    (m.comp m' : Mor F F'' (RingHom.id R)).pull n = (m'.pull n).comp (m.pull n) :=
  LinearMap.ext fun x => (CrystallineSemistableComparison.P.pull_comp m m' n x).1

lemma rc_restrict_comp {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {C'' : Type u''} [Category.{v''} C''] (F : C ⥤ ModuleCat.{w} R) (G : C' ⥤ C) (G' : C'' ⥤ C') (n : ℕ) :
    (Mor.restrict F (G' ⋙ G)).pull n = ((Mor.restrict (G ⋙ F) G').pull n).comp ((Mor.restrict F G).pull n) :=
  rc_pull_comp (Mor.restrict F G) (Mor.restrict (G ⋙ F) G') n

lemma rc_iso_upTo {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {F F₁ : C ⥤ ModuleCat.{w} R}
    (e : F ≅ F₁) (n : ℕ) : UpTo (1 : R) ((Mor.ofNatTrans e.hom).pull n) := by
  have h := CrystallineSemistableComparison.P.coef_upTo e.hom (1 : R) (fun T => by
    refine ((CrystallineSemistableComparison.P.upTo_alg (e.hom.app T).hom LinearMap.id 1 1).2.2.2.2).2 ?_
    exact (e.app T).toLinearEquiv.bijective) n
  rwa [one_pow] at h

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.ri_calc : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C''] (F : C ⥤ ModuleCat.{w} R) (G : C' ⥤ C) (G' : C'' ⥤ C') (s s' : R) (n : ℕ), (RI s n F G → RI s' n (G ⋙ F) G' → RI (s * s') n F (G' ⋙ G)) ∧ (RI s n F G → RI s' n F (G' ⋙ G) → RI (s * s') n (G ⋙ F) G') ∧ (RI s n (G ⋙ F) G' → RI s' n F (G' ⋙ G) → RI (s * s') n F G) ∧ (RI s n F G → RI (s * s') n F G) ∧ (∀ G₁ : C' ⥤ C, (G ≅ G₁) → RI s n F G → RI s n F G₁) ∧ (G.IsEquivalence → RI 1 n F G) ∧ (∀ F₁ : C ⥤ ModuleCat.{w} R, (F ≅ F₁) → RI s n F G → RI s n F₁ G) := by
  intro R _ C _ C' _ C'' _ F G G' s s' n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h1 h2 j hj
    rw [RI, IsoLe] at *
    rw [rc_restrict_comp]
    exact (CrystallineSemistableComparison.P.upTo_alg _ _ s s').1 (h1 j hj) (h2 j hj)
  · intro h1 h2 j hj
    have := h2 j hj
    rw [rc_restrict_comp] at this
    exact (CrystallineSemistableComparison.P.upTo_alg _ _ s s').2.1 (h1 j hj) this
  · intro h1 h2 j hj
    have := h2 j hj
    rw [rc_restrict_comp] at this
    exact (CrystallineSemistableComparison.P.upTo_alg _ _ s s').2.2.1 (h1 j hj) this
  · intro h1 j hj
    exact (CrystallineSemistableComparison.P.upTo_alg ((Mor.restrict F G).pull j) LinearMap.id s s').2.2.2.1 (h1 j hj)
  · intro G₁ e h1 j hj
    have hp : (Mor.restrict F G₁).pull j =
        ((Mor.ofNatTrans (Functor.whiskerRight e.hom F)).pull j).comp ((Mor.restrict F G).pull j) := by
      rw [← rc_pull_comp]
      refine LinearMap.ext fun x => CrystallineSemistableComparison.P.prism (Mor.restrict F G₁)
        ((Mor.restrict F G).comp (Mor.ofNatTrans (Functor.whiskerRight e.hom F))) e.inv ?_ j x
      intro T x
      change (F.map (e.hom.app T)).hom ((F.map (e.inv.app T)).hom x) = x
      rw [← ModuleCat.comp_apply, ← F.map_comp, e.inv_hom_id_app, F.map_id]
      rfl
    rw [hp, ← mul_one s]
    exact (CrystallineSemistableComparison.P.upTo_alg _ _ s 1).1 (h1 j hj) (rc_iso_upTo (Functor.isoWhiskerRight e F) j)
  · intro hG j hj
    exact ((CrystallineSemistableComparison.P.upTo_alg ((Mor.restrict F G).pull j) LinearMap.id 1 1).2.2.2.2).2
      (CrystallineSemistableComparison.P.adj F G G.asEquivalence.inverse G.asEquivalence.toAdjunction j)
  · intro F₁ e h1 j hj
    have hp : (Mor.restrict F₁ G).pull j =
        ((Mor.ofNatTrans (Functor.whiskerLeft G e.hom)).pull j).comp
          (((Mor.restrict F G).pull j).comp ((Mor.ofNatTrans e.inv).pull j)) := by
      rw [← rc_pull_comp, ← rc_pull_comp]
      refine LinearMap.ext fun x => CrystallineSemistableComparison.P.prism (Mor.restrict F₁ G)
        ((Mor.ofNatTrans e.inv).comp ((Mor.restrict F G).comp (Mor.ofNatTrans (Functor.whiskerLeft G e.hom))))
        (𝟙 G) ?_ j x
      intro T x
      change (e.hom.app (G.obj T)).hom ((e.inv.app (G.obj T)).hom ((F₁.map (𝟙 (G.obj T))).hom x)) = x
      rw [F₁.map_id, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply, e.inv_hom_id_app]
      rfl
    rw [hp, ← one_mul s, ← mul_one (1 * s)]
    exact (CrystallineSemistableComparison.P.upTo_alg _ _ (1 * s) 1).1
      ((CrystallineSemistableComparison.P.upTo_alg _ _ 1 s).1 (rc_iso_upTo e.symm j) (h1 j hj))
      (rc_iso_upTo (Functor.isoWhiskerLeft G e) j)
