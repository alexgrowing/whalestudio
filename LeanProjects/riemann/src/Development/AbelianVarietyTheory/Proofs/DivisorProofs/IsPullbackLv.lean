import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.BcLevel

def bcIsoOfIso {E E' : Spc} {S : Scheme.{0}} (α : E ≅ E') (p : E' ⟶ sch.obj S) : bc (α.hom ≫ p) ≅ bc p :=
  haveI : ∀ U, IsIso ((bcMap α.hom p).app U) := fun U => by
    dsimp only [bcMap]; exact pullback.map_isIso _ _ _ _ _ _ _ _ _
  haveI : IsIso (bcMap α.hom p) := NatIso.isIso_of_isIso_app _
  asIso (bcMap α.hom p)

def dq {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) (k : SimplexCategoryᵒᵖ) : disc.obj (E.obj k) ⟶ sch.obj S :=
  disc.map (p.app k)

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.EtC.BcLevel.isPullback_lv {E : _root_.GlobalTheory.EtC.Spc} {S : Scheme.{0}}
    (p : E ⟶ _root_.GlobalTheory.EtC.sch.obj S) (k : SimplexCategoryᵒᵖ) (U : Over S) :
    IsPullback (_root_.GlobalTheory.EtC.disc.map ((pullback.fst p (_root_.GlobalTheory.EtC.sch.map U.hom)).app k) : _root_.GlobalTheory.EtC.disc.obj ((pullback p (_root_.GlobalTheory.EtC.sch.map U.hom)).obj k) ⟶ _root_.GlobalTheory.EtC.disc.obj (E.obj k))
      (_root_.GlobalTheory.EtC.disc.map ((pullback.snd p (_root_.GlobalTheory.EtC.sch.map U.hom)).app k) : _root_.GlobalTheory.EtC.disc.obj ((pullback p (_root_.GlobalTheory.EtC.sch.map U.hom)).obj k) ⟶ _root_.GlobalTheory.EtC.sch.obj U.left)
      (_root_.GlobalTheory.EtC.BcLevel.dq p k) (_root_.GlobalTheory.EtC.sch.map U.hom) := by
  have h := (IsPullback.of_hasPullback p (_root_.GlobalTheory.EtC.sch.map U.hom)).map
    ((evaluation SimplexCategoryᵒᵖ _root_.GlobalTheory.EtC.PSh).obj k)
  exact h.map _root_.GlobalTheory.EtC.disc

def lvIso {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) (k : SimplexCategoryᵒᵖ) (U : Over S) :
    disc.obj ((pullback p (sch.map U.hom)).obj k) ≅ pullback (dq p k) (sch.map U.hom) :=
  (isPullback_lv p k U).isoPullback

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.EtC.BcLevel.lv_nat {E : _root_.GlobalTheory.EtC.Spc} {S : Scheme.{0}}
    (p : E ⟶ _root_.GlobalTheory.EtC.sch.obj S) (k : SimplexCategoryᵒᵖ) {U V : Over S} (g : U ⟶ V) :
    (_root_.GlobalTheory.EtC.disc.map (((_root_.GlobalTheory.EtC.bc p).map g).app k) : _root_.GlobalTheory.EtC.disc.obj ((pullback p (_root_.GlobalTheory.EtC.sch.map U.hom)).obj k) ⟶ _root_.GlobalTheory.EtC.disc.obj ((pullback p (_root_.GlobalTheory.EtC.sch.map V.hom)).obj k)) ≫
      (_root_.GlobalTheory.EtC.BcLevel.lvIso p k V).hom = (_root_.GlobalTheory.EtC.BcLevel.lvIso p k U).hom ≫ (_root_.GlobalTheory.EtC.bc (_root_.GlobalTheory.EtC.BcLevel.dq p k)).map g := by
  have hV₁ := (_root_.GlobalTheory.EtC.BcLevel.isPullback_lv p k V).isoPullback_hom_fst
  have hV₂ := (_root_.GlobalTheory.EtC.BcLevel.isPullback_lv p k V).isoPullback_hom_snd
  have hU₁ := (_root_.GlobalTheory.EtC.BcLevel.isPullback_lv p k U).isoPullback_hom_fst
  have hU₂ := (_root_.GlobalTheory.EtC.BcLevel.isPullback_lv p k U).isoPullback_hom_snd
  unfold _root_.GlobalTheory.EtC.BcLevel.lvIso
  dsimp only [_root_.GlobalTheory.EtC.bc]
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc]
    erw [hV₁, pullback.lift_fst, Category.comp_id, hU₁]
    rw [← Functor.map_comp, ← NatTrans.comp_app, pullback.lift_fst, Category.comp_id]
  · rw [Category.assoc, Category.assoc]
    erw [hV₂, pullback.lift_snd, ← Category.assoc, hU₂]
    change _ = _root_.GlobalTheory.EtC.disc.map _ ≫
      _root_.GlobalTheory.EtC.disc.map ((_root_.GlobalTheory.EtC.sch.map g.left).app k)
    rw [← Functor.map_comp]
    erw [← Functor.map_comp]
    congr 1
    rw [← NatTrans.comp_app]
    erw [← NatTrans.comp_app, pullback.lift_snd]

def bcDiscIso {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) (k : SimplexCategoryᵒᵖ) :
    bc p ⋙ (evaluation _ PSh).obj k ⋙ disc ≅ bc (dq p k) :=
  NatIso.ofComponents (lvIso p k) (fun g => lv_nat p k g)

theorem bc_level : ∀ (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S) (k : SimplexCategoryᵒᵖ) (X : Scheme.{0}) (r : X ⟶ S)
    (e : yoneda.obj X ≅ E.obj k), e.hom ≫ p.app k = yoneda.map r →
    Nonempty (bc (sch.map r) ≅ bc p ⋙ (evaluation _ PSh).obj k ⋙ disc) := by
  intro S E p k X r e h
  have heq : sch.map r = (disc.mapIso e : sch.obj X ≅ disc.obj (E.obj k)).hom ≫ dq p k := by
    change disc.map (yoneda.map r) = disc.map e.hom ≫ disc.map (p.app k)
    rw [← h]
    exact disc.map_comp _ _
  rw [heq]
  exact ⟨bcIsoOfIso _ (dq p k) ≪≫ (bcDiscIso p k).symm⟩

end GlobalTheory.EtC.BcLevel
