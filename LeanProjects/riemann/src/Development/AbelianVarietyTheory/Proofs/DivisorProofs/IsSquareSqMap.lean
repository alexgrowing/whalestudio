import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.UPel.HT.Pull

section Act

variable {S S' : Scheme.{0}} (f : S' ⟶ S)

def OActN.pullback {O : Type} [Ring O] (A : Over S) [GrpObj A] (a : GlobalTheory.UPel.HT.OActN O A) :
    GlobalTheory.UPel.HT.OActN O ((Over.pullback f).obj A) where
  act x := (Over.pullback f).map (a.act x)
  hom x := by have := a.hom x; infer_instance
  one := by rw [a.one, CategoryTheory.Functor.map_id]
  mul x y := by rw [a.mul, CategoryTheory.Functor.map_comp]
  add x y := by rw [a.add]; exact CategoryTheory.Functor.map_mul _ _ _

theorem OActN.pullback_left {O : Type} [Ring O] (A : Over S) [GrpObj A] (a : GlobalTheory.UPel.HT.OActN O A) (c : O) :
    ((OActN.pullback f A a).act c).left ≫ pullback.fst A.hom f = pullback.fst A.hom f ≫ (a.act c).left :=
  pullback.lift_fst _ _ _

end Act

section Sq

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}

def sqMap (w : φ ≫ A.hom = A'.hom ≫ f) : (G2 A').left ⟶ (G2 A).left :=
  (lift (pushPt w (fst A' A')) (pushPt w (snd A' A'))).left

theorem pushPt_left (w : φ ≫ A.hom = A'.hom ≫ f) {T : Over S'} (x : T ⟶ A') : (pushPt w x).left = x.left ≫ φ := rfl

theorem pushPt_comp (w : φ ≫ A.hom = A'.hom ≫ f) {T U : Over S'} (g : T ⟶ U) (x : U ⟶ A') :
    pushPt w (g ≫ x) = (Over.homMk g.left (by
      show g.left ≫ U.hom ≫ f = T.hom ≫ f
      rw [← Category.assoc, Over.w g]) : Over.mk (T.hom ≫ f) ⟶ Over.mk (U.hom ≫ f)) ≫ pushPt w x :=
  Over.OverMorphism.ext (Category.assoc _ _ _)

theorem lift_sqMap (w : φ ≫ A.hom = A'.hom ≫ f) {T : Over S'} (a b : T ⟶ A') :
    (lift a b).left ≫ sqMap w = (lift (pushPt w a) (pushPt w b)).left := by
  have e := pushPt_comp w (lift a b) (fst A' A')
  have e' := pushPt_comp w (lift a b) (snd A' A')
  rw [lift_fst] at e
  rw [lift_snd] at e'
  rw [e, e', ← comp_lift]
  rfl

theorem isSquare_sqMap (w : φ ≫ A.hom = A'.hom ≫ f) : IsSquare φ (sqMap w) := by
  constructor
  · show (lift (pushPt w (fst A' A')) (pushPt w (snd A' A')) ≫ fst A A).left = _
    rw [lift_fst]; rfl
  · show (lift (pushPt w (fst A' A')) (pushPt w (snd A' A')) ≫ snd A A).left = _
    rw [lift_snd]; rfl

end Sq

section Tate

variable {p : ℕ} [Fact p.Prime]

def tateMoveO {D : GlobalTheory.UPel.HT.Datum p} {k : Type} [Field k] {Q Q' : Type} [Group Q] [Group Q']
    {act : D.O → Q → Q} {act' : D.O → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop}
    (Φ : Q' ≃* Q) (hact : ∀ c x, Φ (act' c x) = act c (Φ x)) (he : ∀ n x y c, e n (Φ x) (Φ y) c → e' n x y c)
    (I : GlobalTheory.UPel.HT.TateIsoO D k Q act e) : GlobalTheory.UPel.HT.TateIsoO D k Q' act' e' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev := fun n a => Φ.symm (I.ev n a)
  add := fun n a b => by simp only [I.add, map_mul]
  lin := fun n c a => by
    apply Φ.injective
    rw [MulEquiv.apply_symm_apply, hact, MulEquiv.apply_symm_apply]
    exact I.lin n c a
  ker := fun n hn hp a => (map_eq_one_iff _ Φ.symm.injective).trans (I.ker n hn hp a)
  onto := fun n hn hp x => by
    rw [← map_eq_one_iff Φ Φ.injective, map_pow, I.onto n hn hp]
    exact exists_congr fun a => Φ.symm_apply_eq.symm
  tower := fun n m hn hm hp a => by rw [← map_pow, I.tower n m hn hm hp a]
  isom := fun n hn hp a b => he _ _ _ _ (by
    rw [Φ.apply_symm_apply, Φ.apply_symm_apply]
    exact I.isom n hn hp a b)

theorem tateMoveO_ev {D : GlobalTheory.UPel.HT.Datum p} {k : Type} [Field k] {Q Q' : Type} [Group Q] [Group Q']
    {act : D.O → Q → Q} {act' : D.O → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop}
    (Φ : Q' ≃* Q) (hact : ∀ c x, Φ (act' c x) = act c (Φ x)) (he : ∀ n x y c, e n (Φ x) (Φ y) c → e' n x y c)
    (I : GlobalTheory.UPel.HT.TateIsoO D k Q act e) (n : ℕ) (a : D.La) :
    (tateMoveO Φ hact he I).ev n a = Φ.symm (I.ev n a) := rfl

end Tate

section Pts

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}

theorem sqMap_of (w : φ ≫ A.hom = A'.hom ≫ f) {T : Over S'} {T₀ : Over S} (u : Over.mk (T.hom ≫ f) ⟶ T₀)
    (a' b' : T ⟶ A') (a b : T₀ ⟶ A) (ha : pushPt w a' = u ≫ a) (hb : pushPt w b' = u ≫ b) :
    (lift a' b').left ≫ sqMap w = u.left ≫ (lift a b).left := by
  rw [lift_sqMap, ha, hb, ← comp_lift]
  rfl

end Pts

end GlobalTheory.UPel.HT.Pull
