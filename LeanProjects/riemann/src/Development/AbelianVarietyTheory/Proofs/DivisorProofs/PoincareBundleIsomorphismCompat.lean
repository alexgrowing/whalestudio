import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetGroupMorphismBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracIdExistsTotPos

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KerShift

open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw

theorem evc_congr {S : Scheme.{0}} {A T Y : Over S} {M N : LB (A ⊗ T).left} (hM : M.IsLB) (hN : N.IsLB)
    (e : LBIso M N) (a : Y ⟶ A) (t : Y ⟶ T) : evc hM a t = evc hN a t := by
  unfold evc
  rw [(cls_eq_iff hM hN).2 e]

theorem ker_shift : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (S : Scheme.{0}) (A : Over S) [GrpObj A]
    (rm : OAct (𝓞 F) A) (P : 𝔠.elt → LB (A ⊗ A).left), (∀ c, (P c).IsLB) →
    (∀ c, LBIso (P c) ((P c).pull (lift (snd A A) (fst A A)).left)) →
    (∀ (a : 𝓞 F) c, LBIso (P (a • c)) ((P c).pull (lift (fst A A) (snd A A ≫ rm.act a)).left)) →
    ∀ (c d : 𝔠.elt) (a b : 𝓞 F), a • d = b • c → ∀ (T : Over S) (y : T ⟶ A),
      HasGen ((P c).pull (lift (fst A T) (snd A T ≫ y)).left) →
      HasGen ((P d).pull (lift (fst A T) (snd A T ≫ (y ≫ rm.act a))).left) := by
  intro F _ _ 𝔠 S A _ rm P hP hsymm hsmul c d a b had T y hy
  have sy : ∀ c (Y : Over S) (u v : Y ⟶ A), evc (hP c) u v = evc (hP c) v u := by
    intro c Y u v
    have hs : ((P c).pull (lift (snd A A) (fst A A)).left).IsLB := pull_isLB (hP c) _
    rw [evc_congr (hP c) hs (hsymm c) u v]
    exact (evc_ev (hP c) (snd A A) (fst A A) hs u v).trans (by rw [lift_snd, lift_fst])
  have sm : ∀ (a : 𝓞 F) c (Y : Over S) (u v : Y ⟶ A), evc (hP (a • c)) u v = evc (hP c) u (v ≫ rm.act a) := by
    intro a c Y u v
    have hs : ((P c).pull (lift (fst A A) (snd A A ≫ rm.act a)).left).IsLB := pull_isLB (hP c) _
    rw [evc_congr (hP (a • c)) hs (hsmul a c) u v]
    exact (evc_ev (hP c) (fst A A) (snd A A ≫ rm.act a) hs u v).trans (by rw [lift_fst, lift_snd_assoc])
  have h0 : evc (hP c) (fst A T) (snd A T ≫ y) = 0 := (triv_ev_iff (hP c) _ _).1 hy
  have h1 := congrArg (CechPic.pull (lift (fst A T ≫ rm.act b) (snd A T)).left) h0
  rw [pull_evc, map_zero, lift_fst, lift_snd_assoc] at h1
  have e1 := sm a d (A ⊗ T) (fst A T) (snd A T ≫ y)
  rw [had] at e1
  show Triv _
  rw [triv_ev_iff (hP d), ← Category.assoc, ← e1, sy, sm, sy]
  exact h1

end GlobalTheory.KerShift
