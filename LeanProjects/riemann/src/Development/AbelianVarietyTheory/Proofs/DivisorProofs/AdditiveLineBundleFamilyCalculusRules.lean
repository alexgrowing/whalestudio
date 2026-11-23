import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FamCalc

variable {S : Scheme.{0}} {A : Over S}

theorem whisker_eq {Y T : Over S} (y : Y ⟶ T) : A ◁ y = lift (fst A Y) (snd A Y ≫ y) := by
  ext <;> simp

theorem lift_whisker {Y T Z : Over S} (y : Y ⟶ T) (a : Z ⟶ A) (t : Z ⟶ Y) :
    lift a t ≫ A ◁ y = lift a (t ≫ y) := by
  ext <;> simp

theorem pull_whisker_evc {T Y Z : Over S} {N : LB (A ⊗ T).left} (hN : N.IsLB) (y : Y ⟶ T) (a : Z ⟶ A)
    (t : Z ⟶ Y) :
    CechPic.pull (lift a t).left (CechPic.pull (A ◁ y).left (cls N hN)) = evc hN a (t ≫ y) := by
  rw [← pull_comp, ← Over.comp_left, lift_whisker, evc]

theorem evc_whisker {T Y : Over S} {N : LB (A ⊗ T).left} (hN : N.IsLB) (y : Y ⟶ T) :
    evc hN (fst A Y) (snd A Y ≫ y) = CechPic.pull (A ◁ y).left (cls N hN) := by
  rw [evc, whisker_eq]

theorem evc_ev_whisker {T Y Z : Over S} {N : LB (A ⊗ T).left} (hN : N.IsLB) (y : Y ⟶ T)
    (h : (ev N (fst A Y) (snd A Y ≫ y)).IsLB) (a : Z ⟶ A) (t : Z ⟶ Y) :
    evc h a t = evc hN a (t ≫ y) := by
  rw [evc_ev hN, lift_fst, lift_snd_assoc]

theorem famCalc : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], (∀ (T Y : Over S) (N : LB (A ⊗ T).left) (y : Y ⟶ T), Fam A N → Fam A (ev N (fst A Y) (snd A Y ≫ y))) ∧ (∀ (T U Y : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (hN : Fam A N) (hM : Fam A M) (y : Y ⟶ T) (u : Y ⟶ U) (D : LB (A ⊗ Y).left) (hD : D.IsLB), (cls D hD = GlobalTheory.CechPic.pull (A ◁ y).left (cls N hN.isLB) + GlobalTheory.CechPic.pull (A ◁ u).left (cls M hM.isLB) ∨ cls D hD = GlobalTheory.CechPic.pull (A ◁ y).left (cls N hN.isLB) - GlobalTheory.CechPic.pull (A ◁ u).left (cls M hM.isLB)) → Fam A D) ∧ (∀ (T U Y : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (hN : N.IsLB) (hM : M.IsLB) (y : Y ⟶ T) (u : Y ⟶ U), Same A N M y u ↔ GlobalTheory.CechPic.pull (A ◁ y).left (cls N hN) = GlobalTheory.CechPic.pull (A ◁ u).left (cls M hM)) ∧ (∀ (T U Y Z : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (y : Y ⟶ T) (u : Y ⟶ U) (z : Z ⟶ Y), N.IsLB → M.IsLB → Same A N M y u → Same A N M (z ≫ y) (z ≫ u)) ∧ (∀ (T U Y Z : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (y : Y ⟶ T) (z : Z ⟶ Y) (u : Z ⟶ U), N.IsLB → M.IsLB → (Same A (ev N (fst A Y) (snd A Y ≫ y)) M z u ↔ Same A N M (z ≫ y) u)) := by
  intro S A _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro T Y N y hN
    have h : (ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB hN.isLB _
    refine ⟨h, (isAdditive_iff h).2 fun Z a a' t ↦ ?_⟩
    simp only [evc_ev_whisker hN.isLB y h]
    exact (isAdditive_iff hN.isLB).1 hN.add Z a a' (t ≫ y)
  · intro T U Y N M hN hM y u D hD hc
    refine ⟨hD, (isAdditive_iff hD).2 fun Z a a' t ↦ ?_⟩
    have aN := (isAdditive_iff hN.isLB).1 hN.add Z a a' (t ≫ y)
    have aM := (isAdditive_iff hM.isLB).1 hM.add Z a a' (t ≫ u)
    rcases hc with hc | hc
    · have e : ∀ b : Z ⟶ A, evc hD b t = evc hN.isLB b (t ≫ y) + evc hM.isLB b (t ≫ u) := fun b ↦ by
        rw [evc, hc, map_add, pull_whisker_evc, pull_whisker_evc]
      rw [e, e, e, aN, aM]
      abel
    · have e : ∀ b : Z ⟶ A, evc hD b t = evc hN.isLB b (t ≫ y) - evc hM.isLB b (t ≫ u) := fun b ↦ by
        rw [evc, hc, map_sub, pull_whisker_evc, pull_whisker_evc]
      rw [e, e, e, aN, aM]
      abel
  · intro T U Y N M hN hM y u
    rw [same_iff hN hM, evc_whisker, evc_whisker]
  · intro T U Y Z N M y u z hN hM h
    rw [same_iff hN hM] at h ⊢
    have e := congrArg (CechPic.pull (A ◁ z).left) h
    rwa [pull_evc, pull_evc, whiskerLeft_fst, whiskerLeft_snd_assoc, whiskerLeft_snd_assoc] at e
  · intro T U Y Z N M y z u hN hM
    have h : (ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB hN _
    rw [same_iff h hM, same_iff hN hM, evc_ev_whisker hN y h, Category.assoc]

end GlobalTheory.FamCalc
