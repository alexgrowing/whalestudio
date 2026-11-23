import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveLineBundleFamilyOfGeometricFibresStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsLiftPt

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem exists_fam_of_pull : ∀ (S : Scheme.{0}) (A U U' : Over S) [GrpObj A] [IsLocallyNoetherian U.left],
    IsAbelianScheme A → ∀ (p : U' ⟶ U), IsFinite p.left → Surjective p.left → ∀ (N' : LB (A ⊗ U').left)
    (h : Fam A N') (c : Pic (A ⊗ U).left), GlobalTheory.CechPic.pull (A ◁ p).left c = cls N' h.isLB →
    ∃ M : LB (A ⊗ U).left, Fam A M ∧ Same A M N' p (𝟙 U') := by
  intro S A U U' _ _ hA p hfin hsurj N' h c hc
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  have key : ∀ (Y : Over S) (a : Y ⟶ A) (u : Y ⟶ U'), evc hL a (u ≫ p) = evc h.isLB a u := by
    intro Y a u
    have e : lift a (u ≫ p) = lift a u ≫ (A ◁ p) := by ext <;> simp
    rw [evc, e, Over.comp_left, pull_comp, hc]
    rfl
  obtain ⟨M, hM, hMc⟩ := cls_surj (cls L hL - CechPic.pull (snd A U).left (evc hL (1 : U ⟶ A) (𝟙 U)))
  have form : ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ U), evc hM a t = evc hL a t - evc hL (1 : Y ⟶ A) t := by
    intro Y a t
    rw [evc, hMc, map_sub, ← pull_comp, ← Over.comp_left, lift_snd, pull_evc, MonObj.comp_one, Category.comp_id]
    rfl
  have keyM : ∀ (Y : Over S) (a : Y ⟶ A) (u : Y ⟶ U'), evc hM a (u ≫ p) = evc h.isLB a u := by
    intro Y a u
    rw [form, key, key, h.add.evc_one h.isLB, sub_zero]
  refine ⟨M, ⟨hM, GlobalTheory.T.isAdditive_lineBundleFamily_of_geometricFibres S A U hA M hM ((triv_ev_iff hM _ _).2 (by rw [form, sub_self])) ?_⟩, ?_⟩
  · intro K _ _ s t
    haveI := hfin
    haveI := hsurj
    obtain ⟨b, hb⟩ := exists_lift_pt p.left t.left
    let t' : Over.mk s ⟶ U' := Over.homMk b (by
      rw [← Over.w p, ← Category.assoc, hb, Over.w t])
    have ht : t = t' ≫ p := Over.OverMorphism.ext hb.symm
    rw [ht]
    refine (isAdditive_iff (pull_isLB hM _)).2 fun Y a a' y ↦ ?_
    have e : ∀ a₀ : Y ⟶ A, evc (pull_isLB hM _) a₀ y = evc h.isLB a₀ (y ≫ t') := fun a₀ ↦ by
      rw [evc_ev hM, lift_fst, lift_snd_assoc, ← Category.assoc, keyM]
    rw [e, e, e]
    exact (isAdditive_iff h.isLB).1 h.add _ _ _ _
  · rw [same_iff hM h.isLB, Category.comp_id]
    exact keyM _ _ _

end GlobalTheory.Pinch
