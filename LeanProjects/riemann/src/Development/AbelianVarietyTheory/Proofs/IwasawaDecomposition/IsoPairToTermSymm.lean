import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ECure
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ConcreteSettingExists

noncomputable section

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SRe

variable {D : D7} (Z : New D) {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)

set_option maxHeartbeats 4000000 in

theorem isoPair_toTerm (s : TT Y u u') : (eTT Z Y u u' s).toTerm = eRT Z Y u u' s.toTerm := (by with_unfolding_all exact ((Eq.refl (eRT Z Y u u' s.toTerm)) :))

set_option maxHeartbeats 4000000 in

theorem isoPair_toTerm_symm (s : TT (reY Z Y) (wd Z u) (wd Z u')) :
    ((eTT Z Y u u').symm s).toTerm = (eRT Z Y u u').symm s.toTerm := (by with_unfolding_all exact ((Eq.refl ((eTT Z Y u u').symm s).toTerm) :))

set_option maxHeartbeats 4000000 in

theorem isoPair_row (a b : TT Y u u') :
    rowOf (reY Z Y).TR ((reY Z Y).cs (wd Z u)) ((reY Z Y).cs (wd Z u')) (eTT Z Y u u' a) =
        rowOf (reY Z Y).TR ((reY Z Y).cs (wd Z u)) ((reY Z Y).cs (wd Z u')) (eTT Z Y u u' b) ↔
      rowOf Y.TR (Y.cs u) (Y.cs u') a = rowOf Y.TR (Y.cs u) (Y.cs u') b := (by with_unfolding_all exact ((Iff.rfl : rowOf Y.TR (Y.cs u) (Y.cs u') a = rowOf Y.TR (Y.cs u) (Y.cs u') b ↔ _) :))

set_option maxHeartbeats 4000000 in

theorem isoPair_row_symm (a b : TT (reY Z Y) (wd Z u) (wd Z u')) :
    rowOf Y.TR (Y.cs u) (Y.cs u') ((eTT Z Y u u').symm a) = rowOf Y.TR (Y.cs u) (Y.cs u') ((eTT Z Y u u').symm b) ↔
      rowOf (reY Z Y).TR ((reY Z Y).cs (wd Z u)) ((reY Z Y).cs (wd Z u')) a =
        rowOf (reY Z Y).TR ((reY Z Y).cs (wd Z u)) ((reY Z Y).cs (wd Z u')) b := by
  have := isoPair_row Z Y u u' ((eTT Z Y u u').symm a) ((eTT Z Y u u').symm b)
  simpa only [Equiv.apply_symm_apply] using this.symm

set_option maxHeartbeats 4000000 in

theorem isoPair_s0T (a b : TT Y u u') : s0T (eTT Z Y u u' a) (eTT Z Y u u' b) = s0T a b := (by with_unfolding_all exact (
  (Eq.refl (s0T a b)) :))

set_option maxHeartbeats 4000000 in

theorem isoPair_lift (a b : TT Y u u') : liftScalar (eTT Z Y u u' a) (eTT Z Y u u' b) ↔ liftScalar a b := (by exact (Iff.rfl : liftScalar a b ↔ liftScalar a b))

def isoPairFib (t : RT Y u u') : fib Y t ≃ fib (reY Z Y) (eRT Z Y u u' t) where
  toFun s := ⟨eTT Z Y u u' s.1, by rw [isoPair_toTerm, s.2]⟩
  invFun s := ⟨(eTT Z Y u u').symm s.1, by rw [isoPair_toTerm_symm, s.2, Equiv.symm_apply_apply]⟩
  left_inv s := Subtype.ext (Equiv.symm_apply_apply _ _)
  right_inv s := Subtype.ext (Equiv.apply_symm_apply _ _)

def isoPairE : RP Y u u' ≃ RP (reY Z Y) (wd Z u) (wd Z u') where
  toFun q := ⟨(eRT Z Y u u' q.1.1, eRT Z Y u u' q.1.2), by
    obtain ⟨s₁, s₂, hs⟩ := q.2
    exact ⟨isoPairFib Z Y u u' _ s₁, isoPairFib Z Y u u' _ s₂, (isoPair_row Z Y u u' _ _).2 hs⟩⟩
  invFun q := ⟨((eRT Z Y u u').symm q.1.1, (eRT Z Y u u').symm q.1.2), by
    obtain ⟨s₁, s₂, hs⟩ := q.2
    refine ⟨⟨(eTT Z Y u u').symm s₁.1, by rw [isoPair_toTerm_symm, s₁.2]⟩,
      ⟨(eTT Z Y u u').symm s₂.1, by rw [isoPair_toTerm_symm, s₂.2]⟩, (isoPair_row_symm Z Y u u' _ _).2 hs⟩⟩
  left_inv q := Subtype.ext (by simp)
  right_inv q := Subtype.ext (by simp)

set_option maxHeartbeats 4000000 in

theorem rp_iso_pair : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X) (h : FinX Y) (h' : FinX (reY Z Y))
    (u u' : D.what₂.Word), ∃ e : RP Y u u' ≃ RP (reY Z Y) (wd Z u) (wd Z u'), ∀ q, eRT Z Y u u' q.1.1 = (e q).1.1 ∧
      eRT Z Y u u' q.1.2 = (e q).1.2 ∧ s0T q.l1 q.l2 = s0T (e q).l1 (e q).l2 ∧
      (liftScalar q.l1 q.l2 ↔ liftScalar (e q).l1 (e q).l2) ∧
      pvR h u u' q = pvR h' (wd Z u) (wd Z u') (e q) := by
  intro D Z X Y h h' u u'
  refine ⟨isoPairE Z Y u u', fun q => ⟨rfl, rfl, ?_⟩⟩

  set a := (eTT Z Y u u').symm (isoPairE Z Y u u' q).l1 with ha
  set b := (eTT Z Y u u').symm (isoPairE Z Y u u' q).l2 with hb
  have hA : (isoPairE Z Y u u' q).l1 = eTT Z Y u u' a := by simp [a]
  have hB : (isoPairE Z Y u u' q).l2 = eTT Z Y u u' b := by simp [b]
  have h1 : q.l1.toTerm = q.1.1 := q.2.choose.2
  have h2 : q.l2.toTerm = q.1.2 := q.2.choose_spec.choose.2
  have hr : rowOf Y.TR (Y.cs u) (Y.cs u') q.l1 = rowOf Y.TR (Y.cs u) (Y.cs u') q.l2 := q.2.choose_spec.choose_spec
  have e1 : (isoPairE Z Y u u' q).l1.toTerm = eRT Z Y u u' q.1.1 := (isoPairE Z Y u u' q).2.choose.2
  have e2 : (isoPairE Z Y u u' q).l2.toTerm = eRT Z Y u u' q.1.2 := (isoPairE Z Y u u' q).2.choose_spec.choose.2
  have er := (isoPairE Z Y u u' q).2.choose_spec.choose_spec
  have ha1 : a.toTerm = q.1.1 := by rw [isoPair_toTerm_symm]; erw [e1]; simp
  have hb1 : b.toTerm = q.1.2 := by rw [isoPair_toTerm_symm]; erw [e2]; simp
  have hab : rowOf Y.TR (Y.cs u) (Y.cs u') a = rowOf Y.TR (Y.cs u) (Y.cs u') b :=
    (isoPair_row_symm Z Y u u' _ _).2 er
  obtain ⟨hs, hl⟩ := h.pairIndep u u' q.l1 q.l2 a b (h1.trans ha1.symm) (h2.trans hb1.symm) hr hab
  refine ⟨?_, ?_, ?_⟩
  · rw [hA, hB, isoPair_s0T]; exact hs
  · rw [hA, hB, isoPair_lift]; exact hl
  · letI := h.fibFT q.1.1
    letI := h.fibFT q.1.2
    letI := h'.fibFT (eRT Z Y u u' q.1.1)
    letI := h'.fibFT (eRT Z Y u u' q.1.2)
    unfold pvR
    refine Fintype.sum_equiv ((isoPairFib Z Y u u' q.1.1).prodCongr (isoPairFib Z Y u u' q.1.2)) _ _
      fun r => ?_
    exact (by with_unfolding_all exact ((Eq.refl (if rowOf Y.TR (Y.cs u) (Y.cs u') r.1.1 = rowOf Y.TR (Y.cs u) (Y.cs u') r.2.1
        then inner ℂ (vT Y u u' r.2.1) (vT Y u u' r.1.1) else (0 : ℂ))) :))

end GlobalTheory.Mem.SRe
