import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfA
open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Sloc.AdaptExpand

variable {D : D7}

theorem frame_castSucc {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (i : Fin D.R.rS) :
    frame F (Fin.castSucc i) = F.fl.e i := by
  simp [frame, Formalism.MainNotions.S.FlagG.fvec]

theorem exists_coeff {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (b : Fin (D.R.rS + 1)) (x : (VS D).V)
    (hx : x ∈ Xflag F b.val) :
    ∃ l : Fin D.R.rS → D.host.E, (∀ i, b.val ≤ i.val → l i = 0) ∧ x = ∑ i, l i • F.fl.e i := by
  have hx' : x ∈ Submodule.span D.host.E (F.fl.e '' {i | i.1 < b.val}) := hx
  rw [Finsupp.mem_span_image_iff_linearCombination] at hx'
  obtain ⟨l, hl, rfl⟩ := hx'
  refine ⟨l, fun i hi => ?_, ?_⟩
  · by_contra h
    have := hl (Finsupp.mem_support_iff.2 h)
    simp only [Set.mem_setOf_eq] at this
    omega
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; simp

theorem exists_coeff_frame {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (b : Fin (D.R.rS + 1)) (x : (VS D).V)
    (hx : x ∈ Xflag F b.val) :
    ∃ u : Fin (D.R.rS + 1) → D.host.E, (∀ c, b ≤ c → u c = 0) ∧ x = ∑ c, u c • frame F c := by
  obtain ⟨l, hl, rfl⟩ := exists_coeff F b x hx
  refine ⟨Fin.snoc (α := fun _ => D.host.E) l 0, fun c hc => ?_, ?_⟩
  · induction c using Fin.lastCases with
    | last => simp
    | cast i =>
      simp only [Fin.snoc_castSucc]
      exact hl i (by simpa [Fin.le_def] using hc)
  · rw [Fin.sum_univ_castSucc]
    simp [frame_castSucc]

theorem adapt_expand : ∀ (D : D7) {T : D.host.E} (F0 F : LFlag (VS D) D.R.rS T) (g : GV D), Adapt g F0 F → ∀ (Z : LocDat D) (p : PlF D) (Af : Fin (D.R.rS + 1) → Vp D p), Af = (fun a => frFac Z.δ p a • baseChange₂ D p (frame F a)) → ∃ B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep, (∀ a b, b < a → B a b = 0) ∧ (∀ a, B a a = Ring.inverse (frFac Z.δ p a)) ∧ ∀ b, baseChange₂ D p (g (frame F0 b)) = ∑ a, B a b • Af a := by
  intro D T F0 F g hg Z p Af hAf
  subst hAf
  have hu := fun c => Formalism.L2.SG.Pf.ScalarFramePf.isUnit_frFac Z p c
  choose u hu0 hux using fun b => exists_coeff_frame F b _ (hg.2 b)
  refine ⟨fun a b => ((D.s.atP p).ιE (u b a) + if a = b then 1 else 0) * Ring.inverse (frFac Z.δ p a),
    fun a b hab => ?_, fun a => ?_, fun b => ?_⟩
  · simp [hu0 b a hab.le, (ne_of_lt hab).symm]
  · simp [hu0 a a le_rfl]
  · have e1 : g (frame F0 b) = frame F b + ∑ c, u b c • frame F c := by
      rw [← hux b]; abel
    rw [e1, map_add, map_sum]
    simp only [baseChange_smul₂]
    have e2 : ∀ a, (((D.s.atP p).ιE (u b a) + if a = b then 1 else 0) * Ring.inverse (frFac Z.δ p a)) •
        (frFac Z.δ p a • baseChange₂ D p (frame F a)) =
        (D.s.atP p).ιE (u b a) • baseChange₂ D p (frame F a) + if a = b then baseChange₂ D p (frame F a) else 0 := by
      intro a
      rw [smul_smul, mul_assoc, Ring.inverse_mul_cancel _ (hu a), mul_one, add_smul]
      split_ifs <;> simp
    simp only [e2, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    abel

end GlobalTheory.Sloc.AdaptExpand
