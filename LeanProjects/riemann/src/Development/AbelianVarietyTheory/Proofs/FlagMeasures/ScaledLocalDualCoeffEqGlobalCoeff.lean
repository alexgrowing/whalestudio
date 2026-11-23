import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Ia

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLatXS

theorem scaled_local_coef_eq :
    ∀ (D : D7) (T : D.host.E) (G : LFlag (VS D) D.R.rS T) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ (p : PlF D) (a : Fin D.R.rS) (x : (VS D).V), x ∈ G.fl.X → frFac Z.δ p a.castSucc * (locH Z p).h (baseChange₂ D p x) ((A p).es a) = (D.s.atP p).ιE (G.fl.coefX x a) := by
  intro D T G Z A hA p a x hx

  have hes : ∀ b : Fin D.R.rS, frFac Z.δ p b.castSucc * (locH Z p).h (baseChange₂ D p (G.fl.e b)) ((A p).es a) =
      if b = a then 1 else 0 := by
    intro b
    have h1 := (A p).h_es b a
    rw [hA p] at h1
    rw [← (locH Z p).h_smul_left]
    simpa [frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc] using h1
  have hunit : ∀ b : Fin D.R.rS, IsUnit (frFac Z.δ p b.castSucc) := by
    intro b
    have h1 := (A p).h_es b b
    rw [hA p] at h1
    rw [if_pos rfl, (locH Z p).h_smul_left] at h1
    exact isUnit_iff_exists_inv.mpr ⟨_, by simpa [frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc] using h1⟩
  have hzero : ∀ b : Fin D.R.rS, b ≠ a → (locH Z p).h (baseChange₂ D p (G.fl.e b)) ((A p).es a) = 0 := by
    intro b hb
    have h1 := hes b
    rw [if_neg hb] at h1
    exact (hunit b).mul_right_eq_zero.mp h1

  have hxs : x ∈ Submodule.span D.host.E (Set.range G.fl.e) := hx
  have hexp : x = ∑ b, G.fl.coefX x b • G.fl.e b := by
    have h2 := G.fl.e_indep.linearCombination_repr ⟨x, hxs⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at h2
    simp only [Formalism.MainNotions.S.FlagG.coefX, dif_pos hxs]
    exact h2.symm

  have hsum : ∀ (s : Finset (Fin D.R.rS)) (v : Fin D.R.rS → Vp D p) (y : Vp D p),
      (locH Z p).h (∑ b ∈ s, v b) y = ∑ b ∈ s, (locH Z p).h (v b) y := by
    intro s v y
    induction s using Finset.induction_on with
    | empty => simpa using (locH Z p).h_zero_left y
    | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, (locH Z p).h_add_left, ih]
  have hbc : baseChange₂ D p x = ∑ b, (D.s.atP p).ιE (G.fl.coefX x b) • baseChange₂ D p (G.fl.e b) := by
    conv_lhs => rw [hexp]
    rw [map_sum]
    exact Finset.sum_congr rfl fun b _ => baseChange_smul₂ p _ _
  rw [hbc, hsum, Finset.mul_sum, Finset.sum_eq_single a]
  · rw [(locH Z p).h_smul_left, mul_left_comm, hes a, if_pos rfl, mul_one]
  · intro b _ hb
    rw [(locH Z p).h_smul_left, hzero b hb, mul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

end GlobalTheory.RowLatXS
