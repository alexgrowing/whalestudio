import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.WeightConstB
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalSplitTypeMixedSecond
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RowsAbsX
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SplittingAdmissibleOfTermData

noncomputable section

namespace Formalism.L2.SG.WConst

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pos

variable {D : D7}

theorem gPoint_eq_gval {T T' : ℕ} (F : LFlag (VS D) D.R.rS (T : D.host.E)) (F' : LFlag (VS D) D.R.rS (T' : D.host.E))
    (w : Point D.host.E (D.R.rS + 1)) (hc : IsInCell (Formalism.MainNotions.S.ZhatOM (ZhatL F F')) w) :
    Gpt T T' w = Gval F F' := by
  obtain ⟨L, U, hL, hU, hZ⟩ := hc
  have hL' : IsLo L := ⟨fun a => (hL a a).2 rfl, fun a b hab => (hL a b).1 hab⟩
  have hU' : IsUp U := ⟨fun a => (hU a a).2 rfl, fun a b hab => (hU b a).1 hab⟩
  have hS : Formalism.MainNotions.S.ZhatOM (ZhatL F F') = ZhatL F F' * Sg D.host.E D.R.rS := by
    ext a b
    simp [Formalism.MainNotions.S.ZhatOM, Sg, mul_diagonal, mul_comm]
  have key : ∀ l (hl : l ≤ D.R.rS + 1), leadMinorE (ZhatL F F') l * epsL (D := D) D.R.rS l hl = Dmin w l := by
    intro l hl
    rw [← leadMinor_Sg, ← hS, hZ, leadMinor_LMU hL' hU', dmin_eq']
  have n1 := norm_eq_of _ _ _ (key (D.R.rS + 1) le_rfl) (epsL_sq _ _) (star_epsL _ _)
  have n2 := norm_eq_of _ _ _ (key D.R.rS (Nat.le_succ _)) (epsL_sq _ _) (star_epsL _ _)
  simp only [Gval, Gflag, Gpt, conjF_star]
  unfold Formalism.MainNotions.S.Dl
  rw [n1, n2]

theorem atPt_totPos {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
    (t : Formalism.L2.SG.TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)) (h : t.atPt w) :
    TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w) := by
  obtain ⟨F', ⟨hP, -⟩, hG, hc⟩ := h
  have e := gPoint_eq_gval (T := Tu D u) (T' := Tu D u') (lf D F0) F' w hc
  intro τ
  change 0 < (D.host.emb (D.eTau τ) (Gpt (Tu D u) (Tu D u') w)).re
  rw [e]
  exact (Formalism.MainNotions.LatticeGluingRadicals.b_G_pos (Formalism.MainNotions.LatticeGluingRadicals.p_starConj D) (Formalism.MainNotions.BridgeLemma.tie_Tu_pos D u) (lf D F0) F' rfl
    hP.1.2 hG (Formalism.MainNotions.LatticeGluingRadicals.p_posX D _ (Formalism.MainNotions.BridgeLemma.tie_Tu_pos D u) _) _).1

end Pos

section Use

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)

theorem eligTotPos_holds : EligTotPos X Y u u' := fun t w _ h => atPt_totPos t w h

theorem kapN_pos : 0 < Formalism.L2.SG.MassDataConc.kapN D := by
  unfold Formalism.L2.SG.MassDataConc.kapN
  have hr : 0 < D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE
    exact Real.rpow_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero _))) _
  have hg : 0 < ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos)
  exact mul_pos (pow_pos hr _) (inv_pos.mpr (pow_pos hg _))

theorem weightBound_holds {nc : ℝ} (hnc : 0 < nc) : Formalism.L2.SG.RowsAbsX.WeightBound X Y u u' nc := by
  refine ⟨Real.sqrt (Formalism.L2.SG.MassDataConc.ngFac D / (Formalism.L2.SG.MassDataConc.kapN D * nc)), fun p w hp hreal ht => ?_⟩
  obtain ⟨t, -, hat⟩ := ht
  have hT := atPt_totPos t w hat
  rw [nW_eq X u u' p w hp hreal hT hnc]
  have hK : 0 ≤ Formalism.L2.SG.MassDataConc.ngFac D / (Formalism.L2.SG.MassDataConc.kapN D * nc) := by
    refine div_nonneg ?_ (mul_pos kapN_pos hnc).le
    unfold Formalism.L2.SG.MassDataConc.ngFac
    exact pow_nonneg (Real.sqrt_nonneg _) _
  have hn0 : 0 ≤ n0 nc (D.mem u).A.T (D.mem u').A.T w := by
    unfold n0
    exact mul_nonneg hnc.le (pow_nonneg (Real.sqrt_nonneg _) _)
  rw [Real.sqrt_mul hK, Real.sqrt_mul hn0, Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]

end Use

end Formalism.L2.SG.WConst
