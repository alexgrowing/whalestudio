import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LeadingMinors
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BlockEndMinorsOfCell
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepNormOneOfLeaves
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiTrivOut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.NonRelCharCHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.LsSetresAvgW
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TermTiesEmptyOfLargeIndex

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.ThB Formalism.MainNotions.BesselShellMomentBounds Formalism.MainNotions.LatticeGluingRadicals Formalism.MainNotions.BridgeLemma
  Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut

namespace Formalism.L2.SG.PointUniformity

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Minor

variable {D : D7}

theorem lead_sign (Z : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (l : ℕ) (hl : l ≤ D.R.rS + 1) :
    leadMinorK (ZhatOM Z) l hl * D.host.conj (leadMinorK (ZhatOM Z) l hl) =
      leadMinorK Z l hl * D.host.conj (leadMinorK Z l hl) := by
  have e : ∀ W : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E,
      ((ZhatOM W).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
        (∏ j : Fin l, ((-1 : D.host.E) ^ (D.R.rS - (Fin.castLE hl j).val))) *
          (W.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
    intro W
    rw [← Matrix.det_mul_row]
    rfl
  simp only [leadMinorK]
  rw [e Z, Finset.prod_pow_eq_pow_sum]
  rcases neg_one_pow_eq_or D.host.E (∑ j : Fin l, (D.R.rS - (Fin.castLE hl j).val)) with h | h <;>
    rw [h] <;> simp

theorem gglob_of_cell {T T' : ℕ} (F : LFlag (VS D) D.R.rS (T : D.host.E)) (F' : LFlag (VS D) D.R.rS (T' : D.host.E))
    (p : Point D.host.E (D.R.rS + 1)) (hc : IsInCell (ZhatOM (ZhatL F F')) p) :
    Gglob D T T' p = Gval F F' := by
  obtain ⟨L, U, hL, hU, hZ⟩ := hc
  have hinv : ∀ (l : ℕ) (hl : l ≤ D.R.rS + 1),
      leadMinorK (ZhatOM (ZhatL F F')) l hl = leadMinorK (ptMat p) l hl := by
    intro l hl
    rw [leadMinorK_eq, leadMinorK_eq, hZ]
    exact Formalism.HermitianLatticeCounting.Final.ExpansionTerms.leadingMinorUnipotentInvariant _ _ _ _ _ _ ⟨fun i => (hL i i).2 rfl, fun i j h => (hL i j).1 h⟩
      ⟨fun i => (hU i i).2 rfl, fun i j h => (hU i j).1 h⟩
  unfold Gglob
  rw [← hinv, ← hinv, lead_sign, lead_sign]
  unfold Gval Gflag Dl
  clear hinv hZ hL hU L U
  simp only [Formalism.MainNotions.S.Inh.tie_star]
  have hE : ∀ (l : ℕ) (hl : l ≤ D.R.rS + 1), leadMinorE (Zhat F.fl F'.fl) l = leadMinorK (ZhatL F F') l hl := by
    intro l hl
    unfold leadMinorE leadMinorK
    rw [dif_pos hl]
  rw [hE _ le_rfl, hE _ (Nat.le_succ _)]

theorem det_isIntegral {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) (hM : ∀ i j, IsIntegral ℤ (M i j)) :
    IsIntegral ℤ M.det := by
  have key : M.det ∈ integralClosure ℤ D.host.E := by
    rw [Matrix.det_apply]
    refine Subalgebra.sum_mem _ (fun σ _ => ?_)
    rw [Units.smul_def]
    refine Subalgebra.zsmul_mem _ ?_ _
    exact Subalgebra.prod_mem _ (fun i _ => (mem_integralClosure_iff ..).2 (hM _ _))
  exact (mem_integralClosure_iff ..).1 key

end Minor

theorem rowPt_of {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (hG : t.toTerm.G ≠ 0) (hv : (Y.tO u u').vec t ≠ 0) :
    Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T (Formalism.L2.SG.PairVal.ptOf t.toTerm) := by
  have hrel : t.toTerm.relevant := by
    by_contra hr
    apply hv
    have h0 : OOt t = 0 := Formalism.L2.SG.TermOp.Vanish.ooVanish_of Formalism.L2.SG.TermOp.Vanish.avgCore
      Formalism.L2.SG.Pf.ginfUnimod_holds Formalism.L2.SG.Pf.nLamNinf_holds Formalism.L2.SG.Pf.chiTrivialC_outright
      Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds
      Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds Formalism.L2.SG.NonRelPf.nonRelCharC_holds Y t hr
    show vec (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = 0
    unfold vec ampN
    rw [h0]
    simp
    rfl
  obtain ⟨w, hw⟩ := Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u' t.toTerm hG hrel
  obtain ⟨F2, ⟨hP2, -⟩, hG2, hcell⟩ := Formalism.L2.SG.PairVal.ptOf_spec t.toTerm ⟨w, hw, hrel⟩
  have hrow := (Y.rowsOK u).1 t.toTerm.lam t.toTerm.mem
  have hF : ∀ b, frame (lf D (X.Fu u)) b ∈ t.toTerm.lam :=
    Formalism.L2.SG.NGCut.PtPf.frame_mem _ hrow.2.1.2.2.1.1 hrow.2.2
  have hF2 : ∀ b, frame F2 b ∈ t.toTerm.lam := Formalism.L2.SG.NGCut.PtPf.frame_mem _ hP2.1.1 hP2.2.2.2
  have hZint : ∀ i j, IsIntegral ℤ (ZhatOM (ZhatL (lf D (X.Fu u)) F2) i j) :=
    Formalism.L2.SG.NGCut.PtPf.zhatOM_isIntegral _ _ hrow.2.1.2.1 hF hF2
  have hGg : Gglob D (D.mem u).A.T (D.mem u').A.T (Formalism.L2.SG.PairVal.ptOf t.toTerm) = Gval (lf D (X.Fu u)) F2 :=
    gglob_of_cell (lf D (X.Fu u)) F2 _ hcell
  have hTu := tie_Tu_pos D u
  refine ⟨⟨⟨ZhatOM (ZhatL (lf D (X.Fu u)) F2), hZint, hcell⟩, by rw [hGg]; exact hG2, ?_⟩, fun v => ?_⟩
  ·
    obtain ⟨L, U, hL, hU, hZ⟩ := hcell
    have hlm : ∀ l (hl : l ≤ D.R.rS + 1), IsIntegral ℤ (leadMinorK (ptMat (Formalism.L2.SG.PairVal.ptOf t.toTerm)) l hl) := by
      intro l hl
      have e : leadMinorK (ptMat (Formalism.L2.SG.PairVal.ptOf t.toTerm)) l hl =
          leadMinorK (ZhatOM (ZhatL (lf D (X.Fu u)) F2)) l hl := by
        rw [leadMinorK_eq, leadMinorK_eq]
        exact Formalism.L2.SG.NGCut.LeadingMinorIntegrality.lead_cell _ _ ⟨L, U, hL, hU, hZ⟩ l
      rw [e]
      exact det_isIntegral _ fun i j => hZint _ _
    have hconj : ∀ x : D.host.E, IsIntegral ℤ x → IsIntegral ℤ (D.host.conj x) := fun x hx => by
      rw [← Formalism.MainNotions.S.Inh.tie_star]
      exact hx.map (starRingEnd D.host.E).toIntAlgHom
    unfold Gglob
    have hn : ∀ n : ℕ, IsIntegral ℤ (n : D.host.E) := fun n => by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := (n : ℤ)))
    exact ((hlm _ _).mul (hconj _ (hlm _ _))).sub (((hn _).mul (hn _)).mul ((hlm _ _).mul (hconj _ (hlm _ _))))
  ·
    have hpos := (b_G_pos (p_starConj D) hTu (lf D (X.Fu u)) F2 rfl hP2.1.2 hG2
      (p_posX D _ hTu (lf D (X.Fu u))) (plEmb D v)).1
    have hpos2 : 0 < ((plEmb D v) (Gglob D (D.mem u).A.T (D.mem u').A.T (Formalism.L2.SG.PairVal.ptOf t.toTerm))).re := by
      calc (0 : ℝ) < ((plEmb D v) (Gval (lf D (X.Fu u)) F2)).re := hpos
        _ = _ := by rw [hGg]
    rw [plEmb_Gglob, Complex.ofReal_re] at hpos2
    rw [GPoint_loc]
    have hc : 0 < ((∏ i : Fin D.R.rS, alf D i) ^ 2) ^ 2 := by
      have := Finset.prod_pos (s := Finset.univ) (fun (i : Fin D.R.rS) _ => alf_pos D i)
      positivity
    exact mul_pos hc hpos2

theorem ptUnif' : Formalism.L2.SG.Pf.BDat.PtUnif := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' _ t ht hv => rowPt_of Y u u' t ?_ hv⟩
  intro h0
  apply ht.1
  simp [Full.tO, tOf, Gt, GTerm.G, h0]

theorem ptUnifG : Formalism.L2.SG.Pf.BDat.PtUnifG := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u _ t ht hv => rowPt_of Y u u t ?_ hv⟩
  intro h0
  apply ht.1
  simp [Full.tO, tOf, Gt, GTerm.G, h0]

end Formalism.L2.SG.PointUniformity

end
