import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitriangularFramesGramEqCellPointStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AtPtRel
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Saturated
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

namespace GlobalTheory.Unfold.BasePt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem frame_castSucc {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (i : Fin D.R.rS) :
    frame F i.castSucc = F.fl.e i := by
  simp [frame, FlagG.fvec]

theorem tri_of_adapt {T : D.host.E} (g : GV D) (F G : LFlag (VS D) D.R.rS T) (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (h : ∀ a : Fin (D.R.rS + 1), g (frame F a) - frame G a ∈ Xflag G a.val) :
    GlobalTheory.LocOver.Tri D.host.E (frame G) (frame (Formalism.L2.SG.Saturated.mapL g hg F)) := by
  have ex : ∀ b : Fin (D.R.rS + 1), ∃ l : Fin D.R.rS →₀ D.host.E,
      l ∈ Finsupp.supported D.host.E D.host.E {i : Fin D.R.rS | i.val < b.val} ∧
        Finsupp.linearCombination D.host.E G.fl.e l = g (frame F b) - frame G b := fun b =>
    (Finsupp.mem_span_image_iff_linearCombination D.host.E).1 (h b)
  choose l hl hx using ex
  have hz : ∀ b (i : Fin D.R.rS), ¬ i.val < b.val → l b i = 0 := fun b i hi =>
    (Finsupp.mem_supported' D.host.E (l b)).1 (hl b) i hi
  refine ⟨fun a b => (if a = b then 1 else 0) + (if h : a.val < D.R.rS then l b ⟨a.val, h⟩ else 0), ⟨?_, ?_⟩, ?_⟩
  · intro a b hba
    dsimp only
    rw [if_neg (ne_of_gt hba), zero_add]
    split_ifs with h'
    · exact hz b _ (by show ¬ a.val < b.val; have := Fin.lt_def.1 hba; omega)
    · rfl
  · intro a
    dsimp only
    rw [if_pos rfl]
    split_ifs with h'
    · rw [hz a _ (by simp), add_zero]
    · rw [add_zero]
  · intro b
    rw [Formalism.L2.SG.Saturated.frame_mapL]
    simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_irrefl, dif_neg, not_false_eq_true,
      zero_smul, add_zero, frame_castSucc, Fin.eta]
    have e := hx b
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at e
    rw [e]
    abel

theorem term_at_base_point : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
      (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 →
      ∀ (t : TauC Y u u') (Λ : LV D), TG F F' t Λ → t.G ≠ 0 ∧ ptPN t = toPts w := by
  intro D X Y u u' F F' w hZ hG t Λ hTG
  obtain ⟨g, ⟨hg, h1⟩, ⟨-, h2⟩, -⟩ := hTG
  have hT : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  have hT' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u').A.T_prime.ne_zero
  have hcell : IsInCell (ZhatOM (ZhatL F F')) w := by
    refine ⟨1, 1, fun i j => ⟨fun hij => Matrix.one_apply_ne (ne_of_lt hij), fun hij => by subst hij; exact Matrix.one_apply_eq i⟩,
      fun i j => ⟨fun hij => Matrix.one_apply_ne (ne_of_gt hij), fun hij => by subst hij; exact Matrix.one_apply_eq i⟩, ?_⟩
    rw [hZ, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨-, hB⟩ := GlobalTheory.T.exists_unitriangular_frames_gram_eq_cell_point D F F' w hT hT' hcell
  obtain ⟨hcell2, hG2⟩ := hB _ _ (tri_of_adapt g (lf D (X.Fu u)) F hg h1) (tri_of_adapt g t.frame F' hg h2)
  replace hcell2 : IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) t.frame)) w :=
    (congrArg (fun Z => IsInCell (ZhatOM Z) w) (Formalism.L2.SG.Saturated.zhat_mapL g hg (lf D (X.Fu u)) t.frame)).mp hcell2
  replace hG2 : Gval (lf D (X.Fu u)) t.frame = Gval F F' :=
    (Formalism.L2.SG.Saturated.gval_mapL g hg (lf D (X.Fu u)) t.frame).symm.trans hG2
  have hGt : t.G ≠ 0 := by rw [Formalism.L2.SG.Pf.SatGram.gterm_G Y t, hG2]; exact hG
  have hat : t.toTerm.atPt w := ⟨t.frame, ⟨t.rep.2.2.2.2, rfl⟩, fun h0 => hG (hG2.symm.trans h0), hcell2⟩
  have hrel : t.toTerm.relevant := Formalism.L2.SG.Pf.FinXP.atPtRelevant_holds D u u' _ _ t.toTerm w hat
  have hsp := Formalism.L2.SG.PairVal.ptOf_spec t.toTerm ⟨w, hat, hrel⟩
  have heq := Formalism.L2.SG.Pf.cellPtUnique_of Formalism.L2.SG.Pf.cell_point_uniqueness
    (Formalism.L2.SG.Closed.TermFun_holds D u u') (Y.rowsOK u) t.toTerm _ _ hsp hat
  exact ⟨hGt, by show toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm) = toPts w; rw [heq]⟩

end GlobalTheory.Unfold.BasePt
