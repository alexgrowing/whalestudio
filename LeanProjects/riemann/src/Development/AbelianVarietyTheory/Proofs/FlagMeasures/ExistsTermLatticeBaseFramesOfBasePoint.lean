import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalFramePairsDifferIsometryUnitriangularStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemXflagMapLF
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeadingMinorEqPointMinor
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeRationalFlagIffRationalUnipot
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold

theorem tg_of_base_point : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ t : TauC Y u u', ptPN t = toPts w → ∃ Λ, TG F F' t Λ := by
  intro D X Y u u' F F' w hZ hG t hpt
  have hcF : IsInCell (ZhatOM (ZhatL F F')) w := by
    refine ⟨(1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), 1, ?_, ?_, by rw [hZ]; simp⟩
    · intro i j
      exact ⟨fun h => Matrix.one_apply_ne h.ne, fun h => h ▸ Matrix.one_apply_eq i⟩
    · intro i j
      exact ⟨fun h => Matrix.one_apply_ne h.ne', fun h => h ▸ Matrix.one_apply_eq i⟩
  have hGw := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.gpt_eq F F' w hcF
  have hw : Formalism.L2.SG.PairVal.ptOf t.toTerm = w := Formalism.L2.SG.NGCut.NormalVectorPairings.toPts_inj _ _ hpt
  have hex : ∃ w, t.toTerm.atPt w ∧ t.toTerm.relevant := by
    by_contra h
    apply hG
    rw [← hGw, ← hpt]
    show GPt _ (toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm)) = 0
    unfold Formalism.L2.SG.PairVal.ptOf
    rw [dif_neg h]
    exact Formalism.L2.SG.NGCut.NormalVectorPairings.GPt_junk D u u'
  obtain ⟨F'', ⟨hP, hmk⟩, -, hcell⟩ := Formalism.L2.SG.PairVal.ptOf_spec t.toTerm hex
  rw [hw] at hcell
  have hΛ := (Y.rowsOK u).1 t.lam t.mem
  have hmk' : Formalism.L2.SG.TermDef.mk _ _ _ ⟨F'', hP⟩ = Formalism.L2.SG.TermDef.mk _ _ _ ⟨t.frame, t.rep.2.2.2.2⟩ := hmk
  have hrel := (Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) t.lam hΛ _ _).1 hmk'
  have hcell' : IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) t.frame)) w := ((Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) t.lam hΛ).2.1 _ _ hrel w).1 hcell
  have hGt : Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
    intro h0
    apply hG
    rw [← hGw]
    exact (Formalism.L2.SG.NGCut.LeadingMinorIntegrality.gpt_eq (T := Tu D u) (T' := Tu D u') _ _ w hcell').trans h0
  obtain ⟨-, γ, hγ, ⟨A, hA, hc⟩, ⟨B, hB, hd⟩⟩ := GlobalTheory.T.rationalFramePairs_differ_isometry_unitriangular D (lf D (X.Fu u)) F t.frame F' w
    (Formalism.L2.SG.Corank.tu_ne_zero u) (Formalism.L2.SG.Corank.tu_ne_zero u') hGt hcell' hZ
  exact ⟨Formalism.HermitianLatticesTheory.gmap γ t.lam, γ, ⟨hγ, fun a => GlobalTheory.FlagChange.chg_sub_mem F.fl hA hc a⟩,
    ⟨hγ, fun a => GlobalTheory.FlagChange.chg_sub_mem F'.fl hB hd a⟩, rfl⟩

end GlobalTheory.Unfold
