import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalFramePairsDifferIsometryUnitriangularStatement

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.MoveTerm

theorem term_moves_to_base : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ t₀ : TauC Y u u', t₀.toTerm.atPt w → ∃ (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' := by
  intro D X Y u u' _hS w F00 F'0 FP hZ _hG _hB t₀ ht
  obtain ⟨F', ⟨hP, hmk⟩, hGv, hCell⟩ := ht
  have hrow : IsRowLat D (X.Fu u) t₀.lam := (Y.rowsOK u).1 _ t₀.mem
  obtain ⟨hGF, hCF, -⟩ := Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) t₀.lam hrow
  have hrel := (Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) t₀.lam hrow _ _).1 hmk
  have hGt : Gval (lf D (X.Fu u)) t₀.frame ≠ 0 := by
    intro h
    apply hGv
    rw [hGF _ _ hrel]
    exact h
  have hCt := (hCF _ _ hrel w).1 hCell
  have hTu : ∀ v : D.what₂.Word, ((Tu D v : ℕ) : D.host.E) ≠ 0 := fun v =>
    Nat.cast_ne_zero.mpr (Formalism.L2.SG.GramJoint.Tu_pos D v).ne'
  obtain ⟨-, γ, hγ, ⟨A, hA, hAc⟩, ⟨A', hA', hAc'⟩⟩ :=
    GlobalTheory.T.rationalFramePairs_differ_isometry_unitriangular D (lf D (X.Fu u)) F00 t₀.frame F'0 w (hTu u) (hTu u') hGt hCt hZ
  refine ⟨γ, A, A', hγ, ?_, ?_, fun b => hAc b, fun b => hAc' b⟩
  · exact fun i j => ⟨fun h => hA.1 i j h, fun h => h ▸ hA.2 i⟩
  · exact fun i j => ⟨fun h => hA'.1 i j h, fun h => h ▸ hA'.2 i⟩

end GlobalTheory.HL.MoveTerm
