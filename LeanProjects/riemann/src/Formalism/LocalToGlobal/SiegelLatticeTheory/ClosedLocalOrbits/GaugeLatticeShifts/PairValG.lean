import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.Development
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexAStable
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.InvMulMemOfScaledEntriesCongr
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexBCongruence
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.VolumeIndexRepresentationOfData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal

namespace Formalism.L2.SG.Pf.PairValG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem gval_eq_G (hrows : IsRowReps D F0 what₂) {t : Term D u u' F0 what₂}
    {F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} (hrep : Rep t.lam (lf D F0) (PD D t.lam (lf D F0) u') t.cls F') :
    Gval (lf D F0) F' = t.G := by
  obtain ⟨h, hmk⟩ := hrep
  have hGF := (Formalism.L2.SG.Closed.TermFun_holds D u u' F0 t.lam (hrows.1 t.lam t.mem)).1
  change _ = Gt t.lam (lf D F0) (PD D t.lam (lf D F0) u') t.cls
  rw [← hmk]
  exact (Gt_mk hGF ⟨F', h⟩).symm

theorem atPt_of_normRep {t : Term D u u' F0 what₂} {w : Point D.host.E (D.R.rS + 1)}
    {F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {L U : MatR D} (hN : NormRep t w F' L U)
    (hG : Gval (lf D F0) F' ≠ 0) : t.atPt w :=
  ⟨F', hN.1, hG, ⟨L, U, hN.2.2.1, hN.2.2.2.1, hN.2.2.2.2⟩⟩

theorem vRdef_eq_of (hV : Formalism.L2.SG.Pf.RelativeIndexFlags.VolumeIndexRepresentationNonzero D u u' F0 what₂) (hrows : IsRowReps D F0 what₂)
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hAg : ∀ p, Formalism.MainNotions.S.LocalSplitGroups.Agree δ M p) (t : Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : MatR D) (hr : t.relevant) (hg : t.generic)
    (hN : NormRep t w F' L U) (hG : Gval (lf D F0) F' ≠ 0) :
    vRdef D u u' F0 what₂ δ M t = volIdx D u u' F0 what₂ δ M t w F' L := by
  have hex : t.relevant ∧ t.generic ∧
      ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × MatR D × MatR D,
        NormRep t x.1 x.2.1 x.2.2.1 x.2.2.2 := ⟨hr, hg, ⟨(w, F', L, U), hN⟩⟩
  unfold vRdef
  rw [dif_pos hex]
  have hx := hex.2.2.choose_spec
  set x := hex.2.2.choose with hxdef
  have hGx : Gval (lf D F0) x.2.1 ≠ 0 := by
    rw [gval_eq_G hrows hx.1, ← gval_eq_G hrows hN.1]; exact hG
  have hw : x.1 = w := cell_point_unique_of_term_fun (Formalism.L2.SG.Closed.TermFun_holds D u u') hrows t x.1 w
    (atPt_of_normRep hx hGx) (atPt_of_normRep hN hG)
  have hx' : NormRep t w x.2.1 x.2.2.1 x.2.2.2 := hw ▸ hx
  have e1 : volIdx D u u' F0 what₂ δ M t x.1 x.2.1 x.2.2.1 = volIdx D u u' F0 what₂ δ M t w x.2.1 x.2.2.1 := by rw [hw]
  rw [e1]
  exact hV δ M hAg t w x.2.1 F' x.2.2.1 x.2.2.2 L U hr hg hx' hGx hN hG

theorem vRdef_pos_of (hFin : Formalism.L2.SG.Pf.RelativeIndexFlags.VolIdxFinP D u u' F0 what₂) (hrows : IsRowReps D F0 what₂)
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hAg : ∀ p, Formalism.MainNotions.S.LocalSplitGroups.Agree δ M p) (t : Term D u u' F0 what₂) (hG : t.G ≠ 0) :
    0 < vRdef D u u' F0 what₂ δ M t := by
  unfold vRdef
  split_ifs with h
  · have hx := h.2.2.choose_spec
    have hGx : Gval (lf D F0) h.2.2.choose.2.1 ≠ 0 := by rw [gval_eq_G hrows hx.1]; exact hG
    obtain ⟨h1, h2⟩ := hFin δ M hAg t _ _ _ _ h.1 h.2.1 hx hGx
    unfold volIdx
    exact div_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero h1)) (Nat.cast_pos.2 (Nat.pos_of_ne_zero h2))
  · exact one_pos

theorem volIdxFinP_of (hyps : Formalism.L2.SG.Pf.StabilizerIndexVolumes.Hyps D u u' F0 what₂)
    (hDel : ∀ δ M, Formalism.L2.SG.Pf.StabilizerIndexVolumes.DeltaAE D δ M)
    (hAbdd : ∀ δ M, Formalism.L2.SG.Pf.StabilizerIndexVolumes.ABddOf D u u' F0 what₂ δ M)
    (hAcong : ∀ δ M, Formalism.L2.SG.Pf.StabilizerIndexVolumes.ACong D u u' F0 what₂ δ M) :
    Formalism.L2.SG.Pf.RelativeIndexFlags.VolIdxFinP D u u' F0 what₂ := fun δ M =>
  Formalism.L2.SG.Pf.StabilizerIndexVolumes.volume_index_finite_of_hyps D u u' F0 what₂ δ M hyps Formalism.L2.SG.Pf.StabilizerIndexVolumes.commens
    Formalism.L2.SG.Pf.StabilizerIndexVolumes.stClosed (hDel δ M) (Formalism.L2.SG.Pf.StabilizerIndexVolumes.volume_index_a_stable D u u' F0 what₂ δ M) (hAbdd δ M)
    (hAcong δ M) (Formalism.L2.SG.Pf.StabilizerIndexVolumes.volume_index_b_stable D u u' F0 what₂ δ M) (Formalism.L2.SG.Pf.StabilizerIndexVolumes.volume_index_b_bounded D u u' F0 what₂ δ M)
    (Formalism.L2.SG.Pf.StabilizerIndexVolumes.volume_index_b_congruence D u u' F0 what₂ δ M)

theorem volume_index_representation_of_hyps (hyps : Formalism.L2.SG.Pf.StabilizerIndexVolumes.Hyps D u u' F0 what₂)
    (hDel : ∀ δ M, Formalism.L2.SG.Pf.StabilizerIndexVolumes.DeltaAE D δ M)
    (hAbdd : ∀ δ M, Formalism.L2.SG.Pf.StabilizerIndexVolumes.ABddOf D u u' F0 what₂ δ M)
    (hAcong : ∀ δ M, Formalism.L2.SG.Pf.StabilizerIndexVolumes.ACong D u u' F0 what₂ δ M) :
    Formalism.L2.SG.Pf.RelativeIndexFlags.VolumeIndexRepresentationNonzero D u u' F0 what₂ :=
  volume_index_representation_of_data D u u' F0 what₂ hyps.1 hyps.2.1 hyps.2.2.1 hyps.2.2.2.1 hyps.2.2.2.2.1 hyps.2.2.2.2.2
    (volIdxFinP_of hyps hDel hAbdd hAcong)

end Formalism.L2.SG.Pf.PairValG
