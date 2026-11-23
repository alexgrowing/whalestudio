import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsCorrespond
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerCommensurableInvVolumeSmulComplement

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WtPos

theorem finrank_loc {D : D7} (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have h1 := D.R.m_even
  have h2 := D.R.two_le_m
  have h3 := D.R.m_add_three_le_k
  obtain ⟨c, hc⟩ := h1
  simp only [Ranks.r, Ranks.rS]
  omega

theorem wt_pos : ∀ (D : D7) (Z : LocDat D) (p : PlF D) (P : LocNG.FPair (locH Z p) D.R.rS), P.RelG (LocNG.theta (Z.M p)) → ∀ d0 d : LocNG.Datum P, (∃ t, LocNG.IsTermOver P d0 t) → (∃ t, LocNG.IsTermOver P d t) → 0 < LocNG.Datum.wt d0 d := by
  intro D Z p P hR d0 d ⟨t0, ht0⟩ ⟨t, ht⟩
  have hOK := (Z.agree p).1
  haveI := hOK.loc
  haveI := hOK.char0
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord (Z.M p) hOK (locH Z p) D.R.rS D.R.k P (finrank_loc p) hR
  have h0 := ((GlobalTheory.HL.CoordTermWt.terms_correspond (Z.M p) hOK (locH Z p) D.R.rS D.R.k P S c).1 d0 t0 ht0).1
  have h1 := ((GlobalTheory.HL.CoordTermWt.terms_correspond (Z.M p) hOK (locH Z p) D.R.rS D.R.k P S c).1 d t ht).1
  obtain ⟨a0, b0⟩ := (GlobalTheory.HL.Frames.stab_commensurable_invVol_smul (Z.M p).L D.R.rS D.R.k S).2 _ _ h0
  obtain ⟨a1, b1⟩ := (GlobalTheory.HL.Frames.stab_commensurable_invVol_smul (Z.M p).L D.R.rS D.R.k S).2 _ _ h1
  rw [(GlobalTheory.HL.CoordDatum.transport (Z.M p) hOK (locH Z p) D.R.rS D.R.k P S c).2.2.2.2 d0 d]
  have e1 := Subgroup.relIndex_ne_zero_trans b1 a0
  have e2 := Subgroup.relIndex_ne_zero_trans b0 a1
  unfold GlobalTheory.HL.invVol
  positivity

end GlobalTheory.WtPos
