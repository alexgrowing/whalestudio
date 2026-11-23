import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentGroupsLatticesGlobalCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsOrbitsHeightsAmplitudesInCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDatumOfTwoCongruentFramesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnsignedLocalTermRowLatticeIsTerm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitriangularFrameChangeLocalScalings
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDatumEquivariantFlagIsometries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermDefectNeIffMoveLinearEquivStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermMoveUnitaryIsTermStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramInvariantIsometryUnitriangularMovesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SignedLocalTermDefectIffUnsignedLocalTermStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalFramesMovedTermUnitriangularChangeStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.GenCoord

theorem generic_iff_locU {D : D7} (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (Z : LocDat D)
    (t₀ : TauC Y u u') : t₀.generic ↔
      ∀ p, ¬ LocNG.BBne (H := locH Z p) (locU Z p t₀.lam (lf D (X.Fu u)) t₀.frame (Tu D u) (Tu D u')) := by
  have hrows := Y.rowsOK u
  have hBF := Formalism.L2.SG.Pf.big_block_function_holds D u u'
  have hT := Formalism.L2.SG.Pf.bbTie_holds D Z
  have hMI : ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
      (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)), Formalism.L2.SG.Saturated.MplusIndep Λ (lf D F0) (gS D) F' :=
    fun F0 Λ F' => Formalism.L2.SG.Pf.m_plus_independent _ _ _ _
  have hg := genIffLocBB_of Z hT u u' hBF hMI (X.Fu u) (Y.what₂ u) hrows t₀.toTerm
  show t₀.toTerm.generic ↔ _
  rw [hg]
  refine forall_congr' fun p => not_congr ?_
  have hL := hrows.1 t₀.lam t₀.mem
  refine ((termBBne_iff_loc Z hT hrows hBF (hMI (X.Fu u)) t₀.toTerm p).symm.trans ?_).trans
    (GlobalTheory.T.signedLocalTerm_defect_iff_unsignedLocalTerm Z p t₀.lam (lf D (X.Fu u)) t₀.frame (Tu D u) (Tu D u'))
  refine Iff.trans ?_ (hT u u' (X.Fu u) t₀.lam t₀.frame hL t₀.rep.2.2.2.2 (hMI _ _ _) p)
  constructor
  · rintro ⟨F', ⟨h, hm⟩, P, hP, hbb⟩
    refine ⟨P, hP, ?_⟩
    have e := Formalism.L2.SG.TermDef.const_of_mk
      (fun y : Formalism.L2.SG.TermDef.Carrier (Formalism.L2.SG.TermDef.PD D t₀.lam (lf D (X.Fu u)) u') =>
        Formalism.L2.SG.Saturated.BBneP t₀.lam (gS D) (lf D (X.Fu u)) y.1 P)
      (fun a b hab => propext (hBF (X.Fu u) t₀.lam hL P a b hab)) hm
    exact e ▸ hbb
  · intro h
    exact ⟨t₀.frame, ⟨t₀.rep.2.2.2.2, rfl⟩, h⟩

theorem generic_iff_gen : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → (t₀.generic ↔ G.Gen (G.datOf (c.lat ρ t₀.lam)) (c.lat ρ t₀.lam)) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv
  have hρ : ρ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hMv.1
  rw [generic_iff_locU X Y u u' (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) t₀]
  refine forall_congr' fun p => ?_
  obtain ⟨g, hgExt, hgU, -, -, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p ρ hρ
  have hGv : Gval (lf D (X.Fu u)) t₀.frame ≠ 0 := fun h => hG ((GlobalTheory.T.gramInvariant_isometry_unitriangular_moves F00 F'0 _ _ ρ U U' hMv).symm.trans h)
  have hRL : IsRowLat D (X.Fu u) t₀.lam := (Y.rowsOK u).1 t₀.lam t₀.mem
  obtain ⟨hIT, hTri'⟩ := GlobalTheory.LocOver.locU_isTerm D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) u u' (X.Fu u) t₀.lam hRL
    t₀.frame t₀.rep.2.2.2.2 hGv p
  have hOK : (Y.M p).OK := (Y.agree p).1
  have htIT := GlobalTheory.T.localTerm_move_unitary_isTerm (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) g hgU _ hIT
  obtain ⟨hTA, hTB⟩ := GlobalTheory.T.localFrames_movedTerm_unitriangular_change (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 _ _ ρ U U' g _ hMv hgExt hTri'
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (hAt p).1
  rw [← hA1] at hTA
  rw [← hA2] at hTB
  obtain ⟨d, hd⟩ := GlobalTheory.T.exists_datum_of_two_congruent_frames (Y.M p) hOK (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS (FP p)
    (move g (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t₀.lam (lf D (X.Fu u)) t₀.frame (Tu D u) (Tu D u')))
    htIT hA3.symm hA4.symm hTA hTB
  have hW := ((GlobalTheory.T.terms_orbits_heights_amplitudes_in_coordinates (Y.M p) hOK (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS D.R.k (FP p) (G.S p)
    (c.c p)).1 d _ hd)
  have hlat := (GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv).2.2.2.2.1 ρ hρ p g t₀.lam hgExt
  haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).lf
  haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).char0
  have hlat' : (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam) = (c.c p).lat
      (move g (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t₀.lam (lf D (X.Fu u)) t₀.frame (Tu D u) (Tu D u'))).abelian₂ := hlat
  have hdat := GlobalTheory.HL.DatumOf.datOf_term (G.S p) hW.1
  show _ ↔ (G.S p).BBzero ((G.S p).datOf ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam)))
    ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam))
  rw [hlat', ← hdat, ← GlobalTheory.T.localTermDefect_ne_iff_move_linearEquiv (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) g, hW.2.2]
  exact not_not

end GlobalTheory.HL.GenCoord
