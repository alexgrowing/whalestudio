import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcAllC
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AutLzNonempty
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SummableLogAlpD
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlTiePl
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.RealBracketOfRowBlock
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvHoldsGen
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeVolUD
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowFormAllOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowsSumCPf
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocFramePrim
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataPos
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Rescale
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.StepSize
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocVolPrim
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RhsWLimOfLeaves
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermRepUnram
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CountConst

def emptyPairs {D : D7} (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂ where
  P := Empty
  fst := Empty.elim
  snd := Empty.elim
  row := fun p => p.elim
  inj := fun p => p.elim
  gscal := fun _ => False

set_option maxHeartbeats 4000000 in

theorem countConst_eq_unscaledConst : PI.VolStabS.MassDataS.SWXS → ∀ (Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' → 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (gS D) ^ 2] → ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ → ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf), 0 < Formalism.L2.SG.MassDataConc.ngFac D ∧ Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) * Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) * ∏' p, Formalism.L2.SG.DataInst.alpD u u' p = (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA * Formalism.L2.SG.MassDataConc.ngFac D := by
  intro hSW Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hk hcong hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq
  obtain ⟨hMT, hI, hS, hMC, hLC, hLT, hdet⟩ := hT
  set Q0 := emptyPairs u u' (X.Fu u) (Y.what₂ u) with hQ0
  set vR0 : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℝ := fun _ => 0 with hvR0
  have hK2 := Formalism.L2.SG.Closed.level_subgroup_properties X
  have hV : 0 < X.volK2 := ENNReal.toReal_pos (ne_of_gt hK2.2.2.1) (ne_of_lt hK2.2.2.2)
  have hH : Formalism.L2.SG.TypedSets.HypX X hb (Y.FN u) (Y.FN u') u u' := ⟨hMT, hK2, Y.FN_fund u, Y.FN_fund u'⟩
  have hStd : Formalism.L2.SG.LocVol.StdHyp X.B.I.cm.sig X.B.I.J ψ :=
    ⟨MassDataVolumesW.stepCM X, MassDataVolumesW.stepHerm X, hI, hS⟩
  have hlat : ∃ L : Submodule (NumberField.RingOfIntegers X.B.I.E) (Fin X.B.I.n → X.B.I.E),
      Submodule.IsLattice X.B.I.E L ∧
      (L : Set (Fin X.B.I.n → X.B.I.E)) = (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
    ⟨X.B.I.L, ⟨X.B.I.L_fg, X.B.I.L_span⟩, rfl⟩
  have hdet' : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramE X.B.I.cm.sig X.B.I.J
      (Formalism.L2.SG.Sub.tupH (Formalism.L2.SG.TypedSets.frameOf X u'))).det ≠ 0 :=
    Formalism.L2.SG.Pf.Rescale.standard_gram_nondegenerate X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J _ _ _
      (fun x => star_star x) hStd.2.1 (Formalism.L2.SG.Pf.Rescale.frame_stdX X u')
  have hPC := Formalism.L2.SG.Pf.ProdConvCut2.prodConv_holds_gen X hb ψ hI hS hLC u u'
  have hL := Formalism.L2.SG.LocVol.locTieX_of X ψ u (hLC u) (Formalism.L2.SG.Pf.LocVolPrim.primX X u locFramePrim)
  have hL' := Formalism.L2.SG.LocVol.locTieX_of X ψ u' (hLC u') (Formalism.L2.SG.Pf.LocVolPrim.primX X u' locFramePrim)
  have hTF := Formalism.L2.SG.Pf.typFacts_holds X hb u u'
  have hQ := Formalism.L2.SG.Pf.MassDataPos.quotVolPosC_of X hb Y u u' X0 ψ (Y.tO u u') 0 0 1 vR0 Q0 Y.M Y.δ i0 i0' νq hK2 hV
  have hN := Formalism.L2.SG.Pf.NcAllC.ncTieC_of_closed X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 vR0 Q0
    Y.M Y.δ i0 i0' νq Formalism.L2.SG.Closed.CovolRef_outright hSW hH hMC hStd hlat hdet' hdet hPC hL hL' hTF hQ le_rfl le_rfl
    one_pos hcong (Y.rowsOK u)
  have hρ := Formalism.L2.SG.MassDataConc.RhoTieC_closed X hb Y u u' X0 ψ 0 0 1 vR0 Q0 Y.M Y.δ i0 i0' νq
  have hal := Formalism.L2.SG.Pf.AlTie.locOf_al_eq X (Formalism.L2.SG.Pf.AlTie.etaTie_of X hLT) hk u u' ψ
  have hκ := Formalism.L2.SG.WConst.kapN_pos (D := D)
  have hng := Formalism.L2.SG.Pf.ngFac_pos D
  have hρp := Formalism.L2.SG.RhoPf.massRows_pos X Y u
  have hαp := Formalism.L2.SG.PoincareAmplitudeLowerBounds.tprod_alpD_pos D hk u u'
  refine ⟨hng, ?_⟩
  set B0 := Formalism.L2.SG.MassDataConc.bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 vR0 Q0 Y.M Y.δ i0 i0' νq
    with hB0
  have eU : kapU D = Formalism.L2.SG.MassDataConc.kapN D := if_pos hκ
  have eA : (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA = B0.AA / kapU D := by
    show B0.volB * (B0.Coo / kapU D) * (B0.MM / B0.volZZ) / B0.μK =
      B0.volB * B0.Coo * (B0.MM / B0.volZZ) / B0.μK / kapU D
    ring
  have en : B0.n0c = B0.AA / B0.ρ0 := rfl
  have eal : B0.al = ∏' q, Formalism.L2.SG.DataInst.alpD u u' q := hal
  have eρ : B0.ρ0 = Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) := hρ
  have key : Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) =
      B0.n0c * Formalism.L2.SG.MassDataConc.ngFac D / (B0.al * Formalism.L2.SG.MassDataConc.kapN D) := hN
  rw [key, en, eρ, eal, eA, eU]
  field_simp

end GlobalTheory.CountConst
