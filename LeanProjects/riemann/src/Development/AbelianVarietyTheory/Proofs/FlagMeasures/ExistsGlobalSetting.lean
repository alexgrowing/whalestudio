import Mathlib
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocalAdditiveCharContinuous
import Formalism.PeriodIntegrals.BesselMapUniq
import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.CoefWeightedLocHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.JExistsAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatExistsOfForms0
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MExistsHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPlaceFunctionBlockExistsOfBesselCoef
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusMatchHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HcExistsAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LevelConjHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExistsHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RescaleStep3
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColDictCoreHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FullExistsOfLocTied
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnLevelStabTriv
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinXOfDecay

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.ColDict

namespace GlobalTheory.St.SpectralData

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_transport {D : D7} (F : ∀ u, Formalism.L2.Forms.Forms0 D u)
    (X : HidaSetting D) (hK : X.LevelSubgroupCharacter) (hι : ∃ ιA, GlobalTheory.St.IsAdeleIso X ιA) (u : D.what₂.Word) :
    ∃ Tr : Transport X u (F u), LevelMatch X Tr hK := by
  obtain ⟨wt, hw⟩ := GlobalTheory.St.WittT.wittExists D X u
  obtain ⟨ιA, hι⟩ := hι
  obtain ⟨g0, hg0⟩ := GlobalTheory.St.G.genusMatch_holds D F X u wt ιA hw hι
  obtain ⟨h0, hL, hKm⟩ := GlobalTheory.St.G.levelConj_holds D F X hK u wt ιA g0 hw hι hg0
  choose hcf hcr using GlobalTheory.St.G.hcExists_all D F X u wt ιA h0 hw hι
  obtain ⟨J, hJ1, hJ2, hJ3⟩ := GlobalTheory.jExists_all D F X u wt hw
  exact ⟨⟨wt, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2, ιA, hι.1, hι.2, h0, hcf, hcr, J, hJ1, hJ2, hJ3⟩, hL, hKm⟩

open Formalism.L2.SG.SplitPrimeNormLemmas in

theorem exists_setting (hSW : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent)
    (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) :
      ∃ (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), X.B.I = Formalism.L2.SG.InstExistsPf.instOf D ∧
        (∀ x : X.B.I.E, HEq (X.ιE x) x) ∧ X.MeasTie hb ∧ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ ∧
        Formalism.L2.SG.LocVol.IsStdChar ψ ∧
        Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ ∧ (∀ w, Formalism.L2.SG.LocVol.LocCompatX X ψ w) ∧
        ∀ hK : X.LevelSubgroupCharacter, ∀ u, ∃ Tr : Transport X u (F u), LevelMatch X Tr hK := by
  have hB : BesselNVGap := Formalism.L2.SG.Closed.BesselNVGap_holds
  have hC : CoefWeightedLoc := Formalism.L2.SG.Closed.CoefWeightedLoc_holds
  let A := Formalism.L2.SG.InstExistsPf.instanceOfRecord D
  obtain ⟨L⟩ := GlobalTheory.St.Lat.latExists_of_forms0 D (F D.u₀)
  obtain ⟨P⟩ := Formalism.L2.SG.Closed.PsiExists_holds D A
  obtain ⟨Rf⟩ := Formalism.L2.SG.Closed.RefExists_holds D A L
  obtain ⟨Xu⟩ := Formalism.L2.SG.Closed.XuExists_holds D A L Rf
  obtain ⟨Bu⟩ := Formalism.L2.SG.Closed.BunExists_holds D hC hG A L P Rf
  obtain ⟨Pi⟩ := Formalism.L2.SG.Closed.PiExists_holds D A L
  obtain ⟨Mu⟩ := Formalism.L2.SG.Closed.MuExists_holds D A L
  obtain ⟨Wb⟩ := GlobalTheory.WBlockExists.realPlaceFunctionBlockExists_of_bessel_coef hB hC D hG A L P Rf Bu Pi Mu
  obtain ⟨Mb, hb, hM⟩ := GlobalTheory.St.mExists_holds D A L P Rf Xu Bu Pi Mu Wb
  obtain ⟨mg, hg, mw, hw, hM', ψ, hψ, hstd, hCm, hL⟩ :=
    GlobalTheory.St.Rescale.rescaleStep3 hSW D (mk A L P Rf Xu Bu Pi Mu Wb Mb) hb hM
  refine ⟨Formalism.L2.SG.SettingExistsMeasured.withMeas (mk A L P Rf Xu Bu Pi Mu Wb Mb) mg hg mw hw, hb, ψ, rfl,
    fun _ => HEq.rfl, hM', hψ, hstd, hCm, hL, fun hK u => ?_⟩
  exact exists_transport F _ hK ⟨RingEquiv.refl _, fun _ => rfl, fun _ => Iff.rfl⟩ u

theorem exists_spectralData : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → PI.BesselMapUniq.BesselMapUniq → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → Formalism.L2.SG.Pf.LocCP.LocTied D → ∃ (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (Y : Formalism.L2.SG.Full.Full X) (hF : FinX Y) (tr : ∀ u, Transport X u (F u)), X.B.I = Formalism.L2.SG.InstExistsPf.instOf D ∧ (∀ x : X.B.I.E, HEq (X.ιE x) x) ∧ X.MeasTie hb ∧ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ ∧ Formalism.L2.SG.LocVol.IsStdChar ψ ∧ Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ ∧ (∀ w, Formalism.L2.SG.LocVol.LocCompatX X ψ w) ∧ Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧ ∀ u, LevelMatch X (tr u) Y.hK ∧ ColDictInto X (tr u) Y.hK ∧ ColDictBij X (tr u) Y.hK ∧ ColDictIsom X (tr u) Y.hK (Y.cs u) (hF.shInj u) := by
  intro hSW hMU hRF D F hG hLT
  obtain ⟨X, hb, ψ, hI, hι, hM, hψ, hstd, hCm, hL, hT⟩ := exists_setting hSW D F hG
  obtain ⟨Y⟩ := GlobalTheory.fullExists_of_locTied D X hLT
  obtain ⟨hWD, hph⟩ := Formalism.L2.SG.Pf.wuDecayOfGap_of_jsz hMU D hG X
  have hF : FinX Y := GlobalTheory.FinitenessBundle.finX_of_decay hRF D X Y hWD hph
  choose tr htr using hT Y.hK
  refine ⟨X, hb, ψ, Y, hF, tr, hI, hι, hM, hψ, hstd, hCm, hL, hph, fun u => ?_⟩
  obtain ⟨-, h1, h2, h3⟩ := GlobalTheory.St.colDictCore_holds D X u (F u) (tr u) Y.hK (htr u)
    (GlobalTheory.columnLevel_stabTriv D X Y.hK u)
  exact ⟨htr u, h1, h2, h3 _ (Y.cs u) (hF.shInj u) (Y.colReps u)⟩

end GlobalTheory.St.SpectralData
