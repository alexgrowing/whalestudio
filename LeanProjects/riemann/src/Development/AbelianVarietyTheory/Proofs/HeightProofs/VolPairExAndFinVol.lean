import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCMFamHost
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryAdelicQuotientVolumeIsVolume

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin2

theorem volPairEx_and_finVol : ∀ (D : D7) (V : HSp D), V.SigOK → VolPairEx V ∧ Formalism.L2.Pj.FinVol V := by
  intro D V hs
  have h := GlobalTheory.Mem.Vol.volIs_trueVol _ _ D.sp.cm _ (tauE D) D.cd V
    (GlobalTheory.Mem.Vol.isCMFam_host _ D.host _ D.eTau) hs
  obtain ⟨⟨μ, hμ⟩, hall⟩ := h
  have hex : VolPairEx V := by
    obtain ⟨⟨𝓕, h𝓕⟩, -⟩ := hall μ hμ
    exact ⟨(μ, 𝓕), hμ, h𝓕⟩
  refine ⟨hex, ?_⟩
  have hp := volPair_isVolPair V hex
  have hm : (volPair V).1 (volPair V).2 =
      ENNReal.ofReal (GlobalTheory.Mem.Vol.trueVol D.sp.cm (tauE D) D.cd V) :=
    (hall _ hp.1).2 _ hp.2
  unfold Formalism.L2.Pj.FinVol
  rw [muQ_univ, hm]
  exact ⟨(ENNReal.ofReal_pos.2 (GlobalTheory.Mem.Vol.trueVol_pos _ _ _ _)).ne', ENNReal.ofReal_ne_top⟩

end GlobalTheory.FinalJoin2
