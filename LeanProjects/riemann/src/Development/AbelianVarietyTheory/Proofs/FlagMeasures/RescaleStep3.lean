import Mathlib
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Volumes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SiegelWeilNarrowOfWide
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.StdChar
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FourMulAddFiveLeRank
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LinearIndependentRatTupOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardFrameGramDetNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasWPrescribed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelWeilVolumes
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicTorusMeasureStabiliserHaarStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameStabilizerHaarNormalisedFibreMeasureStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHaarMeasureUnipotentRadicalCovolumeOneStatement

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.St.Rescale

theorem rescaleStep3 :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ D : Formalism.BasicNotions.D7, GlobalTheory.St.RescaleStep3 D := by
  intro hSW D X hb hM
  obtain ⟨hCM, hH, hsize, hfr⟩ := GlobalTheory.CmHermitianRankFrames.cm_herm_rank_frames D X
  obtain ⟨hA, hC⟩ := GlobalTheory.St.siegelWeil_volumes hSW X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH
  obtain ⟨ψ, hψ, hstd⟩ := Formalism.L2.SG.Pf.standard_character_exists X.B.I.F hCM.1
  have hstd' : Formalism.L2.SG.LocVol.IsStdChar ψ := hstd
  have hG := X.measG_norm
  have hμG : X.measG.μG.IsHaarMeasure := hG.1
  have hherm : ∀ {a : ℕ} (X0 : Fin a → Fin X.B.I.n → X.B.I.E) (i j : Fin a),
      X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J X0 j i) = gramE X.B.I.cm.sig X.B.I.J X0 i j :=
    fun X0 i j => GlobalTheory.FrameGram.hE_swap (GlobalTheory.FrameGram.conj_invol hCM) hH.1 _ _

  have hB : ∀ X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E,
      ∃ μ' : Measure (stabT (AF X.B.I.F) X.B.I.cm.sig X.B.I.J X0), μ'.IsHaarMeasure ∧
        ((gramE X.B.I.cm.sig X.B.I.J X0).det ≠ 0 →
          ∃ (hTB : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J X0 j i) =
              gramE X.B.I.cm.sig X.B.I.J X0 i j) (νB : Measure _),
            Formalism.L2.SG.Volumes.IsOmT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J ψ _ hTB νB ∧
            Formalism.L2.SG.Volumes.IsCompatT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J X0 X.measG.μG μ' νB) := by
    intro X0
    by_cases hdet : (gramE X.B.I.cm.sig X.B.I.J X0).det ≠ 0
    · obtain ⟨νX, μ', h1, h2, h3⟩ := GlobalTheory.T.exists_adelicTorusMeasure_stabiliserHaar X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH hA hC ψ hψ
        (2 * D.R.rS + 2) (by omega) (by omega) X0 (hherm X0) hdet X.measG.μG hμG
      exact ⟨μ', h2, fun _ => ⟨hherm X0, νX, h1, h3⟩⟩
    · exact ⟨X.measG.μB X0, hG.2.2.2.2.1 X0, fun h => absurd h hdet⟩
  choose μB' hμB' hBc using hB

  have hW : ∀ u, ∃ W : MeasW X.B.I.cm.sig X.B.I.J (Formalism.L2.SG.TypedSets.frameOf X u), W.IsTextNorm ∧
      W.μNinf = (X.measW u).μNinf ∧ W.μHinf = (X.measW u).μHinf ∧
      (∃ (hT1 : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (Formalism.L2.SG.TypedSets.frameOf X u)) j i) =
            gramE X.B.I.cm.sig X.B.I.J (tupH (Formalism.L2.SG.TypedSets.frameOf X u)) i j) (νH : Measure _),
        Formalism.L2.SG.Volumes.IsOmT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J ψ _ hT1 νH ∧
        Formalism.L2.SG.Volumes.IsCompatT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J
          (tupH (Formalism.L2.SG.TypedSets.frameOf X u)) X.measG.μG W.μH νH) ∧
      covol W.μN = 1 ∧
      ∀ v, Formalism.L2.SG.LocVol.LocTieW X.B.I.cm.sig X.B.I.J ψ v (Formalism.L2.SG.TypedSets.frameOf X u)
        (X.measG.μGv v) (W.μSv v) := by
    intro u
    obtain ⟨T, hP⟩ := hfr u
    obtain ⟨hdet, hT1, -⟩ := GlobalTheory.FrameGram.std_frame_gram X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH
      D.R.rS (Formalism.L2.SG.TypedSets.frameOf X u) T hP
    obtain ⟨νH, μH, h1, h2, h3⟩ := GlobalTheory.T.exists_adelicTorusMeasure_stabiliserHaar X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH hA hC ψ hψ
      (D.R.rS + 1 + D.R.rS) (by omega) (by omega) (tupH (Formalism.L2.SG.TypedSets.frameOf X u)) hT1 hdet
      X.measG.μG hμG
    obtain ⟨μN, hN, hN1⟩ := GlobalTheory.T.exists_haarMeasure_unipotentRadical_covolume_one X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH D.R.rS
      (Formalism.L2.SG.TypedSets.frameOf X u) T hP
    have hS : ∀ v : HeightOneSpectrum (𝓞 X.B.I.F),
        ∃ μS : Measure (Ssub (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (Formalism.L2.SG.TypedSets.frameOf X u)),
          μS.IsHaarMeasure ∧ Formalism.L2.SG.LocVol.LocTieW X.B.I.cm.sig X.B.I.J ψ v
            (Formalism.L2.SG.TypedSets.frameOf X u) (X.measG.μGv v) μS := fun v =>
      GlobalTheory.T.exists_frameStabilizerHaar_normalised_fibreMeasure X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH hA hC ψ hψ hstd' v D.R.rS
        (Formalism.L2.SG.TypedSets.frameOf X u) T hP (by omega) (X.measG.μGv v) (hG.2.2.2.1 v)
    choose μSv hSv hSt using hS
    have hWn := X.measW_norm u
    obtain ⟨W, hWt, e1, e2, e3, e4, e5⟩ := GlobalTheory.St.MeasWord.exists_measW_prescribed X.B.I.F X.B.I.E X.B.I.cm.sig hCM
      X.B.I.n X.B.I.J hH D.R.rS (Formalism.L2.SG.TypedSets.frameOf X u) T hP
      (X.measW u).μNinf (X.measW u).μHinf μN μH μSv hWn.2.2.2.2.1 hWn.2.1 hN h2 hSv
    refine ⟨W, hWt, e1, e2, ⟨hT1, νH, h1, ?_⟩, ?_, ?_⟩
    · rw [e4]; exact h3
    · rw [e3]; exact hN1
    · intro v; rw [e5]; exact hSt v
  choose mw hw hNinf hHinf hOm hCov hLoc using hW
  let mg : MeasG X.B.I.cm.sig X.B.I.J D.R.rS := { X.measG with μB := μB' }
  have hg : mg.IsTextNorm := ⟨hG.1, hG.2.1, hG.2.2.1, hG.2.2.2.1, hμB', hG.2.2.2.2.2⟩
  refine ⟨mg, hg, mw, hw, ?_, ψ, hψ, hstd', ?_, ?_⟩
  · refine ⟨hM.1, hM.2.1, hM.2.2.1, fun u => ?_⟩
    have h := hM.2.2.2 u
    constructor
    · show amb (mw u).μNinf = _
      rw [hNinf u]; exact h.1
    · show amb (mw u).μHinf = _
      rw [hHinf u]; exact h.2
  · exact ⟨fun u => ⟨hOm u, hCov u⟩, hBc⟩
  · intro w v
    exact hLoc w v

end GlobalTheory.St.Rescale
