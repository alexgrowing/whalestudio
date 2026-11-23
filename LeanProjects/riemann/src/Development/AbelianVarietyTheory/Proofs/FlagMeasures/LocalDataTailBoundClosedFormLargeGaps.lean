import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
import Formalism.LocalRingCardinality.DataTies
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantLengthTailBoundOfMomentsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantLengthTwoSidedMomentsLargeGapStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantLengthTailBoundPrimedOfUnprimedStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOneSideOfGoodLocalDataStatement

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TypeAsm.TailTopGap

theorem tailP_of_gap : GlobalTheory.GapIn.Hyp → TailP := by
  intro hH Cg cb Cw cT CT C0 _ _
  obtain ⟨CH, hCH, hmom⟩ := GlobalTheory.T.majorantLength_twoSidedMoments_largeGap hH Cg cb Cw cT CT C0
  refine ⟨CH, hCH, fun C₁ => ⟨0, max 1000 (C₁ : ℝ), fun C' Cl _ hCl D large₂ _ hK hTr => ?_⟩⟩
  have hZ : HypZ D large₂ C' Cl Cg cb Cw cT CT C0 := hK.1
  have h1000 : (1000 : ℝ) ≤ Cl := le_trans (le_max_left _ _) hCl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv, -, -, -, -, hClm, -⟩ := hK.1.1

  have hC₁m : C₁ ≤ D.R.m := by
    have h : (C₁ : ℝ) ≤ (D.R.m : ℝ) := le_trans (le_max_right _ _) (le_trans hCl hClm)
    exact_mod_cast h
  have hrS : D.R.rS ≤ D.R.m := by
    unfold Formalism.BasicNotions.Ranks.rS
    omega
  have hm1 : 1 ≤ D.R.m := le_trans (by norm_num) D.R.two_le_m
  have hq : C₁ * D.R.k * D.R.rS ≤ D.R.k * D.R.m ^ 3 := by
    have h2 : C₁ * D.R.rS ≤ D.R.m ^ 3 :=
      calc C₁ * D.R.rS ≤ D.R.m * D.R.m := Nat.mul_le_mul hC₁m hrS
        _ ≤ D.R.m * D.R.m * D.R.m := Nat.le_mul_of_pos_right _ (by omega)
        _ = D.R.m ^ 3 := by ring
    calc C₁ * D.R.k * D.R.rS = D.R.k * (C₁ * D.R.rS) := by ring
      _ ≤ D.R.k * D.R.m ^ 3 := Nat.mul_le_mul_left _ h2
  have hb : 0 < large₂.sc.b := Real.exp_pos _
  have hH1 : 0 < large₂.sc.b ^ (CH * (D.R.m : ℝ)) := Real.rpow_pos_of_pos hb _

  have hTrpos : ∀ w, 0 < Tr D w := by
    intro w
    have hk : 0 ≤ Formalism.MainNotions.S.Bridge.kaS D ^ (2 * D.R.rS) := (even_two_mul _).pow_nonneg _
    by_contra hneg
    push_neg at hneg
    have h0 : Tr D w * Formalism.MainNotions.S.Bridge.kaS D ^ (2 * D.R.rS) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hneg hk
    linarith [hTr w]
  have hv0 : 0 < D.host.v := by linarith
  intro τ u W hW A hA

  have side : ∀ W' : LocW D.R.k D.R.rS, GoodW D τ u u 1 W' → ∀ A' : LocS W', GoodS D (lamD D τ) A' →
      TailBd W'.z W'.νS A'.Φ (C₁ * D.R.k * D.R.rS) (large₂.sc.b ^ (CH * (D.R.m : ℝ))) := by
    intro W' hW' A' hA'
    obtain ⟨hM, hI⟩ := hmom D large₂ C' Cl h1000 hZ τ u W' hW' A' hA' _ hq
    obtain ⟨hzW, -, -, -, -, hG, hWH, -, hN, hQ, -, -, hcont, -, -⟩ :=
      (GlobalTheory.T.amplitude_one_side_of_good_local_data D τ u u 1 W' (lamD D τ) A' hv0 one_pos (hTrpos u) (hTrpos u) hW' hA').1
    have hnull : W'.νS {x | Matrix.of x ∉ GG D.R.k D.R.rS} = 0 := by
      have hf := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hWH hN
      exact ae_iff.mp (Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 hf.1 hf.2 hQ)
    exact GlobalTheory.T.majorantLengthTailBound_of_moments D.R.k D.R.rS W'.z W'.νS A'.Φ _ _ hzW hH1 hnull hcont hM hI

  exact ⟨side W hW A hA, GlobalTheory.T.majorantLengthTailBound_primed_of_unprimed D τ u 1 (lamD D τ) _ _ side W hW A hA⟩

end GlobalTheory.TypeAsm.TailTopGap
