import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPtRepTrDat
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.JEqOrbInt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellConv
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformBesselConstant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BFCell
import Formalism.FormalDegreeBessel.FinalBF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellQuotientNormalisesUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapConjUnipotentHaarEqSmulStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableBesselPairMajorantMulRightStatement
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

noncomputable section
namespace GlobalTheory.BigConv

theorem good_point (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (hk : 1 ≤ k) (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) :
    ∃ μ₁ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, μ₁ᴴ * Formalism.QuantumDeterminants.Hb k * μ₁ = Formalism.QuantumDeterminants.Hb k ∧
      0 < Formalism.QuantumDeterminants.Gf k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c μ₁) := by
  obtain ⟨μs, -, hμ⟩ := Formalism.FourierDecayAlt.P.SettingConstruction.sectionExists k r L.z L.z' hk L.hz.1 L.hz'.1 L.hz.2 L.hz'.2
  set τ := Formalism.QuantumDeterminants.Tz k r L.z * Formalism.QuantumDeterminants.Tz k r L.z' with hτ
  have hτ0 : 0 < τ := mul_pos L.hz.2 L.hz'.2
  set ζ : ℂ := ((τ + 1 : ℝ) : ℂ) with hζ
  have hn : τ < Complex.normSq ζ := by
    rw [hζ, Complex.normSq_ofReal]; nlinarith
  obtain ⟨hU, hzz⟩ := hμ ζ hn
  refine ⟨μs ζ, hU, ?_⟩
  have hmin := Formalism.QuantumDeterminants.big_cell_minors_holds k r L.z L.z' c (μs ζ) L.hz.1 L.hz'.1
  have hz := hmin.2.2 hc
  rw [Formalism.FourierDecayAlt.P.BigCellHermitian.herm_bigCell _ _ L.hz.1 L.hz'.1, hzz] at hz
  have hr := hmin.1 (Fin.last r)
  set P := Formalism.QuantumDeterminants.Dmin k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c (μs ζ)) ⟨r, by omega⟩ with hP
  have hP0 : P ≠ 0 := by
    have : P = ∏ a : Fin r with a.val < (Fin.last r).val, c a := hr
    rw [this]; exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
  have hlast : Formalism.QuantumDeterminants.Dmin k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c (μs ζ)) (Fin.last (r + 1)) = ζ * P := by
    unfold Formalism.QuantumDeterminants.zeta at hz
    rw [← hP] at hz
    have h2 := div_mul_cancel₀ (Formalism.QuantumDeterminants.Dmin k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c (μs ζ)) (Fin.last (r + 1))) hP0
    rw [hz] at h2
    exact h2.symm
  unfold Formalism.QuantumDeterminants.Gf
  rw [hlast, ← hP, Complex.normSq_mul]
  have h1 : 0 < Complex.normSq P := Complex.normSq_pos.2 hP0
  nlinarith

open Formalism.FourierDecayAlt in

theorem conv_good (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h)
    (hgap : GlobalTheory.CellAmp.GapCell k r h) (hκ : L.κN ≠ ⊤) (c : Fin r → ℂ)
    (μ₁ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hc : ∀ a, c a ≠ 0) (hμ₁ : μ₁ᴴ * Formalism.QuantumDeterminants.Hb k * μ₁ = Formalism.QuantumDeterminants.Hb k)
    (hG : 0 < Formalism.QuantumDeterminants.Gf k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c μ₁)) :
    ∃ b : ℝ, 0 ≤ b ∧ Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b ∧
      MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj (Formalism.QuantumDeterminants.bigCell k r c μ₁) b) (Formalism.MainNotions.S.pairMeas L) := by
  have hg := Formalism.QuantumDeterminants.big_cell_mem_holds k r c μ₁ hc hμ₁
  have hu := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg
  have hinv : (Formalism.QuantumDeterminants.bigCell k r c μ₁)⁻¹ * Formalism.QuantumDeterminants.bigCell k r c μ₁ = 1 := Matrix.nonsing_inv_mul _ hu
  have hZ := Formalism.QuantumDeterminants.bigCellZhat k r L.z L.z' c μ₁ L.hz.1 L.hz'.1
  set ζ := Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.bigCell k r c μ₁ *ᵥ L.z') L.z with hζ
  have hmono : Formalism.FourierDecayAlt.C2.IsMonomial (Formalism.QuantumDeterminants.Zhat k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c μ₁)) := by
    have hζ0 : ζ ≠ 0 := by
      intro h0
      have hmin := Formalism.QuantumDeterminants.big_cell_minors_holds k r L.z L.z' c μ₁ L.hz.1 L.hz'.1
      have hz := hmin.2.2 hc
      set P := Formalism.QuantumDeterminants.Dmin k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c μ₁) ⟨r, by omega⟩ with hP
      have hr := hmin.1 (Fin.last r)
      have hP0 : P ≠ 0 := by
        have : P = ∏ a : Fin r with a.val < (Fin.last r).val, c a := hr
        rw [this]; exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
      unfold Formalism.QuantumDeterminants.zeta at hz
      rw [← hP, ← hζ, h0, div_eq_zero_iff] at hz
      have hD : Formalism.QuantumDeterminants.Dmin k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c μ₁) (Fin.last (r + 1)) = 0 :=
        hz.resolve_right hP0
      unfold Formalism.QuantumDeterminants.Gf at hG
      rw [hD, ← hP] at hG
      have : 0 ≤ Complex.normSq P := Complex.normSq_nonneg _
      have := mul_pos L.hz.2 L.hz'.2
      simp at hG
      nlinarith
    refine ⟨1, fun a => if h : a.val < r then c ⟨a.val, h⟩ else ζ, fun a => ?_, ?_⟩
    · dsimp only
      split_ifs
      · exact hc _
      · exact hζ0
    · refine hZ.trans ?_
      ext i j
      rw [Matrix.diagonal_apply]
      show _ = if i = j then _ else _
      by_cases h : i = j
      · rw [if_pos h, if_pos h, h]
      · rw [if_neg h, if_neg h]
  have hR := GlobalTheory.AmpNorm.rStab_bigCell c μ₁ hc hg
  have hcd := GlobalTheory.CellAmp.Model.cellData_open L 0 _ hg hinv hG hmono hR
  exact GlobalTheory.CellMaj.cellConv k r L h 0 _ _ _ _ hκ hok hgap hcd hmono

theorem bigConv : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ), Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GlobalTheory.CellAmp.GapCell k r h → L.κN ≠ ⊤ → 0 < L.κN → L.c ≠ 0 → ∀ (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) → μᴴ * Formalism.QuantumDeterminants.Hb k * μ = Formalism.QuantumDeterminants.Hb k → ∃ b : ℝ, 0 ≤ b ∧ Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b ∧ MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj (Formalism.QuantumDeterminants.bigCell k r c μ) b) (Formalism.MainNotions.S.pairMeas L) := by
  intro k r L h hok hgap hκ hκ0 hcL c μ hc hμ
  obtain ⟨μ₁, hμ₁, hG⟩ := good_point k r L hok.1 c hc
  obtain ⟨b, hb0, hb1, hint⟩ := conv_good k r L h hok hgap hκ c μ₁ hc hμ₁ hG
  have hg₁ := Formalism.QuantumDeterminants.big_cell_mem_holds k r c μ₁ hc hμ₁
  have hg := Formalism.QuantumDeterminants.big_cell_mem_holds k r c μ hc hμ
  have hu₁ := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg₁
  set a := (Formalism.QuantumDeterminants.bigCell k r c μ₁)⁻¹ * Formalism.QuantumDeterminants.bigCell k r c μ with ha
  have haU : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hg₁) hg
  have hN := GlobalTheory.T.bigCell_quotient_normalises_unipotent k r c μ₁ μ hc hμ₁ hμ
  obtain ⟨C, hC, hmap⟩ := GlobalTheory.T.map_conj_unipotentHaar_eq_smul k r L hκ0 hκ a haU hN
  refine ⟨b, hb0, hb1, ?_⟩
  have e : Formalism.QuantumDeterminants.bigCell k r c μ₁ * a = Formalism.QuantumDeterminants.bigCell k r c μ := by
    rw [ha, Matrix.mul_nonsing_inv_cancel_left _ _ hu₁]
  rw [← e]
  exact GlobalTheory.T.integrable_besselPairMajorant_mul_right k r L _ a b C hκ0 hκ hb0 hg₁ haU hC hmap hint

end GlobalTheory.BigConv
end
