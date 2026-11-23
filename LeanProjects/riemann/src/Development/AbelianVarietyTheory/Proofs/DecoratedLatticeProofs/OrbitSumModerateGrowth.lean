import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTermSeriesSummableModerateGrowthUniformStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspRapidDecayOfSobolev
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ENNReal NNReal

set_option maxHeartbeats 1000000

namespace GlobalTheory.Unf

theorem orbit_sum_moderate_growth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (vW : Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∃ (C : ℝ) (A : ℕ), ∀ g : GA D V, ∫⁻ p in vN.𝓝 ×ˢ vW.𝓕, ∑' y : Orb W x₀, ‖G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1‖ₑ ∂(vN.ν.prod vW.μ) ≤ ENNReal.ofReal (C * height V g ^ A) := by
  intro D ψ V V₀ W ρ d χV χW om om' hw hw' vS vN vW x₀ G Φ hG hΦ
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (isIsoSub_e d)
  haveI := vN.unit.1
  haveI := vW.haar
  obtain ⟨C, A, hC⟩ := GlobalTheory.T.thetaTermSeries_summable_moderateGrowth_uniform D ψ V V₀ W ρ d χV χW om om' hw hw' vS Φ hΦ
  obtain ⟨B, hBd⟩ := hG.2.2 A
  have hB0 : 0 ≤ B := (mul_nonneg (norm_nonneg _) (pow_nonneg (quotHeight_pos W 1).le _)).trans (hBd 1)
  have hfin : (vN.ν.prod vW.μ) (vN.𝓝 ×ˢ vW.𝓕) ≠ ⊤ := by
    rw [Measure.prod_prod, vN.unit.2.2, one_mul]
    exact GlobalTheory.Chain.LiftReg.vol_ne_top vW.haar vW.fund
  have hK0 : 0 ≤ max C 0 * B := mul_nonneg (le_max_right _ _) hB0
  have hm0 : 0 ≤ ((vN.ν.prod vW.μ) (vN.𝓝 ×ˢ vW.𝓕)).toReal := ENNReal.toReal_nonneg
  refine ⟨max C 0 * B * ((vN.ν.prod vW.μ) (vN.𝓝 ×ˢ vW.𝓕)).toReal, A, fun g => ?_⟩
  have hg0 : 0 ≤ height V g ^ A := pow_nonneg (height_pos V g).le _
  have hpt : ∀ (n : flagN d) (h : GA D W),
      ∑' y : Orb W x₀, ‖G h * term ψ d W vS (om (n.1 * g, h) Φ) y.1‖ₑ ≤
        ENNReal.ofReal (max C 0 * B * height V g ^ A) := by
    intro n h
    have h1 : ∑' y : Orb W x₀, ‖G h * term ψ d W vS (om (n.1 * g, h) Φ) y.1‖ₑ =
        ‖G h‖ₑ * ∑' y : Orb W x₀, ‖term ψ d W vS (om (n.1 * g, h) Φ) y.1‖ₑ := by
      simp_rw [enorm_mul]
      exact ENNReal.tsum_mul_left
    have h2 : ∑' y : Orb W x₀, ‖term ψ d W vS (om (n.1 * g, h) Φ) y.1‖ₑ ≤
        ∑' x : Matrix (Fin W.rank) (Fin ρ) D.host.E, ‖term ψ d W vS (om (n.1 * g, h) Φ) x‖ₑ :=
      ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
    have hq0 : 0 ≤ quotHeight W h ^ A := pow_nonneg (quotHeight_pos W h).le _
    have h3 : ∑' x : Matrix (Fin W.rank) (Fin ρ) D.host.E, ‖term ψ d W vS (om (n.1 * g, h) Φ) x‖ₑ ≤
        ENNReal.ofReal (max C 0 * height V g ^ A * quotHeight W h ^ A) := by
      refine (hC g h n.1 n.2).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [mul_pow, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hg0) hq0
    have h4 : ‖G h‖ * (max C 0 * height V g ^ A * quotHeight W h ^ A) ≤ max C 0 * B * height V g ^ A := by
      have e : ‖G h‖ * (max C 0 * height V g ^ A * quotHeight W h ^ A) =
          max C 0 * height V g ^ A * (‖G h‖ * quotHeight W h ^ A) := by ring
      rw [e, mul_right_comm (max C 0) B]
      exact mul_le_mul_of_nonneg_left (hBd h) (mul_nonneg (le_max_right _ _) hg0)
    rw [h1]
    refine (mul_le_mul' le_rfl (h2.trans h3)).trans ?_
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal h4
  calc ∫⁻ p in vN.𝓝 ×ˢ vW.𝓕, ∑' y : Orb W x₀, ‖G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1‖ₑ ∂(vN.ν.prod vW.μ)
      ≤ ∫⁻ p in vN.𝓝 ×ˢ vW.𝓕, ENNReal.ofReal (max C 0 * B * height V g ^ A) ∂(vN.ν.prod vW.μ) :=
        lintegral_mono fun p => hpt p.1 p.2
    _ = ENNReal.ofReal (max C 0 * B * height V g ^ A) * (vN.ν.prod vW.μ) (vN.𝓝 ×ˢ vW.𝓕) := setLIntegral_const _ _
    _ = ENNReal.ofReal (max C 0 * B * ((vN.ν.prod vW.μ) (vN.𝓝 ×ˢ vW.𝓕)).toReal * height V g ^ A) := by
        rw [← ENNReal.ofReal_toReal hfin, ENNReal.toReal_ofReal hm0, ← ENNReal.ofReal_mul (mul_nonneg hK0 hg0)]
        congr 1; ring

end GlobalTheory.Unf
