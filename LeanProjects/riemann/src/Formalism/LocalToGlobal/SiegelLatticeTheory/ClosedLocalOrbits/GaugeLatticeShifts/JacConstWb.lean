import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstWbB

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.WB

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

theorem wbConst_pos {k : ℕ} {T T' a a' : ℝ} (hT : 0 < T) (hT' : 0 < T') (ha : 0 < a) (ha' : 0 < a') :
    0 < wbConst k T T' a a' := by
  unfold wbConst
  have h1 : ∀ j, 0 < Formalism.MainNotions.S.UnitaryVolumeMass.volU j := fun j => by
    unfold Formalism.MainNotions.S.UnitaryVolumeMass.volU
    exact Finset.prod_pos fun i _ => by positivity
  have := h1 k
  have := h1 (k - 1)
  positivity

theorem wbHaar_of (hI : RankGauge) (hS : GaugeShiftW) (hR : RhsWLim) : WbHaar := by
  intro k r z z' hk hz hz' hT hT' μb μW μW' hμb hW hW' a a' ha ha' hma hma' μsec hsec φ hφ
  have D : WbData k r z z' μW μW' a a' μsec := ⟨hk, hz, hz', hT, hT', hW, hW', ha, ha', hma, hma', hsec⟩
  obtain ⟨C, hC, hF⟩ := hI k r z z' μb μW μW' a a' μsec D hμb
  have hlim1 : Tendsto (fun ρ : ℝ => (μb (bBall k r ρ)).toReal / bVol k r ρ) (𝓝[>] 0) (𝓝 1) := hμb.2
  have hlim2 := (hR k r z z' μW μW' a a' μsec D).const_mul (C : ℝ)
  have heq : ∀ᶠ ρ in 𝓝[>] (0:ℝ), (μb (bBall k r ρ)).toReal / bVol k r ρ =
      (C : ℝ) * ((rhsW k r z z' μW μW' μsec ((mBall k r z z' μsec ρ).indicator 1)).toReal / bVol k r ρ) := by
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    obtain ⟨hm, he⟩ := hS k r z z' μb μW μW' a a' μsec D hμb.1 ρ hρ
    have h1 : ∫⁻ x, (mBall k r z z' μsec ρ).indicator 1 x ∂μb = μb (mBall k r z z' μsec ρ) :=
      lintegral_indicator_one hm
    have h2 := hF _ (measurable_one.indicator hm)
    rw [h1, he] at h2
    rw [h2, ENNReal.toReal_mul, ENNReal.coe_toReal, mul_div_assoc]
  have hu := tendsto_nhds_unique (hlim1.congr' heq) hlim2
  have hw := wbConst_pos (k := k) hT hT' ha ha'
  have hCr : (C : ℝ) = wbConst k (Tz k r z) (Tz k r z') a a' := by
    field_simp at hu
    linarith
  have hCe : (C : ℝ≥0∞) = ENNReal.ofReal (wbConst k (Tz k r z) (Tz k r z') a a') := by
    rw [← hCr, ENNReal.ofReal_coe_nnreal]
  rw [hF φ hφ, hCe]
  rfl

end Formalism.L2.SG.Pf.WB
