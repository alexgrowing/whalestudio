import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.SumNonneg
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.IsHaarOnIffGroupsUnitaryUnipotentImports
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGrowthStabilizerUnipotentStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ReproducingFormulaReduction
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.ZhatNormLinearBound
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselFubini

open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity

set_option maxHeartbeats 1600000 in

theorem integrable_of_growth (hGG : GrowthG) (hGS : GrowthS) : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ w ∈ R.sm, Integrable (fun y : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => ⟪v, R.σ (Matrix.of y.1) w⟫_ℂ * star ⟪v, R.σ (Matrix.of y.2.1 * Matrix.of y.2.2 * Matrix.of y.1) w⟫_ℂ) (μG.prod (μW.prod μN)) := by
  intro H k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hR hgap hok hS v hv w hw
  obtain ⟨hz, hT, -, -, hWh, hNh, hGh, hq⟩ := hS
  have := hWh.1; have := hNh.1; have := hGh.1
  obtain ⟨C0, Ws, -, hdec⟩ := GlobalTheory.BesselDecay.decay_TK H k r ε mu h R hR hgap hok v hv
  set a := aOf r h - 1 with ha_def
  have hAG : 0 ≤ AG k r := by unfold AG; positivity
  have ha4 := hok.2.2.2
  have hn2 : (0 : ℝ) ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have ha : 0 < a := by linarith
  have ha2 : AG k r < a / 2 := by linarith
  have hsub : ∀ x y : Mx k r, B.gN (x * y) ≤ B.gN x * B.gN y := fun x y => PI.PolynomialProperness.GN.gN_mul_le x y
  have hNIG : ∀ x ∈ GG k r, B.gN x⁻¹ = B.gN x ∧ 1 ≤ B.gN x :=
    fun x hx => PI.PolynomialProperness.GN.polynomial_normInv k r x hx
  have gN0 : ∀ g : Mx k r, 0 ≤ B.gN g := fun g => Real.sqrt_nonneg _
  set C := max (C0 * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum) 0 with hC
  have hC0 : 0 ≤ C := le_max_right _ _
  have hb : ∀ g ∈ GG k r, ‖⟪v, R.σ g w⟫_ℂ‖ ≤ C * B.gN g ^ (-a) := by
    intro g hg
    have e : -a = 1 - aOf r h := by rw [ha_def]; ring
    rw [e]
    exact (hdec w hw g hg).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (gN0 g) _))
  have hGae : ∀ᵐ y ∂μG, Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := ae_iff.mpr hGh.2.2.1
  have hWae : ∀ᵐ p1 ∂μW, Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z := ae_iff.mpr hWh.2.2.1
  have hNae : ∀ᵐ p2 ∂μN, Matrix.of p2 ∈ Formalism.QuantumDeterminants.Nset k r := ae_iff.mpr hNh.2.2.1
  have hPae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)
  have hQae : ∀ᵐ q ∂(μG.prod (μW.prod μN)), Matrix.of q.1 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧
      Matrix.of q.2.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of q.2.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hGae).and (Measure.quasiMeasurePreserving_snd.ae hPae)
  have sUH : ∀ p1 p2 : Formalism.QuantumDeterminants.Mt k r, Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z → Matrix.of p2 ∈ Formalism.QuantumDeterminants.Nset k r →
      Matrix.of p1 * Matrix.of p2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    fun p1 p2 h1 h2 => DDSmoothness.uh_mul h1.1 h2.1
  have hφ : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      (Matrix.of q.2.1 : Mx k r) * Matrix.of q.2.2 * Matrix.of q.1) := by
    have h1 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
        (Matrix.of q.2.1 : Mx k r)) := continuous_fst.comp continuous_snd
    have h2 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
        (Matrix.of q.2.2 : Mx k r)) := continuous_snd.comp continuous_snd
    have h3 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
        (Matrix.of q.1 : Mx k r)) := continuous_fst
    exact (h1.matrix_mul h2).matrix_mul h3
  have hTm : MeasurableSet ((fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      (Matrix.of q.2.1 : Mx k r) * Matrix.of q.2.2 * Matrix.of q.1) ⁻¹' Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :=
    (isClosed_UH.preimage hφ).measurableSet
  have hTae : ∀ᵐ q ∂(μG.prod (μW.prod μN)), q ∈ ((fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      (Matrix.of q.2.1 : Mx k r) * Matrix.of q.2.2 * Matrix.of q.1) ⁻¹' Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
    filter_upwards [hQae] with q hq
    exact DDSmoothness.uh_mul (sUH _ _ hq.2.1 hq.2.2) hq.1
  have hcs := Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn hR.2 w
  have hof : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r)) := continuous_id
  have hc1 : AEStronglyMeasurable (fun y : Formalism.QuantumDeterminants.Mt k r => ⟪v, R.σ (Matrix.of y) w⟫_ℂ) μG := by
    refine aesm_of_contOn (α := Formalism.QuantumDeterminants.Mt k r) (μ := μG)
      (s := {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)}) ?_ ?_ hGae
    · have h0 : ContinuousOn (fun y : Formalism.QuantumDeterminants.Mt k r => R.σ (Matrix.of y) w)
          {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} :=
        hcs.comp hof.continuousOn (fun y hy => hy)
      exact continuousOn_const.inner h0
    · exact (isClosed_UH.preimage hof).measurableSet
  have hc2 : AEStronglyMeasurable (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      ⟪v, R.σ (Matrix.of q.2.1 * Matrix.of q.2.2 * Matrix.of q.1) w⟫_ℂ) (μG.prod (μW.prod μN)) :=
    aesm_of_contOn (α := Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μ := μG.prod (μW.prod μN))
      (continuousOn_const.inner (hcs.comp hφ.continuousOn (fun q hq => hq))) hTm hTae
  have h1' : AEStronglyMeasurable (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      ⟪v, R.σ (Matrix.of q.1) w⟫_ℂ) (μG.prod (μW.prod μN)) :=
    AEStronglyMeasurable.comp_fst (μ := μG) (ν := μW.prod μN) hc1
  have hMi : Integrable (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      (C * C) * (B.gN (Matrix.of q.1) ^ (-(a / 2)) *
        B.gN (Matrix.of q.2.1 * Matrix.of q.2.2) ^ (-(a / 2)))) (μG.prod (μW.prod μN)) :=
    Integrable.const_mul (Integrable.mul_prod (hGG k r μG (a / 2) hGh ha2)
      (hGS k r z μW μN μG νq (a / 2) hz hT hWh hNh hGh hq ha2)) _
  refine Integrable.mono' hMi (h1'.mul (continuous_star.comp_aestronglyMeasurable hc2)) ?_
  filter_upwards [hQae] with q hq
  obtain ⟨hy, hp1, hp2⟩ := hq
  have hs := sUH _ _ hp1 hp2
  set s := Matrix.of q.2.1 * Matrix.of q.2.2 with hs_def
  set Y : Mx k r := Matrix.of q.1 with hY_def
  have hg : s * Y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hs hy
  have hY1 := (hNIG Y hy).2
  have hg1 := (hNIG _ hg).2
  have hs1 := (hNIG s hs).2
  have hSle : B.gN s ≤ B.gN (s * Y) * 1 * B.gN Y := by
    have e : s = (s * Y) * Y⁻¹ := by
      rw [Matrix.mul_assoc, (uh_inv hy).2.1, Matrix.mul_one]
    calc B.gN s = B.gN ((s * Y) * Y⁻¹) := by rw [← e]
      _ ≤ B.gN (s * Y) * B.gN Y⁻¹ := hsub _ _
      _ = _ := by rw [(hNIG _ hy).1, mul_one]
  have key := key_bound hg1 le_rfl hY1 (by linarith) ha hSle
  rw [Real.one_rpow, one_mul] at key
  rw [norm_mul, norm_star]
  calc ‖⟪v, R.σ Y w⟫_ℂ‖ * ‖⟪v, R.σ (s * Y) w⟫_ℂ‖
      ≤ (C * B.gN Y ^ (-a)) * (C * B.gN (s * Y) ^ (-a)) :=
        mul_le_mul (hb Y hy) (hb _ hg) (norm_nonneg _) (mul_nonneg hC0 (Real.rpow_nonneg (gN0 _) _))
    _ = (C * C) * (B.gN Y ^ (-a) * B.gN (s * Y) ^ (-a)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left key (mul_nonneg hC0 hC0)

theorem integrable_GS : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ w ∈ R.sm, Integrable (fun y : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => ⟪v, R.σ (Matrix.of y.1) w⟫_ℂ * star ⟪v, R.σ (Matrix.of y.2.1 * Matrix.of y.2.2 * Matrix.of y.1) w⟫_ℂ) (μG.prod (μW.prod μN)) :=
  integrable_of_growth GlobalTheory.T.growth_unitaryGroup_rpow_neg_integrable GlobalTheory.T.besselGrowth_stabilizer_unipotent

end GlobalTheory.BesselFubini
