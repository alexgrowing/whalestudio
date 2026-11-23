import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.SchurDecayBounds.NormIdPair
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.DecayZeroRight.NormDec

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace PI.WBL.NIS

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL PI.WBL.FSW Formalism.MainNotions.InverseNormDecayBounds

variable {k r : ℕ}

theorem gN_shift {s y : Mx k r} (hs : s ∈ UH (Hpk k r)) (hy : y ∈ UH (Hpk k r)) {a : ℝ} (ha : 0 ≤ a) :
    Formalism.FourierDecayAlt.B.gN (s * y) ^ (-a) ≤ Formalism.FourierDecayAlt.B.gN y ^ a * Formalism.FourierDecayAlt.B.gN s ^ (-a) := by
  have hN := Formalism.MainNotions.InverseNormDecayBounds.normInvP k r
  have hy1 : 1 ≤ Formalism.FourierDecayAlt.B.gN y := (hN.1 y hy).2
  have hs1 : 1 ≤ Formalism.FourierDecayAlt.B.gN s := (hN.1 s hs).2
  have hyinv : Formalism.FourierDecayAlt.B.gN y⁻¹ = Formalism.FourierDecayAlt.B.gN y := (hN.1 y hy).1
  have hdet : IsUnit y.det := by
    have h1 : yᴴ * Hpk k r * y = Hpk k r := hy
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_mul] at h2
    have hH : IsUnit (Hpk k r).det := Formalism.MainNotions.BesselShellMomentBounds.Hpk_det_unit k r
    have h3 : (yᴴ).det * y.det = 1 := by
      apply hH.mul_left_cancel
      calc (Hpk k r).det * ((yᴴ).det * y.det) = (yᴴ).det * (Hpk k r).det * y.det := by ring
        _ = (Hpk k r).det := h2
        _ = (Hpk k r).det * 1 := (mul_one _).symm
    exact IsUnit.of_mul_eq_one ((yᴴ).det) (by rw [mul_comm]; exact h3)
  have hsy : s = s * y * y⁻¹ := by rw [Matrix.mul_nonsing_inv_cancel_right _ _ hdet]
  have hle : Formalism.FourierDecayAlt.B.gN s ≤ Formalism.FourierDecayAlt.B.gN (s * y) * Formalism.FourierDecayAlt.B.gN y := by
    calc Formalism.FourierDecayAlt.B.gN s = Formalism.FourierDecayAlt.B.gN (s * y * y⁻¹) := by rw [← hsy]
      _ ≤ Formalism.FourierDecayAlt.B.gN (s * y) * Formalism.FourierDecayAlt.B.gN y⁻¹ := hN.2 _ _
      _ = Formalism.FourierDecayAlt.B.gN (s * y) * Formalism.FourierDecayAlt.B.gN y := by rw [hyinv]
  have hypos : 0 < Formalism.FourierDecayAlt.B.gN y := by linarith
  have hspos : 0 < Formalism.FourierDecayAlt.B.gN s := by linarith
  have hq : Formalism.FourierDecayAlt.B.gN s / Formalism.FourierDecayAlt.B.gN y ≤ Formalism.FourierDecayAlt.B.gN (s * y) := by
    rw [div_le_iff₀ hypos]; exact hle
  have hqpos : 0 < Formalism.FourierDecayAlt.B.gN s / Formalism.FourierDecayAlt.B.gN y := div_pos hspos hypos
  calc Formalism.FourierDecayAlt.B.gN (s * y) ^ (-a) ≤ (Formalism.FourierDecayAlt.B.gN s / Formalism.FourierDecayAlt.B.gN y) ^ (-a) :=
        Real.rpow_le_rpow_of_nonpos hqpos hq (by linarith)
    _ = Formalism.FourierDecayAlt.B.gN y ^ a * Formalism.FourierDecayAlt.B.gN s ^ (-a) := by
        rw [Real.div_rpow hspos.le hypos.le, Real.rpow_neg hypos.le, div_eq_mul_inv, inv_inv, mul_comm]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]

theorem measurableSet_S (z : Fin (2 * r + k + 1) → ℂ) :
    MeasurableSet {p : Mt k r × Mt k r | Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r} := by
  have h2 : IsClosed {p : Mt k r × Mt k r | Matrix.of p.1 ∈ UWset k r z} :=
    (PI.WUN.isClosed_UW z).preimage continuous_fst
  have h3 : IsClosed {p : Mt k r × Mt k r | Matrix.of p.2 ∈ Nset k r} :=
    (PI.WUN.isClosed_N k r).preimage continuous_snd
  exact (h2.inter h3).measurableSet

theorem coefS_aesm {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    (hds : IsDSHpk k r ε lam σ) {z : Fin (2 * r + k + 1) → ℂ} (hGr : Cv.GrpF k r z)
    {μW μN : Measure (Mt k r)}
    (hM1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r) (w v : H) :
    AEStronglyMeasurable (fun p : Mt k r × Mt k r => ⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ) (μW.prod μN) := by
  have hm : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mx k r) * Matrix.of p.2) :=
    (continuous_fst : Continuous (fun p : Mt k r × Mt k r => p.1)).matrix_mul continuous_snd
  have h := (ds_rep hds).2.2.2 w
  have hc : ContinuousOn (fun p : Mt k r × Mt k r => ⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ)
      {p : Mt k r × Mt k r | Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r} := by
    refine continuousOn_const.inner (h.comp hm.continuousOn ?_)
    intro p hp
    exact hGr.1 _ hp.1.1 _ hp.2.1
  have hc' := hc.aestronglyMeasurable (μ := μW.prod μN) (measurableSet_S z)
  rwa [Measure.restrict_eq_self_of_ae_mem
    (s := {p : Mt k r × Mt k r | Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r}) hM1] at hc'

theorem int_beF_of_bd {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Mx k r → (H →L[ℂ] H)} (hds : IsDSHpk k r ε lam σ) {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ}
    {π : Mx k r → (Wp →L[ℂ] Wp)} (hGr : Cv.GrpF k r z) (hPi : Cv.PiU z π)
    {μW μN : Measure (Mt k r)} [SFinite μN] (hM : Cv.MeasF z π μW μN) {w v : H} {b C : ℝ} (hb : 0 ≤ b)
    (hbd : ∀ y ∈ UH (Hpk k r), ‖⟪v, σ y w⟫_ℂ‖ ≤ C * Formalism.FourierDecayAlt.B.gN y ^ (-b))
    (hS : Integrable (fun p : Mt k r × Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-(b / 2)))
      (μW.prod μN)) :
    Integrable (beF z c π σ w v) (μW.prod μN) := by
  refine Integrable.mono' (hS.const_mul |C|)
    (Cv.beF_aesm z c π μW μN σ w v hM.2.2.2 (coefS_aesm hds hGr hM.1 w v)) ?_
  filter_upwards [hM.1] with p hp
  have hs : Matrix.of p.1 * Matrix.of p.2 ∈ UH (Hpk k r) := hGr.1 _ hp.1.1 _ hp.2.1
  have g1 := ((normInvP k r).1 _ hs).2
  calc ‖beF z c π σ w v p‖ ≤ ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ‖ :=
        Cv.norm_beF_le z c π σ w v hGr hPi p hp.1
    _ ≤ C * Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-b) := hbd _ hs
    _ ≤ |C| * Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-b) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by linarith) _)
    _ ≤ |C| * Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-(b / 2)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le g1 (by linarith)) (abs_nonneg C)

theorem bd_shift {σ : Mx k r → (H →L[ℂ] H)} (hSg : Cv.SigU σ) {w v : H} {b C : ℝ} (hb : 0 ≤ b)
    (hbd : ∀ y ∈ UH (Hpk k r), ‖⟪v, σ y w⟫_ℂ‖ ≤ C * Formalism.FourierDecayAlt.B.gN y ^ (-b))
    {x : Mx k r} (hx : x ∈ UH (Hpk k r)) :
    ∀ y ∈ UH (Hpk k r), ‖⟪v, σ y (σ x w)⟫_ℂ‖ ≤ (|C| * Formalism.FourierDecayAlt.B.gN x ^ b) * Formalism.FourierDecayAlt.B.gN y ^ (-b) := by
  intro y hy
  have hyx : y * x ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hy hx
  have e : σ y (σ x w) = σ (y * x) w := by rw [hSg.2.1 _ hy _ hx]; rfl
  have g1 := ((normInvP k r).1 _ hyx).2
  rw [e]
  calc ‖⟪v, σ (y * x) w⟫_ℂ‖ ≤ C * Formalism.FourierDecayAlt.B.gN (y * x) ^ (-b) := hbd _ hyx
    _ ≤ |C| * Formalism.FourierDecayAlt.B.gN (y * x) ^ (-b) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by linarith) _)
    _ ≤ |C| * (Formalism.FourierDecayAlt.B.gN x ^ b * Formalism.FourierDecayAlt.B.gN y ^ (-b)) :=
        mul_le_mul_of_nonneg_left (gN_shift hy hx hb) (abs_nonneg C)
    _ = _ := by ring

theorem dInt_of_bd {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Mx k r → (H →L[ℂ] H)} (hds : IsDSHpk k r ε lam σ) {z : Fin (2 * r + k + 1) → ℂ}
    (hGr : Cv.GrpF k r z) {μW μN μG : Measure (Mt k r)} [SFinite μW] [SFinite μN] [SFinite μG]
    (hHaar : IsHaarOn (UH (Hpk k r)) μG)
    (hM1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r)
    {u v : H} {b C : ℝ} (hb : 0 ≤ b)
    (hbd : ∀ y ∈ UH (Hpk k r), ‖⟪v, σ y u⟫_ℂ‖ ≤ C * Formalism.FourierDecayAlt.B.gN y ^ (-b))
    (hGg : Integrable (fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-(b / 2))) μG)
    (hS : Integrable (fun p : Mt k r × Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-(b / 2)))
      (μW.prod μN)) :
    Integrable (fun q : Mt k r × (Mt k r × Mt k r) =>
      ‖⟪v, σ (Matrix.of q.1) u⟫_ℂ‖ * ‖⟪v, σ (sM q.2 * Matrix.of q.1) u⟫_ℂ‖) (μG.prod (μW.prod μN)) := by
  have hprod : Integrable (fun q : Mt k r × (Mt k r × Mt k r) =>
      Formalism.FourierDecayAlt.B.gN (Matrix.of q.1) ^ (-(b / 2)) * Formalism.FourierDecayAlt.B.gN (Matrix.of q.2.1 * Matrix.of q.2.2) ^ (-(b / 2)))
      (μG.prod (μW.prod μN)) := by
    exact hGg.mul_prod hS
  refine Integrable.mono' (hprod.const_mul (|C| * |C|)) ?_ ?_
  · exact ((coef_aesm hds hHaar u v).comp_fst.norm).mul (matrix_coefficient_ae_strongly_measurable hds hGr hHaar hM1 u v).norm
  · filter_upwards [joint_ae hHaar hM1] with q hq
    have hy : Matrix.of q.1 ∈ UH (Hpk k r) := hq.1
    have hs : sM q.2 ∈ UH (Hpk k r) := hGr.1 _ hq.2.1.1 _ hq.2.2.1
    have hsy : sM q.2 * Matrix.of q.1 ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hs hy
    have gy := ((normInvP k r).1 _ hy).2
    have gsy := ((normInvP k r).1 _ hsy).2
    have gs := ((normInvP k r).1 _ hs).2
    have hb2 : 0 ≤ b / 2 := by linarith
    have a1 : ‖⟪v, σ (Matrix.of q.1) u⟫_ℂ‖ ≤ |C| * Formalism.FourierDecayAlt.B.gN (Matrix.of q.1) ^ (-b) :=
      (hbd _ hy).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by linarith) _))
    have a2 : ‖⟪v, σ (sM q.2 * Matrix.of q.1) u⟫_ℂ‖ ≤
        |C| * (Formalism.FourierDecayAlt.B.gN (Matrix.of q.1) ^ (b / 2) * Formalism.FourierDecayAlt.B.gN (sM q.2) ^ (-(b / 2))) := by
      calc ‖⟪v, σ (sM q.2 * Matrix.of q.1) u⟫_ℂ‖ ≤ C * Formalism.FourierDecayAlt.B.gN (sM q.2 * Matrix.of q.1) ^ (-b) :=
            hbd _ hsy
        _ ≤ |C| * Formalism.FourierDecayAlt.B.gN (sM q.2 * Matrix.of q.1) ^ (-b) :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by linarith) _)
        _ ≤ |C| * Formalism.FourierDecayAlt.B.gN (sM q.2 * Matrix.of q.1) ^ (-(b / 2)) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le gsy (by linarith)) (abs_nonneg C)
        _ ≤ _ := mul_le_mul_of_nonneg_left (gN_shift hs hy hb2) (abs_nonneg C)
    have ey : Formalism.FourierDecayAlt.B.gN (Matrix.of q.1) ^ (-b) * Formalism.FourierDecayAlt.B.gN (Matrix.of q.1) ^ (b / 2) =
        Formalism.FourierDecayAlt.B.gN (Matrix.of q.1) ^ (-(b / 2)) := by
      rw [← Real.rpow_add (by linarith)]
      congr 1
      ring
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖⟪v, σ (Matrix.of q.1) u⟫_ℂ‖ * ‖⟪v, σ (sM q.2 * Matrix.of q.1) u⟫_ℂ‖
        ≤ (|C| * Formalism.FourierDecayAlt.B.gN (Matrix.of q.1) ^ (-b)) *
            (|C| * (Formalism.FourierDecayAlt.B.gN (Matrix.of q.1) ^ (b / 2) * Formalism.FourierDecayAlt.B.gN (sM q.2) ^ (-(b / 2)))) :=
          mul_le_mul a1 a2 (norm_nonneg _) (by positivity)
      _ = (|C| * |C|) * ((Formalism.FourierDecayAlt.B.gN (Matrix.of q.1) ^ (-b) * Formalism.FourierDecayAlt.B.gN (Matrix.of q.1) ^ (b / 2)) *
            Formalism.FourierDecayAlt.B.gN (sM q.2) ^ (-(b / 2))) := by ring
      _ = _ := by rw [ey]; rfl

end PI.WBL.NIS
