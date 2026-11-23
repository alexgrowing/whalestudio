import Formalism.HermitianCurvature.HermitianCurvatureProofs.MapInvMEq

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem l_enorm_le {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp]
    {σ : Mx k r → (H →L[ℂ] H)} {w0 : H} (hds : PI.UpqRep.IsDSHpk k r ε lam σ)
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    {l : H → Wp} (hbe : ∀ x ∈ DDsp σ w0, ∀ y ∈ DDsp σ w0,
        be z c π σ μW μN x y = (innerSL ℂ (l y)).smulRight (l x))
    {v : H} (hv : v ∈ DDsp σ w0) (hlv : l v ≠ 0) {x : H} (hx : x ∈ DDsp σ w0)
    {g : Mx k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ‖l (σ g x)‖ₑ ≤ (‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) *
      ∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * g) x⟫_ℂ‖ₑ ∂(μW.prod μN) := by
  rw [l_of_be (hbe _ (dd_stable hds hg x hx) v hv) hlv]
  have hbe' := be_enorm_le (c := c) hds hT hπ hW hN (x := x) (v := v) hg
  calc ‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹ • (be z c π σ μW μN (σ g x) v) (l v)‖ₑ
      = ‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖(be z c π σ μW μN (σ g x) v) (l v)‖ₑ := enorm_smul _ _
    _ ≤ ‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * (‖be z c π σ μW μN (σ g x) v‖ₑ * ‖l v‖ₑ) := by
        gcongr
        exact ContinuousLinearMap.le_opENorm _ _
    _ ≤ ‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ((∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * g) x⟫_ℂ‖ₑ ∂(μW.prod μN)) *
          ‖l v‖ₑ) := by gcongr
    _ = _ := by ring

theorem lint_left {μG : Measure (Formalism.QuantumDeterminants.Mt k r)} (hG : B.IsHaarOn (B.GV k r) μG)
    {a : Mx k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) {F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F (Formalism.QuantumDeterminants.lmulM a x) ∂μG = ∫⁻ x, F x ∂μG := by
  have hm : Measurable (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) a) := by
    have : Continuous (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) a) := by
      unfold Formalism.QuantumDeterminants.lmulM
      exact continuous_const.matrix_mul (show Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r)) from continuous_id)
    exact this.measurable
  rw [← lintegral_map hF hm, hG.left a ha]

theorem gN_mul_rpow (hNI : NormInv) {x Y : Mx k r} (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hY : Y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) {b : ℝ} (hb : 0 ≤ b) :
    B.gN (Y * x) ^ (-b) ≤ B.gN x ^ b * B.gN Y ^ (-b) := by
  obtain ⟨hsub, hinv⟩ := hNI k r
  have hxi := MatrixMultiplicationContinuity.uh_inv hx
  have hYx : Y * x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hY hx
  have h1 : 1 ≤ B.gN x := (hinv x hx).2
  have h2 : 1 ≤ B.gN Y := (hinv Y hY).2
  have h3 : 1 ≤ B.gN (Y * x) := (hinv _ hYx).2
  have hle : B.gN Y ≤ B.gN (Y * x) * B.gN x := by
    have e : Y = Y * x * x⁻¹ := by rw [Matrix.mul_assoc, hxi.2.1, Matrix.mul_one]
    calc B.gN Y = B.gN (Y * x * x⁻¹) := by rw [← e]
      _ ≤ B.gN (Y * x) * B.gN x⁻¹ := hsub _ _
      _ = B.gN (Y * x) * B.gN x := by rw [(hinv x hx).1]
  have hpos : 0 < B.gN x := lt_of_lt_of_le one_pos h1
  have hq : B.gN Y / B.gN x ≤ B.gN (Y * x) := (div_le_iff₀ hpos).mpr hle
  have hqpos : 0 < B.gN Y / B.gN x := div_pos (lt_of_lt_of_le one_pos h2) hpos
  calc B.gN (Y * x) ^ (-b) ≤ (B.gN Y / B.gN x) ^ (-b) :=
        Real.rpow_le_rpow_of_nonpos hqpos hq (by linarith)
    _ = B.gN x ^ b * B.gN Y ^ (-b) := by
        rw [Real.div_rpow (lt_of_lt_of_le one_pos h2).le hpos.le, Real.rpow_neg hpos.le,
          div_eq_mul_inv, inv_inv, mul_comm]

theorem meas_matmul {α : Type*} [MeasurableSpace α] {f g : α → Formalism.QuantumDeterminants.Mt k r}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun p => (fun i j => (Matrix.of (f p) * Matrix.of (g p)) i j : Formalism.QuantumDeterminants.Mt k r)) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun l _ => ?_
  exact ((measurable_pi_apply l).comp ((measurable_pi_apply i).comp hf)).mul
    ((measurable_pi_apply j).comp ((measurable_pi_apply l).comp hg))

end Formalism.FourierDecayAlt.P.S3dx4
