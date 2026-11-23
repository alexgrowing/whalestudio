import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuadInner1

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem l_le_I {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
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
    {v : H} (hv : v ∈ DDsp σ w0) (hlv : l v ≠ 0) (hw0DD : w0 ∈ DDsp σ w0)
    {e1 : Mx k r → ℂ} (hee1 : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), e1 g = ⟪v, σ g w0⟫_ℂ)
    {zz : Formalism.QuantumDeterminants.Mt k r} (hz : Matrix.of zz ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ‖l (σ (Matrix.of zz) w0)‖ₑ ≤ (‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) *
      ∫⁻ p, (fun m : Formalism.QuantumDeterminants.Mt k r => ‖e1 (Matrix.of m)‖ₑ)
        (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of zz) i j) ∂(μW.prod μN) := by
  have b1 := l_enorm_le (c := c) hds hT hπ hW hN hbe hv hlv hw0DD hz
  refine b1.trans (le_of_eq ?_)
  congr 1
  apply lintegral_congr_ae
  filter_upwards [prod_ae hW hN] with p hp
  show ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of zz) w0⟫_ℂ‖ₑ =
    ‖e1 (Matrix.of p.1 * Matrix.of p.2 * Matrix.of zz)‖ₑ
  rw [hee1 _ (DDSmoothness.uh_mul (DDSmoothness.uh_mul hp.1.1 hp.2.1) hz)]

theorem e_weight {e : Mx k r → ℂ} {C a b : ℝ}
    (hb : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e y‖ ≤ C * B.gN y ^ (-a))
    {x : Mx k r} (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hpos : 0 < B.gN x) :
    ‖e x‖ₑ * ENNReal.ofReal (B.gN x ^ b) ≤ ENNReal.ofReal |C| * ‖B.gN x ^ (-(a - b))‖ₑ := by
  have h1 := hb x hx
  have h2 : ‖e x‖ * B.gN x ^ b ≤ |C| * B.gN x ^ (-(a - b)) := by
    have e2 : B.gN x ^ (-(a - b)) = B.gN x ^ (-a) * B.gN x ^ b := by
      rw [← Real.rpow_add hpos]
      ring_nf
    rw [e2, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hpos.le _)))
      (Real.rpow_nonneg hpos.le _)
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _),
    ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal h2

def Iint (A : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) (μ : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (z : Formalism.QuantumDeterminants.Mt k r) :
    ℝ≥0∞ :=
  ∫⁻ p, A (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of z) i j) ∂μ

def Aext (e : Mx k r → ℂ) (m : Formalism.QuantumDeterminants.Mt k r) : ℝ≥0∞ := ‖e (Matrix.of m)‖ₑ

theorem Aext_meas {e : Mx k r → ℂ} (he : Continuous e) : Measurable (Aext e) := by
  unfold Aext
  exact (Continuous.enorm (he.comp (show Continuous (fun m : Formalism.QuantumDeterminants.Mt k r => Matrix.of m) from continuous_id))).measurable

theorem Iint_meas {A : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hA : Measurable A)
    (μ : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) [SFinite μ] : Measurable (Iint A μ) := by
  unfold Iint
  refine Measurable.lintegral_prod_right' (f := fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
    A (fun i j => (Matrix.of q.2.1 * Matrix.of q.2.2 * Matrix.of q.1) i j)) ?_
  refine hA.comp (Continuous.measurable ?_)
  exact ((continuous_snd.fst.matrix_mul continuous_snd.snd).matrix_mul continuous_fst)

theorem unfold_Iint {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)} [SigmaFinite μW] [SigmaFinite μN]
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG (muSof μW μN) νq)
    {A Ψ : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hA : Measurable A) (hΨ : Measurable Ψ)
    (hinv : ∀ᵐ z ∂νq, ∀ᵐ p ∂(μW.prod μN),
      Ψ (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of z) i j) = Ψ z) :
    ∫⁻ z, Iint A (μW.prod μN) z * Ψ z ∂νq = ∫⁻ x, A x * Ψ x ∂μG := by
  have hcont : ∀ z : Formalism.QuantumDeterminants.Mt k r,
      Continuous (fun s : Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of s * Matrix.of z) i j : Formalism.QuantumDeterminants.Mt k r)) :=
    fun z => Continuous.matrix_mul continuous_id continuous_const
  have hg : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) :=
    (show Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) from
      Continuous.matrix_mul continuous_fst continuous_snd).measurable
  rw [hq (fun x => A x * Ψ x) (hA.mul hΨ)]
  refine lintegral_congr_ae ?_
  filter_upwards [hinv] with z hz
  unfold Iint Formalism.FourierDecayAlt.ThreeDimData.muSof
  rw [lintegral_map (f := fun s : Formalism.QuantumDeterminants.Mt k r => A (fun i j => (Matrix.of s * Matrix.of z) i j) *
      Ψ (fun i j => (Matrix.of s * Matrix.of z) i j))
    (by exact (hA.comp (hcont z).measurable).mul (hΨ.comp (hcont z).measurable)) hg]
  have hmA : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      A (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of z) i j)) :=
    hA.comp ((show Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of z) i j : Formalism.QuantumDeterminants.Mt k r)) from
      Continuous.matrix_mul (Continuous.matrix_mul continuous_fst continuous_snd) continuous_const).measurable)
  rw [← lintegral_mul_const _ hmA]
  refine lintegral_congr_ae ?_
  filter_upwards [hz] with p hp
  exact congrArg _ hp.symm

theorem pull2 {νq νq' : Measure (Formalism.QuantumDeterminants.Mt k r)} (F G : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞)
    (M : Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (hm : ∀ z, Measurable fun z' => G z' * M z z') :
    ∫⁻ z, ∫⁻ z', K * (F z * (G z' * M z z')) ∂νq' ∂νq = K * ∫⁻ z, F z * ∫⁻ z', G z' * M z z' ∂νq' ∂νq := by
  have h1 : ∀ z, ∫⁻ z', K * (F z * (G z' * M z z')) ∂νq' = K * (F z * ∫⁻ z', G z' * M z z' ∂νq') := by
    intro z
    have e1 : (fun z' => K * (F z * (G z' * M z z'))) = fun z' => (K * F z) * (G z' * M z z') := by
      funext z'
      ring
    rw [e1, lintegral_const_mul _ (hm z), mul_assoc]
  simp_rw [h1]
  exact lintegral_const_mul' K _ hK

theorem final2 {μG : Measure (Formalism.QuantumDeterminants.Mt k r)} (Fx : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) (hF : Measurable Fx)
    {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    ∫⁻ x, ∫⁻ y, c * (Fx x * Fx y) ∂μG ∂μG = c * ((∫⁻ x, Fx x ∂μG) * ∫⁻ y, Fx y ∂μG) := by
  have h1 : ∀ x, ∫⁻ y, c * (Fx x * Fx y) ∂μG = (c * Fx x) * ∫⁻ y, Fx y ∂μG := by
    intro x
    simp_rw [← mul_assoc]
    exact lintegral_const_mul _ hF
  simp_rw [h1]
  rw [lintegral_mul_const _ (hF.const_mul c), lintegral_const_mul _ hF, mul_assoc]

end Formalism.FourierDecayAlt.P.S3dx4
