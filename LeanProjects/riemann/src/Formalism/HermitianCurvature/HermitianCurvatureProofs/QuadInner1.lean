import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormTwoSidedTranslateGrowthBound

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem hphi_meas : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
    (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) :=
  meas_hn measurable_id

theorem quad_inner {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hds : PI.UpqRep.IsDSHpk k r ε lam σ) (w0 : H) {e0 : Mx k r → ℂ} (he0 : Continuous e0)
    (hee0 : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), e0 g = ⟪w0, σ g w0⟫_ℂ)
    {γ : Mx k r} (hγ : γ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {μW μN μW' : Measure (Formalism.QuantumDeterminants.Mt k r)} [SigmaFinite μW] [SigmaFinite μN] [SigmaFinite μW']
    (hS1 : muSof μW μN {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0)
    (hS2 : muSof μW' μN {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0)
    {zz zz' : Formalism.QuantumDeterminants.Mt k r} (hz : Matrix.of zz ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hz' : Matrix.of zz' ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ∫⁻ s, ∫⁻ s', ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s * γ * (Matrix.of s')⁻¹) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ
      ∂(muSof μW' μN) ∂(muSof μW μN) = abelian₂ e0 γ (μW.prod μN) (μW'.prod μN) zz zz' := by
  have hae1 : ∀ᵐ s ∂(muSof μW μN), Matrix.of s ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    rw [ae_iff]; simpa using hS1
  have hae2 : ∀ᵐ s ∂(muSof μW' μN), Matrix.of s ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    rw [ae_iff]; simpa using hS2
  have hJ : Measurable (fun t : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of t.1 * γ * (Matrix.of t.2)⁻¹ * Matrix.of zz')‖ₑ) := by
    have mγ : Measurable (fun _ : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of.symm γ : Formalism.QuantumDeterminants.Mt k r)) :=
      measurable_const
    exact measurable_enorm_composition he0 (meas_matmul (meas_matmul (meas_matmul (meas_matmul (meas_inv (meas_const_mt zz))
      measurable_fst) mγ) (meas_inv measurable_snd)) (meas_const_mt zz'))
  calc ∫⁻ s, ∫⁻ s', ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s * γ * (Matrix.of s')⁻¹) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ
        ∂(muSof μW' μN) ∂(muSof μW μN)
      = ∫⁻ s, ∫⁻ s', ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of s * γ * (Matrix.of s')⁻¹ * Matrix.of zz')‖ₑ
          ∂(muSof μW' μN) ∂(muSof μW μN) := by
        apply lintegral_congr_ae
        filter_upwards [hae1] with s hs
        apply lintegral_congr_ae
        filter_upwards [hae2] with s' hs'
        have hY : Matrix.of s * γ * (Matrix.of s')⁻¹ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
          DDSmoothness.uh_mul (DDSmoothness.uh_mul hs hγ) (MatrixMultiplicationContinuity.uh_inv hs').1
        have hM : (Matrix.of zz)⁻¹ * (Matrix.of s * γ * (Matrix.of s')⁻¹) * Matrix.of zz' ∈
            Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
          DDSmoothness.uh_mul (DDSmoothness.uh_mul (MatrixMultiplicationContinuity.uh_inv hz).1 hY) hz'
        rw [coef_eq hds hz hY hz', ← hee0 _ hM]
        simp only [Matrix.mul_assoc]
    _ = ∫⁻ p, ∫⁻ q, ‖e0 ((Matrix.of zz)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ *
          (Matrix.of q.1 * Matrix.of q.2)⁻¹ * Matrix.of zz')‖ₑ ∂(μW'.prod μN) ∂(μW.prod μN) := by
        unfold muSof
        rw [lintegral_map (hJ.lintegral_prod_right' (ν := (μW'.prod μN).map
          (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j :
            Formalism.QuantumDeterminants.Mt k r)))) hphi_meas]
        apply lintegral_congr
        intro p
        have hK : Measurable (fun y : Formalism.QuantumDeterminants.Mt k r =>
            ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r) *
              γ * (Matrix.of y)⁻¹ * Matrix.of zz')‖ₑ) := by
          have mc : Measurable (fun _ : Formalism.QuantumDeterminants.Mt k r => (fun i j => ((Matrix.of zz)⁻¹ *
              Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r) * γ) i j :
                Formalism.QuantumDeterminants.Mt k r)) := measurable_const
          exact measurable_enorm_composition he0 (meas_matmul (meas_matmul mc (meas_inv measurable_id)) (meas_const_mt zz'))
        show ∫⁻ y, ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j :
            Formalism.QuantumDeterminants.Mt k r) * γ * (Matrix.of y)⁻¹ * Matrix.of zz')‖ₑ ∂((μW'.prod μN).map
              (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
                (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r))) = _
        rw [lintegral_map hK hphi_meas]
        rfl
    _ = abelian₂ e0 γ (μW.prod μN) (μW'.prod μN) zz zz' := rfl

theorem quad_inner1 {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hds : PI.UpqRep.IsDSHpk k r ε lam σ) (w0 : H) {e0 : Mx k r → ℂ} (he0 : Continuous e0)
    (hee0 : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), e0 g = ⟪w0, σ g w0⟫_ℂ)
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} [SigmaFinite μW] [SigmaFinite μN]
    (hS1 : muSof μW μN {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0)
    {zz zz' : Formalism.QuantumDeterminants.Mt k r} (hz : Matrix.of zz ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hz' : Matrix.of zz' ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ∫⁻ s, ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ ∂(muSof μW μN) =
      Lam1 e0 (μW.prod μN) zz zz' := by
  have hae1 : ∀ᵐ s ∂(muSof μW μN), Matrix.of s ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    rw [ae_iff]; simpa using hS1
  have hJ : Measurable (fun t : Formalism.QuantumDeterminants.Mt k r =>
      ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of t * Matrix.of zz')‖ₑ) :=
    measurable_enorm_composition he0 (meas_matmul (meas_matmul (meas_inv (meas_const_mt zz)) measurable_id) (meas_const_mt zz'))
  calc ∫⁻ s, ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ ∂(muSof μW μN)
      = ∫⁻ s, ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of s * Matrix.of zz')‖ₑ ∂(muSof μW μN) := by
        apply lintegral_congr_ae
        filter_upwards [hae1] with s hs
        have hM : (Matrix.of zz)⁻¹ * Matrix.of s * Matrix.of zz' ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
          DDSmoothness.uh_mul (DDSmoothness.uh_mul (MatrixMultiplicationContinuity.uh_inv hz).1 hs) hz'
        rw [coef_eq hds hz hs hz', ← hee0 _ hM]
    _ = Lam1 e0 (μW.prod μN) zz zz' := by
        unfold muSof Lam1
        rw [lintegral_map hJ hphi_meas]
        rfl

end Formalism.FourierDecayAlt.P.S3dx4
