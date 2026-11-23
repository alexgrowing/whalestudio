import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMemMeasurableSet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem prod_ae {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) :
    ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  obtain ⟨hWs, -, hWc, -⟩ := hW
  obtain ⟨hNs, -, hNc, -⟩ := hN
  have := hWs; have := hNs
  rw [ae_iff]
  have hsub : {p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r |
      ¬ (Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r)} ⊆
      ({x | Matrix.of x ∉ Formalism.QuantumDeterminants.UWset k r z} ×ˢ Set.univ) ∪
        (Set.univ ×ˢ {x | Matrix.of x ∉ Formalism.QuantumDeterminants.Nset k r}) := by
    intro p hp
    by_cases h1 : Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z
    · exact Or.inr ⟨Set.mem_univ _, fun h2 => hp ⟨h1, h2⟩⟩
    · exact Or.inl ⟨h1, Set.mem_univ _⟩
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · rw [Measure.prod_prod, hWc, zero_mul]
  · rw [Measure.prod_prod, hNc, mul_zero]

theorem beInt_norm_le {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {σ : Mx k r → (H →L[ℂ] H)} (hds : PI.UpqRep.IsDSHpk k r ε lam σ)
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    {x v : H} {g : Mx k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r}
    (hp : Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r) :
    ‖beInt z c π σ (σ g x) v p‖ ≤ ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * g) x⟫_ℂ‖ := by
  have hhn : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    DDSmoothness.uh_mul hp.1.1 hp.2.1
  have hσ : σ (Matrix.of p.1 * Matrix.of p.2 * g) x = σ (Matrix.of p.1 * Matrix.of p.2) (σ g x) := by
    rw [sigma_mul' hds hhn hg]; rfl
  have hi := (MatrixMultiplicationContinuity.uw_inv hp.1).1
  have hπn : ‖π (Matrix.of p.1)⁻¹‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      (fun w => by rw [MatrixMultiplicationContinuity.piW_unitary hT hπ _ hi w, one_mul])
  have hψ : ‖star (Formalism.QuantumDeterminants.psi k r z c (Matrix.of p.2))‖ = 1 := by
    rw [norm_star]; unfold Formalism.QuantumDeterminants.psi; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  unfold beInt
  rw [norm_smul, norm_mul, hψ, mul_one, hσ]
  exact mul_le_of_le_one_right (norm_nonneg _) hπn

theorem be_enorm_le {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp]
    {σ : Mx k r → (H →L[ℂ] H)} (hds : PI.UpqRep.IsDSHpk k r ε lam σ)
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    {x v : H} {g : Mx k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ‖be z c π σ μW μN (σ g x) v‖ₑ ≤
      ∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * g) x⟫_ℂ‖ₑ ∂(μW.prod μN) := by
  unfold be
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
  filter_upwards [prod_ae hW hN] with p hp
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (beInt_norm_le hds hT hπ hg hp)

theorem l1_quotient_integral_bound {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mx k r → (H →L[ℂ] H)} (hds : PI.UpqRep.IsDSHpk k r ε lam σ)
    {z : Fin (2 * r + k + 1) → ℂ} {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (hGm : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG)
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG (muSof μW μN) νq)
    {x v : H} {C a : ℝ}
    (hC : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖⟪v, σ y x⟫_ℂ‖ ≤ C * B.gN y ^ (-a))
    (hI : Integrable (fun y : Formalism.QuantumDeterminants.Mt k r => B.gN (Matrix.of y) ^ (-a)) μG) :
    ∫⁻ g, (∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ ∂(μW.prod μN)) ∂νq < ⊤ := by
  obtain ⟨e, he, hee⟩ := coef_ext hds v x
  set U : Set (Formalism.QuantumDeterminants.Mt k r) := {y | Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} with hU
  set f : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := U.indicator (fun y => ‖e (Matrix.of y)‖ₑ) with hf
  have hfm : Measurable f := by
    have hc : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => e (Matrix.of y)) :=
      he.comp (show Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r)) from continuous_id)
    have : Measurable (fun y : Formalism.QuantumDeterminants.Mt k r => ‖e (Matrix.of y)‖ₑ) := hc.measurable.enorm
    exact this.indicator uh_mem_measurableSet
  have hφ : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) := by
    have h1 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.1 : Mx k r)) := continuous_fst
    have h2 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.2 : Mx k r)) := continuous_snd
    exact h1.matrix_mul h2
  have hmul : ∀ g : Formalism.QuantumDeterminants.Mt k r, Measurable (fun s : Formalism.QuantumDeterminants.Mt k r =>
      f (fun i j => (Matrix.of s * Matrix.of g) i j)) := by
    intro g
    have : Continuous (fun s : Formalism.QuantumDeterminants.Mt k r =>
        (fun i j => (Matrix.of s * Matrix.of g) i j : Formalism.QuantumDeterminants.Mt k r)) := by
      have h1 : Continuous (fun s : Formalism.QuantumDeterminants.Mt k r => (Matrix.of s : Mx k r)) := continuous_id
      exact h1.matrix_mul continuous_const
    exact hfm.comp this.measurable
  have hfacts := DDSmoothness.muSof_facts hW hN
  have hae := DDSmoothness.ae_UH_of_quot hGm.2.2.1 hfacts.1 hfacts.2 hq

  have step1 : ∀ᵐ g ∂νq, (∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ ∂(μW.prod μN)) =
      ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of g) i j) ∂(muSof μW μN) := by
    filter_upwards [hae] with g hg
    unfold muSof
    rw [lintegral_map (hmul g) hφ.measurable]
    apply lintegral_congr_ae
    filter_upwards [prod_ae hW hN] with p hp
    have hhn : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hp.1.1 hp.2.1
    have hin : Matrix.of p.1 * Matrix.of p.2 * Matrix.of g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
      DDSmoothness.uh_mul hhn hg
    have key : (fun i j => (Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) *
        Matrix.of g) i j : Formalism.QuantumDeterminants.Mt k r) ∈ U := hin
    show ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ =
      f (fun i j => (Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) * Matrix.of g) i j)
    rw [hf, Set.indicator_of_mem key]
    show _ = ‖e (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g)‖ₑ
    rw [hee _ hin]
  rw [lintegral_congr_ae step1, ← hq f hfm]

  have hb : ∀ᵐ y ∂μG, f y ≤ ‖C * B.gN (Matrix.of y) ^ (-a)‖ₑ := by
    have hGc : ∀ᵐ y ∂μG, Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
      rw [ae_iff]; simpa using hGm.2.2.1
    filter_upwards [hGc] with y hy
    simp only [hf]
    rw [Set.indicator_of_mem (show y ∈ U from hy), hee _ hy, ← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal ((hC _ hy).trans (le_abs_self _) |>.trans (le_of_eq (Real.norm_eq_abs _).symm))
  calc ∫⁻ y, f y ∂μG ≤ ∫⁻ y, ‖C * B.gN (Matrix.of y) ^ (-a)‖ₑ ∂μG := lintegral_mono_ae hb
    _ < ⊤ := (hI.const_mul C).hasFiniteIntegral

end Formalism.FourierDecayAlt.P.S3dx4
