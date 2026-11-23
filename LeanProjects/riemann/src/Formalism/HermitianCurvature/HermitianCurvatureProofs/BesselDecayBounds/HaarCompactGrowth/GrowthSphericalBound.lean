import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.IntegrableGNRpowOfLintegralLtTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.DecayZeroRight.NormDec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.UnitNorm.UnrealifyRealify

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.QuantumDeterminants

variable {k r : ℕ}

def haarCompactGrowthDensity (A : ℝ) (y : Mt k r) : ℝ≥0∞ := ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of y) ^ (-A))

theorem s3dx1S_gNc : Continuous (fun y : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of y)) := by
  unfold Formalism.FourierDecayAlt.B.gN
  simp only [Matrix.of_apply]
  refine Real.continuous_sqrt.comp ?_
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))

theorem s3dx1S_Fm (A : ℝ) : Measurable (haarCompactGrowthDensity (k := k) (r := r) A) := by
  unfold haarCompactGrowthDensity
  exact ENNReal.measurable_ofReal.comp ((s3dx1S_gNc (k := k) (r := r)).measurable.pow_const (-A))

theorem s3dx1S_mulc :
    Continuous (fun p : Mt k r × Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Mt k r)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  exact continuous_finset_sum _ fun l _ => by fun_prop

theorem s3dx1S_mulxc (x : Mt k r) :
    Continuous (fun s : Mt k r => (fun i j => (Matrix.of s * Matrix.of x) i j : Mt k r)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  exact continuous_finset_sum _ fun l _ => by fun_prop

theorem s3dx1S_lower {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Mt k r)} {A Rr : ℝ} (hA : 0 ≤ A)
    (hR : 0 < Rr) (hae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r)
    {x : Mt k r} (hx : Matrix.of x ∈ UH (Hpk k r)) (hxR : Formalism.FourierDecayAlt.B.gN (Matrix.of x) ≤ Rr) :
    ENNReal.ofReal (Rr ^ (-A)) *
        ∫⁻ p, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-A)) ∂(μW.prod μN) ≤
      ∫⁻ p, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x) ^ (-A))
        ∂(μW.prod μN) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae (hae.mono fun p hp => ?_)
  have hs : Matrix.of p.1 * Matrix.of p.2 ∈ UH (Hpk k r) := PI.WUN.UH_mul hp.1.1 hp.2.1
  have hsx : Matrix.of p.1 * Matrix.of p.2 * Matrix.of x ∈ UH (Hpk k r) := PI.WUN.UH_mul hs hx
  have h1 := ((Formalism.MainNotions.InverseNormDecayBounds.normInvP k r).1 _ hsx).2
  have hsub := (Formalism.MainNotions.InverseNormDecayBounds.normInvP k r).2 (Matrix.of p.1 * Matrix.of p.2) (Matrix.of x)
  have hs0 := gN_nonneg_bessel_integrability (Matrix.of p.1 * Matrix.of p.2)
  have hle : Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x) ≤
      Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) * Rr :=
    hsub.trans (mul_le_mul_of_nonneg_left hxR hs0)
  have hmono := Real.rpow_le_rpow_of_nonpos (by linarith) hle (by linarith : -A ≤ 0)
  rw [Real.mul_rpow hs0 hR.le] at hmono
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _)]
  exact ENNReal.ofReal_le_ofReal (by rw [mul_comm]; exact hmono)

theorem s3dx1S_quot_pos {z : Fin (2 * r + k + 1) → ℂ} {μW μN μG νq : Measure (Mt k r)}
    (hG : PI.BesselPeriodGGP.IsHaarOn (UH (Hpk k r)) μG)
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG (Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN) νq)
    (hae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r) :
    νq {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} ≠ 0 := by
  have hGsm : MeasurableSet {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} :=
    ((PI.WUN.isClosed_UH k r).preimage PI.WUN.continuous_of).measurableSet
  have hSnull : Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}ᶜ = 0 := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.muSof
    rw [Measure.map_apply s3dx1S_mulc.measurable hGsm.compl]
    exact ae_iff.1 (hae.mono fun p hp => PI.WUN.UH_mul hp.1.1 hp.2.1)
  intro h0
  have hnot : ∀ᵐ x ∂νq, x ∉ {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} := by
    rw [ae_iff]
    simp only [not_not]
    exact h0
  have hin : ∀ x ∉ {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)},
      (∫⁻ s, {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}.indicator 1
        (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN)) = 0 := by
    intro x hx
    refine le_antisymm ?_ (zero_le)
    calc _ ≤ ∫⁻ s, {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}ᶜ.indicator 1 s ∂(Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN) := by
          refine lintegral_mono fun s => ?_
          by_cases hs : s ∈ {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}
          · have hsx : (fun i j => (Matrix.of s * Matrix.of x) i j : Mt k r) ∉
                {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} := by
              intro hsx
              apply hx
              have hs' : Matrix.of s ∈ UH (Hpk k r) := hs
              have hsx' : Matrix.of s * Matrix.of x ∈ UH (Hpk k r) := hsx
              have hu : IsUnit (Matrix.of s).det := PI.WUN.UH_det hs'
              have e : Matrix.of x = (Matrix.of s)⁻¹ * (Matrix.of s * Matrix.of x) := by
                rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
              show Matrix.of x ∈ UH (Hpk k r)
              rw [e]
              exact PI.WUN.UH_mul (PI.WUN.UH_inv hs') hsx'
            rw [Set.indicator_of_notMem hsx]
            exact zero_le
          · rw [Set.indicator_of_mem (show s ∈ {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}ᶜ from hs)]
            exact Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => zero_le)
      _ = Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}ᶜ :=
          lintegral_indicator_one hGsm.compl
      _ = 0 := hSnull
  have hI := hq ({x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}.indicator 1) (measurable_one.indicator hGsm)
  rw [lintegral_indicator_one hGsm, lintegral_congr_ae (hnot.mono fun x hx => hin x hx), lintegral_zero] at hI
  have hc : μG {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}ᶜ = 0 := hG.2.2.1
  have hu := measure_univ_le_add_compl (μ := μG) {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)}
  rw [hI, hc, add_zero, nonpos_iff_eq_zero, Measure.measure_univ_eq_zero] at hu
  exact hG.2.1 hu

theorem growth_spherical_bound : Formalism.FourierDecayAlt.ThreeDimData.GrowthS := by
  intro k r z μW μN μG νq A hz hT hW hN hG hq hA
  have hA0 : 0 < A := lt_of_le_of_lt (by unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity) hA
  have : SigmaFinite μW := hW.1
  have : SigmaFinite μN := hN.1
  have hae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r := by
    have h1 : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z := by rw [ae_iff]; exact hW.2.2.1
    have h2 : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r := by rw [ae_iff]; exact hN.2.2.1
    exact (Measure.quasiMeasurePreserving_fst.ae h1).and (Measure.quasiMeasurePreserving_snd.ae h2)
  have hqG := s3dx1S_quot_pos hG hq hae
  obtain ⟨n, hn⟩ : ∃ n : ℕ,
      νq {x : Mt k r | Matrix.of x ∈ UH (Hpk k r) ∧ Formalism.FourierDecayAlt.B.gN (Matrix.of x) ≤ (n : ℝ) + 1} ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hqG
    have hU : {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} =
        ⋃ n : ℕ, {x : Mt k r | Matrix.of x ∈ UH (Hpk k r) ∧ Formalism.FourierDecayAlt.B.gN (Matrix.of x) ≤ (n : ℝ) + 1} := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_ge (Formalism.FourierDecayAlt.B.gN (Matrix.of x))
        exact ⟨n, hx, by linarith⟩
      · rintro ⟨n, hx, -⟩
        exact hx
    rw [hU]
    exact measure_iUnion_null hcon
  have hR0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hEm : MeasurableSet
      {x : Mt k r | Matrix.of x ∈ UH (Hpk k r) ∧ Formalism.FourierDecayAlt.B.gN (Matrix.of x) ≤ (n : ℝ) + 1} :=
    (((PI.WUN.isClosed_UH k r).preimage PI.WUN.continuous_of).measurableSet).inter
      (measurableSet_le (s3dx1S_gNc (k := k) (r := r)).measurable measurable_const)
  have hlow : ∀ x : Mt k r,
      {x : Mt k r | Matrix.of x ∈ UH (Hpk k r) ∧ Formalism.FourierDecayAlt.B.gN (Matrix.of x) ≤ (n : ℝ) + 1}.indicator
        (fun _ => ENNReal.ofReal (((n : ℝ) + 1) ^ (-A)) *
          ∫⁻ p, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-A)) ∂(μW.prod μN)) x ≤
        ∫⁻ s, haarCompactGrowthDensity A (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN) := by
    intro x
    by_cases hx : x ∈ {x : Mt k r | Matrix.of x ∈ UH (Hpk k r) ∧ Formalism.FourierDecayAlt.B.gN (Matrix.of x) ≤ (n : ℝ) + 1}
    · rw [Set.indicator_of_mem hx]
      have hf : Measurable (fun s : Mt k r => haarCompactGrowthDensity A (fun i j => (Matrix.of s * Matrix.of x) i j : Mt k r)) :=
        (s3dx1S_Fm A).comp (s3dx1S_mulxc x).measurable
      unfold Formalism.FourierDecayAlt.ThreeDimData.muSof
      rw [lintegral_map hf s3dx1S_mulc.measurable]
      exact s3dx1S_lower hA0.le hR0 hae hx.1 hx.2
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  have hGint := Formalism.FourierDecayAlt.P.growth_group_bound k r μG A hG hA
  have hT : ∫⁻ x, haarCompactGrowthDensity A x ∂μG < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x =>
      Real.rpow_nonneg (gN_nonneg_bessel_integrability _) _)).1 hGint.2
  have hchain : ENNReal.ofReal (((n : ℝ) + 1) ^ (-A)) *
      (∫⁻ p, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-A)) ∂(μW.prod μN)) *
      νq {x : Mt k r | Matrix.of x ∈ UH (Hpk k r) ∧ Formalism.FourierDecayAlt.B.gN (Matrix.of x) ≤ (n : ℝ) + 1} ≤
      ∫⁻ x, haarCompactGrowthDensity A x ∂μG := by
    rw [hq (haarCompactGrowthDensity A) (s3dx1S_Fm A), ← lintegral_indicator_const hEm]
    exact lintegral_mono hlow
  have hc0 : ENNReal.ofReal (((n : ℝ) + 1) ^ (-A)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hR0 _)).ne'
  have hI : (∫⁻ p, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-A)) ∂(μW.prod μN)) < ⊤ := by
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    have hlt := hchain.trans_lt hT
    rw [hc, ENNReal.mul_top hc0, ENNReal.top_mul hn] at hlt
    exact lt_irrefl _ hlt
  refine ⟨((s3dx1S_gNc.comp s3dx1S_mulc).measurable.pow_const (-A)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun p => Real.rpow_nonneg (gN_nonneg_bessel_integrability _) _)]
  exact hI

end Formalism.FourierDecayAlt.P
