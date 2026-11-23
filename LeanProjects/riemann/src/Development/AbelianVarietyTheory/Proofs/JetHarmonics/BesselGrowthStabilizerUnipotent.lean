import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HilbertSchmidtNormSubmulInvGeOneStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GrowthUnitaryGroupRpowNegIntegrableStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

namespace BesselGrowth

theorem continuous_hsNorm (k r : ℕ) :
    Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x : Mx k r)) := by
  unfold Formalism.FourierDecayAlt.B.gN
  refine Real.continuous_sqrt.comp ?_
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  refine Complex.continuous_normSq.comp ?_
  exact (continuous_apply j).comp (continuous_apply i)

theorem measurable_hsNorm_rpow (k r : ℕ) (A : ℝ) :
    Measurable (fun x : Formalism.QuantumDeterminants.Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x : Mx k r) ^ (-A)) :=
  (continuous_hsNorm k r).measurable.pow_const _

theorem hsNorm_nonneg {k r : ℕ} (g : Mx k r) : 0 ≤ Formalism.FourierDecayAlt.B.gN g := Real.sqrt_nonneg _

theorem growthS_of (hN : NormInv) (hG : GrowthG) : GrowthS := by
  intro k r z μW μN μG νq A _ _ hW hNn hGm hq hA
  obtain ⟨hS0, hS⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hNn
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hGm.2.2.1 hS0 hS hq
  have hA0 : 0 ≤ A := by
    have : 0 ≤ AG k r := by unfold AG; positivity
    linarith
  have hint := hG k r μG A hGm hA
  have hm := measurable_hsNorm_rpow k r A
  set F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of x : Mx k r) ^ (-A)) with hF
  have hFm : Measurable F := hm.ennreal_ofReal
  have hfin : ∫⁻ x, F x ∂μG < ⊤ := hint.lintegral_lt_top
  have hν : νq Set.univ ≠ 0 := by
    intro h0
    have h1 := hq (fun _ => 1) measurable_const
    rw [Measure.measure_univ_eq_zero.mp h0, lintegral_zero_measure, lintegral_one] at h1
    exact hGm.2.1 (Measure.measure_univ_eq_zero.mp h1)
  have hSfin : ∫⁻ s, F s ∂(muSof μW μN) < ⊤ := by
    by_contra hc
    have htop : ∫⁻ s, F s ∂(muSof μW μN) = ⊤ := top_le_iff.mp (not_lt.mp hc)
    have hle : ∫⁻ _x, (⊤ : ℝ≥0∞) ∂νq ≤
        ∫⁻ x, (∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(muSof μW μN)) ∂νq := by
      refine lintegral_mono_ae ?_
      filter_upwards [hae] with x hx
      have hx1 := ((hN k r).2 _ hx).2
      have hFx : F x ≠ 0 := by
        simp only [hF, ne_eq, ENNReal.ofReal_eq_zero, not_le]
        exact Real.rpow_pos_of_pos (by linarith) _
      have h2 : ∫⁻ s, F s * F x ∂(muSof μW μN) = ⊤ := by
        rw [lintegral_mul_const _ hFm, htop, ENNReal.top_mul hFx]
      rw [← h2]
      refine lintegral_mono_ae ?_
      filter_upwards [(ae_iff.mpr hS : ∀ᵐ s ∂(muSof μW μN),
        Matrix.of s ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))] with s hs
      have hsx := ((hN k r).2 _ (Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hs hx)).2
      simp only [hF]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (hsNorm_nonneg _) _),
        ← Real.mul_rpow (hsNorm_nonneg _) (hsNorm_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos hsx) ((hN k r).1 _ _) (by linarith)
    rw [← hq F hFm, lintegral_const, ENNReal.top_mul hν] at hle
    exact absurd hfin (not_lt.mpr hle)
  have hf : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) := by
    have h1 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.1 : Mx k r)) :=
      continuous_fst
    have h2 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.2 : Mx k r)) :=
      continuous_snd
    exact h1.matrix_mul h2
  have hI : Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x : Mx k r) ^ (-A))
      (muSof μW μN) :=
    ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hsNorm_nonneg _) _)).mpr hSfin⟩
  exact (integrable_map_measure hm.aestronglyMeasurable hf.measurable.aemeasurable).mp hI

end BesselGrowth

theorem besselGrowthS : Formalism.FourierDecayAlt.ThreeDimData.GrowthS :=
  BesselGrowth.growthS_of GlobalTheory.T.hilbertSchmidt_norm_submul_inv_ge_one GlobalTheory.T.growth_unitaryGroup_rpow_neg_integrable

end GlobalTheory
