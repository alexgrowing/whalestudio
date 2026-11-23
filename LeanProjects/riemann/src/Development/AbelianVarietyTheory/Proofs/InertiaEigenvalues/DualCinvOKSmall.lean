import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualIffLatticeVolumeAndPlancherelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedValuationParitySignCharacterKernelNormStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteNormedAlgebraEqModuleTopology
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem dual_cinvOK_small : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ V ∈ 𝓝 (0 : A.K),
    ∀ᶠ c in 𝓝[≠] (0 : F), {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} ⊆ V := by
  intro F E _ _ _ _ _ A ψ hψ V hV
  classical
  haveI : ContinuousSMul F A.K := IsModuleTopology.toContinuousSMul F A.K
  obtain ⟨-, -, hnd, -, -, -, -, -, -, hOpen, -, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have h0 : (0 : A.K) ∈ A.OK := by rw [← hR]; exact R.zero_mem
  let b := Module.finBasis F A.K
  let d := (Algebra.traceForm F A.K).dualBasis hnd b

  have hU : (⋂ i, {t : F | t • b i ∈ A.OK}) ∈ 𝓝 (0 : F) := by
    refine Filter.iInter_mem.2 fun i => ?_
    have hc : Continuous fun t : F => t • b i := continuous_id.smul continuous_const
    have : A.OK ∈ 𝓝 ((fun t : F => t • b i) 0) := by simpa using hOpen.mem_nhds h0
    exact hc.continuousAt this
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨x₀, hx₀, -⟩ := hψ.2
  have hx₀0 : x₀ ≠ 0 := by rintro rfl; exact hx₀ (AddChar.map_zero_eq_one ψ)

  have key : ∀ t : F, (∀ l : F, ‖l‖ < ε → ψ (l * t) = 1) → ‖t‖ ≤ ‖x₀‖ / ε := by
    intro t ht
    by_contra hlt
    push_neg at hlt
    have ht0 : t ≠ 0 := by
      rintro rfl; simp at hlt; linarith [div_pos (norm_pos_iff.2 hx₀0) hε]
    have hn : ‖x₀ / t‖ < ε := by
      rw [norm_div, div_lt_iff₀ (norm_pos_iff.2 ht0)]
      rw [div_lt_iff₀ hε] at hlt; linarith
    apply hx₀
    have := ht (x₀ / t) hn
    rwa [div_mul_cancel₀ x₀ ht0] at this
  set Rr := ‖x₀‖ / ε with hRr
  have hRr0 : 0 ≤ Rr := div_nonneg (norm_nonneg _) hε.le

  let g : (Fin (Module.finrank F A.K) → F) → A.K := fun t => ∑ i, t i • d i
  have hg : Continuous g := continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const
  have hg0 : g 0 = 0 := by simp [g]
  have hgV : g ⁻¹' V ∈ 𝓝 (0 : Fin (Module.finrank F A.K) → F) := by
    rw [← hg0] at hV; exact hg.continuousAt hV
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.1 hgV
  have hev : ∀ᶠ c in 𝓝 (0 : F), ‖c‖ * Rr < δ := by
    have : Tendsto (fun c : F => ‖c‖ * Rr) (𝓝 0) (𝓝 (‖(0:F)‖ * Rr)) :=
      (continuous_norm.mul continuous_const).tendsto 0
    simp only [norm_zero, zero_mul] at this
    exact this.eventually (gt_mem_nhds hδ)
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with c hc hc0
  intro y hy
  have hc0' : c ≠ 0 := hc0
  have hbound : ∀ i, ‖Algebra.trace F A.K (y * b i)‖ ≤ ‖c‖ * Rr := by
    intro i
    have h1 : ‖c⁻¹ * Algebra.trace F A.K (b i * y)‖ ≤ Rr := by
      apply key
      intro l hl
      have hmem : c • ((l * c⁻¹) • b i) ∈ A.OK := by
        rw [smul_smul, mul_comm l, ← mul_assoc, mul_inv_cancel₀ hc0', one_mul]
        have : l ∈ Metric.ball (0:F) ε := by simpa using hl
        simpa using Set.mem_iInter.1 (hεU this) i
      have := hy _ hmem
      simp only [Et.psiK, smul_mul_assoc, map_smul, smul_eq_mul] at this
      rw [← this]; congr 1; ring
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.2 hc0')] at h1
    rwa [mul_comm y]
  have hy' : y = g (fun i => Algebra.trace F A.K (y * b i)) := by
    simp only [g]
    conv_lhs => rw [← d.sum_repr y]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply]
    rfl
  rw [hy']
  apply hδV
  rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff hδ]
  intro i
  exact lt_of_le_of_lt (hbound i) hc

end GlobalTheory
