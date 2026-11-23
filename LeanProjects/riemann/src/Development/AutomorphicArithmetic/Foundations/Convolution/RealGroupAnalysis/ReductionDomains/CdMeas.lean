import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.cdMeas :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (t : (A F)ˣ), MeasurePreserving (cD t) M₀.μ M₀.μ := by
  intro F _ _ M₀ t
  haveI := M₀.haar
  haveI := M₀.right
  have hm : ∀ s : (A F)ˣ, Measurable (cD s : G1 F → G1 F) := fun s => (M.continuous_cD s).measurable
  let e : G1 F ≃ₜ* G1 F :=
    { toFun := cD t
      invFun := cD t⁻¹
      left_inv := fun g => by rw [M.cD_cD, inv_mul_cancel, M.cD_one]
      right_inv := fun g => by rw [M.cD_cD, mul_inv_cancel, M.cD_one]
      map_mul' := M.cD_mul t
      continuous_toFun := M.continuous_cD t
      continuous_invFun := M.continuous_cD t⁻¹ }
  haveI : (M₀.μ.map (cD t)).IsHaarMeasure := e.isHaarMeasure_map M₀.μ
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, M₀.μ.map (cD t) = c • M₀.μ :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul (M₀.μ.map (cD t)) M₀.μ⟩
  have h2 : M₀.μ.map (cD (t * t)) = M₀.μ := by
    have : (cD (t * t) : G1 F → G1 F) = (fun g => g * mD t) ∘ (fun g => (mD t)⁻¹ * g) := by
      funext g; exact M.cD_sq t g
    rw [this, ← Measure.map_map (measurable_mul_const _) (measurable_const_mul _),
      map_mul_left_eq_self, map_mul_right_eq_self]
  have h3 : M₀.μ.map (cD (t * t)) = (c * c) • M₀.μ := by
    have : (cD (t * t) : G1 F → G1 F) = cD t ∘ cD t := by
      funext g; exact (M.cD_cD t t g).symm
    rw [this, ← Measure.map_map (hm t) (hm t), hc, Measure.map_smul, hc, smul_smul]
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G1 F)
  have hpos : M₀.μ K ≠ 0 := (Measure.measure_pos_of_mem_nhds M₀.μ hK1).ne'
  have hfin : M₀.μ K ≠ ∞ := hK.measure_lt_top.ne
  have h4 : ((c * c : ℝ≥0) : ℝ≥0∞) * M₀.μ K = M₀.μ K := by
    have := congrArg (fun m : Measure (G1 F) => m K) (h3.symm.trans h2)
    simpa [ENNReal.smul_def] using this
  have h5 : ((c * c : ℝ≥0) : ℝ≥0∞) = 1 := by
    have h6 : ((c * c : ℝ≥0) : ℝ≥0∞) * M₀.μ K = 1 * M₀.μ K := by rw [h4, one_mul]
    exact (ENNReal.mul_left_inj hpos hfin).1 h6
  have h7 : c * c = 1 := by exact_mod_cast h5
  have h8 : c = 1 := by
    have := (mul_self_eq_one_iff (a := (c : ℝ))).1 (by exact_mod_cast h7)
    rcases this with h | h
    · exact_mod_cast h
    · have := c.coe_nonneg; linarith
  refine ⟨hm t, ?_⟩
  rw [hc, h8, one_smul]
