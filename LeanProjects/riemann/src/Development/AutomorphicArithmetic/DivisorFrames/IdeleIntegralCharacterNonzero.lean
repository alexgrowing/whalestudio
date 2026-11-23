import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocOpInfMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionMapsSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableIdelesPowerDecay
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBDefs
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open scoped Classical

section
open GlobalTheory.ArchIdeleDecay MeasureTheory.Measure
attribute [local instance] secondCountable_unitsC borel_unitsC

private noncomputable def UpperTheory.unitsIntegrand {ι : Type} [Fintype ι] (κ : ι → ℤ) (e : ℕ) (Φ : (ι → ℂ) → ℂ)
    (a : ι → ℂˣ) : ℂ :=
  ((∏ w, ((a w : ℂ) / (‖(a w : ℂ)‖ : ℂ)) ^ κ w) * ((∏ w, ‖(a w : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (e + 1)) *
    Φ (fun w => (a w : ℂ))

private theorem UpperTheory.measurable_unitsIntegrand {ι : Type} [Fintype ι] (κ : ι → ℤ) (e : ℕ) (Φ : (ι → ℂ) → ℂ)
    (hΦ : Continuous Φ) : Measurable (UpperTheory.unitsIntegrand κ e Φ) := by
  have h1 : ∀ w, Measurable fun a : ι → ℂˣ => (a w : ℂ) := fun w =>
    measurable_units_val.comp (measurable_pi_apply w)
  have h2 : ∀ w, Measurable fun a : ι → ℂˣ => (‖(a w : ℂ)‖ : ℂ) := fun w =>
    Complex.measurable_ofReal.comp (h1 w).norm
  unfold UpperTheory.unitsIntegrand
  refine Measurable.mul (Measurable.mul ?_ ?_) (hΦ.measurable.comp (measurable_pi_lambda _ h1))
  · exact Finset.measurable_prod _ fun w _ => ((h1 w).div (h2 w)).pow_const _
  · exact (Complex.measurable_ofReal.comp
      (Finset.measurable_prod _ fun w _ => (h1 w).norm.pow_const 2)).pow_const _

private theorem UpperTheory.integral_units_haar_eq_weight {ι : Type} [Fintype ι] (κ : ι → ℤ) (e : ℕ) (Φ : (ι → ℂ) → ℂ)
    (hΦ : Continuous Φ) :
    ∫ a, UpperTheory.unitsIntegrand κ e Φ a ∂(unitsHaar ι) = ∫ s, Φ s * FreeSingleHomotopyEquivDiscreteChains.UpperTheory.Dv.ConeB.wt κ e s := by
  have hw : ∀ b : ι → ℂ, (∀ i, b i ≠ 0) → invSqWt b = ENNReal.ofReal (∏ i, (‖b i‖ ^ 2)⁻¹) := by
    intro b hb
    have hx : ∀ i, 0 < ‖b i‖ := fun i => norm_pos_iff.2 (hb i)
    rw [invSqWt, ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_inv_of_pos (by have := hx i; positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
      ENNReal.inv_pow]
  rw [unitsHaar, integral_map measurable_toUnits.aemeasurable
    (UpperTheory.measurable_unitsIntegrand κ e Φ hΦ).aestronglyMeasurable, wVol,
    integral_withDensity_eq_integral_toReal_smul measurable_invSqWt
      (ae_ne_zero.mono fun b hb => by rw [hw b hb]; exact ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [ae_ne_zero] with b hb
  have hval : ∀ i, ((GlobalTheory.ArchIdeleDecay.toUnits b i : ℂˣ) : ℂ) = b i := fun i => by
    simp [GlobalTheory.ArchIdeleDecay.toUnits, hb i]
  rw [hw b hb, ENNReal.toReal_ofReal (by positivity)]
  simp only [UpperTheory.unitsIntegrand, hval, FreeSingleHomotopyEquivDiscreteChains.UpperTheory.Dv.ConeB.wt, Complex.real_smul]
  push_cast
  rw [← mul_assoc, mul_comm, ← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have h : (‖b i‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 (hb i)
  rw [pow_succ ((‖b i‖ : ℂ) ^ 2) e, ← pow_mul]
  field_simp

theorem UpperTheory.idele_integral_character_nonzero :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), IsCMExt F E σ → ∀ (μ : Measure (idelesAt E (evI F))), μ.IsHaarMeasure →
        ∀ (ν : Chr F E) (κ : InfinitePlace F → ℤ), HasExp B.emb ν κ → ∀ e : ℕ,
        ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ : (InfinitePlace F → ℂ) → ℂ, Continuous Φ →
          ∫ l : idelesAt E (evI F), ((ν l.1 : ℂ) * ((GlobalTheory.Doubling.absE F E l.1 : ℝ) : ℂ) ^ (e + 1)) * Φ (fun w => piInf (B.emb w) (l.1 : AE F E)) ∂μ =
            c * ∫ s, Φ s * FreeSingleHomotopyEquivDiscreteChains.UpperTheory.Dv.ConeB.wt κ e s := by
  intro F E _ _ _ _ _ σ B hcm μ hμ ν κ hν k
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evI F)
  obtain ⟨e, he⟩ := exists_archEquiv hcm B.emb
  haveI := e.isHaarMeasure_map μ
  have hsm := isMulLeftInvariant_eq_smul (unitsHaar (InfinitePlace F)) (μ.map e)
  set c := haarScalarFactor (unitsHaar (InfinitePlace F)) (μ.map e)
  have hc0 : c ≠ 0 := by
    intro h
    apply unitsHaar_ne_zero (ι := InfinitePlace F)
    rw [hsm, h, zero_smul]
  have hm : μ.map e = (c⁻¹ : NNReal) • unitsHaar (InfinitePlace F) := by
    rw [hsm, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  refine ⟨(((c⁻¹ : NNReal) : ℝ) : ℂ), by exact_mod_cast inv_ne_zero hc0, fun Φ hΦ => ?_⟩
  have hme : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have h1 := hme.integral_map (μ := μ) (UpperTheory.unitsIntegrand κ k Φ)
  rw [hm, integral_smul_nnreal_measure, UpperTheory.integral_units_haar_eq_weight κ k Φ hΦ] at h1
  rw [← Complex.real_smul, ← NNReal.smul_def, h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun l => ?_)
  simp only [UpperTheory.unitsIntegrand, he, absE_of_mem_arch hcm B.emb l.2]
  rw [hν l.1 l.2]

end
