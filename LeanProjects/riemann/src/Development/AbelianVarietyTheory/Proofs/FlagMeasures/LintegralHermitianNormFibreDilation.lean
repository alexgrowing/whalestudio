import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CdScaleIsTrueScale
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousGaussSp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFibreFamilyEqAtContinuityPoint

noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
open scoped ENNReal NNReal

namespace GlobalTheory.FibreScaling

variable {P Q : ℕ}

theorem qf_continuous : Continuous (qf : Sp P Q → ℝ) := by
  unfold qf
  fun_prop

theorem qf_real_smul (r : ℝ) (x : Sp P Q) : qf (r • x) = r ^ 2 * qf x := by
  simp only [qf, Pi.smul_apply, Complex.real_smul, map_mul, Complex.normSq_ofReal, mul_sub,
    Finset.mul_sum, sq]

theorem finrank_sp : Module.finrank ℝ (Sp P Q) = 2 * (P + Q) := by
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]

theorem map_dx_smul {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ (P + Q)) • (dx P Q).map (fun y => Real.sqrt t • y) = dx P Q := by
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  have h := Measure.map_addHaar_smul (volume : Measure (Sp P Q)) hs
  rw [finrank_sp, pow_mul, Real.sq_sqrt ht.le, abs_of_pos (by positivity)] at h
  rw [dx, Measure.map_smul, h, smul_comm, smul_smul (ENNReal.ofReal _),
    ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one,
    one_smul]

theorem lintegral_inv_mul {t : ℝ} (ht : 0 < t) (g : ℝ → ℝ≥0∞) :
    ∫⁻ b, g (t⁻¹ * b) = ENNReal.ofReal t * ∫⁻ b, g b := by
  have h := (Homeomorph.mulLeft₀ t⁻¹ (inv_ne_zero ht.ne')).measurableEmbedding.lintegral_map
    (μ := volume) g
  rw [Homeomorph.coe_mulLeft₀, Real.map_volume_mul_left (inv_ne_zero ht.ne'), inv_inv,
    abs_of_pos ht, lintegral_smul_measure, smul_eq_mul] at h
  exact h.symm

theorem isDxDq_scale {fib : ℝ → Measure (Sp P Q)} (h : IsDxDq fib) {t : ℝ} (ht : 0 < t) :
    IsDxDq fun b => ENNReal.ofReal (t ^ (P + Q) / t) •
      (fib (t⁻¹ * b)).map (fun y => Real.sqrt t • y) := by
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  have hc : Continuous (fun y : Sp P Q => Real.sqrt t • y) := continuous_const_smul _
  have hm := hc.measurable
  have hpre : (fun y : Sp P Q => Real.sqrt t • y) ⁻¹' {x : Sp P Q | x ≠ 0} = {x | x ≠ 0} :=
    Set.ext fun x => by simp [hs]
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφ hsu hts => ?_⟩
  · have hS : MeasurableSet (qf ⁻¹' {id b} ∩ {x : Sp P Q | x ≠ 0})ᶜ :=
      ((qf_continuous.measurable (measurableSet_singleton _)).inter isOpen_ne.measurableSet).compl
    have h0 : ((fib (t⁻¹ * b)).map (fun y => Real.sqrt t • y))
        (qf ⁻¹' {id b} ∩ {x : Sp P Q | x ≠ 0})ᶜ = 0 := by
      rw [Measure.map_apply hm hS]
      convert h.1 (t⁻¹ * b) using 2
      rw [Set.preimage_compl, Set.preimage_inter, hpre]
      congr 2
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, id, qf_real_smul, Real.sq_sqrt ht.le]
      exact (eq_inv_mul_iff_mul_eq₀ ht.ne').symm
    rw [Measure.smul_apply, h0, smul_zero]
  · simp only [lintegral_smul_measure, lintegral_map hφ hm, smul_eq_mul]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_inv_mul ht fun b => ∫⁻ y, φ (Real.sqrt t • y) ∂(fib b),
      ← h.2.1 (fun x => φ (Real.sqrt t • x)) (hφ.comp hm), ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ ht.ne']
    conv_lhs => rw [← map_dx_smul ht]
    rw [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
      Measure.restrict_map hm isOpen_ne.measurableSet, lintegral_map hφ hm, hpre]
  · have hs' : HasCompactSupport (φ ∘ fun y : Sp P Q => Real.sqrt t • y) :=
      hsu.comp_homeomorph (Homeomorph.smulOfNeZero (Real.sqrt t) hs)
    have ht' : tsupport (φ ∘ fun y : Sp P Q => Real.sqrt t • y) ⊆ {x | x ≠ 0} := by
      rw [← hpre]
      exact (tsupport_comp_subset_preimage φ hc).trans (Set.preimage_mono hts)
    obtain ⟨h1, h2⟩ := h.2.2 _ (hφ.comp hc) hs' ht'
    refine ⟨fun b _ => ?_, ?_⟩
    · exact ((integrable_map_measure hφ.aestronglyMeasurable hm.aemeasurable).2
        (h1 _ trivial)).smul_measure ENNReal.ofReal_ne_top
    · simp only [integral_smul_measure, integral_map hm.aemeasurable hφ.aestronglyMeasurable]
      exact (((continuousOn_univ.1 h2).comp (continuous_const_mul t⁻¹)).const_smul
        (ENNReal.ofReal (t ^ (P + Q) / t)).toReal).continuousOn

theorem lintegral_fibre_scale : ∀ (P Q : ℕ) (fib : ℝ → Measure (Sp P Q)) (β t : ℝ), IsDxDq fib →
    β ≠ 0 → 0 < t → ∀ φ : Sp P Q → ℝ≥0∞, Measurable φ →
      ∫⁻ y, φ y ∂(fib (t * β)) =
        ENNReal.ofReal (t ^ (P + Q) / t) * ∫⁻ y, φ (Real.sqrt t • y) ∂(fib β) := by
  intro P Q fib β t h hβ ht φ hφ
  have hO : (qf : Sp P Q → ℝ) ⁻¹' {t * β} ⊆ {x | x ≠ 0} := by
    rintro x hx rfl
    exact mul_ne_zero ht.ne' hβ (by simpa [qf] using hx.symm)
  have e := GlobalTheory.IsFibreFamily_eq_at (dx P Q) qf {x | x ≠ 0} {x | x ≠ 0} {x | x ≠ 0} Set.univ
    Set.univ fib _ (t * β) qf_continuous.measurable isOpen_ne subset_rfl subset_rfl hO isOpen_univ
    isOpen_univ trivial trivial h (isDxDq_scale h ht)
  rw [e, lintegral_smul_measure, smul_eq_mul, inv_mul_cancel_left₀ ht.ne',
    lintegral_map hφ (continuous_const_smul _).measurable]

end GlobalTheory.FibreScaling
