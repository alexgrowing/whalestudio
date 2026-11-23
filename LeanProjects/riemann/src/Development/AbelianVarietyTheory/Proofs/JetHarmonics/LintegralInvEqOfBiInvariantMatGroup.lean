import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.PeriodIntegrals.QuotSetU
import Formalism.PeriodIntegrals.QuotInv
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.HaarInversion

def mulM {m : ℕ} (x y : PI.MtM m) : PI.MtM m := fun i j => (Matrix.of x * Matrix.of y) i j

noncomputable def invM {m : ℕ} (x : PI.MtM m) : PI.MtM m := fun i j => (Matrix.of x)⁻¹ i j

lemma of_mulM {m : ℕ} (x y : PI.MtM m) : Matrix.of (mulM x y) = Matrix.of x * Matrix.of y := rfl

lemma of_invM {m : ℕ} (x : PI.MtM m) : Matrix.of (invM x) = (Matrix.of x)⁻¹ := rfl

lemma measurable_mulM {m : ℕ} {α : Type*} [MeasurableSpace α] {u v : α → PI.MtM m}
    (hu : Measurable u) (hv : Measurable v) : Measurable fun a => mulM (u a) (v a) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [mulM, Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun k _ => Measurable.mul ?_ ?_
  · exact (measurable_pi_apply k).comp ((measurable_pi_apply i).comp hu)
  · exact (measurable_pi_apply j).comp ((measurable_pi_apply k).comp hv)

lemma measurable_invM {m : ℕ} : Measurable (invM : PI.MtM m → PI.MtM m) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  have hof : Continuous fun x : PI.MtM m => (Matrix.of x : Matrix (Fin m) (Fin m) ℂ) := continuous_id
  have h1 : Measurable fun x : PI.MtM m => (Matrix.of x).det := hof.matrix_det.measurable
  have h2 : Measurable fun x : PI.MtM m => (Matrix.of x).adjugate i j :=
    (hof.matrix_adjugate.matrix_elem i j).measurable
  simp only [invM, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact h1.inv.mul h2

theorem lintegral_inv_eq : ∀ (m : ℕ) (S : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (PI.MtM m)), PI.IsMatGroup S → PI.IsHaarOnM S μ → PI.IsRightInvM S μ → ∀ f : PI.MtM m → ℝ≥0∞, Measurable f → ∫⁻ s, f (fun i j => (Matrix.of s)⁻¹ i j) ∂μ = ∫⁻ s, f s ∂μ := by
  intro m S μ hS hμ hR f hf
  obtain ⟨hσ, hne, hc, hL⟩ := hμ
  obtain ⟨-, -, -, hinv⟩ := hS
  have hae : ∀ᵐ x ∂μ, Matrix.of x ∈ S := hc
  have left : ∀ a : PI.MtM m, Matrix.of a ∈ S → ∀ g : PI.MtM m → ℝ≥0∞, Measurable g →
      ∫⁻ y, g (mulM a y) ∂μ = ∫⁻ y, g y ∂μ := by
    intro a ha g hg
    have h := lintegral_map (μ := μ) hg (measurable_mulM (measurable_const (a := a)) measurable_id)
    have e : (fun y : PI.MtM m => mulM a (id y)) = PI.lmulQ (Matrix.of a) := rfl
    rw [e, hL _ ha] at h
    exact h.symm
  have right : ∀ a : PI.MtM m, Matrix.of a ∈ S → ∀ g : PI.MtM m → ℝ≥0∞, Measurable g →
      ∫⁻ y, g (mulM y a) ∂μ = ∫⁻ y, g y ∂μ := by
    intro a ha g hg
    have h := lintegral_map (μ := μ) hg (measurable_mulM measurable_id (measurable_const (a := a)))
    have e : (fun y : PI.MtM m => mulM (id y) a) = PI.rmulQ (Matrix.of a) := rfl
    rw [e, hR _ ha] at h
    exact h.symm
  obtain ⟨t, ht, -, ht0, ht1⟩ := Measure.exists_subset_measure_lt_top (μ := μ) (r := 0)
    MeasurableSet.univ (Measure.measure_univ_pos.mpr hne)
  set g : PI.MtM m → ℝ≥0∞ := t.indicator 1 with hgdef
  have hg : Measurable g := measurable_one.indicator ht
  have hgi : ∫⁻ y, g y ∂μ = μ t := lintegral_indicator_one ht
  have hfi : Measurable fun x => f (invM x) := hf.comp measurable_invM
  have key : (∫⁻ x, f (invM x) ∂μ) * μ t = (∫⁻ x, f x ∂μ) * μ t := by
    calc (∫⁻ x, f (invM x) ∂μ) * μ t
        = ∫⁻ x, ∫⁻ y, f (invM x) * g (mulM x y) ∂μ ∂μ := by
          rw [← lintegral_mul_const _ hfi]
          refine lintegral_congr_ae (hae.mono fun x hx => ?_)
          simp only
          have hm : Measurable fun y => g (mulM x y) :=
            hg.comp (measurable_mulM measurable_const measurable_id')
          rw [lintegral_const_mul _ hm, left x hx g hg, hgi]
      _ = ∫⁻ y, ∫⁻ x, f (invM x) * g (mulM x y) ∂μ ∂μ := by
          refine lintegral_lintegral_swap (Measurable.aemeasurable ?_)
          exact (hfi.comp measurable_fst).mul (hg.comp (measurable_mulM measurable_fst measurable_snd))
      _ = ∫⁻ y, ∫⁻ x, f (mulM y (invM x)) * g x ∂μ ∂μ := by
          refine lintegral_congr_ae (hae.mono fun y hy => ?_)
          simp only
          rw [← right y hy (fun x => f (mulM y (invM x)) * g x)
            ((hf.comp (measurable_mulM measurable_const measurable_invM)).mul hg)]
          refine lintegral_congr fun x => ?_
          congr 2
          apply Matrix.of.injective
          rw [of_mulM, of_invM, of_invM, of_mulM, Matrix.mul_inv_rev, ← Matrix.mul_assoc,
            (hinv _ hy).2, Matrix.one_mul]
      _ = ∫⁻ x, ∫⁻ y, f (mulM y (invM x)) * g x ∂μ ∂μ := by
          refine lintegral_lintegral_swap (Measurable.aemeasurable ?_)
          exact (hf.comp (measurable_mulM measurable_fst (measurable_invM.comp measurable_snd))).mul
            (hg.comp measurable_snd)
      _ = ∫⁻ x, (∫⁻ y, f y ∂μ) * g x ∂μ := by
          refine lintegral_congr_ae (hae.mono fun x hx => ?_)
          simp only
          have hm : Measurable fun y => f (mulM y (invM x)) :=
            hf.comp (measurable_mulM measurable_id' measurable_const)
          rw [lintegral_mul_const _ hm, right (invM x) (hinv _ hx).1 f hf]
      _ = (∫⁻ x, f x ∂μ) * μ t := by rw [lintegral_const_mul _ hg, hgi]
  exact (ENNReal.mul_left_inj ht0.ne' ht1.ne).mp key

end GlobalTheory.HaarInversion
