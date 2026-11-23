import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight

set_option autoImplicit false

noncomputable section

open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.HSAmp

set_option autoImplicit false in
open Filter Topology MeasureTheory in
open scoped ComplexOrder Matrix in
private lemma ofReal_norm_sum_mul_sq_eq_double_sum_conj {ι : Type} [Fintype ι] (c w : ι → ℂ) :
    ((‖∑ i, c i * w i‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * (w i * (starRingEnd ℂ) (w j)) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  ring

set_option autoImplicit false in
open Filter Topology MeasureTheory in
open scoped ComplexOrder Matrix in

theorem _root_.GlobalTheory.HSAmp.gram_isHermitian_and_l2_eq_quadratic_form (S : Type) (Y : S → Type)
    [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι]
    [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ)
    (h : _root_.GlobalTheory.HSAmp.IsFam μ v) :
    (_root_.GlobalTheory.HSAmp.gram μ v).IsHermitian ∧ ∀ c : ι → ℂ,
      (∀ σ, Integrable (_root_.GlobalTheory.HSAmp.cmb v c σ) (μ σ)) ∧
      0 ≤ _root_.GlobalTheory.HSAmp.l2 μ v c ∧
      (_root_.GlobalTheory.HSAmp.l2 μ v c : ℂ) =
        ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * _root_.GlobalTheory.HSAmp.gram μ v i j := by
  haveI : Fintype S := @Fintype.ofFinite S h.finite
  have hint := h.integrable
  have hterm : ∀ (c : ι → ℂ) (σ : S), Integrable (fun y => ∑ i, ∑ j,
      c i * (starRingEnd ℂ) (c j) * (v σ y i * (starRingEnd ℂ) (v σ y j))) (μ σ) :=
    fun c σ => integrable_finset_sum _ fun i _ =>
      integrable_finset_sum _ fun j _ => (hint σ i j).const_mul _
  refine ⟨?_, fun c => ⟨fun σ => ?_, ?_, ?_⟩⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, _root_.GlobalTheory.HSAmp.gram, Matrix.of_apply,
      finsum_eq_sum_of_fintype]
    rw [star_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Complex.star_def, ← integral_conj]
    congr 1 with y
    simp [mul_comm]
  · refine (hterm c σ).re.congr (ae_of_all _ fun y => ?_)
    simp only [_root_.GlobalTheory.HSAmp.cmb]
    rw [← ofReal_norm_sum_mul_sq_eq_double_sum_conj c (v σ y)]
    exact Complex.ofReal_re _
  · unfold _root_.GlobalTheory.HSAmp.l2
    exact finsum_nonneg fun σ => integral_nonneg fun y => by
      simp only [_root_.GlobalTheory.HSAmp.cmb]
      positivity
  · unfold _root_.GlobalTheory.HSAmp.l2 _root_.GlobalTheory.HSAmp.gram
    simp only [Matrix.of_apply, finsum_eq_sum_of_fintype]
    have key : ∀ σ, ((∫ y, _root_.GlobalTheory.HSAmp.cmb v c σ y ∂μ σ : ℝ) : ℂ) =
        ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * ∫ y, v σ y i * (starRingEnd ℂ) (v σ y j) ∂μ σ := by
      intro σ
      simp only [_root_.GlobalTheory.HSAmp.cmb]
      rw [← integral_complex_ofReal,
        integral_congr_ae (ae_of_all _ fun y => ofReal_norm_sum_mul_sq_eq_double_sum_conj c (v σ y)),
        integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
          (hint σ i j).const_mul _]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finset_sum _ fun j _ => (hint σ i j).const_mul _]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul]
    rw [Complex.ofReal_sum]
    simp only [key, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

end GlobalTheory.HSAmp
