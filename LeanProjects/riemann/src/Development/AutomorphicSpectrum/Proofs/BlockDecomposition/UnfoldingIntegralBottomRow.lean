import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap

namespace GlobalTheory.CompanionTheory.RankinUnfold

open Ad3 Ad3.R

def pp (k : Fin 4) (z : ℂ) : ℝ :=
  match k with
  | 0 => max z.re 0
  | 1 => max z.im 0
  | 2 => max (-z.re) 0
  | 3 => max (-z.im) 0

def uu (k : Fin 4) : ℂ := Complex.I ^ (k : ℕ)

theorem pp_nonneg (k : Fin 4) (z : ℂ) : 0 ≤ pp k z := by
  fin_cases k <;> simp [pp]

theorem continuous_pp (k : Fin 4) : Continuous (pp k) := by
  have h0 : Continuous fun z : ℂ => max z.re 0 := by fun_prop
  have h1 : Continuous fun z : ℂ => max z.im 0 := by fun_prop
  have h2 : Continuous fun z : ℂ => max (-z.re) 0 := by fun_prop
  have h3 : Continuous fun z : ℂ => max (-z.im) 0 := by fun_prop
  fin_cases k
  exacts [h0, h1, h2, h3]

theorem pp_le (k : Fin 4) (z : ℂ) : pp k z ≤ ‖z‖ := by
  have h1 := Complex.abs_re_le_norm z
  have h2 := Complex.abs_im_le_norm z
  have h3 := abs_le.1 h1
  have h4 := abs_le.1 h2
  have h5 := norm_nonneg z
  fin_cases k <;> simp only [pp] <;> simp <;> linarith

theorem sum_pp (z : ℂ) : ∑ k, uu k * (pp k z : ℂ) = z := by
  have h1 : max z.re 0 - max (-z.re) 0 = z.re := max_zero_sub_max_neg_zero_eq_self _
  have h2 : max z.im 0 - max (-z.im) 0 = z.im := max_zero_sub_max_neg_zero_eq_self _
  rw [Fin.sum_univ_four]
  apply Complex.ext
  · simp [uu, pp, pow_succ]
    linarith
  · simp [uu, pp, pow_succ]
    linarith

theorem ofReal_pp_le (k : Fin 4) (z : ℂ) : ENNReal.ofReal (pp k z) ≤ ‖z‖ₑ := by
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (pp_le k z)

theorem mul_eq_parts (z w : ℂ) (t : ℝ) :
    z * w * (t : ℂ) = ∑ k, ∑ j, uu k * uu j * ((pp k z * pp j w * t : ℝ) : ℂ) := by
  conv_lhs => rw [← sum_pp z, ← sum_pp w]
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

section Abstract

variable {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω)

theorem integrable_mul (a b : Ω → ℂ) (m : Ω → ℝ) (ha : Measurable a) (hb : Measurable b)
    (hm : Measurable m) (hm0 : ∀ ω, 0 ≤ m ω)
    (hfin : ∫⁻ ω, ‖a ω‖ₑ * ‖b ω‖ₑ * ENNReal.ofReal (m ω) ∂ρ < ∞) :
    Integrable (fun ω => a ω * b ω * (m ω : ℂ)) ρ := by
  refine ⟨((ha.mul hb).mul (Complex.measurable_ofReal.comp hm)).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (le_of_eq ?_) hfin
  refine lintegral_congr fun ω => ?_
  rw [enorm_mul, enorm_mul, ← ofReal_norm (m ω : ℂ), Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hm0 ω)]

theorem integral_mul_parts (a b : Ω → ℂ) (m : Ω → ℝ) (ha : Measurable a) (hb : Measurable b)
    (hm : Measurable m) (hm0 : ∀ ω, 0 ≤ m ω)
    (hfin : ∫⁻ ω, ‖a ω‖ₑ * ‖b ω‖ₑ * ENNReal.ofReal (m ω) ∂ρ < ∞) :
    ∫ ω, a ω * b ω * (m ω : ℂ) ∂ρ = ∑ k, ∑ j, uu k * uu j *
      (((∫⁻ ω, ENNReal.ofReal (pp k (a ω)) * ENNReal.ofReal (pp j (b ω)) *
        ENNReal.ofReal (m ω) ∂ρ).toReal : ℝ) : ℂ) := by
  have hmeas : ∀ k j, Measurable fun ω => pp k (a ω) * pp j (b ω) * m ω := fun k j =>
    (((continuous_pp k).measurable.comp ha).mul ((continuous_pp j).measurable.comp hb)).mul hm
  have hnn : ∀ k j ω, 0 ≤ pp k (a ω) * pp j (b ω) * m ω := fun k j ω =>
    mul_nonneg (mul_nonneg (pp_nonneg _ _) (pp_nonneg _ _)) (hm0 ω)
  have hof : ∀ k j ω, ENNReal.ofReal (pp k (a ω) * pp j (b ω) * m ω) =
      ENNReal.ofReal (pp k (a ω)) * ENNReal.ofReal (pp j (b ω)) * ENNReal.ofReal (m ω) := by
    intro k j ω
    rw [ENNReal.ofReal_mul (mul_nonneg (pp_nonneg _ _) (pp_nonneg _ _)),
      ENNReal.ofReal_mul (pp_nonneg _ _)]
  have hint : ∀ k j, Integrable (fun ω => pp k (a ω) * pp j (b ω) * m ω) ρ := by
    intro k j
    refine ⟨(hmeas k j).aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt (lintegral_mono fun ω => ?_) hfin
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hnn k j ω), hof]
    gcongr
    · exact ofReal_pp_le _ _
    · exact ofReal_pp_le _ _
  have hintC : ∀ k j, Integrable
      (fun ω => uu k * uu j * ((pp k (a ω) * pp j (b ω) * m ω : ℝ) : ℂ)) ρ :=
    fun k j => ((hint k j).ofReal).const_mul _
  have e : ∫ ω, a ω * b ω * (m ω : ℂ) ∂ρ = ∫ ω, ∑ k, ∑ j, uu k * uu j *
      ((pp k (a ω) * pp j (b ω) * m ω : ℝ) : ℂ) ∂ρ :=
    integral_congr_ae (Eventually.of_forall fun ω => mul_eq_parts _ _ _)
  rw [e, integral_finset_sum _ fun k _ => integrable_finset_sum _ fun j _ => hintC k j]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finset_sum _ fun j _ => hintC k j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_complex_ofReal,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (hnn k j))
      (hmeas k j).aestronglyMeasurable]
  simp_rw [hof]

theorem lintegral_mul_tsum {ι : Type*} [Countable ι] (h : Ω → ℝ≥0∞) (f : ι → Ω → ℝ≥0∞)
    (hh : Measurable h) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ g, h g * ∑' i, f i g ∂ρ = ∑' i, ∫⁻ g, h g * f i g ∂ρ := by
  simp_rw [← ENNReal.tsum_mul_left]
  exact lintegral_tsum fun i => (hh.mul (hf i)).aemeasurable

end Abstract

section Iter

variable {K Z A X : Type*} [MeasurableSpace K] [MeasurableSpace Z] [MeasurableSpace A]
  [MeasurableSpace X] (m₁ : Measure K) (m₂ : Measure Z) (m₃ : Measure A) (m₄ : Measure X)
  [SFinite m₁] [SFinite m₂] [SFinite m₃] [SFinite m₄]

theorem iter_lintegral (E : K × Z × A × X → ℝ≥0∞) (hE : Measurable E) :
    ∫⁻ p, E p ∂(m₁.prod (m₂.prod (m₃.prod m₄))) =
      ∫⁻ κ, ∫⁻ z, ∫⁻ a, ∫⁻ x, E (κ, z, a, x) ∂m₄ ∂m₃ ∂m₂ ∂m₁ := by
  rw [lintegral_prod _ hE.aemeasurable]
  refine lintegral_congr fun κ => ?_
  have h1 : Measurable fun q : Z × A × X => E (κ, q) := hE.comp measurable_prodMk_left
  rw [lintegral_prod _ h1.aemeasurable]
  refine lintegral_congr fun z => ?_
  have h2 : Measurable fun q : A × X => E (κ, z, q) := h1.comp measurable_prodMk_left
  rw [lintegral_prod _ h2.aemeasurable]

theorem iter_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : K × Z × A × X → E) (hf : Integrable f (m₁.prod (m₂.prod (m₃.prod m₄)))) :
    ∫ p, f p ∂(m₁.prod (m₂.prod (m₃.prod m₄))) =
      ∫ κ, ∫ z, ∫ a, ∫ x, f (κ, z, a, x) ∂m₄ ∂m₃ ∂m₂ ∂m₁ := by
  rw [integral_prod _ hf]
  refine integral_congr_ae ?_
  filter_upwards [hf.prod_right_ae] with κ h1
  rw [integral_prod _ h1]
  refine integral_congr_ae ?_
  filter_upwards [h1.prod_right_ae] with z h2
  rw [integral_prod _ h2]

end Iter

section Cont

theorem continuous_unipotentGL2 : Continuous (uni2 : 𝔸[ℚ] → G2) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun x : 𝔸[ℚ] => (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) 𝔸[ℚ])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun x : 𝔸[ℚ] => (!![1, -x; 0, 1] : Matrix (Fin 2) (Fin 2) 𝔸[ℚ])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_diagGL2 : Continuous fun p : Jd × Jd => (dg2 p.1 p.2 : G2) := by
  have hv : Continuous fun a : Jd => (a : 𝔸[ℚ]) := Units.continuous_val
  have hi : Continuous fun a : Jd => ((a⁻¹ : Jd) : 𝔸[ℚ]) := Units.continuous_val.comp continuous_inv
  have h1 : Continuous fun p : Jd × Jd => (p.1 : 𝔸[ℚ]) := hv.comp (by fun_prop)
  have h2 : Continuous fun p : Jd × Jd => (p.2 : 𝔸[ℚ]) := hv.comp (by fun_prop)
  have h3 : Continuous fun p : Jd × Jd => ((p.1⁻¹ : Jd) : 𝔸[ℚ]) := hi.comp (by fun_prop)
  have h4 : Continuous fun p : Jd × Jd => ((p.2⁻¹ : Jd) : 𝔸[ℚ]) := hi.comp (by fun_prop)
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun p : Jd × Jd => (!![(p.1 : 𝔸[ℚ]), 0; 0, (p.2 : 𝔸[ℚ])] : Matrix (Fin 2) (Fin 2) 𝔸[ℚ])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact h1 | exact h2
  · show Continuous fun p : Jd × Jd =>
      (!![((p.1⁻¹ : Jd) : 𝔸[ℚ]), 0; 0, ((p.2⁻¹ : Jd) : 𝔸[ℚ])] : Matrix (Fin 2) (Fin 2) 𝔸[ℚ])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact h3 | exact h4

theorem continuous_pt : Continuous fun p : KA × Jd × Jd × 𝔸[ℚ] => pt p.2.2.2 p.2.2.1 p.2.1 p.1.1 := by
  unfold pt
  have h1 : Continuous fun p : KA × Jd × Jd × 𝔸[ℚ] => (uni2 p.2.2.2 : G2) :=
    continuous_unipotentGL2.comp (by fun_prop)
  have h2 : Continuous fun p : KA × Jd × Jd × 𝔸[ℚ] => (dg2 p.2.2.1 1 : G2) :=
    continuous_diagGL2.comp (f := fun p : KA × Jd × Jd × 𝔸[ℚ] => (p.2.2.1, (1 : Jd))) (by fun_prop)
  have h3 : Continuous fun p : KA × Jd × Jd × 𝔸[ℚ] => (dg2 p.2.1 p.2.1 : G2) :=
    continuous_diagGL2.comp (f := fun p : KA × Jd × Jd × 𝔸[ℚ] => (p.2.1, p.2.1)) (by fun_prop)
  have h4 : Continuous fun p : KA × Jd × Jd × 𝔸[ℚ] => (p.1.1 : G2) :=
    continuous_subtype_val.comp continuous_fst
  exact ((h1.mul h2).mul h3).mul h4

theorem continuous_lrow : Continuous fun p : KA × Jd × Jd × 𝔸[ℚ] => lrow p.2.1 p.1.1 := by
  unfold lrow
  have hv : Continuous fun p : KA × Jd × Jd × 𝔸[ℚ] => ((p.2.1 : Jd) : 𝔸[ℚ]) :=
    Units.continuous_val.comp (by fun_prop)
  have h1 : Continuous fun p : KA × Jd × Jd × 𝔸[ℚ] => (![0, ((p.2.1 : Jd) : 𝔸[ℚ])] : Fin 2 → 𝔸[ℚ]) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · simpa using continuous_const
    · simpa using hv
  have h2 : Continuous fun p : KA × Jd × Jd × 𝔸[ℚ] =>
      (((p.1.1 : G2) : Matrix (Fin 2) (Fin 2) 𝔸[ℚ])) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)
  exact h1.matrix_vecMul h2

theorem continuous_row (ξ : Fin 2 → ℚ) : Continuous (Ad3.R.row ξ) := by
  unfold Ad3.R.row
  exact continuous_const.matrix_vecMul Units.continuous_val

theorem continuous_md : Continuous md :=
  continuous_subtype_val.comp IdeleGroup.continuous_ideleModule

end Cont

theorem complex_unfold_of_nonneg_unfold : Ad3.R.G2b → Ad3.R.G2c := by
  intro hb μ 𝓕 mK 𝓓 C h0 hC H Φ hH hL hΦ hfin
  haveI := h0.probK
  haveI : SecondCountableTopology KA := TopologicalSpace.Subtype.secondCountableTopology _
  set ρ : Measure (KA × Jd × Jd × 𝔸[ℚ]) := mK.prod ((ideleMeasure ℚ).prod
    (((ideleMeasure ℚ).restrict 𝓓).prod ((adeleMeasure ℚ).restrict (fundamentalSet ℚ)))) with hρ
  let p₁ : KA × Jd × Jd × 𝔸[ℚ] → G2 := fun ω => pt ω.2.2.2 ω.2.2.1 ω.2.1 ω.1.1
  let p₂ : KA × Jd × Jd × 𝔸[ℚ] → (Fin 2 → 𝔸[ℚ]) := fun ω => lrow ω.2.1 ω.1.1
  let m : KA × Jd × Jd × 𝔸[ℚ] → ℝ := fun ω => (md ω.2.2.1)⁻¹
  have hp₁ : Measurable p₁ := continuous_pt.measurable
  have hp₂ : Measurable p₂ := continuous_lrow.measurable
  have hm : Measurable m := (continuous_md.measurable.comp (by fun_prop)).inv
  have hm0 : ∀ ω, 0 ≤ m ω := fun ω => inv_nonneg.2 (IdeleGroup.ideleModule ℚ ω.2.2.1).2.le
  have hCne : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast hC.1

  have key : ∀ (H' : G2 → ℝ≥0∞) (Φ' : (Fin 2 → 𝔸[ℚ]) → ℝ≥0∞), Measurable H' → LInv H' →
      Measurable Φ' → ∫⁻ g in 𝓕, H' g * ∑' ξ : NZ, Φ' (Ad3.R.row ξ.1 g) ∂μ =
        C * ∫⁻ ω, H' (p₁ ω) * Φ' (p₂ ω) * ENNReal.ofReal (m ω) ∂ρ := by
    intro H' Φ' h1 h2 h3
    rw [hb μ 𝓕 mK 𝓓 C h0 hC H' Φ' h1 h2 h3, hρ, iter_lintegral]
    exact ((h1.comp hp₁).mul (h3.comp hp₂)).mul (ENNReal.measurable_ofReal.comp hm)
  have hrow : ∀ ξ : NZ, Measurable (Ad3.R.row ξ.1) := fun ξ => (continuous_row ξ.1).measurable

  have hfinρ : ∫⁻ ω, ‖H (p₁ ω)‖ₑ * ‖Φ (p₂ ω)‖ₑ * ENNReal.ofReal (m ω) ∂ρ < ∞ := by
    have h := key (fun g => ‖H g‖ₑ) (fun r => ‖Φ r‖ₑ) hH.enorm
      (fun γ g => by simp only [hL γ g]) hΦ.enorm
    rw [h] at hfin
    refine lt_top_iff_ne_top.2 fun hX => ?_
    rw [hX, ENNReal.mul_top hCne] at hfin
    exact lt_irrefl _ hfin
  have hRHS := iter_integral mK (ideleMeasure ℚ) ((ideleMeasure ℚ).restrict 𝓓)
    ((adeleMeasure ℚ).restrict (fundamentalSet ℚ)) (fun ω => H (p₁ ω) * Φ (p₂ ω) * (m ω : ℂ))
    (integrable_mul ρ _ _ m (hH.comp hp₁) (hΦ.comp hp₂) hm hm0 hfinρ)
  have hparts := integral_mul_parts ρ (fun ω => H (p₁ ω)) (fun ω => Φ (p₂ ω)) m (hH.comp hp₁)
    (hΦ.comp hp₂) hm hm0 hfinρ

  set L : Fin 4 → Fin 4 → NZ → ℝ≥0∞ := fun k j ξ => ∫⁻ g in 𝓕,
    ENNReal.ofReal (pp k (H g)) * ENNReal.ofReal (pp j (Φ (Ad3.R.row ξ.1 g))) ∂μ with hLdef
  have hPH : ∀ k, Measurable fun g => ENNReal.ofReal (pp k (H g)) := fun k =>
    ENNReal.measurable_ofReal.comp ((continuous_pp k).measurable.comp hH)
  have hPΦ : ∀ j, Measurable fun r => ENNReal.ofReal (pp j (Φ r)) := fun j =>
    ENNReal.measurable_ofReal.comp ((continuous_pp j).measurable.comp hΦ)
  have hAL : ∀ k j, ∫⁻ g in 𝓕, ENNReal.ofReal (pp k (H g)) *
      ∑' ξ : NZ, ENNReal.ofReal (pp j (Φ (Ad3.R.row ξ.1 g))) ∂μ = ∑' ξ, L k j ξ := fun k j =>
    lintegral_mul_tsum _ _ _ (hPH k) fun ξ => (hPΦ j).comp (hrow ξ)
  have hAfin : ∀ k j, ∑' ξ, L k j ξ ≠ ∞ := by
    intro k j
    rw [← hAL]
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun g => ?_) hfin)
    exact mul_le_mul' (ofReal_pp_le _ _) (ENNReal.tsum_le_tsum fun ξ => ofReal_pp_le _ _)
  have hnorm : ∑' ξ : NZ, ∫⁻ g in 𝓕, ‖H g‖ₑ * ‖Φ (Ad3.R.row ξ.1 g)‖ₑ ∂μ ≠ ∞ := by
    have h := lintegral_mul_tsum (μ.restrict 𝓕) (fun g => ‖H g‖ₑ)
      (fun (ξ : NZ) g => ‖Φ (Ad3.R.row ξ.1 g)‖ₑ) hH.enorm fun ξ => hΦ.enorm.comp (hrow ξ)
    rw [← h]
    exact hfin.ne
  have hξ : ∀ ξ : NZ, ∫ g in 𝓕, H g * Φ (Ad3.R.row ξ.1 g) ∂μ =
      ∑ k, ∑ j, uu k * uu j * (((L k j ξ).toReal : ℝ) : ℂ) := by
    intro ξ
    have hf : ∫⁻ g in 𝓕, ‖H g‖ₑ * ‖Φ (Ad3.R.row ξ.1 g)‖ₑ * ENNReal.ofReal 1 ∂μ < ∞ := by
      simp only [ENNReal.ofReal_one, mul_one]
      exact lt_of_le_of_lt (ENNReal.le_tsum ξ) (lt_top_iff_ne_top.2 hnorm)
    have h := integral_mul_parts (μ.restrict 𝓕) H (fun g => Φ (Ad3.R.row ξ.1 g)) (fun _ => 1) hH
      (hΦ.comp (hrow ξ)) measurable_const (fun _ => zero_le_one) hf
    simpa only [ENNReal.ofReal_one, mul_one, Complex.ofReal_one] using h
  have hsum : ∀ k j, HasSum (fun ξ => uu k * uu j * (((L k j ξ).toReal : ℝ) : ℂ))
      (uu k * uu j * (((∑' ξ, L k j ξ).toReal : ℝ) : ℂ)) := by
    intro k j
    refine HasSum.mul_left _ (Complex.hasSum_ofReal.2 ?_)
    rw [ENNReal.tsum_toReal_eq fun ξ => ENNReal.ne_top_of_tsum_ne_top (hAfin k j) ξ]
    exact (ENNReal.summable_toReal (hAfin k j)).hasSum
  have hLHS : ∫ g in 𝓕, H g * th Φ g ∂μ =
      ∑ k, ∑ j, uu k * uu j * (((∑' ξ, L k j ξ).toReal : ℝ) : ℂ) := by
    have e1 : ∫ g in 𝓕, H g * th Φ g ∂μ = ∫ g in 𝓕, ∑' ξ : NZ, H g * Φ (Ad3.R.row ξ.1 g) ∂μ :=
      integral_congr_ae (Eventually.of_forall fun g => by
        simp only [th, tsum_mul_left])
    rw [e1, integral_tsum (f := fun (ξ : NZ) g => H g * Φ (Ad3.R.row ξ.1 g))
      (fun ξ => (hH.mul (hΦ.comp (hrow ξ))).aestronglyMeasurable)]
    · simp_rw [hξ]
      exact (hasSum_sum fun k _ => hasSum_sum fun j _ => hsum k j).tsum_eq
    · simpa only [enorm_mul] using hnorm

  have hAB : ∀ k j, ∑' ξ, L k j ξ = C * ∫⁻ ω, ENNReal.ofReal (pp k (H (p₁ ω))) *
      ENNReal.ofReal (pp j (Φ (p₂ ω))) * ENNReal.ofReal (m ω) ∂ρ := by
    intro k j
    rw [← hAL]
    exact key _ _ (hPH k) (fun γ g => by simp only [hL γ g]) (hPΦ j)
  rw [hLHS]
  have hfinal : (∫ κ, ∫ z, ∫ a in 𝓓, ∫ x in fundamentalSet ℚ,
      H (pt x a z κ.1) * Φ (lrow z κ.1) * (((md a)⁻¹ : ℝ) : ℂ)
        ∂adeleMeasure ℚ ∂ideleMeasure ℚ ∂ideleMeasure ℚ ∂mK) =
      ∫ ω, H (p₁ ω) * Φ (p₂ ω) * (m ω : ℂ) ∂ρ := hRHS.symm
  rw [hfinal, hparts, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hAB, ENNReal.toReal_mul, ENNReal.coe_toReal]
  push_cast
  ring

end GlobalTheory.CompanionTheory.RankinUnfold

end
