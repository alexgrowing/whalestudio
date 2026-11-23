import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormWt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
open NumberField MeasureTheory

noncomputable section

namespace GlobalTheory.HeckeTheta.Decay

open GlobalTheory.HeckeTheta

theorem pow_mul_exp_le (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ k * Real.exp (-2 * Real.pi * x ^ 2) ≤ (1 + (k.factorial : ℝ)) * Real.exp (-Real.pi * x ^ 2) := by
  have h1 : x ^ k ≤ 1 + (x ^ 2) ^ k := by
    rcases le_total x 1 with h | h
    · have := pow_le_one₀ (n := k) hx h
      have := pow_nonneg (sq_nonneg x) k
      linarith
    · have h' : x ^ k ≤ x ^ (2 * k) := pow_le_pow_right₀ h (by omega)
      rw [pow_mul] at h'
      linarith
  have h2 : (x ^ 2) ^ k ≤ (k.factorial : ℝ) * Real.exp (x ^ 2) := by
    have := Real.pow_div_factorial_le_exp (x ^ 2) (sq_nonneg x) k
    have hf : (0:ℝ) < k.factorial := by positivity
    rwa [div_le_iff₀ hf, mul_comm] at this
  have he := Real.exp_pos (-2 * Real.pi * x ^ 2)
  have h3 : Real.exp (x ^ 2) * Real.exp (-2 * Real.pi * x ^ 2) ≤ Real.exp (-Real.pi * x ^ 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three, sq_nonneg x])
  have h4 : Real.exp (-2 * Real.pi * x ^ 2) ≤ Real.exp (-Real.pi * x ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, sq_nonneg x])
  have hf0 : (0:ℝ) ≤ k.factorial := by positivity
  calc x ^ k * Real.exp (-2 * Real.pi * x ^ 2)
      ≤ (1 + (x ^ 2) ^ k) * Real.exp (-2 * Real.pi * x ^ 2) := mul_le_mul_of_nonneg_right h1 he.le
    _ = Real.exp (-2 * Real.pi * x ^ 2) + (x ^ 2) ^ k * Real.exp (-2 * Real.pi * x ^ 2) := by ring
    _ ≤ Real.exp (-Real.pi * x ^ 2) + (k.factorial : ℝ) * (Real.exp (x ^ 2) * Real.exp (-2 * Real.pi * x ^ 2)) := by
        have : (x ^ 2) ^ k * Real.exp (-2 * Real.pi * x ^ 2)
            ≤ ((k.factorial : ℝ) * Real.exp (x ^ 2)) * Real.exp (-2 * Real.pi * x ^ 2) :=
          mul_le_mul_of_nonneg_right h2 he.le
        linarith
    _ ≤ Real.exp (-Real.pi * x ^ 2) + (k.factorial : ℝ) * Real.exp (-Real.pi * x ^ 2) := by
        have := mul_le_mul_of_nonneg_left h3 hf0
        linarith
    _ = _ := by ring

variable {I : Type} [Fintype I]

def gC (n : I → ℤ) : ℝ := ∏ i, (1 + ((n i).natAbs.factorial : ℝ))

theorem gC_nonneg (n : I → ℤ) : 0 ≤ gC n := Finset.prod_nonneg fun i _ => by positivity

theorem norm_gauss_le (n : I → ℤ) (w : I → ℂ) :
    ‖gauss n w‖ ≤ gC n * Real.exp (-Real.pi * ∑ i, ‖w i‖ ^ 2) := by
  unfold gauss gC
  rw [norm_prod, Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
  intro i _
  rw [norm_mul, norm_hmon, Complex.norm_exp_ofReal]
  have := pow_mul_exp_le (n i).natAbs (norm_nonneg (w i))
  convert this using 2

theorem norm_dil_sq (y : I → ℝ) (v : I → ℂ) (i : I) :
    ‖dil y v i‖ ^ 2 = Real.exp (y i) * ‖v i‖ ^ 2 := by
  unfold dil
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
  have : Real.exp (y i / 2) ^ 2 = Real.exp (y i) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [this]

theorem sum_ge (y : I → ℝ) (v : I → ℂ) {τ : ℝ} (hτ : 0 ≤ τ) (hy : ∀ i, τ ≤ Real.exp (y i)) :
    τ * ‖v‖ ^ 2 ≤ ∑ i, Real.exp (y i) * ‖v i‖ ^ 2 := by
  have hv : ‖v‖ ^ 2 ≤ ∑ i, ‖v i‖ ^ 2 := by
    have : ‖v‖ ≤ Real.sqrt (∑ i, ‖v i‖ ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
      refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
      exact Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)
    calc ‖v‖ ^ 2 ≤ (Real.sqrt (∑ i, ‖v i‖ ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = _ := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  calc τ * ‖v‖ ^ 2 ≤ τ * ∑ i, ‖v i‖ ^ 2 := mul_le_mul_of_nonneg_left hv hτ
    _ = ∑ i, τ * ‖v i‖ ^ 2 := Finset.mul_sum _ _ _
    _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hy i) (sq_nonneg _)

theorem norm_term_le (n : I → ℤ) (y : I → ℝ) (v : I → ℂ) {τ : ℝ} (hτ : 0 ≤ τ)
    (hy : ∀ i, τ ≤ Real.exp (y i)) :
    ‖gauss n (dil y v)‖ ≤ gC n * Real.exp (-Real.pi * τ * ‖v‖ ^ 2) := by
  refine (norm_gauss_le n _).trans ?_
  apply mul_le_mul_of_nonneg_left _ (gC_nonneg n)
  apply Real.exp_le_exp.mpr
  simp_rw [norm_dil_sq]
  have := mul_le_mul_of_nonneg_left (sum_ge y v hτ hy) Real.pi_pos.le
  linarith

theorem continuous_hmon (m : ℤ) : Continuous (hmon m) := by
  unfold hmon; split_ifs <;> fun_prop

theorem continuous_theta {ι : Type} (e : ι → I → ℂ) (a : ι → ℂ) (n : I → ℤ)
    (ha : ∀ ε : ℝ, 0 < ε → Summable (fun j => ‖a j‖ * Real.exp (-ε * ‖e j‖ ^ 2))) :
    Continuous (theta e a n) := by
  rw [continuous_iff_continuousAt]
  intro y0
  obtain ⟨L, hL⟩ : ∃ L : ℝ, ∀ i, -L < y0 i := ⟨∑ i, |y0 i| + 1, fun i => by
      have := Finset.single_le_sum (f := fun i => |y0 i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
      have := neg_abs_le (y0 i)
      linarith⟩
  let U : Set (I → ℝ) := {y | ∀ i, -L < y i}
  have hU : IsOpen U := by
    simp only [U, Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  have hc : ContinuousOn (theta e a n) U := by
    unfold theta
    refine continuousOn_tsum
      (u := fun j => gC n * (‖a j‖ * Real.exp (-(Real.pi * Real.exp (-L)) * ‖e j‖ ^ 2)))
      (fun j => ?_) ?_ ?_
    · apply Continuous.continuousOn
      apply continuous_const.mul
      unfold gauss
      refine continuous_finset_prod _ fun i _ => ?_
      have hd : Continuous fun y : I → ℝ => dil y (e j) i := by unfold dil; fun_prop
      exact ((continuous_hmon _).comp hd).mul (by fun_prop)
    · exact (ha _ (by positivity)).mul_left _
    · intro j y hy
      rw [norm_mul]
      have h := norm_term_le n y (e j) (Real.exp_pos (-L)).le fun i => Real.exp_le_exp.mpr (hy i).le
      calc ‖a j‖ * ‖gauss n (dil y (e j))‖
          ≤ ‖a j‖ * (gC n * Real.exp (-Real.pi * Real.exp (-L) * ‖e j‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left h (norm_nonneg _)
        _ = _ := by ring_nf
  exact hc.continuousAt (hU.mem_nhds hL)

theorem one_dim {σ c R t : ℝ} (hc : 0 < c) (hR : 0 ≤ R) (ht : -R ≤ t) :
    σ * t - c * Real.exp t ≤ ((|σ| + 1) ^ 2 / (2 * c) + (|σ| + 1) * R) - |t| := by
  have hK1 : 0 ≤ (|σ| + 1) ^ 2 / (2 * c) := by positivity
  have hσ := abs_nonneg σ
  rcases le_total 0 t with h | h
  · have he : t ^ 2 / 2 ≤ Real.exp t := by
      have := Real.pow_div_factorial_le_exp t h 2
      simpa using this
    rw [abs_of_nonneg h]
    have hs : σ * t ≤ |σ| * t := mul_le_mul_of_nonneg_right (le_abs_self σ) h
    have key : (|σ| + 1) * t - c * (t ^ 2 / 2) ≤ (|σ| + 1) ^ 2 / (2 * c) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (c * t - (|σ| + 1))]
    nlinarith [mul_le_mul_of_nonneg_left he hc.le]
  · rw [abs_of_nonpos h]
    have hs : σ * t ≤ |σ| * R := by
      calc σ * t ≤ |σ * t| := le_abs_self _
        _ = |σ| * |t| := abs_mul _ _
        _ ≤ |σ| * R := mul_le_mul_of_nonneg_left (by rw [abs_of_nonpos h]; linarith) hσ
    have := mul_pos hc (Real.exp_pos t)
    nlinarith

theorem integrable_exp_neg_abs_one : Integrable (fun x : ℝ => Real.exp (-1 * |x|)) := by
  have h1 : IntegrableOn (fun x : ℝ => Real.exp (-1 * |x|)) (Set.Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 one_pos).congr_fun (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi
  have h2 : IntegrableOn (fun x : ℝ => Real.exp (-1 * |x|)) (Set.Iic 0) :=
    (integrableOn_exp_mul_Iic one_pos 0).congr_fun (fun x hx => by rw [abs_of_nonpos hx, neg_mul_neg])
      measurableSet_Iic
  have h3 := h2.union h1
  rw [Set.Iic_union_Ioi, integrableOn_univ] at h3
  exact h3

end GlobalTheory.HeckeTheta.Decay

namespace GlobalTheory.HeckeTheta.Decay

open GlobalTheory.HeckeTheta

theorem integrable_weight_theta : ∀ (I : Type) [Fintype I] {ι : Type} (e : ι → I → ℂ) (a : ι → ℂ) (n : I → ℤ) (q : (I → ℝ) → ℝ) (B R : ℝ), (∃ i, n i ≠ 0) → (∀ ε : ℝ, 0 < ε → Summable (fun j => ‖a j‖ * Real.exp (-ε * ‖e j‖ ^ 2))) → (∃ δ : ℝ, 0 < δ ∧ ∀ j, a j ≠ 0 → e j ≠ 0 → δ ≤ ‖e j‖) → Measurable q → (∀ y, |q y| ≤ B) → (∀ y, q y ≠ 0 → ∀ i j, y i - y j ≤ R) → MeasureTheory.AEStronglyMeasurable (fun y => (q y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y) MeasureTheory.volume ∧ ∀ σ : ℝ, MeasureTheory.Integrable (fun y => ‖(q y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y‖ * Real.exp (σ * ∑ i, y i)) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i}) := by
  intro I _ ι e a n q B R hn ha hδ hq hqB hqR
  obtain ⟨δ, hδ0, hδ⟩ := hδ
  obtain ⟨i0, hi0⟩ := hn
  haveI : Nonempty I := ⟨i0⟩
  have hcont := continuous_theta e a n ha
  have hmeas : AEStronglyMeasurable (fun y => (q y : ℂ) * theta e a n y) volume :=
    ((Complex.measurable_ofReal.comp hq).mul hcont.measurable).aestronglyMeasurable
  refine ⟨hmeas, fun σ => ?_⟩
  have hB : 0 ≤ B := (abs_nonneg _).trans (hqB 0)
  set R' := max R 0 with hR'
  have hR0 : 0 ≤ R' := le_max_right _ _
  have hqR' : ∀ y, q y ≠ 0 → ∀ i j, y i ≤ y j + R' := fun y hy i j => by
    have := hqR y hy i j; have := le_max_left R 0; linarith
  set N : ℝ := (Fintype.card I : ℝ) with hN
  have hN0 : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  set τ0 : ℝ := Real.exp (-R') / N with hτ0
  have hτ0p : 0 < τ0 := by positivity
  set ε0 : ℝ := Real.pi / 2 * τ0 with hε0
  have hε0p : 0 < ε0 := by positivity
  have hS := ha ε0 hε0p
  set S : ℝ := ∑' j, ‖a j‖ * Real.exp (-ε0 * ‖e j‖ ^ 2) with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg fun j => by positivity
  set c' : ℝ := Real.pi / 2 * δ ^ 2 * τ0 with hc'
  have hc'p : 0 < c' := by positivity
  set K : ℝ := (|σ| + 1) ^ 2 / (2 * c') + (|σ| + 1) * R' with hK
  set G : (I → ℝ) → ℝ := fun y => B * gC n * S * ∏ i, (Real.exp K * Real.exp (-1 * |y i|)) with hG

  have htheta : ∀ y, q y ≠ 0 → 0 ≤ ∑ i, y i →
      ‖theta e a n y‖ ≤ gC n * Real.exp (-c' * ∑ i, Real.exp (y i)) * S := by
    intro y hy hs
    obtain ⟨k, hk⟩ : ∃ k, 0 ≤ y k := by
      by_contra h
      push_neg at h
      have := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i (_ : i ∈ Finset.univ) => h i)
      simp only [Finset.sum_const_zero] at this
      linarith
    set T : ℝ := Real.exp (-R') * (∑ i, Real.exp (y i)) / N with hT
    have hTi : ∀ i, T ≤ Real.exp (y i) := by
      intro i
      rw [hT, div_le_iff₀ hN0]
      have h1 : ∀ j, Real.exp (-R') * Real.exp (y j) ≤ Real.exp (y i) := fun j => by
        rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by have := hqR' y hy j i; linarith)
      calc Real.exp (-R') * ∑ j, Real.exp (y j) = ∑ j, Real.exp (-R') * Real.exp (y j) := Finset.mul_sum _ _ _
        _ ≤ ∑ _j : I, Real.exp (y i) := Finset.sum_le_sum fun j _ => h1 j
        _ = Real.exp (y i) * N := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN, mul_comm]
    have hTτ : τ0 ≤ T := by
      rw [hT, hτ0]
      apply div_le_div_of_nonneg_right _ hN0.le
      have h1 : 1 ≤ ∑ i, Real.exp (y i) :=
        (Real.one_le_exp hk).trans (Finset.single_le_sum (f := fun i => Real.exp (y i))
          (fun i _ => (Real.exp_pos _).le) (Finset.mem_univ k))
      have := Real.exp_pos (-R')
      nlinarith
    have hT0 : 0 ≤ T := hτ0p.le.trans hTτ
    have hterm : ∀ j, ‖a j * gauss n (dil y (e j))‖ ≤
        gC n * Real.exp (-c' * ∑ i, Real.exp (y i)) * (‖a j‖ * Real.exp (-ε0 * ‖e j‖ ^ 2)) := by
      intro j
      have hC := gC_nonneg n
      by_cases haj : a j = 0
      · simp only [haj, zero_mul, norm_zero, mul_zero]; exact le_refl _
      by_cases hej : e j = 0
      · have : dil y (e j) = 0 := by funext i; simp [dil, hej]
        rw [this, gauss_zero ⟨i0, hi0⟩, mul_zero, norm_zero]
        positivity
      have hd := hδ j haj hej
      rw [norm_mul]
      have h1 := norm_term_le n y (e j) hT0 hTi
      have h2 : Real.exp (-Real.pi * T * ‖e j‖ ^ 2) ≤
          Real.exp (-c' * ∑ i, Real.exp (y i)) * Real.exp (-ε0 * ‖e j‖ ^ 2) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have e1 : c' * ∑ i, Real.exp (y i) = Real.pi / 2 * δ ^ 2 * T := by
          rw [hc', hT, hτ0]; field_simp
        rw [hε0]
        have hδe : δ ^ 2 ≤ ‖e j‖ ^ 2 := pow_le_pow_left₀ hδ0.le hd 2
        have a1 := mul_le_mul_of_nonneg_left hδe hT0
        have a2 := mul_le_mul_of_nonneg_right hTτ (sq_nonneg ‖e j‖)
        have hp := Real.pi_pos
        nlinarith [mul_le_mul_of_nonneg_left a1 hp.le, mul_le_mul_of_nonneg_left a2 hp.le, e1]
      calc ‖a j‖ * ‖gauss n (dil y (e j))‖ ≤ ‖a j‖ * (gC n * Real.exp (-Real.pi * T * ‖e j‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ ≤ ‖a j‖ * (gC n * (Real.exp (-c' * ∑ i, Real.exp (y i)) * Real.exp (-ε0 * ‖e j‖ ^ 2))) := by
            gcongr
        _ = _ := by ring
    have hsum : HasSum (fun j => gC n * Real.exp (-c' * ∑ i, Real.exp (y i)) *
        (‖a j‖ * Real.exp (-ε0 * ‖e j‖ ^ 2))) (gC n * Real.exp (-c' * ∑ i, Real.exp (y i)) * S) :=
      hS.hasSum.mul_left _
    exact tsum_of_norm_bounded hsum hterm
  have hbound : ∀ y, 0 ≤ ∑ i, y i →
      ‖(q y : ℂ) * theta e a n y‖ * Real.exp (σ * ∑ i, y i) ≤ G y := by
    intro y hs
    have hG0 : 0 ≤ G y := by
      simp only [hG]
      have := gC_nonneg n
      positivity
    by_cases hq0 : q y = 0
    · simp only [hq0, Complex.ofReal_zero, zero_mul, norm_zero]; exact hG0
    have hyR : ∀ i, -R' ≤ y i := by
      obtain ⟨k, hk⟩ : ∃ k, 0 ≤ y k := by
        by_contra h
        push_neg at h
        have := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i (_ : i ∈ Finset.univ) => h i)
        simp only [Finset.sum_const_zero] at this
        linarith
      intro i; have := hqR' y hq0 k i; linarith
    have h1 := htheta y hq0 hs
    have h2 : Real.exp (-c' * ∑ i, Real.exp (y i)) * Real.exp (σ * ∑ i, y i) ≤
        ∏ i, (Real.exp K * Real.exp (-1 * |y i|)) := by
      rw [← Real.exp_add]
      have e1 : -c' * ∑ i, Real.exp (y i) + σ * ∑ i, y i = ∑ i, (σ * y i - c' * Real.exp (y i)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e1, Real.exp_sum]
      apply Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le)
      intro i _
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := one_dim (σ := σ) hc'p hR0 (hyR i)
      rw [hK]; linarith
    have hqy : ‖(q y : ℂ)‖ ≤ B := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hqB y
    rw [norm_mul]
    have hC := gC_nonneg n
    calc ‖(q y : ℂ)‖ * ‖theta e a n y‖ * Real.exp (σ * ∑ i, y i)
        ≤ B * (gC n * Real.exp (-c' * ∑ i, Real.exp (y i)) * S) * Real.exp (σ * ∑ i, y i) := by
          gcongr
      _ = B * gC n * S * (Real.exp (-c' * ∑ i, Real.exp (y i)) * Real.exp (σ * ∑ i, y i)) := by ring
      _ ≤ B * gC n * S * ∏ i, (Real.exp K * Real.exp (-1 * |y i|)) := by
          gcongr
  have hGi : Integrable G volume := by
    have h1 : Integrable (fun y : I → ℝ => ∏ i, (Real.exp K * Real.exp (-1 * |y i|))) volume :=
      Integrable.fintype_prod (f := fun _ x => Real.exp K * Real.exp (-1 * |x|))
        fun _ => integrable_exp_neg_abs_one.const_mul _
    exact h1.const_mul _
  have hset : MeasurableSet {y : I → ℝ | 0 ≤ ∑ i, y i} :=
    measurableSet_le measurable_const (by fun_prop)
  refine Integrable.mono' hGi.restrict ?_ ?_
  · exact (hmeas.norm.mul (Continuous.aestronglyMeasurable (by fun_prop))).restrict
  · rw [ae_restrict_iff' hset]
    filter_upwards with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hbound y hy

end GlobalTheory.HeckeTheta.Decay
