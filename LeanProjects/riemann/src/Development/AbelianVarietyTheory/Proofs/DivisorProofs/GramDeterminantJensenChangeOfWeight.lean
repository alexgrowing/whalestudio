import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSimultaneousDiagonalisationPosDefHermitianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramIsHermitianL2EqDoubleSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramPosDefOfL2DefiniteStatement

set_option autoImplicit false

noncomputable section

open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.GramJensen

variable {S : Type} {Y : S → Type} [∀ σ, MeasurableSpace (Y σ)] {ι : Type} [Fintype ι] [DecidableEq ι]

def twist (v : ∀ σ, Y σ → ι → ℂ) (w : ∀ σ, Y σ → ℝ) : ∀ σ, Y σ → ι → ℂ :=
  fun σ y i => v σ y i * (Real.exp (-(w σ y) / 2) : ℝ)

def col (T : Matrix ι ι ℂ) (a : ι) : ι → ℂ := fun i => star (T i a)

theorem exp_half_sq (t : ℝ) : Real.exp (-t / 2) ^ 2 = Real.exp (-t) := by
  rw [sq, ← Real.exp_add]; ring_nf

theorem cmb_twist (v : ∀ σ, Y σ → ι → ℂ) (w : ∀ σ, Y σ → ℝ) (c : ι → ℂ) (σ : S) (y : Y σ) :
    cmb (twist v w) c σ y = cmb v c σ y * Real.exp (-(w σ y)) := by
  have h : ∑ i, c i * twist v w σ y i = (∑ i, c i * v σ y i) * (Real.exp (-(w σ y) / 2) : ℝ) := by
    rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => ?_; simp only [twist]; ring
  rw [cmb, cmb, h, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, exp_half_sq]

theorem cmb_nonneg (v : ∀ σ, Y σ → ι → ℂ) (c : ι → ℂ) (σ : S) (y : Y σ) : 0 ≤ cmb v c σ y := by
  unfold cmb; positivity

theorem exp_neg_le {C t : ℝ} (h : |t| ≤ C) : Real.exp (-t) ≤ Real.exp C :=
  Real.exp_le_exp.2 (by linarith [neg_le_abs t])

theorem exp_neg_ge {C t : ℝ} (h : |t| ≤ C) : Real.exp (-C) ≤ Real.exp (-t) :=
  Real.exp_le_exp.2 (by linarith [le_abs_self t])

variable {μ : ∀ σ, Measure (Y σ)} {v : ∀ σ, Y σ → ι → ℂ} {w : ∀ σ, Y σ → ℝ} {C : ℝ}

theorem isFam_twist (h : IsFam μ v) (hw : ∀ σ, Measurable (w σ)) (hC : ∀ σ y, |w σ y| ≤ C) :
    IsFam μ (twist v w) := by
  refine ⟨h.finite, fun σ i j => ?_⟩
  have e : (fun y => twist v w σ y i * (starRingEnd ℂ) (twist v w σ y j)) =
      fun y => ((Real.exp (-(w σ y)) : ℝ) : ℂ) * (v σ y i * (starRingEnd ℂ) (v σ y j)) := by
    funext y
    simp only [twist, map_mul, Complex.conj_ofReal]
    rw [← exp_half_sq]; push_cast; ring
  rw [e]
  refine (h.integrable σ i j).bdd_mul (c := Real.exp C) ?_ ?_
  · exact (Complex.measurable_ofReal.comp (Real.measurable_exp.comp (hw σ).neg)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact exp_neg_le (hC σ y)

theorem l2_twist_eq_finsum_integral_mul_exp_neg (c : ι → ℂ) :
    l2 μ (twist v w) c = ∑ᶠ σ, ∫ y, cmb v c σ y * Real.exp (-(w σ y)) ∂μ σ := by
  simp only [l2, cmb_twist]

theorem quad (M T : Matrix ι ι ℂ) (a : ι) :
    ∑ i, ∑ j, col T a i * (starRingEnd ℂ) (col T a j) * M i j = (Tᴴ * M * T) a a := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, col]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.star_def, Complex.conj_conj]; ring

theorem quad_vec (M : Matrix ι ι ℂ) (x : ι → ℂ) :
    star x ⬝ᵥ (M *ᵥ x) = ∑ i, ∑ j, star x i * (starRingEnd ℂ) (star x j) * M i j := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, Complex.star_def, Complex.conj_conj]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring

theorem exp_neg_bound_mul_l2_le_l2_twist (h : IsFam μ v) (hw : ∀ σ, Measurable (w σ)) (hC : ∀ σ y, |w σ y| ≤ C) (c : ι → ℂ) :
    Real.exp (-C) * l2 μ v c ≤ l2 μ (twist v w) c := by
  have hS := h.finite
  haveI := Fintype.ofFinite S
  obtain ⟨-, hc⟩ := GlobalTheory.T.gram_isHermitian_l2_eq_double_sum S Y ι μ v h
  rw [l2_twist_eq_finsum_integral_mul_exp_neg]
  simp only [l2, finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_le_sum fun σ _ => ?_
  rw [← integral_const_mul]
  refine integral_mono (((hc c).1 σ).const_mul _) ?_ fun y => ?_
  · exact ((hc c).1 σ).mul_bdd (c := Real.exp C) (Real.measurable_exp.comp (hw σ).neg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact exp_neg_le (hC σ y))
  · have h0 := cmb_nonneg v c σ y
    have h1 := exp_neg_ge (hC σ y)
    simp only
    nlinarith

theorem posDef_twist (h : IsFam μ v) (hG : (gram μ v).PosDef) (hw : ∀ σ, Measurable (w σ))
    (hC : ∀ σ y, |w σ y| ≤ C) : (gram μ (twist v w)).PosDef := by
  refine GlobalTheory.T.gram_posDef_of_l2_definite S Y ι μ _ (isFam_twist h hw hC) fun c hc0 => ?_
  by_contra hne
  have hx : star c ≠ 0 := fun h' => hne (by simpa using congrArg star h')
  have hpos := hG.dotProduct_mulVec_pos hx
  obtain ⟨-, hl⟩ := GlobalTheory.T.gram_isHermitian_l2_eq_double_sum S Y ι μ v h
  rw [quad_vec, star_star, ← (hl c).2.2] at hpos
  have hp : 0 < l2 μ v c := by exact_mod_cast hpos
  have := exp_neg_bound_mul_l2_le_l2_twist h hw hC c
  rw [hc0] at this
  nlinarith [Real.exp_pos (-C)]

theorem jensen (hS : Finite S) (f : ∀ σ, Y σ → ℝ) (hf0 : ∀ σ y, 0 ≤ f σ y)
    (hfi : ∀ σ, Integrable (f σ) (μ σ)) (hf1 : ∑ᶠ σ, ∫ y, f σ y ∂μ σ = 1) (hw : ∀ σ, Measurable (w σ))
    (hC : ∀ σ y, |w σ y| ≤ C) :
    Real.exp (-(∑ᶠ σ, ∫ y, w σ y * f σ y ∂μ σ)) ≤ ∑ᶠ σ, ∫ y, f σ y * Real.exp (-(w σ y)) ∂μ σ := by
  haveI := Fintype.ofFinite S
  simp only [finsum_eq_sum_of_fintype] at hf1 ⊢
  obtain ⟨m, hm⟩ : ∃ m, m = ∑ σ, ∫ y, w σ y * f σ y ∂μ σ := ⟨_, rfl⟩
  rw [← hm]
  have hwi : ∀ σ, Integrable (fun y => w σ y * f σ y) (μ σ) := fun σ =>
    (hfi σ).bdd_mul (c := C) (hw σ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hC σ y)
  have hei : ∀ σ, Integrable (fun y => f σ y * Real.exp (-(w σ y))) (μ σ) := fun σ =>
    (hfi σ).mul_bdd (c := Real.exp C) (Real.measurable_exp.comp (hw σ).neg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact exp_neg_le (hC σ y))
  have pt : ∀ σ y, Real.exp (-m) * (f σ y * (1 + m) - w σ y * f σ y) ≤ f σ y * Real.exp (-(w σ y)) := by
    intro σ y
    have h1 := Real.add_one_le_exp (m - w σ y)
    have h2 : Real.exp (-m) * Real.exp (m - w σ y) = Real.exp (-(w σ y)) := by rw [← Real.exp_add]; ring_nf
    have h3 : Real.exp (-m) * (m - w σ y + 1) ≤ Real.exp (-(w σ y)) := by
      rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    have h4 := mul_le_mul_of_nonneg_left h3 (hf0 σ y)
    nlinarith
  have e : ∀ σ, ∫ y, Real.exp (-m) * (f σ y * (1 + m) - w σ y * f σ y) ∂μ σ =
      Real.exp (-m) * ((1 + m) * ∫ y, f σ y ∂μ σ - ∫ y, w σ y * f σ y ∂μ σ) := by
    intro σ
    rw [integral_const_mul, integral_sub ((hfi σ).mul_const _) (hwi σ), integral_mul_const]; ring
  calc Real.exp (-m) = Real.exp (-m) * ((1 + m) * ∑ σ, ∫ y, f σ y ∂μ σ - ∑ σ, ∫ y, w σ y * f σ y ∂μ σ) := by
        rw [hf1, ← hm]; ring
    _ = ∑ σ, ∫ y, Real.exp (-m) * (f σ y * (1 + m) - w σ y * f σ y) ∂μ σ := by
        rw [Finset.sum_congr rfl fun σ _ => e σ, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ ≤ ∑ σ, ∫ y, f σ y * Real.exp (-(w σ y)) ∂μ σ :=
        Finset.sum_le_sum fun σ _ => integral_mono ((((hfi σ).mul_const _).sub (hwi σ)).const_mul _) (hei σ) (pt σ)

theorem berg_sum (T : Matrix ι ι ℂ) (hT : Tᴴ * gram μ v * T = 1) (σ : S) (y : Y σ) :
    ∑ a, cmb v (col T a) σ y = bergmanDensity μ v σ y := by
  have hinv : (gram μ v)⁻¹ = T * Tᴴ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.mul_assoc]
    exact mul_eq_one_comm.1 hT
  have hn : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have key : ((∑ a, cmb v (col T a) σ y : ℝ) : ℂ) =
      ∑ i, ∑ j, (gram μ v)⁻¹ j i * (v σ y i * (starRingEnd ℂ) (v σ y j)) := by
    have ha : ∀ a, ((cmb v (col T a) σ y : ℝ) : ℂ) =
        ∑ i, ∑ j, T j a * star (T i a) * (v σ y i * (starRingEnd ℂ) (v σ y j)) := by
      intro a
      rw [cmb, hn, map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [col, map_mul, Complex.star_def, Complex.conj_conj]; ring
    rw [hinv, Complex.ofReal_sum]
    simp only [ha, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  rw [bergmanDensity, ← key, Complex.ofReal_re]

theorem jensen_gram (h : IsFam μ v) (hG : (gram μ v).PosDef) (hw : ∀ σ, Measurable (w σ))
    (hC : ∀ σ y, |w σ y| ≤ C) :
    IsFam μ (twist v w) ∧ (gram μ (twist v w)).PosDef ∧
      Real.log (gram μ v).det.re - ∑ᶠ σ, ∫ y, w σ y * bergmanDensity μ v σ y ∂μ σ ≤
        Real.log (gram μ (twist v w)).det.re := by
  have hF := isFam_twist h hw hC
  have hG' := posDef_twist h hG hw hC
  refine ⟨hF, hG', ?_⟩
  have hS := h.finite
  haveI := Fintype.ofFinite S
  obtain ⟨T, d, -, hT, hT'⟩ := GlobalTheory.T.exists_simultaneous_diagonalisation_posDef_hermitian ι _ _ hG hG'.1
  obtain ⟨-, hl⟩ := GlobalTheory.T.gram_isHermitian_l2_eq_double_sum S Y ι μ v h
  obtain ⟨-, hl'⟩ := GlobalTheory.T.gram_isHermitian_l2_eq_double_sum S Y ι μ _ hF
  have hl1 : ∀ a, l2 μ v (col T a) = 1 := fun a => by
    have := (hl (col T a)).2.2
    rw [quad, hT, Matrix.one_apply_eq] at this; exact_mod_cast this
  have hld : ∀ a, l2 μ (twist v w) (col T a) = d a := fun a => by
    have := (hl' (col T a)).2.2
    rw [quad, hT', Matrix.diagonal_apply_eq] at this; exact_mod_cast this
  have hj : ∀ a, Real.exp (-(∑ᶠ σ, ∫ y, w σ y * cmb v (col T a) σ y ∂μ σ)) ≤ d a := fun a => by
    rw [← hld a, l2_twist_eq_finsum_integral_mul_exp_neg]
    exact jensen hS (cmb v (col T a)) (cmb_nonneg v _) (hl (col T a)).1 (hl1 a) hw hC
  have hd : ∀ a, 0 < d a := fun a => (Real.exp_pos _).trans_le (hj a)
  have hdet : (gram μ (twist v w)).det = (gram μ v).det * ∏ a, (d a : ℂ) := by
    have e1 := congrArg Matrix.det hT
    have e2 := congrArg Matrix.det hT'
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one] at e1
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at e2
    linear_combination (gram μ v).det * e2 - (gram μ (twist v w)).det * e1
  have hpos := Complex.pos_iff.1 (Matrix.PosDef.det_pos hG)
  have hre : (gram μ (twist v w)).det.re = (gram μ v).det.re * ∏ a, d a := by
    rw [hdet, ← Complex.ofReal_prod, Complex.re_mul_ofReal]
  rw [hre, Real.log_mul hpos.1.ne' (Finset.prod_pos fun a _ => hd a).ne', Real.log_prod fun a _ => (hd a).ne']
  have hsum : ∑ᶠ σ, ∫ y, w σ y * bergmanDensity μ v σ y ∂μ σ = ∑ a, ∑ᶠ σ, ∫ y, w σ y * cmb v (col T a) σ y ∂μ σ := by
    simp only [finsum_eq_sum_of_fintype]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← integral_finsetSum Finset.univ fun a _ => ((hl (col T a)).1 σ).bdd_mul (c := C)
      (hw σ).aestronglyMeasurable (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hC σ y)]
    congr 1; funext y; rw [← Finset.mul_sum, berg_sum T hT]
  have hlog : ∀ a, -(∑ᶠ σ, ∫ y, w σ y * cmb v (col T a) σ y ∂μ σ) ≤ Real.log (d a) := fun a => by
    have := Real.log_le_log (Real.exp_pos _) (hj a); rwa [Real.log_exp] at this
  rw [hsum]
  have := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => hlog a
  rw [Finset.sum_neg_distrib] at this
  linarith

theorem gram_det_jensen : ∀ (S : Type) (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ), IsFam μ v → (gram μ v).PosDef → ∀ (w : ∀ σ, Y σ → ℝ) (C : ℝ), (∀ σ, Measurable (w σ)) → (∀ σ y, |w σ y| ≤ C) → IsFam μ (fun σ y i => v σ y i * (Real.exp (-(w σ y) / 2) : ℝ)) ∧ (gram μ fun σ y i => v σ y i * (Real.exp (-(w σ y) / 2) : ℝ)).PosDef ∧ Real.log (gram μ v).det.re - ∑ᶠ σ, ∫ y, w σ y * bergmanDensity μ v σ y ∂μ σ ≤ Real.log (gram μ fun σ y i => v σ y i * (Real.exp (-(w σ y) / 2) : ℝ)).det.re := by
  intro S Y _ ι _ _ μ v h hG w C hw hC
  exact jensen_gram h hG hw hC

end GlobalTheory.GramJensen
