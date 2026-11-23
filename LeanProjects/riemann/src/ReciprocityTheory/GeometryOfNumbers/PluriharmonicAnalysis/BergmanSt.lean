import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.BergmanDefs

namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory Matrix
open scoped ComplexOrder

variable {X : Type*} [MeasurableSpace X]

private theorem dotProduct_eq_sum_mul {r : ℕ} (u v : Fin r → ℂ) : u ⬝ᵥ v = ∑ i, u i * v i := rfl

private theorem mulVec_apply_eq_sum_pluriharmonic_analysis {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ) (i : Fin r) :
    (M *ᵥ v) i = ∑ j, M i j * v j := rfl

private theorem isHermitian_of_posDef {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) : G.IsHermitian := by
  exact hG.1

private theorem posDef_inv_of_posDef {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) : G⁻¹.PosDef := by
  exact hG.inv

private theorem star_dotProduct_mulVec_pos_of_posDef {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) {u : Fin r → ℂ}
    (hu : u ≠ 0) : 0 < star u ⬝ᵥ G *ᵥ u := by
  first
  | exact hG.2 u hu
  | exact hG.dotProduct_mulVec_pos hu

private theorem re_pos_and_im_eq_zero_of_pos {z : ℂ} (h : 0 < z) : 0 < z.re ∧ z.im = 0 := by
  have h' := Complex.pos_iff.mp h
  exact ⟨h'.1, h'.2.symm⟩

private theorem re_star_dotProduct_mulVec_nonneg_of_posDef {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) (u : Fin r → ℂ) :
    0 ≤ (star u ⬝ᵥ G *ᵥ u).re := by
  by_cases hu : u = 0
  · subst hu; simp
  · exact (re_pos_and_im_eq_zero_of_pos (star_dotProduct_mulVec_pos_of_posDef hG hu)).1.le

private theorem isUnit_det_of_posDef' {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) : IsUnit G.det := by
  exact (Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit

private theorem mul_inv_eq_one_of_posDef {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) : G * G⁻¹ = 1 :=
  Matrix.mul_nonsing_inv G (isUnit_det_of_posDef' hG)

private theorem inv_mul_eq_one_of_posDef {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) : G⁻¹ * G = 1 :=
  Matrix.nonsing_inv_mul G (isUnit_det_of_posDef' hG)

private theorem conj_star_dotProduct {r : ℕ} (u v : Fin r → ℂ) : starRingEnd ℂ (star u ⬝ᵥ v) = star v ⬝ᵥ u := by
  simp only [dotProduct_eq_sum_mul, Pi.star_apply, map_sum, map_mul, starRingEnd_apply, star_star]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem star_mulVec_dotProduct_of_isHermitian {r : ℕ} {H : Matrix (Fin r) (Fin r) ℂ} (hH : H.IsHermitian)
    (u v : Fin r → ℂ) : star (H *ᵥ u) ⬝ᵥ v = star u ⬝ᵥ H *ᵥ v := by
  simp only [dotProduct_eq_sum_mul, mulVec_apply_eq_sum_pluriharmonic_analysis, Pi.star_apply, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hH.apply i j]
  ring

private theorem quad_form_inv_mulVec_eq_inv_form {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) (y : Fin r → ℂ) :
    star (G⁻¹ *ᵥ y) ⬝ᵥ G *ᵥ (G⁻¹ *ᵥ y) = star y ⬝ᵥ G⁻¹ *ᵥ y := by
  rw [Matrix.mulVec_mulVec, mul_inv_eq_one_of_posDef hG, Matrix.one_mulVec,
    star_mulVec_dotProduct_of_isHermitian (isHermitian_of_posDef (posDef_inv_of_posDef hG))]

private theorem star_smul_sub_dotProduct_mulVec_expand {r : ℕ} (G : Matrix (Fin r) (Fin r) ℂ) (P z : ℂ) (a c : Fin r → ℂ) :
    star (P • c - z • a) ⬝ᵥ G *ᵥ (P • c - z • a) =
      starRingEnd ℂ P * P * (star c ⬝ᵥ G *ᵥ c) - starRingEnd ℂ P * z * (star c ⬝ᵥ G *ᵥ a)
        - starRingEnd ℂ z * P * (star a ⬝ᵥ G *ᵥ c) + starRingEnd ℂ z * z * (star a ⬝ᵥ G *ᵥ a) := by
  simp only [starRingEnd_apply]
  simp only [star_sub, star_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, _root_.sub_dotProduct,
    _root_.dotProduct_sub, _root_.smul_dotProduct, _root_.dotProduct_smul, smul_eq_mul]
  ring

private theorem complex_norm_sq_eq_re_sq_add_im_sq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem posDef_norm_dot_sq_le {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) (c y : Fin r → ℂ) :
    ‖star y ⬝ᵥ c‖ ^ 2 ≤ (star c ⬝ᵥ G *ᵥ c).re * (star y ⬝ᵥ G⁻¹ *ᵥ y).re := by
  by_cases hy : y = 0
  · subst hy; simp
  have hHi := isHermitian_of_posDef (posDef_inv_of_posDef hG)
  have hP := re_pos_and_im_eq_zero_of_pos (star_dotProduct_mulVec_pos_of_posDef (posDef_inv_of_posDef hG) hy)
  have f2 : star (G⁻¹ *ᵥ y) ⬝ᵥ G *ᵥ c = star y ⬝ᵥ c := by
    rw [star_mulVec_dotProduct_of_isHermitian hHi, Matrix.mulVec_mulVec, inv_mul_eq_one_of_posDef hG, Matrix.one_mulVec]
  have f3 : star c ⬝ᵥ G *ᵥ (G⁻¹ *ᵥ y) = starRingEnd ℂ (star y ⬝ᵥ c) := by
    rw [Matrix.mulVec_mulVec, mul_inv_eq_one_of_posDef hG, Matrix.one_mulVec, conj_star_dotProduct]
  have key := re_star_dotProduct_mulVec_nonneg_of_posDef hG ((star y ⬝ᵥ G⁻¹ *ᵥ y) • c - (star y ⬝ᵥ c) • (G⁻¹ *ᵥ y))
  rw [star_smul_sub_dotProduct_mulVec_expand, quad_form_inv_mulVec_eq_inv_form hG, f2, f3] at key
  obtain ⟨p, hp⟩ : ∃ p : ℝ, star y ⬝ᵥ G⁻¹ *ᵥ y = p :=
    ⟨(star y ⬝ᵥ G⁻¹ *ᵥ y).re, Complex.ext (by simp) (by simp [hP.2])⟩
  rw [hp] at key hP ⊢
  generalize star y ⬝ᵥ c = z at key ⊢
  generalize star c ⬝ᵥ G *ᵥ c = B at key ⊢
  simp only [Complex.conj_ofReal, Complex.ofReal_re] at key hP ⊢
  rw [complex_norm_sq_eq_re_sq_add_im_sq]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im] at key
  nlinarith [hP.1, key]

theorem bNormSq_eq (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ)
    (hint : ∀ i j, Integrable (fun x => starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) μ)
    (c : Fin r → ℂ) :
    (bNormSq μ s w c : ℂ) = ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * bGram μ s w i j := by
  have hI : ∀ i j, Integrable (fun x => starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) μ := by
    assumption
  have hpt : ∀ x, ((‖∑ i, c i * s i x‖ ^ 2 * w x : ℝ) : ℂ) =
      ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * (starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) := by
    intro x
    rw [Complex.ofReal_mul, Complex.sq_norm, Complex.normSq_eq_conj_mul_self, map_sum,
      Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_mul]
    ring
  have hJ : ∀ i ∈ (Finset.univ : Finset (Fin r)), Integrable (fun x => ∑ j, starRingEnd ℂ (c i) * c j *
      (starRingEnd ℂ (s i x) * s j x * (w x : ℂ))) μ :=
    fun i _ => integrable_finset_sum _ fun j _ => (hI i j).const_mul _
  have hK : ∀ i, ∀ j ∈ (Finset.univ : Finset (Fin r)), Integrable (fun x => starRingEnd ℂ (c i) * c j *
      (starRingEnd ℂ (s i x) * s j x * (w x : ℂ))) μ :=
    fun i j _ => (hI i j).const_mul _
  unfold bNormSq
  rw [← integral_complex_ofReal]
  simp only [hpt]
  rw [integral_finset_sum _ hJ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ (hK i)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  rfl

theorem bNormSq_eq_re (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ)
    (hint : ∀ i j, Integrable (fun x => starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) μ)
    (c : Fin r → ℂ) :
    bNormSq μ s w c = (star c ⬝ᵥ bGram μ s w *ᵥ c).re := by
  have hI : ∀ i j, Integrable (fun x => starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) μ := by
    assumption
  have h2 : star c ⬝ᵥ bGram μ s w *ᵥ c =
      ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * bGram μ s w i j := by
    simp only [dotProduct_eq_sum_mul, mulVec_apply_eq_sum_pluriharmonic_analysis, Pi.star_apply, Finset.mul_sum, starRingEnd_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [h2, ← bNormSq_eq μ s w hI c, Complex.ofReal_re]

theorem berg_eq_quad (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ) (x : X) :
    bergmanDensity μ s w x = w x * (star (star fun i => s i x) ⬝ᵥ (bGram μ s w)⁻¹ *ᵥ star fun i => s i x).re := by
  unfold bergmanDensity
  rw [star_star]
  congr 2
  simp only [dotProduct_eq_sum_mul, mulVec_apply_eq_sum_pluriharmonic_analysis, Pi.star_apply, Finset.mul_sum, starRingEnd_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem sum_mul_eq_star_dot {r : ℕ} (s : Fin r → X → ℂ) (c : Fin r → ℂ) (x : X) :
    ∑ i, c i * s i x = star (star fun i => s i x) ⬝ᵥ c := by
  rw [star_star, dotProduct_eq_sum_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem sq_le_berg_mul (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x)
    (hint : ∀ i j, Integrable (fun x => starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) μ)
    (hpos : (bGram μ s w).PosDef) (c : Fin r → ℂ) (x : X) :
    ‖∑ i, c i * s i x‖ ^ 2 * w x ≤ bergmanDensity μ s w x * bNormSq μ s w c := by
  have hI : ∀ i j, Integrable (fun x => starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) μ := by
    assumption
  rw [sum_mul_eq_star_dot, berg_eq_quad, bNormSq_eq_re μ s w hI c]
  have h := mul_le_mul_of_nonneg_right (posDef_norm_dot_sq_le hpos c (star fun i => s i x)) (hw x)
  refine le_trans h (le_of_eq ?_)
  ring

theorem berg_le_of_forall (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x)
    (hint : ∀ i j, Integrable (fun x => starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) μ)
    (hpos : (bGram μ s w).PosDef) (x : X) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ c : Fin r → ℂ, ‖∑ i, c i * s i x‖ ^ 2 * w x ≤ M * bNormSq μ s w c) :
    bergmanDensity μ s w x ≤ M := by
  have hI : ∀ i j, Integrable (fun x => starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) μ := by
    assumption
  have h := hM ((bGram μ s w)⁻¹ *ᵥ star fun i => s i x)
  rw [sum_mul_eq_star_dot s ((bGram μ s w)⁻¹ *ᵥ star fun i => s i x) x, bNormSq_eq_re μ s w hI,
    quad_form_inv_mulVec_eq_inv_form hpos] at h
  have hq := re_star_dotProduct_mulVec_nonneg_of_posDef (posDef_inv_of_posDef hpos) (star fun i => s i x)
  rw [berg_eq_quad]
  generalize star (star fun i => s i x) ⬝ᵥ (bGram μ s w)⁻¹ *ᵥ (star fun i => s i x) = q at h hq ⊢
  rw [complex_norm_sq_eq_re_sq_add_im_sq] at h
  have hwx := hw x
  rcases hq.eq_or_lt with h0 | hq0
  · rw [← h0]
    simpa using hM0
  · have h3 : q.re ^ 2 * w x ≤ M * q.re := by nlinarith [sq_nonneg q.im]
    nlinarith

end ReciprocityTheory.GeometryOfNumbersTheory
