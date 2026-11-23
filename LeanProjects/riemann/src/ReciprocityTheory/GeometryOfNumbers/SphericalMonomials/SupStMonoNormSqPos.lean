import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.MonomSt
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.BergmanDefs

namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory

theorem supSt_adt_eq (D n : ℕ) :
    Finset.Nat.antidiagonalTuple (D + 1) n = Finset.piAntidiag Finset.univ n := by
  ext a
  simp [Finset.mem_piAntidiag, Finset.Nat.mem_antidiagonalTuple]

theorem supSt_term {D n : ℕ} (a : Fin (D + 1) → ℕ) (ha : ∑ i, a i = n) (z : Fin (D + 1) → ℂ) :
    ‖monoC a z‖ ^ 2 / monoNormSq a =
      ((n + D).choose D : ℝ) * ((Nat.multinomial Finset.univ a : ℕ) *
        ∏ i, (‖z i‖ ^ 2) ^ a i) := by
  have hnorm : ‖monoC a z‖ ^ 2 = ∏ i, (‖z i‖ ^ 2) ^ a i := by
    simp only [monoC, norm_prod, norm_pow, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => by ring
  have hP : ((∏ i, (a i).factorial : ℕ) : ℝ) ≠ 0 := by
    have : 0 < ∏ i, (a i).factorial := Finset.prod_pos fun i _ => Nat.factorial_pos _
    exact_mod_cast this.ne'
  have hspec := Nat.multinomial_spec Finset.univ a
  rw [ha] at hspec
  have hm : ((Nat.multinomial Finset.univ a : ℕ) : ℝ) =
      (n.factorial : ℝ) / ((∏ i, (a i).factorial : ℕ) : ℝ) := by
    rw [eq_div_iff hP, mul_comm]
    exact_mod_cast hspec
  have hc : ((n + D).choose D : ℝ) = ((n + D).factorial : ℝ) / ((n.factorial : ℝ) * (D.factorial : ℝ)) := by
    rw [eq_div_iff (by positivity), ← mul_assoc]
    exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial n D
  rw [hnorm, monoNormSq, ha, hm, hc]
  have h1 : (n.factorial : ℝ) ≠ 0 := by positivity
  have h2 : (D.factorial : ℝ) ≠ 0 := by positivity
  have h3 : ((n + D).factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem sum_mono_sq_div (D n : ℕ) (z : Fin (D + 1) → ℂ) :
    ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, ‖monoC a z‖ ^ 2 / monoNormSq a =
      ((n + D).choose D : ℝ) * sqN z ^ n := by
  rw [Finset.sum_congr rfl (fun a ha => supSt_term a (Finset.Nat.mem_antidiagonalTuple.mp ha) z),
    ← Finset.mul_sum, supSt_adt_eq, sqN, Finset.sum_pow_eq_sum_piAntidiag]

theorem supSt_norm_mono_le {D : ℕ} (a : Fin (D + 1) → ℕ) (z : Fin (D + 1) → ℂ) (h : sqN z = 1) :
    ‖monoC a z‖ ≤ 1 := by
  simp only [monoC, norm_prod, norm_pow]
  apply Finset.prod_le_one (fun i _ => by positivity)
  intro i _
  have h1 : ‖z i‖ ^ 2 ≤ sqN z := by
    unfold sqN
    exact Finset.single_le_sum (f := fun j => ‖z j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)
  rw [h] at h1
  have h2 : ‖z i‖ ≤ 1 := by nlinarith [norm_nonneg (z i)]
  exact pow_le_one₀ (norm_nonneg _) h2

theorem supSt_integrable {D : ℕ} (a b : Fin (D + 1) → ℕ) :
    Integrable (fun z => starRingEnd ℂ (monoC a z) * monoC b z) (sphProb (D + 1)) := by
  have hae : ∀ᵐ z ∂(sphProb (D + 1)), sqN z = 1 := mem_ae_iff.mpr (sphProb_compl_sphere D)
  refine Integrable.of_bound (sphMonom_continuous_f a b).aestronglyMeasurable 1 ?_
  filter_upwards [hae] with z hz
  rw [norm_mul, RCLike.norm_conj]
  have h1 := supSt_norm_mono_le a z hz
  have h2 := supSt_norm_mono_le b z hz
  nlinarith [norm_nonneg (monoC a z), norm_nonneg (monoC b z)]

theorem supSt_gram {D : ℕ} (a b : Fin (D + 1) → ℕ) :
    ∫ z, starRingEnd ℂ (monoC a z) * monoC b z ∂(sphProb (D + 1)) =
      if a = b then (monoNormSq a : ℂ) else 0 := by
  split_ifs with h
  · subst h
    have hz : ∀ z, starRingEnd ℂ (monoC a z) * monoC a z = ((‖monoC a z‖ ^ 2 : ℝ) : ℂ) := by
      intro z
      rw [Complex.conj_mul']
      push_cast
      ring
    simp_rw [hz]
    rw [integral_complex_ofReal, integral_mono_sq_sphProb]
  · exact integral_mono_sphProb_of_ne h

theorem integral_form_sq (D n : ℕ) (c : (Fin (D + 1) → ℕ) → ℂ) :
    ∫ z, ‖∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, c a * monoC a z‖ ^ 2 ∂(sphProb (D + 1)) =
      ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, ‖c a‖ ^ 2 * monoNormSq a := by
  set T := Finset.Nat.antidiagonalTuple (D + 1) n
  have key : ∀ z, ((‖∑ a ∈ T, c a * monoC a z‖ ^ 2 : ℝ) : ℂ) =
      ∑ a ∈ T, ∑ b ∈ T, (starRingEnd ℂ (c a) * c b) * (starRingEnd ℂ (monoC a z) * monoC b z) := by
    intro z
    push_cast
    rw [← Complex.conj_mul', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul]
    ring
  have hI : ∫ z, ‖∑ a ∈ T, c a * monoC a z‖ ^ 2 ∂(sphProb (D + 1)) =
      (∫ z, ((‖∑ a ∈ T, c a * monoC a z‖ ^ 2 : ℝ) : ℂ) ∂(sphProb (D + 1))).re := by
    rw [integral_complex_ofReal, Complex.ofReal_re]
  have inner : ∀ a ∈ T, ∫ z, ∑ b ∈ T, (starRingEnd ℂ (c a) * c b) *
      (starRingEnd ℂ (monoC a z) * monoC b z) ∂(sphProb (D + 1)) =
      ((‖c a‖ ^ 2 * monoNormSq a : ℝ) : ℂ) := by
    intro a ha
    rw [integral_finset_sum _ (fun b _ => (supSt_integrable a b).const_mul _)]
    simp_rw [integral_const_mul, supSt_gram]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, ha, if_true]
    rw [Complex.conj_mul']
    push_cast
    ring
  rw [hI]
  simp_rw [key]
  rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ (fun b _ => (supSt_integrable a b).const_mul _)),
    Finset.sum_congr rfl inner, ← Complex.ofReal_sum, Complex.ofReal_re]

theorem supSt_monoNormSq_pos {D : ℕ} (a : Fin (D + 1) → ℕ) : 0 < monoNormSq a := by
  unfold monoNormSq
  have : 0 < ∏ i, (a i).factorial := Finset.prod_pos fun i _ => Nat.factorial_pos _
  have h1 : (0 : ℝ) < ((∏ i, (a i).factorial : ℕ) : ℝ) := by exact_mod_cast this
  positivity

theorem form_sq_le (D n : ℕ) (c : (Fin (D + 1) → ℕ) → ℂ) (z : Fin (D + 1) → ℂ) :
    ‖∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, c a * monoC a z‖ ^ 2 ≤
      ((n + D).choose D : ℝ) * sqN z ^ n *
        ∫ w, ‖∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, c a * monoC a w‖ ^ 2
          ∂(sphProb (D + 1)) := by
  set T := Finset.Nat.antidiagonalTuple (D + 1) n
  have hN : ∀ a : Fin (D + 1) → ℕ, 0 < Real.sqrt (monoNormSq a) := fun a => Real.sqrt_pos.mpr (supSt_monoNormSq_pos a)
  have h1 : ‖∑ a ∈ T, c a * monoC a z‖ ≤
      ∑ a ∈ T, (‖c a‖ * Real.sqrt (monoNormSq a)) * (‖monoC a z‖ / Real.sqrt (monoNormSq a)) := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun a _ => ?_))
    rw [norm_mul]
    field_simp [(hN a).ne']
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq T (fun a => ‖c a‖ * Real.sqrt (monoNormSq a))
    (fun a => ‖monoC a z‖ / Real.sqrt (monoNormSq a))
  have e1 : ∑ a ∈ T, (‖c a‖ * Real.sqrt (monoNormSq a)) ^ 2 = ∑ a ∈ T, ‖c a‖ ^ 2 * monoNormSq a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_pow, Real.sq_sqrt (supSt_monoNormSq_pos a).le]
  have e2 : ∑ a ∈ T, (‖monoC a z‖ / Real.sqrt (monoNormSq a)) ^ 2 = ∑ a ∈ T, ‖monoC a z‖ ^ 2 / monoNormSq a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [div_pow, Real.sq_sqrt (supSt_monoNormSq_pos a).le]
  rw [e1, e2, sum_mono_sq_div] at h2
  rw [integral_form_sq]
  calc ‖∑ a ∈ T, c a * monoC a z‖ ^ 2
      ≤ (∑ a ∈ T, (‖c a‖ * Real.sqrt (monoNormSq a)) * (‖monoC a z‖ / Real.sqrt (monoNormSq a))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ a ∈ T, ‖c a‖ ^ 2 * monoNormSq a) * (((n + D).choose D : ℝ) * sqN z ^ n) := h2
    _ = ((n + D).choose D : ℝ) * sqN z ^ n * ∑ a ∈ T, ‖c a‖ ^ 2 * monoNormSq a := by ring

end ReciprocityTheory.GeometryOfNumbersTheory
