import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
open scoped FourierTransform ContDiff RealInnerProductSpace Real

noncomputable section

namespace GlobalTheory.RealWeil.CoefQDecay

variable {n : ℕ}

def prodTrans (g g' : Sch (Fin n)) (p : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) → ℂ :=
  fun x => g (x + p) * starRingEnd ℂ (g' x)

theorem contDiff_prodTrans (g g' : Sch (Fin n)) (p : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ ∞ (prodTrans g g' p) := by
  have h1 : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => g (x + p)) :=
    g.smooth'.comp (contDiff_id.add contDiff_const)
  have h2 : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => starRingEnd ℂ (g' x)) :=
    Complex.conjCLE.contDiff.comp g'.smooth'
  exact h1.mul h2

theorem norm_integral_eq (g g' : Sch (Fin n)) (w : Fin n ⊕ Fin n → ℝ) :
    ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ = ‖𝓕 (prodTrans g g' (pPart w)) (-qPart w)‖ := by
  have e : (fun x => rhoFun w ⇑g x * starRingEnd ℂ (g' x)) = fun x =>
      Complex.exp (((π * ⟪pPart w, qPart w⟫ : ℝ) : ℂ) * Complex.I) *
        (𝐞 (-⟪x, -qPart w⟫) • prodTrans g g' (pPart w) x) := by
    funext x
    simp only [rhoFun, phase, prodTrans, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
    have h : Complex.exp (((2 * π * ⟪qPart w, x⟫ + π * ⟪pPart w, qPart w⟫ : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((π * ⟪pPart w, qPart w⟫ : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((2 * π * -⟪x, -qPart w⟫ : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      rw [inner_neg_right, neg_neg, real_inner_comm]
      push_cast
      ring
    rw [h]
    ring
  rw [e, integral_const_mul, Real.fourier_eq, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

def derivBound (g g' : Sch (Fin n)) (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i g *
    ‖iteratedFDeriv ℝ (j - i) g' x‖

theorem norm_iteratedFDeriv_prodTrans_le (g g' : Sch (Fin n)) (p : EuclideanSpace ℝ (Fin n)) (j : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ j (prodTrans g g' p) x‖ ≤ derivBound g g' j x := by
  have h1 : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => g (x + p)) :=
    g.smooth'.comp (contDiff_id.add contDiff_const)
  have h2 : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => starRingEnd ℂ (g' x)) :=
    Complex.conjCLE.contDiff.comp g'.smooth'
  refine (norm_iteratedFDeriv_mul_le h1 h2 x (n := j) (by exact_mod_cast le_top)).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  have e1 : ‖iteratedFDeriv ℝ i (fun x : EuclideanSpace ℝ (Fin n) => g (x + p)) x‖ ≤
      SchwartzMap.seminorm ℝ 0 i g := by
    rw [iteratedFDeriv_comp_add_right]
    exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ g i (x + p)
  have e2 : ‖iteratedFDeriv ℝ (j - i) (fun x : EuclideanSpace ℝ (Fin n) => starRingEnd ℂ (g' x)) x‖ =
      ‖iteratedFDeriv ℝ (j - i) g' x‖ := by
    have e : (fun x : EuclideanSpace ℝ (Fin n) => starRingEnd ℂ (g' x)) =
        (Complex.conjLIE : ℂ → ℂ) ∘ (g' : EuclideanSpace ℝ (Fin n) → ℂ) := rfl
    rw [e]
    exact Complex.conjLIE.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) _ x _
  rw [e2]
  gcongr

theorem integrable_derivBound (g g' : Sch (Fin n)) (j : ℕ) : Integrable (derivBound g g' j) := by
  unfold derivBound
  refine integrable_finset_sum _ fun i _ => ?_
  have := SchwartzMap.integrable_pow_mul_iteratedFDeriv volume g' 0 (j - i)
  simp only [pow_zero, one_mul] at this
  exact this.const_mul _

theorem integrable_prodTrans (g g' : Sch (Fin n)) (p : EuclideanSpace ℝ (Fin n)) (j : ℕ) :
    Integrable (fun x => ‖iteratedFDeriv ℝ j (prodTrans g g' p) x‖) := by
  refine (integrable_derivBound g g' j).mono'
    ((contDiff_prodTrans g g' p).continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact norm_iteratedFDeriv_prodTrans_le g g' p j x

theorem integral_prodTrans_le (g g' : Sch (Fin n)) (p : EuclideanSpace ℝ (Fin n)) (j : ℕ) :
    ∫ x, ‖iteratedFDeriv ℝ j (prodTrans g g' p) x‖ ≤ ∫ x, derivBound g g' j x :=
  integral_mono (integrable_prodTrans g g' p j) (integrable_derivBound g g' j)
    (fun x => norm_iteratedFDeriv_prodTrans_le g g' p j x)

theorem fourier_bound (g g' : Sch (Fin n)) (p ξ : EuclideanSpace ℝ (Fin n)) (N m : ℕ) (hm : m ≤ N) :
    ‖ξ‖ ^ m * ‖𝓕 (prodTrans g g' p) ξ‖ ≤
      2 ^ m * ∑ j ∈ Finset.range (N + 1), ∫ x, derivBound g g' j x := by
  have h'f : ∀ (k' m' : ℕ), (k' : ℕ∞) ≤ 0 → (m' : ℕ∞) ≤ (m : ℕ∞) →
      Integrable (fun v => ‖v‖ ^ k' * ‖iteratedFDeriv ℝ m' (prodTrans g g' p) v‖) := by
    intro k' m' hk' _
    have hk0 : k' = 0 := by exact_mod_cast nonpos_iff_eq_zero.mp hk'
    subst hk0
    simpa using integrable_prodTrans g g' p m'
  have key := Real.pow_mul_norm_iteratedFDeriv_fourier_le (f := prodTrans g g' p) (K := 0)
    (N := m) ((contDiff_prodTrans g g' p).of_le (by exact_mod_cast le_top)) h'f (k := 0) (n := m)
    le_rfl le_rfl ξ
  have hsum : (∑ q ∈ Finset.range (0 + 1) ×ˢ Finset.range (m + 1),
      ∫ v, ‖v‖ ^ q.1 * ‖iteratedFDeriv ℝ q.2 (prodTrans g g' p) v‖)
      = ∑ j ∈ Finset.range (m + 1), ∫ v, ‖iteratedFDeriv ℝ j (prodTrans g g' p) v‖ := by
    rw [Finset.sum_product]; simp
  rw [hsum, norm_iteratedFDeriv_zero] at key
  simp only [pow_zero, one_mul, Nat.cast_zero, mul_zero, zero_add] at key
  refine key.trans ?_
  gcongr
  calc ∑ j ∈ Finset.range (m + 1), ∫ v, ‖iteratedFDeriv ℝ j (prodTrans g g' p) v‖
      ≤ ∑ j ∈ Finset.range (N + 1), ∫ v, ‖iteratedFDeriv ℝ j (prodTrans g g' p) v‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
          (fun _ _ _ => integral_nonneg fun _ => norm_nonneg _)
    _ ≤ ∑ j ∈ Finset.range (N + 1), ∫ x, derivBound g g' j x :=
        Finset.sum_le_sum fun j _ => integral_prodTrans_le g g' p j

theorem one_add_pow_le (t : ℝ) (ht : 0 ≤ t) (N : ℕ) : (1 + t) ^ N ≤ 2 ^ N * (1 + t ^ N) := by
  have h1 : 1 + t ≤ 2 * max 1 t := by
    rcases le_total 1 t with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have h2 : (max 1 t) ^ N ≤ 1 + t ^ N := by
    rcases le_total 1 t with h | h
    · rw [max_eq_right h]; linarith [pow_nonneg ht N]
    · rw [max_eq_left h, one_pow]; linarith [pow_nonneg ht N]
  calc (1 + t) ^ N ≤ (2 * max 1 t) ^ N := pow_le_pow_left₀ (by linarith) h1 N
    _ = 2 ^ N * (max 1 t) ^ N := mul_pow _ _ _
    _ ≤ 2 ^ N * (1 + t ^ N) := by gcongr

end GlobalTheory.RealWeil.CoefQDecay

theorem GlobalTheory.RealWeil.coef_qDecay : ∀ (n : ℕ) (g g' : Sch (Fin n)) (N : ℕ), ∃ C : ℝ,
    ∀ w : Fin n ⊕ Fin n → ℝ, ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * (1 + ‖qPart w‖) ^ N ≤ C := by
  intro n g g' N
  open GlobalTheory.RealWeil.CoefQDecay in
  set T := ∑ j ∈ Finset.range (N + 1), ∫ x, derivBound g g' j x with hT
  refine ⟨2 ^ N * (T + 2 ^ N * T), fun w => ?_⟩
  rw [GlobalTheory.RealWeil.CoefQDecay.norm_integral_eq]
  set F := ‖𝓕 (GlobalTheory.RealWeil.CoefQDecay.prodTrans g g' (pPart w)) (-qPart w)‖ with hF
  have h0 := GlobalTheory.RealWeil.CoefQDecay.fourier_bound g g' (pPart w) (-qPart w) N 0 (Nat.zero_le _)
  have hN := GlobalTheory.RealWeil.CoefQDecay.fourier_bound g g' (pPart w) (-qPart w) N N le_rfl
  rw [norm_neg] at hN
  simp only [pow_zero, one_mul] at h0
  have hq := GlobalTheory.RealWeil.CoefQDecay.one_add_pow_le ‖qPart w‖ (norm_nonneg _) N
  have hF0 : 0 ≤ F := norm_nonneg _
  calc F * (1 + ‖qPart w‖) ^ N ≤ F * (2 ^ N * (1 + ‖qPart w‖ ^ N)) := by gcongr
    _ = 2 ^ N * (F + ‖qPart w‖ ^ N * F) := by ring
    _ ≤ 2 ^ N * (T + 2 ^ N * T) := by gcongr
