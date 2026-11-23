import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.LogDetSt
import Development.WeilBound.CoreStatements.PluriharmonicCharts.TripleDeriv
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace PositivityTheory.Xgp.gram_grad

theorem inv_entry {k : ℕ} (H : Matrix (Fin k) (Fin k) ℂ) (a : ℝ) (ha : 0 < a) (hH : H.PosDef)
    (h : (H - (a : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef) (p q : Fin k) : ‖H⁻¹ p q‖ ≤ 1 / a := by
  set w : Fin k → ℂ := fun i => H⁻¹ i q with hw
  have hu : IsUnit H.det := isUnit_iff_ne_zero.mpr hH.det_pos.ne'
  have h1 : H *ᵥ w = Pi.single q 1 := by
    ext i
    have := congrFun (congrFun (Matrix.mul_nonsing_inv H hu) i) q
    rw [Matrix.mul_apply] at this
    simp only [mulVec, dotProduct, hw, this, Matrix.one_apply, Pi.single_apply]
  have h2 := h.re_dotProduct_nonneg w
  rw [sub_mulVec, h1, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, dotProduct_single] at h2
  have h3 : star w ⬝ᵥ w = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  rw [h3, smul_eq_mul, ← Complex.ofReal_mul] at h2
  simp only [RCLike.re_to_complex, Complex.sub_re, Complex.ofReal_re, mul_one, Pi.star_apply] at h2
  have h4 : (star (w q)).re ≤ ‖w q‖ := by
    have := Complex.re_le_norm (star (w q))
    rwa [norm_star] at this
  have h5 : ∀ i, ‖w i‖ ^ 2 ≤ ∑ i, ‖w i‖ ^ 2 := fun i =>
    Finset.single_le_sum (f := fun i => ‖w i‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
  have h6 : a * ‖w q‖ ≤ 1 := by
    by_contra hc
    push Not at hc
    have hq : 0 < ‖w q‖ := by
      by_contra h0
      have : ‖w q‖ = 0 := le_antisymm (not_lt.mp h0) (norm_nonneg _)
      rw [this] at hc
      linarith
    nlinarith [h5 q, mul_le_mul_of_nonneg_left (h5 q) ha.le]
  have h7 : (a * ‖w p‖) ^ 2 ≤ 1 := by
    have e1 := mul_le_mul_of_nonneg_left (h5 p) ha.le
    have e2 : a * ‖w p‖ ^ 2 ≤ ‖w q‖ := by linarith
    have e3 := mul_le_mul_of_nonneg_left e2 ha.le
    nlinarith
  have h8 : a * ‖w p‖ ≤ 1 := by
    nlinarith [mul_nonneg ha.le (norm_nonneg (w p))]
  rw [le_div_iff₀ ha]
  show ‖w p‖ * a ≤ 1
  linarith

theorem mul_entry {l m n : ℕ} (A : Matrix (Fin l) (Fin m) ℂ) (B : Matrix (Fin m) (Fin n) ℂ) (α β : ℝ)
    (hα : 0 ≤ α) (hA : ∀ p q, ‖A p q‖ ≤ α) (hB : ∀ p q, ‖B p q‖ ≤ β) (p : Fin l) (q : Fin n) :
    ‖(A * B) p q‖ ≤ m * (α * β) := by
  rw [Matrix.mul_apply]
  calc _ ≤ ∑ j, ‖A p j * B j q‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin m, α * β := Finset.sum_le_sum fun j _ => by
        rw [norm_mul]; exact mul_le_mul (hA p j) (hB j q) (norm_nonneg _) hα
    _ = _ := by simp

theorem triple_entry {n k : ℕ} (U W : Matrix (Fin n) (Fin k) ℂ) (G : Matrix (Fin n) (Fin n) ℂ) (α β γ : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hU : ∀ p q, ‖U p q‖ ≤ α) (hG : ∀ p q, ‖G p q‖ ≤ β) (hW : ∀ p q, ‖W p q‖ ≤ γ)
    (p q : Fin k) : ‖(Uᴴ * G * W) p q‖ ≤ n * (n * (α * β) * γ) :=
  mul_entry _ _ _ _ (by positivity)
    (mul_entry _ _ _ _ hα (fun p q => by rw [conjTranspose_apply, norm_star]; exact hU q p) hG) hW p q

end PositivityTheory.Xgp.gram_grad

theorem PositivityTheory.Xgp.t_gram_grad : ∀ (n k : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (G : E → Matrix (Fin n) (Fin n) ℂ) (V : E → Matrix (Fin n) (Fin k) ℂ) (x : E) (a M : ℝ), 0 < a → 0 ≤ M → (∀ p q, DifferentiableAt ℝ (fun y => G y p q) x) → (∀ p q, DifferentiableAt ℝ (fun y => V y p q) x) → (∀ᶠ y in nhds x, (G y).PosDef ∧ LinearIndependent ℂ (V y)ᵀ) → ((V x)ᴴ * G x * V x - (a : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef → (∀ p q, ‖G x p q‖ ≤ M ∧ ‖fderiv ℝ (fun y => G y p q) x‖ ≤ M) → (∀ p q, ‖V x p q‖ ≤ M ∧ ‖fderiv ℝ (fun y => V y p q) x‖ ≤ M) → ‖fderiv ℝ (fun y => Real.log ((V y)ᴴ * G y * V y).det.re) x‖ ≤ 3 * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 * M ^ 3 / a := by
  intro n k E _ _ G V x a M ha hM hG hV hev hpsd bG bV
  by_cases hd : DifferentiableAt ℝ (fun y => Real.log ((V y)ᴴ * G y * V y).det.re) x
  swap
  · rw [fderiv_zero_of_not_differentiableAt hd, norm_zero]
    positivity
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  obtain ⟨hGx, hVx⟩ := hev.self_of_nhds
  have hpos : ((V x)ᴴ * G x * V x).PosDef :=
    hGx.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff.mpr hVx)
  let G' : Matrix (Fin n) (Fin n) ℂ := fun p q => fderiv ℝ (fun y => G y p q) x v
  let V' : Matrix (Fin n) (Fin k) ℂ := fun p q => fderiv ℝ (fun y => V y p q) x v
  have h1 := PositivityTheory.Xgp.gram_grad.triple_deriv (fun s : ℝ => G (x + s • v)) (fun s : ℝ => V (x + s • v)) G' V' 0
    (fun p q => PositivityTheory.Xgp.gram_grad.line_deriv _ x (hG p q) v)
    (fun p q => PositivityTheory.Xgp.gram_grad.line_deriv _ x (hV p q) v)
  have h2 := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_log_det
    (fun s : ℝ => (V (x + s • v))ᴴ * G (x + s • v) * V (x + s • v)) _ 0 h1 (by simpa using hpos)
  have h3 := (PositivityTheory.Xgp.gram_grad.line_deriv _ x hd v).unique h2
  simp only [zero_smul, add_zero] at h3
  rw [h3]
  have hv := norm_nonneg v
  have bG' : ∀ p q, ‖G' p q‖ ≤ M * ‖v‖ := fun p q =>
    ((fderiv ℝ (fun y => G y p q) x).le_opNorm v).trans (mul_le_mul_of_nonneg_right (bG p q).2 hv)
  have bV' : ∀ p q, ‖V' p q‖ ≤ M * ‖v‖ := fun p q =>
    ((fderiv ℝ (fun y => V y p q) x).le_opNorm v).trans (mul_le_mul_of_nonneg_right (bV p q).2 hv)
  have b3 : ∀ p q, ‖(V'ᴴ * G x * V x + (V x)ᴴ * G' * V x + (V x)ᴴ * G x * V') p q‖ ≤
      3 * (n : ℝ) ^ 2 * M ^ 3 * ‖v‖ := by
    intro p q
    have t1 := PositivityTheory.Xgp.gram_grad.triple_entry V' (V x) (G x) _ _ _ (by positivity) hM bV'
      (fun p q => (bG p q).1) (fun p q => (bV p q).1) p q
    have t2 := PositivityTheory.Xgp.gram_grad.triple_entry (V x) (V x) G' _ _ _ hM (by positivity)
      (fun p q => (bV p q).1) bG' (fun p q => (bV p q).1) p q
    have t3 := PositivityTheory.Xgp.gram_grad.triple_entry (V x) V' (G x) _ _ _ hM hM
      (fun p q => (bV p q).1) (fun p q => (bG p q).1) bV' p q
    rw [Matrix.add_apply, Matrix.add_apply]
    refine norm_add₃_le.trans ?_
    nlinarith
  have b4 := PositivityTheory.Xgp.gram_grad.mul_entry _ _ _ _ (by positivity)
    (PositivityTheory.Xgp.gram_grad.inv_entry _ a ha hpos hpsd) b3
  refine (Complex.abs_re_le_norm _).trans ?_
  unfold Matrix.trace
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => b4 i i).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
