import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.Growth

open UpperHalfPlane hiding I

def sF (w : ℍ) : ℝ := (1 + ‖(w : ℂ)‖ ^ 2) / w.im

lemma sq_norm_coe (w : ℍ) : ‖(w : ℂ)‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, coe_re, coe_im]
  ring

lemma one_le_sF (w : ℍ) : 1 ≤ sF w := by
  have him := w.im_pos
  rw [sF, le_div_iff₀ him, one_mul, sq_norm_coe]
  nlinarith [sq_nonneg w.re, sq_nonneg (w.im - 1)]

lemma sF_nonneg (w : ℍ) : 0 ≤ sF w := zero_le_one.trans (one_le_sF w)

lemma poly_bound (a b c d x y : ℝ) :
    (c * x + d) ^ 2 + (c * y) ^ 2 + ((a * x + b) ^ 2 + (a * y) ^ 2) ≤
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (1 + (x ^ 2 + y ^ 2)) := by
  nlinarith [sq_nonneg (a - b * x), sq_nonneg (c - d * x), sq_nonneg (b * y), sq_nonneg (d * y)]

lemma normSq_lin (a b : ℝ) (z : ℍ) :
    Complex.normSq ((a : ℂ) * z + b) = (a * z.re + b) ^ 2 + (a * z.im) ^ 2 := by
  simp [Complex.normSq_apply]; ring

lemma sF_smul (g : GL (Fin 2) ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℍ, sF (g • z) ≤ K * sF z := by
  have hD : 0 < |g.det.val| := abs_pos.mpr g.det.ne_zero
  refine ⟨((g 0 0) ^ 2 + (g 0 1) ^ 2 + (g 1 0) ^ 2 + (g 1 1) ^ 2) / |g.det.val|, by positivity, fun z => ?_⟩
  have hN : 0 < Complex.normSq (denom g z) := normSq_denom_pos g z.im_ne_zero
  have him := z.im_pos
  have h1 : sF (g • z) =
      (Complex.normSq (denom g z) + Complex.normSq (num g z)) / (|g.det.val| * z.im) := by
    rw [sF, im_smul_eq_div_normSq, coe_smul, norm_σ, norm_div, div_pow, Complex.sq_norm, Complex.sq_norm]
    field_simp
  have h2 : Complex.normSq (denom g z) + Complex.normSq (num g z) ≤
      ((g 0 0) ^ 2 + (g 0 1) ^ 2 + (g 1 0) ^ 2 + (g 1 1) ^ 2) * (1 + ‖(z : ℂ)‖ ^ 2) := by
    have e1 : Complex.normSq (denom g z) = (g 1 0 * z.re + g 1 1) ^ 2 + (g 1 0 * z.im) ^ 2 :=
      normSq_lin _ _ z
    have e2 : Complex.normSq (num g z) = (g 0 0 * z.re + g 0 1) ^ 2 + (g 0 0 * z.im) ^ 2 :=
      normSq_lin _ _ z
    rw [e1, e2, sq_norm_coe]
    exact poly_bound _ _ _ _ _ _
  rw [h1, sF, div_mul_div_comm]
  exact div_le_div_of_nonneg_right h2 (mul_pos hD him).le

lemma denom_inv (g : GL (Fin 2) ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℍ, ‖denom g z‖⁻¹ ≤ K * sF z := by
  have hq : 0 < (g 1 0) ^ 2 + (g 1 1) ^ 2 := by
    by_contra hc
    push_neg at hc
    have h10 : g 1 0 = 0 := by nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
    have h11 : g 1 1 = 0 := by nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
    have hdet := g.det.ne_zero
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h10, h11] at hdet
  refine ⟨1 + 1 / ((g 1 0) ^ 2 + (g 1 1) ^ 2), by positivity, fun z => ?_⟩
  have him := z.im_pos
  have hm : 0 < ‖denom g z‖ := norm_pos_iff.mpr (denom_ne_zero g z)
  have hN : ‖denom g z‖ ^ 2 = (g 1 0 * z.re + g 1 1) ^ 2 + (g 1 0 * z.im) ^ 2 := by
    rw [Complex.sq_norm]
    exact normSq_lin _ _ z
  have key : ((g 1 0) ^ 2 + (g 1 1) ^ 2) * z.im ^ 2 ≤ ‖denom g z‖ ^ 2 * (1 + ‖(z : ℂ)‖ ^ 2) := by
    rw [hN, sq_norm_coe]
    nlinarith [sq_nonneg (g 1 0 * z.re + g 1 1),
      sq_nonneg ((g 1 0 * z.re + g 1 1) * z.re + g 1 0 * z.im ^ 2)]
  have hK1 : 1 ≤ 1 + 1 / ((g 1 0) ^ 2 + (g 1 1) ^ 2) := by
    have : 0 ≤ 1 / ((g 1 0) ^ 2 + (g 1 1) ^ 2) := by positivity
    linarith
  have hKq : (1 + 1 / ((g 1 0) ^ 2 + (g 1 1) ^ 2)) * ((g 1 0) ^ 2 + (g 1 1) ^ 2) =
      ((g 1 0) ^ 2 + (g 1 1) ^ 2) + 1 := by
    field_simp
  have hT1 : 1 ≤ 1 + ‖(z : ℂ)‖ ^ 2 := by nlinarith [sq_nonneg ‖(z : ℂ)‖]
  set q := (g 1 0) ^ 2 + (g 1 1) ^ 2 with hqdef
  set K := 1 + 1 / q with hKdef
  set T := 1 + ‖(z : ℂ)‖ ^ 2 with hTdef
  set m := ‖denom g z‖ with hmdef
  have h1 : 1 ≤ K ^ 2 * q * T := by
    have e : K ^ 2 * q * T = K * (K * q) * T := by ring
    rw [e, hKq]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK1 (by linarith)) hT1
  have hsq : z.im ^ 2 ≤ (K * T * m) ^ 2 := by
    have e : (K * T * m) ^ 2 = K ^ 2 * T * (m ^ 2 * T) := by ring
    rw [e]
    have hKT : 0 ≤ K ^ 2 * T := by positivity
    nlinarith [mul_le_mul_of_nonneg_left key hKT, mul_le_mul_of_nonneg_right h1 (sq_nonneg z.im)]
  have hP : 0 ≤ K * T * m := by positivity
  have hy : z.im ≤ K * T * m := by nlinarith
  rw [inv_eq_one_div, div_le_iff₀ hm, sF, ← hTdef,
    show K * (T / z.im) * m = (K * T * m) / z.im by ring, le_div_iff₀ him, one_mul]
  exact hy

variable {F : Type} [Field F] [NumberField F]

def sP (z : Hn F) : ℝ := ∏ v, sF (z v)

lemma one_le_sP (z : Hn F) : 1 ≤ sP z := by
  calc (1 : ℝ) = ∏ v, (1 : ℝ) := by simp
    _ ≤ ∏ v, sF (z v) := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun v _ => one_le_sF _)

lemma sP_nonneg (z : Hn F) : 0 ≤ sP z := zero_le_one.trans (one_le_sP z)

lemma gr_iff (f : Hn F → ℂ) : Gr f ↔ ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ z, ‖f z‖ ≤ C * sP z ^ A := by
  rw [Gr.eq_1]
  constructor
  · rintro ⟨C, A, hC⟩
    refine ⟨max C 0, A, le_max_right _ _, fun z => (hC z).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (sP_nonneg z) A)
  · rintro ⟨C, A, -, hC⟩
    exact ⟨C, A, hC⟩

lemma gr_add {f g : Hn F → ℂ} (hf : Gr f) (hg : Gr g) : Gr (f + g) := by
  rw [gr_iff] at hf hg ⊢
  obtain ⟨C1, A1, hC1, h1⟩ := hf
  obtain ⟨C2, A2, hC2, h2⟩ := hg
  refine ⟨C1 + C2, A1 + A2, add_nonneg hC1 hC2, fun z => ?_⟩
  have hP := one_le_sP z
  have e1 : sP z ^ A1 ≤ sP z ^ (A1 + A2) := pow_le_pow_right₀ hP (by omega)
  have e2 : sP z ^ A2 ≤ sP z ^ (A1 + A2) := pow_le_pow_right₀ hP (by omega)
  calc ‖(f + g) z‖ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
    _ ≤ C1 * sP z ^ A1 + C2 * sP z ^ A2 := add_le_add (h1 z) (h2 z)
    _ ≤ C1 * sP z ^ (A1 + A2) + C2 * sP z ^ (A1 + A2) :=
      add_le_add (mul_le_mul_of_nonneg_left e1 hC1) (mul_le_mul_of_nonneg_left e2 hC2)
    _ = (C1 + C2) * sP z ^ (A1 + A2) := by ring

lemma gr_mul {f g : Hn F → ℂ} (hf : Gr f) (hg : Gr g) : Gr (f * g) := by
  rw [gr_iff] at hf hg ⊢
  obtain ⟨C1, A1, hC1, h1⟩ := hf
  obtain ⟨C2, A2, hC2, h2⟩ := hg
  refine ⟨C1 * C2, A1 + A2, mul_nonneg hC1 hC2, fun z => ?_⟩
  calc ‖(f * g) z‖ = ‖f z‖ * ‖g z‖ := norm_mul _ _
    _ ≤ (C1 * sP z ^ A1) * (C2 * sP z ^ A2) :=
      mul_le_mul (h1 z) (h2 z) (norm_nonneg _) (mul_nonneg hC1 (pow_nonneg (sP_nonneg z) _))
    _ = C1 * C2 * sP z ^ (A1 + A2) := by ring

lemma gr_const (c : ℂ) : Gr (fun _ : Hn F => c) := by
  rw [gr_iff]
  exact ⟨‖c‖, 0, norm_nonneg _, fun z => by simp⟩

lemma gr_smul (c : ℂ) {f : Hn F → ℂ} (hf : Gr f) : Gr (c • f) := gr_mul (gr_const c) hf

lemma gr_act (h : GL (Fin 2) (InfinitePlace F → ℝ)) {f : Hn F → ℂ} (hf : Gr f) : Gr (fun z => f (act h z)) := by
  rw [gr_iff] at hf ⊢
  obtain ⟨C, A, hC, hfz⟩ := hf
  choose K hK0 hK using fun v : InfinitePlace F => sF_smul (cmp v h)
  have hact : ∀ z : Hn F, sP (act h z) ≤ (∏ v, K v) * sP z := by
    intro z
    unfold sP
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro v _
      exact sF_nonneg _
    · intro v _
      rw [act.eq_1]
      exact hK v (z v)
  refine ⟨C * (∏ v, K v) ^ A, A,
    mul_nonneg hC (pow_nonneg (Finset.prod_nonneg fun v _ => hK0 v) A), fun z => ?_⟩
  calc ‖f (act h z)‖ ≤ C * sP (act h z) ^ A := hfz _
    _ ≤ C * ((∏ v, K v) * sP z) ^ A :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sP_nonneg _) (hact z) A) hC
    _ = C * (∏ v, K v) ^ A * sP z ^ A := by ring

lemma gr_denom (k : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) :
    Gr (fun z : Hn F => (∏ v, denom (GlobalTheory.HilbertThetaSeries.cmp v h) (z v))⁻¹ ^ k) := by
  rw [gr_iff]
  choose K hK0 hK using fun v : InfinitePlace F => denom_inv (cmp v h)
  refine ⟨(∏ v, K v) ^ k, k, pow_nonneg (Finset.prod_nonneg fun v _ => hK0 v) k, fun z => ?_⟩
  have hb : ‖(∏ v, denom (cmp v h) (z v))⁻¹‖ ≤ (∏ v, K v) * sP z := by
    rw [norm_inv, norm_prod, ← Finset.prod_inv_distrib]
    unfold sP
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro v _
      positivity
    · intro v _
      exact hK v (z v)
  rw [norm_pow, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hb k

lemma hilbertModerateGrowth_unnormalizedSlash (k : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) {f : Hn F → ℂ} (hf : Gr f) : Gr (sl0 k h f) :=
  gr_mul (gr_denom k h) (gr_act h hf)

lemma gr_sl (k : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) {f : Hn F → ℂ} (hf : Gr f) : Gr (sl k h f) :=
  gr_mul (gr_const _) (hilbertModerateGrowth_unnormalizedSlash k h hf)

theorem gr_closed : ∀ (F : Type) [Field F] [NumberField F] (k : ℕ) (f g : Hn F → ℂ) (c : ℂ), Gr f → Gr g → Gr (f + g) ∧ Gr (c • f) ∧ Gr (f * g) ∧ Gr (1 : Hn F → ℂ) ∧ Gr (0 : Hn F → ℂ) ∧ ∀ h : GL (Fin 2) (InfinitePlace F → ℝ), Pos h → Gr (sl0 k h f) ∧ Gr (sl k h f) :=
  fun _ _ _ k _ _ c hf hg =>
    ⟨gr_add hf hg, gr_smul c hf, gr_mul hf hg, gr_const 1, gr_const 0, fun h _ => ⟨hilbertModerateGrowth_unnormalizedSlash k h hf, gr_sl k h hf⟩⟩

end GlobalTheory.HilbertThetaSeries.Growth
