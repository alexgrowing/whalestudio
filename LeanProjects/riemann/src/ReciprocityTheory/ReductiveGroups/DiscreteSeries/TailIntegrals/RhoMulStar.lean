import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Imports

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux

private lemma rho_den (t : ℝ) : ((1 + t ^ 2 : ℝ) : ℂ) ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr (by positivity)

private theorem norm_rho (t : ℝ) : ‖rho t‖ = 1 := by
  have h2 : ‖(1 + (t : ℂ) * Complex.I)‖ ^ 2 = 1 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp
    ring
  have hd : ‖((1 + t ^ 2 : ℝ) : ℂ)‖ = 1 + t ^ 2 := by
    exact Complex.norm_of_nonneg (by positivity)
  unfold rho
  rw [norm_div, norm_pow, h2, hd, div_self (by positivity)]

private theorem rho_mul_star (t : ℝ) : rho t * star (rho t) = 1 := by
  have h := norm_rho t
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]
  simp

private theorem rho_mp (t : ℝ) : MeasurePreserving (fun z : ℂ => rho t * z) volume volume := by
  have h1 := rho_mul_star t
  have h1' : star (rho t) * rho t = 1 := by rw [mul_comm]; exact h1
  have hn := norm_rho t
  let e : ℂ ≃ₗᵢ[ℝ] ℂ :=
    { toFun := fun z => rho t * z
      invFun := fun z => star (rho t) * z
      map_add' := fun x y => mul_add _ x y
      map_smul' := fun r x => by
        exact mul_smul_comm r (rho t) x
      left_inv := fun z => by
        show star (rho t) * (rho t * z) = z
        rw [← mul_assoc, h1', one_mul]
      right_inv := fun z => by
        show rho t * (star (rho t) * z) = z
        rw [← mul_assoc, h1, one_mul]
      norm_map' := fun z => by
        show ‖rho t * z‖ = ‖z‖
        rw [norm_mul, hn, one_mul] }
  exact e.measurePreserving

theorem rot_mp {p m : ℕ} (t : ℝ) : MeasurePreserving (rot (p := p) (m := m) t) volume volume := by
  have h0 := rho_mp t
  have hp : ∀ n : ℕ, MeasurePreserving (fun (v : Fin n → ℂ) (j : Fin n) => rho t * v j) volume volume := by
    intro n
    exact measurePreserving_pi (fun _ => volume) (fun _ => volume) (fun _ => h0)
  have h := (hp p).prod ((hp p).prod ((hp m).prod (MeasurePreserving.id (volume : Measure ℝ))))
  exact h

private theorem continuous_rho_tail_integrals : Continuous rho := by
  unfold rho
  exact ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).pow 2).div
    (Complex.continuous_ofReal.comp (continuous_const.add (continuous_id.pow 2))) rho_den

theorem rot_meas {p m : ℕ} : Measurable (fun q : ℝ × Xp p m => rot q.1 q.2) := by
  have hu : Continuous rho := continuous_rho_tail_integrals
  have hc : Continuous (fun q : ℝ × ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m => rot q.1 q.2) := by
    unfold rot
    fun_prop
  exact hc.measurable

theorem de_rot {p m : ℕ} (t : ℝ) (x : Xp p m) (l : Fin (p + 1)) : de (rot t x) l = de x l := by
  have hn : ∀ z : ℂ, ‖rho t * z‖ = ‖z‖ := fun z => by rw [norm_mul, norm_rho, one_mul]
  have hc : ∀ a b : ℂ, rho t * a * star (rho t * b) = a * star b := by
    intro a b
    rw [star_mul']
    linear_combination (a * star b) * rho_mul_star t
  simp only [ReciprocityTheory.ChartRestriction.DS.Xi.de, ReciprocityTheory.ChartRestriction.DS.Xi.Lsq, ReciprocityTheory.ChartRestriction.DS.Xi.rhoSq, ReciprocityTheory.ChartRestriction.DS.Xi.bco, rot, hn, hc]

theorem linF_rot {p m : ℕ} (η η' : Fin p → ℂ) (ζ : Fin m → ℂ) (t : ℝ) (x : Xp p m) :
    linF η η' ζ (rot t x) = rho t * linF η η' ζ x := by
  simp only [ReciprocityTheory.ChartRestriction.DS.Xi.linF, rot]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun j _ => ?_ <;> ring

private lemma key (t c₀ : ℝ) (X : ℂ) : 2 * (rho t * X).im + c₀ =
    ((2 * X.im + c₀) + 4 * X.re * t + (c₀ - 2 * X.im) * t ^ 2) / (1 + t ^ 2) := by
  have hd : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
  have key : rho t * ((1 + t ^ 2 : ℝ) : ℂ) = (1 + t * Complex.I) ^ 2 := by
    unfold rho
    exact div_mul_cancel₀ _ (rho_den t)
  have hre : (rho t).re = (1 - t ^ 2) / (1 + t ^ 2) := by
    rw [eq_div_iff hd]
    have := congrArg Complex.re key
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, sq, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, Complex.mul_im, Complex.I_re, Complex.I_im] at this
    linear_combination this
  have him : (rho t).im = (2 * t) / (1 + t ^ 2) := by
    rw [eq_div_iff hd]
    have := congrArg Complex.im key
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, sq, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, Complex.mul_im, Complex.I_re, Complex.I_im] at this
    linear_combination this
  rw [Complex.mul_im, hre, him]
  field_simp
  ring

private theorem rpow_neg_le_rpow_neg_of_pos_of_le {x y δ : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hδ : 0 ≤ δ) : y ^ (-δ) ≤ x ^ (-δ) := by
  rw [Real.rpow_neg hx.le, Real.rpow_neg (hx.le.trans hxy)]
  have ha : 0 < x ^ δ := Real.rpow_pos_of_pos hx δ
  have hb : x ^ δ ≤ y ^ δ := Real.rpow_le_rpow hx.le hxy hδ
  exact inv_anti₀ ha hb

private theorem complex_norm_le_abs_re_add_abs_im (X : ℂ) : ‖X‖ ≤ |X.re| + |X.im| := by
  calc ‖X‖ = ‖(X.re : ℂ) + X.im * Complex.I‖ := by rw [Complex.re_add_im]
    _ ≤ ‖(X.re : ℂ)‖ + ‖(X.im : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |X.re| + |X.im| := by simp

private theorem complex_norm_ofReal_eq_abs (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  simp

theorem rot_weight (hS : SUB) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℂ) (c₀ : ℝ),
      ∫⁻ t in Icc (1 : ℝ) 2, ENNReal.ofReal ((1 + |2 * (rho t * X).im + c₀|) ^ (-δ)) ≤
        ENNReal.ofReal (C * (1 + |c₀|) ^ (-δ / 4) * (1 + ‖X‖) ^ (-δ / 4)) := by
  obtain ⟨C₁, hC₁⟩ := hS δ hδ0 hδ1
  set K : ℝ := (5 : ℝ)⁻¹ ^ (-δ) with hKdef
  have hK : 0 < K := by positivity
  have hM : 0 < max C₁ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨K * max C₁ 1, mul_pos hK hM, fun X c₀ => ?_⟩
  set A : ℝ := 2 * X.im + c₀ with hA
  set B : ℝ := 4 * X.re with hB
  set D : ℝ := c₀ - 2 * X.im with hD
  set c : Fin 3 → ℂ := ![(A : ℂ), (B : ℂ), (D : ℂ)] with hc
  have c0 : c 0 = (A : ℂ) := rfl
  have c1 : c 1 = (B : ℂ) := rfl
  have c2 : c 2 = (D : ℂ) := rfl
  set N : ℝ := ‖c‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  have hAN : |A| ≤ N := by rw [← complex_norm_ofReal_eq_abs, ← c0]; exact norm_le_pi_norm c 0
  have hBN : |B| ≤ N := by rw [← complex_norm_ofReal_eq_abs, ← c1]; exact norm_le_pi_norm c 1
  have hDN : |D| ≤ N := by rw [← complex_norm_ofReal_eq_abs, ← c2]; exact norm_le_pi_norm c 2
  have hc₀ : |c₀| ≤ N := by
    rw [abs_le] at hAN hDN ⊢
    constructor <;> linarith [hAN.1, hAN.2, hDN.1, hDN.2]
  have hX : ‖X‖ ≤ N := by
    have h1 := complex_norm_le_abs_re_add_abs_im X
    have hre : |X.re| ≤ N / 4 := by
      rw [abs_le] at hBN ⊢; constructor <;> linarith [hBN.1, hBN.2]
    have him : |X.im| ≤ N / 2 := by
      rw [abs_le] at hAN hDN ⊢; constructor <;> linarith [hAN.1, hAN.2, hDN.1, hDN.2]
    linarith
  have hpt : ∀ t ∈ Icc (1 : ℝ) 2,
      ENNReal.ofReal ((1 + |2 * (rho t * X).im + c₀|) ^ (-δ)) ≤
        ENNReal.ofReal K * ENNReal.ofReal ((1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ)) := by
    intro t ht
    rw [← ENNReal.ofReal_mul hK.le]
    apply ENNReal.ofReal_le_ofReal
    have hq : c 0 + c 1 * t + c 2 * t ^ 2 = ((A + B * t + D * t ^ 2 : ℝ) : ℂ) := by
      rw [c0, c1, c2]; push_cast; ring
    rw [hq, complex_norm_ofReal_eq_abs, key]
    set q : ℝ := A + B * t + D * t ^ 2 with hqdef
    have hdpos : 0 < 1 + t ^ 2 := by positivity
    have hd5 : 1 + t ^ 2 ≤ 5 := by nlinarith [ht.1, ht.2]
    rw [hKdef, ← Real.mul_rpow (by norm_num) (by positivity)]
    apply rpow_neg_le_rpow_neg_of_pos_of_le (by positivity) _ hδ0.le
    rw [abs_div, abs_of_pos hdpos]
    have hw0 : 0 ≤ |q| / (1 + t ^ 2) := div_nonneg (abs_nonneg _) hdpos.le
    have hwd : |q| / (1 + t ^ 2) * (1 + t ^ 2) = |q| := by
      exact div_mul_cancel₀ _ hdpos.ne'
    have := mul_le_mul_of_nonneg_left hd5 hw0
    linarith
  have hfin : C₁ * (1 + N) ^ (-δ / 2) ≤ max C₁ 1 * ((1 + |c₀|) ^ (-δ / 4) * (1 + ‖X‖) ^ (-δ / 4)) := by
    have hpos : 0 < 1 + N := by linarith
    have e : (1 + N) ^ (-δ / 2) = (1 + N) ^ (-δ / 4) * (1 + N) ^ (-δ / 4) := by
      rw [← Real.rpow_add hpos]; congr 1; ring
    have hδ4 : 0 ≤ δ / 4 := by positivity
    have ha : (1 + N) ^ (-δ / 4) ≤ (1 + |c₀|) ^ (-δ / 4) := by
      rw [neg_div]; exact rpow_neg_le_rpow_neg_of_pos_of_le (by positivity) (by linarith) hδ4
    have hb : (1 + N) ^ (-δ / 4) ≤ (1 + ‖X‖) ^ (-δ / 4) := by
      rw [neg_div]; exact rpow_neg_le_rpow_neg_of_pos_of_le (by positivity) (by linarith) hδ4
    have hab : (1 + N) ^ (-δ / 2) ≤ (1 + |c₀|) ^ (-δ / 4) * (1 + ‖X‖) ^ (-δ / 4) := by
      rw [e]; exact mul_le_mul ha hb (by positivity) (by positivity)
    exact mul_le_mul (le_max_left _ _) hab (by positivity) hM.le
  have hmono : ∫⁻ t in Icc (1 : ℝ) 2, ENNReal.ofReal ((1 + |2 * (rho t * X).im + c₀|) ^ (-δ)) ≤
      ∫⁻ t in Icc (1 : ℝ) 2, ENNReal.ofReal K * ENNReal.ofReal ((1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ)) := by
    exact setLIntegral_mono' measurableSet_Icc hpt
  calc ∫⁻ t in Icc (1 : ℝ) 2, ENNReal.ofReal ((1 + |2 * (rho t * X).im + c₀|) ^ (-δ))
      ≤ ∫⁻ t in Icc (1 : ℝ) 2, ENNReal.ofReal K * ENNReal.ofReal ((1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ)) := hmono
    _ = ENNReal.ofReal K * ∫⁻ t in Icc (1 : ℝ) 2, ENNReal.ofReal ((1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal (C₁ * (1 + ‖c‖) ^ (-δ / 2)) := by
        gcongr
        exact hC₁ c
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal (max C₁ 1 * ((1 + |c₀|) ^ (-δ / 4) * (1 + ‖X‖) ^ (-δ / 4))) := by
        gcongr
    _ = ENNReal.ofReal (K * max C₁ 1 * (1 + |c₀|) ^ (-δ / 4) * (1 + ‖X‖) ^ (-δ / 4)) := by
        rw [← ENNReal.ofReal_mul hK.le]; congr 1; ring

end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi
