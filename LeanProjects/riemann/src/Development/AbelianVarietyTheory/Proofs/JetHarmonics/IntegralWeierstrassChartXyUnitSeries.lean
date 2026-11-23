import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UwEllipticFlow

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.ChartXY

variable {q : ℕ} [Fact q.Prime]

def IntLt (n : ℕ) (f : ℂ_[q]⟦X⟧) : Prop := ∀ m < n, ‖coeff m f‖ ≤ 1

lemma IntLt.add {n : ℕ} {f g : ℂ_[q]⟦X⟧} (hf : IntLt n f) (hg : IntLt n g) : IntLt n (f + g) := by
  intro m hm
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf m hm) (hg m hm))

lemma IntLt.mul {n : ℕ} {f g : ℂ_[q]⟦X⟧} (hf : IntLt n f) (hg : IntLt n g) : IntLt n (f * g) := by
  intro m hm
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  rintro ⟨i, j⟩ hij
  replace hij : i + j = m := by simpa using hij
  simp only
  rw [norm_mul]
  exact mul_le_one₀ (hf i (by omega)) (norm_nonneg _) (hg j (by omega))

lemma IntLt.mul_succ {n : ℕ} {f g : ℂ_[q]⟦X⟧} (hf : IntLt n f) (hg : IntLt n g)
    (hf0 : constantCoeff f = 0) (hg0 : constantCoeff g = 0) : IntLt (n + 1) (f * g) := by
  intro m hm
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  rintro ⟨i, j⟩ hij
  replace hij : i + j = m := by simpa using hij
  simp only
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [hf0]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [hg0]
  rw [norm_mul]
  exact mul_le_one₀ (hf i (by omega)) (norm_nonneg _) (hg j (by omega))

lemma intLt_C {n : ℕ} {a : ℂ_[q]} (ha : ‖a‖ ≤ 1) : IntLt n (C a : ℂ_[q]⟦X⟧) := by
  intro m _
  rw [coeff_C]
  split_ifs
  · exact ha
  · simp

lemma bd_iff {f : ℂ_[q]⟦X⟧} : Bd 1 f ↔ ∀ n, IntLt n f :=
  ⟨fun h _ m _ => h m, fun h m => h (m + 1) m (Nat.lt_succ_self m)⟩

lemma bd_w {U W : ℂ_[q]⟦X⟧} {a₁ a₂ a₃ a₄ a₆ : ℂ_[q]} (h₁ : ‖a₁‖ ≤ 1) (h₂ : ‖a₂‖ ≤ 1) (h₃ : ‖a₃‖ ≤ 1)
    (h₄ : ‖a₄‖ ≤ 1) (h₆ : ‖a₆‖ ≤ 1) (hU : Bd 1 U) (hU0 : constantCoeff U = 0) (hW0 : constantCoeff W = 0)
    (h : W = U * U * U + W * (C a₁ * U + C a₂ * U * U + C a₃ * W + C a₄ * U * W + C a₆ * W * W)) : Bd 1 W := by
  rw [bd_iff] at hU ⊢
  intro n
  induction n with
  | zero => intro m hm; omega
  | succ n ih =>
    rw [h]
    refine (((hU _).mul (hU _)).mul (hU _)).add (IntLt.mul_succ ih ?_ hW0 (by simp [hU0, hW0]))
    exact (((((intLt_C h₁).mul (hU _)).add (((intLt_C h₂).mul (hU _)).mul (hU _))).add
      ((intLt_C h₃).mul ih)).add (((intLt_C h₄).mul (hU _)).mul ih)).add (((intLt_C h₆).mul ih).mul ih)

section Hat
variable (ι : ℂ ≃+* ℂ_[q]) {ℓ : ℂ_[q]⟦X⟧} (hℓ : constantCoeff ℓ = 0)
include hℓ

lemma hat_add {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0) :
    hat ι ℓ (fun z => F z + G z) = hat ι ℓ F + hat ι ℓ G :=
  ((GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hℓ).1 F G hF hG).1

lemma hat_mul {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0) :
    hat ι ℓ (fun z => F z * G z) = hat ι ℓ F * hat ι ℓ G :=
  ((GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hℓ).1 F G hF hG).2.1

lemma hat_congr {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0)
    (h : ∀ᶠ z in 𝓝[≠] (0 : ℂ), F z = G z) : hat ι ℓ F = hat ι ℓ G :=
  ((GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hℓ).1 F G hF hG).2.2.1 h

lemma hat_const (c : ℂ) : hat ι ℓ (fun _ => c) = C (ι c) :=
  (GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hℓ).2.1 c

lemma hat_pow {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (n : ℕ) :
    hat ι ℓ (fun z => F z ^ n) = hat ι ℓ F ^ n := by
  induction n with
  | zero => simpa using hat_const ι hℓ 1
  | succ n ih =>
    simp only [pow_succ]
    rw [hat_mul ι hℓ (F := fun z => F z ^ n) (hF.fun_pow n) hF, ih]

lemma hat_sum (s : Finset ℕ) {F : ℕ → ℂ → ℂ} (hF : ∀ i, AnalyticAt ℂ (F i) 0) :
    hat ι ℓ (fun z => ∑ i ∈ s, F i z) = ∑ i ∈ s, hat ι ℓ (F i) := by
  induction s using Finset.induction_on with
  | empty => simpa using hat_const ι hℓ 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [hat_add ι hℓ (G := fun z => ∑ i ∈ s, F i z) (hF a)
      (Finset.analyticAt_fun_sum s fun i _ => hF i), ih]

end Hat

noncomputable def homog (D : Polynomial ℂ) (j : ℕ) (u w : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ i ∈ Finset.range (j + 1), D.coeff i * (u z ^ i * w z ^ (j - i))

lemma homog_analytic (D : Polynomial ℂ) (j : ℕ) {u w : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hw : AnalyticAt ℂ w 0) :
    AnalyticAt ℂ (homog D j u w) 0 := by
  unfold homog
  exact Finset.analyticAt_fun_sum _ fun i _ => by fun_prop

lemma homog_eq {D : Polynomial ℂ} {j : ℕ} (hD : D.natDegree ≤ j) {u w : ℂ → ℂ} {z x : ℂ} (h : x * w z = u z) :
    homog D j u w z = D.eval x * w z ^ j := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hD), Finset.sum_mul, homog]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  rw [← h, Nat.add_sub_cancel_left]
  ring

lemma hat_homog (ι : ℂ ≃+* ℂ_[q]) {ℓ : ℂ_[q]⟦X⟧} (hℓ : constantCoeff ℓ = 0) (D : Polynomial ℂ) (j : ℕ)
    {u w : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hw : AnalyticAt ℂ w 0) {v ys : ℂ_[q]⟦X⟧}
    (hU : hat ι ℓ u = X * v) (hW : hat ι ℓ w * ys = X ^ 3) :
    hat ι ℓ (homog D j u w) * ys ^ j =
      X ^ j * ∑ i ∈ Finset.range (j + 1), C (ι (D.coeff i)) * X ^ (2 * (j - i)) * (v * ys) ^ i := by
  have := hat_sum ι hℓ (Finset.range (j + 1)) (F := fun i z => D.coeff i * (u z ^ i * w z ^ (j - i)))
    (fun i => by fun_prop)
  unfold homog
  rw [this, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  rw [hat_mul ι hℓ (F := fun _ => D.coeff i) (G := fun z => u z ^ i * w z ^ (i + m - i)) (by fun_prop) (by fun_prop),
    hat_mul ι hℓ (F := fun z => u z ^ i) (G := fun z => w z ^ (i + m - i)) (by fun_prop) (by fun_prop),
    hat_pow ι hℓ hu, hat_pow ι hℓ hw, hat_const ι hℓ, hU, Nat.add_sub_cancel_left]
  calc _ = C (ι (D.coeff i)) * X ^ i * (v * ys) ^ i * (hat ι ℓ w * ys) ^ m := by ring
    _ = _ := by rw [hW]; ring

theorem chart_xy : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧), M.Chart ℓ → coeff 1 ℓ ≠ 0 ∧ ∃ v xs ys : ℂ_[q]⟦X⟧, Bd 1 v ∧ Bd 1 xs ∧ Bd 1 ys ∧ ‖constantCoeff v‖ = 1 ∧ ‖constantCoeff xs‖ = 1 ∧ ‖constantCoeff ys‖ = 1 ∧ hat M.ι ℓ M.u = X * v ∧ hat M.ι ℓ M.w * ys = -X ^ 3 ∧ xs = -v * ys ∧ ∀ (F : ℂ → ℂ) (A B : Polynomial ℂ) (k : ℕ), AnalyticAt ℂ F 0 → A.natDegree ≤ k → B.natDegree ≤ k → ∀ G : ℂ → ℂ, AnalyticAt ℂ G 0 → ∀ (D : Polynomial ℂ) (j : ℕ), D.natDegree ≤ j → (∀ᶠ z in 𝓝[≠] (0 : ℂ), F z * D.eval (M.x z) = G z * (A.eval (M.x z) + B.eval (M.x z) * M.y z)) → hat M.ι ℓ F * X ^ (2 * k + 3) * (∑ i ∈ Finset.range (j + 1), C (M.ι (D.coeff i)) * X ^ (2 * (j - i)) * xs ^ i) = hat M.ι ℓ G * X ^ (2 * j) * ∑ i ∈ Finset.range (k + 1), (C (M.ι (A.coeff i)) * X ^ (2 * (k - i) + 3) * xs ^ i + C (M.ι (B.coeff i)) * X ^ (2 * (k - i)) * xs ^ i * ys) := by
  rintro q _ M ℓ ⟨hok, hℓ, hU, hU1⟩
  obtain ⟨-, -, -, -, hu0, hw0, -, -, hs⟩ := GlobalTheory.MomOne.uw_elliptic_flow q M hok
  obtain ⟨hu, hw, -, -, hxy, heq⟩ := hs 0 (Or.inl (zero_mem _))
  obtain ⟨-, h₁, h₂, h₃, h₄, h₆, -⟩ := hok
  obtain ⟨-, -, -, hc0, hder, -⟩ := GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι ℓ hℓ
  obtain ⟨hring, -, hinv, -⟩ := GlobalTheory.MomOne.sup_norm_laws q
  have hU0 : constantCoeff (hat M.ι ℓ M.u) = 0 := by rw [hc0, hu0, map_zero]
  have hW0 : constantCoeff (hat M.ι ℓ M.w) = 0 := by rw [hc0, hw0, map_zero]
  refine ⟨?_, ?_⟩
  · intro h0
    have := congrArg (coeff 0) (hder M.u hu)
    rw [coeff_derivative, coeff_zero_eq_constantCoeff_apply, map_mul, ← coeff_zero_eq_constantCoeff_apply,
      coeff_derivative] at this
    simp only [zero_add, h0, Nat.cast_zero, mul_one, zero_mul] at this
    rw [this] at hU1
    simp at hU1
  obtain ⟨v, hv⟩ := X_dvd_iff.mpr hU0
  have hvc : ∀ n, coeff n v = coeff (n + 1) (hat M.ι ℓ M.u) := fun n => by rw [hv, coeff_succ_X_mul]
  have hvB : Bd 1 v := fun n => by rw [hvc]; exact hU _
  have hv0 : ‖constantCoeff v‖ = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hvc]; exact hU1
  have hv0' : constantCoeff v ≠ 0 := by
    intro h; rw [h] at hv0; simp at hv0
  have hvi : v * v⁻¹ = 1 := PowerSeries.mul_inv_cancel v hv0'
  have hviB : Bd 1 v⁻¹ := hinv v _ hvB hv0 hvi
  have hWeq : hat M.ι ℓ M.w = hat M.ι ℓ M.u * hat M.ι ℓ M.u * hat M.ι ℓ M.u + hat M.ι ℓ M.w *
      (C M.W.a₁ * hat M.ι ℓ M.u + C M.W.a₂ * hat M.ι ℓ M.u * hat M.ι ℓ M.u + C M.W.a₃ * hat M.ι ℓ M.w
        + C M.W.a₄ * hat M.ι ℓ M.u * hat M.ι ℓ M.w + C M.W.a₆ * hat M.ι ℓ M.w * hat M.ι ℓ M.w) := by
    have hc : ∀ a : ℂ_[q], C a = hat M.ι ℓ (fun _ => M.ι.symm a) := fun a => by
      rw [hat_const M.ι hℓ, RingEquiv.apply_symm_apply]
    simp only [hc]
    simp (disch := fun_prop) only [← hat_mul M.ι hℓ, ← hat_add M.ι hℓ]
    refine hat_congr M.ι hℓ hw (by fun_prop) ?_
    filter_upwards [nhdsWithin_le_nhds heq] with z hz
    linear_combination hz.1
  have hWB : Bd 1 (hat M.ι ℓ M.w) := bd_w h₁ h₂ h₃ h₄ h₆ hU hU0 hW0 hWeq
  set Q := C M.W.a₁ * hat M.ι ℓ M.u + C M.W.a₂ * hat M.ι ℓ M.u * hat M.ι ℓ M.u + C M.W.a₃ * hat M.ι ℓ M.w
        + C M.W.a₄ * hat M.ι ℓ M.u * hat M.ι ℓ M.w + C M.W.a₆ * hat M.ι ℓ M.w * hat M.ι ℓ M.w with hQ
  have hQ0 : constantCoeff Q = 0 := by simp [hQ, hU0, hW0]
  have hQB : Bd 1 Q := by
    rw [bd_iff] at hU hWB ⊢
    intro n
    exact (((((intLt_C h₁).mul (hU _)).add (((intLt_C h₂).mul (hU _)).mul (hU _))).add
      ((intLt_C h₃).mul (hWB _))).add (((intLt_C h₄).mul (hU _)).mul (hWB _))).add
      (((intLt_C h₆).mul (hWB _)).mul (hWB _))
  set ys := (C 1 + C (-1) * Q) * (v⁻¹ * v⁻¹ * v⁻¹) with hys
  have hysB : Bd 1 ys := by
    rw [bd_iff] at hQB hviB ⊢
    intro n
    exact ((intLt_C (by simp)).add ((intLt_C (by simp)).mul (hQB _))).mul
      (((hviB _).mul (hviB _)).mul (hviB _))
  have hys0 : ‖constantCoeff ys‖ = 1 := by
    simp [hys, hQ0, hv0]
  have hWys : hat M.ι ℓ M.w * ys = X ^ 3 := by
    have h1 : hat M.ι ℓ M.w * (1 - Q) = (X * v) ^ 3 := by
      rw [← hv]; linear_combination hWeq
    calc hat M.ι ℓ M.w * ys = hat M.ι ℓ M.w * (1 - Q) * v⁻¹ ^ 3 := by
          rw [hys, map_neg, map_one]; ring
      _ = X ^ 3 * (v * v⁻¹) ^ 3 := by rw [h1]; ring
      _ = X ^ 3 := by rw [hvi]; ring
  refine ⟨v, v * ys, -ys, hvB, ?_, fun n => by simpa using hysB n, hv0, ?_, by simpa using hys0, hv,
    by rw [mul_neg, hWys], by ring, ?_⟩
  · rw [bd_iff] at hvB hysB ⊢
    exact fun n => (hvB n).mul (hysB n)
  · rw [map_mul, norm_mul, hv0, hys0, mul_one]
  intro F A B k hF hA hB G hG D j hD h
  clear_value ys Q
  clear hs heq hder hring hinv
  have hAa := homog_analytic A k hu hw
  have hBa := homog_analytic B k hu hw
  have hDa := homog_analytic D j hu hw
  have key : hat M.ι ℓ F * hat M.ι ℓ (homog D j M.u M.w) * hat M.ι ℓ M.w ^ (k + 1)
      + hat M.ι ℓ G * hat M.ι ℓ M.w ^ j * hat M.ι ℓ (homog B k M.u M.w)
      = hat M.ι ℓ G * hat M.ι ℓ M.w ^ j * (hat M.ι ℓ (homog A k M.u M.w) * hat M.ι ℓ M.w) := by
    rw [← hat_pow M.ι hℓ hw, ← hat_pow M.ι hℓ hw]
    simp (disch := fun_prop) only [← hat_mul M.ι hℓ, ← hat_add M.ι hℓ]
    refine hat_congr M.ι hℓ (by fun_prop) (by fun_prop) ?_
    filter_upwards [h, hxy] with z hz ⟨_, _, hx, hy⟩
    rw [homog_eq hA hx, homog_eq hB hx, homog_eq hD hx]
    linear_combination M.w z ^ (j + k + 1) * hz
      + G z * M.w z ^ j * (B.eval (M.x z)) * M.w z ^ k * hy
  have eA := hat_homog M.ι hℓ A k hu hw hv hWys
  have eB := hat_homog M.ι hℓ B k hu hw hv hWys
  have eD := hat_homog M.ι hℓ D j hu hw hv hWys
  have hsum : ∑ i ∈ Finset.range (k + 1), (C (M.ι (A.coeff i)) * X ^ (2 * (k - i) + 3) * (v * ys) ^ i
      + C (M.ι (B.coeff i)) * X ^ (2 * (k - i)) * (v * ys) ^ i * -ys) =
      (∑ i ∈ Finset.range (k + 1), C (M.ι (A.coeff i)) * X ^ (2 * (k - i)) * (v * ys) ^ i) * X ^ 3
      - (∑ i ∈ Finset.range (k + 1), C (M.ι (B.coeff i)) * X ^ (2 * (k - i)) * (v * ys) ^ i) * ys := by
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  set SA := ∑ i ∈ Finset.range (k + 1), C (M.ι (A.coeff i)) * X ^ (2 * (k - i)) * (v * ys) ^ i
  set SB := ∑ i ∈ Finset.range (k + 1), C (M.ι (B.coeff i)) * X ^ (2 * (k - i)) * (v * ys) ^ i
  set SD := ∑ i ∈ Finset.range (j + 1), C (M.ι (D.coeff i)) * X ^ (2 * (j - i)) * (v * ys) ^ i
  have hX : (X : ℂ_[q]⟦X⟧) ^ (j + k) ≠ 0 := pow_ne_zero _ X_ne_zero
  apply mul_left_cancel₀ hX
  have key2 : hat M.ι ℓ F * (hat M.ι ℓ (homog D j M.u M.w) * ys ^ j) * (hat M.ι ℓ M.w * ys) ^ (k + 1)
      + hat M.ι ℓ G * (hat M.ι ℓ M.w * ys) ^ j * (hat M.ι ℓ (homog B k M.u M.w) * ys ^ k) * ys
      = hat M.ι ℓ G * (hat M.ι ℓ M.w * ys) ^ j * ((hat M.ι ℓ (homog A k M.u M.w) * ys ^ k)
        * (hat M.ι ℓ M.w * ys)) := by
    linear_combination ys ^ (j + k + 1) * key
  rw [eA, eB, eD, hWys] at key2
  linear_combination key2

end GlobalTheory.MomOne.ChartXY
