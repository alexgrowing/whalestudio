import ReciprocityTheory.Chebotarev.Support

open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.InfinitePlace
  NumberField.Units.dirichletUnitTheorem

open scoped Classical

namespace ReciprocityTheory.Cheb

theorem abs_log_sub_log_le_of_half {a b δ : ℝ} (hb : 0 < b) (hab : |a - b| ≤ δ) (ha : b / 2 ≤ a) :
    |Real.log a - Real.log b| ≤ 2 * δ / b := by
  have ha0 : 0 < a := by linarith
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hab
  rw [abs_le] at hab ⊢
  constructor
  · have h1 : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb ha0)
    rw [Real.log_div hb.ne' ha0.ne'] at h1
    have h2 : b / a - 1 ≤ 2 * δ / b := by
      rw [div_sub_one ha0.ne', div_le_div_iff₀ ha0 hb]
      nlinarith
    linarith
  · have h1 : Real.log (a / b) ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos ha0 hb)
    rw [Real.log_div ha0.ne' hb.ne'] at h1
    have h2 : a / b - 1 ≤ 2 * δ / b := by
      rw [div_sub_one hb.ne']
      apply div_le_div_of_nonneg_right _ hb.le
      linarith
    linarith

theorem abs_exp_neg_mul_sub_le {s u v L : ℝ} (hs : 1 ≤ s) (hL : 0 ≤ L) (hu : L ≤ u) (hv : L ≤ v) :
    |Real.exp (-s * u) - Real.exp (-s * v)| ≤ s * |u - v| * Real.exp (-L) := by
  have key : ∀ u v : ℝ, L ≤ u → u ≤ v →
      Real.exp (-s * u) - Real.exp (-s * v) ≤ s * (v - u) * Real.exp (-L) := by
    intro u v hu huv
    have e1 : Real.exp (-s * v) = Real.exp (-s * u) * Real.exp (-(s * (v - u))) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : 1 - Real.exp (-(s * (v - u))) ≤ s * (v - u) := by
      linarith [Real.add_one_le_exp (-(s * (v - u)))]
    have e3 : Real.exp (-s * u) ≤ Real.exp (-L) := Real.exp_le_exp.mpr (by nlinarith)
    have e4 : 0 ≤ s * (v - u) := mul_nonneg (by linarith) (by linarith)
    rw [e1]
    calc Real.exp (-s * u) - Real.exp (-s * u) * Real.exp (-(s * (v - u)))
        = Real.exp (-s * u) * (1 - Real.exp (-(s * (v - u)))) := by ring
      _ ≤ Real.exp (-L) * (s * (v - u)) :=
        mul_le_mul e3 e2 (by linarith [Real.exp_le_one_iff.mpr (by linarith : -(s * (v - u)) ≤ 0)])
          (Real.exp_pos _).le
      _ = s * (v - u) * Real.exp (-L) := by ring
  rcases le_total u v with huv | hvu
  · have h := key u v hu huv
    have hm : Real.exp (-s * v) ≤ Real.exp (-s * u) := Real.exp_le_exp.mpr (by nlinarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · have h := key v u hv hvu
    have hm : Real.exp (-s * u) ≤ Real.exp (-s * v) := Real.exp_le_exp.mpr (by nlinarith)
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    linarith

theorem sign_add_of_abs_lt {a e : ℝ} (h : |e| < |a|) : SignType.sign (a + e) = SignType.sign a := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rw [abs_of_neg ha] at h
    have : a + e < 0 := by linarith [le_abs_self e]
    rw [sign_neg this, sign_neg ha]
  · subst ha; simp at h; linarith [abs_nonneg e]
  · rw [abs_of_pos ha] at h
    have : 0 < a + e := by linarith [neg_abs_le e]
    rw [sign_pos this, sign_pos ha]

variable {E : Type} [Field E] [NumberField E]

theorem normAtPlace_le_norm' (w : InfinitePlace E) (z : mixedSpace E) : normAtPlace w z ≤ ‖z‖ := by
  rw [norm_eq_sup'_normAtPlace]
  exact Finset.le_sup' (fun w => normAtPlace w z) (Finset.mem_univ w)

theorem abs_normAtPlace_add_sub_le (w : InfinitePlace E) (y k : mixedSpace E) :
    |normAtPlace w (y + k) - normAtPlace w y| ≤ ‖k‖ := by
  have h1 := normAtPlace_add_le w y k
  have h2 := normAtPlace_add_le w (y + k) (-k)
  rw [add_neg_cancel_right, normAtPlace_neg] at h2
  have h3 := normAtPlace_le_norm' w k
  rw [abs_le]; constructor <;> linarith

theorem mult_le_two' (w : InfinitePlace E) : (mult w : ℝ) ≤ 2 := by
  unfold mult; split_ifs <;> norm_num

theorem log_norm_eq_sum {z : mixedSpace E} (hz : ∀ w, normAtPlace w z ≠ 0) :
    Real.log (mixedEmbedding.norm z) = ∑ w, (mult w : ℝ) * Real.log (normAtPlace w z) := by
  rw [mixedEmbedding.norm_apply, Real.log_prod (fun w _ => pow_ne_zero _ (hz w))]
  simp_rw [Real.log_pow]

section Core

variable {y k : mixedSpace E} {B a : ℝ}

theorem half_le_normAtPlace_add (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a) (hy : ∀ w, a ≤ normAtPlace w y)
    (w : InfinitePlace E) : normAtPlace w y / 2 ≤ normAtPlace w (y + k) := by
  have h := abs_normAtPlace_add_sub_le w y k
  rw [abs_le] at h
  linarith [hy w]

theorem normAtPlace_add_pos (hB : 0 < B) (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a) (hy : ∀ w, a ≤ normAtPlace w y)
    (w : InfinitePlace E) : 0 < normAtPlace w (y + k) := by
  have := half_le_normAtPlace_add hk ha hy w
  linarith [hy w]

theorem abs_log_normAtPlace_sub_le (hB : 0 < B) (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a)
    (hy : ∀ w, a ≤ normAtPlace w y) (w : InfinitePlace E) :
    |Real.log (normAtPlace w (y + k)) - Real.log (normAtPlace w y)| ≤ 2 * B / a := by
  have ha0 : 0 < a := by linarith
  have hw : 0 < normAtPlace w y := lt_of_lt_of_le ha0 (hy w)
  refine (abs_log_sub_log_le_of_half hw ((abs_normAtPlace_add_sub_le w y k).trans hk)
    (half_le_normAtPlace_add hk ha hy w)).trans ?_
  exact div_le_div_of_nonneg_left (by linarith) ha0 (hy w)

theorem abs_log_norm_sub_le (hB : 0 < B) (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a)
    (hy : ∀ w, a ≤ normAtPlace w y) :
    |Real.log (mixedEmbedding.norm (y + k)) - Real.log (mixedEmbedding.norm y)| ≤
      (Module.finrank ℚ E : ℝ) * (2 * B / a) := by
  have ha0 : 0 < a := by linarith
  rw [log_norm_eq_sum (fun w => (normAtPlace_add_pos hB hk ha hy w).ne'),
    log_norm_eq_sum (fun w => (lt_of_lt_of_le ha0 (hy w)).ne'), ← Finset.sum_sub_distrib]
  calc |∑ w, ((mult w : ℝ) * Real.log (normAtPlace w (y + k)) - (mult w : ℝ) * Real.log (normAtPlace w y))|
      ≤ ∑ w, |(mult w : ℝ) * Real.log (normAtPlace w (y + k)) - (mult w : ℝ) * Real.log (normAtPlace w y)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w : InfinitePlace E, (mult w : ℝ) * (2 * B / a) := by
        refine Finset.sum_le_sum fun w _ => ?_
        rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        exact mul_le_mul_of_nonneg_left (abs_log_normAtPlace_sub_le hB hk ha hy w) (Nat.cast_nonneg _)
    _ = (Module.finrank ℚ E : ℝ) * (2 * B / a) := by
        rw [← Finset.sum_mul, ← sum_mult_eq]; push_cast; ring

theorem abs_logMap_sub_le (hB : 0 < B) (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a)
    (hy : ∀ w, a ≤ normAtPlace w y) (w : {w : InfinitePlace E // w ≠ w₀}) :
    |logMap (y + k) w - logMap y w| ≤ 4 * (2 * B / a) := by
  have hd : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.mpr Module.finrank_pos
  have hδ : 0 ≤ 2 * B / a := div_nonneg (by linarith) (by linarith)
  simp only [logMap_apply]
  rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  have h1 := abs_log_normAtPlace_sub_le hB hk ha hy w.1
  have h2 := abs_log_norm_sub_le hB hk ha hy
  have h3 : |Real.log (mixedEmbedding.norm (y + k)) * (Module.finrank ℚ E : ℝ)⁻¹ -
      Real.log (mixedEmbedding.norm y) * (Module.finrank ℚ E : ℝ)⁻¹| ≤ 2 * B / a := by
    rw [← sub_mul, abs_mul, abs_of_pos (inv_pos.mpr hd)]
    calc _ ≤ (Module.finrank ℚ E : ℝ) * (2 * B / a) * (Module.finrank ℚ E : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right h2 (inv_pos.mpr hd).le
      _ = 2 * B / a := by field_simp
  have h4 : |Real.log (normAtPlace w.1 (y + k)) - Real.log (mixedEmbedding.norm (y + k)) * (Module.finrank ℚ E : ℝ)⁻¹ -
      (Real.log (normAtPlace w.1 y) - Real.log (mixedEmbedding.norm y) * (Module.finrank ℚ E : ℝ)⁻¹)| ≤
        2 * (2 * B / a) := by
    have := abs_sub (Real.log (normAtPlace w.1 (y + k)) - Real.log (normAtPlace w.1 y))
      (Real.log (mixedEmbedding.norm (y + k)) * (Module.finrank ℚ E : ℝ)⁻¹ -
        Real.log (mixedEmbedding.norm y) * (Module.finrank ℚ E : ℝ)⁻¹)
    calc _ = |Real.log (normAtPlace w.1 (y + k)) - Real.log (normAtPlace w.1 y) -
          (Real.log (mixedEmbedding.norm (y + k)) * (Module.finrank ℚ E : ℝ)⁻¹ -
            Real.log (mixedEmbedding.norm y) * (Module.finrank ℚ E : ℝ)⁻¹)| := by ring_nf
      _ ≤ _ := this
      _ ≤ 2 * (2 * B / a) := by linarith
  calc (mult w.1 : ℝ) * |_| ≤ 2 * (2 * (2 * B / a)) :=
        mul_le_mul (mult_le_two' w.1) h4 (abs_nonneg _) (by norm_num)
    _ = 4 * (2 * B / a) := by ring

theorem norm_logMap_sub_le (hB : 0 < B) (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a)
    (hy : ∀ w, a ≤ normAtPlace w y) : ‖logMap (y + k) - logMap y‖ ≤ 4 * (2 * B / a) := by
  have hδ : 0 ≤ 2 * B / a := div_nonneg (by linarith) (by linarith)
  refine (pi_norm_le_iff_of_nonneg (by linarith)).mpr fun w => ?_
  rw [Pi.sub_apply, Real.norm_eq_abs]
  exact abs_logMap_sub_le hB hk ha hy w

theorem rsgn_add (hB : 0 < B) (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a) (hy : ∀ w, a ≤ normAtPlace w y) :
    rsgn (y + k) = rsgn y := by
  unfold rsgn
  refine Finset.prod_congr rfl fun w _ => ?_
  have h1 : |k.1 w| ≤ B := by
    have := normAtPlace_le_norm' w.1 k
    rw [normAtPlace_apply_of_isReal w.2] at this
    exact (Real.norm_eq_abs _ ▸ this).trans hk
  have h2 : a ≤ |y.1 w| := by
    have := hy w.1
    rwa [normAtPlace_apply_of_isReal w.2, Real.norm_eq_abs] at this
  have h3 : SignType.sign ((y + k).1 w) = SignType.sign (y.1 w) := by
    rw [Prod.fst_add, Pi.add_apply]
    exact sign_add_of_abs_lt (a := y.1 w) (e := k.1 w) (by linarith)
  rw [h3]

end Core

theorem exists_ucoord_bound : ∃ A : ℝ, 0 ≤ A ∧ ∀ x y : mixedSpace E,
    ∑ i, |ucoord x i - ucoord y i| ≤ A * ‖logMap x - logMap y‖ := by
  set b := (basisUnitLattice E).ofZLatticeBasis ℝ (unitLattice E)
  refine ⟨∑ i, ‖LinearMap.toContinuousLinearMap (b.coord i)‖,
    Finset.sum_nonneg fun _ _ => norm_nonneg _, fun x y => ?_⟩
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h : ucoord x i - ucoord y i =
      LinearMap.toContinuousLinearMap (b.coord i) (logMap x - logMap y) := by
    simp [ucoord, b, Module.Basis.coord_apply, map_sub]
  rw [h, ← Real.norm_eq_abs]
  exact ContinuousLinearMap.le_opNorm _ _

theorem abs_uphi_sub_le {x y : mixedSpace E} (hx : mixedEmbedding.norm x ≠ 0)
    (hy : mixedEmbedding.norm y ≠ 0) : |uphi x - uphi y| ≤ ∑ i, |ucoord x i - ucoord y i| := by
  unfold uphi
  rw [if_neg hx, if_neg hy]
  exact abs_Tent_sub_Tent_le _ _

theorem Gs_eq_real {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ) (x : mixedSpace E) :
    Gs χ s x = χ (rsgn x : ZMod l) * ((uphi x * mixedEmbedding.norm x ^ (-s) : ℝ) : ℂ) := by
  unfold Gs
  rw [Complex.ofReal_mul, Complex.ofReal_cpow (mixedEmbedding.norm_nonneg x), Complex.ofReal_neg]
  ring

theorem abs_rpow_neg_sub_le {s m N N' : ℝ} (hs : 1 ≤ s) (hm : 1 ≤ m) (hN : m ≤ N) (hN' : m ≤ N') :
    |N' ^ (-s) - N ^ (-s)| ≤ s * |Real.log N' - Real.log N| * m⁻¹ := by
  have hm0 : 0 < m := by linarith
  rw [Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos (by linarith),
    mul_comm (Real.log N'), mul_comm (Real.log N)]
  have := abs_exp_neg_mul_sub_le hs (Real.log_nonneg hm) (Real.log_le_log hm0 hN')
    (Real.log_le_log hm0 hN)
  rwa [Real.exp_neg, Real.exp_log hm0] at this

theorem rpow_neg_le_inv {s m N : ℝ} (hs : 1 ≤ s) (hm : 1 ≤ m) (hN : m ≤ N) : N ^ (-s) ≤ m⁻¹ := by
  calc N ^ (-s) ≤ N ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = N⁻¹ := Real.rpow_neg_one N
    _ ≤ m⁻¹ := inv_anti₀ (by linarith) hN

theorem pow_le_norm_of_le {z : mixedSpace E} {b : ℝ} (hb : 0 ≤ b) (h : ∀ w, b ≤ normAtPlace w z) :
    b ^ Module.finrank ℚ E ≤ mixedEmbedding.norm z := by
  rw [mixedEmbedding.norm_apply, ← sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun w _ => pow_nonneg hb _) (fun w _ => pow_le_pow_left₀ hb (h w) _)

theorem norm_Gs_add_sub_le_core {l : ℕ} (χ : DirichletCharacter ℂ l) {s : ℝ} (hs : s ∈ Set.Icc (1 : ℝ) 2)
    {A : ℝ} (hA : 0 ≤ A)
    (hAb : ∀ x y : mixedSpace E, ∑ i, |ucoord x i - ucoord y i| ≤ A * ‖logMap x - logMap y‖)
    {y k : mixedSpace E} {B a : ℝ} (hB : 0 < B) (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a) (ha2 : 2 ≤ a)
    (hy : ∀ w, a ≤ normAtPlace w y) :
    ‖Gs χ s (y + k) - Gs χ s y‖ ≤
      (A * (4 * (2 * B / a)) + 2 * ((Module.finrank ℚ E : ℝ) * (2 * B / a))) *
        ((a / 2) ^ Module.finrank ℚ E)⁻¹ := by
  have ha0 : 0 < a := by linarith
  have hyw : ∀ w, 0 < normAtPlace w y := fun w => lt_of_lt_of_le ha0 (hy w)
  have hyN : mixedEmbedding.norm y ≠ 0 := mixedEmbedding.norm_ne_zero_iff.mpr fun w => (hyw w).ne'
  have hykN : mixedEmbedding.norm (y + k) ≠ 0 :=
    mixedEmbedding.norm_ne_zero_iff.mpr fun w => (normAtPlace_add_pos hB hk ha hy w).ne'
  set m := (a / 2) ^ Module.finrank ℚ E with hm_def
  have hm1 : 1 ≤ m := one_le_pow₀ (by linarith)
  have hmN : m ≤ mixedEmbedding.norm y :=
    pow_le_norm_of_le (by linarith) fun w => by linarith [hy w]
  have hmN' : m ≤ mixedEmbedding.norm (y + k) :=
    pow_le_norm_of_le (by linarith) fun w => by
      linarith [hy w, half_le_normAtPlace_add hk ha hy w]
  have hδ : 0 ≤ 2 * B / a := div_nonneg (by linarith) ha0.le

  have hu : |uphi (y + k) - uphi y| ≤ A * (4 * (2 * B / a)) :=
    (abs_uphi_sub_le hykN hyN).trans ((hAb _ _).trans
      (mul_le_mul_of_nonneg_left (norm_logMap_sub_le hB hk ha hy) hA))

  have hP : |mixedEmbedding.norm (y + k) ^ (-s) - mixedEmbedding.norm y ^ (-s)| ≤
      2 * ((Module.finrank ℚ E : ℝ) * (2 * B / a)) * m⁻¹ := by
    refine (abs_rpow_neg_sub_le hs.1 hm1 hmN hmN').trans ?_
    have hl := abs_log_norm_sub_le hB hk ha hy
    have hm0 : 0 ≤ m⁻¹ := inv_nonneg.mpr (by linarith)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hs.2 hl (abs_nonneg _) (by norm_num)) hm0
  have hP' : mixedEmbedding.norm (y + k) ^ (-s) ≤ m⁻¹ := rpow_neg_le_inv hs.1 hm1 hmN'
  have hP0 : 0 ≤ mixedEmbedding.norm (y + k) ^ (-s) :=
    Real.rpow_nonneg (mixedEmbedding.norm_nonneg _) _
  have hu0 : 0 ≤ uphi y := uphi_nonneg y
  have hu1 : uphi y ≤ 1 := uphi_le_one y
  have hreal : |uphi (y + k) * mixedEmbedding.norm (y + k) ^ (-s) - uphi y * mixedEmbedding.norm y ^ (-s)| ≤
      (A * (4 * (2 * B / a)) + 2 * ((Module.finrank ℚ E : ℝ) * (2 * B / a))) * m⁻¹ := by
    have e : uphi (y + k) * mixedEmbedding.norm (y + k) ^ (-s) - uphi y * mixedEmbedding.norm y ^ (-s) =
        (uphi (y + k) - uphi y) * mixedEmbedding.norm (y + k) ^ (-s) +
          uphi y * (mixedEmbedding.norm (y + k) ^ (-s) - mixedEmbedding.norm y ^ (-s)) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hP0, abs_of_nonneg hu0]
    have h1 : |uphi (y + k) - uphi y| * mixedEmbedding.norm (y + k) ^ (-s) ≤ A * (4 * (2 * B / a)) * m⁻¹ :=
      mul_le_mul hu hP' hP0 (by positivity)
    have h2 : uphi y * |mixedEmbedding.norm (y + k) ^ (-s) - mixedEmbedding.norm y ^ (-s)| ≤
        2 * ((Module.finrank ℚ E : ℝ) * (2 * B / a)) * m⁻¹ := by
      calc _ ≤ 1 * |mixedEmbedding.norm (y + k) ^ (-s) - mixedEmbedding.norm y ^ (-s)| :=
            mul_le_mul_of_nonneg_right hu1 (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact hP
    linarith
  rw [Gs_eq_real, Gs_eq_real, rsgn_add hB hk ha hy, ← mul_sub, norm_mul, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  calc ‖χ (rsgn y : ZMod l)‖ * |_| ≤ 1 * |uphi (y + k) * mixedEmbedding.norm (y + k) ^ (-s) -
        uphi y * mixedEmbedding.norm y ^ (-s)| :=
        mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) (abs_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact hreal

end ReciprocityTheory.Cheb
