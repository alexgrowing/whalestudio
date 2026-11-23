import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ConjNeOne
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.RadialIntegralUnitCircleEq
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ExistsFix

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.RadialIntegralLemmas
open UpperTheory.Esk

theorem F_conj (h2 : B1b) (k : ℕ) (g h : GL (Fin 2) ℝ) (z : P) :
    F k (h⁻¹ * g * h) z = F k g (h • z) := by
  unfold B1b at h2
  obtain ⟨hj, hjne, hq, -⟩ := h2
  set m := h⁻¹ * g * h with hm
  have e : g * h = h * m := by rw [hm]; group
  have e2 : g • h • z = h • m • z := by rw [smul_smul, smul_smul, e]
  apply mul_left_cancel₀ (hjne k h z)
  have h3 := hj k g h z
  have h4 := hj k h m z
  have h5 := hq k h z (m • z)
  simp only [F]
  rw [e2]
  rw [e] at h3
  calc j1 k h z * (q1 k z (m • z) * j1 k m z)
      = q1 k (h • z) (h • m • z) * (j1 k h (m • z) * j1 k m z) := by linear_combination (-(j1 k m z)) * h5
    _ = j1 k h z * (q1 k (h • z) (h • m • z) * j1 k g (h • z)) := by rw [← h4, h3]; ring

def smulEquiv (hc : ∀ g : GL (Fin 2) ℝ, Continuous (fun z : P => g • z)) (h : GL (Fin 2) ℝ) : P ≃ᵐ P where
  toEquiv := MulAction.toPerm h
  measurable_toFun := (hc h).measurable
  measurable_invFun := (hc h⁻¹).measurable

theorem comp_smul (h1 : B1a) (h : GL (Fin 2) ℝ) (f : P → ℂ) :
    (Integrable (fun z => f (h • z)) ↔ Integrable f) ∧ ∫ z, f (h • z) = ∫ z, f z := by
  unfold B1a at h1
  have hc : ∀ g : GL (Fin 2) ℝ, Continuous (fun z : P => g • z) := fun g => (h1.2.2 g).1
  have hm : MeasurePreserving (smulEquiv hc h) volume volume := (h1.2.2 h).2
  exact ⟨hm.integrable_comp_emb (smulEquiv hc h).measurableEmbedding, hm.integral_comp' f⟩

theorem F_cont (h1 : B1a) (h2 : B1b) (k : ℕ) (g : GL (Fin 2) ℝ) : Continuous (F k g) := by
  unfold B1a at h1
  unfold B1b at h2
  obtain ⟨-, -, -, -, -, -, hjc, hqc, -⟩ := h2
  exact ((hqc k).comp (continuous_id.prodMk (h1.2.2 g).1)).mul (hjc k g)

theorem F_norm (h2 : B1b) (k : ℕ) (hk : 1 ≤ k) (g : GL (Fin 2) ℝ) (z : P) :
    ‖F k g z‖ = ((k : ℝ) - 1) / (4 * Real.pi) * kap z (g • z) ^ ((k : ℝ) / 2) := by
  unfold B1b at h2
  obtain ⟨-, -, -, -, hj, hq, -⟩ := h2
  have a1 := hj k g z
  have a2 := hq k z (g • z) hk
  have p1 : 0 < |z.1.im| ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos (abs_pos.2 z.2) _
  have p2 : 0 < |(g • z).1.im| ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos (abs_pos.2 (g • z).2) _
  simp only [F, norm_mul]
  apply mul_right_cancel₀ (mul_ne_zero p1.ne' p2.ne')
  calc ‖q1 k z (g • z)‖ * ‖j1 k g z‖ * (|z.1.im| ^ ((k : ℝ) / 2) * |(g • z).1.im| ^ ((k : ℝ) / 2))
      = (‖q1 k z (g • z)‖ * |z.1.im| ^ ((k : ℝ) / 2)) * (‖j1 k g z‖ * |(g • z).1.im| ^ ((k : ℝ) / 2)) := by ring
    _ = _ := by rw [a1, a2]; ring

theorem meas_upper : MeasurableSet {z : P | 0 < z.1.im} :=
  (isOpen_lt continuous_const (Complex.continuous_im.comp continuous_subtype_val)).measurableSet

theorem U_int (h1 : B1a) (h2 : B1b) (h3 : B1c) (h6 : B6) (k : ℕ) (hk : 4 ≤ k) (m : GL (Fin 2) ℝ) (a b : ℝ)
    (h00 : m 0 0 = a) (h01 : m 0 1 = b) (h10 : m 1 0 = -b) (h11 : m 1 1 = a) (hb : b ≠ 0) :
    Integrable (U k m) := by
  obtain ⟨C, hC⟩ := h6 k hk
  unfold B1c at h3
  have hkn : ∀ z w, 0 ≤ kap z w := fun z w => (h3.1 z w).1
  have hkc : Continuous (fun w : P => kap iP w) :=
    h3.2.2.2.2.1.comp (continuous_const.prodMk continuous_id)
  have hint : Integrable (fun w : P => kap iP w ^ ((k : ℝ) / 2)) := by
    refine ⟨(hkc.rpow_const (fun _ => Or.inr (by positivity))).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun w => Real.rpow_nonneg (hkn _ _) _))]
    exact lt_of_le_of_lt (hC iP).1 ENNReal.coe_lt_top
  set K : ℝ := ((k : ℝ) - 1) / (4 * Real.pi) * ((a ^ 2 + b ^ 2) / b ^ 2) ^ ((k : ℝ) / 2)
  have hc0 : 0 ≤ ((k : ℝ) - 1) / (4 * Real.pi) := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    have := Real.pi_pos
    apply div_nonneg <;> linarith
  refine (hint.const_mul K).mono' ?_ (ae_of_all _ (fun z => ?_))
  · exact (Measurable.ite meas_upper (F_cont h1 h2 k m).measurable measurable_const).aestronglyMeasurable
  · simp only [U]
    split_ifs with hz
    · rw [F_norm h2 k (by omega) m z, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hc0
      rw [← Real.mul_rpow (by positivity) (hkn _ _)]
      exact Real.rpow_le_rpow (hkn _ _) (kap_rot m a b h00 h01 h10 h11 hb z hz) (by positivity)
    · rw [norm_zero]
      have : 0 ≤ ((a ^ 2 + b ^ 2) / b ^ 2) ^ ((k : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
      exact mul_nonneg (mul_nonneg hc0 this) (Real.rpow_nonneg (hkn _ _) _)

theorem eta_sq (a b : ℝ) (hb : b ≠ 0) : ‖eta a b ^ 2‖ = 1 ∧ eta a b ^ 2 ≠ 1 := by
  have hp : 0 < a ^ 2 + b ^ 2 := by positivity
  have hs : (Real.sqrt (a ^ 2 + b ^ 2) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hp).ne'
  constructor
  · rw [norm_pow, Complex.sq_norm, eta, Complex.normSq_div, Complex.normSq_ofReal,
      Real.mul_self_sqrt hp.le, Complex.normSq_apply]
    simp
    field_simp
  · intro h
    have h' : ((a : ℂ) - b * Complex.I) ^ 2 = ((Real.sqrt (a ^ 2 + b ^ 2) ^ 2 : ℝ) : ℂ) := by
      rw [eta, div_pow, div_eq_one_iff_eq (pow_ne_zero 2 hs)] at h
      rw [h]; push_cast; ring
    rw [Real.sq_sqrt hp.le] at h'
    have h2 := congrArg Complex.re h'
    simp [sq] at h2
    apply hb
    nlinarith

theorem U_integral (h1 : B1a) (h2 : B1b) (h3 : B1c) (h22 : B2) (h6 : B6) (k : ℕ) (hk : 4 ≤ k)
    (m : GL (Fin 2) ℝ) (a b : ℝ)
    (h00 : m 0 0 = a) (h01 : m 0 1 = b) (h10 : m 1 0 = -b) (h11 : m 1 1 = a) (hb : b ≠ 0) :
    Integrable (U k m) ∧ ∫ z, U k m z = eta a b ^ k / (1 - eta a b ^ 2) := by
  have hI := U_int h1 h2 h3 h6 k hk m a b h00 h01 h10 h11 hb
  refine ⟨hI, ?_⟩
  have hv : ∀ z : P, z.1.im < 0 → U k m z = 0 := fun z hz => if_neg (not_lt.2 hz.le)
  rw [(h22 (U k m) hv hI).2]
  have hs : MeasurableSet (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have e := setIntegral_congr_fun hs (μ := volume) (f := fun p : ℝ × ℝ => ((4 * p.1 / (1 - p.1 ^ 2) ^ 2 : ℝ) : ℂ) *
      ext1 (U k m) (Complex.I * (1 + circleMap 0 p.1 p.2) / (1 - circleMap 0 p.1 p.2)))
    (g := fun p : ℝ × ℝ => ((4 * p.1 / (1 - p.1 ^ 2) ^ 2 : ℝ) : ℂ) * (((k : ℂ) - 1) / (4 * Real.pi) *
      (eta a b * (1 - (p.1 : ℂ) ^ 2) / (1 - eta a b ^ 2 * (p.1 : ℂ) ^ 2)) ^ k))
    (fun p hp => by
      simp only []
      rw [cayley_val k m a b h00 h01 h10 h11 hb p.1 p.2 hp.1.1 hp.1.2])
  rw [e, rad_int k (by omega) _ _ _ (eta_sq a b hb).1 (eta_sq a b hb).2]
  have hk1 : ((k : ℂ) - 1) ≠ 0 := by
    have : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1z : 1 - eta a b ^ 2 ≠ 0 := sub_ne_zero.2 (Ne.symm (eta_sq a b hb).2)
  field_simp

def dr : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℝ), 0; 0, -1] (by simp)

theorem dr_mul : dr * dr = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [dr, Matrix.mul_apply, Fin.sum_univ_two]

theorem dr_smul (z : P) : (dr • z).1 = -z.1 := by
  rw [coe_smul]
  simp [num, den, dr, div_neg]

theorem F_rot (h1 : B1a) (h2 : B1b) (h3 : B1c) (h22 : B2) (h6 : B6) (k : ℕ) (hk : 4 ≤ k)
    (m : GL (Fin 2) ℝ) (a b : ℝ)
    (h00 : m 0 0 = a) (h01 : m 0 1 = b) (h10 : m 1 0 = -b) (h11 : m 1 1 = a) (hb : b ≠ 0) :
    Integrable (F k m) ∧ ∫ z, F k m z = eta a b ^ k / (1 - eta a b ^ 2) + eta a (-b) ^ k / (1 - eta a (-b) ^ 2) := by
  set m' := dr * m * dr with hm'
  have hdi : dr⁻¹ = dr := inv_eq_of_mul_eq_one_right dr_mul
  have hmm : dr⁻¹ * m' * dr = m := by
    rw [hdi, hm', ← mul_assoc, ← mul_assoc, dr_mul, one_mul, mul_assoc, dr_mul, mul_one]
  have ent : ∀ i j, m' i j = (!![(1 : ℝ), 0; 0, -1] * (m : Matrix (Fin 2) (Fin 2) ℝ) * !![(1 : ℝ), 0; 0, -1]) i j := by
    intro i j; simp [hm', dr]
  have e00 : m' 0 0 = a := by rw [ent]; simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, h00]
  have e01 : m' 0 1 = -b := by rw [ent]; simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, h01]
  have e10 : m' 1 0 = -(-b) := by rw [ent]; simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, h10]
  have e11 : m' 1 1 = a := by rw [ent]; simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, h11]
  obtain ⟨hI1, hJ1⟩ := U_integral h1 h2 h3 h22 h6 k hk m a b h00 h01 h10 h11 hb
  obtain ⟨hI2, hJ2⟩ := U_integral h1 h2 h3 h22 h6 k hk m' a (-b) e00 e01 e10 e11 (neg_ne_zero.2 hb)
  have hsplit : F k m = fun z => U k m z + U k m' (dr • z) := by
    funext z
    have hd := dr_smul z
    have hF : F k m z = F k m' (dr • z) := by rw [← F_conj h2, hmm]
    simp only [U]
    rcases lt_or_gt_of_ne z.2 with hz | hz
    · have : 0 < (dr • z).1.im := by rw [hd, Complex.neg_im]; linarith
      rw [if_neg (not_lt.2 hz.le), if_pos this, hF, zero_add]
    · have : ¬ 0 < (dr • z).1.im := by rw [hd, Complex.neg_im]; linarith
      rw [if_pos hz, if_neg this, add_zero]
  obtain ⟨hc1, hc2⟩ := comp_smul h1 dr (U k m')
  rw [hsplit]
  refine ⟨hI1.add (hc1.2 hI2), ?_⟩
  rw [integral_add hI1 (hc1.2 hI2), hc2, hJ1, hJ2]

theorem rot_of_fix (m : GL (Fin 2) ℝ) (hm : m • iP = iP) : m 1 1 = m 0 0 ∧ m 1 0 = -(m 0 1) := by
  have h := congrArg Subtype.val hm
  rw [coe_smul] at h
  have hd := den_ne m (z := iP.1) (by simp [iP])
  rw [div_eq_iff hd] at h
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [num, den, iP] at h1 h2
  constructor <;> linarith

theorem ch_mul {R : Type*} [CommRing R] (x y : R) : ∀ n, ch (x + y) (x * y) n * (x - y) = x ^ n - y ^ n
  | 0 => by simp [ch]
  | 1 => by simp [ch]
  | (n + 2) => by
    have h1 := ch_mul x y (n + 1)
    have h0 := ch_mul x y n
    simp only [ch]
    linear_combination (x + y) * h1 - x * y * h0

theorem ch_cast (t d : ℝ) : ∀ n, ((ch t d n : ℝ) : ℂ) = ch (t : ℂ) (d : ℂ) n
  | 0 => by simp [ch]
  | 1 => by simp [ch]
  | (n + 2) => by
    simp only [ch]
    push_cast
    rw [ch_cast t d (n + 1), ch_cast t d n]

theorem dualNumber_unit_mul_decomposition (k : ℕ) (hk : 2 ≤ k) (a b : ℝ) (hb : b ≠ 0) :
    eta a b ^ k / (1 - eta a b ^ 2) + eta a (-b) ^ k / (1 - eta a (-b) ^ 2) =
      -((ch (2 * a) (a ^ 2 + b ^ 2) (k - 1) * (a ^ 2 + b ^ 2) ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ) := by
  have hp : 0 < a ^ 2 + b ^ 2 := by positivity
  set s := Real.sqrt (a ^ 2 + b ^ 2) with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 hp
  have hss : s ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt hp.le
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  have hr : (a ^ 2 + b ^ 2) ^ (1 - ((n + 2 : ℕ) : ℝ) / 2) = 1 / s ^ n := by
    rw [← hss, ← Real.rpow_natCast s 2, ← Real.rpow_mul hs.le]
    rw [show ((2 : ℕ) : ℝ) * (1 - ((n + 2 : ℕ) : ℝ) / 2) = -(n : ℝ) by push_cast; ring]
    rw [Real.rpow_neg hs.le, Real.rpow_natCast, one_div]
  rw [hr, show n + 2 - 1 = n + 1 by omega]
  have hS : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  set x : ℂ := (a : ℂ) + b * Complex.I with hx
  set y : ℂ := (a : ℂ) - b * Complex.I with hy
  have hxy : x * y = (s : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, hss, hx, hy]
    push_cast
    linear_combination (-(b : ℂ) ^ 2) * Complex.I_sq
  have hbI : (b : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hb) Complex.I_ne_zero
  have key := ch_mul x y (n + 1)
  have e1 : x + y = ((2 * a : ℝ) : ℂ) := by rw [hx, hy]; push_cast; ring
  have e2 : x * y = ((a ^ 2 + b ^ 2 : ℝ) : ℂ) := by
    rw [hxy, ← Complex.ofReal_pow, hss]
  rw [e1, e2, ← ch_cast] at key
  set c : ℂ := ((ch (2 * a) (a ^ 2 + b ^ 2) (n + 1) : ℝ) : ℂ) with hc
  set u := eta a b with hu_def
  set v := eta a (-b) with hv_def
  have hu : u = y / (s : ℂ) := by rw [hu_def, eta]
  have hv : v = x / (s : ℂ) := by
    rw [hv_def, eta, hx, hs_def]
    push_cast
    rw [neg_sq]
    ring
  have hx0 : x ≠ 0 := by
    intro h0; have := congrArg Complex.im h0; rw [hx] at this; simp at this; exact hb this
  have hy0 : y ≠ 0 := by
    intro h0; have := congrArg Complex.im h0; rw [hy] at this; simp at this; exact hb this
  have hu0 : u ≠ 0 := by rw [hu]; exact div_ne_zero hy0 hS
  have hv0 : v ≠ 0 := by rw [hv]; exact div_ne_zero hx0 hS
  have huv : u * v = 1 := by
    rw [hu, hv, div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero hS hS)]
    linear_combination hxy
  have hvu : v - u ≠ 0 := by
    rw [hu, hv, ← sub_div]
    apply div_ne_zero _ hS
    rw [hx, hy]; ring_nf
    exact mul_ne_zero (mul_ne_zero (by exact_mod_cast hb) Complex.I_ne_zero) two_ne_zero
  have huv' : u - v ≠ 0 := by rw [← neg_sub]; exact neg_ne_zero.2 hvu
  have hC : c / (s : ℂ) ^ n * (v - u) = v ^ (n + 1) - u ^ (n + 1) := by
    have hx' : x = (s : ℂ) * v := by rw [hv]; field_simp
    have hy' : y = (s : ℂ) * u := by rw [hu]; field_simp
    rw [hx', hy'] at key
    rw [div_mul_eq_mul_div, div_eq_iff (pow_ne_zero n hS)]
    apply mul_left_cancel₀ hS
    linear_combination key
  have t1 : u ^ (n + 2) / (1 - u ^ 2) = u ^ (n + 1) / (v - u) := by
    rw [show 1 - u ^ 2 = u * (v - u) by linear_combination -huv, pow_succ', mul_div_mul_left _ _ hu0]
  have t2 : v ^ (n + 2) / (1 - v ^ 2) = v ^ (n + 1) / (u - v) := by
    rw [show 1 - v ^ 2 = v * (u - v) by linear_combination -huv, pow_succ', mul_div_mul_left _ _ hv0]
  rw [t1, t2]
  push_cast
  rw [one_div, ← div_eq_mul_inv]
  rw [show u - v = -(v - u) by ring, div_neg, ← sub_eq_add_neg, ← sub_div, div_eq_iff hvu]
  linear_combination hC

end UpperTheory.Esk.RadialIntegralLemmas

open UpperTheory.Esk.RadialIntegralLemmas in
theorem UpperTheory.Esk.radial_integral_formula_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.B2 → UpperTheory.Esk.B6 → UpperTheory.Esk.B4 := by
  intro h1 h2 h3 h22 h6 k hk g hg
  obtain ⟨z0, hz0⟩ := exists_fix g hg
  have h3' := h3
  unfold B1c at h3'
  obtain ⟨h, -, -, hh⟩ := h3'.2.2.2.2.2 z0
  set m := h⁻¹ * g * h with hm_def
  have hmi : m • iP = iP := by
    rw [hm_def, mul_smul, mul_smul, hh, hz0, ← hh, inv_smul_smul]
  obtain ⟨e11, e10⟩ := rot_of_fix m hmi
  have hmv : m.val = (h⁻¹).val * g.val * h.val := by
    rw [hm_def, Units.val_mul, Units.val_mul]
  have htr : g.val.trace = m.val.trace := by
    rw [hmv, Matrix.trace_mul_comm, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  have hdt : g.val.det = m.val.det := by
    rw [hmv, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.det_one, one_mul]
  set a := m 0 0 with ha
  set b := m 0 1 with hb_def
  have htr' : m.val.trace = 2 * a := by rw [Matrix.trace_fin_two]; change m 0 0 + m 1 1 = _; rw [e11]; ring
  have hdt' : m.val.det = a ^ 2 + b ^ 2 := by rw [det_eq, e11, e10]; ring
  have hb : b ≠ 0 := by
    intro h0
    rw [htr, hdt, htr', hdt', h0] at hg
    nlinarith
  obtain ⟨hI, hJ⟩ := F_rot h1 h2 h3 h22 h6 k hk m a b rfl rfl (by rw [e10]) (by rw [e11]) hb
  have hF : ∀ z, F k m z = F k g (h • z) := fun z => F_conj h2 k g h z
  obtain ⟨hc1, hc2⟩ := comp_smul h1 h (F k g)
  change Integrable (F k g) ∧ ∫ z, F k g z = _
  rw [htr, hdt, htr', hdt', ← dualNumber_unit_mul_decomposition k (by omega) a b hb, ← hJ, ← hc2]
  have hF' : (fun z => F k g (h • z)) = F k m := funext fun z => (hF z).symm
  refine ⟨hc1.1 (hF' ▸ hI), ?_⟩
  rw [hF']
