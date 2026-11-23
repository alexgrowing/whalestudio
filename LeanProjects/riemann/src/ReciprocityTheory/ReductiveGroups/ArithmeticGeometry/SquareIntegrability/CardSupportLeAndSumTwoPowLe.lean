import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.IntegralMulConjGaussianEqCoeffNormSq

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory

open Complex in

noncomputable def fockIP {g : ℕ} (F G : EuclideanSpace ℂ (Fin g) → ℂ) : ℂ :=
  ((Real.pi ^ g)⁻¹ : ℝ) * ∫ z, F z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ)

open Complex in

noncomputable def fockU {g : ℕ} (a : EuclideanSpace ℂ (Fin g)) (F : EuclideanSpace ℂ (Fin g) → ℂ) :
    EuclideanSpace ℂ (Fin g) → ℂ :=
  fun z => cexp ((∑ i, z i * (starRingEnd ℂ) (a i)) - (‖a‖ ^ 2 / 2 : ℝ)) * F (z - a)

def IsPolyLE {g : ℕ} (c : ℕ) (F : EuclideanSpace ℂ (Fin g) → ℂ) : Prop :=
  ∃ p : MvPolynomial (Fin g) ℂ, p.totalDegree ≤ c ∧ ∀ z, F z = MvPolynomial.eval (fun i => z i) p

theorem mul_le_sqrt_mul_sqrt_mul_avg {u v A B P Q t : ℝ} (hv : 0 ≤ v) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (ht : 0 < t) (huP : u ^ 2 ≤ A * P) (hvQ : v ^ 2 ≤ B * Q) :
    u * v ≤ Real.sqrt A * Real.sqrt B * ((t * P + Q / t) / 2) := by
  have hu : |u| ≤ Real.sqrt A * Real.sqrt P := by
    rw [← Real.sqrt_mul hA, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt huP
  have hv' : v ≤ Real.sqrt B * Real.sqrt Q := by
    rw [← Real.sqrt_mul hB, ← Real.sqrt_sq hv]
    exact Real.sqrt_le_sqrt hvQ
  have hPQ : Real.sqrt P * Real.sqrt Q ≤ (t * P + Q / t) / 2 := by
    have key : 2 * t * (Real.sqrt P * Real.sqrt Q) ≤ t ^ 2 * P + Q := by
      nlinarith [sq_nonneg (t * Real.sqrt P - Real.sqrt Q), Real.sq_sqrt hP, Real.sq_sqrt hQ]
    have e : (t * P + Q / t) / 2 = (t ^ 2 * P + Q) / (2 * t) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    linarith
  calc u * v ≤ |u| * v := mul_le_mul_of_nonneg_right (le_abs_self u) hv
    _ ≤ (Real.sqrt A * Real.sqrt P) * (Real.sqrt B * Real.sqrt Q) :=
        mul_le_mul hu hv' hv (by positivity)
    _ = Real.sqrt A * Real.sqrt B * (Real.sqrt P * Real.sqrt Q) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hPQ (by positivity)

theorem sqrt_exp_neg_div_eight (x : ℝ) : Real.sqrt (Real.exp (-x / 8)) = Real.exp (-x / 16) := by
  rw [show -x / 8 = -x / 16 + -x / 16 by ring, Real.exp_add,
    Real.sqrt_mul_self (Real.exp_pos _).le]

theorem fockInner_self_re_eq_coeffNormSq {g : ℕ} (p : MvPolynomial (Fin g) ℂ) (F : EuclideanSpace ℂ (Fin g) → ℂ)
    (hF : ∀ z, F z = MvPolynomial.eval (fun i => z i) p) : (fockIP F F).re = fa1N p := by
  unfold fockIP
  rw [integral_mul_conj_gaussian_eq_coeffNormSq p F hF, Complex.ofReal_re]

theorem card_support_le_and_sum_two_pow_le {g c : ℕ} (p : MvPolynomial (Fin g) ℂ) (hp : p.totalDegree ≤ c) :
    (p.support.card : ℝ) ≤ 2 ^ (g + c) ∧
      ∑ α ∈ p.support, (2 : ℝ) ^ (g + ∑ i, α i) ≤ 2 ^ (g + c) * 2 ^ (g + c) := by
  have hdeg : ∀ α ∈ p.support, ∑ i, α i ≤ c := fun α hα => by
    have := MvPolynomial.le_totalDegree hα
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
    exact this.trans hp
  have h1 : (p.support.card : ℝ) ≤ ∑ α ∈ p.support, (2 : ℝ) ^ c * ∏ i, (1 / 2 : ℝ) ^ α i := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun α hα => ?_
    rw [Nat.cast_one, Finset.prod_pow_eq_pow_sum, one_div, inv_pow, ← div_eq_mul_inv,
      one_le_div (by positivity)]
    exact pow_le_pow_right₀ (by norm_num) (hdeg α hα)
  have hsub : p.support.image (fun α : Fin g →₀ ℕ => (α : Fin g → ℕ)) ⊆
      Fintype.piFinset (fun _ : Fin g => Finset.range (c + 1)) := by
    intro x hx
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hx
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact (Finset.single_le_sum (fun j _ => Nat.zero_le (α j)) (Finset.mem_univ i)).trans
      (hdeg α hα)
  have h2 : ∑ α ∈ p.support, ∏ i, (1 / 2 : ℝ) ^ α i ≤
      ∏ _i : Fin g, ∑ k ∈ Finset.range (c + 1), (1 / 2 : ℝ) ^ k := by
    calc ∑ α ∈ p.support, ∏ i, (1 / 2 : ℝ) ^ α i
        = ∑ x ∈ p.support.image (fun α : Fin g →₀ ℕ => (α : Fin g → ℕ)),
            ∏ i, (1 / 2 : ℝ) ^ x i :=
          (Finset.sum_image (f := fun x : Fin g → ℕ => ∏ i, (1 / 2 : ℝ) ^ x i) (s := p.support)
            (g := fun α : Fin g →₀ ℕ => (α : Fin g → ℕ))
            (fun a _ b _ h => Finsupp.ext (congrFun h))).symm
      _ ≤ ∑ x ∈ Fintype.piFinset (fun _ : Fin g => Finset.range (c + 1)),
            ∏ i, (1 / 2 : ℝ) ^ x i :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = _ := (Finset.prod_univ_sum _ _).symm
  have hcard : (p.support.card : ℝ) ≤ 2 ^ (g + c) := by
    calc (p.support.card : ℝ) ≤ ∑ α ∈ p.support, (2 : ℝ) ^ c * ∏ i, (1 / 2 : ℝ) ^ α i := h1
      _ = 2 ^ c * ∑ α ∈ p.support, ∏ i, (1 / 2 : ℝ) ^ α i := by rw [Finset.mul_sum]
      _ ≤ 2 ^ c * ∏ _i : Fin g, ∑ k ∈ Finset.range (c + 1), (1 / 2 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ 2 ^ c * ∏ _i : Fin g, (2 : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _ => by positivity)
            (fun _ _ => sum_geometric_two_le _)) (by positivity)
      _ = 2 ^ (g + c) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_add]
          ring
  refine ⟨hcard, ?_⟩
  calc ∑ α ∈ p.support, (2 : ℝ) ^ (g + ∑ i, α i) ≤ ∑ α ∈ p.support, (2 : ℝ) ^ (g + c) :=
        Finset.sum_le_sum fun α hα => pow_le_pow_right₀ (by norm_num) (by have := hdeg α hα; omega)
    _ = p.support.card * 2 ^ (g + c) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ (g + c) * 2 ^ (g + c) := mul_le_mul_of_nonneg_right hcard (by positivity)

theorem fockU_coeff_le {g c : ℕ} (a : EuclideanSpace ℂ (Fin g)) (F G : EuclideanSpace ℂ (Fin g) → ℂ)
    (hF : IsPolyLE c F) (hG : IsPolyLE c G) :
    ‖fockIP (fockU a F) G‖ ≤ 2 ^ (1 + 3 * ((g : ℝ) + c) / 2) * Real.exp (-‖a‖ ^ 2 / 16) *
      Real.sqrt (fockIP F F).re * Real.sqrt (fockIP G G).re := by
  obtain ⟨p, hpc, hp⟩ := hF
  obtain ⟨q, hqc, hq⟩ := hG
  rw [fockInner_self_re_eq_coeffNormSq p F hp, fockInner_self_re_eq_coeffNormSq q G hq]
  have hNF := coeffNormSq_nonneg p
  have hNG := coeffNormSq_nonneg q

  have hre : ∀ z : EuclideanSpace ℂ (Fin g), (∑ i, z i * (starRingEnd ℂ) (a i)).re =
      (‖z‖ ^ 2 + ‖a‖ ^ 2 - ‖z - a‖ ^ 2) / 2 := by
    intro z
    have h1 : (∑ i, z i * (starRingEnd ℂ) (a i)) = inner ℂ a z := by
      simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
    have h2 := norm_sub_sq (𝕜 := ℂ) z a
    have h3 := inner_re_symm (𝕜 := ℂ) z a
    simp only [RCLike.re_to_complex] at h2 h3
    rw [h1]
    linarith
  have hI : ∀ z : EuclideanSpace ℂ (Fin g),
      ‖fockU a F z * (starRingEnd ℂ) (G z) * ((Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ)‖ =
        ‖F (z - a)‖ * ‖G z‖ * Real.exp (-‖z - a‖ ^ 2 / 2 - ‖z‖ ^ 2 / 2) := by
    intro z
    simp only [fockU, norm_mul, Complex.norm_exp, Complex.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [Complex.sub_re, Complex.ofReal_re, hre z]
    have e : Real.exp ((‖z‖ ^ 2 + ‖a‖ ^ 2 - ‖z - a‖ ^ 2) / 2 - ‖a‖ ^ 2 / 2) *
        Real.exp (-‖z‖ ^ 2) = Real.exp (-‖z - a‖ ^ 2 / 2 - ‖z‖ ^ 2 / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← e]
    ring
  have hmain : ∀ M : EuclideanSpace ℂ (Fin g) → ℝ, Integrable M →
      (∀ z, ‖F (z - a)‖ * ‖G z‖ * Real.exp (-‖z - a‖ ^ 2 / 2 - ‖z‖ ^ 2 / 2) ≤ M z) →
      ‖fockIP (fockU a F) G‖ ≤ (Real.pi ^ g)⁻¹ * ∫ z, M z := by
    intro M hM hle
    unfold fockIP
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le hM
      (Filter.Eventually.of_forall fun z => (hI z).le.trans (hle z))) (by positivity)
  have hexp2 : ∀ x : ℝ, Real.exp (x / 2) ^ 2 = Real.exp x := by
    intro x
    rw [sq, ← Real.exp_add]
    ring_nf
  have hs : 0 ≤ Real.sqrt (fa1N p) * Real.sqrt (fa1N q) := by positivity
  obtain ⟨hcp, hsp⟩ := card_support_le_and_sum_two_pow_le p hpc
  obtain ⟨hcq, hsq⟩ := card_support_le_and_sum_two_pow_le q hqc
  have hi1p : Integrable (fun z : EuclideanSpace ℂ (Fin g) => fa1K p z * Real.exp (-‖z‖ ^ 2)) := by
    simpa using integrable_monomialKernel_mul_gaussian p (b := 1) one_pos
  have hi1q : Integrable (fun z : EuclideanSpace ℂ (Fin g) => fa1K q z * Real.exp (-‖z‖ ^ 2)) := by
    simpa using integrable_monomialKernel_mul_gaussian q (b := 1) one_pos
  have hi2p : Integrable (fun z : EuclideanSpace ℂ (Fin g) =>
      fa1K p z * Real.exp (-(1 / 2) * ‖z‖ ^ 2)) := integrable_monomialKernel_mul_gaussian p (by norm_num)
  have hi2q : Integrable (fun z : EuclideanSpace ℂ (Fin g) =>
      fa1K q z * Real.exp (-(1 / 2) * ‖z‖ ^ 2)) := integrable_monomialKernel_mul_gaussian q (by norm_num)

  have hB1 : ‖fockIP (fockU a F) G‖ ≤
      Real.sqrt (fa1N p) * Real.sqrt (fa1N q) * 2 ^ (g + c) := by
    have hM : Integrable (fun z : EuclideanSpace ℂ (Fin g) =>
        Real.sqrt (fa1N p) * Real.sqrt (fa1N q) * ((fa1K p (z - a) * Real.exp (-‖z - a‖ ^ 2) +
          fa1K q z * Real.exp (-‖z‖ ^ 2)) / 2)) :=
      (((hi1p.comp_sub_right a).add hi1q).div_const 2).const_mul _
    refine (hmain _ hM (fun z => ?_)).trans ?_
    · have hu : (‖F (z - a)‖ * Real.exp (-‖z - a‖ ^ 2 / 2)) ^ 2 ≤
          fa1N p * (fa1K p (z - a) * Real.exp (-‖z - a‖ ^ 2)) := by
        rw [mul_pow, hexp2, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (by rw [hp]; exact norm_eval_sq_le p (z - a)) (Real.exp_pos _).le
      have hv : (‖G z‖ * Real.exp (-‖z‖ ^ 2 / 2)) ^ 2 ≤
          fa1N q * (fa1K q z * Real.exp (-‖z‖ ^ 2)) := by
        rw [mul_pow, hexp2, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (by rw [hq]; exact norm_eval_sq_le q z) (Real.exp_pos _).le
      have hab := mul_le_sqrt_mul_sqrt_mul_avg (by positivity) hNF hNG
        (mul_nonneg (monomialKernel_nonneg p _) (Real.exp_pos _).le)
        (mul_nonneg (monomialKernel_nonneg q _) (Real.exp_pos _).le) one_pos hu hv
      calc ‖F (z - a)‖ * ‖G z‖ * Real.exp (-‖z - a‖ ^ 2 / 2 - ‖z‖ ^ 2 / 2)
          = (‖F (z - a)‖ * Real.exp (-‖z - a‖ ^ 2 / 2)) * (‖G z‖ * Real.exp (-‖z‖ ^ 2 / 2)) := by
            rw [show -‖z - a‖ ^ 2 / 2 - ‖z‖ ^ 2 / 2 = -‖z - a‖ ^ 2 / 2 + -‖z‖ ^ 2 / 2 by ring,
              Real.exp_add]
            ring
        _ ≤ _ := hab
        _ = _ := by ring
    · have hT : ∫ z : EuclideanSpace ℂ (Fin g), fa1K p (z - a) * Real.exp (-‖z - a‖ ^ 2) =
          ∫ z : EuclideanSpace ℂ (Fin g), fa1K p z * Real.exp (-‖z‖ ^ 2) :=
        integral_sub_right_eq_self (fun z => fa1K p z * Real.exp (-‖z‖ ^ 2)) a
      rw [integral_const_mul, integral_div, integral_add (hi1p.comp_sub_right a) hi1q, hT,
        integral_monomialKernel_mul_gaussian, integral_monomialKernel_mul_gaussian]
      have hpi : 0 < Real.pi ^ g := by positivity
      have e : (Real.pi ^ g)⁻¹ * (Real.sqrt (fa1N p) * Real.sqrt (fa1N q) *
          ((Real.pi ^ g * p.support.card + Real.pi ^ g * q.support.card) / 2)) =
          Real.sqrt (fa1N p) * Real.sqrt (fa1N q) * ((p.support.card + q.support.card) / 2) := by
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left (by linarith) hs

  have hB2 : ‖fockIP (fockU a F) G‖ ≤ Real.exp (-‖a‖ ^ 2 / 8) *
      (Real.sqrt (fa1N p) * Real.sqrt (fa1N q) * (2 ^ (g + c) * 2 ^ (g + c))) := by
    have hM : Integrable (fun z : EuclideanSpace ℂ (Fin g) => Real.exp (-‖a‖ ^ 2 / 8) *
        (Real.sqrt (fa1N p) * Real.sqrt (fa1N q) *
          ((fa1K p (z - a) * Real.exp (-(1 / 2) * ‖z - a‖ ^ 2) +
            fa1K q z * Real.exp (-(1 / 2) * ‖z‖ ^ 2)) / 2))) :=
      ((((hi2p.comp_sub_right a).add hi2q).div_const 2).const_mul _).const_mul _
    refine (hmain _ hM (fun z => ?_)).trans ?_
    · have hu : (‖F (z - a)‖ * Real.exp (-(1 / 2) * ‖z - a‖ ^ 2 / 2)) ^ 2 ≤
          fa1N p * (fa1K p (z - a) * Real.exp (-(1 / 2) * ‖z - a‖ ^ 2)) := by
        rw [mul_pow, hexp2, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (by rw [hp]; exact norm_eval_sq_le p (z - a)) (Real.exp_pos _).le
      have hv : (‖G z‖ * Real.exp (-(1 / 2) * ‖z‖ ^ 2 / 2)) ^ 2 ≤
          fa1N q * (fa1K q z * Real.exp (-(1 / 2) * ‖z‖ ^ 2)) := by
        rw [mul_pow, hexp2, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (by rw [hq]; exact norm_eval_sq_le q z) (Real.exp_pos _).le
      have hab := mul_le_sqrt_mul_sqrt_mul_avg (by positivity) hNF hNG
        (mul_nonneg (monomialKernel_nonneg p _) (Real.exp_pos _).le)
        (mul_nonneg (monomialKernel_nonneg q _) (Real.exp_pos _).le) one_pos hu hv
      have hpar : ‖a‖ ^ 2 ≤ 2 * (‖z - a‖ ^ 2 + ‖z‖ ^ 2) := by
        have h := norm_sub_le z (z - a)
        rw [sub_sub_cancel] at h
        nlinarith [norm_nonneg a, norm_nonneg z, norm_nonneg (z - a), sq_nonneg (‖z‖ - ‖z - a‖)]
      have hexpb : Real.exp (-‖z - a‖ ^ 2 / 2 - ‖z‖ ^ 2 / 2) ≤ Real.exp (-‖a‖ ^ 2 / 8) *
          (Real.exp (-(1 / 2) * ‖z - a‖ ^ 2 / 2) * Real.exp (-(1 / 2) * ‖z‖ ^ 2 / 2)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        exact Real.exp_le_exp.2 (by nlinarith)
      calc ‖F (z - a)‖ * ‖G z‖ * Real.exp (-‖z - a‖ ^ 2 / 2 - ‖z‖ ^ 2 / 2)
          ≤ ‖F (z - a)‖ * ‖G z‖ * (Real.exp (-‖a‖ ^ 2 / 8) *
            (Real.exp (-(1 / 2) * ‖z - a‖ ^ 2 / 2) * Real.exp (-(1 / 2) * ‖z‖ ^ 2 / 2))) :=
            mul_le_mul_of_nonneg_left hexpb (by positivity)
        _ = Real.exp (-‖a‖ ^ 2 / 8) * ((‖F (z - a)‖ * Real.exp (-(1 / 2) * ‖z - a‖ ^ 2 / 2)) *
            (‖G z‖ * Real.exp (-(1 / 2) * ‖z‖ ^ 2 / 2))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hab (Real.exp_pos _).le
        _ = _ := by ring
    · have hT : ∫ z : EuclideanSpace ℂ (Fin g), fa1K p (z - a) * Real.exp (-(1 / 2) * ‖z - a‖ ^ 2) =
          ∫ z : EuclideanSpace ℂ (Fin g), fa1K p z * Real.exp (-(1 / 2) * ‖z‖ ^ 2) :=
        integral_sub_right_eq_self (fun z => fa1K p z * Real.exp (-(1 / 2) * ‖z‖ ^ 2)) a
      rw [integral_const_mul, integral_const_mul, integral_div,
        integral_add (hi2p.comp_sub_right a) hi2q, hT, integral_monomialKernel_mul_gaussian_half, integral_monomialKernel_mul_gaussian_half]
      have hpi : 0 < Real.pi ^ g := by positivity
      have e : (Real.pi ^ g)⁻¹ * (Real.exp (-‖a‖ ^ 2 / 8) * (Real.sqrt (fa1N p) * Real.sqrt (fa1N q) *
          ((Real.pi ^ g * ∑ α ∈ p.support, (2 : ℝ) ^ (g + ∑ i, α i) +
            Real.pi ^ g * ∑ α ∈ q.support, (2 : ℝ) ^ (g + ∑ i, α i)) / 2))) =
          Real.exp (-‖a‖ ^ 2 / 8) * (Real.sqrt (fa1N p) * Real.sqrt (fa1N q) *
            ((∑ α ∈ p.support, (2 : ℝ) ^ (g + ∑ i, α i) +
              ∑ α ∈ q.support, (2 : ℝ) ^ (g + ∑ i, α i)) / 2)) := by
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hs)
        (Real.exp_pos _).le

  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (2 : ℝ) ^ (((g : ℝ) + c) / 2) := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by
    rw [hy]
    positivity
  have hyT : y ^ 2 = (2 : ℝ) ^ (g + c) := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      show ((g : ℝ) + c) / 2 * ((2 : ℕ) : ℝ) = ((g + c : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hR : (2 : ℝ) ^ (1 + 3 * ((g : ℝ) + c) / 2) = 2 * y ^ 3 := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), Real.rpow_add (by norm_num),
      Real.rpow_one, show 3 * ((g : ℝ) + c) / 2 = ((g : ℝ) + c) / 2 * ((3 : ℕ) : ℝ) by push_cast; ring]
  have hE : Real.exp (-‖a‖ ^ 2 / 16) ^ 2 = Real.exp (-‖a‖ ^ 2 / 8) := by
    rw [sq, ← Real.exp_add]
    ring_nf
  have hX0 := norm_nonneg (fockIP (fockU a F) G)
  rw [hR]
  have key : ‖fockIP (fockU a F) G‖ ^ 2 ≤ (2 * y ^ 3 * Real.exp (-‖a‖ ^ 2 / 16) *
      Real.sqrt (fa1N p) * Real.sqrt (fa1N q)) ^ 2 := by
    have h12 := mul_le_mul hB1 hB2 hX0 (by positivity)
    have e1 : Real.sqrt (fa1N p) * Real.sqrt (fa1N q) * 2 ^ (g + c) * (Real.exp (-‖a‖ ^ 2 / 8) *
        (Real.sqrt (fa1N p) * Real.sqrt (fa1N q) * (2 ^ (g + c) * 2 ^ (g + c)))) =
        Real.sqrt (fa1N p) ^ 2 * Real.sqrt (fa1N q) ^ 2 * y ^ 6 * Real.exp (-‖a‖ ^ 2 / 8) := by
      rw [← hyT]
      ring
    have e2 : (2 * y ^ 3 * Real.exp (-‖a‖ ^ 2 / 16) * Real.sqrt (fa1N p) * Real.sqrt (fa1N q)) ^ 2 =
        4 * (Real.sqrt (fa1N p) ^ 2 * Real.sqrt (fa1N q) ^ 2 * y ^ 6 * Real.exp (-‖a‖ ^ 2 / 8)) := by
      rw [← hE]
      ring
    rw [sq, e2]
    rw [e1] at h12
    have : 0 ≤ Real.sqrt (fa1N p) ^ 2 * Real.sqrt (fa1N q) ^ 2 * y ^ 6 * Real.exp (-‖a‖ ^ 2 / 8) := by
      positivity
    linarith
  exact (pow_le_pow_iff_left₀ hX0 (by positivity) two_ne_zero).1 key

end ReciprocityTheory.ChartRestriction.G.I2
