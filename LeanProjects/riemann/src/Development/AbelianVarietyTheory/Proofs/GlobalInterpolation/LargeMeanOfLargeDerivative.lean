import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsTsumVonMangoldtDivRpowLeDiv
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SummableNonPrimeVonMangoldtDivRpow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumPrimesIocEqSumIndicator
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntervalIntegrableDivOfBounded
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

noncomputable section

namespace GlobalTheory.Lin.LargeMean

def pw (k : ℕ) (u : ℝ) : ℝ := u ^ k / (k.factorial : ℝ) * Real.exp (-u)

lemma pw_nonneg (k : ℕ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ pw k u := by
  unfold pw; positivity

lemma pw_le (k : ℕ) {u θ : ℝ} (hu : 0 ≤ u) (hθ : 0 < θ) :
    pw k u ≤ θ ^ k * Real.exp (u / θ - u) := by
  have h := Real.pow_div_factorial_le_exp (u / θ) (by positivity) k
  have e : pw k u = θ ^ k * ((u / θ) ^ k / (k.factorial : ℝ) * Real.exp (-u)) := by
    unfold pw; rw [div_pow]; field_simp
  rw [e, sub_eq_add_neg, Real.exp_add]
  gcongr

lemma pw_le_one (k : ℕ) {u : ℝ} (hu : 0 ≤ u) : pw k u ≤ 1 := by
  simpa using pw_le k hu one_pos

lemma pw_small (K k : ℕ) {u δ : ℝ} (hδ : 0 < δ) (hu : 0 ≤ u) (h : u ≤ δ / 3 * K) (hK : K ≤ k) :
    pw k u ≤ δ ^ k * Real.exp (-(u / 2)) := by
  have h1 := pw_le k hu (θ := δ / 3) (by positivity)
  have h2 : u / (δ / 3) ≤ k := by
    rw [div_le_iff₀ (by positivity)]
    have : (K : ℝ) ≤ k := by exact_mod_cast hK
    nlinarith
  have h3 : Real.exp (u / (δ / 3) - u) ≤ 3 ^ k * Real.exp (-(u / 2)) := by
    have h4 : Real.exp k ≤ 3 ^ k := by
      rw [← mul_one (k : ℝ), Real.exp_nat_mul]
      gcongr
      exact (Real.exp_one_lt_d9.trans (by norm_num)).le
    calc _ ≤ Real.exp (k + -(u / 2)) := by gcongr; linarith
      _ ≤ _ := by rw [Real.exp_add]; gcongr
  calc _ ≤ (δ / 3) ^ k * (3 ^ k * Real.exp (-(u / 2))) := h1.trans (by gcongr)
    _ = _ := by rw [div_pow]; field_simp

lemma pw_large (K k : ℕ) {u δ : ℝ} (hδ : 0 < δ) (h : 32 / δ * K ≤ u) (hK : k ≤ 2 * K) :
    pw k u ≤ δ ^ k * Real.exp (-(u / 2)) := by
  have hu : 0 ≤ u := le_trans (by positivity) h
  have h1 := pw_le k hu (θ := 4) (by positivity)
  have hK' : (k : ℝ) ≤ 2 * K := by exact_mod_cast hK
  have h2 : (4 / δ) ^ k ≤ Real.exp (u / 4) := by
    calc (4 / δ) ^ k ≤ Real.exp (4 / δ) ^ k := by
          gcongr; linarith [Real.add_one_le_exp (4 / δ)]
      _ = Real.exp (k * (4 / δ)) := by rw [Real.exp_nat_mul]
      _ ≤ _ := by
          gcongr
          have : k * (4 / δ) ≤ 2 * K * (4 / δ) := by gcongr
          have e : 32 / δ * K = 4 * (2 * K * (4 / δ)) := by ring
          linarith
  have e : Real.exp (-(u / 2)) = Real.exp (u / 4) * Real.exp (u / 4 - u) := by
    rw [← Real.exp_add]; congr 1; ring
  calc _ ≤ _ := h1
    _ = δ ^ k * ((4 / δ) ^ k * Real.exp (u / 4 - u)) := by rw [div_pow]; field_simp
    _ ≤ _ := by rw [e]; gcongr

lemma pw_pp (k : ℕ) {v r : ℝ} (hr : 0 < r) (hv : 0 ≤ v) :
    pw k (r * v) ≤ (4 * r) ^ k * Real.exp (v / 4) := by
  have h1 := pw_le k (u := r * v) (by positivity) (θ := 4 * r) (by positivity)
  refine h1.trans ?_
  have : r * v / (4 * r) = v / 4 := by field_simp
  rw [this]
  gcongr
  have : 0 ≤ r * v := by positivity
  linarith

lemma hasDerivAt_pw (m : ℕ) (u : ℝ) : HasDerivAt (pw (m + 1)) (pw m u - pw (m + 1) u) u := by
  have h1 := ((hasDerivAt_pow (m + 1) u).div_const ((m + 1).factorial : ℝ)).mul
    (hasDerivAt_neg u).exp
  refine HasDerivAt.congr_deriv (f := pw (m + 1)) h1 ?_
  unfold pw
  rw [Nat.factorial_succ]
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

lemma continuous_pw (k : ℕ) : Continuous (pw k) := by
  unfold pw; fun_prop

lemma term_eq (c : ℕ → ℂ) (k n : ℕ) (r : ℝ) :
    (r : ℂ) ^ k * (((Λ n : ℝ) : ℂ) * c n * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) *
      (n : ℂ) ^ (-((1 + r : ℝ) : ℂ))) = ((Λ n / n * pw k (r * Real.log n) : ℝ) : ℂ) * c n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e : (n : ℂ) ^ (-((1 + r : ℝ) : ℂ)) = ((Real.exp (-(r * Real.log n)) / n : ℝ) : ℂ) := by
    rw [← ofReal_natCast, ← ofReal_neg, ← ofReal_cpow hn'.le]
    congr 1
    rw [Real.rpow_def_of_pos hn', eq_div_iff hn'.ne']
    nth_rewrite 2 [← Real.exp_log hn']
    rw [← Real.exp_add]; congr 1; ring
  rw [e]
  unfold pw
  push_cast
  ring

lemma rpow_form (n : ℕ) (hn : 0 < n) (s x : ℝ) :
    x / (n : ℝ) ^ (1 + s) = x / n * Real.exp (-(s * Real.log n)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_add hn', Real.rpow_one, Real.rpow_def_of_pos hn', Real.exp_neg, mul_comm s]
  field_simp

lemma pointwise (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (K k : ℕ)
    (h1 : K ≤ k) (h2 : k ≤ 2 * K) (n : ℕ) :
    ‖((Λ n / n * pw k (r * Real.log n) : ℝ) : ℂ) * c n -
      (if n ∈ primesIoc (Real.exp (δ / 3 * K / r)) (Real.exp (32 / δ * K / r)) then
        (Real.log n : ℂ) * c n / n *
          ((pw k (r * Real.log n) - pw k (r * Real.log (Real.exp (32 / δ * K / r))) : ℝ) : ℂ)
        else 0)‖ ≤
      δ ^ k * (Λ n / (n : ℝ) ^ (1 + r / 2)) +
        (4 * r) ^ k * ((if n.Prime then 0 else Λ n) / (n : ℝ) ^ (3 / 4 : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [primesIoc]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hΛ : 0 ≤ Λ n := vonMangoldt_nonneg
  have key : ∀ w : ℝ, 0 ≤ w → ‖((Λ n / n * w : ℝ) : ℂ) * c n‖ ≤ Λ n / n * w := by
    intro w hw
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right (by positivity) (hc n)
  have hpw : 0 ≤ pw k (r * Real.log n) := pw_nonneg k (by positivity)
  have fin : ∀ w : ℝ, 0 ≤ w → w ≤ δ ^ k * Real.exp (-(r * Real.log n / 2)) →
      ‖((Λ n / n * w : ℝ) : ℂ) * c n‖ ≤ δ ^ k * (Λ n / (n : ℝ) ^ (1 + r / 2)) := by
    intro w hw h
    refine (key w hw).trans ?_
    rw [rpow_form n hn]
    calc _ ≤ Λ n / n * (δ ^ k * Real.exp (-(r * Real.log n / 2))) := by gcongr
      _ = _ := by ring_nf
  by_cases hp : n.Prime
  · simp only [hp, if_true, zero_div, mul_zero, add_zero]
    split_ifs with hm
    · rw [primesIoc, Finset.mem_filter, Finset.mem_Ioc, Nat.le_floor_iff (Real.exp_pos _).le] at hm
      rw [Real.log_exp]
      have e0 : r * (32 / δ * K / r) = 32 / δ * K := by field_simp
      rw [e0]
      have e : ((Λ n / n * pw k (r * Real.log n) : ℝ) : ℂ) * c n - (Real.log n : ℂ) * c n / n *
          ((pw k (r * Real.log n) - pw k (32 / δ * K) : ℝ) : ℂ) =
          ((Λ n / n * pw k (32 / δ * K) : ℝ) : ℂ) * c n := by
        rw [vonMangoldt_apply_prime hp]; push_cast; ring
      rw [e]
      refine fin _ (pw_nonneg k (by positivity)) ((pw_large K k hδ le_rfl h2).trans ?_)
      have h3 : Real.log n ≤ 32 / δ * K / r := by
        rw [Real.log_le_iff_le_exp hn']; exact hm.1.2
      rw [le_div_iff₀ hr] at h3
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
    · rw [sub_zero]
      refine fin _ hpw ?_
      rw [primesIoc, Finset.mem_filter, Finset.mem_Ioc, Nat.le_floor_iff (Real.exp_pos _).le,
        Nat.floor_lt (Real.exp_pos _).le] at hm
      by_cases h4 : Real.exp (δ / 3 * K / r) < n
      · have h5 : Real.exp (32 / δ * K / r) < n := by
          by_contra h6
          exact hm ⟨⟨h4, not_lt.mp h6⟩, hp⟩
        refine pw_large K k hδ ?_ h2
        have h3 := (Real.lt_log_iff_exp_lt hn').mpr h5
        rw [div_lt_iff₀ hr] at h3
        linarith
      · refine pw_small K k hδ (by positivity) ?_ h1
        have h3 := (Real.log_le_iff_le_exp hn').mpr (not_lt.mp h4)
        rw [le_div_iff₀ hr] at h3
        linarith
  · have hm : n ∉ primesIoc (Real.exp (δ / 3 * K / r)) (Real.exp (32 / δ * K / r)) := by
      rw [primesIoc, Finset.mem_filter]; exact fun h => hp h.2
    simp only [hp, hm, if_false, sub_zero]
    refine (key _ hpw).trans (le_add_of_nonneg_of_le (by positivity) ?_)
    have e : (3 / 4 : ℝ) = 1 + (-1 / 4) := by norm_num
    rw [e, rpow_form n hn]
    calc _ ≤ Λ n / n * ((4 * r) ^ k * Real.exp (Real.log n / 4)) := by
          gcongr; exact pw_pp k hr hl
      _ = _ := by ring_nf

lemma norm_tsum_le_of_close {T P : ℕ → ℂ} {G : ℕ → ℝ} (hP : Summable P)
    (hG : Summable G) (h : ∀ n, ‖T n - P n‖ ≤ G n) :
    ‖∑' n, T n‖ ≤ ‖∑' n, P n‖ + ∑' n, G n := by
  have h1 : Summable fun n => T n - P n := Summable.of_norm_bounded hG h
  have h2 : ∑' n, T n = ∑' n, P n + ∑' n, (T n - P n) := by
    rw [← hP.tsum_add h1]; simp
  rw [h2]
  refine (norm_add_le _ _).trans ?_
  gcongr
  exact tsum_of_norm_bounded hG.hasSum h

lemma series_le (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (K k : ℕ)
    (h1 : K ≤ k) (h2 : k ≤ 2 * K) (hs : Summable fun n : ℕ => Λ n / (n : ℝ) ^ (1 + r / 2)) :
    r ^ k * ‖derSeries c k ((1 + r : ℝ) : ℂ)‖ ≤
      ‖∑ n ∈ primesIoc (Real.exp (δ / 3 * K / r)) (Real.exp (32 / δ * K / r)),
        (Real.log n : ℂ) * c n / n *
          ((pw k (r * Real.log n) - pw k (r * Real.log (Real.exp (32 / δ * K / r))) : ℝ) : ℂ)‖ +
      (δ ^ k * ∑' n : ℕ, Λ n / (n : ℝ) ^ (1 + r / 2) +
        (4 * r) ^ k * ∑' n : ℕ, (if n.Prime then 0 else Λ n) / (n : ℝ) ^ (3 / 4 : ℝ)) := by
  have hq := GlobalTheory.Lin.NonPrimeVonMangoldt.summable_nonPrime_vonMangoldt_div_rpow
  have hP := hasSum_sum_of_ne_finset_zero
    (s := primesIoc (Real.exp (δ / 3 * K / r)) (Real.exp (32 / δ * K / r)))
    (L := SummationFilter.unconditional ℕ)
    (f := fun n : ℕ => if n ∈ primesIoc (Real.exp (δ / 3 * K / r)) (Real.exp (32 / δ * K / r)) then
        (Real.log n : ℂ) * c n / n *
          ((pw k (r * Real.log n) - pw k (r * Real.log (Real.exp (32 / δ * K / r))) : ℝ) : ℂ)
        else 0) (fun n hn => if_neg hn)
  have h := norm_tsum_le_of_close hP.summable ((hs.mul_left (δ ^ k)).add (hq.mul_left ((4 * r) ^ k)))
    (pointwise c hc hr hδ K k h1 h2)
  rw [hP.tsum_eq, (hs.mul_left _).tsum_add (hq.mul_left _), tsum_mul_left, tsum_mul_left,
    Finset.sum_congr rfl (fun n hn => if_pos hn)] at h
  refine le_of_eq_of_le ?_ h
  simp_rw [← term_eq]
  rw [tsum_mul_left, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.le, derSeries]

lemma abel_pw (a : ℕ → ℂ) {r x y : ℝ} (hr : 0 < r) (hx : 1 ≤ x) (hxy : x ≤ y) (m : ℕ) :
    ‖∑ n ∈ primesIoc x y, a n *
        ((pw (m + 1) (r * Real.log n) - pw (m + 1) (r * Real.log y) : ℝ) : ℂ)‖ ≤
      r * ∫ t in x..y, ‖∑ p ∈ primesIoc x t, a p‖ / t := by
  refine GlobalTheory.Lin.abel_primesIoc_weight a (fun t => pw (m + 1) (r * Real.log t))
    (fun t => (pw m (r * Real.log t) - pw (m + 1) (r * Real.log t)) * (r * t⁻¹)) x y r hx hxy
    ?_ ?_ ?_
  · intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact (hasDerivAt_pw m _).comp t ((Real.hasDerivAt_log ht0).const_mul r)
  · have hl : ContinuousOn (fun t => r * Real.log t) (Set.Icc x y) :=
      continuousOn_const.mul (continuousOn_id.log fun t ht => by
        have := ht.1; simp only [id]; linarith)
    refine (((continuous_pw m).comp_continuousOn hl).sub
      ((continuous_pw (m + 1)).comp_continuousOn hl)).mul
      (continuousOn_const.mul (continuousOn_id.inv₀ fun t ht => ?_))
    have := ht.1; simp only [id]; linarith
  · intro t ht
    have ht1 : 1 ≤ t := hx.trans ht.1
    have hu : 0 ≤ r * Real.log t := mul_nonneg hr.le (Real.log_nonneg ht1)
    have h1 : |pw m (r * Real.log t) - pw (m + 1) (r * Real.log t)| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [pw_nonneg m hu, pw_nonneg (m + 1) hu, pw_le_one m hu,
        pw_le_one (m + 1) hu]
    have h2 : 0 ≤ r * t⁻¹ := by have : 0 < t := by linarith
                                positivity
    rw [abs_mul, abs_of_nonneg h2, div_eq_mul_inv]
    exact mul_le_of_le_one_left h2 h1

theorem large_mean_of_large_derivative : ∀ A : ℝ, 1 ≤ A → ∃ a b C r₀ K₀ : ℝ, 0 < a ∧ a < b ∧ 0 < C ∧ 0 < r₀ ∧ ∀ (c : ℕ → ℂ) (r : ℝ) (K k : ℕ), (∀ n, ‖c n‖ ≤ 1) → 0 < r → r ≤ r₀ → K₀ ≤ K → K ≤ k → k ≤ 2 * K → 1 / (A * r) ^ (k + 1) ≤ ‖derSeries c k ((1 + r : ℝ) : ℂ)‖ → Real.exp (-(C * K)) / r ^ 3 ≤ ∫ y in (Real.exp (a * K / r))..(Real.exp (b * K / r)), ‖∑ p ∈ primesIoc (Real.exp (a * K / r)) y, (Real.log p : ℂ) * c p / p‖ ^ 2 / y := by
  intro A hA
  obtain ⟨C, hC, hCs⟩ := GlobalTheory.Lin.exists_tsum_vonMangoldt_div_rpow_le_div
  set B : ℝ := ∑' n : ℕ, (if n.Prime then 0 else Λ n) / (n : ℝ) ^ (3 / 4 : ℝ) with hB
  have hB0 : 0 ≤ B := tsum_nonneg fun n => by
    have : 0 ≤ Λ n := vonMangoldt_nonneg
    positivity
  have hA0 : 0 < A := by linarith
  have hC0 : 0 < C := by linarith
  set η : ℝ := 1 / (16 * C * A) with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 := by
    rw [hη, div_le_one (by positivity)]; nlinarith
  set δ : ℝ := A⁻¹ * η with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := mul_le_one₀ (inv_le_one_of_one_le₀ hA) hη0.le hη1
  have hab : δ / 3 < 32 / δ := by
    rw [div_lt_div_iff₀ (by norm_num) hδ0]; nlinarith
  have hlA : 0 ≤ Real.log A := Real.log_nonneg hA
  refine ⟨δ / 3, 32 / δ, 6 * Real.log A + 4 * (32 / δ), 1 / (8 * A * (B + 1)), 1, by positivity,
    hab, by positivity, by positivity, ?_⟩
  intro c r K k hc hr hr0 hK h1 h2 hD
  have hK1 : 1 ≤ K := by exact_mod_cast hK
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [le_div_iff₀ (by positivity)] at hr0
  have hrA : 8 * (r * A) ≤ 1 := by
    have : 0 ≤ r * A * B := by positivity
    nlinarith
  have hrB : 8 * (r * A * B) ≤ 1 := by
    have : 0 ≤ r * A := by positivity
    nlinarith
  have hr1 : r / 2 ≤ 1 := by nlinarith
  obtain ⟨hs, hsum⟩ := hCs (r / 2) (by positivity) hr1
  have hser := series_le c hc hr hδ0 K (m + 1) h1 h2 hs
  have hxy' : δ / 3 * K / r ≤ 32 / δ * K / r := by gcongr
  have hx : 1 ≤ Real.exp (δ / 3 * K / r) := Real.one_le_exp (by positivity)
  have hxy : Real.exp (δ / 3 * K / r) ≤ Real.exp (32 / δ * K / r) := Real.exp_le_exp.mpr hxy'
  have hab2 := abel_pw (fun p => (Real.log p : ℂ) * c p / p) hr hx hxy m
  have hcs := GlobalTheory.Lin.sq_integral_primeSum_div_le (fun p => (Real.log p : ℂ) * c p / p) _ _ hx hxy
  have hI2 : 0 ≤ ∫ y in (Real.exp (δ / 3 * K / r))..(Real.exp (32 / δ * K / r)),
      ‖∑ p ∈ primesIoc (Real.exp (δ / 3 * K / r)) y, (Real.log p : ℂ) * c p / p‖ ^ 2 / y :=
    intervalIntegral.integral_nonneg hxy fun t ht => by
      have : 0 < t := by linarith [ht.1]
      positivity
  rw [← Real.exp_sub, Real.log_exp] at hcs
  rw [← hB] at hser
  generalize (∫ y in (Real.exp (δ / 3 * K / r))..(Real.exp (32 / δ * K / r)),
      ‖∑ p ∈ primesIoc (Real.exp (δ / 3 * K / r)) y, (Real.log p : ℂ) * c p / p‖ ^ 2 / y) = I₂ at *
  generalize (∫ y in (Real.exp (δ / 3 * K / r))..(Real.exp (32 / δ * K / r)),
      ‖∑ p ∈ primesIoc (Real.exp (δ / 3 * K / r)) y, (Real.log p : ℂ) * c p / p‖ / y) = I₁ at *
  set M : ℝ := A⁻¹ ^ (m + 1) * (A * r)⁻¹ with hM
  have hM0 : 0 < M := by positivity
  have e1 : M ≤ r ^ (m + 1) * ‖derSeries c (m + 1) ((1 + r : ℝ) : ℂ)‖ := by
    calc M = r ^ (m + 1) * (1 / (A * r) ^ (m + 1 + 1)) := by
          rw [hM, inv_pow, mul_pow]; field_simp; ring
      _ ≤ _ := by gcongr
  have e2 : δ ^ (m + 1) * ∑' n : ℕ, Λ n / (n : ℝ) ^ (1 + r / 2) ≤ M / 8 := by
    have h3 : η ^ (m + 1) ≤ η := pow_le_of_le_one hη0.le hη1 (by omega)
    calc _ ≤ δ ^ (m + 1) * (C / (r / 2)) := by gcongr
      _ = A⁻¹ ^ (m + 1) * η ^ (m + 1) * (C / (r / 2)) := by rw [hδ, mul_pow]
      _ ≤ A⁻¹ ^ (m + 1) * η * (C / (r / 2)) := by gcongr
      _ = M / 8 := by rw [hM, hη]; field_simp; ring
  have e3 : (4 * r) ^ (m + 1) * B ≤ M / 8 := by
    have h3 : 4 * r ≤ A⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ hA0]
      have : 0 ≤ r * A := by positivity
      nlinarith
    have h4 : B ≤ (A * r)⁻¹ / 8 := by
      rw [inv_eq_one_div, div_div, le_div_iff₀ (by positivity)]
      nlinarith
    calc _ ≤ A⁻¹ ^ (m + 1) * ((A * r)⁻¹ / 8) := by gcongr
      _ = _ := by rw [hM]; ring
  have e4 : M / (2 * r) ≤ I₁ := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have e5 : (M / (2 * r)) ^ 2 ≤ (32 / δ * K / r) * I₂ := by
    calc _ ≤ I₁ ^ 2 := by gcongr
      _ ≤ _ := hcs
      _ ≤ _ := by
        gcongr
        have : 0 ≤ δ / 3 * K / r := by positivity
        linarith
  have hK0 : (0 : ℝ) < K := by linarith
  have e6 : A ^ (2 * (m + 2)) * (4 * (32 / δ * K)) ≤
      Real.exp ((6 * Real.log A + 4 * (32 / δ)) * K) := by
    have h3 : A ^ (2 * (m + 2)) ≤ A ^ (6 * K) := pow_le_pow_right₀ hA (by omega)
    have h4 : A ^ (6 * K) = Real.exp (6 * Real.log A * K) := by
      nth_rewrite 1 [← Real.exp_log hA0]
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [add_mul, Real.exp_add, ← h4]
    gcongr
    linarith [Real.add_one_le_exp (4 * (32 / δ) * K)]
  rw [← div_le_iff₀' (by positivity)] at e5
  refine le_trans ?_ e5
  calc _ ≤ (A ^ (2 * (m + 2)) * (4 * (32 / δ * K)))⁻¹ / r ^ 3 := by
        rw [Real.exp_neg]; gcongr
    _ = _ := by
        rw [hM, inv_pow]; field_simp; ring

end GlobalTheory.Lin.LargeMean

end
