import Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes
import Formalism.GL3MeanSquares.HookFormulaTorsion.SmoothedRemainderRealIntegralFormula
import Formalism.GL3MeanSquares.HookFormulaTorsion.ExpNegLeDivPowFour
import Formalism.GL3MeanSquares.HookFormulaTorsion.PrimesInProgressionCountLowerBound
import Formalism.GL3MeanSquares.HookFormulaTorsion.SmallPrimeFactorSumBound
import Formalism.GL3MeanSquares.HookFormulaTorsion.SmoothedRemainderRealHasDerivBound
import Formalism.GL3MeanSquares.HookFormulaTorsion.PsiZeroIntegral
import Formalism.GL3MeanSquares.HookFormulaTorsion.HasDerivAtLogSquareAntiderivative
import Formalism.GL3MeanSquares.HookFormulaTorsion.ShortIntervalImpliesProgressionsStatement
import Formalism.GL3MeanSquares.HookFormulaTorsion.CharacterEstimateOfHypothesis
import Formalism.SizeWindowBrackets.ChainSlopeWindows.LipschitzWeightAndMinimum
import Formalism.SizeWindowBrackets.ChainSlopeWindows.PrimeCongruenceConditions
import Formalism.ZetaNonvanishing.GzLipschitz
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts

noncomputable section

namespace Formalism.MainNotions.ShortIntervalPrimes.Br

open Finset Filter Topology ArithmeticFunction MeasureTheory Formalism.MainNotions.GlobalTheoryTheory
open Formalism.HermitianLattices.GL2PrimeSums (psum psumR Gchi Gone)
open Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN (truncC truncR sum_vM_le floor_div_le lip_triv)

def Fc (c : ℕ → ℂ) (ell : ℂ) (y : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊y⌋₊, c n * ((y / n - 1 : ℝ) : ℂ) + (y : ℂ) * ell

lemma Fc_lip (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ Λ n) (ell : ℂ) (y z : ℝ) (hy : 1 ≤ y) :
    ‖Fc c ell y - Fc c ell z‖ ≤ |y - z| * (Real.log (max y z) + (Real.log 4 + 4) + ‖ell‖) := by
  have hyM : ⌊y⌋₊ ≤ ⌊max y z⌋₊ := Nat.floor_le_floor (le_max_left _ _)
  have hzM : ⌊z⌋₊ ≤ ⌊max y z⌋₊ := Nat.floor_le_floor (le_max_right _ _)
  have hmax1 : 1 ≤ max y z := le_trans hy (le_max_left _ _)
  have hM1 : 1 ≤ ⌊max y z⌋₊ := Nat.le_floor (by simpa using hmax1)
  have ty := truncC c y _ hyM
  have tz := truncC c z _ hzM
  unfold Fc
  rw [ty, tz]
  have e : (∑ n ∈ Icc 1 ⌊max y z⌋₊, c n * ((max (y / n - 1) 0 : ℝ) : ℂ) + (y : ℂ) * ell)
      - (∑ n ∈ Icc 1 ⌊max y z⌋₊, c n * ((max (z / n - 1) 0 : ℝ) : ℂ) + (z : ℂ) * ell)
      = ∑ n ∈ Icc 1 ⌊max y z⌋₊, c n * ((max (y / n - 1) 0 - max (z / n - 1) 0 : ℝ) : ℂ)
        + ((y - z : ℝ) : ℂ) * ell := by
    have : ∀ n : ℕ, c n * ((max (y / n - 1) 0 - max (z / n - 1) 0 : ℝ) : ℂ)
        = c n * ((max (y / n - 1) 0 : ℝ) : ℂ) - c n * ((max (z / n - 1) 0 : ℝ) : ℂ) := by
      intro n; push_cast; ring
    simp only [this, Finset.sum_sub_distrib]
    push_cast; ring
  rw [e]
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖∑ n ∈ Icc 1 ⌊max y z⌋₊, c n * ((max (y / n - 1) 0 - max (z / n - 1) 0 : ℝ) : ℂ)‖
      ≤ |y - z| * Formalism.LogFactorialMertensBounds.A ⌊max y z⌋₊ := by
    refine le_trans (norm_sum_le _ _) ?_
    unfold Formalism.LogFactorialMertensBounds.A
    rw [← Formalism.LogFactorialMertensBounds.Icc_one_eq_Ioc, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have ha : |max (y / n - 1) 0 - max (z / n - 1) 0| ≤ |y - z| / n := by
      refine le_trans (abs_max_sub_max_le_abs _ _ _) ?_
      have : y / n - 1 - (z / n - 1) = (y - z) / n := by ring
      rw [this, abs_div, abs_of_pos hn0]
    calc ‖c n‖ * |max (y / n - 1) 0 - max (z / n - 1) 0|
        ≤ Λ n * (|y - z| / n) := mul_le_mul (hc n) ha (abs_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
      _ = |y - z| * (Λ n / n) := by ring
  have h2 : ‖((y - z : ℝ) : ℂ) * ell‖ = |y - z| * ‖ell‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h3 := Formalism.LogFactorialMertensBounds.mertens_upper _ hM1
  have h4 : Real.log (⌊max y z⌋₊ : ℝ) ≤ Real.log (max y z) :=
    Real.log_le_log (by exact_mod_cast hM1) (Nat.floor_le (by linarith))
  rw [h2]
  have h5 : |y - z| * Formalism.LogFactorialMertensBounds.A ⌊max y z⌋₊ ≤ |y - z| * (Real.log (max y z) + (Real.log 4 + 4)) :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  nlinarith

lemma wFc (c : ℕ → ℂ) (ell : ℂ) (A w : ℝ) (hw : 0 < w) (M : ℕ) (hM : ⌊A / w⌋₊ ≤ M) :
    (w : ℂ) * Fc c ell (A / w)
      = ∑ n ∈ Icc 1 M, c n * ((max (A / n - w) 0 : ℝ) : ℂ) + (A : ℂ) * ell := by
  have t := truncC c (A / w) M hM
  unfold Fc
  rw [t, mul_add, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : (n : ℝ) ≠ 0 := by
      have : (0 : ℝ) < n := by exact_mod_cast hn.1
      exact this.ne'
    have : max (A / n - w) 0 = w * max (A / w / n - 1) 0 := by
      rw [mul_max_of_nonneg _ _ hw.le, mul_zero]
      congr 1
      field_simp
    rw [this]; push_cast; ring
  · rw [← mul_assoc, ← Complex.ofReal_mul, mul_div_cancel₀ _ hw.ne']

lemma Fc_lipW (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ Λ n) (ell : ℂ)
    (A w w' : ℝ) (hA : 0 < A) (hw : 0 < w) (hw' : 0 < w') :
    ‖(w : ℂ) * Fc c ell (A / w) - (w' : ℂ) * Fc c ell (A / w')‖ ≤ 3 * A / min w w' * |w - w'| := by
  have hμ : 0 < min w w' := lt_min hw hw'
  rw [wFc c ell A w hw _ (floor_div_le hA.le hμ (min_le_left _ _)),
    wFc c ell A w' hw' _ (floor_div_le hA.le hμ (min_le_right _ _)), add_sub_add_right_eq_sub,
    ← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ n ∈ Icc 1 ⌊A / min w w'⌋₊,
      ‖c n * ((max (A / n - w) 0 : ℝ) : ℂ) - c n * ((max (A / n - w') 0 : ℝ) : ℂ)‖ ≤ Λ n * |w - w'| := by
    intro n _
    rw [← mul_sub, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have ha : |max (A / n - w) 0 - max (A / n - w') 0| ≤ |w - w'| := by
      refine le_trans (abs_max_sub_max_le_abs _ _ _) ?_
      have : A / n - w - (A / n - w') = -(w - w') := by ring
      rw [this, abs_neg]
    exact mul_le_mul (hc n) ha (abs_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul]
  have := sum_vM_le (Y := A / min w w') (by positivity)
  calc (∑ n ∈ Icc 1 ⌊A / min w w'⌋₊, Λ n) * |w - w'| ≤ (3 * (A / min w w')) * |w - w'| :=
        mul_le_mul_of_nonneg_right this (abs_nonneg _)
    _ = 3 * A / min w w' * |w - w'| := by ring

lemma log_form {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) (A : ℝ) (hA : 0 < A)
    (h : ∀ w w' : ℝ, 0 < w → 0 < w' → ‖F w - F w'‖ ≤ 3 * A / min w w' * |w - w'|)
    (w1 w2 : ℝ) (h1 : 0 < w1) (h12 : w1 ≤ w2) : ‖F w2 - F w1‖ ≤ 3 * A * Real.log (w2 / w1) := by
  set L : ℝ := Real.log (w2 / w1) with hL
  have h2 : 0 < w2 := lt_of_lt_of_le h1 h12
  have hL0 : 0 ≤ L := Real.log_nonneg ((one_le_div h1).2 h12)
  have step : ∀ k : ℕ, 1 ≤ k → L ≤ k → ‖F w2 - F w1‖ ≤ 3 * A * (L + L ^ 2 / k) := by
    intro k hk hLk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    set t : ℕ → ℝ := fun i => w1 * Real.exp (L / k * i) with ht
    have ht0 : t 0 = w1 := by simp [ht]
    have htk : t k = w2 := by
      simp only [ht]
      rw [div_mul_cancel₀ _ hk0.ne', hL, Real.exp_log (div_pos h2 h1)]
      field_simp
    have htel : F w2 - F w1 = ∑ i ∈ range k, (F (t (i + 1)) - F (t i)) := by
      rw [Finset.sum_range_sub (fun i => F (t i)), ht0, htk]
    have hx0 : 0 ≤ L / k := by positivity
    have hx1 : L / k ≤ 1 := (div_le_one hk0).2 hLk
    have hexp : Real.exp (L / k) - 1 ≤ L / k + (L / k) ^ 2 := by
      have := Real.abs_exp_sub_one_sub_id_le (x := L / k) (by rw [abs_of_nonneg hx0]; exact hx1)
      have := (abs_le.1 this).2
      linarith
    have hterm : ∀ i ∈ range k, ‖F (t (i + 1)) - F (t i)‖ ≤ 3 * A * (L / k + (L / k) ^ 2) := by
      intro i _
      have hti : 0 < t i := by simp only [ht]; positivity
      have hti1 : t (i + 1) = t i * Real.exp (L / k) := by
        simp only [ht]
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        push_cast; ring
      have hge : t i ≤ t (i + 1) := by
        rw [hti1]
        have : 1 ≤ Real.exp (L / k) := Real.one_le_exp hx0
        nlinarith
      have hb := h (t (i + 1)) (t i) (lt_of_lt_of_le hti hge) hti
      rw [min_eq_right hge, abs_of_nonneg (by linarith)] at hb
      refine hb.trans ?_
      have e : 3 * A / t i * (t (i + 1) - t i) = 3 * A * (Real.exp (L / k) - 1) := by
        rw [hti1]; field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left hexp (by positivity)
    rw [htel]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [Finset.sum_const, card_range, nsmul_eq_mul]
    apply le_of_eq
    field_simp
  have hlim : Tendsto (fun k : ℕ => 3 * A * (L + L ^ 2 / (k : ℝ))) atTop (𝓝 (3 * A * (L + 0))) :=
    (tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (L ^ 2))).const_mul _
  rw [add_zero] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈L⌉₊] with k hk1 hk2
  exact step k hk1 ((Nat.le_ceil L).trans (by exact_mod_cast hk2))

def dom (t : ℝ) : ℝ := 1 / (t * Real.log t ^ 2)

lemma dom_integrableOn {a : ℝ} (ha : 1 < a) : IntegrableOn dom (Set.Ioi a) := by
  have hlim : Tendsto (fun t : ℝ => -(Real.log t)⁻¹) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).neg
    simpa using this
  refine integrableOn_Ioi_deriv_of_nonneg' (g := fun t : ℝ => -(Real.log t)⁻¹) (l := 0) ?_ ?_ hlim
  · intro x hx
    have hx1 : 1 < x := lt_of_lt_of_le ha hx
    have hx0 : x ≠ 0 := by positivity
    have hl : Real.log x ≠ 0 := (Real.log_pos hx1).ne'
    have h := ((Real.hasDerivAt_log hx0).inv hl).neg
    have e : dom x = -(-x⁻¹ / Real.log x ^ 2) := by
      unfold dom
      field_simp
    rw [e]
    exact h
  · intro x hx
    have hx1 : 1 < x := lt_trans ha hx
    unfold dom
    positivity

lemma exp_sqrt_le {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : 1 < x) :
    Real.exp (-c * Real.sqrt (Real.log x)) ≤ 24 / c ^ 4 / Real.log x ^ 2 := by
  have hL : 0 < Real.log x := Real.log_pos hx
  set y : ℝ := c * Real.sqrt (Real.log x) with hy
  have hy0 : 0 ≤ y := by positivity
  have h1 := Real.pow_div_factorial_le_exp y hy0 4
  have hy4 : y ^ 4 = c ^ 4 * Real.log x ^ 2 := by
    rw [hy, mul_pow]
    have : Real.sqrt (Real.log x) ^ 4 = (Real.sqrt (Real.log x) ^ 2) ^ 2 := by ring
    rw [this, Real.sq_sqrt hL.le]
  have hpos : 0 < c ^ 4 * Real.log x ^ 2 := by positivity
  have hfac : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hfac, hy4] at h1
  have h2 : Real.exp (-c * Real.sqrt (Real.log x)) = (Real.exp y)⁻¹ := by
    rw [← Real.exp_neg, hy]; ring_nf
  rw [h2]
  have h3 : (Real.exp y)⁻¹ ≤ (c ^ 4 * Real.log x ^ 2 / 24)⁻¹ :=
    inv_anti₀ (by positivity) h1
  refine h3.trans (le_of_eq ?_)
  field_simp

def rem (a : ℕ → ℂ) (m : ℂ) (t : ℝ) : ℂ := (∑ k ∈ Icc 1 ⌊t⌋₊, a k) - m * t

def RemBound (a : ℕ → ℂ) (m : ℂ) : Prop :=
  ∃ K x₁ : ℝ, 1 < x₁ ∧ ∀ t : ℝ, x₁ ≤ t → ‖rem a m t‖ ≤ K * t / Real.log t ^ 2

lemma norm_cpow_neg_add_one {t : ℝ} (ht : 0 < t) (σ : ℝ) :
    ‖(t : ℂ) ^ (-((σ : ℂ) + 1))‖ = t ^ (-(σ + 1)) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp

lemma cpow_contOn (s : ℂ) : ContinuousOn (fun t : ℝ => (t : ℂ) ^ s) (Set.Ici 1) := by
  refine ContinuousOn.cpow Complex.continuous_ofReal.continuousOn continuousOn_const ?_
  intro t ht
  exact Complex.ofReal_mem_slitPlane.2 (lt_of_lt_of_le zero_lt_one ht)

lemma core_bigO {a : ℕ → ℂ} {m : ℂ} (h : RemBound a m) :
    (fun t : ℝ => rem a m t * (t : ℂ) ^ (-(((1 : ℝ) : ℂ) + 1))) =O[atTop] dom := by
  obtain ⟨K, x₁, hx₁, hK⟩ := h
  refine Asymptotics.IsBigO.of_bound K ?_
  filter_upwards [eventually_ge_atTop x₁] with t ht
  have ht1 : 1 < t := lt_of_lt_of_le hx₁ ht
  have ht0 : 0 < t := by positivity
  have hL : 0 < Real.log t := Real.log_pos ht1
  rw [norm_mul, norm_cpow_neg_add_one ht0, Real.norm_of_nonneg (by unfold dom; positivity)]
  have e : t ^ (-((1 : ℝ) + 1)) = (t ^ 2)⁻¹ := by
    rw [Real.rpow_neg ht0.le]
    norm_num
  rw [e]
  calc ‖rem a m t‖ * (t ^ 2)⁻¹ ≤ (K * t / Real.log t ^ 2) * (t ^ 2)⁻¹ := by
        gcongr; exact hK t ht
    _ = K * dom t := by unfold dom; field_simp

lemma core_integrable {a : ℕ → ℂ} {m : ℂ} (h : RemBound a m) :
    IntegrableOn (fun t : ℝ => rem a m t * (t : ℂ) ^ (-(((1 : ℝ) : ℂ) + 1))) (Set.Ioi 1) := by
  have hO := core_bigO h
  obtain ⟨K, x₁, hx₁, hK⟩ := h
  have h1 : LocallyIntegrableOn (fun t : ℝ => (t : ℂ) ^ (-(((1 : ℝ) : ℂ) + 1))) (Set.Ici 1) :=
    (cpow_contOn _).locallyIntegrableOn measurableSet_Ici
  have h2 := locallyIntegrableOn_mul_sum_Icc a (m := 1) zero_le_one h1
  have h3 : LocallyIntegrableOn (fun t : ℝ => (t : ℂ) ^ (-(((1 : ℝ) : ℂ) + 1)) * (m * t)) (Set.Ici 1) :=
    ((cpow_contOn _).mul (by fun_prop)).locallyIntegrableOn measurableSet_Ici
  have h4 : LocallyIntegrableOn (fun t : ℝ => rem a m t * (t : ℂ) ^ (-(((1 : ℝ) : ℂ) + 1))) (Set.Ici 1) := by
    have e : (fun t : ℝ => rem a m t * (t : ℂ) ^ (-(((1 : ℝ) : ℂ) + 1))) =
        (fun t : ℝ => (t : ℂ) ^ (-(((1 : ℝ) : ℂ) + 1)) * ∑ k ∈ Icc 1 ⌊t⌋₊, a k) -
          fun t : ℝ => (t : ℂ) ^ (-(((1 : ℝ) : ℂ) + 1)) * (m * t) := by
      funext t
      simp only [rem, Pi.sub_apply]
      ring
    rw [e]
    exact h2.sub h3
  refine (h4.integrableOn_of_isBigO_atTop (g := dom) ?_ ?_).mono_set Set.Ioi_subset_Ici_self
  · exact hO
  · exact ⟨Set.Ioi x₁, Ioi_mem_atTop x₁, dom_integrableOn hx₁⟩

def aChi {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) : ℂ := (abelian₂ n : ℂ) * χ (n : ZMod N)

lemma norm_aChi_le {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) : ‖aChi χ n‖ ≤ Λ n := by
  unfold aChi
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (DirichletCharacter.norm_le_one χ _)

lemma psi_zero_nontrivial_character {N : ℕ} {χ : DirichletCharacter ℂ N} (h : χ ≠ 1) (t : ℝ) : psi0 χ t = rem (aChi χ) 0 t := by
  unfold psi0 rem aChi; rw [if_neg h]; simp

lemma psi_zero_trivial_character {N : ℕ} {χ : DirichletCharacter ℂ N} (h : χ = 1) (t : ℝ) : psi0 χ t = rem (aChi χ) 1 t := by
  unfold psi0 rem aChi; rw [if_pos h]; simp

lemma psi0_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ∃ K x₁ : ℝ, 1 < x₁ ∧ ∀ t : ℝ, x₁ ≤ t → ‖psi0 χ t‖ ≤ K * t / Real.log t ^ 2 := by
  obtain ⟨c, C, hc, h⟩ := Formalism.ZeroFreeDirichlet.siegelWalfisz 1 one_pos
  have hE : 0 < Real.exp (N : ℝ) := Real.exp_pos _
  refine ⟨|C| * (24 / c ^ 4), Real.exp N + 2, by linarith, fun t ht => ?_⟩
  have ht2 : 2 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hq : (N : ℝ) ≤ Real.log t ^ (1 : ℝ) := by
    rw [Real.rpow_one, Real.le_log_iff_exp_le ht0]
    linarith
  have h1 := h N χ t ht2 hq
  have e : psi0 χ t = Formalism.ZeroFreeDirichlet.psiChi χ t - (if χ = 1 then (t : ℂ) else 0) := by
    unfold psi0 Formalism.ZeroFreeDirichlet.psiChi
    by_cases hχ : χ = 1 <;> simp [hχ]
  rw [e]
  refine h1.trans ?_
  have h2 := exp_sqrt_le hc (x := t) (by linarith)
  calc C * t * Real.exp (-c * Real.sqrt (Real.log t))
      ≤ |C| * t * (24 / c ^ 4 / Real.log t ^ 2) := by
        gcongr
        exact le_abs_self C
    _ = |C| * (24 / c ^ 4) * t / Real.log t ^ 2 := by ring

lemma cpow_neg_two {t : ℝ} : (t : ℂ) ^ (-(((1 : ℝ) : ℂ) + 1)) = ((t : ℂ) ^ 2)⁻¹ := by
  rw [Complex.cpow_neg]
  congr 1
  have : ((1 : ℝ) : ℂ) + 1 = ((2 : ℕ) : ℂ) := by norm_num
  rw [this, Complex.cpow_natCast]

lemma psi_zero_div_sq_integrable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) (hy : 1 ≤ y) :
    IntegrableOn (fun u : ℝ => psi0 χ u / (u : ℂ) ^ 2) (Set.Ioi y) := by
  obtain ⟨K, x₁, hx₁, hK⟩ := psi0_bound χ
  by_cases hχ : χ = 1
  · have h := core_integrable (a := aChi χ) (m := 1) ⟨K, x₁, hx₁, fun t ht => by rw [← psi_zero_trivial_character hχ]; exact hK t ht⟩
    refine (h.mono_set (Set.Ioi_subset_Ioi hy)).congr_fun ?_ measurableSet_Ioi
    intro t _
    simp only [cpow_neg_two, psi_zero_trivial_character hχ, div_eq_mul_inv]
  · have h := core_integrable (a := aChi χ) (m := 0) ⟨K, x₁, hx₁, fun t ht => by rw [← psi_zero_nontrivial_character hχ]; exact hK t ht⟩
    refine (h.mono_set (Set.Ioi_subset_Ioi hy)).congr_fun ?_ measurableSet_Ioi
    intro t _
    simp only [cpow_neg_two, psi_zero_nontrivial_character hχ, div_eq_mul_inv]

lemma gChi_ne {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (h : χ ≠ 1) (y : ℝ) :
    gChi χ y = Fc (aChi χ) (logDerivativeAtOne χ) y := by
  unfold gChi sumLamChi Fc
  rw [if_neg h, truncC (aChi χ) y _ le_rfl]
  rfl

lemma Fc_eq_Gchi (c : ℕ → ℂ) (ell : ℂ) (y : ℝ) : Fc c ell y = Formalism.HermitianLattices.GL2PrimeSums.Gchi c (-ell) y := by
  unfold Fc Formalism.HermitianLattices.GL2PrimeSums.Gchi; ring

lemma gChi_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (h : χ = 1) (y : ℝ) :
    gChi χ y = ((GlobalTheoryTheory.G y : ℝ) : ℂ) := by
  unfold gChi; rw [if_pos h]

lemma G_eq_Gz (y : ℝ) : GlobalTheoryTheory.G y = Formalism.Gz y := by
  rw [G_eq_Gfun]; unfold Formalism.BasicNotions.Gfun Formalism.Gz Formalism.Sz; rfl

lemma G_eq_Gone (y : ℝ) : GlobalTheoryTheory.G y = Formalism.HermitianLattices.GL2PrimeSums.Gone (fun n => Λ n) y := by
  rw [G_eq_Gfun]; unfold Formalism.BasicNotions.Gfun Formalism.HermitianLattices.GL2PrimeSums.Gone; ring

lemma series_aChi {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (h : χ ≠ 1) :
    Tendsto (fun M : ℕ => ∑ n ∈ Icc 1 M, aChi χ n / (n : ℂ)) atTop (𝓝 (-(logDerivativeAtOne χ))) :=
  Formalism.HermitianLattices.GL2a2.log_deriv_series N χ h

lemma one_apply_of_primitive {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (h : χ = 1)
    (n : ℕ) : χ (n : ZMod N) = 1 := by
  subst h
  have hN : N = 1 := by
    have := hp
    unfold DirichletCharacter.IsPrimitive at this
    rw [DirichletCharacter.conductor_one] at this
    exact this.symm
  subst hN
  exact MulChar.one_apply (isUnit_of_subsingleton _)

end Formalism.MainNotions.ShortIntervalPrimes.Br

namespace Formalism.MainNotions.ShortIntervalPrimes

open Finset Filter Topology ArithmeticFunction MeasureTheory Formalism.MainNotions.GlobalTheoryTheory
open Formalism.HermitianLattices.GL2PrimeSums (psum psumR Gchi Gone)
open Br

theorem l21a {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive) (y : ℝ) (hy : 1 ≤ y) :
    IntegrableOn (fun u : ℝ => psi0 χ u / (u : ℂ) ^ 2) (Set.Ioi y) ∧
      gChi χ y = -(y : ℂ) * ∫ u in Set.Ioi y, psi0 χ u / (u : ℂ) ^ 2 := by
  have hint := psi_zero_div_sq_integrable χ y hy
  refine ⟨hint, ?_⟩
  have ht := intervalIntegral_tendsto_integral_Ioi y hint tendsto_id
  by_cases hχ : χ = 1
  · obtain ⟨I, hI, hG⟩ := Formalism.HermitianLattices.GL2PrimeSums.smoothedRemainderRealIntegralFormula (fun n => Λ n) Formalism.HermitianLattices.GL2a2.psi_zero_integral_constant y hy
    have hf : ∀ u : ℝ, psi0 χ u / (u : ℂ) ^ 2 = (((Formalism.HermitianLattices.GL2PrimeSums.psumR (fun n => Λ n) u - u) / u ^ 2 : ℝ) : ℂ) := by
      intro u
      unfold psi0 Formalism.HermitianLattices.GL2PrimeSums.psumR
      rw [if_pos hχ]
      simp only [one_apply_of_primitive hp hχ, mul_one]
      push_cast
      rfl
    have ht' : Tendsto (fun U : ℝ => (((∫ u in y..U, (Formalism.HermitianLattices.GL2PrimeSums.psumR (fun n => Λ n) u - u) / u ^ 2 : ℝ)) : ℂ)) atTop
        (𝓝 (∫ u in Set.Ioi y, psi0 χ u / (u : ℂ) ^ 2)) := by
      refine ht.congr ?_
      intro U
      simp only [id, hf]
      exact intervalIntegral.integral_ofReal
    have hI' : Tendsto (fun U : ℝ => (((∫ u in y..U, (Formalism.HermitianLattices.GL2PrimeSums.psumR (fun n => Λ n) u - u) / u ^ 2 : ℝ)) : ℂ)) atTop
        (𝓝 ((I : ℝ) : ℂ)) := (Complex.continuous_ofReal.tendsto I).comp hI
    rw [tendsto_nhds_unique ht' hI', gChi_one hχ, G_eq_Gone, hG]
    push_cast; ring
  · obtain ⟨I, hI, hG⟩ := Formalism.HermitianLattices.GL2PrimeSums.smoothedRemainderIntegralFormula (aChi χ) (-(logDerivativeAtOne χ)) (series_aChi hχ) y hy
    have hf : ∀ u : ℝ, psi0 χ u / (u : ℂ) ^ 2 = Formalism.HermitianLattices.GL2PrimeSums.psum (aChi χ) u / (u : ℂ) ^ 2 := by
      intro u
      rw [psi_zero_nontrivial_character hχ]; unfold rem Formalism.HermitianLattices.GL2PrimeSums.psum; simp
    have ht' : Tendsto (fun U : ℝ => ∫ u in y..U, Formalism.HermitianLattices.GL2PrimeSums.psum (aChi χ) u / (u : ℂ) ^ 2) atTop
        (𝓝 (∫ u in Set.Ioi y, psi0 χ u / (u : ℂ) ^ 2)) := by
      refine ht.congr ?_
      intro U
      simp only [id, hf]
    rw [tendsto_nhds_unique ht' hI, gChi_ne hχ, Fc_eq_Gchi, hG]

theorem l21b {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (x : ℝ) (hx : 1 ≤ x) :
    Tendsto (fun M : ℕ => ∑ n ∈ Finset.Icc 1 M, (cn x n : ℂ) * χ (n : ZMod N)) atTop
      (𝓝 (-(gChi χ x))) := by
  have h := Formalism.HermitianLattices.GL2PrimeSums.weighted_sum_tendsto (aChi χ) (-(logDerivativeAtOne χ)) (series_aChi hχ) x hx
  rw [gChi_ne hχ, Fc_eq_Gchi]
  refine h.congr ?_
  intro M
  apply Finset.sum_congr rfl
  intro n _
  unfold aChi cn
  push_cast; ring

theorem l21d {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (a : ℝ) (ha : 0 < a) (w1 w2 : ℝ) (h1 : 0 < w1)
    (h12 : w1 ≤ w2) :
    ‖(w2 : ℂ) * gChi χ (a / w2) - (w1 : ℂ) * gChi χ (a / w1)‖ ≤ 3 * a * Real.log (w2 / w1) := by
  by_cases hχ : χ = 1
  · have h := log_form (fun w : ℝ => w * Formalism.Gz (a / w)) a ha
      (fun w w' hw hw' => by
        rw [Real.norm_eq_abs]; exact Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN.lip_triv a w w' ha hw hw') w1 w2 h1 h12
    rw [gChi_one hχ, gChi_one hχ, G_eq_Gz, G_eq_Gz, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      ← Complex.ofReal_sub, Complex.norm_real]
    exact h
  · have h := log_form (fun w : ℝ => (w : ℂ) * Fc (aChi χ) (logDerivativeAtOne χ) (a / w)) a ha
      (fun w w' hw hw' => Fc_lipW (aChi χ) (norm_aChi_le χ) (logDerivativeAtOne χ) a w w' ha hw hw') w1 w2 h1 h12
    rw [gChi_ne hχ, gChi_ne hχ]
    exact h

theorem ramification_two_and_conjugation_at_q_and_d : ∃ C : ℝ, 0 < C ∧ ∀ D : Formalism.BasicNotions.D7, Conclusion1 D C := by
  obtain ⟨K, hK⟩ := Formalism.zetaPrimeSumErrorLipschitz
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hK0 := abs_nonneg K
  refine ⟨|K| + (Real.log 4 + 4) + 1, by positivity, ?_⟩
  intro D N _ χ hp
  have lipG : ∀ y1 y2 : ℝ, 1 / 2 ≤ y1 → 1 / 2 ≤ y2 → |GlobalTheoryTheory.G y2 - GlobalTheoryTheory.G y1| ≤ |K| * |y2 - y1| := by
    intro y1 y2 h1 h2
    rw [G_eq_Gz, G_eq_Gz]
    exact ((hK y2 y1 h2 h1).2).trans (mul_le_mul_of_nonneg_right (le_abs_self K) (abs_nonneg _))
  refine ⟨fun y hy => l21a χ hp y hy, fun hχ x hx => l21b χ hχ x hx, ?_, ?_, ?_, ?_,
    fun a ha w1 w2 h1 h12 => l21d χ a ha w1 w2 h1 h12⟩
  · intro hχ y hy
    have hy0 : 0 < y := by linarith
    have hly : 0 ≤ Real.log y := Real.log_nonneg hy
    have e : (fun t : ℝ => gChi χ t) = Fc (aChi χ) (logDerivativeAtOne χ) := funext (fun t => gChi_ne hχ t)
    rw [e]
    apply norm_deriv_le_of_lip' (by positivity)
    have hlt : y < y * Real.exp 1 := by
      have : 1 < Real.exp 1 := by
        have := Real.add_one_lt_exp (x := 1) one_ne_zero
        linarith
      nlinarith
    filter_upwards [Iio_mem_nhds hlt] with t ht
    have h := Fc_lip (aChi χ) (norm_aChi_le χ) (logDerivativeAtOne χ) y t hy
    rw [norm_sub_rev, Real.norm_eq_abs, abs_sub_comm t y, mul_comm]
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
    have hm : Real.log (max y t) ≤ Real.log y + 1 := by
      have h1 : max y t ≤ y * Real.exp 1 := max_le hlt.le (le_of_lt ht)
      have h2 := Real.log_le_log (lt_of_lt_of_le hy0 (le_max_left y t)) h1
      rwa [Real.log_mul hy0.ne' (Real.exp_pos 1).ne', Real.log_exp] at h2
    linarith
  · intro y hy
    rw [← Real.norm_eq_abs]
    have : ‖deriv GlobalTheoryTheory.G y‖ ≤ |K| := by
      apply norm_deriv_le_of_lip' hK0
      filter_upwards [Ioi_mem_nhds (show (1 / 2 : ℝ) < y by linarith)] with t ht
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      exact lipG y t (by linarith) (le_of_lt ht)
    linarith
  · intro hχ y1 y2 h1 h2
    have h := Fc_lip (aChi χ) (norm_aChi_le χ) (logDerivativeAtOne χ) y2 y1 h2
    rw [gChi_ne hχ, gChi_ne hχ, mul_comm, max_comm]
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
    linarith
  · intro y1 y2 h1 h2
    refine (lipG y1 y2 (by linarith) (by linarith)).trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
    linarith

theorem proposition_eleven_one_family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Conclusion1Family Fm := by
  obtain ⟨C, hC, h⟩ := ramification_two_and_conjugation_at_q_and_d
  exact ⟨C, hC, fun x _ i => h _⟩

end Formalism.MainNotions.ShortIntervalPrimes

end

noncomputable section

namespace Formalism.MainNotions.ShortIntervalPrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Filter Topology

def projection_sandwich_lattice (C : ℝ) : Prop :=
  ∀ Q : ℝ, 1 ≤ Q →
    (∑ N ∈ Finset.range ⌊Q⌋₊, ({χ : DirichletCharacter ℂ (N + 1) |
      χ.IsPrimitive ∧ IsRealChar χ ∧ ¬ GoodFor Q χ}.ncard : ℝ)) ≤ C * Q ^ ((1 : ℝ) / 4)

def MassRatio₂ (x eps C : ℝ) : Prop :=
  ∀ Q : ℝ, 0 < Q → x ^ (eps / 6) ≤ Real.log Q → Real.log Q ≤ x ^ (eps / 4) →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → GoodFor Q χ →
      (∃ S : ℂ, TailSum χ (zz x) S ∧ ‖(x : ℂ) * S‖ ≤ x ^ eps) ∧
      ‖logDerivativeAtOne χ‖ ≤ C * Real.log x

theorem lemma_two_two_iff_both_claims (D : D7) (x eps C : ℝ) : Conclusion2 D x eps C ↔ projection_sandwich_lattice C ∧ MassRatio₂ x eps C := Iff.rfl

theorem one_le_order {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 1 ∨ χ ≠ 1)
    (hz : DirichletCharacter.LFunction χ s = 0) :
    1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) s := by
  have key : ∀ U : Set ℂ, IsOpen U → IsPreconnected U → s ∈ U → (2 : ℂ) ∈ U →
      (∀ z ∈ U, z ≠ 1 ∨ χ ≠ 1) → 1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) s := by
    intro U hU hc hsU h2U hd
    have han : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) U := by
      apply DifferentiableOn.analyticOnNhd _ hU
      intro z hzU
      exact (DirichletCharacter.differentiableAt_LFunction χ z (hd z hzU)).differentiableWithinAt
    have h2 : DirichletCharacter.LFunction χ 2 ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num)) (by norm_num)
    have o2 : analyticOrderAt (DirichletCharacter.LFunction χ) 2 ≠ ⊤ := by
      rw [(han 2 h2U).analyticOrderAt_eq_zero.2 h2]; simp
    have os : analyticOrderAt (DirichletCharacter.LFunction χ) s ≠ ⊤ :=
      han.analyticOrderAt_ne_top_of_isPreconnected hc h2U hsU o2
    have o0 : analyticOrderAt (DirichletCharacter.LFunction χ) s ≠ 0 :=
      (han s hsU).analyticOrderAt_ne_zero.2 hz
    by_contra hlt
    have h0 : analyticOrderNatAt (DirichletCharacter.LFunction χ) s = 0 := by omega
    have := Nat.cast_analyticOrderNatAt os
    rw [h0] at this
    exact o0 this.symm
  by_cases hχ : χ = 1
  · have hs1 : s ≠ 1 := by
      rcases hs with h | h
      · exact h
      · exact absurd hχ h
    refine key {1}ᶜ isOpen_compl_singleton
      (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) 1).isPreconnected
      hs1 (by norm_num) (fun z hz => Or.inl hz)
  · exact key Set.univ isOpen_univ isPreconnected_univ trivial trivial (fun z _ => Or.inr hχ)

theorem zero_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive) {s : ℂ}
    (hz : DirichletCharacter.LFunction χ s = 0) : s ≠ 1 ∨ χ ≠ 1 := by
  by_cases hχ : χ = 1
  · left
    rintro rfl
    have hN : N = 1 := by
      have h := hp
      rw [DirichletCharacter.isPrimitive_def, hχ,
        DirichletCharacter.conductor_one] at h
      exact h.symm
    subst hN
    rw [DirichletCharacter.LFunction_modOne_eq] at hz
    exact riemannZeta_one_ne_zero hz
  · exact Or.inr hχ

open Classical in

def badZero (Q : ℝ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℂ :=
  if h : ∃ s : ℂ, 1 - 1 / 400 < s.re ∧ |s.im| ≤ Q ∧ DirichletCharacter.LFunction χ s = 0
  then h.choose else 0

theorem badZero_spec (Q : ℝ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (h : ∃ s : ℂ, 1 - 1 / 400 < s.re ∧ |s.im| ≤ Q ∧ DirichletCharacter.LFunction χ s = 0) :
    1 - 1 / 400 < (badZero Q χ).re ∧ |(badZero Q χ).im| ≤ Q ∧
      DirichletCharacter.LFunction χ (badZero Q χ) = 0 := by
  unfold badZero
  rw [dif_pos h]
  exact h.choose_spec

theorem num_bound {Q : ℝ} (hQ : 1 ≤ Q) : (max Q 3) ^ ((1 : ℝ) / 4) ≤ 3 * Q ^ ((1 : ℝ) / 4) := by
  have hQ0 : 0 ≤ Q := by linarith
  have h1 : max Q 3 ≤ 3 * Q := max_le (by linarith) (by linarith)
  calc (max Q 3) ^ ((1 : ℝ) / 4) ≤ (3 * Q) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow (le_trans hQ0 (le_max_left _ _)) h1 (by norm_num)
    _ = 3 ^ ((1 : ℝ) / 4) * Q ^ ((1 : ℝ) / 4) := Real.mul_rpow (by norm_num) hQ0
    _ ≤ 3 * Q ^ ((1 : ℝ) / 4) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hQ0 _)
        calc (3 : ℝ) ^ ((1 : ℝ) / 4) ≤ 3 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 3 := Real.rpow_one _

theorem first_claim_lemma_two_two_of_count (D : D7) (C1 c : ℝ) (hC1 : 0 ≤ C1) (h : adm6 D C1 c) {C : ℝ} (hC : 3 * C1 ≤ C) : projection_sandwich_lattice C := by
  classical
  intro Q hQ
  obtain ⟨h1, -⟩ := h
  have hfin : ∀ N : ℕ, ({χ : DirichletCharacter ℂ (N + 1) |
      χ.IsPrimitive ∧ IsRealChar χ ∧ ¬ GoodFor Q χ}).Finite := fun N => Set.toFinite _
  have hex : ∀ N ∈ Finset.range ⌊Q⌋₊, ∀ χ : DirichletCharacter ℂ (N + 1),
      χ.IsPrimitive ∧ IsRealChar χ ∧ ¬ GoodFor Q χ →
      ((N + 1 : ℕ) : ℝ) ≤ Q ∧
      ∃ s : ℂ, 1 - 1 / 400 < s.re ∧ |s.im| ≤ Q ∧ DirichletCharacter.LFunction χ s = 0 := by
    intro N hN χ hχ
    obtain ⟨hp, hr, hg⟩ := hχ
    have hNQ : ((N + 1 : ℕ) : ℝ) ≤ Q := by
      have h2 : N + 1 ≤ ⌊Q⌋₊ := Finset.mem_range.mp hN
      exact (Nat.cast_le.mpr h2).trans (Nat.floor_le (by linarith))
    refine ⟨hNQ, ?_⟩
    by_contra hno
    push Not at hno
    exact hg ⟨hp, hr, hNQ, fun s h1 h2 => hno s h1 h2⟩
  let T : Finset ZPt := (Finset.range ⌊Q⌋₊).sigma (fun N => (hfin N).toFinset.map
    ⟨fun χ => (χ, badZero Q χ), fun a b hab => (Prod.ext_iff.mp hab).1⟩)
  have hcard : (T.card : ℝ) = ∑ N ∈ Finset.range ⌊Q⌋₊, ({χ : DirichletCharacter ℂ (N + 1) |
      χ.IsPrimitive ∧ IsRealChar χ ∧ ¬ GoodFor Q χ}.ncard : ℝ) := by
    simp only [T, Finset.card_sigma, Finset.card_map]
    push_cast
    apply Finset.sum_congr rfl
    intro N _
    rw [Set.ncard_eq_toFinset_card _ (hfin N)]
  have hT : ∀ p ∈ T, ((p.1 + 1 : ℕ) : ℝ) ≤ max Q 3 ∧ p.2.1.IsPrimitive ∧
      DirichletCharacter.LFunction p.2.1 p.2.2 = 0 ∧ (1 - 1 / 400 : ℝ) ≤ p.2.2.re ∧
      |p.2.2.im| ≤ max Q 3 := by
    rintro ⟨N, χ, s⟩ hp
    simp only [T, Finset.mem_sigma, Finset.mem_map, Set.Finite.mem_toFinset] at hp
    obtain ⟨hN, χ', hχ', heq⟩ := hp
    have e1 : χ' = χ := congrArg Prod.fst heq
    have e2 : badZero Q χ' = s := congrArg Prod.snd heq
    subst e1
    subst e2
    obtain ⟨hNQ, hs⟩ := hex N hN χ' hχ'
    obtain ⟨s1, s2, s3⟩ := badZero_spec Q χ' hs
    exact ⟨hNQ.trans (le_max_left _ _), hχ'.1, s3, s1.le, s2.trans (le_max_left _ _)⟩
  have hsum := h1 (max Q 3) (le_max_right _ _) T hT
  have hle : T.card ≤ ∑ p ∈ T, analyticOrderNatAt (DirichletCharacter.LFunction p.2.1) p.2.2 := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨-, hp2, hp3, -, -⟩ := hT p hp
    exact one_le_order p.2.1 (zero_ne_one p.2.1 hp2 hp3) hp3
  rw [← hcard]
  calc (T.card : ℝ)
      ≤ ((∑ p ∈ T, analyticOrderNatAt (DirichletCharacter.LFunction p.2.1) p.2.2 : ℕ) : ℝ) := by
        exact_mod_cast hle
    _ ≤ C1 * (max Q 3) ^ ((1 : ℝ) / 4) := hsum
    _ ≤ C1 * (3 * Q ^ ((1 : ℝ) / 4)) := mul_le_mul_of_nonneg_left (num_bound hQ) hC1
    _ = 3 * C1 * Q ^ ((1 : ℝ) / 4) := by ring
    _ ≤ C * Q ^ ((1 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (by linarith) _)

def PsiBounds (C1 c1 : ℝ) : Prop :=
  ∀ Q : ℝ, 0 < Q → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → GoodFor Q χ →
    (∀ u : ℝ, 2 ≤ u → ‖psi0 χ u‖ ≤
      C1 * (u ^ (1 - (1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + u / Q * Real.log (u * Q) ^ 2)) ∧
    (∀ u : ℝ, Real.exp (Real.log Q ^ 2) ≤ u →
      ‖psi0 χ u‖ ≤ C1 * u * Real.exp (-c1 * Real.sqrt (Real.log u)))

theorem Icc_one_eq (M : ℕ) : Finset.Icc 1 M = Finset.Ioc 0 M := by
  ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega

theorem mertens_chi {N : ℕ} (χ : DirichletCharacter ℂ N) (y : ℝ) (hy : 1 ≤ y) :
    ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ‖(abelian₂ n : ℂ) * χ (n : ZMod N)‖ / (n : ℝ) ≤
      Real.log y + (Real.log 4 + 4) := by
  have hM1 : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by simpa using hy)
  have h3 := Formalism.LogFactorialMertensBounds.mertens_upper _ hM1
  have h4 : Real.log (⌊y⌋₊ : ℝ) ≤ Real.log y :=
    Real.log_le_log (by exact_mod_cast hM1) (Nat.floor_le (by linarith))
  have h5 : ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ‖(abelian₂ n : ℂ) * χ (n : ZMod N)‖ / (n : ℝ) ≤
      Formalism.LogFactorialMertensBounds.A ⌊y⌋₊ := by
    unfold Formalism.LogFactorialMertensBounds.A
    rw [Icc_one_eq]
    apply Finset.sum_le_sum
    intro n _
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    calc abelian₂ n * ‖χ (n : ZMod N)‖ ≤ abelian₂ n * 1 :=
          mul_le_mul_of_nonneg_left (DirichletCharacter.norm_le_one χ _)
            ArithmeticFunction.vonMangoldt_nonneg
      _ = abelian₂ n := mul_one _
  linarith

theorem second_claim_lemma_two_two_of_psi_bounds {eps : ℝ} (h0 : 0 < eps) (h1 : eps < 1) {C1 c1 : ℝ} (hC1 : 0 < C1)
    (hc1 : 0 < c1) (H : PsiBounds C1 c1) :
    ∃ C x0 : ℝ, 0 < C ∧ 1 < x0 ∧ ∀ x ≥ x0, ∀ C' ≥ C, MassRatio₂ x eps C' := by
  obtain ⟨x₀, C, hT⟩ := Formalism.HermitianLattices.GL2PrimeSums.tail_bound_joint eps h0 h1 C1 c1 (Real.log 4 + 4) hC1 hc1
    (by have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith)
  refine ⟨max C 1, max x₀ 2, lt_of_lt_of_le one_pos (le_max_right _ _),
    lt_of_lt_of_le one_lt_two (le_max_right _ _), ?_⟩
  intro x hx C' hC' Q hQ hq1 hq2 N _ χ hχ hg
  have hx0 : x₀ ≤ x := (le_max_left _ _).trans hx
  have hx2 : 2 ≤ x := (le_max_right _ _).trans hx
  obtain ⟨H1, H2⟩ := H Q hQ N χ hχ hg
  have hps : ∀ u : ℝ,
      Formalism.HermitianLattices.GL2PrimeSums.psum (fun n : ℕ => (abelian₂ n : ℂ) * χ (n : ZMod N)) u = psi0 χ u := by
    intro u
    unfold Formalism.HermitianLattices.GL2PrimeSums.psum psi0
    rw [if_neg hχ, sub_zero]
  have hser : Tendsto (fun M : ℕ => ∑ n ∈ Finset.Icc 1 M, (abelian₂ n : ℂ) * χ (n : ZMod N) / (n : ℂ))
      atTop (𝓝 (-(logDerivativeAtOne χ))) := Formalism.HermitianLattices.GL2a2.log_deriv_series N χ hχ
  obtain ⟨t1, t2⟩ := hT x hx0 Q hQ hq1 hq2 (fun n : ℕ => (abelian₂ n : ℂ) * χ (n : ZMod N))
    (-(logDerivativeAtOne χ)) hser (fun y hy => mertens_chi χ y hy) (fun u hu => by rw [hps]; exact H1 u hu)
    (fun u hu => by rw [hps]; exact H2 u hu)
  have hz : x ^ (400 : ℝ) = zz x := by
    unfold zz
    exact_mod_cast Real.rpow_natCast x 400
  rw [hz] at t1
  constructor
  · refine ⟨-(logDerivativeAtOne χ) - ∑ n ∈ Finset.Icc 1 ⌊zz x⌋₊, (abelian₂ n : ℂ) * χ (n : ZMod N) / (n : ℂ),
      ?_, t1⟩
    unfold TailSum
    have hlim := hser.sub_const
      (∑ n ∈ Finset.Icc 1 ⌊zz x⌋₊, (abelian₂ n : ℂ) * χ (n : ZMod N) / (n : ℂ))
    refine Tendsto.congr' ?_ hlim
    filter_upwards [eventually_ge_atTop ⌊zz x⌋₊] with M hM
    rw [Icc_one_eq, Icc_one_eq, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hM]
    ring
  · rw [norm_neg] at t2
    refine t2.trans ?_
    exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans hC') (Real.log_nonneg (by linarith))

theorem lemma_two_two_of_count_and_psi_bounds {eps : ℝ} (h0 : 0 < eps) (h1 : eps < 1) {C1 c1 : ℝ} (hC1 : 0 < C1)
    (hc1 : 0 < c1) (H : PsiBounds C1 c1) {Cq : ℝ} (hCq : 0 ≤ Cq) :
    ∃ C x0 : ℝ, 0 < C ∧ 1 < x0 ∧ ∀ x ≥ x0, ∀ (D : D7) (c : ℝ), adm6 D Cq c → Conclusion2 D x eps C := by
  obtain ⟨C, x0, hC, hx0, h⟩ := second_claim_lemma_two_two_of_psi_bounds h0 h1 hC1 hc1 H
  refine ⟨max C (3 * Cq), x0, lt_of_lt_of_le hC (le_max_left _ _), hx0, ?_⟩
  intro x hx D c h6
  exact ⟨first_claim_lemma_two_two_of_count D Cq c hCq h6 (le_max_right _ _), h x hx _ (le_max_left _ _)⟩

theorem lemma_two_two_family_of_psi_bounds {eps : ℝ} (Fm : FamP eps) (h0 : 0 < eps) (h1 : eps < 1)
    {C1 c1 : ℝ} (hC1 : 0 < C1) (hc1 : 0 < c1) (H : PsiBounds C1 c1) (h6 : FamilySixthHypothesis Fm) : Conclusion2Family Fm := by
  obtain ⟨Cq, c, hCq, -, hc⟩ := h6
  obtain ⟨C, x0, hC, hx0, h⟩ := lemma_two_two_of_count_and_psi_bounds h0 h1 hC1 hc1 H hCq.le
  exact ⟨C, hC, x0, hx0, fun x hx i => h x hx _ c (hc x (lt_of_lt_of_le hx0 hx) i)⟩

def ZeroSum (C2 : ℝ) : Prop :=
  ∀ Q : ℝ, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → GoodFor Q χ →
    ∀ T : ℝ, 1 ≤ T → ∑ᶠ ρ ∈ ZerosBelow χ T, (zOrd χ ρ : ℝ) / ‖ρ‖ ≤ C2 * Real.log (Q * T) ^ 2

def FirstPsiBound (C1 : ℝ) : Prop :=
  ∀ Q : ℝ, 0 < Q → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → GoodFor Q χ →
    ∀ u : ℝ, 2 ≤ u → ‖psi0 χ u‖ ≤
      C1 * (u ^ (1 - (1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + u / Q * Real.log (u * Q) ^ 2)

def SecondPsiBound (C1 c1 : ℝ) : Prop :=
  ∀ Q : ℝ, 0 < Q → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → GoodFor Q χ →
    ∀ u : ℝ, Real.exp (Real.log Q ^ 2) ≤ u →
      ‖psi0 χ u‖ ≤ C1 * u * Real.exp (-c1 * Real.sqrt (Real.log u))

theorem psiBounds_of {A B c1 : ℝ} (h1 : FirstPsiBound A) (h2 : SecondPsiBound B c1) : PsiBounds (max A B) c1 := by
  intro Q hQ N _ χ hχ hg
  constructor
  · intro u hu
    refine (h1 Q hQ N χ hχ hg u hu).trans ?_
    have hu0 : 0 < u := by linarith
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · intro u hu
    refine (h2 Q hQ N χ hχ hg u hu).trans ?_
    have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos _) hu
    have : B * u ≤ max A B * u := mul_le_mul_of_nonneg_right (le_max_right _ _) hu0.le
    exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le

theorem first_psi_bound_of_zero_sum {C C2 : ℝ} (hC : 0 < C) (hC2 : 0 ≤ C2) (D : D7) (h7 : adm7 D C) (hZ : ZeroSum C2) :
    FirstPsiBound (C * (5 + C2) + C2) := by
  intro Q hQ N _ χ hχ hg u hu
  have hu0 : 0 < u := by linarith
  have hu1 : 1 ≤ u := by linarith
  have hN1 : N ≠ 1 := by
    intro h
    subst h
    exact hχ (DirichletCharacter.level_one χ)
  have hN2 : 2 ≤ N := by
    have := NeZero.ne N
    omega
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNQ : (N : ℝ) ≤ Q := hg.2.2.1
  have hQ2 : 2 ≤ Q := hN2'.trans hNQ
  set P : ℝ := u ^ (1 - (1 : ℝ) / 400) with hP
  set L : ℝ := Real.log (u * Q) with hL
  have hP1 : 1 ≤ P := Real.one_le_rpow hu1 (by norm_num)
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    nlinarith
  obtain ⟨T, hT2, hTu, hTQ, hTdiv⟩ : ∃ T : ℝ, 2 ≤ T ∧ T ≤ u ∧ T ≤ Q ∧ u / T ≤ P + u / Q := by
    rcases le_total u Q with h | h
    · refine ⟨u, hu, le_rfl, h, ?_⟩
      rw [div_self hu0.ne']
      have : 0 ≤ u / Q := by positivity
      linarith
    · refine ⟨Q, hQ2, h, le_rfl, ?_⟩
      linarith
  have hT0 : 0 < T := by linarith
  obtain ⟨hfin, hexp⟩ := h7 N χ hg.1 u T hT2 hTu

  have hN0 : (0 : ℝ) < N := by linarith
  have l1 : 0 ≤ Real.log (N * u * T) := by
    apply Real.log_nonneg
    have : 1 ≤ (N : ℝ) * u := by nlinarith
    nlinarith
  have l2 : Real.log (N * u * T) ≤ 2 * L := by
    have s1 : (N : ℝ) * u * T ≤ Q * u * u := by gcongr
    have s2 : Q * u * u ≤ (u * Q) ^ 2 := by
      calc Q * u * u = Q * u * u * 1 := by ring
        _ ≤ Q * u * u * Q := by gcongr; linarith
        _ = (u * Q) ^ 2 := by ring
    have := Real.log_le_log (by positivity) (s1.trans s2)
    rw [Real.log_pow] at this
    simpa [hL] using this
  have l3 : Real.log (N * u) ≤ L := by
    apply Real.log_le_log (by positivity)
    rw [mul_comm]
    gcongr
  have l4 : 0 ≤ Real.log (Q * 1) := Real.log_nonneg (by linarith)
  have l5 : Real.log (Q * 1) ≤ L := by
    apply Real.log_le_log (by positivity)
    nlinarith
  have l6 : 0 ≤ Real.log (Q * T) := Real.log_nonneg (by nlinarith)
  have l7 : Real.log (Q * T) ≤ L := by
    apply Real.log_le_log (by positivity)
    rw [mul_comm u Q]
    gcongr
  have q1 : Real.log (N * u * T) ^ 2 ≤ 4 * L ^ 2 := by
    have := pow_le_pow_left₀ l1 l2 2
    nlinarith
  have q2 : Real.log (Q * 1) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ l4 l5 2
  have q3 : Real.log (Q * T) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ l6 l7 2
  have hL2 : 0 ≤ L ^ 2 := by positivity
  have hLL : L ≤ L ^ 2 := by nlinarith
  have hLP : L ^ 2 ≤ L ^ 2 * P := by nlinarith
  have hUQ : 0 ≤ u / Q := by positivity

  have e1 : u * Real.log (N * u * T) ^ 2 / T ≤ 4 * L ^ 2 * (P + u / Q) := by
    calc u * Real.log (N * u * T) ^ 2 / T = u / T * Real.log (N * u * T) ^ 2 := by ring
      _ ≤ (P + u / Q) * (4 * L ^ 2) :=
          mul_le_mul hTdiv q1 (by positivity) (by linarith)
      _ = 4 * L ^ 2 * (P + u / Q) := by ring
  have e2 : Real.log (N * u) ≤ L ^ 2 * P := l3.trans (hLL.trans hLP)
  have e3 : ∑ᶠ ρ ∈ ZerosBelow χ 1, (zOrd χ ρ : ℝ) / ‖ρ‖ ≤ C2 * L ^ 2 * P := by
    refine (hZ Q N χ hχ hg 1 le_rfl).trans ?_
    calc C2 * Real.log (Q * 1) ^ 2 ≤ C2 * (L ^ 2 * P) :=
          mul_le_mul_of_nonneg_left (q2.trans hLP) hC2
      _ = C2 * L ^ 2 * P := by ring

  have hterm : ∀ ρ ∈ hfin.toFinset,
      ‖(zOrd χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ P * ((zOrd χ ρ : ℝ) / ‖ρ‖) := by
    intro ρ hρ
    obtain ⟨r0, r1, r2, r3⟩ : ρ ∈ ZerosBelow χ T := hfin.mem_toFinset.mp hρ
    have hre : ρ.re ≤ 1 - 1 / 400 := by
      by_contra hh
      push Not at hh
      exact hg.2.2.2 ρ hh (r2.le.trans hTQ) r3
    rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    have hle : u ^ ρ.re ≤ P := Real.rpow_le_rpow_of_exponent_le hu1 hre
    calc (zOrd χ ρ : ℝ) * (u ^ ρ.re / ‖ρ‖) ≤ (zOrd χ ρ : ℝ) * (P / ‖ρ‖) := by gcongr
      _ = P * ((zOrd χ ρ : ℝ) / ‖ρ‖) := by ring
  have e4 : ‖∑ᶠ ρ ∈ ZerosBelow χ T, (zOrd χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ P * (C2 * L ^ 2) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [← Finset.mul_sum, ← finsum_mem_eq_finite_toFinset_sum _ hfin]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    exact (hZ Q N χ hχ hg T (by linarith)).trans (mul_le_mul_of_nonneg_left q3 hC2)
  have key : C * (4 * L ^ 2 * (P + u / Q) + L ^ 2 * P + C2 * L ^ 2 * P) + P * (C2 * L ^ 2) =
      (C * (5 + C2) + C2) * (P * L ^ 2 + u / Q * L ^ 2) -
        (C * (1 + C2) + C2) * (u / Q * L ^ 2) := by ring
  have hnn : 0 ≤ (C * (1 + C2) + C2) * (u / Q * L ^ 2) := by positivity
  calc ‖psi0 χ u‖
      = ‖(psi0 χ u + ∑ᶠ ρ ∈ ZerosBelow χ T, (zOrd χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)) -
          ∑ᶠ ρ ∈ ZerosBelow χ T, (zOrd χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ := by
        rw [add_sub_cancel_right]
    _ ≤ ‖psi0 χ u + ∑ᶠ ρ ∈ ZerosBelow χ T, (zOrd χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ +
          ‖∑ᶠ ρ ∈ ZerosBelow χ T, (zOrd χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ := norm_sub_le _ _
    _ ≤ C * (4 * L ^ 2 * (P + u / Q) + L ^ 2 * P + C2 * L ^ 2 * P) + P * (C2 * L ^ 2) := by
        refine add_le_add (hexp.trans ?_) e4
        exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add e1 e2) e3) hC.le
    _ ≤ (C * (5 + C2) + C2) * (P * L ^ 2 + u / Q * L ^ 2) := by rw [key]; linarith

theorem inv_eq_self_of_real {N : ℕ} (χ : DirichletCharacter ℂ N) (hr : IsRealChar χ) : χ⁻¹ = χ := by
  apply MulChar.ext
  intro a
  rw [MulChar.inv_apply_eq_inv']
  have h1 : ‖χ a‖ = 1 := DirichletCharacter.unit_norm_eq_one χ a
  have h2 : (χ a).im = 0 := hr a
  have h4 : (χ a).re * (χ a).re = 1 := by
    have h := Complex.normSq_apply (χ a)
    rw [Complex.normSq_eq_norm_sq, h1, h2] at h
    linarith
  have h3 : χ a * χ a = 1 := by
    apply Complex.ext
    · simp only [Complex.mul_re, h2, Complex.one_re]; linarith
    · simp only [Complex.mul_im, h2, Complex.one_im]; ring
  exact inv_eq_of_mul_eq_one_left h3

theorem re_ge_of_good {Q : ℝ} {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hg : GoodFor Q χ) {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (him : |ρ.im| ≤ Q)
    (hz : DirichletCharacter.LFunction χ ρ = 0) : 1 / 400 ≤ ρ.re := by
  by_contra hh
  push Not at hh
  have hz' := zero_symm hg.1 h0 h1 hz
  rw [inv_eq_self_of_real χ hg.2.1] at hz'
  refine hg.2.2.2 (1 - ρ) ?_ ?_ hz'
  · rw [Complex.sub_re, Complex.one_re]; linarith
  · rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]; exact him

theorem zeroSum_of {C7 C : ℝ} (hC : 0 < C) (D : D7) (h7 : adm7 D C7) (h11 : adm11 D C) :
    ZeroSum (28800 * C) := by
  classical
  intro Q N _ χ hχ hg T hT
  have hN1 : N ≠ 1 := by
    intro h
    subst h
    exact hχ (DirichletCharacter.level_one χ)
  have hN2 : 2 ≤ N := by
    have := NeZero.ne N
    omega
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNQ : (N : ℝ) ≤ Q := hg.2.2.1
  have hQ2 : 2 ≤ Q := hN2'.trans hNQ
  have hfin : (ZerosBelow χ T).Finite := by
    refine (h7 N χ hg.1 (max T 2) (max T 2) (le_max_right _ _) le_rfl).1.subset ?_
    rintro ρ ⟨r0, r1, r2, r3⟩
    exact ⟨r0, r1, lt_of_lt_of_le r2 (le_max_left _ _), r3⟩
  set M : ℕ := ⌊T⌋₊ with hM
  have hMT : (M : ℝ) ≤ T := Nat.floor_le (by linarith)
  set Lq : ℝ := Real.log (Q * T) with hLq
  set La : ℝ := Real.log (Q * ((M : ℝ) + 2)) with hLa
  have hQT2 : 2 ≤ Q * T := by nlinarith
  have hLq1 : 1 ≤ 2 * Lq := by
    have h1 : Real.log 2 ≤ Lq := Real.log_le_log (by norm_num) hQT2
    have := Real.log_two_gt_d9
    linarith
  have hLa0 : 0 ≤ La := Real.log_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) M])
  have hLa3 : La ≤ 3 * Lq := by
    have c1 : Q * ((M : ℝ) + 2) ≤ Q * (3 * T) := by gcongr; linarith
    have c2 : (3 : ℝ) ≤ (Q * T) ^ 2 := by nlinarith
    have c3 : Q * (3 * T) ≤ (Q * T) ^ 3 := by
      calc Q * (3 * T) = (Q * T) * 3 := by ring
        _ ≤ (Q * T) * (Q * T) ^ 2 := by gcongr
        _ = (Q * T) ^ 3 := by ring
    have := Real.log_le_log (by positivity) (c1.trans c3)
    rw [Real.log_pow] at this
    simpa [hLa, hLq] using this
  have hLM : Real.log ((M + 1 : ℕ) : ℝ) ≤ Lq := by
    apply Real.log_le_log (by positivity)
    push_cast
    nlinarith

  have hwin : ∀ i : ℕ, i ≤ M → ∀ t : ℝ, |t| = i →
      ∑ ρ ∈ (h11 N χ hg.1 t).1.toFinset, (zOrd χ ρ : ℝ) ≤ C * La := by
    intro i hi t ht
    have h := (h11 N χ hg.1 t).2
    rw [finsum_mem_eq_finite_toFinset_sum _ (h11 N χ hg.1 t).1] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hC.le)
    rw [ht]
    apply Real.log_le_log (by positivity)
    have : (i : ℝ) ≤ M := by exact_mod_cast hi
    gcongr
  have hfib : ∀ i ∈ Finset.range (M + 1),
      ∑ ρ ∈ hfin.toFinset with ⌊|ρ.im|⌋₊ = i, (zOrd χ ρ : ℝ) / ‖ρ‖ ≤
        1600 / ((i : ℝ) + 1) * (2 * (C * La)) := by
    intro i hi
    have hiM : i ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hi0 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have st1 : ∑ ρ ∈ hfin.toFinset with ⌊|ρ.im|⌋₊ = i, (zOrd χ ρ : ℝ) / ‖ρ‖ ≤
        ∑ ρ ∈ hfin.toFinset with ⌊|ρ.im|⌋₊ = i, 1600 / ((i : ℝ) + 1) * (zOrd χ ρ : ℝ) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      obtain ⟨hρF, hρi⟩ := Finset.mem_filter.mp hρ
      obtain ⟨r0, r1, r2, r3⟩ : ρ ∈ ZerosBelow χ T := hfin.mem_toFinset.mp hρF
      have hile : (i : ℝ) ≤ |ρ.im| := by rw [← hρi]; exact Nat.floor_le (abs_nonneg _)
      have hnorm : ((i : ℝ) + 1) / 1600 ≤ ‖ρ‖ := by
        rcases le_total |ρ.im| 2 with h2 | h2
        · have := re_ge_of_good hg r0 r1 (h2.trans hQ2) r3
          have h3 := (le_abs_self ρ.re).trans (Complex.abs_re_le_norm ρ)
          linarith
        · have h3 := Complex.abs_im_le_norm ρ
          linarith
      have hpos : 0 < ‖ρ‖ := lt_of_lt_of_le (by positivity) hnorm
      rw [div_le_iff₀ hpos]
      have h1 : 1 ≤ 1600 / ((i : ℝ) + 1) * ‖ρ‖ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hi0]
        linarith
      calc (zOrd χ ρ : ℝ) = (zOrd χ ρ : ℝ) * 1 := (mul_one _).symm
        _ ≤ (zOrd χ ρ : ℝ) * (1600 / ((i : ℝ) + 1) * ‖ρ‖) :=
            mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
        _ = 1600 / ((i : ℝ) + 1) * (zOrd χ ρ : ℝ) * ‖ρ‖ := by ring
    refine st1.trans ?_
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun ρ : ℂ => 0 ≤ ρ.im), two_mul]
    apply add_le_add
    · refine le_trans ?_ (hwin i hiM (i : ℝ) (Nat.abs_cast i))
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro ρ hρ
        obtain ⟨hρ1, hs⟩ := Finset.mem_filter.mp hρ
        obtain ⟨hρF, hρi⟩ := Finset.mem_filter.mp hρ1
        obtain ⟨r0, r1, r2, r3⟩ : ρ ∈ ZerosBelow χ T := hfin.mem_toFinset.mp hρF
        rw [Set.Finite.mem_toFinset]
        refine ⟨r0, r1, ?_, r3⟩
        have a1 : (i : ℝ) ≤ |ρ.im| := by rw [← hρi]; exact Nat.floor_le (abs_nonneg _)
        have a2 : |ρ.im| < (i : ℝ) + 1 := by rw [← hρi]; exact Nat.lt_floor_add_one _
        rw [abs_of_nonneg hs] at a1 a2
        rw [abs_le]
        constructor <;> linarith
      · intro ρ _ _
        exact Nat.cast_nonneg _
    · refine le_trans ?_ (hwin i hiM (-(i : ℝ)) (by rw [abs_neg, Nat.abs_cast]))
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro ρ hρ
        obtain ⟨hρ1, hs⟩ := Finset.mem_filter.mp hρ
        obtain ⟨hρF, hρi⟩ := Finset.mem_filter.mp hρ1
        obtain ⟨r0, r1, r2, r3⟩ : ρ ∈ ZerosBelow χ T := hfin.mem_toFinset.mp hρF
        rw [Set.Finite.mem_toFinset]
        refine ⟨r0, r1, ?_, r3⟩
        have a1 : (i : ℝ) ≤ |ρ.im| := by rw [← hρi]; exact Nat.floor_le (abs_nonneg _)
        have a2 : |ρ.im| < (i : ℝ) + 1 := by rw [← hρi]; exact Nat.lt_floor_add_one _
        rw [abs_of_neg (not_le.mp hs)] at a1 a2
        rw [abs_le]
        constructor <;> linarith
      · intro ρ _ _
        exact Nat.cast_nonneg _
  have hmaps : ∀ ρ ∈ hfin.toFinset, ⌊|ρ.im|⌋₊ ∈ Finset.range (M + 1) := by
    intro ρ hρ
    obtain ⟨r0, r1, r2, r3⟩ : ρ ∈ ZerosBelow χ T := hfin.mem_toFinset.mp hρ
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.floor_le_floor r2.le))
  have hH : ∑ i ∈ Finset.range (M + 1), (1 : ℝ) / ((i : ℝ) + 1) ≤ 1 + Lq := by
    have h := harmonic_le_one_add_log (M + 1)
    have e : ((harmonic (M + 1) : ℚ) : ℝ) = ∑ i ∈ Finset.range (M + 1), (1 : ℝ) / ((i : ℝ) + 1) := by
      simp [harmonic, one_div]
    rw [e] at h
    linarith
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ i ∈ Finset.range (M + 1), ∑ ρ ∈ hfin.toFinset with ⌊|ρ.im|⌋₊ = i, (zOrd χ ρ : ℝ) / ‖ρ‖
      ≤ ∑ i ∈ Finset.range (M + 1), 1600 / ((i : ℝ) + 1) * (2 * (C * La)) := Finset.sum_le_sum hfib
    _ = 3200 * C * La * ∑ i ∈ Finset.range (M + 1), (1 : ℝ) / ((i : ℝ) + 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ ≤ 3200 * C * (3 * Lq) * (3 * Lq) := by
        have hLq0 : 0 ≤ Lq := by linarith
        apply mul_le_mul _ (by linarith) (Finset.sum_nonneg (fun i _ => by positivity)) (by positivity)
        exact mul_le_mul_of_nonneg_left hLa3 (by positivity)
    _ = 28800 * C * Lq ^ 2 := by ring

theorem ms_sum {β : Type*} [AddCommMonoid β] (F : Finset ℂ) (n : ℂ → ℕ) (f : ℂ → β) :
    ((∑ ρ ∈ F, Multiset.replicate (n ρ) ρ).map f).sum = ∑ ρ ∈ F, n ρ • f ρ := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Multiset.map_add, Multiset.sum_add, ih, Finset.sum_insert ha,
      Multiset.map_replicate, Multiset.sum_replicate]

theorem ms_mem (F : Finset ℂ) (n : ℂ → ℕ) {x : ℂ}
    (hx : x ∈ ∑ ρ ∈ F, Multiset.replicate (n ρ) ρ) : x ∈ F := by
  obtain ⟨i, hi, hxi⟩ := Multiset.mem_sum.mp hx
  rw [Multiset.eq_of_mem_replicate hxi]
  exact hi

theorem not_primitive_two (χ : DirichletCharacter ℂ 2) : ¬ χ.IsPrimitive := by
  intro hp
  have h1 : χ = 1 := by
    apply MulChar.ext
    intro a
    have ha : a = 1 := by revert a; decide
    rw [ha]; simp
  rw [DirichletCharacter.isPrimitive_def, h1, DirichletCharacter.conductor_one] at hp
  norm_num at hp

theorem exceptional_zero_real_of_landau_page {C1 c : ℝ} (hc : 0 < c) (D : D7) (h6 : adm6 D C1 c) {Q : ℝ} {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (hNQ : (N : ℝ) ≤ Q) {ρ : ℂ} (h0 : 0 < ρ.re)
    (hz : DirichletCharacter.LFunction χ ρ = 0) (hr : 1 - c / Real.log (Q * (|ρ.im| + 3)) < ρ.re) :
    3 ≤ N ∧ ρ.im = 0 ∧ IsRealChar χ := by
  obtain ⟨-, hD1, hD3⟩ := h6
  have hN0 : N ≠ 0 := NeZero.ne N
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hN0
  have ha : 0 ≤ |ρ.im| := abs_nonneg _
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  by_cases h3 : 3 ≤ N
  · have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast h3
    have hm3 : (3 : ℝ) ≤ max (N : ℝ) (N * |ρ.im|) := hN3.trans (le_max_left _ _)
    have hmQ : max (N : ℝ) (N * |ρ.im|) ≤ Q * (|ρ.im| + 3) := by
      apply max_le <;> nlinarith
    have hlm : 0 < Real.log (max (N : ℝ) (N * |ρ.im|)) := Real.log_pos (by linarith)
    have hll : Real.log (max (N : ℝ) (N * |ρ.im|)) ≤ Real.log (Q * (|ρ.im| + 3)) :=
      Real.log_le_log (by linarith) hmQ
    have hdiv : c / Real.log (Q * (|ρ.im| + 3)) ≤ c / Real.log (max (N : ℝ) (N * |ρ.im|)) :=
      div_le_div_of_nonneg_left hc.le hlm hll
    obtain ⟨a1, a2, -⟩ := hD1 N χ hp h3 ρ hz (by linarith)
    exact ⟨h3, a2, a1⟩
  · exfalso
    have hcases : N = 1 ∨ N = 2 := by omega
    rcases hcases with rfl | rfl
    · rw [DirichletCharacter.LFunction_modOne_eq] at hz
      have h1 : ρ.re < 1 := by
        by_contra hge
        exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hz
      have h2 := hD3 ρ hz h0 h1
      have hg : 0 < Real.log (|ρ.im| + 3) := Real.log_pos (by linarith)
      have hll : Real.log (|ρ.im| + 3) ≤ Real.log (Q * (|ρ.im| + 3)) :=
        Real.log_le_log (by linarith) (by nlinarith)
      have hdiv : c / Real.log (Q * (|ρ.im| + 3)) ≤ c / Real.log (|ρ.im| + 3) :=
        div_le_div_of_nonneg_left hc.le hg hll
      linarith
    · exact not_primitive_two χ hp

theorem zero_free {Cq c : ℝ} (hc : 0 < c) (D : D7) (h6 : adm6 D Cq c) {Q : ℝ} (hQ3 : 3 ≤ Q) {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hg : GoodFor Q χ) {ρ : ℂ}
    (hz : DirichletCharacter.LFunction χ ρ = 0) :
    ρ.re ≤ 1 - min c (1 / 400) / Real.log (Q * (|ρ.im| + 3)) := by
  by_contra hh
  push Not at hh
  have hlog1 : 1 ≤ Real.log (Q * (|ρ.im| + 3)) := by
    rw [Real.le_log_iff_exp_le (by nlinarith [abs_nonneg ρ.im])]
    have := Real.exp_one_lt_d9
    nlinarith [abs_nonneg ρ.im]
  have hlogpos : 0 < Real.log (Q * (|ρ.im| + 3)) := by linarith
  have h1 : min c (1 / 400) / Real.log (Q * (|ρ.im| + 3)) ≤ c / Real.log (Q * (|ρ.im| + 3)) :=
    div_le_div_of_nonneg_right (min_le_left _ _) hlogpos.le
  have h1' : min c (1 / 400) / Real.log (Q * (|ρ.im| + 3)) ≤ 1 / 400 := by
    calc min c (1 / 400) / Real.log (Q * (|ρ.im| + 3)) ≤ min c (1 / 400) / 1 :=
          div_le_div_of_nonneg_left (lt_min hc (by norm_num)).le one_pos hlog1
      _ ≤ 1 / 400 := by rw [div_one]; exact min_le_right _ _
  have h := (exceptional_zero_real_of_landau_page hc D h6 hg.1 hg.2.2.1 (by linarith) hz (by linarith)).2
  have him : ρ.im = 0 := h.1
  rw [him, abs_zero, zero_add] at hh
  have hl1 : 1 ≤ Real.log (Q * 3) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  have h2 : min c (1 / 400) / Real.log (Q * 3) ≤ 1 / 400 := by
    calc min c (1 / 400) / Real.log (Q * 3) ≤ min c (1 / 400) / 1 :=
          div_le_div_of_nonneg_left (lt_min hc (by norm_num)).le one_pos hl1
      _ ≤ 1 / 400 := by rw [div_one]; exact min_le_right _ _
  exact hg.2.2.2 ρ (by linarith) (by rw [him, abs_zero]; linarith) hz

set_option maxHeartbeats 1000000 in

theorem second_psi_bound_of_region_and_zero_sum {Cq c C7 C2 : ℝ} (hc : 0 < c) (hC7 : 0 < C7) (hC2 : 0 < C2) (D : D7) (h6 : adm6 D Cq c)
    (h7 : adm7 D C7) (hZ : ZeroSum C2) : ∃ B c1 : ℝ, 0 < B ∧ 0 < c1 ∧ SecondPsiBound B c1 := by
  obtain ⟨A, a, hA, ha, hH⟩ := Formalism.HermitianLattices.GL2a2.zero_sum_bound_large (min c (1 / 400)) C2
    (lt_min hc (by norm_num)) hC2
  refine ⟨C7 * (3460 + 2 * C2) + A, min a (1 / 2), by positivity, lt_min ha (by norm_num), ?_⟩
  intro Q hQ N _ χ hχ hg u hu
  have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos _) hu
  have hN1 : N ≠ 1 := by
    intro h
    subst h
    exact hχ (DirichletCharacter.level_one χ)
  have hN2 : N ≠ 2 := by
    intro h
    subst h
    apply hχ
    apply MulChar.ext
    intro b
    rw [Subsingleton.elim b 1]
    simp
  have hN3 : 3 ≤ N := by
    have := NeZero.ne N
    omega
  have hN3' : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hNQ : (N : ℝ) ≤ Q := hg.2.2.1
  have hQ3 : 3 ≤ Q := hN3'.trans hNQ
  have hN0 : (0 : ℝ) < N := by linarith
  have hlQ1 : 1 < Real.log Q := by
    rw [Real.lt_log_iff_exp_lt hQ]
    have := Real.exp_one_lt_d9
    linarith
  obtain ⟨lu, hlu⟩ : ∃ lu, lu = Real.log u := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt lu := ⟨_, rfl⟩
  rw [← hlu, ← hs]
  have hu' : Real.log Q ^ 2 ≤ lu := by rw [hlu, Real.le_log_iff_exp_le hu0]; exact hu
  have hlu1 : 1 ≤ lu := by nlinarith
  have hs2 : s ^ 2 = lu := by rw [hs]; exact Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ s := by rw [hs]; exact (Real.le_sqrt' one_pos).2 (by simpa using hlu1)
  have hlQs : Real.log Q ≤ s := by rw [hs]; exact (Real.le_sqrt' (by linarith)).2 hu'
  have hslu : s ≤ lu := by nlinarith
  have hT2 : 2 ≤ Real.exp s := by have := Real.add_one_le_exp s; linarith
  have hTu : Real.exp s ≤ u := by rw [← Real.le_log_iff_exp_le hu0, ← hlu]; exact hslu
  obtain ⟨hfin, hexp⟩ := h7 N χ hg.1 u (Real.exp s) hT2 hTu
  obtain ⟨X, hX⟩ : ∃ X, X = Real.exp (s / 2) := ⟨_, rfl⟩
  have hX0 : 0 < X := by rw [hX]; exact Real.exp_pos _
  have hTX : Real.exp s = X * X := by rw [hX, ← Real.exp_add]; congr 1; ring
  have hXinv : X⁻¹ = Real.exp (-(s / 2)) := by rw [hX, Real.exp_neg]
  have p4 : s ^ 4 ≤ 384 * X := by
    have h := Real.pow_div_factorial_le_exp (s / 2) (by linarith) 4
    have hfac : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [hfac, ← hX] at h
    have e : (s / 2) ^ 4 / 24 = s ^ 4 / 384 := by ring
    rw [e] at h
    linarith
  have w : lu / 2 ≤ u * X⁻¹ := by
    have e : u * X⁻¹ = Real.exp (lu - s / 2) := by
      rw [Real.exp_sub, hlu, Real.exp_log hu0, ← hX, div_eq_mul_inv]
    rw [e]
    calc lu / 2 ≤ lu / 2 + 1 := by linarith
      _ ≤ Real.exp (lu / 2) := Real.add_one_le_exp _
      _ ≤ Real.exp (lu - s / 2) := Real.exp_le_exp.2 (by linarith)

  have tableLogDegreeOne : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have lNQ : Real.log N ≤ Real.log Q := Real.log_le_log hN0 hNQ
  have l1 : Real.log (N * u) = Real.log N + lu := by rw [Real.log_mul hN0.ne' hu0.ne', hlu]
  have l2 : Real.log (N * u * Real.exp s) = Real.log N + lu + s := by
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', l1, Real.log_exp]
  have q1 : Real.log (N * u * Real.exp s) ^ 2 ≤ 9 * (384 * X) := by
    have h0 : 0 ≤ Real.log (N * u * Real.exp s) := by rw [l2]; linarith
    have h3 : Real.log (N * u * Real.exp s) ≤ 3 * lu := by rw [l2]; linarith
    have h4 := pow_le_pow_left₀ h0 h3 2
    have h5 : (3 * lu) ^ 2 = 9 * s ^ 4 := by rw [← hs2]; ring
    rw [h5] at h4
    linarith
  have e1 : u * Real.log (N * u * Real.exp s) ^ 2 / Real.exp s ≤ 3456 * (u * X⁻¹) := by
    rw [hTX]
    calc u * Real.log (N * u * (X * X)) ^ 2 / (X * X) ≤ u * (9 * (384 * X)) / (X * X) := by
          rw [← hTX]
          gcongr
      _ = 3456 * (u * X⁻¹) := by field_simp; ring
  have e2 : Real.log (N * u) ≤ 4 * (u * X⁻¹) := by rw [l1]; linarith
  have e3 : ∑ᶠ ρ ∈ ZerosBelow χ 1, (zOrd χ ρ : ℝ) / ‖ρ‖ ≤ 2 * C2 * (u * X⁻¹) := by
    refine (hZ Q N χ hχ hg 1 le_rfl).trans ?_
    rw [mul_one]
    calc C2 * Real.log Q ^ 2 ≤ C2 * (2 * (u * X⁻¹)) :=
          mul_le_mul_of_nonneg_left (by linarith) hC2.le
      _ = 2 * C2 * (u * X⁻¹) := by ring

  have hHH := hH Q u (∑ ρ ∈ hfin.toFinset, Multiset.replicate (zOrd χ ρ) ρ) hQ3 hu
  rw [← hlu, ← hs, ms_sum, ms_sum] at hHH
  have e4 : ‖∑ᶠ ρ ∈ ZerosBelow χ (Real.exp s), (zOrd χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤
      A * u * Real.exp (-a * s) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    have h := hHH ?_ ?_
    · simpa [nsmul_eq_mul] using h
    · intro ρ hρ
      obtain ⟨r0, r1, r2, r3⟩ : ρ ∈ ZerosBelow χ (Real.exp s) :=
        hfin.mem_toFinset.mp (ms_mem _ _ hρ)
      exact ⟨r2.le, zero_free hc D h6 hQ3 hg r3⟩
    · have h := hZ Q N χ hχ hg (Real.exp s) (by linarith)
      rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at h
      simpa [nsmul_eq_mul, div_eq_mul_inv] using h
  obtain ⟨Em, hEm⟩ : ∃ Em, Em = Real.exp (-min a (1 / 2) * s) := ⟨_, rfl⟩
  rw [← hEm]
  have hEm0 : 0 < Em := by rw [hEm]; exact Real.exp_pos _
  have m1 : X⁻¹ ≤ Em := by
    rw [hXinv, hEm]
    apply Real.exp_le_exp.2
    have h := mul_le_mul_of_nonneg_right (min_le_right a (1 / 2)) (by linarith : (0 : ℝ) ≤ s)
    linarith
  have m2 : Real.exp (-a * s) ≤ Em := by
    rw [hEm]
    apply Real.exp_le_exp.2
    have h := mul_le_mul_of_nonneg_right (min_le_left a (1 / 2)) (by linarith : (0 : ℝ) ≤ s)
    linarith
  have m3 : u * X⁻¹ ≤ u * Em := mul_le_mul_of_nonneg_left m1 hu0.le
  calc ‖psi0 χ u‖
      = ‖(psi0 χ u + ∑ᶠ ρ ∈ ZerosBelow χ (Real.exp s), (zOrd χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)) -
          ∑ᶠ ρ ∈ ZerosBelow χ (Real.exp s), (zOrd χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ := by
        rw [add_sub_cancel_right]
    _ ≤ ‖psi0 χ u + ∑ᶠ ρ ∈ ZerosBelow χ (Real.exp s), (zOrd χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ +
          ‖∑ᶠ ρ ∈ ZerosBelow χ (Real.exp s), (zOrd χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ := norm_sub_le _ _
    _ ≤ C7 * (3456 * (u * X⁻¹) + 4 * (u * X⁻¹) + 2 * C2 * (u * X⁻¹)) + A * u * Real.exp (-a * s) := by
        refine add_le_add (hexp.trans ?_) e4
        exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add e1 e2) e3) hC7.le
    _ = C7 * (3460 + 2 * C2) * (u * X⁻¹) + A * u * Real.exp (-a * s) := by ring
    _ ≤ C7 * (3460 + 2 * C2) * (u * Em) + A * u * Em :=
        add_le_add (mul_le_mul_of_nonneg_left m3 (by positivity))
          (mul_le_mul_of_nonneg_left m2 (by positivity))
    _ = (C7 * (3460 + 2 * C2) + A) * u * Em := by ring

theorem psiBounds_of_adm {Cq c C7 C11 : ℝ} (hc : 0 < c) (hC7 : 0 < C7) (hC11 : 0 < C11) (D : D7)
    (h6 : adm6 D Cq c) (h7 : adm7 D C7) (h11 : adm11 D C11) :
    ∃ C1 c1 : ℝ, 0 < C1 ∧ 0 < c1 ∧ PsiBounds C1 c1 := by
  have hZ : ZeroSum (28800 * C11) := zeroSum_of hC11 D h7 h11
  have hC2 : 0 < 28800 * C11 := by positivity
  obtain ⟨B, c1, hB, hc1, hH2⟩ := second_psi_bound_of_region_and_zero_sum hc hC7 hC2 D h6 h7 hZ
  exact ⟨max (C7 * (5 + 28800 * C11) + 28800 * C11) B, c1, lt_of_lt_of_le hB (le_max_right _ _), hc1,
    psiBounds_of (first_psi_bound_of_zero_sum hC7 hC2.le D h7 hZ) hH2⟩

theorem proposition_eleven_two_of_characters {eps : ℝ} (h0 : 0 < eps) (h1 : eps < 1) {Cq c C7 C11 : ℝ} (hCq : 0 < Cq) (hc : 0 < c) (hC7 : 0 < C7)
    (hC11 : 0 < C11) (D0 : D7) (h6 : adm6 D0 Cq c) (h7 : adm7 D0 C7) (h11 : adm11 D0 C11) :
    ∃ C x0 : ℝ, 0 < C ∧ 1 < x0 ∧ ∀ x ≥ x0, ∀ D : D7, Conclusion2 D x eps C := by
  obtain ⟨C1, c1, hC1, hc1, H⟩ := psiBounds_of_adm hc hC7 hC11 D0 h6 h7 h11
  obtain ⟨C, x0, hC, hx0, h⟩ := lemma_two_two_of_count_and_psi_bounds h0 h1 hC1 hc1 H hCq.le
  exact ⟨C, x0, hC, hx0, fun x hx D => h x hx D c h6⟩

theorem lemma_two_two_family_of_count_and_zeros {eps : ℝ} (Fm : FamP eps) (h0 : 0 < eps) (h1 : eps < 1) (h6 : FamilySixthHypothesis Fm)
    (h7 : adm7F Fm) (h11 : ComplementTwoFamily Fm) : Conclusion2Family Fm := by
  obtain ⟨Cq, c, hCq, hc, h6⟩ := h6
  obtain ⟨C7, hC7, h7⟩ := h7
  obtain ⟨C11, hC11, h11⟩ := h11
  obtain ⟨y, hy, -, -, ⟨i⟩⟩ := Fm.toFamCore.exists_pt 2
  have hy1 : y > 1 := by linarith
  obtain ⟨C, x0, hC, hx0, h⟩ := proposition_eleven_two_of_characters h0 h1 hCq hc hC7 hC11 (Fm.D y i) (h6 y hy1 i)
    (h7 y hy1 i) (h11 y hy1 i)
  exact ⟨C, hC, x0, hx0, fun x hx j => h x hx _⟩

theorem fam_eps {eps : ℝ} (Fm : FamP eps) : 0 < eps ∧ eps < 1 := by
  obtain ⟨i⟩ := Fm.Ix_zero
  have e := Fm.L_eps 0 i
  have p := (Fm.L 0 i).sc.eps_pos
  have q := (Fm.L 0 i).sc.eps_lt
  rw [e] at p q
  exact ⟨p, by linarith⟩

theorem lemma_two_two_family_of_admitted {eps : ℝ} (Fm : FamP eps) (h6 : FamilySixthHypothesis Fm) (h7 : adm7F Fm) (h11 : ComplementTwoFamily Fm) :
    Conclusion2Family Fm :=
  lemma_two_two_family_of_count_and_zeros Fm (fam_eps Fm).1 (fam_eps Fm).2 h6 h7 h11

end Formalism.MainNotions.ShortIntervalPrimes

end

noncomputable section

namespace Formalism.MainNotions.ShortIntervalPrimes

open Finset Filter Topology ArithmeticFunction MeasureTheory Formalism.MainNotions.GlobalTheoryTheory
open Br

open private Emain_lower_bound from Formalism.GL3MeanSquares.HookFormulaTorsion.PrimesInProgressionCountLowerBound

section ShortIntervalLowerBound

variable (K0 : Type) [Field K0] [NumberField K0]

def GrBound : Prop :=
  ∀ qq : Ideal (NumberField.RingOfIntegers K0), qq ≠ ⊥ → 1 ≤ grCard K0 qq ∧ (grCard K0 qq : ℝ) ≤ Bmod K0 qq

def Deg2Bound : Prop :=
  ∀ (qq I0 : Ideal (NumberField.RingOfIntegers K0)) (Y : ℝ), 1 ≤ Y →
    (Set.ncard {P : Ideal (NumberField.RingOfIntegers K0) | P.IsPrime ∧ CoprimeTo K0 qq P ∧ RayRel K0 qq P I0 ∧
      ¬ (Ideal.absNorm P).Prime ∧ (Ideal.absNorm P : ℝ) ≤ Y} : ℝ) ≤ 2 * Real.sqrt Y

variable {K0}

lemma Bmod_ge {qq : Ideal (NumberField.RingOfIntegers K0)} (h : qq ≠ ⊥) : 4 ≤ Bmod K0 qq := by
  unfold Bmod
  have h1 : (1 : ℝ) ≤ |(NumberField.discr K0 : ℝ)| := by
    have : (1 : ℤ) ≤ |NumberField.discr K0| := Int.one_le_abs (NumberField.discr_ne_zero K0)
    exact_mod_cast this
  have h2 : (1 : ℝ) ≤ (Ideal.absNorm qq : ℝ) := by
    have : Ideal.absNorm qq ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  nlinarith

lemma rhoErr_eq (C c B X : ℝ) : rhoErr C c B X = Formalism.HermitianLattices.GL2PrimeSums.rhoErr C c B X := by
  unfold rhoErr Formalism.HermitianLattices.GL2PrimeSums.rhoErr
  congr 3 <;> ring

lemma Emain_eq (θ : ℤ) (β X : ℝ) : Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X = Li X - (θ : ℝ) * Li (X ^ β) := rfl

theorem lemma_two_three_first_Li_lower_bound {cQ C0 : ℝ} (hcQ : 0 < cQ) (h60 : 60 ≤ C0) (h2 : 2 / cQ ≤ C0)
    {qq : Ideal (NumberField.RingOfIntegers K0)} (hqq : qq ≠ ⊥) {X : ℝ} (hX : Bmod K0 qq ^ C0 ≤ X)
    (be : ℝ) (th : ℤ) (hth : th = -1 ∨ th = 0 ∨ th = 1) (hb1 : 1 / 2 ≤ be) (hb2 : be < 1)
    (hb3 : cQ / (Bmod K0 qq ^ 2 * Real.log (Bmod K0 qq)) ≤ 1 - be) :
    1 / 100 * Bmod K0 qq ^ (-5 : ℝ) * X / Real.log X ≤ Li X - (th : ℝ) * Li (X ^ be) := by
  have hB := Bmod_ge hqq
  set B := Bmod K0 qq with hBdef
  have hB0 : 0 < B := by linarith
  have hlB : 0 < Real.log B := Real.log_pos (by linarith)
  have hX60 : B ^ (60 : ℝ) ≤ X := (Real.rpow_le_rpow_of_exponent_le (by linarith) h60).trans hX
  have hlogX : C0 * Real.log B ≤ Real.log X := by
    have := Real.log_le_log (Real.rpow_pos_of_pos hB0 _) hX
    rwa [Real.log_rpow hB0] at this
  have hd : th = 1 → 2 / B ^ 2 ≤ (1 - be) * Real.log X := by
    intro _
    have e : 2 / B ^ 2 = (cQ / (B ^ 2 * Real.log B)) * ((2 / cQ) * Real.log B) := by field_simp
    rw [e]
    refine mul_le_mul hb3 ?_ (by positivity) (by linarith)
    exact (mul_le_mul_of_nonneg_right h2 hlB.le).trans hlogX
  rw [← Emain_eq]
  exact Emain_lower_bound hth hB hb1 hb2 hd hX60

lemma finite_norm_le (Y : ℝ) :
    {P : Ideal (NumberField.RingOfIntegers K0) | (Ideal.absNorm P : ℝ) ≤ Y}.Finite := by
  refine (Ideal.finite_setOfPred_absNorm_le (S := NumberField.RingOfIntegers K0) ⌊Y⌋₊).subset ?_
  intro P hP
  exact Nat.le_floor hP

end ShortIntervalLowerBound

theorem lemma_two_three_second_of_Q4 (C0 Cr cr cQ : ℝ) (hC0 : 0 < C0) (hCr : 0 < Cr) (hcr : 0 < cr) (hcQ : 0 < cQ) :
    ∃ C0' c : ℝ, C0 ≤ C0' ∧ 0 < c ∧ ∀ (K0 : Type) [Field K0] [NumberField K0]
      (Comparison₂ : Ideal (NumberField.RingOfIntegers K0) → ℝ → (Ideal (NumberField.RingOfIntegers K0) → ℤ) → Prop),
      SiegelZeroExceptionalCharacter K0 Comparison₂ C0 Cr cr cQ → GrBound K0 → Deg2Bound K0 →
      ∀ qq : Ideal (NumberField.RingOfIntegers K0), qq ≠ ⊥ → ∀ X : ℝ, Bmod K0 qq ^ C0' ≤ X →
      ∀ I0, CoprimeTo K0 qq I0 → ∀ h : ℝ, rhoErr Cr cr (Bmod K0 qq) X ≤ h / 100 → h ≤ 1 →
        Bmod K0 qq ^ (7 : ℝ) ≤ h * X ^ ((1 : ℝ) / 3) →
        c * h * Bmod K0 qq ^ (-6 : ℝ) * X / Real.log X ≤ (nDeg1 K0 qq I0 X h : ℝ) := by
  obtain ⟨C0', c, h0, hc, core⟩ := Formalism.HermitianLattices.GL2PrimeSums.shortIntervalLowerBound C0 Cr cr cQ hC0 hCr hcr hcQ
  refine ⟨C0', c, h0, hc, ?_⟩
  intro K0 _ _ Comparison₂ hQ hG hD qq hqq X hX I0 hI0 h hρ hh1 hB7
  obtain ⟨be, th, halt, -, hpi⟩ := hQ qq hqq
  have hB := Bmod_ge hqq
  obtain ⟨hG1, hGB⟩ := hG qq hqq
  set B := Bmod K0 qq with hBdef
  have hB0 : 0 < B := by linarith
  set S1 : ℝ → Set (Ideal (NumberField.RingOfIntegers K0)) := fun Y =>
    {P | P.IsPrime ∧ CoprimeTo K0 qq P ∧ RayRel K0 qq P I0 ∧ (Ideal.absNorm P).Prime ∧
      (Ideal.absNorm P : ℝ) ≤ Y} with hS1
  set S2 : ℝ → Set (Ideal (NumberField.RingOfIntegers K0)) := fun Y =>
    {P | P.IsPrime ∧ CoprimeTo K0 qq P ∧ RayRel K0 qq P I0 ∧ ¬ (Ideal.absNorm P).Prime ∧
      (Ideal.absNorm P : ℝ) ≤ Y} with hS2
  have f1 : ∀ Y, (S1 Y).Finite := fun Y => (finite_norm_le Y).subset (fun P hP => hP.2.2.2.2)
  have f2 : ∀ Y, (S2 Y).Finite := fun Y => (finite_norm_le Y).subset (fun P hP => hP.2.2.2.2)
  have hsum : ∀ Y, piCC K0 qq I0 Y = (S1 Y).ncard + (S2 Y).ncard := by
    intro Y
    rw [← Set.ncard_union_eq ?_ (f1 Y) (f2 Y)]
    · unfold piCC
      congr 1
      ext P
      simp only [hS1, hS2, Set.mem_ofPred_eq, Set.mem_union]
      by_cases hp : (Ideal.absNorm P).Prime <;> simp [hp]
    · rw [Set.disjoint_left]
      intro P h1 h2
      exact h2.2.2.2.1 h1.2.2.2.1
  have hθ : th I0 ∈ ({-1, 0, 1} : Set ℤ) := by
    rcases halt with h | h
    · simp [h I0]
    · rcases h.1.1 I0 hI0 with h | h <;> simp [h]
  have hβ : th I0 ≠ 0 → 1 / 2 ≤ be ∧ be < 1 ∧ cQ / (B ^ 2 * Real.log B) ≤ 1 - be := by
    intro hne
    rcases halt with h | h
    · exact absurd (h I0) hne
    · exact h.2
  have hGpos : (0 : ℝ) < grCard K0 qq := by exact_mod_cast hG1
  have hQ' : ∀ Y : ℝ, B ^ C0 ≤ Y →
      |(grCard K0 qq : ℝ) * (((S1 Y).ncard : ℝ) + (S2 Y).ncard) - Formalism.HermitianLattices.GL2PrimeSums.Emain (th I0) be Y| ≤
        Formalism.HermitianLattices.GL2PrimeSums.rhoErr Cr cr B Y * Formalism.HermitianLattices.GL2PrimeSums.Emain (th I0) be Y := by
    intro Y hY
    have := hpi I0 hI0 Y hY
    rw [hsum Y, rhoErr_eq, ← Emain_eq] at this
    push_cast at this
    have e : (grCard K0 qq : ℝ) * (((S1 Y).ncard : ℝ) + (S2 Y).ncard) - Formalism.HermitianLattices.GL2PrimeSums.Emain (th I0) be Y =
        (grCard K0 qq : ℝ) * ((((S1 Y).ncard : ℝ) + (S2 Y).ncard) -
          Formalism.HermitianLattices.GL2PrimeSums.Emain (th I0) be Y / (grCard K0 qq : ℝ)) := by
      field_simp
    rw [e, abs_mul, abs_of_pos hGpos]
    calc (grCard K0 qq : ℝ) * |(((S1 Y).ncard : ℝ) + (S2 Y).ncard) -
          Formalism.HermitianLattices.GL2PrimeSums.Emain (th I0) be Y / (grCard K0 qq : ℝ)|
        ≤ (grCard K0 qq : ℝ) * (Formalism.HermitianLattices.GL2PrimeSums.rhoErr Cr cr B Y *
            (Formalism.HermitianLattices.GL2PrimeSums.Emain (th I0) be Y / (grCard K0 qq : ℝ))) :=
          mul_le_mul_of_nonneg_left this hGpos.le
      _ = _ := by field_simp
  have key := (core B (grCard K0 qq) be (th I0) (fun Y => (S1 Y).ncard) (fun Y => (S2 Y).ncard) hB
    (by exact_mod_cast hG1) hGB hθ hβ (fun Y hY => hD qq I0 Y hY) hQ' X hX).2 h hh1
    (by rw [← rhoErr_eq]; exact hρ) hB7
  refine key.trans (le_of_eq ?_)
  have hρ0 : 0 < rhoErr Cr cr B X := by unfold rhoErr; positivity
  have hh0 : 0 < h := by linarith
  have hX0 : 0 < X := lt_of_lt_of_le (Real.rpow_pos_of_pos hB0 _) hX
  have hsub : S1 X ⊆ S1 (X * (1 + h)) := by
    intro P hP
    refine ⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2.1, hP.2.2.2.2.trans ?_⟩
    nlinarith
  have hdiff : nDeg1 K0 qq I0 X h = (S1 (X * (1 + h)) \ S1 X).ncard := by
    unfold nDeg1
    congr 1
    ext P
    simp only [hS1, Set.mem_ofPred_eq, Set.mem_sdiff]
    constructor
    · rintro ⟨a, b, c', d, e, f⟩
      exact ⟨⟨a, b, c', d, f⟩, fun hh => absurd hh.2.2.2.2 (not_le.2 e)⟩
    · rintro ⟨⟨a, b, c', d, f⟩, hn⟩
      refine ⟨a, b, c', d, ?_, f⟩
      by_contra hle
      exact hn ⟨a, b, c', d, not_lt.1 hle⟩
  rw [hdiff, Set.ncard_sdiff hsub (f1 X), Nat.cast_sub (Set.ncard_le_ncard hsub (f1 _))]

theorem lemma_two_three_of_Q4_both_fields (C0 Cr cr cQ cQ' : ℝ) (hC0 : 0 < C0) (hCr : 0 < Cr) (hcr : 0 < cr) (hcQ : 0 < cQ)
    (hcQ' : 0 < cQ') :
    ∃ C0' c1 c2 : ℝ, 0 < C0' ∧ 0 < c1 ∧ 0 < c2 ∧ ∀ (D : Formalism.BasicNotions.D7) (c1' : ℝ), adm8 D C0 Cr cr cQ c1' →
      GrBound ℚ → Deg2Bound ℚ → GrBound D.host.K → Deg2Bound D.host.K →
      PointsLemma D cQ' C0' Cr cr c1 c2 := by
  obtain ⟨C0', c, h0, hc, hii⟩ := lemma_two_three_second_of_Q4 C0 Cr cr cQ hC0 hCr hcr hcQ
  refine ⟨max C0' (max 60 (2 / cQ')), 1 / 100, c, by positivity, by norm_num, hc, ?_⟩
  intro D c1' hadm hGQ hDQ hGK hDK
  have a1 : C0' ≤ max C0' (max 60 (2 / cQ')) := le_max_left _ _
  have a2 : 60 ≤ max C0' (max 60 (2 / cQ')) := (le_max_left _ _).trans (le_max_right _ _)
  have a3 : 2 / cQ' ≤ max C0' (max 60 (2 / cQ')) := (le_max_right _ _).trans (le_max_right _ _)
  constructor
  · intro qq hqq X hX
    refine ⟨fun be th hth hb1 hb2 hb3 => lemma_two_three_first_Li_lower_bound hcQ' a2 a3 hqq hX be th hth hb1 hb2 hb3, ?_⟩
    have hB := Bmod_ge hqq
    exact hii ℚ _ hadm.1 hGQ hDQ qq hqq X ((Real.rpow_le_rpow_of_exponent_le (by linarith) a1).trans hX)
  · intro qq hqq X hX
    refine ⟨fun be th hth hb1 hb2 hb3 => lemma_two_three_first_Li_lower_bound hcQ' a2 a3 hqq hX be th hth hb1 hb2 hb3, ?_⟩
    have hB := Bmod_ge hqq
    exact hii D.host.K _ hadm.2 hGK hDK qq hqq X ((Real.rpow_le_rpow_of_exponent_le (by linarith) a1).trans hX)

theorem lemma_two_three_of_siegel_bound {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h8 : FamilyTemperatureAsymptotic Fm) (hGQ : GrBound ℚ) (hDQ : Deg2Bound ℚ)
    (hK : ∀ x > 1, ∀ i : Fm.Ix x, GrBound (Fm.D x i).host.K ∧ Deg2Bound (Fm.D x i).host.K) : Conclusion3Family Fm := by
  obtain ⟨C0, Cr, cr, cQ, c1', hC0, hCr, hcr, hcQ, -, h⟩ := h8
  intro cQ' hcQ'
  obtain ⟨C0', c1, c2, p1, p2, p3, hh⟩ := lemma_two_three_of_Q4_both_fields C0 Cr cr cQ cQ' hC0 hCr hcr hcQ hcQ'
  exact ⟨C0', Cr, cr, c1, c2, p1, hCr, hcr, p2, p3,
    fun x hx i => hh _ c1' (h x hx i) hGQ hDQ (hK x hx i).1 (hK x hx i).2⟩

end Formalism.MainNotions.ShortIntervalPrimes

end

noncomputable section

namespace Formalism.MainNotions.ShortIntervalPrimes

open Finset Filter Topology ArithmeticFunction MeasureTheory Formalism.MainNotions.GlobalTheoryTheory
open Br

def Conclusion4a (x eps : ℝ) : Prop :=
  ∀ m0 : ℕ, 0 < m0 → 8 ∣ m0 →
    (∀ p : ℕ, p.Prime → p ∣ m0 → (p : ℝ) ≤ x ^ (eps / 5) ∨ zz x < p) →
  ∀ a0 : ℤ, IsCoprime a0 (m0 : ℤ) → a0 % 4 = 3 →
  ∀ X : ℝ, 0 < X → (1 / 4) * Real.log x ^ 2 * Real.log m0 ≤ Real.log X →
    x ^ (eps / 6) ≤ Real.log X →
    X ^ ((9 : ℝ) / 10) ≤ ((PPset m0 a0 X).card : ℝ)

def Conclusion4b (x eps C : ℝ) : Prop :=
  ∀ m0 : ℕ, 0 < m0 → 8 ∣ m0 →
    (∀ p : ℕ, p.Prime → p ∣ m0 → (p : ℝ) ≤ x ^ (eps / 5) ∨ zz x < p) →
  ∀ a0 : ℤ, IsCoprime a0 (m0 : ℤ) → a0 % 4 = 3 →
  ∀ X : ℝ, 0 < X → (1 / 4) * Real.log x ^ 2 * Real.log m0 ≤ Real.log X →
    x ^ (eps / 6) ≤ Real.log X →
  ∀ ka : ℕ → ℂ, (∀ n, ‖ka n‖ ≤ 1) → ka 1 = 1 → (∀ a b, ka (a * b) = ka a * ka b) →
    (∑ q ∈ PPset m0 a0 X,
        ‖∑ n ∈ Finset.Icc 1 ⌊zz x⌋₊, (cn x n : ℂ) * ka n * kron (-(q : ℤ)) n‖ ^ 2) /
      ((PPset m0 a0 X).card : ℝ) ≤ C * x * Real.log x

theorem lemma_two_four_iff_both_claims (D : Formalism.BasicNotions.D7) (x eps C : ℝ) : Conclusion4 D x eps C ↔ Conclusion4a x eps ∧ Conclusion4b x eps C := by
  constructor
  · intro h
    refine ⟨fun m0 h1 h2 h3 a0 h4 h5 X h6 h7 h8 =>
      (h m0 h1 h2 h3 a0 h4 h5 X h6 h7 h8 (fun _ => 1) (by simp) rfl (by simp)).1,
      fun m0 h1 h2 h3 a0 h4 h5 X h6 h7 h8 ka k1 k2 k3 => (h m0 h1 h2 h3 a0 h4 h5 X h6 h7 h8 ka k1 k2 k3).2⟩
  · rintro ⟨ha, hb⟩ m0 h1 h2 h3 a0 h4 h5 X h6 h7 h8 ka k1 k2 k3
    exact ⟨ha m0 h1 h2 h3 a0 h4 h5 X h6 h7 h8, hb m0 h1 h2 h3 a0 h4 h5 X h6 h7 h8 ka k1 k2 k3⟩

def idQ (n : ℕ) : Ideal (NumberField.RingOfIntegers ℚ) := Ideal.span {(n : NumberField.RingOfIntegers ℚ)}

def RatDict : Prop :=
  ∀ m a : ℕ, 3 ≤ m → Nat.Coprime a m → CoprimeTo ℚ (idQ m) (idQ a) ∧ ∀ Y h : ℝ,
    nDeg1 ℚ (idQ m) (idQ a) Y h ≤
      ((Ioc ⌊Y⌋₊ ⌊Y * (1 + h)⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD m])).card

lemma absNorm_idQ (n : ℕ) : Ideal.absNorm (idQ n) = n := by
  unfold idQ
  rw [Ideal.absNorm_span_singleton]
  have e : (n : NumberField.RingOfIntegers ℚ) = algebraMap ℤ (NumberField.RingOfIntegers ℚ) (n : ℤ) := by simp
  rw [e, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
  simp

lemma Bmod_idQ (m : ℕ) : Bmod ℚ (idQ m) = 4 * (m : ℝ) := by
  unfold Bmod
  rw [absNorm_idQ, Rat.numberField_discr]
  simp

lemma idQ_ne_bot {m : ℕ} (h : m ≠ 0) : idQ m ≠ ⊥ := by
  intro hb
  have := absNorm_idQ m
  rw [hb] at this
  simp at this
  exact h this.symm

theorem primes_in_progressions_short_intervals {cQ C0 Cr cr c1 c2 : ℝ} (h : ShortIntervalLowerBound ℚ cQ C0 Cr cr c1 c2) (hd : RatDict) :
    Formalism.HermitianLattices.GL2PrimeSums.PrimesAPInterval C0 Cr cr c2 := by
  intro m a hm hcop Y hh hY hh1 hρ hB7
  obtain ⟨hco, hcount⟩ := hd m a hm hcop
  have hne : idQ m ≠ ⊥ := idQ_ne_bot (by omega)
  have key := (h (idQ m) hne Y (by rw [Bmod_idQ]; exact hY)).2 (idQ a) hco hh
    (by rw [Bmod_idQ, rhoErr_eq]; exact hρ) hh1 (by rw [Bmod_idQ]; exact hB7)
  rw [Bmod_idQ] at key
  exact key.trans (by exact_mod_cast hcount Y hh)

theorem first_claim_lemma_two_four_of_lemma_two_three {cQ C0 Cr cr c1 c2 : ℝ} (hC0 : 0 < C0) (hCr : 0 < Cr) (hcr : 0 < cr) (hc2 : 0 < c2)
    (h : ShortIntervalLowerBound ℚ cQ C0 Cr cr c1 c2) (hd : RatDict) (eps : ℝ) (he0 : 0 < eps) (he1 : eps < 1) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ x : ℝ, x0 ≤ x → Conclusion4a x eps := by
  obtain ⟨x₀, hx₀⟩ := Formalism.HermitianLattices.GL2PrimeSums.primesInProgressionCountLowerBound C0 Cr cr c2 hC0 hCr hcr hc2 (primes_in_progressions_short_intervals h hd) eps he0 he1
  refine ⟨max x₀ 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro x hx m0 hm0 h8 _ a0 hcop _ X hX h1 h2
  have hm3 : 3 ≤ m0 := by
    have := Nat.le_of_dvd hm0 h8
    omega
  have hm0z : (0 : ℤ) < (m0 : ℤ) := by exact_mod_cast hm0
  set a₀ : ℕ := (a0 % (m0 : ℤ)).toNat with ha₀
  have ha₀z : (a₀ : ℤ) = a0 % (m0 : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ hm0z.ne')
  have hcop' : Nat.Coprime a₀ m0 := by
    rw [← Nat.isCoprime_iff_coprime, ha₀z]
    have e : a0 % (m0 : ℤ) = a0 + (m0 : ℤ) * (-(a0 / (m0 : ℤ))) := by
      have := Int.emod_add_mul_ediv a0 (m0 : ℤ)
      linarith
    rw [e]
    exact (IsCoprime.add_mul_left_left_iff).2 hcop
  have key := hx₀ x ((le_max_left _ _).trans hx) m0 a₀ hm3 hcop' X hX h1 h2
  refine key.trans ?_
  have hsub : Formalism.HermitianLattices.GL2PrimeSums.PP m0 a₀ X ⊆ PPset m0 a0 X := by
    intro q hq
    unfold Formalism.HermitianLattices.GL2PrimeSums.PP at hq
    unfold PPset
    rw [Finset.mem_filter, Finset.mem_Ioc] at hq
    rw [Finset.mem_filter, Finset.mem_Icc]
    obtain ⟨⟨hq1, hq2⟩, hqp, hqa⟩ := hq
    refine ⟨⟨hqp.one_lt.le, hq2⟩, hqp, ?_, Nat.lt_of_floor_lt hq1⟩
    have h3 : (q : ℤ) ≡ (a₀ : ℤ) [ZMOD (m0 : ℤ)] := (Int.natCast_modEq_iff).2 hqa
    rw [ha₀z] at h3
    exact h3.trans (Int.mod_modEq a0 _)
  exact_mod_cast Finset.card_le_card hsub

local notation "OQ" => NumberField.RingOfIntegers ℚ

lemma exists_int (α : OQ) : ∃ z : ℤ, α = (z : OQ) :=
  ⟨Rat.ringOfIntegersEquiv α, ((Rat.ringOfIntegersEquiv.symm_apply_apply α).symm).trans
    (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* OQ) _)⟩

lemma absNorm_span_int (z : ℤ) : Ideal.absNorm (Ideal.span {(z : OQ)}) = z.natAbs := by
  rw [Ideal.absNorm_span_singleton]
  have e : (z : OQ) = algebraMap ℤ OQ z := by simp
  rw [e, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
  simp

lemma int_dvd_of_mem {m : ℕ} {z : ℤ} (h : (z : OQ) ∈ idQ m) : (m : ℤ) ∣ z := by
  unfold idQ at h
  rw [Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  obtain ⟨w, rfl⟩ := exists_int c
  refine ⟨w, ?_⟩
  have : ((z : ℤ) : OQ) = (((m : ℤ) * w : ℤ) : OQ) := by rw [hc]; push_cast; rfl
  exact Int.cast_injective this

lemma eq_idQ (I : Ideal OQ) (hI : I ≠ ⊥) : I = idQ (Ideal.absNorm I) := by
  have hle : idQ (Ideal.absNorm I) ≤ I := by
    unfold idQ
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.absNorm_mem I
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  have hn : Ideal.absNorm I ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hI
  have h1 := congrArg Ideal.absNorm hJ
  rw [absNorm_idQ, map_mul] at h1
  have h2 : Ideal.absNorm J = 1 := by
    have : Ideal.absNorm I * 1 = Ideal.absNorm I * Ideal.absNorm J := by rw [mul_one]; exact h1
    exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn) this).symm
  rw [Ideal.absNorm_eq_one_iff] at h2
  rw [hJ, h2, Ideal.mul_top]

lemma prime_absNorm (P : Ideal OQ) (hP : P.IsPrime) (h0 : P ≠ ⊥) : (Ideal.absNorm P).Prime := by
  have hn : Ideal.absNorm P ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h0
  have e := eq_idQ P h0
  rw [e] at hP
  unfold idQ at hP
  have hne : ((Ideal.absNorm P : ℕ) : OQ) ≠ 0 := by exact_mod_cast hn
  have hp := (Ideal.span_singleton_prime hne).1 hP
  have hp' := (MulEquiv.prime_iff (Rat.ringOfIntegersEquiv : OQ ≃* ℤ)).2 hp
  rw [Nat.prime_iff_prime_int]
  simpa using hp'

theorem deg2Bound_rat : Deg2Bound ℚ := by
  intro qq I0 Y hY
  have : {P : Ideal OQ | P.IsPrime ∧ CoprimeTo ℚ qq P ∧ RayRel ℚ qq P I0 ∧
      ¬ (Ideal.absNorm P).Prime ∧ (Ideal.absNorm P : ℝ) ≤ Y} = ∅ := by
    ext P
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2, -, h4, -⟩
    exact h4 (prime_absNorm P h1 h2.1)
  rw [this]
  simp only [Set.ncard_empty, Nat.cast_zero]
  positivity

lemma norm_modEq_one {m : ℕ} {α : OQ} (h1 : α - 1 ∈ idQ m) (hpos : 0 < (algebraMap ℚ ℝ) (α : ℚ)) :
    Ideal.absNorm (Ideal.span {α}) ≡ 1 [MOD m] := by
  obtain ⟨z, rfl⟩ := exists_int α
  have hz : 0 < z := by
    have : (algebraMap ℚ ℝ) (((z : OQ)) : ℚ) = (z : ℝ) := by simp
    rw [this] at hpos
    exact_mod_cast hpos
  have hd : (m : ℤ) ∣ z - 1 := int_dvd_of_mem (by push_cast; exact h1)
  rw [absNorm_span_int, ← Int.natCast_modEq_iff, Int.natCast_natAbs, abs_of_pos hz]
  exact (Int.modEq_iff_dvd.2 hd).symm

lemma absNorm_modEq_of_rayRel {m : ℕ} {I J : Ideal OQ} (h : RayRel ℚ (idQ m) I J) :
    Ideal.absNorm I ≡ Ideal.absNorm J [MOD m] := by
  obtain ⟨a, b, -, -, ha, hb, hpos, he⟩ := h
  have h1 := norm_modEq_one ha (hpos (algebraMap ℚ ℝ)).1
  have h2 := norm_modEq_one hb (hpos (algebraMap ℚ ℝ)).2
  have h3 := congrArg Ideal.absNorm he
  rw [map_mul, map_mul] at h3
  calc Ideal.absNorm I = 1 * Ideal.absNorm I := (one_mul _).symm
    _ ≡ Ideal.absNorm (Ideal.span {a}) * Ideal.absNorm I [MOD m] := (h1.symm).mul_right _
    _ = Ideal.absNorm (Ideal.span {b}) * Ideal.absNorm J := h3
    _ ≡ 1 * Ideal.absNorm J [MOD m] := h2.mul_right _
    _ = Ideal.absNorm J := one_mul _

theorem ratDict_holds : RatDict := by
  intro m a hm hcop
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hcop
    omega
  refine ⟨⟨idQ_ne_bot ha0, ?_⟩, ?_⟩
  · unfold idQ
    rw [← Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_span_singleton_iff]
    exact Nat.Coprime.cast hcop
  · intro Y h
    unfold nDeg1
    rw [← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard_of_injOn (fun P => Ideal.absNorm P) ?_ ?_ (Finset.finite_toSet _)
    · rintro P ⟨-, -, h3, h4, h5, h6⟩
      simp only [Finset.coe_filter, Finset.mem_Ioc, Set.mem_ofPred_eq]
      refine ⟨⟨(Nat.floor_lt' h4.ne_zero).2 h5, Nat.le_floor h6⟩, h4, ?_⟩
      have := absNorm_modEq_of_rayRel h3
      rwa [absNorm_idQ] at this
    · rintro P ⟨-, hP, -⟩ P' ⟨-, hP', -⟩ he
      simp only at he
      rw [eq_idQ P hP.1, eq_idQ P' hP'.1, he]

lemma mem_idQ_of_modEq {n m : ℕ} (h : n ≡ 1 [MOD m]) : ((n : ℕ) : OQ) - 1 ∈ idQ m := by
  have h1 : ((1 : ℕ) : ℤ) ≡ (n : ℤ) [ZMOD (m : ℤ)] := (Int.natCast_modEq_iff.2 h).symm
  obtain ⟨w, hw⟩ := Int.modEq_iff_dvd.1 h1
  unfold idQ
  rw [Ideal.mem_span_singleton]
  refine ⟨(w : OQ), ?_⟩
  have := congrArg (Int.cast : ℤ → OQ) hw
  push_cast at this
  exact this

lemma coprime_of_coprimeTo {m : ℕ} {I : Ideal OQ} (h : CoprimeTo ℚ (idQ m) I) :
    Nat.Coprime (Ideal.absNorm I) m := by
  have e := eq_idQ I h.1
  have h2 := h.2
  rw [e] at h2
  unfold idQ at h2
  rw [← Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_span_singleton_iff] at h2
  obtain ⟨u, v, huv⟩ := h2
  obtain ⟨u', rfl⟩ := exists_int u
  obtain ⟨v', rfl⟩ := exists_int v
  rw [← Nat.isCoprime_iff_coprime]
  refine ⟨u', v', ?_⟩
  have : ((u' * (Ideal.absNorm I : ℤ) + v' * (m : ℤ) : ℤ) : OQ) = ((1 : ℤ) : OQ) := by
    push_cast; exact huv
  exact Int.cast_injective this

lemma rayRel_of_modEq {m : ℕ} (hm : m ≠ 0) {I J : Ideal OQ} (hI : CoprimeTo ℚ (idQ m) I)
    (hJ : CoprimeTo ℚ (idQ m) J) (h : Ideal.absNorm I ≡ Ideal.absNorm J [MOD m]) : RayRel ℚ (idQ m) I J := by
  set i := Ideal.absNorm I with hi
  set j := Ideal.absNorm J with hj
  have hi0 : i ≠ 0 := by rw [hi, Ne, Ideal.absNorm_eq_zero_iff]; exact hI.1
  have hj0 : j ≠ 0 := by rw [hj, Ne, Ideal.absNorm_eq_zero_iff]; exact hJ.1
  obtain ⟨t, ht0, ht⟩ : ∃ t : ℕ, t ≠ 0 ∧ j * t ≡ 1 [MOD m] := by
    have : NeZero m := ⟨hm⟩
    refine ⟨((j : ZMod m)⁻¹).val + m, by omega, ?_⟩
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_self, add_zero]
    exact ZMod.coe_mul_inv_eq_one j (coprime_of_coprimeTo hJ)
  have ht' : i * t ≡ 1 [MOD m] := (h.mul_right t).trans ht
  have pos : ∀ (n : ℕ), n ≠ 0 → ∀ σ : ℚ →+* ℝ, 0 < σ (((n : ℕ) : OQ) : ℚ) := by
    intro n hn σ
    have : σ (((n : ℕ) : OQ) : ℚ) = (n : ℝ) := by simp
    rw [this]
    exact_mod_cast Nat.pos_of_ne_zero hn
  refine ⟨((j * t : ℕ) : OQ), ((i * t : ℕ) : OQ), ?_, ?_, mem_idQ_of_modEq ht, mem_idQ_of_modEq ht',
    fun σ => ⟨pos _ (mul_ne_zero hj0 ht0) σ, pos _ (mul_ne_zero hi0 ht0) σ⟩, ?_⟩
  · exact_mod_cast mul_ne_zero hj0 ht0
  · exact_mod_cast mul_ne_zero hi0 ht0
  · rw [eq_idQ I hI.1, eq_idQ J hJ.1, ← hi, ← hj]
    unfold idQ
    rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton]
    congr 2
    push_cast; ring

theorem grBound_rat : GrBound ℚ := by
  intro qq hqq
  have hm : Ideal.absNorm qq ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hqq
  obtain ⟨m, hmdef⟩ : ∃ m, m = Ideal.absNorm qq := ⟨_, rfl⟩
  rw [← hmdef] at hm
  have hq : qq = idQ m := by rw [hmdef]; exact eq_idQ qq hqq
  subst hq
  have : NeZero m := ⟨hm⟩
  let f : RayCls ℚ (idQ m) → ZMod m :=
    Quot.lift (fun I => ((Ideal.absNorm I.1 : ℕ) : ZMod m))
      (fun I J h => (ZMod.natCast_eq_natCast_iff _ _ _).2 (absNorm_modEq_of_rayRel h))
  have hf : Function.Injective f := by
    intro A B
    induction A using Quot.ind with
    | _ I =>
      induction B using Quot.ind with
      | _ J =>
        intro h
        exact Quot.sound (rayRel_of_modEq hm I.2 J.2 ((ZMod.natCast_eq_natCast_iff _ _ _).1 h))
  have : Finite (RayCls ℚ (idQ m)) := Finite.of_injective f hf
  have : Nonempty (RayCls ℚ (idQ m)) := ⟨Quot.mk _ ⟨⊤, ⟨top_ne_bot, by simp⟩⟩⟩
  have h1 : grCard ℚ (idQ m) ≤ m := by
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_zmod] at this
  refine ⟨Nat.card_pos, ?_⟩
  rw [Bmod_idQ]
  have : (grCard ℚ (idQ m) : ℝ) ≤ m := by exact_mod_cast h1
  have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

theorem lemma_two_three_of_Q4_field_bounds (C0 Cr cr cQ cQ' : ℝ) (hC0 : 0 < C0) (hCr : 0 < Cr) (hcr : 0 < cr) (hcQ : 0 < cQ)
    (hcQ' : 0 < cQ') :
    ∃ C0' c1 c2 : ℝ, 0 < C0' ∧ 0 < c1 ∧ 0 < c2 ∧ ∀ (D : Formalism.BasicNotions.D7) (c1' : ℝ), adm8 D C0 Cr cr cQ c1' →
      GrBound D.host.K → Deg2Bound D.host.K → PointsLemma D cQ' C0' Cr cr c1 c2 := by
  obtain ⟨C0', c1, c2, p1, p2, p3, h⟩ := lemma_two_three_of_Q4_both_fields C0 Cr cr cQ cQ' hC0 hCr hcr hcQ hcQ'
  exact ⟨C0', c1, c2, p1, p2, p3, fun D c1' ha hG hD => h D c1' ha grBound_rat deg2Bound_rat hG hD⟩

theorem lemma_two_three_rat_of_Q4 (C0 Cr cr cQ : ℝ) (hC0 : 0 < C0) (hCr : 0 < Cr) (hcr : 0 < cr) (hcQ : 0 < cQ) :
    ∃ C0' c2 : ℝ, 0 < C0' ∧ 0 < c2 ∧
      ∀ Comparison₂, SiegelZeroExceptionalCharacter ℚ Comparison₂ C0 Cr cr cQ → ShortIntervalLowerBound ℚ cQ C0' Cr cr (1 / 100) c2 := by
  obtain ⟨C0', c, h0, hc, hii⟩ := lemma_two_three_second_of_Q4 C0 Cr cr cQ hC0 hCr hcr hcQ
  refine ⟨max C0' (max 60 (2 / cQ)), c, by positivity, hc, ?_⟩
  intro Comparison₂ hQ qq hqq X hX
  have a1 : C0' ≤ max C0' (max 60 (2 / cQ)) := le_max_left _ _
  have a2 : 60 ≤ max C0' (max 60 (2 / cQ)) := (le_max_left _ _).trans (le_max_right _ _)
  have a3 : 2 / cQ ≤ max C0' (max 60 (2 / cQ)) := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨fun be th hth hb1 hb2 hb3 => lemma_two_three_first_Li_lower_bound hcQ a2 a3 hqq hX be th hth hb1 hb2 hb3, ?_⟩
  have hB := Bmod_ge hqq
  exact hii ℚ Comparison₂ hQ grBound_rat deg2Bound_rat qq hqq X
    ((Real.rpow_le_rpow_of_exponent_le (by linarith) a1).trans hX)

theorem first_claim_lemma_two_four_of_Q4 (C0 Cr cr cQ : ℝ) (hC0 : 0 < C0) (hCr : 0 < Cr) (hcr : 0 < cr) (hcQ : 0 < cQ)
    (eps : ℝ) (he0 : 0 < eps) (he1 : eps < 1) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ (D : Formalism.BasicNotions.D7) (c1' : ℝ), adm8 D C0 Cr cr cQ c1' → ∀ x : ℝ, x0 ≤ x → Conclusion4a x eps := by
  obtain ⟨C0', c2, p1, p2, h⟩ := lemma_two_three_rat_of_Q4 C0 Cr cr cQ hC0 hCr hcr hcQ
  by_cases hex : ∃ Comparison₂, SiegelZeroExceptionalCharacter ℚ Comparison₂ C0 Cr cr cQ
  · obtain ⟨Comparison₂, hT⟩ := hex
    obtain ⟨x0, hx0, hx⟩ := first_claim_lemma_two_four_of_lemma_two_three p1 hCr hcr p2 (h Comparison₂ hT) ratDict_holds eps he0 he1
    exact ⟨x0, hx0, fun _ _ _ x hxx => hx x hxx⟩
  · exact ⟨2, by norm_num, fun D c1' ha => absurd ⟨_, ha.1⟩ hex⟩

theorem lemma_two_three_family_of_Q4_field_bounds {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h8 : FamilyTemperatureAsymptotic Fm)
    (hK : ∀ x > 1, ∀ i : Fm.Ix x, GrBound (Fm.D x i).host.K ∧ Deg2Bound (Fm.D x i).host.K) : Conclusion3Family Fm :=
  lemma_two_three_of_siegel_bound Fm h8 grBound_rat deg2Bound_rat hK

theorem first_claim_lemma_two_four_family {eps : ℝ} (he0 : 0 < eps) (he1 : eps < 1) (Fm : Formalism.MainNotions.FamP eps) (h8 : FamilyTemperatureAsymptotic Fm) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ x ≥ x0, ∀ _i : Fm.Ix x, Conclusion4a x eps := by
  obtain ⟨C0, Cr, cr, cQ, c1', hC0, hCr, hcr, hcQ, -, h⟩ := h8
  obtain ⟨x0, hx0, hx⟩ := first_claim_lemma_two_four_of_Q4 C0 Cr cr cQ hC0 hCr hcr hcQ eps he0 he1
  exact ⟨x0, hx0, fun x hxx i => hx _ c1' (h x (lt_of_lt_of_le hx0 hxx) i) x hxx⟩

theorem lemma_two_four_family_of_Q4_mean_square {eps : ℝ} (he0 : 0 < eps) (he1 : eps < 1) (Fm : Formalism.MainNotions.FamP eps) (h8 : FamilyTemperatureAsymptotic Fm)
    (hb : ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧ ∀ x ≥ x0, ∀ _i : Fm.Ix x, Conclusion4b x eps C) : SlopeLemmaFamily Fm := by
  obtain ⟨xa, hxa, ha⟩ := first_claim_lemma_two_four_family he0 he1 Fm h8
  obtain ⟨C, hC, xb, hxb, hb⟩ := hb
  exact ⟨C, hC, max xa xb, lt_of_lt_of_le hxa (le_max_left _ _), fun x hx i =>
    (lemma_two_four_iff_both_claims _ x eps C).2 ⟨ha x ((le_max_left _ _).trans hx) i, hb x ((le_max_right _ _).trans hx) i⟩⟩

end Formalism.MainNotions.ShortIntervalPrimes

end

noncomputable section

namespace Formalism.MainNotions.ShortIntervalPrimes

open NumberField

section Deg2

variable {K0 : Type} [Field K0] [NumberField K0]

lemma exists_prime_mem {P : Ideal (𝓞 K0)} (hP : P.IsPrime) (h0 : P ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 K0) ∈ P := by
  have := hP
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 K0 ⧸ P)
  have := hp
  have hmem : ((p : ℕ) : 𝓞 K0) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero (𝓞 K0 ⧸ P) p
  rcases CharP.char_is_prime_or_zero (𝓞 K0 ⧸ P) p with h | h
  · exact ⟨p, h, hmem⟩
  · exfalso
    have hn : ((Ideal.absNorm P : ℕ) : 𝓞 K0 ⧸ P) = 0 := by
      have := Ideal.absNorm_mem P
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast] at this
      exact this
    rw [CharP.cast_eq_zero_iff (𝓞 K0 ⧸ P) p, h, zero_dvd_iff, Ideal.absNorm_eq_zero_iff] at hn
    exact h0 hn

lemma absNorm_natCast (h : Module.finrank ℚ K0 = 2) (p : ℕ) :
    Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K0)}) = p ^ 2 := by
  rw [Ideal.absNorm_span_singleton]
  have e : ((p : ℕ) : 𝓞 K0) = algebraMap ℤ (𝓞 K0) (p : ℤ) := by simp
  rw [e, Algebra.norm_algebraMap_of_basis (NumberField.RingOfIntegers.basis K0),
    ← Module.finrank_eq_card_chooseBasisIndex, NumberField.RingOfIntegers.rank, h]
  simp [Int.natAbs_pow]

theorem deg2Bound_of_absNorm (h : ∀ p : ℕ, Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K0)}) = p ^ 2) :
    Deg2Bound K0 := by
  intro qq I0 Y hY
  have hsub : {P : Ideal (𝓞 K0) | P.IsPrime ∧ CoprimeTo K0 qq P ∧ RayRel K0 qq P I0 ∧
      ¬ (Ideal.absNorm P).Prime ∧ (Ideal.absNorm P : ℝ) ≤ Y} ⊆
      (fun p : ℕ => Ideal.span {((p : ℕ) : 𝓞 K0)}) '' (Finset.Icc 1 ⌊Real.sqrt Y⌋₊ : Set ℕ) := by
    rintro P ⟨hP, hc, -, hnp, hle⟩
    obtain ⟨p, hp, hmem⟩ := exists_prime_mem hP hc.1
    have hle' : Ideal.span {((p : ℕ) : 𝓞 K0)} ≤ P := (Ideal.span_singleton_le_iff_mem _).2 hmem
    have hdvd : Ideal.absNorm P ∣ p ^ 2 := by
      rw [← h p]; exact Ideal.absNorm_dvd_absNorm_of_le hle'
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hk2 : k = 2 := by
      interval_cases k
      · exfalso; rw [pow_zero, Ideal.absNorm_eq_one_iff] at hkeq; exact hP.ne_top hkeq
      · exfalso; rw [pow_one] at hkeq; exact hnp (hkeq ▸ hp)
      · rfl
    subst hk2
    have heq : Ideal.span {((p : ℕ) : 𝓞 K0)} = P := by
      obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle'
      have h1 := congrArg Ideal.absNorm hJ
      rw [h p, map_mul, hkeq] at h1
      have hpos : 0 < p ^ 2 := pow_pos hp.pos 2
      have hJ1 : Ideal.absNorm J = 1 := Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_one]; exact h1.symm)
      rw [Ideal.absNorm_eq_one_iff] at hJ1
      rw [hJ, hJ1, Ideal.mul_top]
    refine ⟨p, ?_, heq⟩
    simp only [Finset.coe_Icc, Set.mem_Icc]
    refine ⟨hp.one_le, Nat.le_floor ?_⟩
    apply Real.le_sqrt_of_sq_le
    rw [hkeq] at hle
    exact_mod_cast hle
  have hcard := (Set.ncard_le_ncard hsub ((Finset.finite_toSet _).image _)).trans
    (Set.ncard_image_le (Finset.finite_toSet _))
  rw [Set.ncard_coe_finset, Nat.card_Icc, Nat.add_sub_cancel] at hcard
  calc _ ≤ ((⌊Real.sqrt Y⌋₊ : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ Real.sqrt Y := Nat.floor_le (Real.sqrt_nonneg _)
    _ ≤ 2 * Real.sqrt Y := by linarith [Real.sqrt_nonneg Y]

theorem deg2Bound_of_finrank (h : Module.finrank ℚ K0 = 2) : Deg2Bound K0 :=
  deg2Bound_of_absNorm (absNorm_natCast h)

end Deg2

theorem deg2Bound_K (D : Formalism.BasicNotions.D7) : Deg2Bound D.host.K :=
  deg2Bound_of_absNorm (Formalism.MainNotions.UnusedSlot33.HK.absNorm_natK D.host)

end Formalism.MainNotions.ShortIntervalPrimes

end

noncomputable section

namespace Formalism.MainNotions.ShortIntervalPrimes

open Finset Filter Topology ArithmeticFunction MeasureTheory Formalism.MainNotions.GlobalTheoryTheory
open Br

def lamE (D : Formalism.BasicNotions.D7) : ℝ := max 1 (Real.log (NE D))

def PsiThin (D : Formalism.BasicNotions.D7) (x eps C c : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), IsCharED D χ →
    ∀ u : ℝ, Real.exp (x ^ (eps / 3)) / 3 ≤ u → ‖psi0 χ u‖ ≤
      C * u * (Real.log u + lamE D) ^ 2 * Real.exp (-c * Real.log u / (lamE D + Real.sqrt (Real.log u)))

def ThinE (D : Formalism.BasicNotions.D7) (x eps c : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), IsCharED D χ →
    ∀ y : ℝ, Real.exp (x ^ (eps / 3)) / 3 ≤ y → ‖gChi χ y‖ ≤ y * Real.exp (-(c * x ^ (eps / 8)))

theorem log_conductor_le_of_proposition_two_six {D : Formalism.BasicNotions.D7} {x eps : ℝ} (hx : 0 ≤ x) (h5 : PropTwoSixBoxHypothesis D x eps) :
    Real.log (NE D : ℝ) ≤ 8 * x ^ (eps / 5) * Real.log x ^ 2 := by
  have h1 := h5.2
  have h2 : 0 ≤ x ^ (eps / 5) * Real.log x ^ 2 := by positivity
  linarith

theorem thin_of_psiThin (eps c C : ℝ) (heps : 0 < eps) (hc : 0 < c) (hC : 0 < C) :
    ∃ c' x0 : ℝ, 0 < c' ∧ 1 < x0 ∧ ∀ x : ℝ, x0 ≤ x → ∀ D : Formalism.BasicNotions.D7,
      Real.log (NE D : ℝ) ≤ 8 * x ^ (eps / 5) * Real.log x ^ 2 → PsiThin D x eps C c → ThinE D x eps c' := by
  obtain ⟨c', x₀, hc', h⟩ := Formalism.HermitianLattices.ZeroFreeRegionGL2.nonvanishing_of_hypothesis (eps / 2) c C (by positivity) hc hC
  refine ⟨c', max x₀ (max 3 (2 ^ (3 / eps))), hc', lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans (le_max_right _ _)), ?_⟩
  intro x hx D hlast hpsi N _ χ hχ y hy
  have hx0 : x₀ ≤ x := (le_max_left _ _).trans hx
  have hx3 : 3 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hx2 : (2 : ℝ) ^ (3 / eps) ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hxpos : 0 < x := by linarith
  have hp2 : 2 ≤ x ^ (eps / 3) := by
    have h1 : ((2 : ℝ) ^ (3 / eps)) ^ (eps / 3) ≤ x ^ (eps / 3) :=
      Real.rpow_le_rpow (by positivity) hx2 (by positivity)
    rw [← Real.rpow_mul (by norm_num)] at h1
    have e : 3 / eps * (eps / 3) = 1 := by field_simp
    rwa [e, Real.rpow_one] at h1
  have hy1 : 1 ≤ y := by
    have h1 : x ^ (eps / 3) + 1 ≤ Real.exp (x ^ (eps / 3)) := Real.add_one_le_exp _
    linarith
  have hlogx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hxpos]
    have := Real.exp_one_lt_d9
    linarith
  have hlam : lamE D ≤ 8 * x ^ (eps / 5) * Real.log x ^ 2 := by
    unfold lamE
    apply max_le
    · have h1 : 1 ≤ x ^ (eps / 5) := Real.one_le_rpow (by linarith) (by positivity)
      have h2 : 1 ≤ Real.log x ^ 2 := by nlinarith
      nlinarith
    · exact hlast
  have hsq : ∀ a : ℝ, (x ^ (2 : ℝ)) ^ (eps / 2 / a) = x ^ (eps / a) := by
    intro a
    rw [← Real.rpow_mul hxpos.le]
    congr 1
    ring
  have hxx : x₀ ≤ x ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    nlinarith
  have key := h (x ^ (2 : ℝ)) hxx y (lamE D) (psi0 χ) (by rw [hsq]; exact hy) (le_max_left _ _)
    (by rw [hsq, Real.log_rpow hxpos]; linarith)
    (fun u hu => hpsi N χ hχ u (hy.trans hu))
  rw [(l21a χ hχ.1 y hy1).2, neg_mul, norm_neg]
  rw [neg_mul, hsq] at key
  exact key

theorem proposition_six_of_psi_thin (eps c C : ℝ) (heps : 0 < eps) (hc : 0 < c) (hC : 0 < C) :
    ∃ c' x0 : ℝ, 0 < c' ∧ 1 < x0 ∧ ∀ x : ℝ, x0 ≤ x → ∀ D : Formalism.BasicNotions.D7, PsiThin D x eps C c →
      PropTwoSixThinScales D x eps c' := by
  obtain ⟨c', x0, hc', hx0, h⟩ := thin_of_psiThin eps c C heps hc hC
  exact ⟨c', x0, hc', hx0, fun x hx D hpsi h5 => h x hx D (log_conductor_le_of_proposition_two_six (by linarith) h5) hpsi⟩

theorem proposition_six_family_of_psi_thin {eps : ℝ} (heps : 0 < eps) (Fm : Formalism.MainNotions.FamP eps)
    (h : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, PsiThin (Fm.D x i) x eps C c) :
    FamilyPropTwoSixCongruenceForm Fm := by
  obtain ⟨C, c, hC, hc, x1, h1⟩ := h
  obtain ⟨c', x0, hc', hx0, h0⟩ := proposition_six_of_psi_thin eps c C heps hc hC
  exact ⟨c', hc', max x0 x1, lt_of_lt_of_le hx0 (le_max_left _ _),
    fun x hx i => h0 x ((le_max_left _ _).trans hx) _ (h1 x ((le_max_right _ _).trans hx) i)⟩

end Formalism.MainNotions.ShortIntervalPrimes

end

noncomputable section

namespace Formalism.MainNotions.ShortIntervalPrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Filter Topology

theorem rpow_le_mul_exp_neg_log {u v r k : ℝ} (hu0 : 0 < u) (hv : v = Real.log u) (hv0 : 0 ≤ v) (hr : r ≤ 1 - k) :
    u ^ r ≤ u * Real.exp (-k * v) := by
  have hu : u = Real.exp v := by rw [hv, Real.exp_log hu0]
  rw [Real.rpow_def_of_pos hu0, ← hv]
  calc Real.exp (v * r) ≤ Real.exp (v + -k * v) := Real.exp_le_exp.2 (by nlinarith)
    _ = Real.exp v * Real.exp (-k * v) := Real.exp_add _ _
    _ = u * Real.exp (-k * v) := by rw [← hu]

set_option maxHeartbeats 1000000 in

theorem psi_thin_core {C7 C2 c lam : ℝ} (hC7 : 0 < C7) (hC2 : 0 ≤ C2) (hc : 0 < c) (hlam : 1 ≤ lam) (D : D7)
    (h7 : adm7 D C7) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive)
    (hN : Real.log N ≤ lam)
    (hzf : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → DirichletCharacter.LFunction χ ρ = 0 →
      ρ.re ≤ 1 - c / (lam + Real.log (|ρ.im| + 3)))
    (hZ : ∀ T : ℝ, 1 ≤ T → ∑ᶠ ρ ∈ ZerosBelow χ T, (zOrd χ ρ : ℝ) / ‖ρ‖ ≤ C2 * (lam + Real.log T) ^ 2)
    (u : ℝ) (hu : Real.exp 1 ≤ u) :
    ‖psi0 χ u‖ ≤ (C7 * (5 + C2) + C2) * u * (Real.log u + lam) ^ 2 *
      Real.exp (-(min (c / 3) 1) * Real.log u / (lam + Real.sqrt (Real.log u))) := by
  have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos 1) hu
  set v : ℝ := Real.log u with hv
  have hv1 : 1 ≤ v := by rw [hv, Real.le_log_iff_exp_le hu0]; exact hu
  set s : ℝ := Real.sqrt v with hs
  have hss : s * s = v := Real.mul_self_sqrt (by linarith)
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.2 hv1
  have hsv : s ≤ v := by nlinarith
  set c' : ℝ := min (c / 3) 1 with hc'
  have hc'0 : 0 < c' := lt_min (by positivity) one_pos
  have hc'1 : c' ≤ 1 := min_le_right _ _
  have hc'3 : c' ≤ c / 3 := min_le_left _ _
  have hls : 0 < lam + s := by linarith
  set E : ℝ := Real.exp (-c' * v / (lam + s)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set T : ℝ := Real.exp s with hT
  have hT2 : 2 ≤ T := by have := Real.add_one_le_exp s; linarith
  have huv : u = Real.exp v := (Real.exp_log hu0).symm
  have hTu : T ≤ u := by rw [huv]; exact Real.exp_le_exp.2 hsv
  have hT0 : 0 < T := Real.exp_pos _
  have hlT : Real.log T = s := Real.log_exp s
  set W : ℝ := v + lam with hW
  have hW2 : 2 ≤ W := by linarith
  set P : ℝ := u * E with hP
  have hP0 : 0 < P := by positivity
  have q0 : c' * v / (lam + s) ≤ v := by
    rw [div_le_iff₀ hls]; nlinarith
  have q1 : c' * v / (lam + s) ≤ s := by
    rw [div_le_iff₀ hls]; nlinarith
  have hP1 : 1 ≤ P := by
    rw [hP, huv, hE, ← Real.exp_add]
    apply Real.one_le_exp
    have : -c' * v / (lam + s) = -(c' * v / (lam + s)) := by ring
    rw [this]; linarith
  have hTE : T⁻¹ ≤ E := by
    rw [hT, ← Real.exp_neg, hE]
    apply Real.exp_le_exp.2
    have : -c' * v / (lam + s) = -(c' * v / (lam + s)) := by ring
    rw [this]; linarith
  obtain ⟨hfin, hexp⟩ := h7 N χ hp u T hT2 hTu
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hN0 : (0 : ℝ) < N := by linarith
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have l1 : Real.log (N * u * T) = Real.log N + v + s := by
    rw [Real.log_mul (by positivity) hT0.ne', Real.log_mul hN0.ne' hu0.ne', hlT]
  have l2 : Real.log (N * u) = Real.log N + v := Real.log_mul hN0.ne' hu0.ne'
  have hW0 : 0 ≤ W ^ 2 := by positivity
  have hWW : W ≤ W ^ 2 := by nlinarith
  have hWP : W ^ 2 ≤ W ^ 2 * P := by nlinarith
  have e1 : u * Real.log (N * u * T) ^ 2 / T ≤ 4 * W ^ 2 * P := by
    have a1 : Real.log (N * u * T) ^ 2 ≤ (2 * W) ^ 2 := by
      rw [l1]; apply pow_le_pow_left₀ (by linarith); linarith
    calc u * Real.log (N * u * T) ^ 2 / T = u * T⁻¹ * Real.log (N * u * T) ^ 2 := by
          rw [div_eq_mul_inv]; ring
      _ ≤ u * E * (2 * W) ^ 2 := by gcongr
      _ = 4 * W ^ 2 * P := by rw [hP]; ring
  have e2 : Real.log (N * u) ≤ W ^ 2 * P := by
    rw [l2]; exact (by linarith : Real.log N + v ≤ W).trans (hWW.trans hWP)
  have e3 : ∑ᶠ ρ ∈ ZerosBelow χ 1, (zOrd χ ρ : ℝ) / ‖ρ‖ ≤ C2 * W ^ 2 * P := by
    refine (hZ 1 le_rfl).trans ?_
    rw [Real.log_one, add_zero]
    have : lam ^ 2 ≤ W ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    calc C2 * lam ^ 2 ≤ C2 * (W ^ 2 * P) := mul_le_mul_of_nonneg_left (this.trans hWP) hC2
      _ = C2 * W ^ 2 * P := by ring
  have hl4 : Real.log 4 ≤ 2 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  have hterm : ∀ ρ ∈ hfin.toFinset,
      ‖(zOrd χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ P * ((zOrd χ ρ : ℝ) / ‖ρ‖) := by
    intro ρ hρ
    obtain ⟨r0, r1, r2, r3⟩ : ρ ∈ ZerosBelow χ T := hfin.mem_toFinset.mp hρ
    have hre := hzf ρ r0 r1 r3
    have hg0 : 0 ≤ |ρ.im| := abs_nonneg _
    have hlg0 : 0 ≤ Real.log (|ρ.im| + 3) := Real.log_nonneg (by linarith)
    have hlg : Real.log (|ρ.im| + 3) ≤ s + 2 := by
      have : Real.log (|ρ.im| + 3) ≤ Real.log (4 * T) := Real.log_le_log (by linarith) (by linarith)
      rw [Real.log_mul (by norm_num) hT0.ne', hlT] at this
      linarith
    have hden : 0 < lam + Real.log (|ρ.im| + 3) := by linarith
    have hcmp : c' / (lam + s) ≤ c / (lam + Real.log (|ρ.im| + 3)) := by
      rw [div_le_div_iff₀ hls hden]
      have h1 : c' * (lam + Real.log (|ρ.im| + 3)) ≤ c / 3 * (3 * (lam + s)) :=
        mul_le_mul hc'3 (by linarith) hden.le (by positivity)
      linarith
    have hle : u ^ ρ.re ≤ P := by
      have h3 : ρ.re ≤ 1 - c' / (lam + s) := by linarith
      have h4 := rpow_le_mul_exp_neg_log hu0 hv (by linarith) h3
      have h2 : -c' * v / (lam + s) = -(c' / (lam + s)) * v := by ring
      rw [hP, hE, h2]
      exact h4
    rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    calc (zOrd χ ρ : ℝ) * (u ^ ρ.re / ‖ρ‖) ≤ (zOrd χ ρ : ℝ) * (P / ‖ρ‖) := by gcongr
      _ = P * ((zOrd χ ρ : ℝ) / ‖ρ‖) := by ring
  have e4 : ‖∑ᶠ ρ ∈ ZerosBelow χ T, (zOrd χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ P * (C2 * W ^ 2) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [← Finset.mul_sum, ← finsum_mem_eq_finite_toFinset_sum _ hfin]
    apply mul_le_mul_of_nonneg_left _ hP0.le
    refine (hZ T (by linarith)).trans (mul_le_mul_of_nonneg_left ?_ hC2)
    rw [hlT]
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  calc ‖psi0 χ u‖
      = ‖(psi0 χ u + ∑ᶠ ρ ∈ ZerosBelow χ T, (zOrd χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)) -
          ∑ᶠ ρ ∈ ZerosBelow χ T, (zOrd χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ := by
        rw [add_sub_cancel_right]
    _ ≤ ‖psi0 χ u + ∑ᶠ ρ ∈ ZerosBelow χ T, (zOrd χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ +
          ‖∑ᶠ ρ ∈ ZerosBelow χ T, (zOrd χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ := norm_sub_le _ _
    _ ≤ C7 * (4 * W ^ 2 * P + W ^ 2 * P + C2 * W ^ 2 * P) + P * (C2 * W ^ 2) := by
        refine add_le_add (hexp.trans ?_) e4
        exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add e1 e2) e3) hC7.le
    _ = (C7 * (5 + C2) + C2) * u * W ^ 2 * E := by rw [hP]; ring

def ZeroFreeE (D : D7) (c : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), IsCharED D χ → ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 →
    DirichletCharacter.LFunction χ ρ = 0 → ρ.re ≤ 1 - c / (lamE D + Real.log (|ρ.im| + 3))

def CondE (D : D7) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), IsCharED D χ → (N : ℝ) ≤ NE D

def ZeroSumE (D : D7) (C2 : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), IsCharED D χ → ∀ T : ℝ, 1 ≤ T →
    ∑ᶠ ρ ∈ ZerosBelow χ T, (zOrd χ ρ : ℝ) / ‖ρ‖ ≤ C2 * (lamE D + Real.log T) ^ 2

theorem log_cond_le {D : D7} (hC : CondE D) {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (h : IsCharED D χ) :
    Real.log N ≤ lamE D := by
  have hN1 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  exact (Real.log_le_log hN1 (hC N χ h)).trans (le_max_right _ _)

theorem psiThin_of {C7 C2 c : ℝ} (hC7 : 0 < C7) (hC2 : 0 ≤ C2) (hc : 0 < c) (D : D7) (h7 : adm7 D C7)
    (hzf : ZeroFreeE D c) (hcond : CondE D) (hZ : ZeroSumE D C2) (x eps : ℝ) (hx : 3 ≤ x ^ (eps / 3)) :
    PsiThin D x eps (C7 * (5 + C2) + C2) (min (c / 3) 1) := by
  intro N _ χ hχ u hu
  have hu1 : Real.exp 1 ≤ u := by
    refine le_trans ?_ hu
    have h1 : Real.exp 3 ≤ Real.exp (x ^ (eps / 3)) := Real.exp_le_exp.2 hx
    have h2 : Real.exp 3 = Real.exp 1 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
    have h3 : (3 : ℝ) ≤ Real.exp 2 := by have := Real.add_one_le_exp (2 : ℝ); linarith
    have h4 := Real.exp_pos 1
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  exact psi_thin_core hC7 hC2 hc (le_max_left _ _) D h7 χ hχ.1 (log_cond_le hcond hχ)
    (fun ρ h0 h1 hz => hzf N χ hχ ρ h0 h1 hz) (fun T hT => hZ N χ hχ T hT) u hu1

set_option maxHeartbeats 1000000 in

theorem zero_sum_core {C7 C lam ka : ℝ} (hC : 0 < C) (hlam : 1 ≤ lam) (hka : 0 < ka) (D : D7)
    (h7 : adm7 D C7) (h11 : adm11 D C) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive)
    (hN : Real.log N ≤ lam)
    (hlow : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ 2 → DirichletCharacter.LFunction χ ρ = 0 → ka / lam ≤ ρ.re)
    (T : ℝ) (hT : 1 ≤ T) :
    ∑ᶠ ρ ∈ ZerosBelow χ T, (zOrd χ ρ : ℝ) / ‖ρ‖ ≤ 6 * C * (3 / ka + 4) * (lam + Real.log T) ^ 2 := by
  classical
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hN0 : (0 : ℝ) < N := by linarith
  have hfin : (ZerosBelow χ T).Finite := by
    refine (h7 N χ hp (max T 2) (max T 2) (le_max_right _ _) le_rfl).1.subset ?_
    rintro ρ ⟨r0, r1, r2, r3⟩
    exact ⟨r0, r1, lt_of_lt_of_le r2 (le_max_left _ _), r3⟩
  set M : ℕ := ⌊T⌋₊ with hM
  have hMT : (M : ℝ) ≤ T := Nat.floor_le (by linarith)
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hlT : 0 ≤ Real.log T := Real.log_nonneg hT
  set Y : ℝ := lam + Real.log T with hY
  have hY1 : 1 ≤ Y := by linarith
  set La : ℝ := lam + Real.log ((M : ℝ) + 2) with hLa
  have hl2 := Real.log_two_lt_d9
  have hl3 : Real.log 3 ≤ 2 := by
    have h1 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  have hLa0 : 0 ≤ La := by
    have : 0 ≤ Real.log ((M : ℝ) + 2) := Real.log_nonneg (by linarith)
    linarith
  have hLa3 : La ≤ 3 * Y := by
    have h1 : Real.log ((M : ℝ) + 2) ≤ Real.log (3 * T) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    linarith
  have hLM : Real.log ((M + 1 : ℕ) : ℝ) ≤ 1 + Real.log T := by
    have h1 : Real.log ((M + 1 : ℕ) : ℝ) ≤ Real.log (2 * T) := by
      apply Real.log_le_log (by positivity)
      push_cast
      linarith
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    linarith
  have hwin : ∀ i : ℕ, i ≤ M → ∀ t : ℝ, |t| = i →
      ∑ ρ ∈ (h11 N χ hp t).1.toFinset, (zOrd χ ρ : ℝ) ≤ C * La := by
    intro i hi t ht
    have h := (h11 N χ hp t).2
    rw [finsum_mem_eq_finite_toFinset_sum _ (h11 N χ hp t).1] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hC.le)
    rw [ht, Real.log_mul hN0.ne' (by positivity), hLa]
    have : (i : ℝ) ≤ M := by exact_mod_cast hi
    have h2 : Real.log ((i : ℝ) + 2) ≤ Real.log ((M : ℝ) + 2) := Real.log_le_log (by positivity) (by linarith)
    linarith
  set a : ℕ → ℝ := fun i => (if i ≤ 2 then lam / ka else 0) + 2 * (1 / ((i : ℝ) + 1)) with ha
  have ha0 : ∀ i, 0 ≤ a i := by
    intro i
    simp only [ha]
    split_ifs <;> positivity
  have hfib : ∀ i ∈ Finset.range (M + 1),
      ∑ ρ ∈ hfin.toFinset with ⌊|ρ.im|⌋₊ = i, (zOrd χ ρ : ℝ) / ‖ρ‖ ≤ a i * (2 * (C * La)) := by
    intro i hi
    have hiM : i ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hi0 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have st1 : ∑ ρ ∈ hfin.toFinset with ⌊|ρ.im|⌋₊ = i, (zOrd χ ρ : ℝ) / ‖ρ‖ ≤
        ∑ ρ ∈ hfin.toFinset with ⌊|ρ.im|⌋₊ = i, a i * (zOrd χ ρ : ℝ) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      obtain ⟨hρF, hρi⟩ := Finset.mem_filter.mp hρ
      obtain ⟨r0, r1, r2, r3⟩ : ρ ∈ ZerosBelow χ T := hfin.mem_toFinset.mp hρF
      have hile : (i : ℝ) ≤ |ρ.im| := by rw [← hρi]; exact Nat.floor_le (abs_nonneg _)
      have hpos : 0 < ‖ρ‖ := lt_of_lt_of_le r0 ((le_abs_self ρ.re).trans (Complex.abs_re_le_norm ρ))
      have h1 : 1 ≤ a i * ‖ρ‖ := by
        rcases le_total |ρ.im| 2 with h2 | h2
        · have hre := hlow ρ r0 r1 h2 r3
          have h3 := (le_abs_self ρ.re).trans (Complex.abs_re_le_norm ρ)
          have hi2 : i ≤ 2 := by
            have : (i : ℝ) ≤ 2 := hile.trans h2
            exact_mod_cast this
          have h4 : lam / ka ≤ a i := by
            simp only [ha, if_pos hi2]
            have : 0 ≤ 2 * (1 / ((i : ℝ) + 1)) := by positivity
            linarith
          calc (1 : ℝ) = lam / ka * (ka / lam) := by field_simp
            _ ≤ a i * ‖ρ‖ := mul_le_mul h4 (hre.trans h3) (by positivity) (ha0 i)
        · have h3 := Complex.abs_im_le_norm ρ
          have hlt : |ρ.im| < (i : ℝ) + 1 := by rw [← hρi]; exact Nat.lt_floor_add_one _
          have h4 : 2 * (1 / ((i : ℝ) + 1)) ≤ a i := by
            simp only [ha]
            split_ifs
            · have : 0 ≤ lam / ka := by positivity
              linarith
            · linarith
          have h5 : ((i : ℝ) + 1) / 2 ≤ ‖ρ‖ := by linarith
          calc (1 : ℝ) = 2 * (1 / ((i : ℝ) + 1)) * (((i : ℝ) + 1) / 2) := by field_simp
            _ ≤ a i * ‖ρ‖ := mul_le_mul h4 h5 (by positivity) (ha0 i)
      rw [div_le_iff₀ hpos]
      calc (zOrd χ ρ : ℝ) = (zOrd χ ρ : ℝ) * 1 := (mul_one _).symm
        _ ≤ (zOrd χ ρ : ℝ) * (a i * ‖ρ‖) := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
        _ = a i * (zOrd χ ρ : ℝ) * ‖ρ‖ := by ring
    refine st1.trans ?_
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (ha0 i)
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun ρ : ℂ => 0 ≤ ρ.im), two_mul]
    apply add_le_add
    · refine le_trans ?_ (hwin i hiM (i : ℝ) (Nat.abs_cast i))
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro ρ hρ
        obtain ⟨hρ1, hs⟩ := Finset.mem_filter.mp hρ
        obtain ⟨hρF, hρi⟩ := Finset.mem_filter.mp hρ1
        obtain ⟨r0, r1, r2, r3⟩ : ρ ∈ ZerosBelow χ T := hfin.mem_toFinset.mp hρF
        rw [Set.Finite.mem_toFinset]
        refine ⟨r0, r1, ?_, r3⟩
        have a1 : (i : ℝ) ≤ |ρ.im| := by rw [← hρi]; exact Nat.floor_le (abs_nonneg _)
        have a2 : |ρ.im| < (i : ℝ) + 1 := by rw [← hρi]; exact Nat.lt_floor_add_one _
        rw [abs_of_nonneg hs] at a1 a2
        rw [abs_le]
        constructor <;> linarith
      · intro ρ _ _
        exact Nat.cast_nonneg _
    · refine le_trans ?_ (hwin i hiM (-(i : ℝ)) (by rw [abs_neg, Nat.abs_cast]))
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro ρ hρ
        obtain ⟨hρ1, hs⟩ := Finset.mem_filter.mp hρ
        obtain ⟨hρF, hρi⟩ := Finset.mem_filter.mp hρ1
        obtain ⟨r0, r1, r2, r3⟩ : ρ ∈ ZerosBelow χ T := hfin.mem_toFinset.mp hρF
        rw [Set.Finite.mem_toFinset]
        refine ⟨r0, r1, ?_, r3⟩
        have a1 : (i : ℝ) ≤ |ρ.im| := by rw [← hρi]; exact Nat.floor_le (abs_nonneg _)
        have a2 : |ρ.im| < (i : ℝ) + 1 := by rw [← hρi]; exact Nat.lt_floor_add_one _
        rw [abs_of_neg (not_le.mp hs)] at a1 a2
        rw [abs_le]
        constructor <;> linarith
      · intro ρ _ _
        exact Nat.cast_nonneg _
  have hmaps : ∀ ρ ∈ hfin.toFinset, ⌊|ρ.im|⌋₊ ∈ Finset.range (M + 1) := by
    intro ρ hρ
    obtain ⟨r0, r1, r2, r3⟩ : ρ ∈ ZerosBelow χ T := hfin.mem_toFinset.mp hρ
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.floor_le_floor r2.le))
  have hH : ∑ i ∈ Finset.range (M + 1), (1 : ℝ) / ((i : ℝ) + 1) ≤ 2 + Real.log T := by
    have h := harmonic_le_one_add_log (M + 1)
    have e : ((harmonic (M + 1) : ℚ) : ℝ) = ∑ i ∈ Finset.range (M + 1), (1 : ℝ) / ((i : ℝ) + 1) := by
      simp [harmonic, one_div]
    rw [e] at h
    linarith
  have hb0 : 0 ≤ lam / ka := by positivity
  have hI : ∑ i ∈ Finset.range (M + 1), (if i ≤ 2 then lam / ka else 0) ≤ 3 * (lam / ka) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ hb0
    have : ((Finset.range (M + 1)).filter (fun i => i ≤ 2)).card ≤ (Finset.range 3).card := by
      apply Finset.card_le_card
      intro i hi
      have := (Finset.mem_filter.mp hi).2
      exact Finset.mem_range.mpr (by omega)
    rw [Finset.card_range] at this
    exact_mod_cast this
  have hA : ∑ i ∈ Finset.range (M + 1), a i ≤ (3 / ka + 4) * Y := by
    simp only [ha]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 : 3 * (lam / ka) ≤ 3 / ka * Y := by
      have : lam ≤ Y := by linarith
      calc 3 * (lam / ka) = 3 / ka * lam := by ring
        _ ≤ 3 / ka * Y := mul_le_mul_of_nonneg_left this (by positivity)
    nlinarith
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ i ∈ Finset.range (M + 1), ∑ ρ ∈ hfin.toFinset with ⌊|ρ.im|⌋₊ = i, (zOrd χ ρ : ℝ) / ‖ρ‖
      ≤ ∑ i ∈ Finset.range (M + 1), a i * (2 * (C * La)) := Finset.sum_le_sum hfib
    _ = (∑ i ∈ Finset.range (M + 1), a i) * (2 * (C * La)) := by rw [Finset.sum_mul]
    _ ≤ ((3 / ka + 4) * Y) * (2 * (C * (3 * Y))) := by
        apply mul_le_mul hA _ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLa3 hC.le) (by norm_num)
    _ = 6 * C * (3 / ka + 4) * Y ^ 2 := by ring

def InvE (D : D7) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), IsCharED D χ → IsCharED D χ⁻¹

theorem zeroSumE_of {C7 C c : ℝ} (hC : 0 < C) (hc : 0 < c) (D : D7) (h7 : adm7 D C7) (h11 : adm11 D C)
    (hzf : ZeroFreeE D c) (hcond : CondE D) (hinv : InvE D) :
    ZeroSumE D (6 * C * (3 / (c / 3) + 4)) := by
  intro N _ χ hχ T hT
  have hlam : 1 ≤ lamE D := le_max_left _ _
  refine zero_sum_core hC hlam (by positivity) D h7 h11 χ hχ.1 (log_cond_le hcond hχ) ?_ T hT
  intro ρ r0 r1 r2 r3
  have hz' := zero_symm hχ.1 r0 r1 r3
  have h := hzf N χ⁻¹ (hinv N χ hχ) (1 - ρ) (by rw [Complex.sub_re, Complex.one_re]; linarith)
    (by rw [Complex.sub_re, Complex.one_re]; linarith) hz'
  rw [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at h
  have hl5 : Real.log (|ρ.im| + 3) ≤ 2 := by
    have h1 : Real.log (|ρ.im| + 3) ≤ Real.log (Real.exp 2) := by
      apply Real.log_le_log (by positivity)
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      have h3 := Real.exp_one_gt_d9
      nlinarith
    rwa [Real.log_exp] at h1
  have hl0 : 0 ≤ Real.log (|ρ.im| + 3) := Real.log_nonneg (by linarith [abs_nonneg ρ.im])
  have hcmp : c / 3 / lamE D ≤ c / (lamE D + Real.log (|ρ.im| + 3)) := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by linarith)]
    nlinarith
  linarith

theorem thin_of_zeroFree (eps C7 C11 c : ℝ) (heps : 0 < eps) (hC7 : 0 < C7) (hC11 : 0 < C11) (hc : 0 < c) :
    ∃ c' x0 : ℝ, 0 < c' ∧ 1 < x0 ∧ ∀ x : ℝ, x0 ≤ x → ∀ D : D7,
      Real.log (NE D : ℝ) ≤ 8 * x ^ (eps / 5) * Real.log x ^ 2 → adm7 D C7 → adm11 D C11 → ZeroFreeE D c →
      CondE D → InvE D → ThinE D x eps c' := by
  have hC2 : 0 < 6 * C11 * (3 / (c / 3) + 4) := by positivity
  obtain ⟨c', x0, hc', hx0, h⟩ := thin_of_psiThin eps (min (c / 3) 1)
    (C7 * (5 + 6 * C11 * (3 / (c / 3) + 4)) + 6 * C11 * (3 / (c / 3) + 4)) heps
    (lt_min (by positivity) one_pos) (by positivity)
  refine ⟨c', max x0 (3 ^ (3 / eps)), hc', lt_of_lt_of_le hx0 (le_max_left _ _), ?_⟩
  intro x hx D hlog h7 h11 hzf hcond hinv
  have hx3 : (3 : ℝ) ^ (3 / eps) ≤ x := (le_max_right _ _).trans hx
  have hp3 : 3 ≤ x ^ (eps / 3) := by
    have h1 : ((3 : ℝ) ^ (3 / eps)) ^ (eps / 3) ≤ x ^ (eps / 3) :=
      Real.rpow_le_rpow (by positivity) hx3 (by positivity)
    rw [← Real.rpow_mul (by norm_num)] at h1
    have e : 3 / eps * (eps / 3) = 1 := by field_simp
    rwa [e, Real.rpow_one] at h1
  exact h x ((le_max_left _ _).trans hx) D hlog
    (psiThin_of hC7 hC2.le hc D h7 hzf hcond (zeroSumE_of hC11 hc D h7 h11 hzf hcond hinv) x eps hp3)

theorem proposition_six_of_zero_free_region (eps C7 C11 c : ℝ) (heps : 0 < eps) (hC7 : 0 < C7) (hC11 : 0 < C11) (hc : 0 < c) :
    ∃ c' x0 : ℝ, 0 < c' ∧ 1 < x0 ∧ ∀ x : ℝ, x0 ≤ x → ∀ D : D7, adm7 D C7 → adm11 D C11 → ZeroFreeE D c →
      CondE D → InvE D → PropTwoSixThinScales D x eps c' := by
  obtain ⟨c', x0, hc', hx0, h⟩ := thin_of_zeroFree eps C7 C11 c heps hC7 hC11 hc
  exact ⟨c', x0, hc', hx0, fun x hx D h7 h11 hzf hcond hinv h5 =>
    h x hx D (log_conductor_le_of_proposition_two_six (by linarith) h5) h7 h11 hzf hcond hinv⟩

theorem inv_of_cube {w : ℂ} (h : w ^ 3 = w) : w⁻¹ = w := by
  by_cases h0 : w = 0
  · simp [h0]
  · have h1 : w * w = 1 := by
      have h2 : w * (w * w) = w * 1 := by
        calc w * (w * w) = w ^ 3 := by ring
          _ = w * 1 := by rw [h, mul_one]
      exact mul_left_cancel₀ h0 h2
    exact inv_eq_of_mul_eq_one_left h1

theorem kronSym_cube (D : ℤ) (a : ℕ) : kronSym D a ^ 3 = kronSym D a := by
  unfold kronSym
  have h1 : ∀ z : ℤ, (z = 0 ∨ z = 1 ∨ z = -1) → z ^ 3 = z := by
    rintro z (h | h | h) <;> subst h <;> norm_num
  have hj := h1 _ (jacobiSym.trichotomy D (a / 2 ^ a.factorization 2))
  have hk : kron2 D ^ 3 = kron2 D := by
    unfold kron2; split_ifs <;> norm_num
  rw [mul_pow, hj, ← pow_mul, mul_comm (a.factorization 2) 3, pow_mul, hk]

theorem kron_cube (D : ℤ) (a : ℕ) : kron D a ^ 3 = kron D a := by
  unfold kron
  exact_mod_cast kronSym_cube D a

theorem principal_quartic_character_cube (q d : ℕ) (i : Fin 4) (a : ℕ) : chi0 q d i a ^ 3 = chi0 q d i a := by
  fin_cases i
  · simp [chi0]
  · exact kron_cube _ _
  · exact kron_cube _ _
  · show (chDir d a * psDir q a) ^ 3 = chDir d a * psDir q a
    rw [mul_pow]
    unfold chDir psDir
    rw [kron_cube, kron_cube]

theorem invE_holds (D : D7) : InvE D := by
  intro N _ χ hχ
  obtain ⟨hp, ψ, h⟩ := hχ
  refine ⟨isPrimitive_inv hp, ψ⁻¹, fun a ha => ?_⟩
  rw [MulChar.inv_apply_eq_inv', h a ha, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]

def RealNoExcE (D : D7) (c : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), IsCharED D χ → IsRealChar χ → 3 ≤ N → ∀ b : ℝ, 1 - 1 / 400 < b →
    b < 1 → 1 - c / Real.log ((NE D : ℝ) * 3) ≤ b → DirichletCharacter.LFunction χ b ≠ 0

theorem zeroFreeE_of {Cq c : ℝ} (hc : 0 < c) (D : D7) (h6 : adm6 D Cq c) (hcond : CondE D) (hre : RealNoExcE D c) :
    ZeroFreeE D (min c (1 / 400)) := by
  intro N _ χ hχ ρ r0 r1 hz
  by_contra hh
  push Not at hh
  have hlam : 1 ≤ lamE D := le_max_left _ _
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hNQ : (N : ℝ) ≤ NE D := hcond N χ hχ
  have hQ1 : (1 : ℝ) ≤ NE D := hN1.trans hNQ
  have hg3 : (3 : ℝ) ≤ |ρ.im| + 3 := by linarith [abs_nonneg ρ.im]
  have hl3 : 1 ≤ Real.log (|ρ.im| + 3) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlogeq : Real.log ((NE D : ℝ) * (|ρ.im| + 3)) = Real.log (NE D) + Real.log (|ρ.im| + 3) :=
    Real.log_mul (by linarith) (by linarith)
  have hlQ0 : 0 ≤ Real.log (NE D : ℝ) := Real.log_nonneg hQ1
  have hlogpos : 0 < Real.log ((NE D : ℝ) * (|ρ.im| + 3)) := by rw [hlogeq]; linarith
  have hlogle : Real.log ((NE D : ℝ) * (|ρ.im| + 3)) ≤ lamE D + Real.log (|ρ.im| + 3) := by
    rw [hlogeq]
    have : Real.log (NE D : ℝ) ≤ lamE D := le_max_right _ _
    linarith
  have hm0 : 0 < min c (1 / 400) := lt_min hc (by norm_num)
  have hcmp : min c (1 / 400) / (lamE D + Real.log (|ρ.im| + 3)) ≤ c / Real.log ((NE D : ℝ) * (|ρ.im| + 3)) :=
    (div_le_div_of_nonneg_left hm0.le hlogpos hlogle).trans
      (div_le_div_of_nonneg_right (min_le_left _ _) hlogpos.le)
  have h := exceptional_zero_real_of_landau_page hc D h6 hχ.1 hNQ r0 hz (by linarith)
  have him : ρ.im = 0 := h.2.1
  have hreal : IsRealChar χ := h.2.2
  have hρ : ρ = ((ρ.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  have h400 : min c (1 / 400) / (lamE D + Real.log (|ρ.im| + 3)) ≤ 1 / 400 := by
    calc min c (1 / 400) / (lamE D + Real.log (|ρ.im| + 3)) ≤ min c (1 / 400) / 1 :=
          div_le_div_of_nonneg_left hm0.le one_pos (by linarith)
      _ ≤ 1 / 400 := by rw [div_one]; exact min_le_right _ _
  have hreg : 1 - c / Real.log ((NE D : ℝ) * 3) ≤ ρ.re := by
    have h5 : 1 - c / Real.log ((NE D : ℝ) * (|ρ.im| + 3)) ≤ ρ.re := by linarith
    rwa [him, abs_zero, zero_add] at h5
  refine hre N χ hχ hreal h.1 ρ.re (by linarith) r1 hreg ?_
  rw [← hρ]; exact hz

theorem small_no_zero_le (B : ℕ) : ∃ c0 : ℝ, 0 < c0 ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    3 ≤ N → N ≤ B → ∀ b : ℝ, 1 - c0 ≤ b → b ≤ 1 → DirichletCharacter.LFunction χ b ≠ 0 := by
  have hev : ∀ᶠ s in 𝓝 (1 : ℂ), ∀ (k : Fin B) (χ : DirichletCharacter ℂ (k.val + 1)), χ ≠ 1 →
      DirichletCharacter.LFunction χ s ≠ 0 := by
    rw [Filter.eventually_all]
    intro k
    rw [Filter.eventually_all]
    intro χ
    by_cases hχ : χ = 1
    · exact Filter.Eventually.of_forall (fun _ h => absurd hχ h)
    · have hcont : ContinuousAt (DirichletCharacter.LFunction χ) 1 :=
        (DirichletCharacter.differentiable_LFunction hχ).continuous.continuousAt
      have hne : DirichletCharacter.LFunction χ 1 ≠ 0 := DirichletCharacter.LFunction_apply_one_ne_zero hχ
      exact (hcont.eventually_ne hne).mono (fun _ h _ => h)
  obtain ⟨e, he, h⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨e / 2, by linarith, ?_⟩
  intro N _ χ hp h3 h8 b hb1 hb2
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  have hχ : χ ≠ 1 := by
    rintro rfl
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at hp
    omega
  have hd : dist ((b : ℝ) : ℂ) 1 < e := by
    rw [Complex.dist_eq]
    have : ((b : ℝ) : ℂ) - 1 = ((b - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  exact h hd ⟨k, by omega⟩ χ hχ

theorem small_no_zero : ∃ c0 : ℝ, 0 < c0 ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → 3 ≤ N →
    N ≤ 8 → ∀ b : ℝ, 1 - c0 ≤ b → b ≤ 1 → DirichletCharacter.LFunction χ b ≠ 0 := small_no_zero_le 8

def RealClassE (D : D7) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), IsCharED D χ → IsRealChar χ →
    N ∣ 8 * oddQS D ∨ D.host.q ∣ N ∨ D.host.d ∣ N

def RealBoxE (D : D7) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), IsCharED D χ → IsRealChar χ → (D.host.q ∣ N ∨ D.host.d ∣ N) →
    ∀ b : ℝ, 1 - 1 / 400 < b → DirichletCharacter.LFunction χ b ≠ 0

theorem good_real_ne {Q : ℝ} (hQ : 0 ≤ Q) {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hg : GoodFor Q χ) {b : ℝ}
    (hb : 1 - 1 / 400 < b) : DirichletCharacter.LFunction χ b ≠ 0 :=
  hg.2.2.2 (b : ℂ) (by simpa using hb) (by simpa using hQ)

theorem realBoxE_of_boxE {D : D7} {Y e : ℝ} (h : BoxE D Y e) : RealBoxE D := by
  intro N _ χ hχ hr hqd b hb
  obtain ⟨h1, h2⟩ := h N χ hχ hr
  by_cases hd : D.host.d ∣ N
  · exact good_real_ne (by unfold X1 X2; positivity) (h1 hd) hb
  · exact good_real_ne (by unfold X1; positivity) (h2 (hqd.resolve_right hd) hd) hb

theorem real_box_of_proposition_two_six {D : D7} {x eps : ℝ} (h : PropTwoSixBoxHypothesis D x eps) : RealBoxE D := by
  obtain ⟨⟨Y, -, -, hb⟩, -⟩ := h
  exact realBoxE_of_boxE hb

theorem oddQS_pos (D : D7) : 0 < oddQS D := Nat.ordCompl_pos 2 D.host.QS_pos.ne'

theorem oddQS_le_Co {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) :
    (oddQS (Fm.D x i) : ℝ) ≤ Fm.Co ^ 2 := by
  have h1 := Fm.o_le_Co x i hx
  have h2 := Fm.QS_le_Co x i hx
  generalize Fm.D x i = D at h1 h2 ⊢
  have hQ : D.host.QS ≠ 0 := D.host.QS_pos.ne'
  have h3 : 2 ^ D.R.e ∣ 2 ^ D.host.QS.factorization 2 := by
    apply pow_dvd_pow
    have := (Nat.prime_two.pow_dvd_iff_le_factorization hQ).1 D.host.tower_dvd
    omega
  have h4 : 2 ^ D.R.e * oddQS D ≤ D.host.QS := by
    calc 2 ^ D.R.e * oddQS D ≤ 2 ^ D.host.QS.factorization 2 * oddQS D :=
          Nat.mul_le_mul_right _ (Nat.le_of_dvd (by positivity) h3)
      _ = D.host.QS := Nat.ordProj_mul_ordCompl_eq_self _ 2
  have h5 : D.R.n ≤ D.R.o * 2 ^ D.R.e := D.R.toFrame.ord_le_o_mul_two_pow
  have h4' : (2 : ℝ) ^ D.R.e * oddQS D ≤ D.host.QS := by exact_mod_cast h4
  have h5' : (D.R.n : ℝ) ≤ D.R.o * 2 ^ D.R.e := by exact_mod_cast h5
  have hC : 0 ≤ Fm.Co := (Nat.cast_nonneg _).trans h1
  have hp : (0 : ℝ) < 2 ^ D.R.e := by positivity
  have h6 : (D.R.n : ℝ) ≤ Fm.Co * 2 ^ D.R.e := h5'.trans (mul_le_mul_of_nonneg_right h1 hp.le)
  have h7 : (2 : ℝ) ^ D.R.e * oddQS D ≤ 2 ^ D.R.e * Fm.Co ^ 2 := by
    calc _ ≤ Fm.Co * D.R.n := h4'.trans h2
      _ ≤ Fm.Co * (Fm.Co * 2 ^ D.R.e) := mul_le_mul_of_nonneg_left h6 hC
      _ = _ := by ring
  exact le_of_mul_le_mul_left h7 hp

theorem realNoExcE_of (D : D7) (c : ℝ) (hc : 0 ≤ c) (hB : RealBoxE D)
    (hq : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → 3 ≤ N → N ≤ 8 * oddQS D → ∀ b : ℝ,
      1 - c ≤ b → b ≤ 1 → DirichletCharacter.LFunction χ b ≠ 0) (hcl : RealClassE D)
    (hcond : CondE D) : RealNoExcE D c := by
  intro N _ χ hχ hr hN3 b hb hb1 hreg
  rcases hcl N χ hχ hr with h | h
  · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
    have hNQ := hcond N χ hχ
    have hl1 : 1 ≤ Real.log ((NE D : ℝ) * 3) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9
      linarith
    have hdiv : c / Real.log ((NE D : ℝ) * 3) ≤ c := div_le_self hc hl1
    exact hq N χ hχ.1 hN3 (Nat.le_of_dvd (by have := oddQS_pos D; omega) h) b (by linarith) hb1.le
  · exact hB N χ hχ hr h b hb

lemma lambda_size_bound_mono {D : Formalism.BasicNotions.D7} {C1 c c' : ℝ} (hcc : c' ≤ c) (h : adm6 D C1 c) : adm6 D C1 c' := by
  obtain ⟨h1, h2, h3⟩ := h
  have key : ∀ {N : ℕ} (_ : 3 ≤ N) (t : ℝ),
      c' / Real.log (max (N : ℝ) (N * |t|)) ≤ c / Real.log (max (N : ℝ) (N * |t|)) := by
    intro N hN t
    have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    exact div_le_div_of_nonneg_right hcc (Real.log_nonneg (by linarith [le_max_left (N : ℝ) (N * |t|)]))
  refine ⟨h1, fun N _ χ hp hN ρ hz hr => ?_, fun ρ hz h0 h1' => ?_⟩
  · obtain ⟨a1, a2, a3, a4⟩ := h2 N χ hp hN ρ hz (by linarith [key hN ρ.im])
    exact ⟨a1, a2, a3, fun ρ' hz' hr' => a4 ρ' hz' (by linarith [key hN ρ'.im])⟩
  · have := h3 ρ hz h0 h1'
    have hl : 0 ≤ Real.log (|ρ.im| + 3) := Real.log_nonneg (by linarith [abs_nonneg ρ.im])
    have := div_le_div_of_nonneg_right hcc hl
    linarith

theorem thin_of_adm (eps c6 C7 C11 : ℝ) (B : ℕ) (heps : 0 < eps) (hc6 : 0 < c6) (hC7 : 0 < C7) (hC11 : 0 < C11) :
    ∃ c' x0 : ℝ, 0 < c' ∧ 1 < x0 ∧ ∀ x : ℝ, x0 ≤ x → ∀ (D : D7) (Cq : ℝ), oddQS D ≤ B → RealBoxE D →
      Real.log (NE D : ℝ) ≤ 8 * x ^ (eps / 5) * Real.log x ^ 2 → adm6 D Cq c6 → adm7 D C7 → adm11 D C11 →
      CondE D → RealClassE D → ThinE D x eps c' := by
  obtain ⟨c0, hc0, hq⟩ := small_no_zero_le (8 * B)
  have hcm : 0 < min c6 c0 := lt_min hc6 hc0
  obtain ⟨c', x0, hc', hx0, h⟩ := thin_of_zeroFree eps C7 C11 (min (min c6 c0) (1 / 400)) heps hC7 hC11
    (lt_min hcm (by norm_num))
  refine ⟨c', x0, hc', hx0, fun x hx D Cq hodd hB hlog h6 h7 h11 hcond hcl => ?_⟩
  have hq' : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → 3 ≤ N → N ≤ 8 * oddQS D → ∀ b : ℝ,
      1 - min c6 c0 ≤ b → b ≤ 1 → DirichletCharacter.LFunction χ b ≠ 0 :=
    fun N _ χ hp h3 h8 b hb hb1 => hq N χ hp h3 (by omega) b (by linarith [min_le_right c6 c0]) hb1
  exact h x hx D hlog h7 h11 (zeroFreeE_of hcm D (lambda_size_bound_mono (min_le_left _ _) h6) hcond
    (realNoExcE_of D (min c6 c0) hcm.le hB hq' hcl hcond)) hcond (invE_holds D)

theorem classMap_estimate_of_admissible (eps c6 C7 C11 : ℝ) (B : ℕ) (heps : 0 < eps) (hc6 : 0 < c6) (hC7 : 0 < C7) (hC11 : 0 < C11) :
    ∃ c' x0 : ℝ, 0 < c' ∧ 1 < x0 ∧ ∀ x : ℝ, x0 ≤ x → ∀ (D : D7) (Cq : ℝ), oddQS D ≤ B →
      adm6 D Cq c6 → adm7 D C7 → adm11 D C11 →
      CondE D → RealClassE D → PropTwoSixThinScales D x eps c' := by
  obtain ⟨c', x0, hc', hx0, h⟩ := thin_of_adm eps c6 C7 C11 B heps hc6 hC7 hC11
  exact ⟨c', x0, hc', hx0, fun x hx D Cq hodd h6 h7 h11 hcond hcl h5 =>
    h x hx D Cq hodd (real_box_of_proposition_two_six h5) (log_conductor_le_of_proposition_two_six (by linarith) h5) h6 h7 h11 hcond hcl⟩

theorem thin_set_family_of_conditions {eps : ℝ} (Fm : FamP eps) (h6 : FamilySixthHypothesis Fm) (h7 : adm7F Fm) (h11 : ComplementTwoFamily Fm) :
    ∃ c : ℝ, 0 < c ∧ ∃ x0 : ℝ, 1 < x0 ∧ ∀ x ≥ x0, ∀ i : Fm.Ix x, CondE (Fm.D x i) → RealClassE (Fm.D x i) →
      RealBoxE (Fm.D x i) → Real.log (NE (Fm.D x i) : ℝ) ≤ 8 * x ^ (eps / 5) * Real.log x ^ 2 →
      ThinE (Fm.D x i) x eps c := by
  obtain ⟨Cq, c6, -, hc6, h6⟩ := h6
  obtain ⟨C7, hC7, h7⟩ := h7
  obtain ⟨C11, hC11, h11⟩ := h11
  obtain ⟨c', x0, hc', hx0, h⟩ := thin_of_adm eps c6 C7 C11 ⌈Fm.Co ^ 2⌉₊ (fam_eps Fm).1 hc6 hC7 hC11
  refine ⟨c', hc', max x0 (Fm.x1 + 1), lt_of_lt_of_le hx0 (le_max_left _ _), ?_⟩
  intro x hx i hcond hcl hB hlog
  have hx1 : 1 < x := lt_of_lt_of_le hx0 ((le_max_left _ _).trans hx)
  have hx2 : Fm.x1 < x := lt_of_lt_of_le (by linarith) ((le_max_right _ _).trans hx)
  have hodd : oddQS (Fm.D x i) ≤ ⌈Fm.Co ^ 2⌉₊ := by
    exact_mod_cast (oddQS_le_Co Fm x hx2 i).trans (Nat.le_ceil _)
  exact h x ((le_max_left _ _).trans hx) _ Cq hodd hB hlog (h6 x hx1 i) (h7 x hx1 i) (h11 x hx1 i) hcond hcl

theorem proposition_six_family_of_real_conditions {eps : ℝ} (Fm : FamP eps) (h6 : FamilySixthHypothesis Fm) (h7 : adm7F Fm) (h11 : ComplementTwoFamily Fm)
    (hE : ∃ x1 : ℝ, ∀ x ≥ x1, ∀ i : Fm.Ix x, CondE (Fm.D x i) ∧ RealClassE (Fm.D x i)) : FamilyPropTwoSixCongruenceForm Fm := by
  obtain ⟨x1, hE⟩ := hE
  obtain ⟨c', hc', x0, hx0, h⟩ := thin_set_family_of_conditions Fm h6 h7 h11
  refine ⟨c', hc', max x0 x1, lt_of_lt_of_le hx0 (le_max_left _ _), ?_⟩
  intro x hx i h5
  have a0 : x0 ≤ x := (le_max_left _ _).trans hx
  have a1 : x1 ≤ x := (le_max_right _ _).trans hx
  exact h x a0 i (hE x a1 i).1 (hE x a1 i).2 (real_box_of_proposition_two_six h5) (log_conductor_le_of_proposition_two_six (by linarith) h5)

end Formalism.MainNotions.ShortIntervalPrimes

end

noncomputable section

namespace Formalism.MainNotions.ShortIntervalPrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Filter Topology DirichletCharacter

lemma kronecker_two_eq_chi_eight (D : ℤ) : kron2 D = ZMod.χ₈ (D : ZMod 8) := by
  have h8 : (D : ZMod 8) = ((D % 8 : ℤ) : ZMod 8) := by
    have := ZMod.intCast_mod D 8
    exact_mod_cast this.symm
  have h2 : D % 2 = (D % 8) % 2 := by omega
  have h88 : D % 8 = (D % 8) % 8 := by omega
  have h0 := Int.emod_nonneg D (show (8 : ℤ) ≠ 0 by norm_num)
  have h1 := Int.emod_lt_of_pos D (show (0 : ℤ) < 8 by norm_num)
  unfold kron2
  rw [h8, h2, h88]
  generalize D % 8 = r at *
  interval_cases r <;> simp <;> decide

lemma kronSym_eq_jacobi' (q n : ℕ) (hq : q % 4 = 3) (hn : n ≠ 0) :
    kronSym (-(q : ℤ)) n = jacobiSym (n : ℤ) q := by
  unfold kronSym
  set v := n.factorization 2 with hv
  set m := n / 2 ^ v with hm
  have hnm : 2 ^ v * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hodd : Odd m := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact Nat.not_dvd_ordCompl Nat.prime_two hn
  have e1 : jacobiSym (n : ℤ) q = jacobiSym 2 q ^ v * jacobiSym (m : ℤ) q := by
    rw [← hnm]; push_cast
    rw [jacobiSym.mul_left, jacobiSym.pow_left]
  rw [e1, Formalism.HermitianLattices.GL2a2.kronecker_odd q m hq hodd, kronecker_two_eq_chi_eight, Formalism.HermitianLattices.GL2a2.kronecker_two q hq, mul_comm]

lemma changeLevel_natCast {n M : ℕ} (h : n ∣ M) (χ : DirichletCharacter ℂ n) (a : ℕ) (ha : a.Coprime M) :
    changeLevel h χ (a : ZMod M) = χ (a : ZMod n) := by
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime a M).2 ha
  rw [← hu, changeLevel_eq_cast_of_dvd, hu, ZMod.cast_natCast h]

theorem level_dvd_of_agree {N M : ℕ} [NeZero N] (hM : M ≠ 0) (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive)
    (ψ : DirichletCharacter ℂ M) (h : ∀ a : ℕ, a.Coprime M → χ (a : ZMod N) = ψ (a : ZMod M)) : N ∣ M := by
  have hL : N * M ≠ 0 := mul_ne_zero (NeZero.ne N) hM
  have : NeZero (N * M) := ⟨hL⟩
  have d1 : N ∣ N * M := ⟨M, rfl⟩
  have d2 : M ∣ N * M := ⟨N, by ring⟩
  have key : changeLevel d1 χ = changeLevel d2 ψ := by
    ext u
    have hc : ((u : ZMod (N * M)).val).Coprime (N * M) := ZMod.val_coe_unit_coprime u
    have hu : (((u : ZMod (N * M)).val : ℕ) : ZMod (N * M)) = u := ZMod.natCast_zmod_val _
    rw [← hu, changeLevel_natCast d1 χ _ hc, changeLevel_natCast d2 ψ _ hc]
    exact h _ (Nat.Coprime.coprime_dvd_right d2 hc)
  have c1 : conductor (changeLevel d1 χ) = N := by rw [conductor_changeLevel]; exact hp
  have c2 : conductor (changeLevel d2 ψ) = conductor ψ := by rw [conductor_changeLevel]
  rw [← c1, key, c2]
  exact conductor_dvd_level ψ

def Jc (p : ℕ) [Fact p.Prime] : DirichletCharacter ℂ p :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

lemma Jc_apply (p : ℕ) [Fact p.Prime] (a : ℕ) : Jc p (a : ZMod p) = ((jacobiSym (a : ℤ) p : ℤ) : ℂ) := by
  unfold Jc
  rw [MulChar.ringHomComp_apply, ← jacobiSym.legendreSym.to_jacobiSym]
  unfold legendreSym
  simp

lemma kron_eq_Jc (p : ℕ) [Fact p.Prime] (hp4 : p % 4 = 3) (a : ℕ) (ha : a ≠ 0) :
    kron (-(p : ℤ)) a = Jc p (a : ZMod p) := by
  unfold kron
  rw [kronSym_eq_jacobi' p a hp4 ha, Jc_apply]

theorem level_dvd_NE {n q d : ℕ} (hn : 0 < n) (hq : q.Prime) (hq4 : q % 4 = 3) (hd : d.Prime) (hd4 : d % 4 = 3)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (h : IsCharE n q d χ) : N ∣ 4 * n * q * d := by
  obtain ⟨hp, i, ξ, -, hv⟩ := h
  have : Fact q.Prime := ⟨hq⟩
  have : Fact d.Prime := ⟨hd⟩
  have hM : 4 * n * q * d ≠ 0 := by
    have := hq.pos; have := hd.pos; positivity
  have dn : 4 * n ∣ 4 * n * q * d := ⟨q * d, by ring⟩
  have dq : q ∣ 4 * n * q * d := ⟨4 * n * d, by ring⟩
  have dd : d ∣ 4 * n * q * d := ⟨4 * n * q, by ring⟩
  have hne : ∀ a : ℕ, a.Coprime (4 * n * q * d) → a ≠ 0 := by
    rintro a ha rfl
    rw [Nat.coprime_zero_left] at ha
    have h4 : 4 ∣ 4 * n * q * d := ⟨n * q * d, by ring⟩
    rw [ha] at h4
    omega
  fin_cases i
  · refine level_dvd_of_agree hM χ hp (changeLevel dn ξ) (fun a ha => ?_)
    rw [hv a ha, changeLevel_natCast dn ξ a ha]
    simp [chi0]
  · refine level_dvd_of_agree hM χ hp (changeLevel dd (Jc d) * changeLevel dn ξ) (fun a ha => ?_)
    rw [hv a ha, MulChar.mul_apply, changeLevel_natCast dn ξ a ha, changeLevel_natCast dd _ a ha,
      ← kron_eq_Jc d hd4 a (hne a ha)]
    rfl
  · refine level_dvd_of_agree hM χ hp (changeLevel dq (Jc q) * changeLevel dn ξ) (fun a ha => ?_)
    rw [hv a ha, MulChar.mul_apply, changeLevel_natCast dn ξ a ha, changeLevel_natCast dq _ a ha,
      ← kron_eq_Jc q hq4 a (hne a ha)]
    rfl
  · refine level_dvd_of_agree hM χ hp (changeLevel dd (Jc d) * changeLevel dq (Jc q) * changeLevel dn ξ)
      (fun a ha => ?_)
    rw [hv a ha, MulChar.mul_apply, MulChar.mul_apply, changeLevel_natCast dn ξ a ha,
      changeLevel_natCast dq _ a ha, changeLevel_natCast dd _ a ha,
      ← kron_eq_Jc q hq4 a (hne a ha), ← kron_eq_Jc d hd4 a (hne a ha)]
    rfl

theorem level_dvd_condN (D : D7) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (h : IsCharED D χ) :
    N ∣ D.host.QS * D.host.q * D.host.d := by
  obtain ⟨hp, ψ, hv⟩ := h
  have hM : D.host.QS * D.host.q * D.host.d ≠ 0 := by
    have := D.host.hyp.1.pos; have := D.host.hyp.2.1.pos; have := D.host.QS_pos; positivity
  refine level_dvd_of_agree hM χ hp (MulChar.ofUnitHom (ψ.comp D.host.art)) (fun a ha => ?_)
  rw [hv a ha, ← ZMod.coe_unitOfCoprime a ha, MulChar.ofUnitHom_coe]
  rfl

theorem condE_holds (D : D7) : CondE D := by
  intro N _ χ hχ
  have hpos : 0 < D.host.QS * D.host.q * D.host.d := by
    have := D.host.hyp.1.pos; have := D.host.hyp.2.1.pos; have := D.host.QS_pos; positivity
  have := Nat.le_of_dvd hpos (level_dvd_condN D χ hχ)
  unfold NE
  exact_mod_cast this

theorem condE_of (D : D7) (_hn : 0 < D.R.n) (_hq : D.host.q.Prime) (_hq4 : D.host.q % 4 = 3) (_hd : D.host.d.Prime)
    (_hd4 : D.host.d % 4 = 3) : CondE D := condE_holds D

theorem condition_E_of_proposition_two_five (D : D7) (x eps C5 : ℝ) (_hn : 0 < D.R.n) (_h5 : PrimesAsPropTwoFive D x eps C5) : CondE D :=
  condE_holds D

theorem proposition_six_of_real_class_condition (eps c6 C7 C11 : ℝ) (B : ℕ) (h0 : 0 < eps) (h6 : 0 < c6) (h7 : 0 < C7) (h11 : 0 < C11) :
    ∃ c' x0 : ℝ, 0 < c' ∧ 1 < x0 ∧ ∀ x : ℝ, x0 ≤ x → ∀ (D : D7) (Cq : ℝ), oddQS D ≤ B →
      adm6 D Cq c6 → adm7 D C7 → adm11 D C11 →
      RealClassE D → PropTwoSixThinScales D x eps c' := by
  obtain ⟨c', x0, hc', hx0, h⟩ := classMap_estimate_of_admissible eps c6 C7 C11 B h0 h6 h7 h11
  exact ⟨c', x0, hc', hx0, fun x hx D Cq hodd a6 a7 a11 hr => h x hx D Cq hodd a6 a7 a11 (condE_holds D) hr⟩

theorem proposition_six_family_of_real_classes {eps : ℝ} (Fm : FamP eps) (h6 : FamilySixthHypothesis Fm) (h7 : adm7F Fm) (h11 : ComplementTwoFamily Fm)
    (hR : ∃ x1 : ℝ, ∀ x ≥ x1, ∀ i : Fm.Ix x, RealClassE (Fm.D x i)) : FamilyPropTwoSixCongruenceForm Fm := by
  obtain ⟨x1, hR⟩ := hR
  exact proposition_six_family_of_real_conditions Fm h6 h7 h11 ⟨x1, fun x hx i => ⟨condE_holds _, hR x hx i⟩⟩

lemma gen5 (e : ℕ) (v : (ZMod (2 ^ (e + 2)))ˣ) :
    ∃ k : ℕ, v = Formalism.TwoAdicCyclotomicDecomposition.u5 (e + 2) ^ k ∨ v = -(Formalism.TwoAdicCyclotomicDecomposition.u5 (e + 2) ^ k) := by
  obtain ⟨k, hk⟩ := Formalism.LFunctionChainParameters.LBr2.H_gen e (Formalism.FrobeniusOrbits.hcl e v)
  refine ⟨k, ?_⟩
  have h1 : Formalism.FrobeniusOrbits.hcl e v = Formalism.FrobeniusOrbits.hcl e (Formalism.TwoAdicCyclotomicDecomposition.u5 (e + 2) ^ k) := by rw [hk]; rfl
  unfold Formalism.FrobeniusOrbits.hcl at h1
  rw [QuotientGroup.eq] at h1
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 h1
  rcases Int.even_or_odd j with h | h
  · rw [h.neg_one_zpow] at hj
    left
    exact inv_mul_eq_one.1 hj.symm
  · rw [h.neg_one_zpow] at hj
    right
    have h2 : Formalism.TwoAdicCyclotomicDecomposition.u5 (e + 2) ^ k = v * (-1) := by rw [hj]; group
    rw [h2]; simp

theorem even_char_two_pow (e : ℕ) (he : 1 ≤ e) (ξ : DirichletCharacter ℂ (2 ^ (e + 2))) (hev : ξ.Even) (a : ℕ)
    (ha : Odd a) : ∃ k : ℕ, ξ (a : ZMod (2 ^ (e + 2))) = ξ ((5 : ℕ) : ZMod (2 ^ (e + 2))) ^ k ∧ chi8 a = (-1) ^ k := by
  have hcop : a.Coprime (2 ^ (e + 2)) := Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 ha)
  obtain ⟨v, hv⟩ := (ZMod.isUnit_iff_coprime a (2 ^ (e + 2))).2 hcop
  obtain ⟨k, hk⟩ := gen5 e v
  have h5 : ((Formalism.TwoAdicCyclotomicDecomposition.u5 (e + 2) : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = ((5 : ℕ) : ZMod (2 ^ (e + 2))) :=
    ZMod.coe_unitOfCoprime 5 _
  have h8 : 8 ∣ 2 ^ (e + 2) := by
    obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le he
    exact ⟨2 ^ f, by ring⟩
  have hval : (a : ZMod (2 ^ (e + 2))) = ((5 : ℕ) : ZMod (2 ^ (e + 2))) ^ k ∨
      (a : ZMod (2 ^ (e + 2))) = -(((5 : ℕ) : ZMod (2 ^ (e + 2))) ^ k) := by
    rcases hk with h | h
    · left; rw [← hv, h, Units.val_pow_eq_pow_val, h5]
    · right; rw [← hv, h, Units.val_neg, Units.val_pow_eq_pow_val, h5]
  have hchi : chi8 a = ((ZMod.χ₈ (a : ZMod 8) : ℤ) : ℂ) := by
    unfold chi8 kron kronSym
    have hf : a.factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by rw [← even_iff_two_dvd, Nat.not_even_iff_odd]; exact ha)
    rw [hf, pow_zero, pow_zero, Nat.div_one, mul_one, jacobiSym.at_two ha]
  have hcast : (a : ZMod 8) = (5 : ZMod 8) ^ k ∨ (a : ZMod 8) = -((5 : ZMod 8) ^ k) := by
    rcases hval with h | h
    · left
      have := congrArg (ZMod.castHom h8 (ZMod 8)) h
      rw [map_natCast, map_pow, map_natCast] at this
      simpa using this
    · right
      have := congrArg (ZMod.castHom h8 (ZMod 8)) h
      rw [map_natCast, map_neg, map_pow, map_natCast] at this
      simpa using this
  have c5 : ZMod.χ₈ (5 : ZMod 8) = -1 := by decide
  have cm : ZMod.χ₈ (-1 : ZMod 8) = 1 := by decide
  refine ⟨k, ?_, ?_⟩
  · rcases hval with h | h
    · rw [h, map_pow]
    · rw [h, ← neg_one_mul, map_mul, map_pow, hev, one_mul]
  · rw [hchi]
    rcases hcast with h | h
    · rw [h, map_pow, c5]; push_cast; rfl
    · rw [h, ← neg_one_mul, map_mul, map_pow, c5, cm, one_mul]; push_cast; rfl

theorem level_dvd_of_agree' {N M M' : ℕ} [NeZero N] (hM : M ≠ 0) (hM' : M' ≠ 0) (χ : DirichletCharacter ℂ N)
    (hp : χ.IsPrimitive) (ψ : DirichletCharacter ℂ M')
    (h : ∀ a : ℕ, a.Coprime M → χ (a : ZMod N) = ψ (a : ZMod M')) : N ∣ M' := by
  have hL : N * M * M' ≠ 0 := mul_ne_zero (mul_ne_zero (NeZero.ne N) hM) hM'
  have : NeZero (N * M * M') := ⟨hL⟩
  have d1 : N ∣ N * M * M' := ⟨M * M', by ring⟩
  have d2 : M' ∣ N * M * M' := ⟨N * M, by ring⟩
  have d3 : M ∣ N * M * M' := ⟨N * M', by ring⟩
  have key : changeLevel d1 χ = changeLevel d2 ψ := by
    ext u
    have hc : ((u : ZMod (N * M * M')).val).Coprime (N * M * M') := ZMod.val_coe_unit_coprime u
    have hu : (((u : ZMod (N * M * M')).val : ℕ) : ZMod (N * M * M')) = u := ZMod.natCast_zmod_val _
    rw [← hu, changeLevel_natCast d1 χ _ hc, changeLevel_natCast d2 ψ _ hc]
    exact h _ (Nat.Coprime.coprime_dvd_right d3 hc)
  have c1 : conductor (changeLevel d1 χ) = N := by rw [conductor_changeLevel]; exact hp
  have c2 : conductor (changeLevel d2 ψ) = conductor ψ := by rw [conductor_changeLevel]
  rw [← c1, key, c2]
  exact conductor_dvd_level ψ

lemma chi_eight_odd_eq_zmod (a : ℕ) (ha : Odd a) : chi8 a = ((ZMod.χ₈ (a : ZMod 8) : ℤ) : ℂ) := by
  unfold chi8 kron kronSym
  have hf : a.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by rw [← even_iff_two_dvd, Nat.not_even_iff_odd]; exact ha)
  rw [hf, pow_zero, pow_zero, Nat.div_one, mul_one, jacobiSym.at_two ha]

lemma kron_sq (p a : ℕ) (hp4 : p % 4 = 3) (ha : a.Coprime p) (ha0 : a ≠ 0) : kron (-(p : ℤ)) a ^ 2 = 1 := by
  unfold kron
  rw [kronSym_eq_jacobi' p a hp4 ha0]
  have : jacobiSym (a : ℤ) p ^ 2 = 1 := jacobiSym.sq_one (by rw [Int.gcd_natCast_natCast]; exact ha)
  exact_mod_cast this

lemma principal_quartic_character_sq_eq_one (q d : ℕ) (hq4 : q % 4 = 3) (hd4 : d % 4 = 3) (i : Fin 4) (a : ℕ) (hq : a.Coprime q) (hd : a.Coprime d)
    (ha0 : a ≠ 0) : chi0 q d i a ^ 2 = 1 := by
  have h1 := kron_sq q a hq4 hq ha0
  have h2 := kron_sq d a hd4 hd ha0
  fin_cases i
  · simp [chi0]
  · exact h2
  · exact h1
  · show (kron (-(d : ℤ)) a * kron (-(q : ℤ)) a) ^ 2 = 1
    rw [mul_pow, h1, h2, one_mul]

lemma real_unit_sq {N : ℕ} (χ : DirichletCharacter ℂ N) (hreal : IsRealChar χ) (a : ℕ) (ha : a.Coprime N) :
    χ (a : ZMod N) ^ 2 = 1 := by
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime a N).2 ha
  have hn : ‖χ (a : ZMod N)‖ = 1 := by rw [← hu]; exact DirichletCharacter.unit_norm_eq_one χ u
  have him : (χ (a : ZMod N)).im = 0 := hreal _
  set z := χ (a : ZMod N) with hz
  have h1 : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]
  have h2 : z.re ^ 2 = 1 := by
    have := Complex.sq_norm z
    rw [hn, Complex.normSq_apply, him] at this
    nlinarith
  rw [h1]; exact_mod_cast h2

theorem realClass_core (e : ℕ) (he : 1 ≤ e) {q d : ℕ} (hq : q.Prime) (hq4 : q % 4 = 3) (hd : d.Prime)
    (hd4 : d % 4 = 3) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive) (hreal : IsRealChar χ)
    (i : Fin 4) (ξ : DirichletCharacter ℂ (2 ^ (e + 2))) (hev : ξ.Even)
    (hv : ∀ a : ℕ, a.Coprime (2 ^ (e + 2) * q * d) → χ (a : ZMod N) = chi0 q d i a * ξ (a : ZMod (2 ^ (e + 2)))) :
    N ≤ 8 ∨ Induces χ (psDir q) (8 * q * d) ∨ Induces χ (fun a => chi8 a * psDir q a) (8 * q * d) ∨
    Induces χ (chDir d) (8 * q * d) ∨ Induces χ (fun a => chi8 a * chDir d a) (8 * q * d) ∨
    Induces χ (fun a => chDir d a * psDir q a) (8 * q * d) ∨
    Induces χ (fun a => chi8 a * chDir d a * psDir q a) (8 * q * d) := by
  have hqp := hq.pos
  have hdp := hd.pos
  have hMpos : 0 < 2 ^ (e + 2) * q * d := by positivity
  have h8pos : 8 * q * d ≠ 0 := by positivity
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have : NeZero (2 ^ (e + 2)) := ⟨by positivity⟩

  have hs : ξ ((5 : ℕ) : ZMod (2 ^ (e + 2))) = 1 ∨ ξ ((5 : ℕ) : ZMod (2 ^ (e + 2))) = -1 := by
    have hu5 : IsUnit (((5 : ℕ) : ZMod (2 ^ (e + 2)))) :=
      (ZMod.isUnit_iff_coprime 5 _).2 (Nat.Coprime.pow_right _ (by norm_num))
    obtain ⟨p, hpgt, hpp, hpu⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu5 (2 ^ (e + 2) * q * d + N)
    have cM : p.Coprime (2 ^ (e + 2) * q * d) :=
      (Nat.Prime.coprime_iff_not_dvd hpp).2 (Nat.not_dvd_of_pos_of_lt hMpos (by omega))
    have cN : p.Coprime N := (Nat.Prime.coprime_iff_not_dvd hpp).2 (Nat.not_dvd_of_pos_of_lt hNpos (by omega))
    have cq : p.Coprime q := Nat.Coprime.coprime_dvd_right ⟨2 ^ (e + 2) * d, by ring⟩ cM
    have cd : p.Coprime d := Nat.Coprime.coprime_dvd_right ⟨2 ^ (e + 2) * q, by ring⟩ cM
    have h1 := real_unit_sq χ hreal p cN
    have h2 := principal_quartic_character_sq_eq_one q d hq4 hd4 i p cq cd hpp.ne_zero
    rw [hv p cM, mul_pow, h2, one_mul, hpu] at h1
    have h3 : (ξ ((5 : ℕ) : ZMod (2 ^ (e + 2))) - 1) * (ξ ((5 : ℕ) : ZMod (2 ^ (e + 2))) + 1) = 0 := by
      linear_combination h1
    rcases mul_eq_zero.1 h3 with h | h
    · left; linear_combination h
    · right; linear_combination h
  have hcop : ∀ a : ℕ, a.Coprime (8 * q * d) → Odd a ∧ a.Coprime (2 ^ (e + 2) * q * d) := by
    intro a ha
    have c2 : a.Coprime 2 := Nat.Coprime.coprime_dvd_right ⟨4 * q * d, by ring⟩ ha
    have cq : a.Coprime q := Nat.Coprime.coprime_dvd_right ⟨8 * d, by ring⟩ ha
    have cd : a.Coprime d := Nat.Coprime.coprime_dvd_right ⟨8 * q, by ring⟩ ha
    exact ⟨Nat.coprime_two_right.1 c2, Nat.Coprime.mul_right (Nat.Coprime.mul_right (Nat.Coprime.pow_right _ c2) cq) cd⟩
  rcases hs with hs | hs
  · have key : ∀ a : ℕ, a.Coprime (8 * q * d) → χ (a : ZMod N) = chi0 q d i a := by
      intro a ha
      obtain ⟨ho, hc⟩ := hcop a ha
      obtain ⟨k, hk, -⟩ := even_char_two_pow e he ξ hev a ho
      rw [hv a hc, hk, hs, one_pow, mul_one]
    fin_cases i
    · left
      have := level_dvd_of_agree' h8pos one_ne_zero χ hp (1 : DirichletCharacter ℂ 1) (fun a ha => by
        rw [key a ha, MulChar.one_apply (isUnit_of_subsingleton _)]; rfl)
      have := Nat.le_of_dvd one_pos this
      omega
    · right; right; right; left
      exact ⟨hp, fun a ha => key a ha⟩
    · right; left
      exact ⟨hp, fun a ha => key a ha⟩
    · right; right; right; right; right; left
      exact ⟨hp, fun a ha => key a ha⟩
  · have key : ∀ a : ℕ, a.Coprime (8 * q * d) → χ (a : ZMod N) = chi0 q d i a * chi8 a := by
      intro a ha
      obtain ⟨ho, hc⟩ := hcop a ha
      obtain ⟨k, hk, hk8⟩ := even_char_two_pow e he ξ hev a ho
      rw [hv a hc, hk, hs, hk8]
    fin_cases i
    · left
      have := level_dvd_of_agree' h8pos (by norm_num) χ hp
        ((ZMod.χ₈).ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ 8) (fun a ha => by
          rw [key a ha, MulChar.ringHomComp_apply, chi_eight_odd_eq_zmod a (hcop a ha).1]
          simp [chi0])
      exact Nat.le_of_dvd (by norm_num) this
    · right; right; right; right; left
      exact ⟨hp, fun a ha => by rw [key a ha, mul_comm]; rfl⟩
    · right; right; left
      exact ⟨hp, fun a ha => by rw [key a ha, mul_comm]; rfl⟩
    · right; right; right; right; right; right
      exact ⟨hp, fun a ha => by
        rw [key a ha]
        show chDir d a * psDir q a * chi8 a = chi8 a * chDir d a * psDir q a
        ring⟩

private theorem conductor_le_of_quadratic_squares {N M : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive)
    (h2 : χ ^ 2 = 1) (hM : M ∣ N) (hM0 : M ≠ 0)
    (hsq : ∀ t : ℤ, ∃ v : ZMod N, v ^ 2 = 1 + (M : ZMod N) * (t : ZMod N)) : N ≤ M := by
  haveI : NeZero M := ⟨hM0⟩
  have hf : χ.FactorsThrough M := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hM]
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective (u : ZMod N)
    have h1 : ((a : ℤ) : ZMod M) = ((1 : ℤ) : ZMod M) := by
      have h := congrArg (fun x : (ZMod M)ˣ => (x : ZMod M)) hu
      simp only [ZMod.unitsMap_val, Units.val_one] at h
      rw [← ha, ZMod.cast_intCast hM] at h
      simpa using h
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
    obtain ⟨t, ht⟩ := h1
    obtain ⟨v, hv⟩ := hsq (-t)
    have ha' : a = 1 + (M : ℤ) * (-t) := by linarith
    have huv : (u : ZMod N) = v ^ 2 := by
      rw [hv, ← ha, ha']; push_cast; ring
    have hvu : IsUnit v := by
      have : IsUnit (v ^ 2) := huv ▸ u.isUnit
      exact (isUnit_pow_iff two_ne_zero).mp this
    ext
    rw [MulChar.coe_toUnitHom, huv, map_pow, ← MulChar.pow_apply' χ two_ne_zero, h2,
      MulChar.one_apply hvu, Units.val_one]
  have hle : χ.conductor ≤ M := Nat.sInf_le hf
  rw [DirichletCharacter.isPrimitive_def] at hp
  omega

private theorem sq_eq_one_of_real {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hr : IsRealChar χ) : χ ^ 2 = 1 := by
  ext u
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
  have h1 : ‖χ (u : ZMod N)‖ = 1 := χ.unit_norm_eq_one u
  have h2 := hr (u : ZMod N)
  have h3 : χ (u : ZMod N) = (((χ (u : ZMod N)).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [h2]
  rw [h3, Complex.norm_real, Real.norm_eq_abs] at h1
  rw [h3, ← Complex.ofReal_pow, ← sq_abs, h1]
  simp

theorem not_sixteen_dvd_of_real {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive)
    (hr : IsRealChar χ) : ¬ 2 ^ 4 ∣ N := by
  have h2 := sq_eq_one_of_real χ hr
  rintro ⟨k, hk⟩
  have hN : N ≠ 0 := NeZero.ne N
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hN hk
  have hle : N ≤ 8 * k := by
    refine conductor_le_of_quadratic_squares χ hp h2 ⟨2, by rw [hk]; ring⟩ (mul_ne_zero (by norm_num) hk0) fun t => ?_
    refine ⟨1 + 4 * (k : ZMod N) * t, ?_⟩
    have h0 : (16 : ZMod N) * k = 0 := by
      have h := congrArg (Nat.cast : ℕ → ZMod N) hk
      rw [ZMod.natCast_self] at h
      push_cast at h
      linear_combination -h
    push_cast
    linear_combination (k * t ^ 2) * h0
  omega

private theorem dvd_eight_mul_ordCompl {N Q : ℕ} (hQ : Q ≠ 0) (h : N ∣ Q) (h16 : ¬ 2 ^ 4 ∣ N) :
    N ∣ 8 * ordCompl[2] Q := by
  have hN : N ≠ 0 := by rintro rfl; exact hQ (Nat.eq_zero_of_zero_dvd h)
  have h3 : N.factorization 2 ≤ 3 := by
    by_contra hc
    exact h16 ((pow_dvd_pow 2 (by omega)).trans (Nat.ordProj_dvd N 2))
  have h8 : 2 ^ N.factorization 2 ∣ 8 := pow_dvd_pow 2 h3
  calc N = 2 ^ N.factorization 2 * ordCompl[2] N := (Nat.ordProj_mul_ordCompl_eq_self N 2).symm
    _ ∣ 8 * ordCompl[2] Q := mul_dvd_mul h8 (Nat.ordCompl_dvd_ordCompl_of_dvd h 2)

theorem realClassE_holds (D : D7) : RealClassE D := by
  intro N _ χ hχ hreal
  by_cases hq : D.host.q ∣ N
  · exact Or.inr (Or.inl hq)
  by_cases hd : D.host.d ∣ N
  · exact Or.inr (Or.inr hd)
  left
  have h1 := level_dvd_condN D χ hχ
  have h2 : N ∣ D.host.QS * D.host.q :=
    ((D.host.hyp.2.1.coprime_iff_not_dvd.2 hd).symm).dvd_of_dvd_mul_right h1
  have h3 : N ∣ D.host.QS := ((D.host.hyp.1.coprime_iff_not_dvd.2 hq).symm).dvd_of_dvd_mul_right h2
  exact dvd_eight_mul_ordCompl D.host.QS_pos.ne' h3 (not_sixteen_dvd_of_real χ hχ.1 hreal)

theorem proposition_six_of_bounded_odd_moduli (eps c6 C7 C11 : ℝ) (B : ℕ) (h0 : 0 < eps) (h6 : 0 < c6) (h7 : 0 < C7) (h11 : 0 < C11) :
    ∃ c' x0 : ℝ, 0 < c' ∧ 1 < x0 ∧ ∀ x : ℝ, x0 ≤ x → ∀ (D : D7) (Cq : ℝ), oddQS D ≤ B →
      adm6 D Cq c6 → adm7 D C7 → adm11 D C11 →
      PropTwoSixThinScales D x eps c' := by
  obtain ⟨c', x0, hc', hx0, h⟩ := proposition_six_of_real_class_condition eps c6 C7 C11 B h0 h6 h7 h11
  exact ⟨c', x0, hc', hx0, fun x hx D Cq hodd a6 a7 a11 => h x hx D Cq hodd a6 a7 a11 (realClassE_holds D)⟩

theorem thin_set_family_of_admitted {eps : ℝ} (Fm : FamP eps) (h6 : FamilySixthHypothesis Fm) (h7 : adm7F Fm) (h11 : ComplementTwoFamily Fm) :
    ∃ c : ℝ, 0 < c ∧ ∃ x0 : ℝ, 1 < x0 ∧ ∀ x ≥ x0, ∀ i : Fm.Ix x, RealBoxE (Fm.D x i) →
      Real.log (NE (Fm.D x i) : ℝ) ≤ 8 * x ^ (eps / 5) * Real.log x ^ 2 → ThinE (Fm.D x i) x eps c := by
  obtain ⟨c, hc, x0, hx0, h⟩ := thin_set_family_of_conditions Fm h6 h7 h11
  exact ⟨c, hc, x0, hx0, fun x hx i => h x hx i (condE_holds _) (realClassE_holds _)⟩

theorem proposition_six_norm_family_of_admitted {eps : ℝ} (Fm : FamP eps) (h6 : FamilySixthHypothesis Fm) (h7 : adm7F Fm) (h11 : ComplementTwoFamily Fm) :
    FamilyPropTwoSixCongruenceForm Fm :=
  proposition_six_family_of_real_classes Fm h6 h7 h11 ⟨0, fun _ _ _ => realClassE_holds _⟩

theorem proposition_six_family_of_admitted {eps : ℝ} (Fm : FamP eps) (h6 : FamilySixthHypothesis Fm) (h7 : adm7F Fm) (h11 : ComplementTwoFamily Fm) :
    Conclusion6Family Fm := prop_two_six_family_of_congruence_form Fm (proposition_six_norm_family_of_admitted Fm h6 h7 h11)

end Formalism.MainNotions.ShortIntervalPrimes

end

noncomputable section

namespace Formalism.MainNotions.ShortIntervalPrimes

open Finset Filter Topology ArithmeticFunction MeasureTheory Formalism.MainNotions.GlobalTheoryTheory
open Br

theorem proposition_seven_remainder_quarter (D : Formalism.BasicNotions.D7) (x eps : ℝ) (h9 : adm9 D x eps) (h10 : adm10 D 1)
    (hm : 8 ≤ (D.R.m : ℝ) * x ^ eps) : TstarLogLowerBound D x eps (1 / 4) := by
  intro u
  have hX : 0 < (D.mem u).A.Xu := by
    unfold Formalism.BasicNotions.ColumnsAtT.Xu
    exact Real.rpow_pos_of_pos (div_pos (D.mem u).A.Dstar_pos (by exact_mod_cast (D.mem u).A.duStar_pos)) _
  have hG : 0 < (D.mem u).A.GamP := lt_trans zero_lt_one (D.mem u).A.one_lt_gammaP
  have hGp : 0 < (D.mem u).A.GamP ^ (-(2 : ℝ) / ((D.R.f : ℝ) * D.R.k)) := Real.rpow_pos_of_pos hG _
  have hT : (D.mem u).A.Tstar = (D.mem u).A.Xu * (D.mem u).A.GamP ^ (-(2 : ℝ) / ((D.R.f : ℝ) * D.R.k)) := rfl
  refine ⟨by rw [hT]; positivity, ?_⟩
  rw [hT, Real.log_mul hX.ne' hGp.ne', Real.log_rpow hG]
  have h9u := h9 u
  have h10u := h10 u
  have hlG : 0 < Real.log (D.mem u).A.GamP := Real.log_pos (D.mem u).A.one_lt_gammaP
  have hfk : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.k := by positivity
  have hterm : -2 ≤ -(2 : ℝ) / ((D.R.f : ℝ) * D.R.k) * Real.log (D.mem u).A.GamP := by
    rcases hfk.eq_or_lt with h0 | h0
    · rw [← h0]; simp
    · rw [div_mul_eq_mul_div, le_div_iff₀ h0]
      nlinarith
  linarith

theorem proposition_seven_remainder_family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h9 : proportionalityInputFamily Fm) (h10 : compactDualInputFamily Fm) :
    ∃ c : ℝ, 0 < c ∧ ∃ x0 : ℝ, 1 < x0 ∧ ∀ x ≥ x0, ∀ i : Fm.Ix x, TstarLogLowerBound (Fm.D x i) x eps c := by
  have heps : 0 ≤ eps := (fam_eps Fm).1.le
  obtain ⟨x9, -, h9⟩ := h9
  obtain ⟨x10, -, h10⟩ := h10 1 one_pos
  refine ⟨1 / 4, by norm_num, max (max x9 x10) (max 64 (Fm.x1 + 1)),
    lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans (le_max_right _ _)), ?_⟩
  intro x hx i
  have a9 : x9 ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have a10 : x10 ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have a64 : 64 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have a1 : Fm.x1 < x := lt_of_lt_of_le (by linarith) (((le_max_right _ _).trans (le_max_right _ _)).trans hx)
  refine proposition_seven_remainder_quarter _ x eps (h9 x a9 i) (h10 x a10 i) ?_
  have hm := (fam_sizes Fm x a1 i).2.1.1
  have hx0 : 0 < x := by linarith
  have hs8 : 8 ≤ Real.sqrt x := by
    apply Real.le_sqrt_of_sq_le; norm_num; linarith
  have e1 : Real.sqrt (x * x ^ (-(eps / 8))) = Real.sqrt x * x ^ (-(eps / 16)) := by
    rw [Real.sqrt_mul hx0.le, Real.sqrt_eq_rpow (x ^ (-(eps / 8))), ← Real.rpow_mul hx0.le]
    congr 2; ring
  have e2 : x ^ (-(eps / 100)) * (Real.sqrt x * x ^ (-(eps / 16))) * x ^ eps
      = Real.sqrt x * x ^ (-(eps / 100) + -(eps / 16) + eps) := by
    rw [Real.rpow_add hx0, Real.rpow_add hx0]; ring
  have h1 : 1 ≤ x ^ (-(eps / 100) + -(eps / 16) + eps) :=
    Real.one_le_rpow (by linarith) (by linarith)
  have hxe : 0 < x ^ eps := Real.rpow_pos_of_pos hx0 _
  calc (8 : ℝ) ≤ Real.sqrt x * 1 := by linarith
    _ ≤ Real.sqrt x * x ^ (-(eps / 100) + -(eps / 16) + eps) :=
        mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg x)
    _ = x ^ (-(eps / 100)) * Real.sqrt (x * x ^ (-(eps / 8))) * x ^ eps := by rw [e1, e2]
    _ ≤ ((Fm.D x i).R.m : ℝ) * x ^ eps := mul_le_mul_of_nonneg_right hm hxe.le

theorem second_admissible_holds (D : Formalism.BasicNotions.D7) : adm2 D (Real.log 4 + 4) := by
  intro u hu
  have hk : 1 ≤ ⌊u⌋₊ := Nat.le_floor (by simpa using hu)
  have hk0 : (0 : ℝ) < (⌊u⌋₊ : ℝ) := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ (⌊u⌋₊ : ℝ) := by exact_mod_cast hk
  have e : ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, abelian₂ n / n = Formalism.LogFactorialMertensBounds.A ⌊u⌋₊ := by
    unfold Formalism.LogFactorialMertensBounds.A; rw [Formalism.LogFactorialMertensBounds.Icc_one_eq_Ioc]
  rw [e]
  have h1 := Formalism.LogFactorialMertensBounds.mertens_upper _ hk
  have h2 := Formalism.LogFactorialMertensBounds.mertens_lower _ hk
  have h3 : Real.log (⌊u⌋₊ : ℝ) ≤ Real.log u := Real.log_le_log hk0 (Nat.floor_le (by linarith))
  have h4 : Real.log u ≤ Real.log (⌊u⌋₊ : ℝ) + Real.log 2 := by
    rw [← Real.log_mul hk0.ne' (by norm_num)]
    apply Real.log_le_log (by linarith)
    have := (Nat.lt_floor_add_one u).le
    linarith
  have h5 := Real.log_two_lt_d9
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]
  constructor <;> linarith

theorem subgroup_admissible_holds : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ D : Formalism.BasicNotions.D7, adm3 D c C := by
  obtain ⟨c, C, hc, h⟩ := Formalism.ZeroFreeDirichlet.siegelWalfisz 1 one_pos
  refine ⟨c, |C| + 2 * Real.exp (2 * c), hc, by positivity, ?_⟩
  intro D u hu
  have hu0 : 0 < u := by linarith
  have hE : 0 < Real.exp (-(c * Real.sqrt (Real.log u))) := Real.exp_pos _
  by_cases h3 : 3 ≤ u
  · have hq : ((1 : ℕ) : ℝ) ≤ Real.log u ^ (1 : ℝ) := by
      rw [Real.rpow_one, Nat.cast_one, Real.le_log_iff_exp_le hu0]
      have := Real.exp_one_lt_d9
      linarith
    have h1 := h 1 (1 : DirichletCharacter ℂ 1) u hu hq
    have e : Formalism.ZeroFreeDirichlet.psiChi (1 : DirichletCharacter ℂ 1) u - (if (1 : DirichletCharacter ℂ 1) = 1 then (u : ℂ) else 0)
        = ((psiCheb u - u : ℝ) : ℂ) := by
      unfold Formalism.ZeroFreeDirichlet.psiChi psiCheb
      have : ∀ n : ℕ, (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 :=
        fun n => MulChar.one_apply (isUnit_of_subsingleton _)
      simp only [this, mul_one, if_true]
      push_cast
      rfl
    rw [e, Complex.norm_real, Real.norm_eq_abs, neg_mul] at h1
    refine h1.trans ?_
    have : C ≤ |C| + 2 * Real.exp (2 * c) := by
      have := le_abs_self C
      have := Real.exp_pos (2 * c)
      linarith
    gcongr
  · push Not at h3
    have hp0 : 0 ≤ psiCheb u := Finset.sum_nonneg (fun n _ => ArithmeticFunction.vonMangoldt_nonneg)
    have hp3 : psiCheb u ≤ 3 * u := Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN.sum_vM_le hu0.le
    have habs : |psiCheb u - u| ≤ 2 * u := by
      rw [abs_le]; constructor <;> linarith
    have hl : Real.log u ≤ 4 := by
      have h1 : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hu0
      linarith
    have hs : Real.sqrt (Real.log u) ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt hl
    have hone : 1 ≤ Real.exp (2 * c) * Real.exp (-(c * Real.sqrt (Real.log u))) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    calc |psiCheb u - u| ≤ 2 * u * 1 := by linarith
      _ ≤ 2 * u * (Real.exp (2 * c) * Real.exp (-(c * Real.sqrt (Real.log u)))) :=
          mul_le_mul_of_nonneg_left hone (by positivity)
      _ ≤ (|C| + 2 * Real.exp (2 * c)) * u * Real.exp (-(c * Real.sqrt (Real.log u))) := by
          have : 0 ≤ |C| * u * Real.exp (-(c * Real.sqrt (Real.log u))) := by positivity
          nlinarith

theorem chebyshev_family_holds {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : FamilySecondHypothesis Fm :=
  ⟨Real.log 4 + 4, by have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith, fun _ _ _ => second_admissible_holds _⟩

theorem third_admissible_family_holds {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : FamilyAdmittedLemmaThree Fm := by
  obtain ⟨c, C, hc, hC, h⟩ := subgroup_admissible_holds
  exact ⟨c, C, hc, hC, fun _ _ _ => h _⟩

lemma kronecker_two_eq_chi_eight_int (D : ℤ) : kron2 D = ZMod.χ₈ (D : ZMod 8) := by
  have h8 : (D : ZMod 8) = ((D % 8 : ℤ) : ZMod 8) := by
    have := ZMod.intCast_mod D 8
    exact_mod_cast this.symm
  have h2 : D % 2 = (D % 8) % 2 := by omega
  have h88 : D % 8 = (D % 8) % 8 := by omega
  have h0 := Int.emod_nonneg D (show (8 : ℤ) ≠ 0 by norm_num)
  have h1 := Int.emod_lt_of_pos D (show (0 : ℤ) < 8 by norm_num)
  unfold kron2
  rw [h8, h2, h88]
  generalize D % 8 = r at *
  interval_cases r <;> simp <;> decide

lemma kronSym_eq_jacobi (q n : ℕ) (hq : q % 4 = 3) (hn : n ≠ 0) :
    kronSym (-(q : ℤ)) n = jacobiSym (n : ℤ) q := by
  unfold kronSym
  set v := n.factorization 2 with hv
  set m := n / 2 ^ v with hm
  have hnm : 2 ^ v * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hodd : Odd m := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact Nat.not_dvd_ordCompl Nat.prime_two hn
  have e1 : jacobiSym (n : ℤ) q = jacobiSym 2 q ^ v * jacobiSym (m : ℤ) q := by
    rw [← hnm]; push_cast
    rw [jacobiSym.mul_left, jacobiSym.pow_left]
  rw [e1, Formalism.HermitianLattices.GL2a2.kronecker_odd q m hq hodd, kronecker_two_eq_chi_eight_int, Formalism.HermitianLattices.GL2a2.kronecker_two q hq, mul_comm]

lemma zz_eq (x : ℝ) : zz x = x ^ (400 : ℝ) := by
  unfold zz; rw [← Real.rpow_natCast]; norm_num

def MuBound (x eps C' c' : ℝ) : Prop :=
  ∀ m0 : ℕ, 0 < m0 → 8 ∣ m0 →
    (∀ p : ℕ, p.Prime → p ∣ m0 → (p : ℝ) ≤ x ^ (eps / 5) ∨ zz x < p) →
  ∀ a0 : ℤ, IsCoprime a0 (m0 : ℤ) → a0 % 4 = 3 →
  ∀ X : ℝ, 0 < X → (1 / 4) * Real.log x ^ 2 * Real.log m0 ≤ Real.log X →
    x ^ (eps / 6) ≤ Real.log X →
  ∃ nStar : ℕ, ∀ n n' : ℕ, n ∈ Finset.Icc 1 ⌊zz x⌋₊ → n' ∈ Finset.Icc 1 ⌊zz x⌋₊ →
    IsPrimePow n → IsPrimePow n' → Formalism.HermitianLattices.GL2PrimeSums.outPart m0 (n * n') ≠ 1 →
    Formalism.HermitianLattices.GL2PrimeSums.outPart m0 (n * n') ≠ nStar →
    |(∑ q ∈ PPset m0 a0 X, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)) / ((PPset m0 a0 X).card : ℝ)| ≤
      C' * Real.exp (-c' * Real.log x ^ 2)

theorem second_bound_of_chebyshev_and_means (eps C' c' : ℝ) (h0 : 0 < eps) (h1 : eps < 1) (hC' : 0 < C') (hc' : 0 < c')
    (D0 : Formalism.BasicNotions.D7) (c1 : ℝ) (hch : adm1 D0 c1) :
    ∃ C x0 : ℝ, 0 < C ∧ 1 < x0 ∧ ∀ x : ℝ, x0 ≤ x → MuBound x eps C' c' → Conclusion4b x eps C := by
  have cheb : ∀ y : ℝ, 0 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n ≤ 2 * y := by
    intro y hy
    by_cases h : 1 ≤ y
    · exact hch.2 y h
    · push Not at h
      rw [Nat.floor_eq_zero.2 h]; simpa using hy
  obtain ⟨x₀, C, core⟩ := Formalism.HermitianLattices.GL2PrimeSums.central_sum_estimate cheb eps h0 h1 C' c' hC' hc'
  have hev : ∀ᶠ x : ℝ in atTop, 800 * Real.log x ≤ x ^ (eps / 6) := by
    have := (isLittleO_log_rpow_atTop (show 0 < eps / 6 by positivity)).bound (show (0 : ℝ) < 1 / 800 by norm_num)
    filter_upwards [this, eventually_ge_atTop 1] with x hx hx1
    rw [Real.norm_of_nonneg (Real.log_nonneg hx1), Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hx
    linarith
  obtain ⟨x1, hx1⟩ := eventually_atTop.1 hev
  refine ⟨max C 1, max (max x₀ x1) 2, by positivity, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro x hx hmu m0 g1 g2 g3 a0 g4 g5 X g6 g7 g8 ka g9 g10 g11
  have a0' : x₀ ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have a1' : x1 ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have a2' : 2 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hCx : C * x * Real.log x ≤ max C 1 * x * Real.log x := by
    have := le_max_left C 1
    gcongr
  by_cases hne : (PPset m0 a0 X).Nonempty
  · obtain ⟨nStar, hst⟩ := hmu m0 g1 g2 g3 a0 g4 g5 X g6 g7 g8
    have hmem : ∀ q ∈ PPset m0 a0 X, q.Prime ∧ q % 4 = 3 ∧ x ^ (400 : ℝ) < q := by
      intro q hq
      unfold PPset at hq
      rw [Finset.mem_filter] at hq
      obtain ⟨-, hp, hcong, hsq⟩ := hq
      refine ⟨hp, ?_, ?_⟩
      · have h4 : (q : ℤ) ≡ a0 [ZMOD 4] := hcong.of_dvd (by
          have : (8 : ℤ) ∣ (m0 : ℤ) := by exact_mod_cast g2
          exact (show (4 : ℤ) ∣ 8 by norm_num).trans this)
        have h4' : (q : ℤ) % 4 = 3 := by rw [← g5]; exact h4
        omega
      · refine lt_of_le_of_lt ?_ hsq
        apply Real.le_sqrt_of_sq_le
        rw [← Real.log_le_log_iff (by positivity) g6, Real.log_pow, Real.log_rpow hx0]
        have := hx1 x a1'
        push_cast
        linarith
    have key := core x a0' m0 (PPset m0 a0 X) ka nStar g2 g1 (by simpa only [zz_eq] using g3) hne hmem g10 g11 g9
      (by simpa only [zz_eq] using hst)
    refine le_trans (le_of_eq ?_) (key.trans hCx)
    congr 1
    apply Finset.sum_congr rfl
    intro q hq
    congr 2
    unfold Formalism.HermitianLattices.GL2PrimeSums.sqSum
    rw [zz_eq]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Icc.1 hn).1; omega
    unfold kron
    rw [kronSym_eq_jacobi q n (hmem q hq).2.1 hn0]
    rfl
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp only [Finset.sum_empty, zero_div]
    positivity

theorem lemma_two_four_family_of_chebyshev_Q4_means {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h1 : familyUnitInput Fm) (h8 : FamilyTemperatureAsymptotic Fm)
    (hmu : ∃ C' c' : ℝ, 0 < C' ∧ 0 < c' ∧ ∃ x0 : ℝ, ∀ x ≥ x0, MuBound x eps C' c') : SlopeLemmaFamily Fm := by
  by_cases hE : ∃ x > 1, Nonempty (Fm.Ix x)
  · obtain ⟨xx, hxx, ⟨ii⟩⟩ := hE
    obtain ⟨c1, -, hch⟩ := h1
    obtain ⟨C', c', hC', hc', xm, hm⟩ := hmu
    obtain ⟨C, x0, hC, hx0, h⟩ := second_bound_of_chebyshev_and_means eps C' c' (fam_eps Fm).1 (fam_eps Fm).2 hC' hc' _ c1 (hch xx hxx ii)
    exact lemma_two_four_family_of_Q4_mean_square (fam_eps Fm).1 (fam_eps Fm).2 Fm h8 ⟨C, hC, max x0 xm, lt_of_lt_of_le hx0 (le_max_left _ _),
      fun x hx _ => h x ((le_max_left _ _).trans hx) (hm x ((le_max_right _ _).trans hx))⟩
  · exact ⟨1, one_pos, 2, by norm_num, fun x hx i => absurd ⟨x, by linarith, ⟨i⟩⟩ hE⟩

end Formalism.MainNotions.ShortIntervalPrimes

end

noncomputable section

namespace Formalism.MainNotions.ShortIntervalPrimes

open Finset Filter Topology ArithmeticFunction MeasureTheory Formalism.MainNotions.GlobalTheoryTheory
open Br

theorem lemma_three_of_Q4_growth_bound (C0 Cr cr cQ cQ' : ℝ) (hC0 : 0 < C0) (hCr : 0 < Cr) (hcr : 0 < cr) (hcQ : 0 < cQ)
    (hcQ' : 0 < cQ') :
    ∃ C0' c1 c2 : ℝ, 0 < C0' ∧ 0 < c1 ∧ 0 < c2 ∧ ∀ (D : Formalism.BasicNotions.D7) (c1' : ℝ), adm8 D C0 Cr cr cQ c1' →
      GrBound D.host.K → PointsLemma D cQ' C0' Cr cr c1 c2 := by
  obtain ⟨C0', c1, c2, p1, p2, p3, h⟩ := lemma_two_three_of_Q4_field_bounds C0 Cr cr cQ cQ' hC0 hCr hcr hcQ hcQ'
  exact ⟨C0', c1, c2, p1, p2, p3, fun D c1' ha hG => h D c1' ha hG (deg2Bound_K D)⟩

theorem lemma_two_three_family_of_Q4_galois_bound {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h8 : FamilyTemperatureAsymptotic Fm)
    (hK : ∀ x > 1, ∀ i : Fm.Ix x, GrBound (Fm.D x i).host.K) : Conclusion3Family Fm :=
  lemma_two_three_family_of_Q4_field_bounds Fm h8 (fun x hx i => ⟨hK x hx i, deg2Bound_K _⟩)

theorem stmtF_of_rest {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (h : AdmF Fm → Conclusion3Family Fm ∧ SlopeLemmaFamily Fm ∧ SlopeLossFamily Fm ∧
      (∀ C c : ℝ, 0 < C → 0 < c → ∃ x0 : ℝ, 1 < x0 ∧ ∀ x ≥ x0, ∀ i : Fm.Ix x, division_rows_rational_lattice (Fm.D x i) x eps C c) ∧
      FamilyAuxiliaryPrimesBound Fm) : KudlaFamilyStatement Fm := by
  intro hA
  obtain ⟨h3, h4, h5, h7, h8⟩ := h hA
  obtain ⟨-, -, -, -, -, a6, a7, -, a9, a10, a11⟩ := hA
  exact ⟨proposition_eleven_one_family Fm, lemma_two_two_family_of_admitted Fm a6 a7 a11, h3, h4, h5, proposition_six_family_of_admitted Fm a6 a7 a11,
    ⟨h7, proposition_seven_remainder_family Fm a9 a10⟩, h8, proposition_six_norm_family_of_admitted Fm a6 a7 a11⟩

theorem stmtF_of_open {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (hK : ∀ x > 1, ∀ i : Fm.Ix x, GrBound (Fm.D x i).host.K)
    (hmu : ∃ C' c' : ℝ, 0 < C' ∧ 0 < c' ∧ ∃ x0 : ℝ, ∀ x ≥ x0, MuBound x eps C' c')
    (h5 : AdmF Fm → SlopeLossFamily Fm)
    (h7 : AdmF Fm → ∀ C c : ℝ, 0 < C → 0 < c →
      ∃ x0 : ℝ, 1 < x0 ∧ ∀ x ≥ x0, ∀ i : Fm.Ix x, division_rows_rational_lattice (Fm.D x i) x eps C c)
    (h8 : AdmF Fm → FamilyAuxiliaryPrimesBound Fm) : KudlaFamilyStatement Fm := by
  refine stmtF_of_rest Fm (fun hA => ?_)
  have hA' := hA
  obtain ⟨a1, -, -, -, -, -, -, a8, -, -, -⟩ := hA'
  exact ⟨lemma_two_three_family_of_Q4_galois_bound Fm a8 hK, lemma_two_four_family_of_chebyshev_Q4_means Fm a1 a8 hmu, h5 hA, h7 hA, h8 hA⟩

end Formalism.MainNotions.ShortIntervalPrimes

end
