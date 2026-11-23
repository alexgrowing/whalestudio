import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExpSumBoundsStatement
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

noncomputable section

namespace GlobalTheory.Hk.RealChar

def kerW (y w : ℝ) : ℝ := Real.exp (-(y / w)) * Real.exp (-w) / w

def besW (y : ℝ) : ℝ := ∫ w in Set.Ioi (0 : ℝ), kerW y w

lemma kerW_pos (y : ℝ) {w : ℝ} (hw : 0 < w) : 0 < kerW y w := by
  unfold kerW; positivity

lemma kerW_le {y w : ℝ} (hy : 0 < y) (hw : 0 < w) :
    kerW y w ≤ 6 / y ^ 3 * (Real.exp (-w) * w ^ ((3 : ℝ) - 1)) := by
  have h := Real.pow_div_factorial_le_exp (y / w) (by positivity) 3
  have h3 : w ^ ((3 : ℝ) - 1) = w ^ 2 := by
    rw [show (3 : ℝ) - 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h1 : Real.exp (-(y / w)) ≤ 6 * w ^ 3 / y ^ 3 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
    refine le_trans (le_of_eq ?_) h
    simp only [Nat.factorial]
    field_simp
    norm_num
  rw [h3]
  unfold kerW
  calc Real.exp (-(y / w)) * Real.exp (-w) / w ≤ 6 * w ^ 3 / y ^ 3 * Real.exp (-w) / w := by
        gcongr
    _ = _ := by field_simp

lemma measurable_kerW (y : ℝ) : Measurable (kerW y) := by
  unfold kerW; fun_prop

lemma integrableOn_kerW {y : ℝ} (hy : 0 < y) : IntegrableOn (kerW y) (Set.Ioi 0) := by
  refine Integrable.mono' ((Real.GammaIntegral_convergent (s := 3) (by norm_num)).const_mul (6 / y ^ 3))
    (measurable_kerW y).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun w hw => ?_)
  rw [Real.norm_of_nonneg (kerW_pos y hw).le]
  exact kerW_le hy hw

lemma besW_nonneg (y : ℝ) : 0 ≤ besW y :=
  setIntegral_nonneg measurableSet_Ioi fun _ hw => (kerW_pos y hw).le

lemma besW_le : ∃ G : ℝ, 0 ≤ G ∧ ∀ y : ℝ, 0 < y → besW y ≤ G / y ^ 3 := by
  refine ⟨6 * ∫ w in Set.Ioi (0 : ℝ), Real.exp (-w) * w ^ ((3 : ℝ) - 1), ?_, fun y hy => ?_⟩
  · refine mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Ioi fun w hw => ?_)
    have : 0 < w := hw
    positivity
  · calc besW y ≤ ∫ w in Set.Ioi (0 : ℝ), 6 / y ^ 3 * (Real.exp (-w) * w ^ ((3 : ℝ) - 1)) :=
          setIntegral_mono_on (integrableOn_kerW hy)
            ((Real.GammaIntegral_convergent (s := 3) (by norm_num)).const_mul (6 / y ^ 3))
            measurableSet_Ioi fun w hw => kerW_le hy hw
      _ = _ := by rw [integral_const_mul]; ring

lemma besW_one_le {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) : besW 1 ≤ besW v := by
  refine setIntegral_mono_on (integrableOn_kerW one_pos) (integrableOn_kerW hv)
    measurableSet_Ioi fun w hw => ?_
  have : 0 < w := hw
  unfold kerW
  gcongr

lemma besW_one_pos : 0 < besW 1 := by
  unfold besW
  rw [setIntegral_pos_iff_support_of_nonneg_ae ?_ (integrableOn_kerW one_pos)]
  · have : Function.support (kerW 1) ∩ Set.Ioi 0 = Set.Ioi 0 :=
      Set.inter_eq_right.2 fun w hw => (kerW_pos 1 hw).ne'
    rw [this]; simp
  · exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun w hw => (kerW_pos 1 hw).le)

lemma scale_eq (y : ℝ) {n w : ℝ} (hn : 0 < n) (hw : 0 < w) :
    Real.exp (-(y / w)) * Real.exp (-(w * n)) / w = n * kerW (y * n) (w * n) := by
  unfold kerW
  rw [mul_div_mul_right _ _ hn.ne']
  field_simp

lemma scale_integrable {y n : ℝ} (hy : 0 < y) (hn : 0 < n) :
    IntegrableOn (fun w => Real.exp (-(y / w)) * Real.exp (-(w * n)) / w) (Set.Ioi 0) := by
  have h : IntegrableOn (fun w => kerW (y * n) (w * n)) (Set.Ioi 0) := by
    rw [integrableOn_Ioi_comp_mul_right_iff (kerW (y * n)) 0 hn, zero_mul]
    exact integrableOn_kerW (by positivity)
  exact IntegrableOn.congr_fun (h.const_mul n) (fun w hw => (scale_eq y hn hw).symm) measurableSet_Ioi

lemma scale_integral (y : ℝ) {n : ℝ} (hn : 0 < n) :
    ∫ w in Set.Ioi (0 : ℝ), Real.exp (-(y / w)) * Real.exp (-(w * n)) / w = besW (y * n) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun w hw => scale_eq y hn hw), integral_const_mul,
    integral_comp_mul_right_Ioi (kerW (y * n)) 0 hn, zero_mul, smul_eq_mul]
  unfold besW
  field_simp

def th (a : ℕ → ℝ) (t : ℝ) : ℝ := ∑' n : ℕ, a n * Real.exp (-(t * n))

lemma measurable_th (a : ℕ → ℝ) : Measurable (th a) := by
  unfold th
  exact Measurable.tsum fun n => by fun_prop

lemma summable_th {a : ℕ → ℝ} {D : ℝ} (ha : ∀ n, |a n| ≤ D * n) {t : ℝ} (ht : 0 < t) :
    Summable fun n : ℕ => ‖a n * Real.exp (-(t * n))‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((Real.summable_pow_mul_exp_neg_nat_mul 1 ht).mul_left D)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le, pow_one, ← mul_assoc, neg_mul]
  gcongr
  exact ha n

lemma hasSum_pairs {a b : ℕ → ℝ} {D : ℝ} (ha : ∀ n, |a n| ≤ D * n) (hb : ∀ n, |b n| ≤ D * n)
    {v : ℝ} (hv : 0 < v) :
    HasSum (fun p : ℕ × ℕ => a p.1 * b p.2 * besW (v * p.1 * p.2))
      (∫ w in Set.Ioi (0 : ℝ), th a (v / w) * th b w / w) := by
  have a0 : a 0 = 0 := by simpa using ha 0
  have b0 : b 0 = 0 := by simpa using hb 0
  have hD : 0 ≤ D := by simpa using (abs_nonneg _).trans (ha 1)
  set f : ℕ × ℕ → ℝ → ℝ := fun p w =>
    a p.1 * b p.2 * (Real.exp (-(v * p.1 / w)) * Real.exp (-(w * p.2)) / w) with hf
  have hz : ∀ p : ℕ × ℕ, a p.1 * b p.2 = 0 ∨ (0 < p.1 ∧ 0 < p.2) := by
    rintro ⟨m, n⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · left; simp [a0]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · left; simp [b0]
    exact Or.inr ⟨hm, hn⟩
  have hint : ∀ p, Integrable (f p) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro p
    rcases hz p with h | ⟨h1, h2⟩
    · simp [hf, h]
    · exact (scale_integrable (y := v * p.1) (n := p.2) (by positivity) (by positivity)).const_mul _
  have hval : ∀ p, ∫ w in Set.Ioi (0 : ℝ), f p w = a p.1 * b p.2 * besW (v * p.1 * p.2) := by
    intro p
    rcases hz p with h | ⟨h1, h2⟩
    · simp [hf, h]
    · simp only [hf]
      rw [integral_const_mul, scale_integral (v * p.1) (n := p.2) (by positivity)]
  obtain ⟨G, hG0, hG⟩ := besW_le
  have hs2 : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 := Real.summable_one_div_nat_pow.2 (by norm_num)
  have hsum : Summable fun p => ∫ w in Set.Ioi (0 : ℝ), ‖f p w‖ := by
    refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun w => norm_nonneg _) (fun p => ?_)
      ((hs2.mul_of_nonneg hs2 (fun n => by positivity) (fun n => by positivity)).mul_left
        (D * D * G / v ^ 3))
    rcases hz p with h | ⟨h1, h2⟩
    · simp only [hf, h, zero_mul, norm_zero, integral_zero]
      positivity
    · have e : ∫ w in Set.Ioi (0 : ℝ), ‖f p w‖ = |a p.1| * |b p.2| * besW (v * p.1 * p.2) := by
        rw [← scale_integral (v * p.1) (n := p.2) (by positivity), ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
        have : 0 < w := hw
        simp only [hf]
        rw [norm_mul, norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ Real.exp (-(v * p.1 / w)) * Real.exp (-(w * p.2)) / w)]
        rfl
      rw [e]
      have h1' : (0 : ℝ) < p.1 := by positivity
      have h2' : (0 : ℝ) < p.2 := by positivity
      calc |a p.1| * |b p.2| * besW (v * p.1 * p.2)
          ≤ (D * p.1) * (D * p.2) * (G / (v * p.1 * p.2) ^ 3) := by
            gcongr
            · exact besW_nonneg _
            · exact ha _
            · exact hb _
            · exact hG _ (by positivity)
        _ = _ := by field_simp
  have H := hasSum_integral_of_summable_integral_norm hint hsum
  simp only [hval] at H
  suffices e : ∫ w in Set.Ioi (0 : ℝ), th a (v / w) * th b w / w
      = ∫ w in Set.Ioi (0 : ℝ), ∑' p, f p w by rw [e]; exact H
  refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
  have hw' : 0 < w := hw
  simp only [th]
  rw [tsum_mul_tsum_of_summable_norm (summable_th ha (by positivity)) (summable_th hb hw'),
    ← tsum_div_const]
  refine tsum_congr fun p => ?_
  simp only [hf]
  rw [show v / w * (p.1 : ℝ) = v * p.1 / w by ring]
  ring

lemma besW_le_integral {a b : ℕ → ℝ} {D : ℝ} (ha : ∀ n, |a n| ≤ D * n) (hb : ∀ n, |b n| ≤ D * n)
    (a1 : a 1 = 1) (b1 : b 1 = 1)
    (hr : ∀ n : ℕ, 0 ≤ ∑ p ∈ n.divisorsAntidiagonal, a p.1 * b p.2) {v : ℝ} (hv : 0 < v) :
    besW v ≤ ∫ w in Set.Ioi (0 : ℝ), th a (v / w) * th b w / w := by
  have a0 : a 0 = 0 := by simpa using ha 0
  have b0 : b 0 = 0 := by simpa using hb 0
  have H := (hasSum_pairs ha hb hv).tsum_fiberwise (fun p : ℕ × ℕ => p.1 * p.2)
  have e : ∀ n : ℕ, ∑' p : (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {n},
      a p.val.1 * b p.val.2 * besW (v * p.val.1 * p.val.2)
      = (∑ p ∈ n.divisorsAntidiagonal, a p.1 * b p.2) * besW (v * n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · have : ∀ p : (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {0},
          a p.val.1 * b p.val.2 * besW (v * p.val.1 * p.val.2) = 0 := by
        rintro ⟨⟨m, n⟩, hp⟩
        have hp' : m * n = 0 := hp
        rcases Nat.mul_eq_zero.1 hp' with rfl | rfl <;> simp [a0, b0]
      simp [this]
    · rw [show (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {n} = n.divisorsAntidiagonal by ext; simp [hn],
        Finset.tsum_subtype' n.divisorsAntidiagonal
          fun p => a p.1 * b p.2 * besW (v * p.1 * p.2), Finset.sum_mul]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [← (Nat.mem_divisorsAntidiagonal.1 hp).1, Nat.cast_mul, mul_assoc v]
  simp only [e] at H
  have := le_hasSum H 1 fun n _ => mul_nonneg (hr n) (besW_nonneg _)
  simpa [a1, b1] using this

def wt (w : ℝ) : ℝ := min w (1 / w) / (Real.sqrt w * w)

lemma wt_nonneg {w : ℝ} (hw : 0 < w) : 0 ≤ wt w := by
  unfold wt; positivity

lemma integrableOn_wt : IntegrableOn wt (Set.Ioi 0) := by
  have hm : Measurable wt := by unfold wt; fun_prop
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · refine Integrable.mono' (intervalIntegral.intervalIntegrable_rpow' (r := -(1 / 2)) (a := 0) (b := 1)
      (by norm_num)).1 hm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun w hw => ?_)
    have h0 : 0 < w := hw.1
    rw [Real.norm_of_nonneg (wt_nonneg h0), Real.rpow_neg h0.le, ← Real.sqrt_eq_rpow]
    have hs : 0 < Real.sqrt w := Real.sqrt_pos.2 h0
    unfold wt
    calc min w (1 / w) / (Real.sqrt w * w) ≤ w / (Real.sqrt w * w) := by
          gcongr; exact min_le_left _ _
      _ = _ := by field_simp
  · refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) one_pos)
      hm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun w hw => ?_)
    have h1 : 1 < w := hw
    have h0 : 0 < w := by linarith
    rw [Real.norm_of_nonneg (wt_nonneg h0), Real.rpow_neg h0.le, Real.rpow_two]
    have hs : 1 ≤ Real.sqrt w := Real.one_le_sqrt.2 h1.le
    unfold wt
    calc min w (1 / w) / (Real.sqrt w * w) ≤ (1 / w) / (1 * w) := by
          gcongr; exact min_le_right _ _
      _ = _ := by field_simp

lemma min_le_sqrt {u : ℝ} (hu : 0 < u) : min u (1 / u) ≤ Real.sqrt u := by
  rcases le_total u 1 with h | h
  · refine (min_le_left _ _).trans (Real.le_sqrt_of_sq_le ?_)
    nlinarith
  · exact (min_le_right _ _).trans (((div_le_one hu).2 h).trans (Real.one_le_sqrt.2 h))

lemma integrableOn_of_bounds {Q : ℝ → ℝ} (hm : Measurable Q) {E E' : ℝ} (hE : 0 ≤ E)
    (h1 : ∀ t, 0 < t → |Q t| ≤ E * min t (1 / t))
    (h2 : ∀ t, 1 ≤ t → |Q t| ≤ E' * Real.exp (-(t / 2))) : IntegrableOn Q (Set.Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · refine Integrable.mono' (g := fun _ => E) (integrableOn_const (by simp)) hm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun w hw => ?_)
    refine (h1 w hw.1).trans ?_
    exact mul_le_of_le_one_right hE ((min_le_left _ _).trans hw.2)
  · refine Integrable.mono' ((exp_neg_integrableOn_Ioi 1 (b := 1 / 2) (by norm_num)).const_mul E')
      hm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun w hw => ?_)
    refine (h2 w (le_of_lt hw)).trans (le_of_eq ?_)
    congr 2; ring

lemma integral_le {P Q : ℝ → ℝ} (hP : Measurable P) (hQ : Measurable Q) {ρ E : ℝ} (hE : 0 ≤ E)
    (h1 : ∀ t, 0 < t → |P t - ρ / t| ≤ E * min t (1 / t))
    (h2 : ∀ t, 0 < t → |Q t| ≤ E * min t (1 / t)) (hi : IntegrableOn Q (Set.Ioi 0))
    {v : ℝ} (hv : 0 < v) :
    ∫ w in Set.Ioi (0 : ℝ), P (v / w) * Q w / w ≤
      ρ / v * (∫ w in Set.Ioi (0 : ℝ), Q w) + E ^ 2 * Real.sqrt v * ∫ w in Set.Ioi (0 : ℝ), wt w := by
  set R : ℝ → ℝ := fun w => (P (v / w) - ρ / (v / w)) * Q w / w with hR
  have hRm : Measurable R := by simp only [hR]; fun_prop
  have hRb : ∀ w ∈ Set.Ioi (0 : ℝ), |R w| ≤ E ^ 2 * Real.sqrt v * wt w := by
    intro w hw
    have h0 : 0 < w := hw
    have hs : 0 < Real.sqrt w := Real.sqrt_pos.2 h0
    simp only [hR]
    rw [abs_div, abs_mul, abs_of_pos h0]
    have e1 : |P (v / w) - ρ / (v / w)| ≤ E * (Real.sqrt v / Real.sqrt w) := by
      refine (h1 _ (by positivity)).trans ?_
      rw [← Real.sqrt_div hv.le]
      gcongr
      exact min_le_sqrt (by positivity)
    calc _ ≤ E * (Real.sqrt v / Real.sqrt w) * (E * min w (1 / w)) / w := by
          gcongr
          exact h2 w h0
      _ = _ := by unfold wt; field_simp
  have hw := integrableOn_wt.const_mul (E ^ 2 * Real.sqrt v)
  have hRi : IntegrableOn R (Set.Ioi 0) :=
    Integrable.mono' hw hRm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hRb))
  have e : ∫ w in Set.Ioi (0 : ℝ), P (v / w) * Q w / w
      = ∫ w in Set.Ioi (0 : ℝ), (ρ / v * Q w + R w) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
    have h0 : 0 < w := hw
    simp only [hR]
    field_simp
    ring
  rw [e, integral_add (hi.const_mul _) hRi, integral_const_mul, ← integral_const_mul (E ^ 2 * Real.sqrt v)]
  gcongr ?_ + ?_
  · exact le_rfl
  · exact setIntegral_mono_on hRi hw measurableSet_Ioi fun w hw => (le_abs_self _).trans (hRb w hw)

def bRe (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (n : ℕ) : ℝ := ∑ g, (χ g).re * 𝓕.a g n

lemma chi_real {𝓕 : LFam} {χ : AddChar 𝓕.G ℂ} (h : χ * χ = 1) (g : 𝓕.G) :
    χ g = 1 ∨ χ g = -1 := by
  have : χ g * χ g = 1 := by
    have := DFunLike.congr_fun h g
    simpa using this
  exact mul_self_eq_one_iff.1 this

lemma aChi_eq {𝓕 : LFam} {χ : AddChar 𝓕.G ℂ} (h : χ * χ = 1) (n : ℕ) :
    𝓕.aChi χ n = (bRe 𝓕 χ n : ℂ) := by
  unfold LFam.aChi bRe
  push_cast
  refine Finset.sum_congr rfl fun g _ => ?_
  rcases chi_real h g with e | e <;> simp [e]

lemma a_le (𝓕 : LFam) (g : 𝓕.G) (n : ℕ) : 𝓕.a g n ≤ 14 * n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [𝓕.a_zero]
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := (abs_le.1 (𝓕.count g n h1)).2
  rw [Nat.floor_natCast] at h
  have h2 : 𝓕.a g n ≤ ∑ m ∈ Finset.Icc 1 n, 𝓕.a g m :=
    Finset.single_le_sum (fun m _ => 𝓕.a_nonneg g m) (Finset.mem_Icc.2 ⟨hn, le_rfl⟩)
  have h3 : Real.sqrt n ≤ n := Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
  have h4 : 𝓕.κ * n ≤ 4 * n := mul_le_mul_of_nonneg_right 𝓕.κ_le (by positivity)
  linarith

lemma bRe_le {𝓕 : LFam} {χ : AddChar 𝓕.G ℂ} (h : χ * χ = 1) (n : ℕ) :
    |bRe 𝓕 χ n| ≤ (Fintype.card 𝓕.G * 14 : ℝ) * n := by
  unfold bRe
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (14 * n : ℝ) fun g _ => ?_).trans (le_of_eq ?_)
  · rw [abs_mul, abs_of_nonneg (𝓕.a_nonneg g n)]
    rcases chi_real h g with e | e <;> simpa [e] using a_le 𝓕 g n
  · simp [mul_assoc]

lemma bRe_one (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) : bRe 𝓕 χ 1 = 1 := by
  unfold bRe
  rw [Finset.sum_eq_single 0 (fun g _ hg => by simp [𝓕.a_one_ne g hg]) (by simp)]
  simp [𝓕.a_one]

lemma th_eq {𝓕 : LFam} {χ : AddChar 𝓕.G ℂ} (h : χ * χ = 1) (t : ℝ) :
    ∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ) = (th (bRe 𝓕 χ) t : ℂ) := by
  unfold th
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [aChi_eq h, Complex.ofReal_mul]

theorem norm_F_one_ge : ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ), χ * χ = 1 →
    c / 𝓕.B ^ A ≤ ‖𝓕.F χ 1‖ := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.T.tsum_exp_mul_aChi_bounds
  set K := ∫ w in Set.Ioi (0 : ℝ), wt w with hK
  have hK0 : 0 ≤ K := setIntegral_nonneg measurableSet_Ioi fun w hw => wt_nonneg hw
  have hw0 := besW_one_pos
  set w0 := besW 1 with hw0def
  set δ := min 1 (w0 / (2 * (C ^ 2 * K + 1))) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : C ^ 2 * K * δ ≤ w0 / 2 := by
    have h1 : δ ≤ w0 / (2 * (C ^ 2 * K + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  refine ⟨((45 : ℕ) : ℝ), min 1 (δ ^ 2 * w0 / 8), by norm_num, by positivity, fun 𝓕 χ hχ => ?_⟩
  rw [Real.rpow_natCast]
  have hB := 𝓕.B_ge
  have hB1 : 1 ≤ 𝓕.B := by linarith
  have hB0 : 0 < 𝓕.B := by linarith
  have hκ : 0 < 𝓕.κ := lt_of_lt_of_le (by positivity) 𝓕.κ_ge
  have hcard : (1 : ℝ) ≤ Fintype.card 𝓕.G := by exact_mod_cast Fintype.card_pos
  by_cases h1 : χ = 1
  · have e : 𝓕.F χ 1 = ((𝓕.κ * Fintype.card 𝓕.G : ℝ) : ℂ) := by
      simp [LFam.F, LFam.res, h1]
    rw [e, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    calc min 1 (δ ^ 2 * w0 / 8) / 𝓕.B ^ 45 ≤ 1 / 𝓕.B := by
          gcongr
          · exact min_le_left _ _
          · exact le_self_pow₀ hB1 (by norm_num)
      _ ≤ 𝓕.κ := 𝓕.κ_ge
      _ ≤ _ := le_mul_of_one_le_right hκ.le hcard
  have h11 : (1 : AddChar 𝓕.G ℂ) * 1 = 1 := mul_one _
  set ρ := 𝓕.κ * Fintype.card 𝓕.G with hρ
  have hP : ∀ t, 0 < t → |th (bRe 𝓕 1) t - ρ / t| ≤ C * 𝓕.B ^ 11 * min t (1 / t) := by
    intro t ht
    have := ((H 𝓕 1).1 t ht).2
    rw [th_eq h11, LFam.res, if_pos rfl, ← Complex.ofReal_div, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  have hQ : ∀ t, 0 < t → |th (bRe 𝓕 χ) t| ≤ C * 𝓕.B ^ 11 * min t (1 / t) := by
    intro t ht
    have := ((H 𝓕 χ).1 t ht).2
    rw [th_eq hχ, LFam.res, if_neg h1, zero_div, sub_zero,
      Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  have hQ' : ∀ t, 1 ≤ t → |th (bRe 𝓕 χ) t| ≤ C * 𝓕.B * Real.exp (-(t / 2)) := by
    intro t ht
    have := ((H 𝓕 χ).2 h1).1 t ht
    rw [th_eq hχ, Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  have hF : 𝓕.F χ 1 = ((∫ t in Set.Ioi (0 : ℝ), th (bRe 𝓕 χ) t : ℝ) : ℂ) := by
    rw [← ((H 𝓕 χ).2 h1).2]
    simp only [th_eq hχ]
    exact integral_ofReal
  set L := ∫ t in Set.Ioi (0 : ℝ), th (bRe 𝓕 χ) t with hL
  have hE : 0 ≤ C * 𝓕.B ^ 11 := by positivity
  set s := δ / 𝓕.B ^ 22 with hs
  have hs0 : 0 < s := by positivity
  have hs1 : s ≤ 1 := (div_le_one (by positivity)).2 (hδ1.trans (one_le_pow₀ hB1))
  have hv : 0 < s ^ 2 := by positivity
  have hv1 : s ^ 2 ≤ 1 := pow_le_one₀ hs0.le hs1
  have up := integral_le (measurable_th _) (measurable_th _) hE hP hQ
    (integrableOn_of_bounds (measurable_th _) hE hQ hQ') hv
  have lo := besW_le_integral (bRe_le h11) (bRe_le hχ) (bRe_one 𝓕 1) (bRe_one 𝓕 χ)
    (fun n => by simpa [bRe] using (𝓕.sq χ hχ n).1) hv
  have lo' := besW_one_le hv hv1
  rw [Real.sqrt_sq hs0.le, ← hL, ← hK] at up
  have e1 : (C * 𝓕.B ^ 11) ^ 2 * s * K = C ^ 2 * K * δ := by
    rw [hs]; field_simp
  have h2 : w0 / 2 ≤ ρ / s ^ 2 * L := by linarith
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 4 * 𝓕.B := mul_le_mul 𝓕.κ_le 𝓕.card_le (by positivity) (by norm_num)
  have h3 : w0 / 2 ≤ 4 * 𝓕.B / s ^ 2 * |L| :=
    h2.trans ((mul_le_mul_of_nonneg_left (le_abs_self L) (by positivity)).trans (by gcongr))
  rw [hF, Complex.norm_real, Real.norm_eq_abs]
  calc min 1 (δ ^ 2 * w0 / 8) / 𝓕.B ^ 45 ≤ (δ ^ 2 * w0 / 8) / 𝓕.B ^ 45 := by
        gcongr; exact min_le_right _ _
    _ = s ^ 2 / (4 * 𝓕.B) * (w0 / 2) := by rw [hs]; field_simp; norm_num
    _ ≤ s ^ 2 / (4 * 𝓕.B) * (4 * 𝓕.B / s ^ 2 * |L|) := by gcongr
    _ = |L| := by field_simp

end GlobalTheory.Hk.RealChar

end
