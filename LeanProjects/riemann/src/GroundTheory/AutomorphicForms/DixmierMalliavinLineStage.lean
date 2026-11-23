import Mathlib
import GroundTheory.AutomorphicForms.DixmierMalliavinLineKernel

namespace GroundTheory.Automorphic

open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace LineKernel

theorem contDiff_iteratedDeriv_of_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ ∞ f) (m : ℕ) : ContDiff ℝ ∞ (iteratedDeriv m f) := by
  rw [iteratedDeriv_eq_iterate]; exact hf.iterate_deriv m

theorem hasCompactSupport_iteratedDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : HasCompactSupport f) (m : ℕ) : HasCompactSupport (iteratedDeriv m f) := by
  induction m with
  | zero => simpa using hf
  | succ m ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem hasDerivAt_iteratedDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ ∞ f) (m : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv m f) (iteratedDeriv (m + 1) f x) x := by
  rw [iteratedDeriv_succ]
  exact ((contDiff_iteratedDeriv_of_contDiff hf m).differentiable (by simp) x).hasDerivAt

theorem iteratedDeriv_ofReal {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    iteratedDeriv m (fun t => (f t : ℂ)) = fun t => ((iteratedDeriv m f t : ℝ) : ℂ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact ((hasDerivAt_iteratedDeriv hf m t).ofReal_comp).deriv

theorem ofReal_convolution (f g : ℝ → ℝ) (x : ℝ) :
    (((f ⋆[mul ℝ ℝ] g) x : ℝ) : ℂ) =
      ((fun t => (f t : ℂ)) ⋆[mul ℂ ℂ] (fun t => (g t : ℂ))) x := by
  rw [convolution_mul, convolution_mul, ← integral_complex_ofReal]
  push_cast; rfl

theorem pairing_convolution {G K k : ℝ → ℂ} (hG : Continuous G) (hK : Integrable K)
    (hk : Integrable k) (hKc : HasCompactSupport K) (hkc : HasCompactSupport k) :
    Integrable (fun s => K s * ∫ t, G (s + t) * k t) ∧
      ∫ u, G u * (K ⋆[mul ℂ ℂ] k) u = ∫ s, K s * ∫ t, G (s + t) * k t := by
  obtain ⟨M, hM⟩ := (hKc.isCompact.add hkc.isCompact).exists_bound_of_continuousOn hG.continuousOn
  set Ψ : ℝ × ℝ → ℂ := fun p => G p.1 * (K p.2 * k (p.1 - p.2)) with hΨ
  have hconv : Integrable (fun p : ℝ × ℝ => mul ℂ ℂ (K p.2) (k (p.1 - p.2))) (volume.prod volume) :=
    hK.convolution_integrand (mul ℂ ℂ) hk
  have hΨi : Integrable Ψ (volume.prod volume) := by
    refine Integrable.mono' (hconv.norm.const_mul M) ?_ (Eventually.of_forall fun p => ?_)
    · exact (hG.comp continuous_fst).aestronglyMeasurable.mul hconv.aestronglyMeasurable
    · simp only [hΨ, mul_apply', norm_mul]
      by_cases h : K p.2 * k (p.1 - p.2) = 0
      · rw [mul_eq_zero] at h
        rcases h with h | h <;> simp [h]
      · rw [mul_eq_zero, not_or] at h
        have hp : p.1 ∈ tsupport K + tsupport k :=
          ⟨p.2, subset_tsupport _ h.1, p.1 - p.2, subset_tsupport _ h.2, by ring⟩
        have := hM p.1 hp
        calc ‖G p.1‖ * (‖K p.2‖ * ‖k (p.1 - p.2)‖) ≤ M * (‖K p.2‖ * ‖k (p.1 - p.2)‖) :=
              mul_le_mul_of_nonneg_right this (by positivity)
          _ = _ := rfl
  have hswap := integral_integral_swap (f := fun u s => Ψ (u, s)) hΨi
  have hinner : ∀ s, ∫ u, Ψ (u, s) = K s * ∫ t, G (s + t) * k t := by
    intro s
    rw [← integral_const_mul, ← integral_add_left_eq_self (fun u => Ψ (u, s)) s]
    congr 1; funext t; simp only [hΨ]; rw [add_sub_cancel_left]; ring
  refine ⟨?_, ?_⟩
  · have := hΨi.integral_prod_right
    simpa only [hinner] using this
  · calc ∫ u, G u * (K ⋆[mul ℂ ℂ] k) u = ∫ u, ∫ s, Ψ (u, s) := by
          congr 1; funext u
          rw [convolution_mul, ← integral_const_mul]
      _ = ∫ s, ∫ u, Ψ (u, s) := hswap
      _ = ∫ s, K s * ∫ t, G (s + t) * k t := by simp only [hinner]

theorem integral_deriv_mul {F ψ : ℝ → ℂ} (hF : ContDiff ℝ 1 F) (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) : ∫ u, deriv F u * ψ u = -∫ u, F u * deriv ψ u := by
  have hFd : Differentiable ℝ F := hF.differentiable one_ne_zero
  have hψd : Differentiable ℝ ψ := hψ.differentiable one_ne_zero
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable (u := F) (v := ψ) (u' := deriv F)
    (v' := deriv ψ) (fun x _ => (hFd x).hasDerivAt) (fun x _ => (hψd x).hasDerivAt)
    ((hF.continuous.mul (hψ.continuous_deriv le_rfl)).integrable_of_hasCompactSupport
      hψc.deriv.mul_left)
    (((hF.continuous_deriv le_rfl).mul hψ.continuous).integrable_of_hasCompactSupport
      hψc.mul_left)
    ((hF.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left)
  rw [h, neg_neg]

theorem integral_iteratedDeriv_mul {F ψ : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (p : ℕ) :
    ∫ u, iteratedDeriv p F u * ψ u = (-1) ^ p * ∫ u, F u * iteratedDeriv p ψ u := by
  induction p generalizing F with
  | zero => simp
  | succ p ih =>
    have hF' : ContDiff ℝ ∞ (deriv F) := (contDiff_infty_iff_deriv.1 hF).2
    rw [iteratedDeriv_succ', ih hF', pow_succ, mul_assoc]
    congr 1
    rw [integral_deriv_mul (hF.of_le (by simp))
      ((contDiff_iteratedDeriv_of_contDiff hψ p).of_le (by simp))
      (hasCompactSupport_iteratedDeriv hψc p), ← iteratedDeriv_succ]
    ring

def coef (a : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, p => if p = 0 then 1 else 0
  | n + 1, 0 => coef a n 0
  | n + 1, p + 1 => coef a n (p + 1) + coef a n p / a n

theorem coef_zero_right (a : ℕ → ℝ) (n : ℕ) : coef a n 0 = 1 := by
  induction n with
  | zero => simp [coef]
  | succ n ih => simp [coef, ih]

theorem coef_eq_zero (a : ℕ → ℝ) {n p : ℕ} (h : n < p) : coef a n p = 0 := by
  induction n generalizing p with
  | zero =>
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp [coef]
  | succ n ih =>
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp [coef, ih (by omega : n < q + 1), ih (by omega : n < q)]

theorem coef_nonneg {a : ℕ → ℝ} (ha : ∀ j, 0 < a j) (n p : ℕ) : 0 ≤ coef a n p := by
  induction n generalizing p with
  | zero => simp only [coef]; split_ifs <;> norm_num
  | succ n ih =>
    cases p with
    | zero => simp only [coef]; exact ih 0
    | succ p => simp only [coef]; exact add_nonneg (ih _) (div_nonneg (ih _) (ha n).le)

def sc (a : ℕ → ℝ) (n p : ℕ) : ℂ := (-1) ^ p * (coef a n p : ℂ)

def opT (a : ℕ → ℝ) (n : ℕ) (F : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∑ p ∈ Finset.range (n + 1), sc a n p * iteratedDeriv p F u

theorem sum_sc_succ (a : ℕ → ℝ) (n : ℕ) (d : ℕ → ℂ) :
    ∑ p ∈ Finset.range (n + 2), sc a (n + 1) p * d p =
      ∑ p ∈ Finset.range (n + 1), sc a n p * d p -
        (a n : ℂ)⁻¹ * ∑ p ∈ Finset.range (n + 1), sc a n p * d (p + 1) := by
  have key : ∀ p, sc a (n + 1) (p + 1) * d (p + 1) =
      sc a n (p + 1) * d (p + 1) - (a n : ℂ)⁻¹ * (sc a n p * d (p + 1)) := by
    intro p; simp only [sc, coef]; push_cast; ring
  rw [Finset.sum_range_succ' _ (n + 1), Finset.sum_range_succ _ n,
    Finset.sum_range_succ' (fun p => sc a n p * d p) n,
    Finset.sum_range_succ (fun p => sc a n p * d (p + 1)) n,
    Finset.sum_congr rfl (fun p _ => key p), Finset.sum_sub_distrib, ← Finset.mul_sum, key n]
  have h1 : sc a n (n + 1) = 0 := by simp [sc, coef_eq_zero a (Nat.lt_succ_self n)]
  have h2 : sc a (n + 1) 0 = sc a n 0 := by simp [sc, coef_zero_right]
  rw [h1, h2]
  ring

theorem continuous_opT (a : ℕ → ℝ) (n : ℕ) {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) :
    Continuous (opT a n F) :=
  continuous_finsetSum _ fun p _ => continuous_const.mul
    (hF.continuous_iteratedDeriv p (by exact_mod_cast le_top))

theorem hasDerivAt_opT (a : ℕ → ℝ) (n : ℕ) {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (x : ℝ) :
    HasDerivAt (opT a n F)
      (∑ p ∈ Finset.range (n + 1), sc a n p * iteratedDeriv (p + 1) F x) x := by
  have := HasDerivAt.sum (u := Finset.range (n + 1)) (A := fun p y => sc a n p * iteratedDeriv p F y)
    (fun p _ => (hasDerivAt_iteratedDeriv hF p x).const_mul (sc a n p))
  have e : opT a n F = ∑ i ∈ Finset.range (n + 1), fun y => sc a n i * iteratedDeriv i F y := by
    funext y; simp [opT, Finset.sum_apply]
  rw [e]; exact this

theorem opT_succ (a : ℕ → ℝ) (n : ℕ) (F : ℝ → ℂ) (u : ℝ) :
    opT a (n + 1) F u = opT a n F u -
      (a n : ℂ)⁻¹ * ∑ p ∈ Finset.range (n + 1), sc a n p * iteratedDeriv (p + 1) F u :=
  sum_sc_succ a n fun p => iteratedDeriv p F u

theorem integral_opT_mul (a : ℕ → ℝ) (n : ℕ) {F ψ : ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    ∫ u, opT a n F u * ψ u =
      ∫ u, F u * ∑ p ∈ Finset.range (n + 1), (coef a n p : ℂ) * iteratedDeriv p ψ u := by
  have hint : ∀ p, Integrable fun u => sc a n p * iteratedDeriv p F u * ψ u := fun p =>
    ((continuous_const.mul (hF.continuous_iteratedDeriv p (by exact_mod_cast le_top))).mul
      hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left
  have hint' : ∀ p, Integrable fun u => F u * ((coef a n p : ℂ) * iteratedDeriv p ψ u) := fun p =>
    (hF.continuous.mul (continuous_const.mul
      (hψ.continuous_iteratedDeriv p (by exact_mod_cast le_top)))).integrable_of_hasCompactSupport
      ((hasCompactSupport_iteratedDeriv hψc p).mul_left.mul_left)
  simp only [opT, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ fun p _ => hint p, integral_finsetSum _ fun p _ => hint' p]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [mul_assoc]
  rw [integral_const_mul, integral_iteratedDeriv_mul hF hψ hψc p, sc]
  have : ∫ u, F u * ((coef a n p : ℂ) * iteratedDeriv p ψ u) =
      (coef a n p : ℂ) * ∫ u, F u * iteratedDeriv p ψ u := by
    rw [← integral_const_mul]; congr 1; funext u; ring
  rw [this]
  have h1 : ((-1 : ℂ) ^ p) * ((-1) ^ p) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  linear_combination ((coef a n p : ℂ) * ∫ u, F u * iteratedDeriv p ψ u) * h1

def Kc (a r : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0 => kern (a 0) (r 0)
  | n + 1 => Kc a r n ⋆[mul ℝ ℝ] kern (a (n + 1)) (r (n + 1))

def Rs (r : ℕ → ℝ) (n : ℕ) : ℝ := ∑ j ∈ Finset.range (n + 1), 2 * r j

def KC (a r : ℕ → ℝ) (n : ℕ) : ℝ → ℂ := fun t => (Kc a r n t : ℂ)

def kC (a r : ℕ → ℝ) (j : ℕ) : ℝ → ℂ := fun t => (kern (a j) (r j) t : ℂ)

def ηC (a r : ℕ → ℝ) (j : ℕ) : ℝ → ℂ := fun t => (rem (a j) (r j) t : ℂ)

def ρ (a r : ℕ → ℝ) : ℕ → ℝ → ℂ
  | 0 => ηC a r 0
  | n + 1 => fun u => ∑ p ∈ Finset.range (n + 2),
      (coef a (n + 1) p : ℂ) * iteratedDeriv p (KC a r n ⋆[mul ℂ ℂ] ηC a r (n + 1)) u

theorem contDiff_ηC (a r : ℕ → ℝ) (j : ℕ) : ContDiff ℝ ∞ (ηC a r j) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_rem _ _)

section Kernels

variable {a r : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hr : ∀ j, 0 < r j)
include ha hr

theorem hasCompactSupport_ηC (j : ℕ) : HasCompactSupport (ηC a r j) :=
  (hasCompactSupport_rem (hr j)).comp_left Complex.ofReal_zero

theorem Kc_nonneg (n : ℕ) (t : ℝ) : 0 ≤ Kc a r n t := by
  induction n generalizing t with
  | zero => exact kern_nonneg (ha 0).le _ _
  | succ n ih =>
    simp only [Kc]; rw [convolution_mul]
    exact integral_nonneg fun s => mul_nonneg (ih s) (kern_nonneg (ha _).le _ _)

theorem integrable_Kc (n : ℕ) : Integrable (Kc a r n) := by
  induction n with
  | zero => exact integrable_kern (ha 0).le (hr 0)
  | succ n ih => exact ih.integrable_convolution (mul ℝ ℝ) (integrable_kern (ha _).le (hr _))

theorem support_Kc_subset (n : ℕ) : support (Kc a r n) ⊆ Icc 0 (Rs r n) := by
  induction n with
  | zero =>
    show support (kern (a 0) (r 0)) ⊆ _
    simpa [Rs] using support_kern_subset (hr 0)
  | succ n ih =>
    refine (support_convolution_subset (mul ℝ ℝ)).trans ?_
    refine (Set.add_subset_add ih (support_kern_subset (hr _))).trans ?_
    refine (Set.Icc_add_Icc_subset _ _ _ _).trans (Icc_subset_Icc (by simp) (le_of_eq ?_))
    simp [Rs, Finset.sum_range_succ]

theorem hasCompactSupport_Kc (n : ℕ) : HasCompactSupport (Kc a r n) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (support_Kc_subset ha hr n)

theorem integral_Kc_le_one (n : ℕ) : ∫ t, Kc a r n t ≤ 1 := by
  induction n with
  | zero => exact integral_kern_le_one (ha 0) (hr 0)
  | succ n ih =>
    simp only [Kc]
    rw [integral_convolution (mul ℝ ℝ) (integrable_Kc ha hr n) (integrable_kern (ha _).le (hr _)),
      mul_apply']
    have h1 : 0 ≤ ∫ t, Kc a r n t := integral_nonneg (Kc_nonneg ha hr n)
    have h2 := integral_kern_le_one (ha (n + 1)) (hr (n + 1))
    nlinarith

theorem KC_succ (n : ℕ) : KC a r (n + 1) = KC a r n ⋆[mul ℂ ℂ] kC a r (n + 1) :=
  funext fun x => ofReal_convolution _ _ x

theorem integrable_KC (n : ℕ) : Integrable (KC a r n) := (integrable_Kc ha hr n).ofReal

theorem hasCompactSupport_KC (n : ℕ) : HasCompactSupport (KC a r n) :=
  (hasCompactSupport_Kc ha hr n).comp_left Complex.ofReal_zero

theorem contDiff_conv_ηC (n : ℕ) : ContDiff ℝ ∞ (KC a r n ⋆[mul ℂ ℂ] ηC a r (n + 1)) := by
  have e : (KC a r n ⋆[mul ℂ ℂ] ηC a r (n + 1)) = (KC a r n ⋆[mul ℝ ℂ] ηC a r (n + 1)) := by
    funext x; simp only [convolution_def, mul_apply']
  rw [e]
  exact (hasCompactSupport_ηC ha hr _).contDiff_convolution_right (mul ℝ ℂ)
    (integrable_KC ha hr n).locallyIntegrable (contDiff_ηC a r _)

theorem hasCompactSupport_conv_ηC (n : ℕ) :
    HasCompactSupport (KC a r n ⋆[mul ℂ ℂ] ηC a r (n + 1)) :=
  (hasCompactSupport_KC ha hr n).convolution (mul ℂ ℂ) (hasCompactSupport_ηC ha hr _)

theorem stage_identity {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    F 0 = (∫ u, opT a (n + 1) F u * KC a r n u) +
      ∑ j ∈ Finset.range (n + 1), ∫ u, F u * ρ a r j u := by
  induction n with
  | zero =>
    have hd : ∀ t, HasDerivAt F (deriv F t) t := fun t =>
      (hF.differentiable (by simp) t).hasDerivAt
    have h := step_identity (ha 0) (hr 0) hd (hF.continuous_deriv (by simp))
    rw [h, Finset.sum_range_one]
    congr 1
    congr 1; funext u
    have hT : opT a 1 F u = F u - (a 0 : ℂ)⁻¹ * deriv F u := by
      simp [opT, sc, coef, Finset.sum_range_succ, iteratedDeriv_one]; ring
    rw [hT]; rfl
  | succ n ih =>
    rw [ih, Finset.sum_range_succ _ (n + 1)]
    suffices hs : ∫ u, opT a (n + 1) F u * KC a r n u =
        (∫ u, opT a (n + 1 + 1) F u * KC a r (n + 1) u) + ∫ u, F u * ρ a r (n + 1) u by
      rw [hs]; ring
    set G := opT a (n + 1) F with hG
    set G2 := opT a (n + 2) F with hG2
    have hGc : Continuous G := continuous_opT a _ hF
    have hG2c : Continuous G2 := continuous_opT a _ hF

    have hpt : ∀ s, G s = (∫ t, G2 (s + t) * kC a r (n + 1) t) +
        ∫ t, G (s + t) * ηC a r (n + 1) t := by
      intro s
      have hd : ∀ t, HasDerivAt (fun t => G (s + t))
          (∑ p ∈ Finset.range (n + 2), sc a (n + 1) p * iteratedDeriv (p + 1) F (s + t)) t :=
        fun t => (hasDerivAt_opT a (n + 1) hF (s + t)).comp_const_add s t
      have hdc : Continuous fun t =>
          ∑ p ∈ Finset.range (n + 2), sc a (n + 1) p * iteratedDeriv (p + 1) F (s + t) :=
        continuous_finsetSum _ fun p _ => continuous_const.mul
          ((hF.continuous_iteratedDeriv (p + 1) (by exact_mod_cast le_top)).comp
            (continuous_const.add continuous_id))
      have h := step_identity (ha (n + 1)) (hr (n + 1)) hd hdc
      simp only [add_zero] at h
      rw [h]
      congr 1
      congr 1; funext t
      congr 1
      exact (opT_succ a (n + 1) F (s + t)).symm
    have hpk := pairing_convolution (k := kC a r (n + 1)) hG2c (integrable_KC ha hr n)
      (integrable_kern (ha (n + 1)).le (hr (n + 1))).ofReal (hasCompactSupport_KC ha hr n)
      ((HasCompactSupport.of_support_subset_isCompact isCompact_Icc
        (support_kern_subset (hr (n + 1)))).comp_left Complex.ofReal_zero)
    have hpη := pairing_convolution (k := ηC a r (n + 1)) hGc (integrable_KC ha hr n)
      (integrable_rem (hr (n + 1))).ofReal (hasCompactSupport_KC ha hr n)
      (hasCompactSupport_ηC ha hr (n + 1))
    calc ∫ u, G u * KC a r n u
        = ∫ s, KC a r n s * ((∫ t, G2 (s + t) * kC a r (n + 1) t) +
            ∫ t, G (s + t) * ηC a r (n + 1) t) := by
          congr 1; funext s; rw [hpt s, mul_comm]
      _ = (∫ s, KC a r n s * ∫ t, G2 (s + t) * kC a r (n + 1) t) +
            ∫ s, KC a r n s * ∫ t, G (s + t) * ηC a r (n + 1) t := by
          simp only [mul_add]; exact integral_add hpk.1 hpη.1
      _ = (∫ u, G2 u * KC a r (n + 1) u) + ∫ u, F u * ρ a r (n + 1) u := by
          rw [← hpk.2, ← hpη.2, KC_succ ha hr n]
          congr 1
          rw [integral_opT_mul a (n + 1) hF (contDiff_conv_ηC ha hr n)
            (hasCompactSupport_conv_ηC ha hr n)]
          rfl

end Kernels

end LineKernel

end

end GroundTheory.Automorphic
