import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin.PsiToPi

open Formalism.HermitianLattices.GL2PrimeSums (Li Emain)

noncomputable def mainPsi (θ : ℤ) (β u : ℝ) : ℝ := u - θ * (u ^ β / β)

noncomputable def wt (P : ℕ → Prop) (n : ℕ) : ℝ := if n.Prime ∧ P n then Real.log n else 0

noncomputable def cnt (P : ℕ → Prop) (u : ℝ) : ℝ := (((Finset.Icc 1 ⌊u⌋₊).filter (fun p => p.Prime ∧ P p)).card : ℝ)

theorem contOn_inv_log : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.Ioi 1) := fun t ht =>
  (continuousAt_const.div (Real.continuousAt_log (by have : 1 < t := ht; linarith))
    (Real.log_pos ht).ne').continuousWithinAt

theorem intInt_inv_log {x : ℝ} (hx : 1 < x) : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume 2 x := by
  apply ContinuousOn.intervalIntegrable
  refine contOn_inv_log.mono fun t ht => ?_
  have := ht.1
  have h2 : (1 : ℝ) < min 2 x := lt_min (by norm_num) hx
  exact lt_of_lt_of_le h2 this

theorem hasDerivAt_Li {x : ℝ} (hx : 1 < x) : HasDerivAt Li (1 / Real.log x) x :=
  intervalIntegral.integral_hasDerivAt_right (intInt_inv_log hx)
    (contOn_inv_log.stronglyMeasurableAtFilter isOpen_Ioi x hx)
    (contOn_inv_log.continuousAt (Ioi_mem_nhds hx))

theorem li_bounds {x : ℝ} (hx : 2 ≤ x) : 0 ≤ Li x ∧ Li x ≤ 3 / 2 * x := by
  have h2 := Real.log_two_gt_d9
  constructor
  · exact intervalIntegral.integral_nonneg hx fun t ht =>
      div_nonneg zero_le_one (Real.log_nonneg (by linarith [ht.1]))
  · have h := intervalIntegral.integral_mono_on hx (intInt_inv_log (by linarith))
      (intervalIntegrable_const (c := (3 / 2 : ℝ))) (fun t ht => by
        have := Real.log_le_log (by norm_num) ht.1
        rw [div_le_iff₀ (by linarith)]; linarith)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at h
    unfold Li; linarith

theorem hasDerivAt_diff (θ : ℤ) {β u : ℝ} (hβ : 0 < β) (hu : 1 < u) :
    HasDerivAt (fun u => Emain θ β u - mainPsi θ β u / Real.log u) (mainPsi θ β u / (u * Real.log u ^ 2)) u := by
  have hu0 : 0 < u := by linarith
  have hl : 0 < Real.log u := Real.log_pos hu
  have h1 : HasDerivAt (fun u : ℝ => u ^ β) (β * u ^ (β - 1)) u := Real.hasDerivAt_rpow_const (Or.inl hu0.ne')
  have h2 := (hasDerivAt_Li (Real.one_lt_rpow hu hβ)).comp u h1
  have h3 := (hasDerivAt_Li hu).sub (h2.const_mul (θ : ℝ))
  have h4 := ((hasDerivAt_id u).sub ((h1.div_const β).const_mul (θ : ℝ))).div (Real.hasDerivAt_log hu0.ne') hl.ne'
  have h5 := h3.sub h4
  refine HasDerivAt.congr_deriv (f := fun u => Emain θ β u - mainPsi θ β u / Real.log u) h5 ?_
  simp only [mainPsi, id, Pi.sub_apply]
  rw [Real.log_rpow hu0]
  field_simp
  ring

theorem contOn_w {Y X : ℝ} (hY : 1 < Y) : ContinuousOn (fun t : ℝ => 1 / (t * Real.log t ^ 2)) (Set.Icc Y X) := by
  intro t ht
  have h1 : 1 < t := lt_of_lt_of_le hY ht.1
  have hl := Real.log_pos h1
  exact (continuousAt_const.div (continuousAt_id.mul ((Real.continuousAt_log (by linarith)).pow 2))
    (mul_ne_zero (by show t ≠ 0; linarith) (pow_ne_zero 2 hl.ne'))).continuousWithinAt

theorem contOn_main (θ : ℤ) (β : ℝ) {Y X : ℝ} (hY : 1 < Y) :
    ContinuousOn (fun t : ℝ => 1 / (t * Real.log t ^ 2) * mainPsi θ β t) (Set.Icc Y X) := by
  refine (contOn_w hY).mul fun t ht => ?_
  have h1 : 1 < t := lt_of_lt_of_le hY ht.1
  exact (continuousAt_id.sub (continuousAt_const.mul
    ((Real.continuousAt_rpow_const t β (Or.inl (by linarith))).div_const β))).continuousWithinAt

theorem integral_main (θ : ℤ) {β Y X : ℝ} (hβ : 0 < β) (hY : 1 < Y) (hYX : Y ≤ X) :
    ∫ t in Y..X, 1 / (t * Real.log t ^ 2) * mainPsi θ β t =
      (Emain θ β X - mainPsi θ β X / Real.log X) - (Emain θ β Y - mainPsi θ β Y / Real.log Y) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u => Emain θ β u - mainPsi θ β u / Real.log u)
  · intro t ht
    rw [Set.uIcc_of_le hYX] at ht
    exact (hasDerivAt_diff θ hβ (lt_of_lt_of_le hY ht.1)).congr_deriv (by ring)
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hYX]; exact contOn_main θ β hY

theorem cnt_eq (P : ℕ → Prop) (u : ℝ) :
    cnt P u = ∑ k ∈ Finset.Ioc 0 ⌊u⌋₊, 1 / Real.log k * wt P k := by
  unfold cnt
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold wt
  split_ifs with h
  · have : 0 < Real.log k := Real.log_pos (by exact_mod_cast h.1.one_lt)
    field_simp; simp
  · simp

theorem abel (P : ℕ → Prop) {Y X : ℝ} (hY : 1 < Y) (hYX : Y ≤ X) :
    cnt P X - cnt P Y = (∑ k ∈ Finset.Icc 0 ⌊X⌋₊, wt P k) / Real.log X - (∑ k ∈ Finset.Icc 0 ⌊Y⌋₊, wt P k) / Real.log Y +
      ∫ t in Y..X, 1 / (t * Real.log t ^ 2) * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, wt P k := by
  have hd : ∀ t ∈ Set.Icc Y X, HasDerivAt (fun t : ℝ => 1 / Real.log t) (-(1 / (t * Real.log t ^ 2))) t := by
    intro t ht
    have h1 : 1 < t := lt_of_lt_of_le hY ht.1
    have hl := Real.log_pos h1
    refine HasDerivAt.congr_deriv (f := fun t : ℝ => 1 / Real.log t)
      ((hasDerivAt_const t (1 : ℝ)).div (Real.hasDerivAt_log (by linarith : t ≠ 0)) hl.ne') ?_
    field_simp; ring
  have hint : IntegrableOn (deriv fun t : ℝ => 1 / Real.log t) (Set.Icc Y X) :=
    ((contOn_w hY).neg.congr fun t ht => (hd t ht).deriv).integrableOn_Icc
  have h := sum_mul_eq_sub_sub_integral_mul (wt P) (f := fun t : ℝ => 1 / Real.log t) (by linarith) hYX
    (fun t ht => (hd t ht).differentiableAt) hint
  rw [cnt_eq, cnt_eq, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le ⌊Y⌋₊) (Nat.floor_le_floor hYX),
    add_sub_cancel_left, h, intervalIntegral.integral_of_le hYX, sub_eq_add_neg _ (∫ t in _, _), ← integral_neg]
  congr 1
  · ring
  · refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [(hd t (Set.Ioc_subset_Icc_self ht)).deriv]; ring

theorem core (P : ℕ → Prop) (θ : ℤ) {β φ ρ Y X : ℝ} (hβ : 0 < β) (hY : 1 < Y) (hYX : Y ≤ X)
    (h : ∀ u ∈ Set.Icc Y X, |φ * (∑ k ∈ Finset.Icc 0 ⌊u⌋₊, wt P k) - mainPsi θ β u| ≤ ρ * mainPsi θ β u) :
    |φ * (cnt P X - cnt P Y) - (Emain θ β X - Emain θ β Y)| ≤
      ρ * (Emain θ β X - Emain θ β Y + 2 * (mainPsi θ β Y / Real.log Y)) := by
  have hlY := Real.log_pos hY
  have hlX : 0 < Real.log X := Real.log_pos (by linarith)
  have iA : IntervalIntegrable (fun t : ℝ => 1 / (t * Real.log t ^ 2) * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, wt P k) volume Y X :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hYX).2
      (integrableOn_mul_sum_Icc (wt P) (by linarith) (contOn_w hY).integrableOn_Icc)
  have iB : IntervalIntegrable (fun t : ℝ => 1 / (t * Real.log t ^ 2) * mainPsi θ β t) volume Y X :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hYX).2 (contOn_main θ β hY).integrableOn_Icc
  have hw : ∀ t ∈ Set.Icc Y X, 0 ≤ 1 / (t * Real.log t ^ 2) := fun t ht => by
    have : 0 < t := by linarith [ht.1]
    positivity
  have u1 := intervalIntegral.integral_mono_on hYX (iA.const_mul φ) (iB.const_mul (1 + ρ)) fun t ht => by
    have := mul_le_mul_of_nonneg_left (abs_le.1 (h t ht)).2 (hw t ht)
    linarith
  have u2 := intervalIntegral.integral_mono_on hYX (iB.const_mul (1 - ρ)) (iA.const_mul φ) fun t ht => by
    have := mul_le_mul_of_nonneg_left (abs_le.1 (h t ht)).1 (hw t ht)
    linarith
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_main θ hβ hY hYX] at u1 u2
  obtain ⟨x1, x2⟩ := abs_le.1 (h X ⟨hYX, le_rfl⟩)
  obtain ⟨y1, y2⟩ := abs_le.1 (h Y ⟨le_rfl, hYX⟩)
  have x1 := mul_le_mul_of_nonneg_left x1 (inv_pos.2 hlX).le
  have x2 := mul_le_mul_of_nonneg_left x2 (inv_pos.2 hlX).le
  have y1 := mul_le_mul_of_nonneg_left y1 (inv_pos.2 hlY).le
  have y2 := mul_le_mul_of_nonneg_left y2 (inv_pos.2 hlY).le
  rw [abel P hY hYX, abs_le]
  simp only [div_eq_mul_inv] at *
  constructor <;> linarith

theorem psi_sub_wt (P : ℕ → Prop) {u : ℝ} (hu : 1 ≤ u) :
    |(∑ n ∈ (Finset.Icc 1 ⌊u⌋₊).filter P, Λ n) - ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, wt P k| ≤ 2 * √u * Real.log u := by
  refine le_trans ?_ (Chebyshev.psi_sub_theta_le hu)
  rw [← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le _), show wt P 0 = 0 by simp [wt], zero_add,
    show Finset.Icc 1 ⌊u⌋₊ = Finset.Ioc 0 ⌊u⌋₊ from rfl, Finset.sum_filter, ← Finset.sum_sub_distrib,
    Chebyshev.psi, Chebyshev.theta, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  have h0 : 0 ≤ Λ n := vonMangoldt_nonneg
  unfold wt
  by_cases hp : n.Prime <;> by_cases hP : P n <;> simp [hp, hP, vonMangoldt_apply_prime, abs_of_nonneg h0, h0]

theorem main_bounds {θ : ℤ} {β δ u : ℝ} (hθ : θ = 0 ∨ θ = 1 ∨ θ = -1) (hβ : 7 / 8 ≤ β) (hδ : 0 < δ) (hδβ : δ ≤ 1 - β)
    (hu : 1 ≤ u) (hl : 4 ≤ Real.log u) : δ * u ≤ mainPsi θ β u ∧ mainPsi θ β u ≤ 3 * u := by
  have hu0 : 0 < u := by linarith
  have hp : 0 < u ^ β := Real.rpow_pos_of_pos hu0 β
  have h1 : u ^ β ≤ u := by
    simpa using Real.rpow_le_rpow_of_exponent_le hu (show β ≤ 1 by linarith)
  have h2 : 0 < u ^ β / β := by positivity
  have h3 : u ^ β / β ≤ 2 * u := by rw [div_le_iff₀ (by linarith)]; nlinarith
  have h4 : δ * u ≤ u := by nlinarith
  unfold mainPsi
  rcases hθ with rfl | rfl | rfl
  · simp; constructor <;> linarith
  · have e : u = u ^ β * Real.exp ((1 - β) * Real.log u) := by
      rw [Real.rpow_def_of_pos hu0, ← Real.exp_add]
      rw [show Real.log u * β + (1 - β) * Real.log u = Real.log u by ring, Real.exp_log hu0]
    have h5 : 1 + 4 * (1 - β) ≤ Real.exp ((1 - β) * Real.log u) := by
      have := Real.add_one_le_exp ((1 - β) * Real.log u)
      nlinarith
    have h6 : u ^ β * (1 + 4 * (1 - β)) ≤ u := by
      have := mul_le_mul_of_nonneg_left h5 hp.le
      linarith
    have h7 : u ^ β / β ≤ β * u := by
      rw [div_le_iff₀ (by linarith)]
      have h8 : 1 ≤ (1 + 4 * (1 - β)) * (β * β) := by
        have : 0 ≤ 1 - β := by linarith
        have h9 : 3 / 4 ≤ β * β := by nlinarith
        nlinarith
      have := mul_le_mul_of_nonneg_left h8 hp.le
      have := mul_le_mul_of_nonneg_right h6 (show 0 ≤ β * β by positivity)
      nlinarith
    push_cast
    constructor <;> nlinarith
  · push_cast
    constructor <;> linarith

theorem abs_emain_le {θ : ℤ} {β u : ℝ} (hθ : θ = 0 ∨ θ = 1 ∨ θ = -1) (hβ : 7 / 8 ≤ β) (hβ1 : β ≤ 1)
    (hu : 4 ≤ u) : |Emain θ β u| ≤ 3 * u := by
  have h1 : u ^ β ≤ u := by
    simpa using Real.rpow_le_rpow_of_exponent_le (show 1 ≤ u by linarith) hβ1
  have h2 : 2 ≤ u ^ β := by
    have h3 : u ^ (1 / 2 : ℝ) ≤ u ^ β := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have e : (2 : ℝ) ≤ u ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]; apply Real.le_sqrt_of_sq_le; linarith
    linarith
  obtain ⟨a1, a2⟩ := li_bounds (x := u) (by linarith)
  obtain ⟨b1, b2⟩ := li_bounds h2
  unfold Emain
  rw [abs_le]
  rcases hθ with rfl | rfl | rfl <;> push_cast <;> constructor <;> linarith

theorem cnt_bounds (P : ℕ → Prop) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ cnt P u ∧ cnt P u ≤ u := by
  refine ⟨Nat.cast_nonneg _, le_trans ?_ (Nat.floor_le hu)⟩
  have := Finset.card_filter_le (Finset.Icc 1 ⌊u⌋₊) (fun p => p.Prime ∧ P p)
  rw [Nat.card_Icc, Nat.add_sub_cancel] at this
  unfold cnt
  exact_mod_cast this

theorem step (P : ℕ → Prop) {θ : ℤ} {β δ φ B ρ s : ℝ} (hθ : θ = 0 ∨ θ = 1 ∨ θ = -1) (hβ : 7 / 8 ≤ β) (hδ : 0 < δ)
    (hδβ : δ ≤ 1 - β) (hB : 3 ≤ B) (hφ : 0 ≤ φ) (hφB : φ ≤ B) (hρ : 0 ≤ ρ) (hs : 64 * B ≤ δ * s)
    (h : ∀ u ∈ Set.Icc (s ^ 8) (s ^ 16),
      |φ * (∑ n ∈ (Finset.Icc 1 ⌊u⌋₊).filter P, Λ n) - mainPsi θ β u| ≤ ρ * mainPsi θ β u) :
    0 ≤ Emain θ β (s ^ 16) ∧
      |φ * cnt P (s ^ 16) - Emain θ β (s ^ 16)| ≤ (3 * ρ + 4 / s) * Emain θ β (s ^ 16) := by
  have hs0 : 0 < s := by
    by_contra hc
    nlinarith
  have hsB : 64 * B ≤ s := by nlinarith
  have hs1 : 1 ≤ s := by linarith
  have hls : 1 ≤ Real.log s := by
    rw [Real.le_log_iff_exp_le hs0]; linarith [Real.exp_one_lt_d9]
  have hY : s ≤ s ^ 8 := le_self_pow₀ hs1 (by norm_num)
  have hYX : s ^ 8 ≤ s ^ 16 := pow_le_pow_right₀ hs1 (by norm_num)
  have hlY : 4 ≤ Real.log (s ^ 8) := by rw [Real.log_pow]; push_cast; linarith
  have hm : ∀ u ∈ Set.Icc (s ^ 8) (s ^ 16), δ * u ≤ mainPsi θ β u ∧ mainPsi θ β u ≤ 3 * u := fun u hu =>
    main_bounds hθ hβ hδ hδβ (by linarith [hu.1]) (hlY.trans (Real.log_le_log (by positivity) hu.1))
  have h' : ∀ u ∈ Set.Icc (s ^ 8) (s ^ 16),
      |φ * (∑ k ∈ Finset.Icc 0 ⌊u⌋₊, wt P k) - mainPsi θ β u| ≤ (ρ + 1 / s) * mainPsi θ β u := by
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    have k1 := psi_sub_wt P (u := u) (by linarith [hu.1])
    obtain ⟨r, hr0, hr⟩ : ∃ r : ℝ, 0 < r ∧ u = r ^ 4 :=
      ⟨√(√u), by positivity, by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by positivity), Real.sq_sqrt hu0.le]⟩
    have hsr : s ^ 2 ≤ r := by
      apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hr0.le
      rw [← hr, ← pow_mul]; exact hu.1
    have k2 : √u = r ^ 2 := by
      rw [hr, show r ^ 4 = (r ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    have k3 : Real.log u ≤ 4 * r := by
      rw [hr, Real.log_pow]; push_cast; linarith [Real.log_le_sub_one_of_pos hr0]
    have k4 : 2 * √u * Real.log u ≤ 8 * r ^ 3 := by
      rw [k2]
      have := mul_le_mul_of_nonneg_left k3 (show 0 ≤ 2 * r ^ 2 by positivity)
      linarith
    have k5 : B * (8 * r ^ 3) ≤ 1 / s * (δ * u) := by
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hs0, hr]
      have a1 : 8 * B * s ≤ δ * r := by nlinarith
      have := mul_le_mul_of_nonneg_left a1 (show 0 ≤ r ^ 3 by positivity)
      linarith
    have k6 : 1 / s * (δ * u) ≤ 1 / s * mainPsi θ β u := mul_le_mul_of_nonneg_left (hm u hu).1 (by positivity)
    have k7 : |φ * ((∑ n ∈ (Finset.Icc 1 ⌊u⌋₊).filter P, Λ n) - ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, wt P k)| ≤ B * (8 * r ^ 3) := by
      rw [abs_mul, abs_of_nonneg hφ]
      exact mul_le_mul hφB (k1.trans k4) (abs_nonneg _) (by linarith)
    have k8 := abs_le.1 (h u hu)
    rw [abs_le] at k7 ⊢
    constructor <;> linarith [k7.1, k7.2, k8.1, k8.2]
  have hc := core P θ (φ := φ) (by linarith : 0 < β) (by linarith) hYX h'
  have hI : 0 ≤ ∫ t in s ^ 8..s ^ 16, 1 / (t * Real.log t ^ 2) * mainPsi θ β t :=
    intervalIntegral.integral_nonneg hYX fun t ht => by
      have : 0 < t := by linarith [ht.1]
      exact mul_nonneg (by positivity) (le_trans (by positivity) (hm t ht).1)
  rw [integral_main θ (by linarith) (by linarith) hYX] at hI
  have e1 := abs_le.1 (abs_emain_le (u := s ^ 8) hθ hβ (by linarith) (by linarith))
  have e2 : mainPsi θ β (s ^ 8) / Real.log (s ^ 8) ≤ s ^ 8 := by
    rw [div_le_iff₀ (by linarith)]
    have := (hm _ ⟨le_rfl, hYX⟩).2
    nlinarith
  have e3 : 8 * s ^ 14 ≤ mainPsi θ β (s ^ 16) / Real.log (s ^ 16) := by
    rw [le_div_iff₀ (Real.log_pos (by linarith)), Real.log_pow]
    have a1 := (hm _ ⟨hYX, le_rfl⟩).1
    have a2 : Real.log s ≤ s := by linarith [Real.log_le_sub_one_of_pos hs0]
    have a3 := mul_le_mul_of_nonneg_left a2 (show 0 ≤ s ^ 14 by positivity)
    have a4 := mul_le_mul_of_nonneg_left (show 128 ≤ δ * s by linarith) (show 0 ≤ s ^ 15 by positivity)
    push_cast
    nlinarith
  have e4 : s ^ 8 ≤ s ^ 10 := pow_le_pow_right₀ hs1 (by norm_num)
  have e5 : s ^ 10 ≤ s ^ 14 := pow_le_pow_right₀ hs1 (by norm_num)
  have e6 : 4 * s ^ 10 ≤ Emain θ β (s ^ 16) := by linarith [e1.1]
  have hY0 : 0 < s ^ 8 := by positivity
  refine ⟨by linarith, ?_⟩
  have e7 : (ρ + 1 / s) * (Emain θ β (s ^ 16) - Emain θ β (s ^ 8) + 2 * (mainPsi θ β (s ^ 8) / Real.log (s ^ 8))) ≤
      (ρ + 1 / s) * (3 * Emain θ β (s ^ 16)) := mul_le_mul_of_nonneg_left (by linarith [e1.1]) (by positivity)
  obtain ⟨c1, c2⟩ := cnt_bounds P hY0.le
  have e8 : φ * cnt P (s ^ 8) ≤ B * s ^ 8 := mul_le_mul hφB c2 c1 (by linarith)
  have e9 : 0 ≤ φ * cnt P (s ^ 8) := mul_nonneg hφ c1
  have e10 : B * s ^ 8 + 3 * s ^ 8 ≤ 1 / s * Emain θ β (s ^ 16) := by
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hs0]
    have := mul_le_mul_of_nonneg_left (show B + 3 ≤ s by linarith) (show 0 ≤ s ^ 9 by positivity)
    have : 0 < s ^ 10 := by positivity
    nlinarith
  have e11 := abs_le.1 (hc.trans e7)
  have e12 : 0 ≤ B * s ^ 8 := by positivity
  rw [abs_le, show 4 / s = 4 * (1 / s) by ring]
  constructor <;> linarith [e11.1, e11.2, e1.1, e1.2]

end GlobalTheory.Lin.PsiToPi

namespace GlobalTheory.Lin

open PsiToPi

theorem pi_rel_of_psi_rel : ∀ c₂ c₃ C cS : ℝ, 0 < c₂ → 0 < c₃ → 0 < C → 0 < cS → ∃ c₂' c₃' C' : ℝ, 0 < c₂' ∧ 0 < c₃' ∧ 0 < C' ∧ ∀ (B φ β : ℝ) (θ : ℤ) (P : ℕ → Prop), 3 ≤ B → 1 ≤ φ → φ ≤ B → (θ = 0 ∨ ((θ = 1 ∨ θ = -1) ∧ 7 / 8 ≤ β ∧ cS / B ^ 3 ≤ 1 - β)) → (∀ u : ℝ, B ^ c₂ ≤ u → |φ * (∑ n ∈ (Finset.Icc 1 ⌊u⌋₊).filter P, Λ n) - (u - θ * (u ^ β / β))| ≤ C * (Real.exp (-c₃ * Real.log u / Real.log B) + Real.exp (-Real.sqrt (c₃ * Real.log u))) * (u - θ * (u ^ β / β))) → ∀ X : ℝ, B ^ c₂' ≤ X → |φ * (((Finset.Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ P p)).card : ℝ) - Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X| ≤ C' * (Real.exp (-c₃' * Real.log X / Real.log B) + Real.exp (-Real.sqrt (c₃' * Real.log X))) * Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X := by
  intro c₂ c₃ C cS h2 h3 hC hS
  set c := min cS 1 with hc
  have hc0 : 0 < c := lt_min hS one_pos
  set d := min (c₃ / 2) (1 / 16) with hd
  have hd0 : 0 < d := lt_min (by positivity) (by norm_num)
  have hd1 : d ≤ c₃ / 2 := min_le_left _ _
  have hd2 : d ≤ 1 / 16 := min_le_right _ _
  refine ⟨16 * (c₂ + 4 + 64 / c), d, 3 * C + 4, by positivity, hd0, by positivity, ?_⟩
  intro B φ β θ P hB hφ hφB hθ h X hX
  have hB0 : 0 < B := by linarith
  have hB1 : 1 ≤ B := by linarith
  have hlB : 1 ≤ Real.log B := by
    rw [Real.le_log_iff_exp_le hB0]; linarith [Real.exp_one_lt_d9]
  have hX1 : 1 ≤ X := le_trans (Real.one_le_rpow hB1 (by positivity)) hX
  have hX0 : 0 < X := by linarith
  obtain ⟨s, hs0, rfl⟩ : ∃ s : ℝ, 0 < s ∧ X = s ^ 16 :=
    ⟨X ^ ((16 : ℕ) : ℝ)⁻¹, by positivity, (Real.rpow_inv_natCast_pow hX0.le (by norm_num)).symm⟩
  have hs : B ^ (c₂ + 4 + 64 / c) ≤ s := by
    apply le_of_pow_le_pow_left₀ (n := 16) (by norm_num) hs0.le
    rw [← Real.rpow_natCast, ← Real.rpow_mul hB0.le, mul_comm]
    exact_mod_cast hX
  have hs1 : 1 ≤ s := le_trans (Real.one_le_rpow hB1 (by positivity)) hs
  have hs2 : B ^ c₂ ≤ s := le_trans (Real.rpow_le_rpow_of_exponent_le hB1 (by
    have : 0 < 64 / c := by positivity
    linarith)) hs
  have hs3 : 64 * B ≤ c / B ^ 3 * s := by
    have a1 : B ^ (4 + 64 / c) ≤ s := le_trans (Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)) hs
    have a2 : 64 / c ≤ B ^ (64 / c) := by
      rw [Real.rpow_def_of_pos hB0]
      have := Real.add_one_le_exp (Real.log B * (64 / c))
      have : 0 < 64 / c := by positivity
      nlinarith
    rw [Real.rpow_add hB0, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at a1
    have a3 : B ^ 4 * (64 / c) ≤ s := le_trans (by gcongr) a1
    calc 64 * B = c / B ^ 3 * (B ^ 4 * (64 / c)) := by field_simp
      _ ≤ _ := by gcongr
  have hls : 0 ≤ Real.log s := Real.log_nonneg hs1
  set e := Real.exp (-d * Real.log (s ^ 16) / Real.log B) + Real.exp (-Real.sqrt (d * Real.log (s ^ 16))) with he
  have he0 : 0 < e := by positivity
  have herr : ∀ u ∈ Set.Icc (s ^ 8) (s ^ 16),
      Real.exp (-c₃ * Real.log u / Real.log B) + Real.exp (-Real.sqrt (c₃ * Real.log u)) ≤ e := by
    intro u hu
    have a1 : d * Real.log (s ^ 16) ≤ c₃ * Real.log u := by
      have := Real.log_le_log (by positivity) hu.1
      rw [Real.log_pow] at this ⊢
      push_cast at this ⊢
      nlinarith
    refine add_le_add (Real.exp_le_exp.2 ?_) (Real.exp_le_exp.2 (neg_le_neg (Real.sqrt_le_sqrt a1)))
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  have hse : 1 / s ≤ e := by
    have a1 : 1 / s ≤ Real.exp (-d * Real.log (s ^ 16) / Real.log B) := by
      rw [one_div, ← Real.exp_log hs0, ← Real.exp_neg, Real.exp_log hs0]
      apply Real.exp_le_exp.2
      rw [le_div_iff₀ (by linarith), Real.log_pow]
      push_cast
      nlinarith
    exact a1.trans (le_add_of_nonneg_right (Real.exp_pos _).le)
  have key : ∀ β' : ℝ, (θ = 0 ∨ θ = 1 ∨ θ = -1) → 7 / 8 ≤ β' → c / B ^ 3 ≤ 1 - β' →
      (∀ u, mainPsi θ β' u = u - θ * (u ^ β / β)) →
      |φ * cnt P (s ^ 16) - Formalism.HermitianLattices.GL2PrimeSums.Emain θ β' (s ^ 16)| ≤ (3 * C + 4) * e * Formalism.HermitianLattices.GL2PrimeSums.Emain θ β' (s ^ 16) := by
    intro β' t1 t2 t3 t4
    have hY : s ≤ s ^ 8 := le_self_pow₀ hs1 (by norm_num)
    obtain ⟨r1, r2⟩ := step P (ρ := C * e) t1 t2 (by positivity) t3 hB (by linarith) hφB (by positivity) hs3 (fun u hu => by
      have hh := h u (by linarith [hu.1])
      rw [← t4 u] at hh
      have h0 : 0 ≤ mainPsi θ β' u := (mul_nonneg_iff_of_pos_left (by positivity)).1 (le_trans (abs_nonneg _) hh)
      exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (herr u hu) hC.le) h0))
    refine r2.trans (mul_le_mul_of_nonneg_right ?_ r1)
    rw [show 4 / s = 4 * (1 / s) by ring]
    linarith
  rcases hθ with rfl | ⟨t1, t2, t3⟩
  · have := key (7 / 8) (Or.inl rfl) le_rfl (by
      rw [div_le_iff₀ (by positivity)]
      have a1 : (3 : ℝ) ^ 3 ≤ B ^ 3 := by gcongr
      have a2 : c ≤ 1 := min_le_right _ _
      linarith) (fun u => by simp [mainPsi])
    simpa [Formalism.HermitianLattices.GL2PrimeSums.Emain, cnt] using this
  · exact key β (Or.inr t1) t2 (le_trans (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)) t3)
      (fun u => rfl)

end GlobalTheory.Lin
