import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MeasurableCompInfGL
import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset

noncomputable section

open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory.JSW.RapidModel

open GlobalTheory.CuspRep GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [IsTotallyComplex E] in

theorem norm_toL_mul (x y : Matrix (Fin a) (Fin a) (Cinf E)) : ‖toL (x * y)‖ ≤ a * (‖toL x‖ * ‖toL y‖) := by
  refine pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun i => pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun j => ?_
  change ‖(x * y) i j‖ ≤ _
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (‖toL x‖ * ‖toL y‖) fun l _ => ?_).trans_eq (by simp))
  exact (norm_mul_le _ _).trans (mul_le_mul ((norm_le_pi_norm (toL x i) l).trans (norm_le_pi_norm (toL x) i))
    ((norm_le_pi_norm (toL y l) j).trans (norm_le_pi_norm (toL y) l)) (norm_nonneg _) (norm_nonneg _))

omit [IsTotallyComplex E] in

theorem height_mul_le (x y : GL (Fin a) (Cinf E)) : height (x * y) ≤ (1 + 2 * a) * (height x * height y) := by
  have h1 := norm_toL_mul x.val y.val
  have h2 := norm_toL_mul (y⁻¹).val (x⁻¹).val
  have hx := one_le_height x
  have hy := one_le_height y
  have a1 : ‖toL x.val‖ ≤ height x := by unfold height; linarith [norm_nonneg (toL (x⁻¹).val)]
  have a2 : ‖toL (x⁻¹).val‖ ≤ height x := by unfold height; linarith [norm_nonneg (toL x.val)]
  have b1 : ‖toL y.val‖ ≤ height y := by unfold height; linarith [norm_nonneg (toL (y⁻¹).val)]
  have b2 : ‖toL (y⁻¹).val‖ ≤ height y := by unfold height; linarith [norm_nonneg (toL y.val)]
  have c1 : ‖toL x.val‖ * ‖toL y.val‖ ≤ height x * height y := mul_le_mul a1 b1 (norm_nonneg _) (by linarith)
  have c2 : ‖toL (y⁻¹).val‖ * ‖toL (x⁻¹).val‖ ≤ height x * height y := by
    rw [mul_comm]; exact mul_le_mul a2 b2 (norm_nonneg _) (by linarith)
  have c0 : 1 ≤ height x * height y := one_le_mul_of_one_le_of_one_le hx hy
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have e : height (x * y) = 1 + ‖toL (x.val * y.val)‖ + ‖toL ((y⁻¹).val * (x⁻¹).val)‖ := by
    unfold height; rw [mul_inv_rev]; rfl
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left c1 ha, mul_le_mul_of_nonneg_left c2 ha]

variable (E a) in

def modGr : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | ∀ g, Measurable (chart F g) ∧ ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ y, ‖F (g * infGL E a y)‖ ≤ C * height y ^ N}
  add_mem' := fun {F G} hF hG g => by
    obtain ⟨m1, C, N, h0, h1⟩ := hF g
    obtain ⟨m2, C', N', h0', h2⟩ := hG g
    refine ⟨?_, C + C', N + N', by positivity, fun y => ?_⟩
    · have e : chart (F + G) g = fun x => chart F g x + chart G g x := by
        funext x
        by_cases h : IsUnit (Matrix.of x) <;> simp [chart, h]
      rw [e]; exact m1.add m2
    · have hy := one_le_height y
      have p1 : height y ^ N ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
      have p2 : height y ^ N' ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
      refine (norm_add_le _ _).trans ?_
      nlinarith [h1 y, h2 y, mul_le_mul_of_nonneg_left p1 h0, mul_le_mul_of_nonneg_left p2 h0']
  zero_mem' g := ⟨by
      have e : chart (0 : GA E a → ℂ) g = fun _ => 0 := by funext x; simp [chart]
      rw [e]; exact measurable_const, 0, 0, le_rfl, fun y => by simp⟩
  smul_mem' c F hF g := by
    obtain ⟨m1, C, N, h0, h1⟩ := hF g
    refine ⟨?_, ‖c‖ * C, N, by positivity, fun y => ?_⟩
    · have e : chart (c • F) g = fun x => c * chart F g x := by
        funext x
        by_cases h : IsUnit (Matrix.of x) <;> simp [chart, h]
      rw [e]; exact m1.const_mul c
    · rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (h1 y) (norm_nonneg _)

theorem integrable_of_modGr {F : GA E a → ℂ} (hF : F ∈ modGr E a) {X : Type} [MeasurableSpace X] {ν : Measure X}
    {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) (g : GA E a) :
    Integrable (fun x => k x * F (g * infGL E a (γ x))) ν := by
  obtain ⟨m, C, N, h0, hC⟩ := hF g
  have h : Measurable fun x => toL (γ x).val := hk.2.1
  have e : (fun x => F (g * infGL E a (γ x))) = fun x => chart F g (toL (γ x).val) :=
    funext fun x => (chart_val F g (γ x)).symm
  have hm : Measurable fun x => F (g * infGL E a (γ x)) := by rw [e]; exact m.comp h
  refine ((hk.2.2 N).const_mul C).mono' (hk.1.mul hm).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  calc ‖k x‖ * ‖F (g * infGL E a (γ x))‖ ≤ ‖k x‖ * (C * height (γ x) ^ N) :=
        mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
    _ = C * (‖k x‖ * height (γ x) ^ N) := by ring

theorem rspan_le_modGr (π : CuspSub E a) : rspan π ≤ modGr E a := by
  refine rspan_le (fun φ hφ g => ⟨measurable_chart φ.2 g, ?_⟩) (fun F hF h g => ?_) fun F hF X _ ν _ k γ hk g => ?_
  · obtain ⟨C, N, hC⟩ := (π.cusp φ hφ).1.growth g
    exact ⟨|C|, N, abs_nonneg C, fun y => (hC y).trans
      (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (by linarith [one_le_height y]) N))⟩
  · rw [← infGL_mul_finGL h]
    set y := Matrix.GeneralLinearGroup.map (pInf E) h
    set k := Matrix.GeneralLinearGroup.map (pFin E) h
    obtain ⟨m, C, N, h0, hC⟩ := hF (g * finGL E a k)
    refine ⟨?_, C * ((1 + 2 * a) * height y) ^ N, N, by have := one_le_height y; positivity, fun z => ?_⟩
    · have e : (fun x => F (x * (infGL E a y * finGL E a k))) =
          fun x => (fun x => F (x * finGL E a k)) (x * infGL E a y) := by
        funext x; simp only [mul_assoc]
      rw [e, chart_rt_inf (fun x => F (x * finGL E a k)), chart_rt_fin]
      exact m.comp (rmul (toL y.val)).continuous.measurable
    · have e : g * infGL E a z * (infGL E a y * finGL E a k) = g * finGL E a k * infGL E a (z * y) := by
        rw [mul_assoc g (finGL E a k), ← infGL_comm, map_mul]; simp only [mul_assoc]
      change ‖F (g * infGL E a z * (infGL E a y * finGL E a k))‖ ≤ _
      rw [e]
      refine (hC _).trans ?_
      rw [mul_assoc C, ← mul_pow]
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [one_le_height (z * y)]) ?_ N) h0
      exact (height_mul_le z y).trans_eq (by ring)
  · obtain ⟨m, C, N, h0, hC⟩ := hF g
    refine ⟨?_, C * (1 + 2 * a) ^ N * ∫ x, ‖k x‖ * height (γ x) ^ N ∂ν, N, ?_, fun z => ?_⟩
    · have e : chart (kerInf ν k γ F) g = fun x => ∫ t, k t * chart F g (toL (Matrix.of x * (γ t).val)) ∂ν := by
        funext x
        by_cases h : IsUnit (Matrix.of x)
        · obtain ⟨u, hu⟩ := h
          have hx : x = (toL u.val) := hu.symm
          rw [hx, chart_val, kerInf]
          congr 1
          funext t
          rw [mul_assoc, ← map_mul, ← chart_val F g]
          rfl
        · have h' : ∀ t, ¬ IsUnit (Matrix.of (toL (Matrix.of x * (γ t).val))) :=
            fun t h' => h ((Units.isUnit_mul_units _ (γ t)).1 h')
          simp only [chart, dif_neg h, dif_neg (h' _), mul_zero, integral_zero]
      rw [e]
      have hγ : Measurable fun x => toL (γ x).val := hk.2.1
      have hm : Measurable fun p : Lie E a × X => toL (Matrix.of p.1 * (γ p.2).val) := by
        refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
        change Measurable fun p : Lie E a × X => (Matrix.of p.1 * (γ p.2).val) i j
        simp only [Matrix.mul_apply]
        refine Finset.measurable_sum _ fun l _ => Measurable.mul ?_ ?_
        · exact (measurable_pi_apply l).comp ((measurable_pi_apply i).comp measurable_fst)
        · exact (measurable_pi_apply j).comp ((measurable_pi_apply l).comp (hγ.comp measurable_snd))
      have hs : StronglyMeasurable fun p : Lie E a × X => k p.2 * chart F g (toL (Matrix.of p.1 * (γ p.2).val)) :=
        ((hk.1.comp measurable_snd).mul (m.comp hm)).stronglyMeasurable
      exact hs.integral_prod_right'.measurable
    · refine mul_nonneg (by positivity) (integral_nonneg fun x => ?_)
      have := one_le_height (γ x)
      positivity
    · rw [kerInf]
      have hz := one_le_height z
      calc _ ≤ ∫ x, (C * (1 + 2 * a) ^ N * height z ^ N) * (‖k x‖ * height (γ x) ^ N) ∂ν := by
            refine norm_integral_le_of_norm_le ((hk.2.2 N).const_mul _) (Filter.Eventually.of_forall fun x => ?_)
            rw [norm_mul, mul_assoc g, ← map_mul]
            have h1 := (hC (z * γ x)).trans (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by linarith [one_le_height (z * γ x)]) (height_mul_le z (γ x)) N) h0)
            refine (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans_eq ?_
            rw [mul_pow, mul_pow]; ring
        _ = _ := by rw [integral_const_mul]; ring

theorem kerInf_integrable_of_mem_rspan {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ rspan π) {X : Type}
    [MeasurableSpace X] {ν : Measure X} {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) (g : GA E a) :
    Integrable (fun x => k x * F (g * infGL E a (γ x))) ν :=
  integrable_of_modGr (rspan_le_modGr π hF) hk g

theorem kerInf_add {π : CuspSub E a} {F G : GA E a → ℂ} (hF : F ∈ rspan π) (hG : G ∈ rspan π) {X : Type}
    [MeasurableSpace X] {ν : Measure X} {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) :
    kerInf ν k γ (F + G) = kerInf ν k γ F + kerInf ν k γ G := by
  funext g
  rw [Pi.add_apply, kerInf, kerInf, kerInf, ← integral_add (kerInf_integrable_of_mem_rspan hF hk g)
    (kerInf_integrable_of_mem_rspan hG hk g)]
  simp only [Pi.add_apply, mul_add]

theorem rspan_triv (ha : a ≤ 1) : rspan (CuspSub.triv E ha) = Submodule.span ℂ {fun _ => 1} := by
  rw [rspan_eq_mspanR, WhitModel.mspanR_triv]

theorem rspan_twist_triv (ha : a ≤ 1) (χ : Formalism.L2.Host.HChar E) :
    rspan ((CuspSub.triv E ha).twist χ) = Submodule.span ℂ {fun g => ((chiDet a χ g : ℂˣ) : ℂ)} := by
  apply le_antisymm
  · refine rspan_le ?_ (fun F hF h => ?_) fun F hF X _ ν _ k γ _ => ?_
    · rintro _ ⟨φ, hφ, rfl⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
      exact Submodule.mem_span_singleton.2 ⟨c, by funext g; simp [oneFn]⟩
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hF
      exact Submodule.mem_span_singleton.2 ⟨c * ((chiDet a χ h : ℂˣ) : ℂ), by funext g; simp; ring⟩
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hF
      refine Submodule.mem_span_singleton.2 ⟨∫ x, k x * (c * ((chiDet a χ (infGL E a (γ x)) : ℂˣ) : ℂ)) ∂ν, ?_⟩
      funext g
      simp only [Pi.smul_apply, smul_eq_mul, kerInf, map_mul, Units.val_mul]
      rw [← integral_mul_const]
      congr 1; funext x; ring
  · refine Submodule.span_le.2 ?_
    rintro _ rfl
    have h := mem_rspan (π := (CuspSub.triv E ha).twist χ) (φ := mulChi a χ (oneFn E a))
      ⟨oneFn E a, Submodule.mem_span_singleton_self _, rfl⟩
    have e : (mulChi a χ (oneFn E a)).1 = fun g => ((chiDet a χ g : ℂˣ) : ℂ) := by funext g; simp [oneFn]
    rw [e] at h
    exact h

theorem plGL_injective (w : InfinitePlace E) : Function.Injective (plGL (a := a) w) := fun g h e => by
  have h1 := map_plGL w g w
  rw [e, map_plGL, if_pos rfl, if_pos rfl] at h1
  exact h1.symm

end GlobalTheory.JSW.RapidModel
