import Formalism.EllipticTorsion.FormalGroupPointsParametrisation
import Formalism.EllipticTorsion.EllipticTorsionProofs.WSeries

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

namespace FormalGroupPointsParam

open Formalism.G

section Eval

variable {K : Type u} [NormedField K]

def AbsSum (f : PowerSeries K) (t : K) : Prop := Summable fun n => ‖coeff n f * t ^ n‖

def Ev (f : PowerSeries K) (t v : K) : Prop := AbsSum f t ∧ evalPS f t = v

theorem ev_C (a t : K) : Ev (C a) t a := by
  have h : ∀ n, coeff n (C a : PowerSeries K) * t ^ n = if n = 0 then a else 0 := by
    intro n; rw [coeff_C]; split_ifs with hn <;> simp [hn]
  refine ⟨?_, ?_⟩
  · have e : (fun n => ‖coeff n (C a : PowerSeries K) * t ^ n‖) = fun n => if n = 0 then ‖a‖ else 0 := by
      funext n; rw [h]; split_ifs <;> simp
    unfold AbsSum; rw [e]
    exact summable_of_ne_finset_zero (s := {0}) (fun n hn => by simp at hn; simp [hn])
  · unfold evalPS
    rw [tsum_eq_single 0 (fun n hn => by rw [h, if_neg hn])]
    simp

theorem ev_X (t : K) : Ev (X : PowerSeries K) t t := by
  have h : ∀ n, coeff n (X : PowerSeries K) * t ^ n = if n = 1 then t else 0 := by
    intro n; rw [coeff_X]; split_ifs with hn <;> simp [hn]
  refine ⟨?_, ?_⟩
  · have e : (fun n => ‖coeff n (X : PowerSeries K) * t ^ n‖) = fun n => if n = 1 then ‖t‖ else 0 := by
      funext n; rw [h]; split_ifs <;> simp
    unfold AbsSum; rw [e]
    exact summable_of_ne_finset_zero (s := {1}) (fun n hn => by simp at hn; simp [hn])
  · unfold evalPS
    rw [tsum_eq_single 1 (fun n hn => by rw [h, if_neg hn])]
    simp

variable [CompleteSpace K]

theorem Ev.add {f g : PowerSeries K} {t a b : K} (hf : Ev f t a) (hg : Ev g t b) :
    Ev (f + g) t (a + b) := by
  refine ⟨?_, ?_⟩
  · refine (hf.1.add hg.1).of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    simp only [map_add, add_mul]
    exact norm_add_le _ _
  · unfold evalPS
    simp only [map_add, add_mul]
    rw [hf.1.of_norm.tsum_add hg.1.of_norm]
    exact congrArg₂ (· + ·) hf.2 hg.2

theorem Ev.mul {f g : PowerSeries K} {t a b : K} (hf : Ev f t a) (hg : Ev g t b) :
    Ev (f * g) t (a * b) := by
  have key : ∀ n, coeff n (f * g) * t ^ n =
      ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, (coeff kl.1 f * t ^ kl.1) * (coeff kl.2 g * t ^ kl.2) := by
    intro n
    rw [coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hkl, pow_add]; ring
  have e1 : (fun n => ‖coeff n (f * g) * t ^ n‖) = fun n =>
      ‖∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, (coeff kl.1 f * t ^ kl.1) * (coeff kl.2 g * t ^ kl.2)‖ :=
    funext fun n => by rw [key n]
  have e2 : (fun n => coeff n (f * g) * t ^ n) = fun n =>
      ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, (coeff kl.1 f * t ^ kl.1) * (coeff kl.2 g * t ^ kl.2) :=
    funext key
  refine ⟨?_, ?_⟩
  · show Summable (fun n => ‖coeff n (f * g) * t ^ n‖)
    rw [e1]
    exact summable_norm_sum_mul_antidiagonal_of_summable_norm (f := fun n => coeff n f * t ^ n)
      (g := fun n => coeff n g * t ^ n) hf.1 hg.1
  · show ∑' n, coeff n (f * g) * t ^ n = a * b
    rw [e2, ← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (f := fun n => coeff n f * t ^ n)
      (g := fun n => coeff n g * t ^ n) hf.1 hg.1]
    exact congrArg₂ (· * ·) hf.2 hg.2

theorem Ev.pow {f : PowerSeries K} {t a : K} (hf : Ev f t a) (n : ℕ) : Ev (f ^ n) t (a ^ n) := by
  induction n with
  | zero =>
    have h := ev_C (1 : K) t
    rw [map_one] at h
    simpa using h
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul hf

theorem absSum_of_integral {f : PowerSeries K} (hf : IntegralPS f) {t : K} (ht : ‖t‖ < 1) :
    AbsSum f t := by
  refine (summable_geometric_of_lt_one (norm_nonneg t) ht).of_nonneg_of_le
    (fun _ => norm_nonneg _) fun n => ?_
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) (hf n)

end Eval

section Ultra

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem nle {a b : K} {c : ℝ} (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) : ‖a + b‖ ≤ c :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

theorem neq {a b : K} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt h), max_eq_left h.le]

theorem sm {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans_lt (max_lt ha hb)

theorem smm {c a : K} (hc : ‖c‖ ≤ 1) (ha : ‖a‖ < 1) : ‖c * a‖ < 1 := by
  rw [norm_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hc) ha

theorem smp {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a * b‖ < 1 := by
  rw [mul_comm]; exact smm hb.le ha

theorem norm_one_sub {E : K} (hE : ‖E‖ < 1) : ‖1 - E‖ = 1 := by
  rw [sub_eq_add_neg, neq (by rw [norm_neg, norm_one]; exact hE), norm_one]

theorem norm_two_le : ‖(2 : K)‖ ≤ 1 := by
  simpa using IsUltrametricDist.norm_natCast_le_one K 2

theorem norm_three_le : ‖(3 : K)‖ ≤ 1 := by
  simpa using IsUltrametricDist.norm_natCast_le_one K 3

theorem norm_eval_le [CompleteSpace K] {f : PowerSeries K} (hf : IntegralPS f) (h0 : coeff 0 f = 0)
    {t : K} (ht : ‖t‖ < 1) : ‖evalPS f t‖ ≤ ‖t‖ := by
  unfold evalPS
  apply IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg t)
  intro n
  rcases n with _ | n
  · simp [h0]
  · rw [norm_mul, norm_pow]
    calc ‖coeff (n + 1) f‖ * ‖t‖ ^ (n + 1) ≤ 1 * ‖t‖ ^ 1 :=
          mul_le_mul (hf _) (pow_le_pow_of_le_one (norm_nonneg _) ht.le (by omega))
            (by positivity) zero_le_one
      _ = ‖t‖ := by simp

theorem integral_w {W : WeierstrassCurve K} {w : PowerSeries K} (hW : IntegralModel W)
    (hw : WFixed W w) : IntegralPS w := by
  let W' : WeierstrassCurve (unitBall K) :=
    ⟨⟨W.a₁, hW.1⟩, ⟨W.a₂, hW.2.1⟩, ⟨W.a₃, hW.2.2.1⟩, ⟨W.a₄, hW.2.2.2.1⟩, ⟨W.a₆, hW.2.2.2.2⟩⟩
  obtain ⟨v, hv, -⟩ := wSeriesExistsUnique_holds.{u} (unitBall K) W'
  have hmap : WFixed W (PowerSeries.map (unitBall K).subtype v) := by
    refine ⟨?_, ?_⟩
    · have h := hv.1
      have : constantCoeff (PowerSeries.map (unitBall K).subtype v)
          = (unitBall K).subtype (constantCoeff v) := by
        rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_map]
      rw [this, h, map_zero]
    · have h := congrArg (PowerSeries.map (unitBall K).subtype) hv.2
      simp only [map_add, map_mul, map_pow, map_X, map_C] at h
      exact h
  have he : w = PowerSeries.map (unitBall K).subtype v := WeierstrassSeriesLimit.fixed_unique W hw hmap
  intro n
  rw [he, coeff_map]
  exact (coeff n v).2

variable [CompleteSpace K]

theorem eval_w {W : WeierstrassCurve K} {w : PowerSeries K} (hW : IntegralModel W)
    (hw : WFixed W w) {t : K} (ht : ‖t‖ < 1) :
    evalPS w t = t ^ 3 + W.a₁ * t * evalPS w t + W.a₂ * t ^ 2 * evalPS w t
        + W.a₃ * evalPS w t ^ 2 + W.a₄ * t * evalPS w t ^ 2 + W.a₆ * evalPS w t ^ 3 ∧
      ‖evalPS w t‖ = ‖t‖ ^ 3 := by
  have hI := integral_w hW hw
  have hwv : Ev w t (evalPS w t) := ⟨absSum_of_integral hI ht, rfl⟩
  have hX := ev_X (K := K) t
  have hR := (((((hX.pow 3).add (((ev_C W.a₁ t).mul hX).mul hwv)).add
    (((ev_C W.a₂ t).mul (hX.pow 2)).mul hwv)).add ((ev_C W.a₃ t).mul (hwv.pow 2))).add
    (((ev_C W.a₄ t).mul hX).mul (hwv.pow 2))).add ((ev_C W.a₆ t).mul (hwv.pow 3))
  have weq := (congrArg (fun f => evalPS f t) hw.2).trans hR.2
  refine ⟨weq, ?_⟩
  set ω := evalPS w t with hω
  have h0 : coeff 0 w = 0 := by simpa using hw.1
  have hωt : ‖ω‖ ≤ ‖t‖ := norm_eval_le hI h0 ht
  have hω1 : ‖ω‖ < 1 := lt_of_le_of_lt hωt ht
  set E := W.a₁ * t + W.a₂ * t ^ 2 + W.a₃ * ω + W.a₄ * (t * ω) + W.a₆ * ω ^ 2 with hE
  have ht2 : ‖t ^ 2‖ < 1 := by rw [sq]; exact smp ht ht
  have hE1 : ‖E‖ < 1 :=
    sm (sm (sm (sm (smm hW.1 ht) (smm hW.2.1 ht2)) (smm hW.2.2.1 hω1))
      (smm hW.2.2.2.1 (smp ht hω1))) (smm hW.2.2.2.2 (by rw [sq]; exact smp hω1 hω1))
  have key : ω * (1 - E) = t ^ 3 := by rw [hE]; linear_combination weq
  have := congrArg norm key
  rw [norm_mul, norm_one_sub hE1, mul_one, norm_pow] at this
  exact this

end Ultra

end FormalGroupPointsParam

open FormalGroupPointsParam in
theorem formal_group_points_param_holds : FormalGroupPointsParametrisation.{u} := by
  intro K _ _ _ W w hW hw
  refine ⟨fun t ht0 ht1 => ?_, fun x y hxy hx => ?_⟩
  · obtain ⟨weq, hn⟩ := eval_w hW hw ht1
    set ω := evalPS w t with hω
    have hω0 : ω ≠ 0 := by
      rw [← norm_pos_iff, hn]; positivity
    have hω1 : ‖ω‖ < 1 := by
      rw [hn]; exact pow_lt_one₀ (norm_nonneg _) ht1 (by norm_num)
    refine ⟨hω0, ?_, ?_, ?_⟩
    · rw [WeierstrassCurve.Affine.nonsingular_iff']
      have heq : (-1 / ω) ^ 2 + W.a₁ * (t / ω) * (-1 / ω) + W.a₃ * (-1 / ω)
          - ((t / ω) ^ 3 + W.a₂ * (t / ω) ^ 2 + W.a₄ * (t / ω) + W.a₆) = 0 := by
        have k : ((-1 / ω) ^ 2 + W.a₁ * (t / ω) * (-1 / ω) + W.a₃ * (-1 / ω)
            - ((t / ω) ^ 3 + W.a₂ * (t / ω) ^ 2 + W.a₄ * (t / ω) + W.a₆)) * ω ^ 3
            = ω - (t ^ 3 + W.a₁ * t * ω + W.a₂ * t ^ 2 * ω + W.a₃ * ω ^ 2 + W.a₄ * t * ω ^ 2
              + W.a₆ * ω ^ 3) := by
          field_simp; ring
        rw [sub_eq_zero.mpr weq] at k
        exact (mul_eq_zero.mp k).resolve_right (pow_ne_zero _ hω0)
      refine ⟨(WeierstrassCurve.Affine.equation_iff' _ _).mpr heq, ?_⟩
      by_contra hc
      push Not at hc
      obtain ⟨hA, hB⟩ := hc
      have eA : -W.a₁ * ω - 3 * t ^ 2 - 2 * W.a₂ * t * ω - W.a₄ * ω ^ 2 = 0 := by
        have k : -W.a₁ * ω - 3 * t ^ 2 - 2 * W.a₂ * t * ω - W.a₄ * ω ^ 2
            = ω ^ 2 * (W.a₁ * (-1 / ω) - (3 * (t / ω) ^ 2 + 2 * W.a₂ * (t / ω) + W.a₄)) := by
          field_simp; ring
        rw [k, hA, mul_zero]
      have eB : -2 + W.a₁ * t + W.a₃ * ω = 0 := by
        have k : -2 + W.a₁ * t + W.a₃ * ω = ω * (2 * (-1 / ω) + W.a₁ * (t / ω) + W.a₃) := by
          field_simp
          try ring
        rw [k, hB, mul_zero]
      set Q := W.a₁ * t + W.a₂ * t ^ 2 + (2 * W.a₃) * ω + (2 * W.a₄) * (t * ω)
        + (3 * W.a₆) * ω ^ 2 with hQ
      have kQ : ω * (1 - Q) = 0 := by
        rw [hQ]; linear_combination ω * eB - t * eA + 3 * weq
      have ht2 : ‖t ^ 2‖ < 1 := by rw [sq]; exact FormalGroupPointsParam.smp ht1 ht1
      have two : ∀ a : K, ‖a‖ ≤ 1 → ‖2 * a‖ ≤ 1 := fun a ha => by
        rw [norm_mul]; exact mul_le_one₀ norm_two_le (norm_nonneg _) ha
      have three : ∀ a : K, ‖a‖ ≤ 1 → ‖3 * a‖ ≤ 1 := fun a ha => by
        rw [norm_mul]; exact mul_le_one₀ norm_three_le (norm_nonneg _) ha
      have hQ1 : ‖Q‖ < 1 :=
        sm (sm (sm (sm (smm hW.1 ht1) (smm hW.2.1 ht2)) (smm (two _ hW.2.2.1) hω1))
          (smm (two _ hW.2.2.2.1) (smp ht1 hω1)))
          (smm (three _ hW.2.2.2.2) (by rw [sq]; exact smp hω1 hω1))
      have h1Q : (1 - Q) ≠ 0 := fun h => by
        have := norm_one_sub hQ1; rw [h, norm_zero] at this; exact zero_ne_one this
      exact (mul_ne_zero hω0 h1Q) kQ
    · rw [norm_div, hn, lt_div_iff₀ (by positivity), one_mul]
      have h2 : ‖t‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg _) ht1 (by norm_num)
      calc ‖t‖ ^ 3 = ‖t‖ * ‖t‖ ^ 2 := by ring
        _ < ‖t‖ * 1 := mul_lt_mul_of_pos_left h2 ht0
        _ = ‖t‖ := mul_one _
    · field_simp
  ·
    have hx0 : x ≠ 0 := by
      rw [← norm_pos_iff]; linarith
    have heq : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
      (WeierstrassCurve.Affine.equation_iff _ _).mp hxy.1
    have hx1 : (1 : ℝ) ≤ ‖x‖ := hx.le
    have hxx : ‖x‖ ≤ ‖x‖ ^ 2 := by nlinarith
    have hx23 : ‖x‖ ^ 2 < ‖x‖ ^ 3 := by
      have : 0 < ‖x‖ ^ 2 := by positivity
      nlinarith
    have hlow : ‖W.a₂ * x ^ 2 + W.a₄ * x + W.a₆‖ ≤ ‖x‖ ^ 2 := by
      refine nle (nle ?_ ?_) ?_
      · rw [norm_mul, norm_pow]; exact mul_le_of_le_one_left (by positivity) hW.2.1
      · rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) hW.2.2.2.1).trans hxx
      · exact hW.2.2.2.2.trans (by nlinarith)
    have hRn : ‖x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆‖ = ‖x‖ ^ 3 := by
      have : x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ = x ^ 3 + (W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) := by
        ring
      rw [this, neq (by rw [norm_pow]; exact lt_of_le_of_lt hlow hx23), norm_pow]
    have hLf : y ^ 2 + W.a₁ * x * y + W.a₃ * y = y * (y + (W.a₁ * x + W.a₃)) := by ring
    rw [← heq, hLf, norm_mul] at hRn

    have hmid : ‖W.a₁ * x + W.a₃‖ ≤ ‖x‖ := by
      refine nle ?_ (hW.2.2.1.trans hx1)
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) hW.1
    have hyx : ‖x‖ < ‖y‖ := by
      by_contra hc
      push Not at hc
      have h1 : ‖y + (W.a₁ * x + W.a₃)‖ ≤ ‖x‖ := nle hc hmid
      have : ‖y‖ * ‖y + (W.a₁ * x + W.a₃)‖ ≤ ‖x‖ * ‖x‖ :=
        mul_le_mul hc h1 (norm_nonneg _) (norm_nonneg _)
      nlinarith
    have hY : ‖y‖ ^ 2 = ‖x‖ ^ 3 := by
      rw [← hRn, neq (lt_of_le_of_lt hmid hyx), sq]
    have hy0 : y ≠ 0 := by
      rw [← norm_pos_iff]; linarith
    have hxpos : 0 < ‖x‖ := by linarith
    have hypos : 0 < ‖y‖ := by linarith
    set z := -x / y with hz
    have hzn : ‖z‖ = ‖x‖ / ‖y‖ := by rw [hz, norm_div, norm_neg]
    have hz0 : 0 < ‖z‖ := by rw [hzn]; positivity
    have hz1 : ‖z‖ < 1 := by rw [hzn, div_lt_one hypos]; exact hyx
    refine ⟨hz0, hz1, ?_⟩
    obtain ⟨weq', hn'⟩ := eval_w hW hw hz1
    set ω' := evalPS w z with hω'
    set ω := -1 / y with hω
    have hωn : ‖ω‖ = ‖z‖ ^ 3 := by
      rw [hω, hzn, norm_div, norm_neg, norm_one, div_pow, ← hY]
      field_simp
    have weq : ω = z ^ 3 + W.a₁ * z * ω + W.a₂ * z ^ 2 * ω + W.a₃ * ω ^ 2 + W.a₄ * z * ω ^ 2
        + W.a₆ * ω ^ 3 := by
      rw [hω, hz]
      field_simp
      linear_combination -heq
    have hω1 : ‖ω‖ < 1 := by rw [hωn]; exact pow_lt_one₀ (norm_nonneg _) hz1 (by norm_num)
    have hω'1 : ‖ω'‖ < 1 := by rw [hn']; exact pow_lt_one₀ (norm_nonneg _) hz1 (by norm_num)
    set E := W.a₁ * z + W.a₂ * z ^ 2 + W.a₃ * (ω + ω') + W.a₄ * (z * (ω + ω'))
      + W.a₆ * (ω ^ 2 + ω * ω' + ω' ^ 2) with hE
    have hz2 : ‖z ^ 2‖ < 1 := by rw [sq]; exact smp hz1 hz1
    have hs : ‖ω + ω'‖ < 1 := sm hω1 hω'1
    have hE1 : ‖E‖ < 1 :=
      sm (sm (sm (sm (smm hW.1 hz1) (smm hW.2.1 hz2)) (smm hW.2.2.1 hs))
        (smm hW.2.2.2.1 (smp hz1 hs)))
        (smm hW.2.2.2.2 (sm (sm (by rw [sq]; exact smp hω1 hω1) (smp hω1 hω'1))
          (by rw [sq]; exact smp hω'1 hω'1)))
    have key : (ω - ω') * (1 - E) = 0 := by
      rw [hE]; linear_combination weq - weq'
    have h1E : (1 - E) ≠ 0 := fun h => by
      have := norm_one_sub hE1; rw [h, norm_zero] at this; exact zero_ne_one this
    have hωω : ω = ω' := sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right h1E)
    rw [← hωω, hω, hz]
    constructor
    · field_simp
    · field_simp

theorem formal_group_points_param_of (_hU : WSubstUnique.{u}) : FormalGroupPointsParametrisation.{u} := formal_group_points_param_holds

end Formalism.ELL
