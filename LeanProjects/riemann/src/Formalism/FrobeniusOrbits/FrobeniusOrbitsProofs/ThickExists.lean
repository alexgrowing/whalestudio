import Mathlib
import Formalism.FrobeniusOrbits.HostThickExists
import Lemmata.GeneralBFactSecondLast.Imports

open Finset

noncomputable section

namespace Formalism.FrobeniusOrbits.ThickExists

lemma coeff_zero (B : ℤ) : ∀ {S : ℕ} (c : Fin S → ℤ), (∀ m, |c m| < B) →
    ∑ m, c m * B ^ (m : ℕ) = 0 → ∀ m, c m = 0 := by
  first | exact Bl.general_b_fact_second_last.goal1 .. | (apply Bl.general_b_fact_second_last.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_last.goal1 <;> assumption)

lemma map_lt (B : ℕ) : ∀ {S : ℕ} (v : Fin S → ℕ), (∀ m, v m < B) → Behrend.map B v < B ^ S := by
  intro S
  induction S with
  | zero => intro v _; simp [Behrend.map_apply]
  | succ S ih =>
    intro v hv
    have h1 := ih (fun m => v m.succ) (fun m => hv _)
    have hsplit : Behrend.map B v = v 0 + B * Behrend.map B (fun m : Fin S => v m.succ) := by
      simp only [Behrend.map_apply]
      rw [Fin.sum_univ_succ, Finset.mul_sum]
      congr 1
      · simp
      · refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [Fin.val_succ, pow_succ]
        ring
    rw [hsplit, pow_succ]
    have h2 : B * (Behrend.map B (fun m : Fin S => v m.succ) + 1) ≤ B * B ^ S :=
      Nat.mul_le_mul_left B h1
    have h3 := hv 0
    nlinarith

lemma sphere_rel {S : ℕ} (v₁ v₂ v₃ : Fin S → ℤ) (k : ℤ) (h₁ : ∑ m, v₁ m ^ 2 = k)
    (h₂ : ∑ m, v₂ m ^ 2 = k) (h₃ : ∑ m, v₃ m ^ 2 = k) (i j : ℤ) (hj : j ≠ 0) (hij : i ≠ j)
    (h : ∀ m, j * (v₂ m - v₁ m) = i * (v₃ m - v₁ m)) : v₂ = v₁ := by
  have hA : ∑ m, (2 * v₁ m * (v₂ m - v₁ m) + (v₂ m - v₁ m) ^ 2) = 0 := by
    have e : ∀ m, 2 * v₁ m * (v₂ m - v₁ m) + (v₂ m - v₁ m) ^ 2 = v₂ m ^ 2 - v₁ m ^ 2 :=
      fun m => by ring
    rw [Finset.sum_congr rfl (fun m _ => e m), Finset.sum_sub_distrib, h₂, h₁, sub_self]
  have hB : ∑ m, (2 * v₁ m * (v₃ m - v₁ m) + (v₃ m - v₁ m) ^ 2) = 0 := by
    have e : ∀ m, 2 * v₁ m * (v₃ m - v₁ m) + (v₃ m - v₁ m) ^ 2 = v₃ m ^ 2 - v₁ m ^ 2 :=
      fun m => by ring
    rw [Finset.sum_congr rfl (fun m _ => e m), Finset.sum_sub_distrib, h₃, h₁, sub_self]
  have hW : ∑ m, i * (i - j) * (v₃ m - v₁ m) ^ 2 = 0 := by
    have e : ∀ m, i * (i - j) * (v₃ m - v₁ m) ^ 2
        = j ^ 2 * (2 * v₁ m * (v₂ m - v₁ m) + (v₂ m - v₁ m) ^ 2)
          - i * j * (2 * v₁ m * (v₃ m - v₁ m) + (v₃ m - v₁ m) ^ 2) := fun m => by
      linear_combination (-(2 * j * v₁ m + j * (v₂ m - v₁ m) + i * (v₃ m - v₁ m))) * h m
    rw [Finset.sum_congr rfl (fun m _ => e m), Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hA, hB, mul_zero, mul_zero, sub_zero]
  by_cases hi : i = 0
  · funext m
    have h' := h m
    rw [hi, zero_mul] at h'
    have h'' := (mul_eq_zero.mp h').resolve_left hj
    linarith
  · have hne : i * (i - j) ≠ 0 := mul_ne_zero hi (sub_ne_zero.mpr hij)
    rw [← Finset.mul_sum] at hW
    have hs0 := (mul_eq_zero.mp hW).resolve_left hne
    have hw0 : ∀ m, v₃ m - v₁ m = 0 := by
      intro m
      have h' := (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => sq_nonneg (v₃ m - v₁ m))).mp hs0 m
        (Finset.mem_univ m)
      exact (pow_eq_zero_iff two_ne_zero).mp h'
    funext m
    have h' := h m
    rw [hw0 m, mul_zero] at h'
    have h'' := (mul_eq_zero.mp h').resolve_left hj
    linarith

lemma cast_map (B : ℕ) {S : ℕ} (v : Fin S → ℕ) :
    ((Behrend.map B v : ℕ) : ℤ) = ∑ m, (v m : ℤ) * (B : ℤ) ^ (m : ℕ) := by
  rw [Behrend.map_apply, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Nat.cast_mul, Nat.cast_pow]

private lemma sphere_mem_lemma {S d k : ℕ} {v : Fin S → ℕ} (hv : v ∈ Behrend.sphere S d k) :
    (∀ i, v i < d) ∧ ∑ i, v i ^ 2 = k := by
  simp only [Behrend.sphere, Finset.mem_filter, Behrend.mem_box] at hv
  exact hv

lemma noRel_image (L S d k : ℕ) (hL : 1 ≤ L) :
    NoRel ((Behrend.sphere S d k).image (Behrend.map (4 * L * d))) L := by
  unfold NoRel
  intro s₁ hs₁ s₂ hs₂ s₃ hs₃ h12 h13 h23 i j hi0 hiL hj0 hjL hij heq
  rw [Finset.mem_image] at hs₁ hs₂ hs₃
  obtain ⟨v₁, hv₁, rfl⟩ := hs₁
  obtain ⟨v₂, hv₂, rfl⟩ := hs₂
  obtain ⟨v₃, hv₃, rfl⟩ := hs₃
  obtain ⟨hb₁, hq₁⟩ := sphere_mem_lemma hv₁
  obtain ⟨hb₂, hq₂⟩ := sphere_mem_lemma hv₂
  obtain ⟨hb₃, hq₃⟩ := sphere_mem_lemma hv₃
  rw [cast_map, cast_map, cast_map] at heq
  obtain ⟨B, hB⟩ : ∃ B : ℤ, B = ((4 * L * d : ℕ) : ℤ) := ⟨_, rfl⟩
  rw [← hB] at heq
  have hL' : (1 : ℤ) ≤ L := by exact_mod_cast hL
  obtain ⟨hi1, hi2⟩ := abs_le.mp hiL
  obtain ⟨hj1, hj2⟩ := abs_le.mp hjL
  have hbound : ∀ m : Fin S, |j * ((v₂ m : ℤ) - v₁ m) - i * ((v₃ m : ℤ) - v₁ m)| < B := by
    intro m
    have a1 : (v₁ m : ℤ) < d := by exact_mod_cast hb₁ m
    have a2 : (v₂ m : ℤ) < d := by exact_mod_cast hb₂ m
    have a3 : (v₃ m : ℤ) < d := by exact_mod_cast hb₃ m
    have z1 : (0 : ℤ) ≤ v₁ m := by positivity
    have z2 : (0 : ℤ) ≤ v₂ m := by positivity
    have z3 : (0 : ℤ) ≤ v₃ m := by positivity
    have hdpos : (1 : ℤ) ≤ d := by omega
    have f1 : (0 : ℤ) ≤ L - j := by linarith
    have f2 : (0 : ℤ) ≤ L + j := by linarith
    have f3 : (0 : ℤ) ≤ L - i := by linarith
    have f4 : (0 : ℤ) ≤ L + i := by linarith
    have g1 : (0 : ℤ) ≤ d + ((v₂ m : ℤ) - v₁ m) := by linarith
    have g2 : (0 : ℤ) ≤ d - ((v₂ m : ℤ) - v₁ m) := by linarith
    have g3 : (0 : ℤ) ≤ d + ((v₃ m : ℤ) - v₁ m) := by linarith
    have g4 : (0 : ℤ) ≤ d - ((v₃ m : ℤ) - v₁ m) := by linarith
    have hLd : (1 : ℤ) ≤ L * d := by nlinarith
    rw [hB]
    push_cast
    rw [abs_lt]
    constructor <;> nlinarith [mul_nonneg f1 g1, mul_nonneg f2 g2, mul_nonneg f1 g2,
      mul_nonneg f2 g1, mul_nonneg f3 g3, mul_nonneg f4 g4, mul_nonneg f3 g4, mul_nonneg f4 g3]
  have hsum : ∑ m, (j * ((v₂ m : ℤ) - v₁ m) - i * ((v₃ m : ℤ) - v₁ m)) * B ^ (m : ℕ) = 0 := by
    have E : ∑ m, (j * ((v₂ m : ℤ) - v₁ m) - i * ((v₃ m : ℤ) - v₁ m)) * B ^ (m : ℕ)
        = ∑ m, (j * ((v₂ m : ℤ) * B ^ (m : ℕ)) - j * ((v₁ m : ℤ) * B ^ (m : ℕ))
          - i * ((v₃ m : ℤ) * B ^ (m : ℕ)) + i * ((v₁ m : ℤ) * B ^ (m : ℕ))) :=
      Finset.sum_congr rfl (fun m _ => by ring)
    rw [E, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    linear_combination heq
  have hzero := coeff_zero B (fun m => j * ((v₂ m : ℤ) - v₁ m) - i * ((v₃ m : ℤ) - v₁ m))
    hbound hsum
  have q₁ : ∑ m, ((v₁ m : ℕ) : ℤ) ^ 2 = (k : ℤ) := by exact_mod_cast hq₁
  have q₂ : ∑ m, ((v₂ m : ℕ) : ℤ) ^ 2 = (k : ℤ) := by exact_mod_cast hq₂
  have q₃ : ∑ m, ((v₃ m : ℕ) : ℤ) ^ 2 = (k : ℤ) := by exact_mod_cast hq₃
  have hrel := sphere_rel (fun m => (v₁ m : ℤ)) (fun m => (v₂ m : ℤ)) (fun m => (v₃ m : ℤ))
    (k : ℤ) q₁ q₂ q₃ i j (abs_pos.mp hj0) hij (fun m => by
      show j * ((v₂ m : ℤ) - v₁ m) = i * ((v₃ m : ℤ) - v₁ m)
      have h0 : j * ((v₂ m : ℤ) - v₁ m) - i * ((v₃ m : ℤ) - v₁ m) = 0 := hzero m
      linarith)
  have hv : v₂ = v₁ := funext fun m => Nat.cast_injective (congrFun hrel m)
  exact h12 (by rw [hv])

lemma card_image (L S d k : ℕ) (hL : 1 ≤ L) :
    ((Behrend.sphere S d k).image (Behrend.map (4 * L * d))).card =
      (Behrend.sphere S d k).card := by
  apply Finset.card_image_of_injOn
  intro v hv w hw hvw
  obtain ⟨hbv, -⟩ := sphere_mem_lemma (Finset.mem_coe.mp hv)
  obtain ⟨hbw, -⟩ := sphere_mem_lemma (Finset.mem_coe.mp hw)
  have hc : ((Behrend.map (4 * L * d) v : ℕ) : ℤ) = ((Behrend.map (4 * L * d) w : ℕ) : ℤ) := by
    rw [hvw]
  rw [cast_map, cast_map] at hc
  have hbound : ∀ m : Fin S, |(v m : ℤ) - w m| < ((4 * L * d : ℕ) : ℤ) := by
    intro m
    have a1 : (v m : ℤ) < d := by exact_mod_cast hbv m
    have a2 : (w m : ℤ) < d := by exact_mod_cast hbw m
    have z1 : (0 : ℤ) ≤ v m := by positivity
    have z2 : (0 : ℤ) ≤ w m := by positivity
    have z3 : (0 : ℤ) ≤ d := by positivity
    have hL' : (1 : ℤ) ≤ L := by exact_mod_cast hL
    push_cast
    rw [abs_lt]
    constructor <;> nlinarith
  have hsum : ∑ m, ((v m : ℤ) - w m) * ((4 * L * d : ℕ) : ℤ) ^ (m : ℕ) = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [hc, sub_self]
  have hz := coeff_zero ((4 * L * d : ℕ) : ℤ) (fun m => (v m : ℤ) - w m) hbound hsum
  funext m
  have h0 : (v m : ℤ) - w m = 0 := hz m
  omega

end Formalism.FrobeniusOrbits.ThickExists

namespace Formalism.FrobeniusOrbits

set_option maxHeartbeats 1000000 in
open ThickExists in
theorem hostThickExists : HostThickExists := by
  unfold HostThickExists
  refine ⟨32, by norm_num, ?_⟩
  intro n L hL
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by linarith
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = Real.log (L : ℝ) := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = Real.log (n : ℝ) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt (x * y) := ⟨_, rfl⟩
  have hrw : Real.sqrt (Real.log (n : ℝ) * Real.log (L : ℝ)) = s := by rw [hs, hx, hy]
  rw [hrw]
  have hy_half : (1 : ℝ) / 2 < y := by
    have h1 := Real.log_two_gt_d9
    have h2 := Real.log_le_log (by norm_num) hL2
    rw [hy]
    linarith
  have hy0 : 0 < y := by linarith
  by_cases hsmall : (n : ℝ) * Real.exp (-32 * s) / L ≤ 1
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · refine ⟨∅, by simp, ?_, by simp [hn]⟩
      unfold NoRel
      intro s₁ hs₁
      simp at hs₁
    · refine ⟨{0}, ?_, ?_, ?_⟩
      · intro m hm
        rw [Finset.mem_singleton] at hm
        subst hm
        simpa using hn
      · unfold NoRel
        intro s₁ hs₁ s₂ hs₂ s₃ hs₃ h12
        rw [Finset.mem_singleton] at hs₁ hs₂
        exact absurd (hs₁.trans hs₂.symm) h12
      · rw [Finset.card_singleton, Nat.cast_one]
        exact hsmall
  push_neg at hsmall
  have hnpos : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn] at hsmall
      norm_num at hsmall
    · exact_mod_cast hn
  have eL : Real.exp y = L := by rw [hy, Real.exp_log hLpos]
  have en : Real.exp x = n := by rw [hx, Real.exp_log hnpos]
  have hpos : 0 < x + -32 * s - y := by
    rw [← Real.exp_lt_exp, Real.exp_zero, Real.exp_sub, Real.exp_add, eL, en]
    exact hsmall
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hxpos : 0 < x := by linarith
  have hs2 : s ^ 2 = x * y := by rw [hs]; exact Real.sq_sqrt (mul_pos hxpos hy0).le
  have hs32 : 32 * y < s := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hc), mul_pos hpos hy0, sq_nonneg y]
  have hs16 : 16 < s := by linarith
  obtain ⟨S, hSdef⟩ : ∃ S : ℕ, S = ⌊s / y⌋₊ := ⟨_, rfl⟩
  have hS1 : (S : ℝ) ≤ s / y := by rw [hSdef]; exact Nat.floor_le (div_nonneg hs0 hy0.le)
  have hS2 : s / y < S + 1 := by rw [hSdef]; exact Nat.lt_floor_add_one _
  have hSy : (S : ℝ) * y ≤ s := (le_div_iff₀ hy0).mp hS1
  have hSy2 : s < (S + 1) * y := (div_lt_iff₀ hy0).mp hS2
  have hS31 : (31 : ℝ) < S := by
    have h := lt_of_mul_lt_mul_right (show (32 : ℝ) * y < (S + 1) * y by linarith) hy0.le
    linarith
  have hSpos : (0 : ℝ) < S := by linarith
  have hSne : (S : ℝ) ≠ 0 := hSpos.ne'
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (x - y - 3) / S := ⟨_, rfl⟩
  have haS : a * S = x - y - 3 := by rw [ha]; field_simp
  have h2Sy : s ≤ 2 * S * y := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ S - 1) hy0.le]
  have hxle : x ≤ 2 * s * S := by
    have h : x * y ≤ (2 * s * S) * y := by nlinarith [mul_le_mul_of_nonneg_left h2Sy hs0]
    exact le_of_mul_le_mul_right h hy0
  have ha2s : a ≤ 2 * s := by
    have h : a * S ≤ (2 * s) * S := by nlinarith
    exact le_of_mul_le_mul_right h hSpos
  have ha7 : 7 + y ≤ a := by
    have h1 : (7 + y) * S * y ≤ (x - y - 3) * y := by
      nlinarith [mul_nonneg hy0.le (sub_nonneg.mpr hSy), mul_nonneg hs0 (sub_nonneg.mpr hs32.le),
        mul_nonneg hy0.le (sub_nonneg.mpr hs32.le), mul_nonneg hs0 (sub_nonneg.mpr hy_half.le)]
    have h2 : (7 + y) * S ≤ x - y - 3 := le_of_mul_le_mul_right h1 hy0
    exact le_of_mul_le_mul_right (by rw [haS]; exact h2) hSpos
  have hexpb : 3 + S * (7 + y) + S + 2 * a ≤ 32 * s := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy_half.le) hSpos.le]
  have h4L : (0 : ℝ) < 4 * L := by positivity
  obtain ⟨d, hddef⟩ : ∃ d : ℕ, d = ⌊Real.exp a / (4 * L)⌋₊ := ⟨_, rfl⟩
  have hd1 : (d : ℝ) ≤ Real.exp a / (4 * L) := by rw [hddef]; exact Nat.floor_le (by positivity)
  have hd2 : Real.exp a / (4 * L) < d + 1 := by rw [hddef]; exact Nat.lt_floor_add_one _
  have hd1' : (d : ℝ) * (4 * L) ≤ Real.exp a := (le_div_iff₀ h4L).mp hd1
  have hd2' : Real.exp a < (d + 1) * (4 * L) := (div_lt_iff₀ h4L).mp hd2
  have h8Ly : 8 * (L : ℝ) ≤ Real.exp (7 + y) := by
    have h87 : (8 : ℝ) ≤ Real.exp 7 := by linarith [Real.add_one_le_exp (7 : ℝ)]
    rw [Real.exp_add, eL]
    nlinarith
  have h8L : 8 * (L : ℝ) ≤ Real.exp a := le_trans h8Ly (Real.exp_le_exp.mpr ha7)
  have hQd : Real.exp a / (8 * L) ≤ d := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hd1r : (1 : ℝ) ≤ d := le_trans ((one_le_div (by positivity)).mpr h8L) hQd
  have hdpos : (0 : ℝ) < d := by linarith
  have hdQ : (d : ℝ) ≤ Real.exp a := by
    nlinarith [mul_nonneg hdpos.le (by linarith : (0 : ℝ) ≤ 4 * L - 1)]
  have hdS : Real.exp a ^ S ≤ (d : ℝ) ^ S * (8 * L) ^ S := by
    have h : (Real.exp a / (8 * L)) ^ S ≤ (d : ℝ) ^ S := by gcongr
    rwa [div_pow, div_le_iff₀ (by positivity)] at h
  have hQS : Real.exp a ^ S = Real.exp (x - y - 3) := by
    rw [← Real.exp_nat_mul, mul_comm, haS]
  have hn_eq : (n : ℝ) = Real.exp a ^ S * L * Real.exp 3 := by
    rw [hQS, ← eL, ← Real.exp_add, ← Real.exp_add, ← en]
    congr 1
    ring
  have hprod : Real.exp 3 * (8 * L) ^ S * S * Real.exp a ^ 2 ≤ Real.exp (32 * s) := by
    have hP : ((8 : ℝ) * L) ^ S ≤ Real.exp (S * (7 + y)) := by
      rw [Real.exp_nat_mul]
      gcongr
    have hSe : (S : ℝ) ≤ Real.exp S := by linarith [Real.add_one_le_exp (S : ℝ)]
    have hQ2 : Real.exp a ^ 2 = Real.exp (2 * a) := by rw [sq, ← Real.exp_add, two_mul]
    calc Real.exp 3 * (8 * L) ^ S * S * Real.exp a ^ 2
        ≤ Real.exp 3 * Real.exp (S * (7 + y)) * Real.exp S * Real.exp (2 * a) := by
          rw [hQ2]
          gcongr
      _ = Real.exp (3 + S * (7 + y) + S + 2 * a) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_add]
      _ ≤ Real.exp (32 * s) := Real.exp_le_exp.mpr hexpb
  obtain ⟨k, hk⟩ := Behrend.exists_large_sphere S d
  refine ⟨(Behrend.sphere S d k).image (Behrend.map (4 * L * d)), ?_,
    noRel_image L S d k (by omega), ?_⟩
  · intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨v, hv, rfl⟩ := hm
    obtain ⟨hbox, -⟩ := sphere_mem_lemma hv
    have hdd : d ≤ 4 * L * d := by nlinarith
    have hmlt := map_lt (4 * L * d) v (fun i => lt_of_lt_of_le (hbox i) hdd)
    have hpowle : ((4 : ℝ) * L * d) ^ S ≤ Real.exp a ^ S := by
      gcongr
      linarith
    have hreal : (4 : ℝ) * L * (4 * L * d) ^ S ≤ n := by
      nlinarith [mul_le_mul_of_nonneg_left hpowle h4L.le,
        mul_nonneg (by linarith [Real.add_one_le_exp (3 : ℝ)] : (0 : ℝ) ≤ Real.exp 3 - 4)
          (by positivity : (0 : ℝ) ≤ L * Real.exp a ^ S)]
    have hnat : 4 * L * (4 * L * d) ^ S ≤ n := by exact_mod_cast hreal
    exact lt_of_lt_of_le (mul_lt_mul_of_pos_left hmlt (by omega)) hnat
  · rw [card_image L S d k (by omega)]
    refine le_trans ?_ hk
    push_cast
    rw [div_le_iff₀ hLpos, div_mul_eq_mul_div, le_div_iff₀ (mul_pos hSpos (pow_pos hdpos 2))]
    calc (n : ℝ) * Real.exp (-32 * s) * (S * d ^ 2)
        ≤ n * Real.exp (-32 * s) * (S * Real.exp a ^ 2) := by gcongr
      _ = (Real.exp a ^ S * L * Real.exp 3) * Real.exp (-32 * s) * (S * Real.exp a ^ 2) := by
          rw [← hn_eq]
      _ ≤ ((d : ℝ) ^ S * (8 * L) ^ S * L * Real.exp 3) * Real.exp (-32 * s)
            * (S * Real.exp a ^ 2) := by gcongr
      _ = (d : ℝ) ^ S * L * (Real.exp (-32 * s) * (Real.exp 3 * (8 * L) ^ S * S * Real.exp a ^ 2)) := by
          ring
      _ ≤ (d : ℝ) ^ S * L * (Real.exp (-32 * s) * Real.exp (32 * s)) := by gcongr
      _ = (d : ℝ) ^ S * L := by
          rw [← Real.exp_add, show -32 * s + 32 * s = 0 by ring, Real.exp_zero, mul_one]

end Formalism.FrobeniusOrbits
