import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaDMLinear
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem ofCoeff_add_of_disjoint {f g : ℕ → L} (h : ∀ n, f n = 0 ∨ g n = 0) :
    T.ofCoeff f + T.ofCoeff g = T.ofCoeff (f + g) := by
  have hfin : ∀ n, T.finSum f n + T.finSum g n = T.finSum (f + g) n := fun n => by
    simp only [finSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases h i with hi | hi <;> simp [hi]
  have hall : ∀ n, T.ofCoeff f + T.ofCoeff g - T.ofCoeff (f + g) ∈ Ideal.span {T.π ^ n} := by
    intro n
    have : T.ofCoeff f + T.ofCoeff g - T.ofCoeff (f + g) = (T.ofCoeff f - T.finSum f n) +
        (T.ofCoeff g - T.finSum g n) - (T.ofCoeff (f + g) - T.finSum (f + g) n) := by
      rw [← hfin n]; ring
    rw [this]
    exact sub_mem (add_mem (T.mk_sub_finSum_mem f n) (T.mk_sub_finSum_mem g n))
      (T.mk_sub_finSum_mem _ n)
  have h0 : T.ofCoeff f + T.ofCoeff g - T.ofCoeff (f + g) = 0 := T.eq_of_coeff_eq (funext fun n => by
    rw [T.coeff_zero_elem]; exact T.coeff_of_mem_span (hall (n + 1)) n le_rfl)
  exact sub_eq_zero.1 h0

def splitS (θ : ℝ) (x : Γ) : Γ :=
  T.ofCoeff fun n => if ‖T.coeff x n‖ < θ then T.coeff x n else 0

def splitB (θ : ℝ) (x : Γ) : Γ :=
  T.ofCoeff fun n => if ‖T.coeff x n‖ < θ then 0 else T.coeff x n

theorem coeff_splitS (θ : ℝ) (x : Γ) (n : ℕ) :
    T.coeff (T.splitS θ x) n = if ‖T.coeff x n‖ < θ then T.coeff x n else 0 := by
  simp [splitS]

theorem coeff_splitB (θ : ℝ) (x : Γ) (n : ℕ) :
    T.coeff (T.splitB θ x) n = if ‖T.coeff x n‖ < θ then 0 else T.coeff x n := by
  simp [splitB]

theorem splitS_add_splitB (θ : ℝ) (x : Γ) : T.splitS θ x + T.splitB θ x = x := by
  rw [splitS, splitB, T.ofCoeff_add_of_disjoint (fun n => by split_ifs <;> simp)]
  conv_rhs => rw [← T.ofCoeff_coeff x]
  congr 1; funext n; simp only [Pi.add_apply]; split_ifs <;> simp

def den (b : T.B) : ℕ := (IsLocalization.Away.surj T.π b).choose

def num (b : T.B) : Γ := (IsLocalization.Away.surj T.π b).choose_spec.choose

theorem num_spec (b : T.B) : b * algebraMap Γ T.B T.π ^ T.den b = algebraMap Γ T.B (T.num b) :=
  (IsLocalization.Away.surj T.π b).choose_spec.choose_spec

theorem invSelf_pow_mul_pow (N : ℕ) :
    IsLocalization.Away.invSelf T.π ^ N * algebraMap Γ T.B T.π ^ N = 1 := by
  rw [← mul_pow, mul_comm, IsLocalization.Away.mul_invSelf, one_pow]

theorem eq_num_mul (b : T.B) :
    b = algebraMap Γ T.B (T.num b) * IsLocalization.Away.invSelf T.π ^ T.den b := by
  rw [← T.num_spec, mul_assoc, mul_comm (_ ^ _), T.invSelf_pow_mul_pow, mul_one]

def smallPart (θ : ℝ) (b : T.B) : T.B :=
  algebraMap Γ T.B (T.splitS θ (T.num b)) * IsLocalization.Away.invSelf T.π ^ T.den b

def bigPart (θ : ℝ) (b : T.B) : T.B :=
  algebraMap Γ T.B (T.splitB θ (T.num b)) * IsLocalization.Away.invSelf T.π ^ T.den b

theorem smallPart_add_bigPart (θ : ℝ) (b : T.B) : T.smallPart θ b + T.bigPart θ b = b := by
  rw [smallPart, bigPart, ← add_mul, ← map_add, T.splitS_add_splitB, ← T.eq_num_mul]

theorem mul_pow_eq_of_invSelf {x : Γ} (N : ℕ) :
    (algebraMap Γ T.B x * IsLocalization.Away.invSelf T.π ^ N) * algebraMap Γ T.B T.π ^ N =
      algebraMap Γ T.B x := by
  rw [mul_assoc, T.invSelf_pow_mul_pow, mul_one]

theorem coeffB_smallPart (θ : ℝ) (hθ : 0 < θ) (b : T.B) (n : ℤ) :
    T.coeffB (T.smallPart θ b) n = if ‖T.coeffB b n‖ < θ then T.coeffB b n else 0 := by
  rw [smallPart, T.coeffB_eq (T.mul_pow_eq_of_invSelf _), T.coeffB_eq (T.num_spec b)]
  simp only
  rcases lt_or_ge (n + T.den b) 0 with h | h
  · rw [T.zcoeff_of_neg _ h, T.zcoeff_of_neg _ h]; simp [hθ]
  · lift n + T.den b to ℕ using h with k
    rw [zcoeff_natCast, zcoeff_natCast, coeff_splitS]

theorem coeffB_bigPart (θ : ℝ) (b : T.B) (n : ℤ) :
    T.coeffB (T.bigPart θ b) n = if ‖T.coeffB b n‖ < θ then 0 else T.coeffB b n := by
  rw [bigPart, T.coeffB_eq (T.mul_pow_eq_of_invSelf _), T.coeffB_eq (T.num_spec b)]
  simp only
  rcases lt_or_ge (n + T.den b) 0 with h | h
  · rw [T.zcoeff_of_neg _ h, T.zcoeff_of_neg _ h]; simp
  · lift n + T.den b to ℕ using h with k
    rw [zcoeff_natCast, zcoeff_natCast, coeff_splitB]

end TeichLift

section Dominate

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

theorem convergesAt_of_norm_le {a b : ℤ → K} {ρ : ℝ} (hρ : 0 < ρ) (h : ∀ n, ‖a n‖ ≤ ‖b n‖)
    (hb : ConvergesAt b ρ) : ConvergesAt a ρ ∧ gaussNorm a ρ ≤ gaussNorm b ρ := by
  refine ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun n => mul_nonneg (norm_nonneg _) (zpow_pos hρ n).le)
    (fun n => mul_le_mul_of_nonneg_right (h n) (zpow_pos hρ n).le), ?_⟩
  exact gaussNorm_le fun n =>
    (mul_le_mul_of_nonneg_right (h n) (zpow_pos hρ n).le).trans (hb.le_gaussNorm n)

end Dominate

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem norm_coeffB_smallPart_le {θ : ℝ} (hθ : 0 < θ) (b : T.B) (n : ℤ) :
    ‖T.coeffB (T.smallPart θ b) n‖ ≤ ‖T.coeffB b n‖ := by
  rw [T.coeffB_smallPart θ hθ]; split_ifs <;> simp

theorem norm_coeffB_bigPart_le (θ : ℝ) (b : T.B) (n : ℤ) :
    ‖T.coeffB (T.bigPart θ b) n‖ ≤ ‖T.coeffB b n‖ := by
  rw [T.coeffB_bigPart]; split_ifs <;> simp

theorem norm_coeffB_smallPart_lt {θ : ℝ} (hθ : 0 < θ) (b : T.B) (n : ℤ) :
    ‖T.coeffB (T.smallPart θ b) n‖ < θ := by
  rw [T.coeffB_smallPart θ hθ]; split_ifs with h
  · exact h
  · simpa using hθ

theorem coeffB_bigPart_eq_zero_or (θ : ℝ) (b : T.B) (n : ℤ) :
    T.coeffB (T.bigPart θ b) n = 0 ∨ θ ≤ ‖T.coeffB (T.bigPart θ b) n‖ := by
  rw [T.coeffB_bigPart]; split_ifs with h
  · exact Or.inl rfl
  · exact Or.inr (not_lt.1 h)

theorem zcoeff_weight_le {x : Γ} {ρ Y : ℝ} (hY : 0 ≤ Y)
    (h : ∀ n : ℕ, ‖T.coeff x n‖ * ρ ^ n ≤ Y) (j : ℤ) : ‖T.zcoeff x j‖ * ρ ^ j ≤ Y := by
  rcases lt_or_ge j 0 with hj | hj
  · rw [T.zcoeff_of_neg _ hj, norm_zero, zero_mul]; exact hY
  · lift j to ℕ using hj
    rw [zcoeff_natCast, zpow_natCast]; exact h j

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

namespace TeichFrob

variable (F : T.TeichFrob)

theorem toB_invSelf {v : Γ} (hv : F.u * v = 1) :
    F.toB (IsLocalization.Away.invSelf T.π) =
      IsLocalization.Away.invSelf T.π * algebraMap Γ T.B v := by
  have e1 : algebraMap Γ T.B T.π * algebraMap Γ T.B F.u * F.toB (IsLocalization.Away.invSelf T.π) = 1 := by
    rw [← map_mul, ← F.φ_π, ← F.toB_algebraMap, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  have e2 : algebraMap Γ T.B T.π * IsLocalization.Away.invSelf T.π = 1 :=
    IsLocalization.Away.mul_invSelf T.π
  have e3 : algebraMap Γ T.B F.u * algebraMap Γ T.B v = 1 := by rw [← map_mul, hv, map_one]
  linear_combination (IsLocalization.Away.invSelf T.π * algebraMap Γ T.B v) * e1 -
    (F.toB (IsLocalization.Away.invSelf T.π) * algebraMap Γ T.B F.u * algebraMap Γ T.B v) * e2 -
    F.toB (IsLocalization.Away.invSelf T.π) * e3

theorem exists_sol_big [IsAlgClosed L] (ha : 0 < F.a) (c : ℕ) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    {b : T.B} (hbig : ∀ n, T.coeffB b n = 0 ∨ θ ≤ ‖T.coeffB b n‖) :
    ∃ z : T.B, F.toB z - algebraMap Γ T.B T.π ^ c * z = b ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ConvergesAt (T.coeffB b) ρ → ∀ n, ‖T.coeffB z n‖ * ρ ^ n ≤ θ⁻¹ * gaussNorm (T.coeffB b) ρ := by
  by_cases hb0 : b = 0
  · refine ⟨0, by simp [hb0], fun ρ hρ0 _ hb n => ?_⟩
    rw [← map_zero (algebraMap Γ T.B), T.coeffB_algebraMap, (T.zcoeff_eq_zero_iff 0).2 rfl]
    simp only [Pi.zero_apply, norm_zero, zero_mul]
    exact mul_nonneg (inv_nonneg.2 hθ.le) (gaussNorm_nonneg hρ0)
  obtain ⟨v, hvint, huv, hv1⟩ := F.exists_inv_u
  set N := T.den b
  set x := T.num b
  have hx0 : x ≠ 0 := by
    intro h
    apply hb0
    rw [T.eq_num_mul b]
    change algebraMap Γ T.B x * _ = 0
    rw [h, map_zero, zero_mul]
  obtain ⟨m, x', hxx', hx'0, hz⟩ := T.exists_eq_π_pow_mul hx0
  set α := F.u ^ m * v ^ N
  have hα : α ∈ T.int := mul_mem (pow_mem F.u_mem_int m) (pow_mem hvint N)
  have hα1 : ‖T.red α‖ = 1 := by
    simp only [α, map_mul, map_pow, norm_mul, norm_pow, F.norm_red_u, hv1, one_pow, one_mul]
  obtain ⟨z', hz'eq, hz'b⟩ := F.exists_linear_sol ha hα hα1 (T.π ^ c) x'
  set P : T.B := algebraMap Γ T.B (T.π ^ m) * IsLocalization.Away.invSelf T.π ^ N
  have hP : F.toB P = P * algebraMap Γ T.B α := by
    simp only [P, α, map_mul, map_pow, F.toB_algebraMap, F.φ_π, F.toB_invSelf huv]
    ring
  refine ⟨algebraMap Γ T.B z' * P, ?_, fun ρ hρ0 hρ1 hb n => ?_⟩
  · rw [map_mul, hP, F.toB_algebraMap]
    have : algebraMap Γ T.B (F.φ z') * (P * algebraMap Γ T.B α) -
        algebraMap Γ T.B T.π ^ c * (algebraMap Γ T.B z' * P) =
        algebraMap Γ T.B (α * F.φ z' - T.π ^ c * z') * P := by
      simp only [map_sub, map_mul, map_pow]; ring
    rw [this, hz'eq, T.eq_num_mul b]
    change _ = algebraMap Γ T.B x * _
    simp only [P, hxx', map_mul]; ring
  ·
    have hbx : T.coeffB b = fun k => T.zcoeff x' (k + ((N : ℤ) - m)) := by
      rw [T.coeffB_eq (T.num_spec b)]
      funext k
      change T.zcoeff x (k + N) = _
      rw [hz]
      congr 1; ring
    have hx'c : ConvergesAt (T.zcoeff x') ρ := by
      rw [hbx, convergesAt_shift_iff hρ0] at hb; exact hb
    have hgb : gaussNorm (T.coeffB b) ρ = gaussNorm (T.zcoeff x') ρ * ρ ^ (-((N : ℤ) - m)) := by
      rw [hbx, gaussNorm_shift hρ0]
    set G := gaussNorm (T.zcoeff x') ρ
    have hG : θ ≤ G := by
      have h0 := T.weight_natCast_le hx'c 0
      simp only [Nat.cast_zero, zpow_zero, mul_one, coeff_zero] at h0
      refine le_trans ?_ h0
      have := hbig (((m : ℤ) - N))
      rw [hbx] at this
      simp only [show (m : ℤ) - N + (N - m) = 0 by ring] at this
      rcases this with h | h
      · exfalso; apply hx'0
        have e : T.zcoeff x' 0 = T.red x' := by simpa using T.zcoeff_natCast x' 0
        rw [← e]; exact h
      · have e : T.zcoeff x' 0 = T.red x' := by simpa using T.zcoeff_natCast x' 0
        rwa [e] at h
    set Y := max 1 G
    have hY1 : 1 ≤ Y := le_max_left _ _
    have hYq : 2 ≤ p ^ F.a := F.two_le_q ha
    have hγ : ConvergesAt (T.zcoeff (T.π ^ c)) ρ := by
      rw [zcoeff_π_pow]; exact convergesAt_pi_single _ _ _
    have hγY : gaussNorm (T.zcoeff (T.π ^ c)) ρ ≤ Y ^ (p ^ F.a - 1) := by
      rw [zcoeff_π_pow, gaussNorm_pi_single _ _ hρ0, norm_one, one_mul, zpow_natCast]
      exact (pow_le_one₀ hρ0.le hρ1.le).trans (one_le_pow₀ hY1)
    have hyY : G ≤ Y ^ p ^ F.a := (le_max_right _ _).trans (le_self_pow₀ hY1 (by omega))
    have hw := hz'b ρ Y hρ0 hρ1 hγ hx'c (zero_le_one.trans hY1) hγY hyY
    have hYG : Y ≤ θ⁻¹ * G := by
      refine max_le ?_ ?_
      · rw [le_inv_mul_iff₀ hθ]; simpa using hG
      · exact le_mul_of_one_le_left (hθ.le.trans hG) (one_le_inv₀ hθ |>.2 hθ1)
    have hzc : T.coeffB (algebraMap Γ T.B z' * P) = fun k => T.zcoeff z' (k + ((N : ℤ) - m)) := by
      have : (algebraMap Γ T.B z' * P) * algebraMap Γ T.B T.π ^ N =
          algebraMap Γ T.B (T.π ^ m * z') := by
        simp only [P, map_mul, map_pow]
        rw [show ∀ a b c d : T.B, a * (b * c) * d = a * b * (c * d) by intros; ring,
          T.invSelf_pow_mul_pow, mul_one, mul_comm]
      rw [T.coeffB_eq this]
      funext k
      rw [show k + ((N : ℤ) - m) = k + N - m by ring]
      have := T.zcoeff_π_pow_mul m z' (k + N - m)
      rw [sub_add_cancel] at this
      exact this
    rw [hzc]
    simp only
    have hwz := T.zcoeff_weight_le (zero_le_one.trans hY1) hw (n + ((N : ℤ) - m))
    calc ‖T.zcoeff z' (n + ((N : ℤ) - m))‖ * ρ ^ n
        = (‖T.zcoeff z' (n + ((N : ℤ) - m))‖ * ρ ^ (n + ((N : ℤ) - m))) * ρ ^ (-((N : ℤ) - m)) := by
          rw [mul_assoc, ← zpow_add₀ hρ0.ne', add_neg_cancel_right]
      _ ≤ Y * ρ ^ (-((N : ℤ) - m)) := mul_le_mul_of_nonneg_right hwz (zpow_pos hρ0 _).le
      _ ≤ θ⁻¹ * G * ρ ^ (-((N : ℤ) - m)) := mul_le_mul_of_nonneg_right hYG (zpow_pos hρ0 _).le
      _ = θ⁻¹ * gaussNorm (T.coeffB b) ρ := by rw [hgb]; ring

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
