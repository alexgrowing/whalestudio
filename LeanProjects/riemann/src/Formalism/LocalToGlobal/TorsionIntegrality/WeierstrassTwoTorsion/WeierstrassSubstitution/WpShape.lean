import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementI
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementT
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.Laurent
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.CurveSer

open PowerSeries

universe u

noncomputable section

namespace Formalism.L2.Th1.A

namespace WpSh

theorem alg_first {S : Type*} [CommRing S] (z zi A B c2 c3 : S) (hz : z * zi = 1)
    (h : (zi ^ 2 * B + (-2) * zi ^ 3 * A) ^ 2 = 4 * (zi ^ 2 * A) ^ 3 - c2 * (zi ^ 2 * A) - c3) :
    (z * B - 2 * A) ^ 2 = 4 * A ^ 3 - c2 * z ^ 4 * A - c3 * z ^ 6 := by
  have e1 : z ^ 6 * (zi ^ 2 * B + (-2) * zi ^ 3 * A) ^ 2 = (z * B * (z * zi) ^ 2 - 2 * A * (z * zi) ^ 3) ^ 2 := by ring
  have e2 : z ^ 6 * (4 * (zi ^ 2 * A) ^ 3 - c2 * (zi ^ 2 * A) - c3)
      = 4 * A ^ 3 * (z * zi) ^ 6 - c2 * z ^ 4 * A * (z * zi) ^ 2 - c3 * z ^ 6 := by ring
  rw [hz] at e1 e2
  simp only [one_pow, mul_one] at e1 e2
  rw [← e1, h, e2]

theorem alg_second {S : Type*} [CommRing S] (z zi A B c : S) (hz : z * zi = 1)
    (h : (-2) * ((-3) * zi ^ 4) + B = 6 * (zi ^ 2 + A) ^ 2 - c) :
    z ^ 2 * B = 12 * A + z ^ 2 * (6 * (A * A)) - z ^ 2 * c := by
  have e : z ^ 2 * ((-2) * ((-3) * zi ^ 4) + B) = z ^ 2 * (6 * (zi ^ 2 + A) ^ 2 - c) := by rw [h]
  have e' : z ^ 2 * B = 12 * A * (z * zi) ^ 2 + z ^ 2 * (6 * (A * A)) - z ^ 2 * c := by
    linear_combination e
  rw [hz, one_pow, mul_one] at e'
  exact e'

variable {K : Type u} [Field K]

theorem z_mul_zi : (toL X : LaurentSeries K) * uPow (-1) = 1 := by
  simp only [uPow, HahnSeries.ofPowerSeries_X, HahnSeries.single_mul_single, mul_one]
  rw [show (1 : ℤ) + -1 = 0 by norm_num, ← HahnSeries.C_apply, map_one]

theorem uPow_neg_two : (uPow (-2) : LaurentSeries K) = uPow (-1) ^ 2 := by
  rw [sq, ← uPow_add]
  norm_num

theorem uPow_neg_three : (uPow (-2 - 1) : LaurentSeries K) = uPow (-1) ^ 3 := by
  rw [pow_succ, sq, ← uPow_add, ← uPow_add]
  norm_num

theorem uPow_neg_four : (uPow (-2 - 1 - 1) : LaurentSeries K) = uPow (-1) ^ 4 := by
  rw [pow_succ, pow_succ, sq, ← uPow_add, ← uPow_add, ← uPow_add]
  norm_num

theorem C_neg_two : (HahnSeries.C (((-2 : ℤ)) : K) : LaurentSeries K) = -2 := by
  rw [Int.cast_neg, Int.cast_ofNat, map_neg, map_ofNat]

theorem C_neg_three : (HahnSeries.C (((-2 - 1 : ℤ)) : K) : LaurentSeries K) = -3 := by
  rw [Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_one, map_sub, map_neg, map_ofNat,
    map_one]
  norm_num

theorem add_eq_mul (r : K⟦X⟧) :
    (uPow (-2) : LaurentSeries K) + toL r = uPow (-2) * toL (1 + X ^ 2 * r) := by
  rw [map_add, map_one, map_mul, map_pow, mul_add, mul_one, uPow_neg_two]
  congr 1
  have h := z_mul_zi (K := K)
  linear_combination (-(toL X * uPow (-1) + 1) * toL r) * h

theorem coeff_ofNat_mul (a : ℕ) [a.AtLeastTwo] (f : K⟦X⟧) (n : ℕ) :
    coeff n ((OfNat.ofNat a : K⟦X⟧) * f) = (OfNat.ofNat a : K) * coeff n f := by
  have e : (OfNat.ofNat a : K⟦X⟧) = C (OfNat.ofNat a : K) := (map_ofNat C a).symm
  rw [e, coeff_C_mul]

theorem coeff_X_mul_derivative (f : K⟦X⟧) (n : ℕ) :
    coeff n (X * derivative K f) = (n : K) * coeff n f := by
  rcases n with _ | m
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

theorem coeff_shift_zero {f : K⟦X⟧} (A : K⟦X⟧) {n m : ℕ} (hf : ∀ k < n, coeff k f = 0)
    (hm : 0 < m) : coeff n (X ^ m * (f * A)) = 0 := by
  rw [coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [hf p.1 (by omega), zero_mul]
  · rfl

theorem derivative_X_sq_mul (t : K⟦X⟧) :
    derivative K (X ^ 2 * t) = 2 * X * t + X ^ 2 * derivative K t := by
  rw [pow_two, mul_assoc, Derivation.leibniz, Derivation.leibniz, derivative_X]
  simp only [smul_eq_mul]
  ring

theorem derivative_X_mul (t : K⟦X⟧) :
    derivative K (X * t) = t + X * derivative K t := by
  rw [Derivation.leibniz, derivative_X]
  simp only [smul_eq_mul]
  ring

theorem rescale_C' (a c : K) : rescale a (C c) = C c := by
  ext n
  rw [coeff_rescale, coeff_C]
  split_ifs with h <;> simp [h]

theorem derivative_rescale_neg_one (r : K⟦X⟧) :
    derivative K (rescale (-1 : K) r) = -rescale (-1 : K) (derivative K r) := by
  ext n
  simp only [coeff_derivative, coeff_rescale, map_neg]
  ring

def ClearedM (g2 g3 : K) (M : K⟦X⟧) : Prop :=
  (X * derivative K M - 2 * M) ^ 2 = 4 * M ^ 3 - C g2 * X ^ 4 * M - C g3 * X ^ 6

def Cleared (g2 g3 : K) (r : K⟦X⟧) : Prop :=
  (-2 + X ^ 3 * derivative K r) ^ 2 =
    4 * (1 + X ^ 2 * r) ^ 3 - C g2 * X ^ 4 * (1 + X ^ 2 * r) - C g3 * X ^ 6

theorem clearedM_of_ode {g2 g3 : K} {M : K⟦X⟧}
    (h : dL (uPow (-2) * toL M) ^ 2 = 4 * (uPow (-2) * toL M) ^ 3
      - HahnSeries.C g2 * (uPow (-2) * toL M) - HahnSeries.C g3) : ClearedM g2 g3 M := by
  have hd : dL (uPow (-2) * toL M : LaurentSeries K)
      = uPow (-1) ^ 2 * toL (derivative K M) + (-2) * uPow (-1) ^ 3 * toL M := by
    rw [dL_mul, dL_toL, dL_uPow, C_neg_two, uPow_neg_two, uPow_neg_three]
    ring
  rw [hd, uPow_neg_two] at h
  have e := alg_first (toL X) (uPow (-1)) (toL M) (toL (derivative K M)) (HahnSeries.C g2)
    (HahnSeries.C g3) z_mul_zi h
  unfold ClearedM
  apply toL_injective
  simp only [map_sub, map_mul, map_pow, map_ofNat, HahnSeries.ofPowerSeries_C]
  linear_combination e

theorem cleared_of_clearedM {g2 g3 : K} {r : K⟦X⟧} (h : ClearedM g2 g3 (1 + X ^ 2 * r)) :
    Cleared g2 g3 r := by
  unfold ClearedM at h
  unfold Cleared
  rw [map_add, Derivation.map_one_eq_zero, derivative_X_sq_mul] at h
  have e : X * (0 + (2 * X * r + X ^ 2 * derivative K r)) - 2 * (1 + X ^ 2 * r)
      = -2 + X ^ 3 * derivative K r := by ring
  rw [e] at h
  exact h

theorem cleared_of_ode {g2 g3 : K} {r : K⟦X⟧}
    (h : dL (uPow (-2) + toL r) ^ 2 = 4 * (uPow (-2) + toL r) ^ 3
      - HahnSeries.C g2 * (uPow (-2) + toL r) - HahnSeries.C g3) : Cleared g2 g3 r := by
  rw [add_eq_mul] at h
  exact cleared_of_clearedM (clearedM_of_ode h)

theorem cleared_main {g2 g3 : K} {r : K⟦X⟧} (h : Cleared g2 g3 r) :
    4 * (X * derivative K r) + 12 * r =
      X ^ 2 * (C g2 + C g3 * X ^ 2 + C g2 * X ^ 2 * r - 12 * r ^ 2 - 4 * X ^ 2 * r ^ 3
        + X ^ 2 * derivative K r ^ 2) := by
  unfold Cleared at h
  have hX : (X : K⟦X⟧) ^ 2 ≠ 0 := pow_ne_zero _ X_ne_zero
  apply mul_left_cancel₀ hX
  linear_combination (-1 : K⟦X⟧) * h

theorem cleared_unique [CharZero K] {g2 g3 : K} {r s : K⟦X⟧} (hr : Cleared g2 g3 r)
    (hs : Cleared g2 g3 s) : r = s := by
  have hr' := cleared_main hr
  have hs' := cleared_main hs
  have key : ∀ n, coeff n (4 * (X * derivative K (r - s)) + 12 * (r - s)) =
      coeff n (X ^ 4 * ((r - s) * C g2) + X ^ 2 * ((r - s) * (-12 * (r + s)))
        + X ^ 4 * ((r - s) * (-4 * (r ^ 2 + r * s + s ^ 2)))
        + X ^ 3 * ((X * derivative K (r - s)) * (derivative K r + derivative K s))) := by
    intro n
    congr 1
    rw [map_sub]
    linear_combination hr' - hs'
  have main : ∀ n, (∀ k < n, coeff k (r - s) = 0) → coeff n (r - s) = 0 := by
    intro n hn
    have hn' : ∀ k < n, coeff k (X * derivative K (r - s)) = 0 := by
      intro k hk
      rw [coeff_X_mul_derivative, hn k hk, mul_zero]
    have t1 := coeff_shift_zero (m := 4) (C g2) hn (by norm_num)
    have t2 := coeff_shift_zero (m := 2) (-12 * (r + s)) hn (by norm_num)
    have t3 := coeff_shift_zero (m := 4) (-4 * (r ^ 2 + r * s + s ^ 2)) hn (by norm_num)
    have t4 := coeff_shift_zero (m := 3) (derivative K r + derivative K s) hn' (by norm_num)
    have e := key n
    simp only [map_add] at e
    rw [t1, t2, t3, t4, coeff_ofNat_mul, coeff_ofNat_mul, coeff_X_mul_derivative] at e
    have e2 : ((4 : K) * n + 12) * coeff n (r - s) = 0 := by linear_combination e
    have h4 : ((4 : K) * n + 12) ≠ 0 := by
      exact_mod_cast (show (4 * n + 12 : ℕ) ≠ 0 by omega)
    exact (mul_eq_zero.mp e2).resolve_left h4
  have all : ∀ n, coeff n (r - s) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih => exact main n ih
  rw [← sub_eq_zero]
  ext n
  rw [all n, map_zero]

theorem cleared_low [CharZero K] {g2 g3 : K} {r : K⟦X⟧} (h : Cleared g2 g3 r) :
    coeff 0 r = 0 ∧ coeff 1 r = 0 ∧ coeff 2 r = g2 / 20 ∧ coeff 4 r = g3 / 28 := by
  have E := cleared_main h
  have lhs : ∀ n : ℕ, coeff n (4 * (X * derivative K r) + 12 * r) = (4 * (n : K) + 12) * coeff n r := by
    intro n
    rw [map_add, coeff_ofNat_mul, coeff_ofNat_mul, coeff_X_mul_derivative]
    ring
  have r0 : coeff 0 r = 0 := by
    have e := congrArg (coeff 0) E
    rw [lhs, coeff_X_pow_mul', if_neg (by norm_num : ¬ (2 ≤ 0))] at e
    have h12 : (4 * ((0 : ℕ) : K) + 12) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp e).resolve_left h12
  have r1 : coeff 1 r = 0 := by
    have e := congrArg (coeff 1) E
    rw [lhs, coeff_X_pow_mul', if_neg (by norm_num : ¬ (2 ≤ 1))] at e
    have h16 : (4 * ((1 : ℕ) : K) + 12) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp e).resolve_left h16
  obtain ⟨t, rfl⟩ : X ^ 2 ∣ r := by
    rw [X_pow_dvd_iff]
    intro m hm
    interval_cases m <;> assumption
  have E2 : 4 * (X * derivative K t) + 20 * t = C g2 + X ^ 2 * (C g3 + X ^ 2 * (C g2 * t - 12 * t ^ 2
      - 4 * X ^ 4 * t ^ 3 + (2 * t + X * derivative K t) ^ 2)) := by
    have hX : (X : K⟦X⟧) ^ 2 ≠ 0 := pow_ne_zero _ X_ne_zero
    apply mul_left_cancel₀ hX
    rw [derivative_X_sq_mul] at E
    linear_combination E
  have lt : ∀ n : ℕ, coeff n (4 * (X * derivative K t) + 20 * t) = (4 * (n : K) + 20) * coeff n t := by
    intro n
    rw [map_add, coeff_ofNat_mul, coeff_ofNat_mul, coeff_X_mul_derivative]
    ring
  have f0 := congrArg (coeff 0) E2
  rw [lt, map_add, coeff_C, if_pos rfl, coeff_X_pow_mul', if_neg (by norm_num : ¬ (2 ≤ 0))] at f0
  have f2 := congrArg (coeff 2) E2
  rw [lt, map_add, coeff_C, if_neg (by norm_num : (2 : ℕ) ≠ 0), coeff_X_pow_mul', if_pos (le_refl 2),
    Nat.sub_self, map_add, coeff_C, if_pos rfl, coeff_X_pow_mul', if_neg (by norm_num : ¬ (2 ≤ 0))] at f2
  push_cast at f0 f2
  refine ⟨r0, r1, ?_, ?_⟩
  · rw [coeff_X_pow_mul', if_pos (le_refl 2), Nat.sub_self, eq_div_iff (by norm_num)]
    linear_combination f0
  · rw [coeff_X_pow_mul', if_pos (by norm_num : 2 ≤ 4), show 4 - 2 = 2 from rfl, eq_div_iff (by norm_num)]
    linear_combination f2

theorem cleared_neg {g2 g3 : K} {r : K⟦X⟧} (h : Cleared g2 g3 r) :
    Cleared g2 g3 (rescale (-1 : K) r) := by
  unfold Cleared at h ⊢
  have e := congrArg (rescale (-1 : K)) h
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, rescale_X,
    rescale_C'] at e
  rw [derivative_rescale_neg_one]
  linear_combination e

theorem cleared_odd [CharZero K] {g2 g3 : K} {r : K⟦X⟧} (h : Cleared g2 g3 r) (n : ℕ)
    (hn : Odd n) : coeff n r = 0 := by
  have e := cleared_unique (cleared_neg h) h
  have e1 := congrArg (coeff n) e
  rw [coeff_rescale, hn.neg_one_pow] at e1
  have e2 : (2 : K) * coeff n r = 0 := by linear_combination (-1 : K) * e1
  exact (mul_eq_zero.mp e2).resolve_left two_ne_zero

theorem second_cleared {c : K} {r : K⟦X⟧}
    (h : dL (dL (uPow (-2) + toL r)) = 6 * (uPow (-2) + toL r) ^ 2 - HahnSeries.C c) :
    X ^ 2 * derivative K (derivative K r) = 12 * r + X ^ 2 * (6 * (r * r)) - X ^ 2 * C c := by
  rw [map_add, dL_uPow, dL_toL] at h
  rw [map_add, dL_mul, dL_C, dL_uPow, dL_toL] at h
  rw [C_neg_two, C_neg_three, uPow_neg_four, mul_zero, add_zero, uPow_neg_two] at h
  have e := alg_second (toL X) (uPow (-1)) (toL r) (toL (derivative K (derivative K r)))
    (HahnSeries.C c) z_mul_zi h
  apply toL_injective
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, HahnSeries.ofPowerSeries_C]
  linear_combination e

theorem sum_even (a : ℕ → K) (h0 : a 0 = 0) (hodd : ∀ n, Odd n → a n = 0) (q : ℕ) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (2 * q), a p.1 * a p.2 =
      ∑ i ∈ Finset.Icc 1 (q - 1), a (2 * i) * a (2 * (q - i)) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  dsimp only
  have himg : ∑ i ∈ Finset.Icc 1 (q - 1), a (2 * i) * a (2 * (q - i))
      = ∑ k ∈ (Finset.Icc 1 (q - 1)).image (fun i => 2 * i), a k * a (2 * q - k) := by
    rw [Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) h)]
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    omega
  rw [himg]
  symm
  apply Finset.sum_subset
  · intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    rw [Finset.mem_Icc] at hi
    rw [Finset.mem_range]
    omega
  · intro k hk hk'
    rw [Finset.mem_range] at hk
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | hko
    · by_cases hj0 : j = 0
      · rw [show k = 0 by omega, h0, zero_mul]
      · by_cases hjq : j = q
        · rw [show 2 * q - k = 0 by omega, h0, mul_zero]
        · exfalso
          apply hk'
          exact Finset.mem_image.mpr ⟨j, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · rw [hodd k hko, zero_mul]

theorem recursion_of [CharZero K] {c : K} {r : K⟦X⟧}
    (h : X ^ 2 * derivative K (derivative K r) = 12 * r + X ^ 2 * (6 * (r * r)) - X ^ 2 * C c)
    (h0 : coeff 0 r = 0) (hodd : ∀ n, Odd n → coeff n r = 0) (q : ℕ) (hq : 1 ≤ q) :
    ((q : K) - 1) * (2 * (q : K) + 5) * coeff (2 * q + 2) r =
      3 * ∑ i ∈ Finset.Icc 1 (q - 1), coeff (2 * i) r * coeff (2 * (q - i)) r := by
  have h2 : 2 ≤ 2 * q + 2 := by omega
  have h3 : 2 * q + 2 - 2 = 2 * q := by omega
  have h4 : 2 * q ≠ 0 := by omega
  have e := congrArg (coeff (2 * q + 2)) h
  simp only [map_sub, map_add, coeff_X_pow_mul', if_pos h2, h3, coeff_ofNat_mul, coeff_derivative,
    coeff_C, if_neg h4, sub_zero] at e
  rw [show 2 * q + 1 + 1 = 2 * q + 2 by omega] at e
  have hs := sum_even (fun n => coeff n r) h0 hodd q
  rw [coeff_ofNat_mul, coeff_ofNat_mul, coeff_mul, hs] at e
  push_cast at e
  linear_combination (1 / 2 : K) * e

theorem wpL_eq (hE : ExpSpec.{u}) [CharZero K] (W : WeierstrassCurve K) :
    ∃ M : K⟦X⟧, constantCoeff M = 1 ∧ wpL W = uPow (-2) * toL M := by
  obtain ⟨e0, e1, -⟩ := hE K W
  have hs : HasSubst (expSer W) := HasSubst.of_constantCoeff_zero' e0
  obtain ⟨E, hE'⟩ := X_dvd_iff.mpr e0
  have hE0 : constantCoeff E = 1 := by
    rw [hE'] at e1
    have := coeff_succ_X_mul 0 E
    rw [zero_add, e1] at this
    rw [← coeff_zero_eq_constantCoeff_apply, ← this]
  have hEi : E * E⁻¹ = 1 := PowerSeries.mul_inv_cancel E (by rw [hE0]; exact one_ne_zero)
  have hEi0 : constantCoeff E⁻¹ = 1 := by
    have := congrArg constantCoeff hEi
    rwa [map_mul, hE0, one_mul, map_one] at this
  have hinv : (toL (expSer W))⁻¹ = uPow (-1) * toL E⁻¹ := by
    apply inv_eq_of_mul_eq_one_right
    rw [hE', map_mul]
    have := congrArg toL hEi
    rw [map_mul, map_one] at this
    linear_combination toL E * toL E⁻¹ * z_mul_zi (K := K) + this
  obtain ⟨T, hT⟩ : X ∣ xS W - 1 :=
    X_dvd_iff.mpr (by rw [map_sub, CurveSer.xS_cc, map_one, sub_self])
  have hT' : xS W = 1 + X * T := by linear_combination hT
  have hx0 : constantCoeff ((xS W).subst (expSer W)) = 1 := by
    rw [hT', ← coe_substAlgHom hs, map_add, map_one, map_mul, coe_substAlgHom, subst_X hs,
      map_add, map_one, map_mul, e0, zero_mul, add_zero]
  refine ⟨E⁻¹ ^ 2 * (xS W).subst (expSer W) + C (W.b₂ / 12) * X ^ 2, ?_, ?_⟩
  · rw [map_add, map_mul, map_pow, hEi0, hx0, map_mul, map_pow, constantCoeff_X]
    simp
  · rw [wpL, xZ, hinv, map_add, map_mul, map_mul, map_pow, map_pow, toL_C, uPow_neg_two]
    linear_combination
      (-HahnSeries.C (W.b₂ / 12) * (toL X * uPow (-1) + 1)) * z_mul_zi (K := K)

theorem wpL_shape (hE : ExpSpec.{u}) (hO : WpODE.{u}) [CharZero K] (W : WeierstrassCurve K) :
    wpL W = uPow (-2) + toL (wpReg W) ∧ Cleared (g₂ W) (g₃ W) (wpReg W) := by
  obtain ⟨M, hM1, hM⟩ := wpL_eq hE W
  have hode := (hO K W).2.1
  rw [hM] at hode
  have hC := clearedM_of_ode hode
  obtain ⟨M1, hM1'⟩ : X ∣ M - 1 := by
    rw [X_dvd_iff, map_sub, hM1, map_one, sub_self]
  have hMe : M = 1 + X * M1 := by
    rw [← hM1']
    ring
  rw [hMe] at hC
  unfold ClearedM at hC
  rw [map_add, Derivation.map_one_eq_zero, derivative_X_mul] at hC
  have key : X * (8 * M1 - X * (-4 * derivative K M1 - 11 * M1 ^ 2 - 2 * X * M1 * derivative K M1
      + X ^ 2 * derivative K M1 ^ 2 - 4 * X * M1 ^ 3 + C (g₂ W) * X ^ 2 * (1 + X * M1)
      + C (g₃ W) * X ^ 4)) = 0 := by
    linear_combination (-1 : K⟦X⟧) * hC
  have h8 := (mul_eq_zero.mp key).resolve_left X_ne_zero
  have hc : constantCoeff M1 = 0 := by
    have e := congrArg constantCoeff h8
    rw [map_sub, map_mul, map_mul, constantCoeff_X, zero_mul, sub_zero, map_ofNat, map_zero] at e
    exact (mul_eq_zero.mp e).resolve_left (by norm_num)
  obtain ⟨M2, hM2⟩ : X ∣ M1 := X_dvd_iff.mpr hc
  have hL : wpL W = uPow (-2) + toL M2 := by
    rw [hM, hMe, hM2, show (1 : K⟦X⟧) + X * (X * M2) = 1 + X ^ 2 * M2 by ring, add_eq_mul]
  have hR : wpReg W = M2 := by
    ext n
    rw [wpReg, coeff_mk, hL]
    first
    | simp [uPow, HahnSeries.coeff_single, show (n : ℤ) ≠ -2 by omega]
    | simp [uPow, HahnSeries.single_coeff_of_ne, show (n : ℤ) ≠ -2 by omega]
    | simp [uPow, show (n : ℤ) ≠ -2 by omega]
  refine ⟨?_, ?_⟩
  · rw [hR]
    exact hL
  · rw [hR]
    apply cleared_of_ode
    rw [← hL]
    exact (hO K W).2.1

end WpSh

open WpSh

theorem weierstrass_p_unique : WpUnique.{u} := by
  intro K _ _ g2 g3 r r' h h'
  exact cleared_unique (cleared_of_ode h) (cleared_of_ode h')

theorem wpShape_of (hE : ExpSpec.{u}) (hO : WpODE.{u}) : WpShape.{u} := by
  intro K _ _ W
  obtain ⟨h1, h2⟩ := wpL_shape hE hO W
  obtain ⟨a, _, c, d⟩ := cleared_low h2
  exact ⟨h1, a, fun n hn => cleared_odd h2 n hn, c, d⟩

theorem wpCleared_of (hE : ExpSpec.{u}) (hO : WpODE.{u}) : WpCleared.{u} := by
  intro K _ _ W
  obtain ⟨_, h2⟩ := wpL_shape hE hO W
  refine ⟨?_, fun n hn => cleared_odd h2 n hn, h2⟩
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact (cleared_low h2).1

theorem wpRecursion_of (hE : ExpSpec.{u}) (hO : WpODE.{u}) : WpRecursion.{u} := by
  intro K _ _ W k hk
  obtain ⟨h1, h2⟩ := wpL_shape hE hO W
  have hs := (hO K W).2.2
  rw [h1] at hs
  have e := recursion_of (second_cleared hs) (cleared_low h2).1 (cleared_odd h2) (k - 1)
    (by omega)
  have k1 : k - 1 - 1 = k - 2 := by omega
  have k2 : 2 * (k - 1) + 2 = 2 * k := by omega
  have k3 : ((k - 1 : ℕ) : K) = (k : K) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [k1, k2, k3] at e
  linear_combination e

end Formalism.L2.Th1.A
