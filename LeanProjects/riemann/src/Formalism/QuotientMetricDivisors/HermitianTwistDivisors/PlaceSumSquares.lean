import Mathlib
import Formalism.QuotientMetricDivisors.UntwistedChoice
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ConjugateWeightLatticeOfGeneral

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

namespace W5

lemma log_le_near (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    Real.log p ≤ Real.log q + (p - q) / q := by
  have h := Real.log_le_sub_one_of_pos (div_pos hp hq)
  rw [Real.log_div hp.ne' hq.ne'] at h
  have : (p - q) / q = p / q - 1 := by field_simp
  linarith

lemma log_smooth (a b c d : ℕ) :
    Real.log ((2 : ℝ) ^ a * 3 ^ b * 5 ^ c * 7 ^ d) =
      a * Real.log 2 + b * Real.log 3 + c * Real.log 5 + d * Real.log 7 := by
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_pow]

lemma logp (p : ℝ) (a b c d : ℕ) (e : ℝ) (hp : 0 < p)
    (he : (p - (2 : ℝ) ^ a * 3 ^ b * 5 ^ c * 7 ^ d) / ((2 : ℝ) ^ a * 3 ^ b * 5 ^ c * 7 ^ d) ≤ e) :
    Real.log p ≤ a * Real.log 2 + b * Real.log 3 + c * Real.log 5 + d * Real.log 7 + e := by
  have h := log_le_near p ((2 : ℝ) ^ a * 3 ^ b * 5 ^ c * 7 ^ d) hp (by positivity)
  rw [log_smooth] at h
  linarith

lemma log_three_le : Real.log 3 ≤ (19 * Real.log 2 + 7153 / 524288) / 12 := by
  have h := logp ((3 : ℝ) ^ 12) 19 0 0 0 (7153 / 524288) (by positivity) (by norm_num)
  rw [Real.log_pow] at h
  push_cast at h
  linarith

lemma log_five_le : Real.log 5 ≤ (7 * Real.log 2 - 3 / 128) / 3 := by
  have h := logp ((5 : ℝ) ^ 3) 7 0 0 0 (-3 / 128) (by positivity) (by norm_num)
  rw [Real.log_pow] at h
  push_cast at h
  linarith

lemma place_sum_over_primes : Real.log 7 ≤ (4 * Real.log 2 + Real.log 3 + 1 / 48) / 2 := by
  have h := logp ((7 : ℝ) ^ 2) 4 1 0 0 (1 / 48) (by positivity) (by norm_num)
  rw [Real.log_pow] at h
  push_cast at h
  linarith

lemma head_num :
    Real.log 2 / 2 ^ 2 + Real.log 3 / 3 ^ 2 + Real.log 5 / 5 ^ 2 + Real.log 7 / 7 ^ 2 + Real.log 11 / 11 ^ 2 + Real.log 13 / 13 ^ 2 + Real.log 17 / 17 ^ 2 + Real.log 19 / 19 ^ 2 + Real.log 23 / 23 ^ 2 + Real.log 29 / 29 ^ 2 + Real.log 31 / 31 ^ 2 + Real.log 37 / 37 ^ 2 + Real.log 41 / 41 ^ 2 + Real.log 43 / 43 ^ 2 + Real.log 47 / 47 ^ 2 + Real.log 53 / 53 ^ 2 + Real.log 59 / 59 ^ 2 + Real.log 61 / 61 ^ 2 + Real.log 67 / 67 ^ 2 + Real.log 71 / 71 ^ 2 + Real.log 73 / 73 ^ 2 + Real.log 79 / 79 ^ 2 + Real.log 83 / 83 ^ 2 + Real.log 89 / 89 ^ 2 + Real.log 97 / 97 ^ 2 + Real.log 101 / 101 ^ 2 + Real.log 103 / 103 ^ 2 + Real.log 107 / 107 ^ 2 + Real.log 109 / 109 ^ 2 + Real.log 113 / 113 ^ 2 + Real.log 127 / 127 ^ 2 + Real.log 131 / 131 ^ 2 + Real.log 137 / 137 ^ 2 + Real.log 139 / 139 ^ 2 + Real.log 149 / 149 ^ 2 + Real.log 151 / 151 ^ 2 + Real.log 157 / 157 ^ 2 + Real.log 163 / 163 ^ 2 + Real.log 167 / 167 ^ 2 + Real.log 173 / 173 ^ 2 + Real.log 179 / 179 ^ 2 + Real.log 181 / 181 ^ 2 + Real.log 191 / 191 ^ 2 + Real.log 193 / 193 ^ 2 + Real.log 197 / 197 ^ 2 + Real.log 199 / 199 ^ 2 + Real.log 211 / 211 ^ 2 + Real.log 223 / 223 ^ 2 + Real.log 227 / 227 ^ 2 + Real.log 229 / 229 ^ 2 + Real.log 233 / 233 ^ 2 + Real.log 239 / 239 ^ 2 + (Real.log 234 + 1) / 234 / 3 ≤ 4995 / 10000 := by
  have l2 := Real.log_two_lt_d9
  have l3 := log_three_le
  have l5 := log_five_le
  have l7 := place_sum_over_primes
  have h11 : Real.log 11 ≤ 2 * Real.log 2 + 1 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 12 := by
    exact_mod_cast logp 11 2 1 0 0 ((-1 : ℝ) / 12) (by norm_num) (by norm_num)
  have h13 : Real.log 13 ≤ 1 * Real.log 2 + 0 * Real.log 3 + 0 * Real.log 5 + 1 * Real.log 7 + (-1 : ℝ) / 14 := by
    exact_mod_cast logp 13 1 0 0 1 ((-1 : ℝ) / 14) (by norm_num) (by norm_num)
  have h17 : Real.log 17 ≤ 1 * Real.log 2 + 2 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 18 := by
    exact_mod_cast logp 17 1 2 0 0 ((-1 : ℝ) / 18) (by norm_num) (by norm_num)
  have h19 : Real.log 19 ≤ 2 * Real.log 2 + 0 * Real.log 3 + 1 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 20 := by
    exact_mod_cast logp 19 2 0 1 0 ((-1 : ℝ) / 20) (by norm_num) (by norm_num)
  have h23 : Real.log 23 ≤ 3 * Real.log 2 + 1 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 24 := by
    exact_mod_cast logp 23 3 1 0 0 ((-1 : ℝ) / 24) (by norm_num) (by norm_num)
  have h29 : Real.log 29 ≤ 1 * Real.log 2 + 1 * Real.log 3 + 1 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 30 := by
    exact_mod_cast logp 29 1 1 1 0 ((-1 : ℝ) / 30) (by norm_num) (by norm_num)
  have h31 : Real.log 31 ≤ 5 * Real.log 2 + 0 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 32 := by
    exact_mod_cast logp 31 5 0 0 0 ((-1 : ℝ) / 32) (by norm_num) (by norm_num)
  have h37 : Real.log 37 ≤ 2 * Real.log 2 + 2 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (1 : ℝ) / 36 := by
    exact_mod_cast logp 37 2 2 0 0 ((1 : ℝ) / 36) (by norm_num) (by norm_num)
  have h41 : Real.log 41 ≤ 1 * Real.log 2 + 1 * Real.log 3 + 0 * Real.log 5 + 1 * Real.log 7 + (-1 : ℝ) / 42 := by
    exact_mod_cast logp 41 1 1 0 1 ((-1 : ℝ) / 42) (by norm_num) (by norm_num)
  have h43 : Real.log 43 ≤ 1 * Real.log 2 + 1 * Real.log 3 + 0 * Real.log 5 + 1 * Real.log 7 + (1 : ℝ) / 42 := by
    exact_mod_cast logp 43 1 1 0 1 ((1 : ℝ) / 42) (by norm_num) (by norm_num)
  have h47 : Real.log 47 ≤ 4 * Real.log 2 + 1 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 48 := by
    exact_mod_cast logp 47 4 1 0 0 ((-1 : ℝ) / 48) (by norm_num) (by norm_num)
  have h53 : Real.log 53 ≤ 1 * Real.log 2 + 3 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 54 := by
    exact_mod_cast logp 53 1 3 0 0 ((-1 : ℝ) / 54) (by norm_num) (by norm_num)
  have h59 : Real.log 59 ≤ 2 * Real.log 2 + 1 * Real.log 3 + 1 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 60 := by
    exact_mod_cast logp 59 2 1 1 0 ((-1 : ℝ) / 60) (by norm_num) (by norm_num)
  have h61 : Real.log 61 ≤ 2 * Real.log 2 + 1 * Real.log 3 + 1 * Real.log 5 + 0 * Real.log 7 + (1 : ℝ) / 60 := by
    exact_mod_cast logp 61 2 1 1 0 ((1 : ℝ) / 60) (by norm_num) (by norm_num)
  have h67 : Real.log 67 ≤ 1 * Real.log 2 + 0 * Real.log 3 + 1 * Real.log 5 + 1 * Real.log 7 + (-3 : ℝ) / 70 := by
    exact_mod_cast logp 67 1 0 1 1 ((-3 : ℝ) / 70) (by norm_num) (by norm_num)
  have h71 : Real.log 71 ≤ 3 * Real.log 2 + 2 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 72 := by
    exact_mod_cast logp 71 3 2 0 0 ((-1 : ℝ) / 72) (by norm_num) (by norm_num)
  have h73 : Real.log 73 ≤ 3 * Real.log 2 + 2 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (1 : ℝ) / 72 := by
    exact_mod_cast logp 73 3 2 0 0 ((1 : ℝ) / 72) (by norm_num) (by norm_num)
  have h79 : Real.log 79 ≤ 4 * Real.log 2 + 0 * Real.log 3 + 1 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 80 := by
    exact_mod_cast logp 79 4 0 1 0 ((-1 : ℝ) / 80) (by norm_num) (by norm_num)
  have h83 : Real.log 83 ≤ 2 * Real.log 2 + 1 * Real.log 3 + 0 * Real.log 5 + 1 * Real.log 7 + (-1 : ℝ) / 84 := by
    exact_mod_cast logp 83 2 1 0 1 ((-1 : ℝ) / 84) (by norm_num) (by norm_num)
  have h89 : Real.log 89 ≤ 1 * Real.log 2 + 2 * Real.log 3 + 1 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 90 := by
    exact_mod_cast logp 89 1 2 1 0 ((-1 : ℝ) / 90) (by norm_num) (by norm_num)
  have h97 : Real.log 97 ≤ 1 * Real.log 2 + 0 * Real.log 3 + 0 * Real.log 5 + 2 * Real.log 7 + (-1 : ℝ) / 98 := by
    exact_mod_cast logp 97 1 0 0 2 ((-1 : ℝ) / 98) (by norm_num) (by norm_num)
  have h101 : Real.log 101 ≤ 2 * Real.log 2 + 0 * Real.log 3 + 2 * Real.log 5 + 0 * Real.log 7 + (1 : ℝ) / 100 := by
    exact_mod_cast logp 101 2 0 2 0 ((1 : ℝ) / 100) (by norm_num) (by norm_num)
  have h103 : Real.log 103 ≤ 0 * Real.log 2 + 1 * Real.log 3 + 1 * Real.log 5 + 1 * Real.log 7 + (-2 : ℝ) / 105 := by
    exact_mod_cast logp 103 0 1 1 1 ((-2 : ℝ) / 105) (by norm_num) (by norm_num)
  have h107 : Real.log 107 ≤ 2 * Real.log 2 + 3 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 108 := by
    exact_mod_cast logp 107 2 3 0 0 ((-1 : ℝ) / 108) (by norm_num) (by norm_num)
  have h109 : Real.log 109 ≤ 2 * Real.log 2 + 3 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (1 : ℝ) / 108 := by
    exact_mod_cast logp 109 2 3 0 0 ((1 : ℝ) / 108) (by norm_num) (by norm_num)
  have h113 : Real.log 113 ≤ 4 * Real.log 2 + 0 * Real.log 3 + 0 * Real.log 5 + 1 * Real.log 7 + (1 : ℝ) / 112 := by
    exact_mod_cast logp 113 4 0 0 1 ((1 : ℝ) / 112) (by norm_num) (by norm_num)
  have h127 : Real.log 127 ≤ 7 * Real.log 2 + 0 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 128 := by
    exact_mod_cast logp 127 7 0 0 0 ((-1 : ℝ) / 128) (by norm_num) (by norm_num)
  have h131 : Real.log 131 ≤ 7 * Real.log 2 + 0 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (3 : ℝ) / 128 := by
    exact_mod_cast logp 131 7 0 0 0 ((3 : ℝ) / 128) (by norm_num) (by norm_num)
  have h137 : Real.log 137 ≤ 0 * Real.log 2 + 3 * Real.log 3 + 1 * Real.log 5 + 0 * Real.log 7 + (2 : ℝ) / 135 := by
    exact_mod_cast logp 137 0 3 1 0 ((2 : ℝ) / 135) (by norm_num) (by norm_num)
  have h139 : Real.log 139 ≤ 2 * Real.log 2 + 0 * Real.log 3 + 1 * Real.log 5 + 1 * Real.log 7 + (-1 : ℝ) / 140 := by
    exact_mod_cast logp 139 2 0 1 1 ((-1 : ℝ) / 140) (by norm_num) (by norm_num)
  have h149 : Real.log 149 ≤ 1 * Real.log 2 + 1 * Real.log 3 + 2 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 150 := by
    exact_mod_cast logp 149 1 1 2 0 ((-1 : ℝ) / 150) (by norm_num) (by norm_num)
  have h151 : Real.log 151 ≤ 1 * Real.log 2 + 1 * Real.log 3 + 2 * Real.log 5 + 0 * Real.log 7 + (1 : ℝ) / 150 := by
    exact_mod_cast logp 151 1 1 2 0 ((1 : ℝ) / 150) (by norm_num) (by norm_num)
  have h157 : Real.log 157 ≤ 5 * Real.log 2 + 0 * Real.log 3 + 1 * Real.log 5 + 0 * Real.log 7 + (-3 : ℝ) / 160 := by
    exact_mod_cast logp 157 5 0 1 0 ((-3 : ℝ) / 160) (by norm_num) (by norm_num)
  have h163 : Real.log 163 ≤ 1 * Real.log 2 + 4 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (1 : ℝ) / 162 := by
    exact_mod_cast logp 163 1 4 0 0 ((1 : ℝ) / 162) (by norm_num) (by norm_num)
  have h167 : Real.log 167 ≤ 3 * Real.log 2 + 1 * Real.log 3 + 0 * Real.log 5 + 1 * Real.log 7 + (-1 : ℝ) / 168 := by
    exact_mod_cast logp 167 3 1 0 1 ((-1 : ℝ) / 168) (by norm_num) (by norm_num)
  have h173 : Real.log 173 ≤ 0 * Real.log 2 + 0 * Real.log 3 + 2 * Real.log 5 + 1 * Real.log 7 + (-2 : ℝ) / 175 := by
    exact_mod_cast logp 173 0 0 2 1 ((-2 : ℝ) / 175) (by norm_num) (by norm_num)
  have h179 : Real.log 179 ≤ 2 * Real.log 2 + 2 * Real.log 3 + 1 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 180 := by
    exact_mod_cast logp 179 2 2 1 0 ((-1 : ℝ) / 180) (by norm_num) (by norm_num)
  have h181 : Real.log 181 ≤ 2 * Real.log 2 + 2 * Real.log 3 + 1 * Real.log 5 + 0 * Real.log 7 + (1 : ℝ) / 180 := by
    exact_mod_cast logp 181 2 2 1 0 ((1 : ℝ) / 180) (by norm_num) (by norm_num)
  have h191 : Real.log 191 ≤ 6 * Real.log 2 + 1 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 192 := by
    exact_mod_cast logp 191 6 1 0 0 ((-1 : ℝ) / 192) (by norm_num) (by norm_num)
  have h193 : Real.log 193 ≤ 6 * Real.log 2 + 1 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (1 : ℝ) / 192 := by
    exact_mod_cast logp 193 6 1 0 0 ((1 : ℝ) / 192) (by norm_num) (by norm_num)
  have h197 : Real.log 197 ≤ 2 * Real.log 2 + 0 * Real.log 3 + 0 * Real.log 5 + 2 * Real.log 7 + (1 : ℝ) / 196 := by
    exact_mod_cast logp 197 2 0 0 2 ((1 : ℝ) / 196) (by norm_num) (by norm_num)
  have h199 : Real.log 199 ≤ 3 * Real.log 2 + 0 * Real.log 3 + 2 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 200 := by
    exact_mod_cast logp 199 3 0 2 0 ((-1 : ℝ) / 200) (by norm_num) (by norm_num)
  have h211 : Real.log 211 ≤ 1 * Real.log 2 + 1 * Real.log 3 + 1 * Real.log 5 + 1 * Real.log 7 + (1 : ℝ) / 210 := by
    exact_mod_cast logp 211 1 1 1 1 ((1 : ℝ) / 210) (by norm_num) (by norm_num)
  have h223 : Real.log 223 ≤ 5 * Real.log 2 + 0 * Real.log 3 + 0 * Real.log 5 + 1 * Real.log 7 + (-1 : ℝ) / 224 := by
    exact_mod_cast logp 223 5 0 0 1 ((-1 : ℝ) / 224) (by norm_num) (by norm_num)
  have h227 : Real.log 227 ≤ 0 * Real.log 2 + 2 * Real.log 3 + 2 * Real.log 5 + 0 * Real.log 7 + (2 : ℝ) / 225 := by
    exact_mod_cast logp 227 0 2 2 0 ((2 : ℝ) / 225) (by norm_num) (by norm_num)
  have h229 : Real.log 229 ≤ 0 * Real.log 2 + 2 * Real.log 3 + 2 * Real.log 5 + 0 * Real.log 7 + (4 : ℝ) / 225 := by
    exact_mod_cast logp 229 0 2 2 0 ((4 : ℝ) / 225) (by norm_num) (by norm_num)
  have h233 : Real.log 233 ≤ 4 * Real.log 2 + 1 * Real.log 3 + 1 * Real.log 5 + 0 * Real.log 7 + (-7 : ℝ) / 240 := by
    exact_mod_cast logp 233 4 1 1 0 ((-7 : ℝ) / 240) (by norm_num) (by norm_num)
  have h239 : Real.log 239 ≤ 4 * Real.log 2 + 1 * Real.log 3 + 1 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 240 := by
    exact_mod_cast logp 239 4 1 1 0 ((-1 : ℝ) / 240) (by norm_num) (by norm_num)
  have h234 : Real.log 234 ≤ 4 * Real.log 2 + 1 * Real.log 3 + 1 * Real.log 5 + 0 * Real.log 7 + (-6 : ℝ) / 240 := by
    exact_mod_cast logp 234 4 1 1 0 ((-6 : ℝ) / 240) (by norm_num) (by norm_num)
  linarith

set_option maxRecDepth 100000 in
lemma head_sum :
    ∑ n ∈ Finset.range 240, (if n.Prime then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0) =
    Real.log 2 / 2 ^ 2 + Real.log 3 / 3 ^ 2 + Real.log 5 / 5 ^ 2 + Real.log 7 / 7 ^ 2 + Real.log 11 / 11 ^ 2 + Real.log 13 / 13 ^ 2 + Real.log 17 / 17 ^ 2 + Real.log 19 / 19 ^ 2 + Real.log 23 / 23 ^ 2 + Real.log 29 / 29 ^ 2 + Real.log 31 / 31 ^ 2 + Real.log 37 / 37 ^ 2 + Real.log 41 / 41 ^ 2 + Real.log 43 / 43 ^ 2 + Real.log 47 / 47 ^ 2 + Real.log 53 / 53 ^ 2 + Real.log 59 / 59 ^ 2 + Real.log 61 / 61 ^ 2 + Real.log 67 / 67 ^ 2 + Real.log 71 / 71 ^ 2 + Real.log 73 / 73 ^ 2 + Real.log 79 / 79 ^ 2 + Real.log 83 / 83 ^ 2 + Real.log 89 / 89 ^ 2 + Real.log 97 / 97 ^ 2 + Real.log 101 / 101 ^ 2 + Real.log 103 / 103 ^ 2 + Real.log 107 / 107 ^ 2 + Real.log 109 / 109 ^ 2 + Real.log 113 / 113 ^ 2 + Real.log 127 / 127 ^ 2 + Real.log 131 / 131 ^ 2 + Real.log 137 / 137 ^ 2 + Real.log 139 / 139 ^ 2 + Real.log 149 / 149 ^ 2 + Real.log 151 / 151 ^ 2 + Real.log 157 / 157 ^ 2 + Real.log 163 / 163 ^ 2 + Real.log 167 / 167 ^ 2 + Real.log 173 / 173 ^ 2 + Real.log 179 / 179 ^ 2 + Real.log 181 / 181 ^ 2 + Real.log 191 / 191 ^ 2 + Real.log 193 / 193 ^ 2 + Real.log 197 / 197 ^ 2 + Real.log 199 / 199 ^ 2 + Real.log 211 / 211 ^ 2 + Real.log 223 / 223 ^ 2 + Real.log 227 / 227 ^ 2 + Real.log 229 / 229 ^ 2 + Real.log 233 / 233 ^ 2 + Real.log 239 / 239 ^ 2 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

end W5

namespace W5

lemma tele (u h : ℝ) (hh : 0 < h) (hu : 2 * h ≤ u) (hlog : 2 ≤ Real.log u) :
    h * (Real.log u / u ^ 2) ≤ (Real.log (u - h) + 1) / (u - h) - (Real.log u + 1) / u := by
  obtain ⟨v, hv⟩ : ∃ v, v = u - h := ⟨_, rfl⟩
  have hu' : u = v + h := by linarith
  have hv0 : 0 < v := by linarith
  have hu0 : 0 < u := by linarith
  rw [← hv]
  have h1 := log_le_near u v hu0 hv0
  have h2 : Real.log u - h / v ≤ Real.log v := by
    have : (u - v) / v = h / v := by rw [hu']; ring
    linarith
  set ℓ := Real.log u with hℓ
  have h3 : (ℓ - h / v + 1) / v ≤ (Real.log v + 1) / v :=
    div_le_div_of_nonneg_right (by linarith) hv0.le
  have h4 : (ℓ - h / v + 1) / v - (ℓ + 1) / u - h * (ℓ / u ^ 2) =
      h ^ 2 * (ℓ * v - u) / (u ^ 2 * v ^ 2) := by
    rw [hu']
    field_simp
    ring
  have h5 : 0 ≤ h ^ 2 * (ℓ * v - u) / (u ^ 2 * v ^ 2) := by
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (by positivity)
    nlinarith
  linarith

lemma exp_two_le : Real.exp 2 ≤ 8 := by
  have h := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [this]
  nlinarith

lemma anti (u v : ℝ) (hu : 8 ≤ u) (huv : u ≤ v) :
    Real.log v / v ^ 2 ≤ Real.log u / u ^ 2 := by
  have hA := Real.log_div_self_rpow_antitoneOn (a := 2) (by norm_num)
  have he : Real.exp (2 : ℝ)⁻¹ ≤ 8 := by
    refine le_trans (Real.exp_le_exp.2 ?_) exp_two_le
    norm_num
  have := hA (a := u) (b := v) (Set.mem_Ici.2 (by linarith)) (Set.mem_Ici.2 (by linarith)) huv
  simpa [Real.rpow_two] using this

lemma blk (K : ℕ) (hK : 40 ≤ K) :
    ∑ n ∈ Finset.Ico 240 (6 * K),
      (if n % 6 = 1 ∨ n % 6 = 5 then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0) ≤
    ((Real.log 234 + 1) / 234 - (Real.log ((6 * K : ℕ) - 6 : ℝ) + 1) / ((6 * K : ℕ) - 6 : ℝ)) / 3 := by
  induction K, hK using Nat.le_induction with
  | base => norm_num
  | succ K hK ih =>
    have e : 6 * (K + 1) = 6 * K + 1 + 1 + 1 + 1 + 1 + 1 := by ring
    have c0 : ¬ ((6 * K) % 6 = 1 ∨ (6 * K) % 6 = 5) := by omega
    have c1 : ((6 * K + 1) % 6 = 1 ∨ (6 * K + 1) % 6 = 5) := by omega
    have c2 : ¬ ((6 * K + 1 + 1) % 6 = 1 ∨ (6 * K + 1 + 1) % 6 = 5) := by omega
    have c3 : ¬ ((6 * K + 1 + 1 + 1) % 6 = 1 ∨ (6 * K + 1 + 1 + 1) % 6 = 5) := by omega
    have c4 : ¬ ((6 * K + 1 + 1 + 1 + 1) % 6 = 1 ∨ (6 * K + 1 + 1 + 1 + 1) % 6 = 5) := by omega
    have c5 : ((6 * K + 1 + 1 + 1 + 1 + 1) % 6 = 1 ∨ (6 * K + 1 + 1 + 1 + 1 + 1) % 6 = 5) := by omega
    have hsum : ∑ n ∈ Finset.Ico 240 (6 * (K + 1)),
        (if n % 6 = 1 ∨ n % 6 = 5 then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0) =
        ∑ n ∈ Finset.Ico 240 (6 * K),
          (if n % 6 = 1 ∨ n % 6 = 5 then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0) +
        Real.log ((6 * K + 1 : ℕ) : ℝ) / ((6 * K + 1 : ℕ) : ℝ) ^ 2 +
        Real.log ((6 * K + 1 + 1 + 1 + 1 + 1 : ℕ) : ℝ) / ((6 * K + 1 + 1 + 1 + 1 + 1 : ℕ) : ℝ) ^ 2 := by
      rw [e, Finset.sum_Ico_succ_top (by omega), Finset.sum_Ico_succ_top (by omega),
        Finset.sum_Ico_succ_top (by omega), Finset.sum_Ico_succ_top (by omega),
        Finset.sum_Ico_succ_top (by omega), Finset.sum_Ico_succ_top (by omega),
        if_neg c0, if_pos c1, if_neg c2, if_neg c3, if_neg c4, if_pos c5]
      ring
    rw [hsum]
    have hKr : (240 : ℝ) ≤ ((6 * K : ℕ) : ℝ) := by exact_mod_cast (by omega : 240 ≤ 6 * K)
    have a1 := anti ((6 * K : ℕ) : ℝ) ((6 * K + 1 : ℕ) : ℝ) (by linarith) (by push_cast; linarith)
    have a5 := anti ((6 * K : ℕ) : ℝ) ((6 * K + 1 + 1 + 1 + 1 + 1 : ℕ) : ℝ) (by linarith)
      (by push_cast; linarith)
    have hl : 2 ≤ Real.log ((6 * K : ℕ) : ℝ) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      linarith [exp_two_le]
    have t := tele ((6 * K : ℕ) : ℝ) 6 (by norm_num) (by linarith) hl
    have e2 : (((6 * (K + 1) : ℕ) : ℝ) - 6) = ((6 * K : ℕ) : ℝ) := by push_cast; ring
    rw [e2]
    linarith

lemma aux_statement_15 (p : ℕ) (hp : p.Prime) (h : 240 ≤ p) : p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 : ¬ 2 ∣ p := fun hd => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 hd
    omega
  have h3 : ¬ 3 ∣ p := fun hd => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 hd
    omega
  omega

lemma term_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) / (n : ℝ) ^ 2 :=
  div_nonneg (Real.log_natCast_nonneg n) (by positivity)

lemma prime_sum_le (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ∑ p ∈ s, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 4995 / 10000 := by
  classical
  obtain ⟨K, hK40, hK⟩ : ∃ K : ℕ, 40 ≤ K ∧ ∀ p ∈ s, p < 6 * K := by
    refine ⟨s.sup id + 40, by omega, fun p hp => ?_⟩
    have : p ≤ s.sup id := Finset.le_sup (f := id) hp
    omega
  rw [← Finset.sum_filter_add_sum_filter_not s (fun p => p < 240)]
  have hhead : ∑ p ∈ s.filter (fun p => p < 240), Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤
      ∑ n ∈ Finset.range 240, (if n.Prime then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0) := by
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rw [Finset.mem_filter] at hp
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hp.2, hs p hp.1⟩
    · intro n _ _
      exact term_nonneg n
  have htail : ∑ p ∈ s.filter (fun p => ¬ p < 240), Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤
      ∑ n ∈ Finset.Ico 240 (6 * K),
        (if n % 6 = 1 ∨ n % 6 = 5 then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0) := by
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rw [Finset.mem_filter] at hp
      exact Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨by omega, hK p hp.1⟩,
        aux_statement_15 p (hs p hp.1) (by omega)⟩
    · intro n _ _
      exact term_nonneg n
  have hb := blk K hK40
  have hpos : 0 ≤ (Real.log ((6 * K : ℕ) - 6 : ℝ) + 1) / ((6 * K : ℕ) - 6 : ℝ) := by
    have h1 : (234 : ℝ) ≤ ((6 * K : ℕ) : ℝ) - 6 := by
      have : (240 : ℝ) ≤ ((6 * K : ℕ) : ℝ) := by exact_mod_cast (by omega : 240 ≤ 6 * K)
      linarith
    apply div_nonneg _ (by linarith)
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ ((6 * K : ℕ) : ℝ) - 6)
    linarith
  rw [head_sum] at hhead
  have hn := head_num
  linarith

end W5

theorem prime_mod_six_of_large : PrimeSumSq := by
  have h1 : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) →
      ∑ p ∈ s, 2 * Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 999 / 1000 := by
    intro s hs
    have h := W5.prime_sum_le s hs
    have e : ∑ p ∈ s, 2 * Real.log (p : ℝ) / (p : ℝ) ^ 2 =
        2 * ∑ p ∈ s, Real.log (p : ℝ) / (p : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun p _ => by ring)
    rw [e]
    linarith
  have h2 : ∀ u : Finset Nat.Primes,
      ∑ p ∈ u, 2 * Real.log ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2 ≤ 999 / 1000 := by
    intro u
    have h := h1 (u.map ⟨Subtype.val, Subtype.val_injective⟩) (by
      intro p hp
      obtain ⟨q, -, rfl⟩ := Finset.mem_map.1 hp
      exact q.2)
    have e := Finset.sum_map u ⟨Subtype.val, Subtype.val_injective⟩
      (fun p : ℕ => 2 * Real.log (p : ℝ) / (p : ℝ) ^ 2)
    exact le_of_eq_of_le e.symm h
  have h0 : 0 ≤ fun p : Nat.Primes => 2 * Real.log ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2 := fun p =>
    div_nonneg (mul_nonneg (by norm_num) (Real.log_natCast_nonneg _)) (by positivity)
  exact ⟨h1, summable_of_sum_le h0 h2,
    lt_of_le_of_lt (Real.tsum_le_of_sum_le h0 h2) (by norm_num)⟩

namespace W5

variable {K : Type} [Field K] [NumberField K]

lemma lw_nonneg (w : HeightOneSpectrum (𝓞 K)) : 0 ≤ lw w :=
  div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

lemma vw_int (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    vw w (x : K) = FractionalIdeal.count K w
      ((Ideal.span {x} : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
  unfold vw
  rw [FractionalIdeal.coeIdeal_span_singleton]

lemma vw_nat_nonneg (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) : 0 ≤ vw w (n : K) := by
  have h : ((n : 𝓞 K) : K) = (n : K) := map_natCast _ n
  rw [← h, vw_int]
  exact FractionalIdeal.count_coe_nonneg K w _

end W5

theorem place_sum_natural : PlaceSumNat := by
  intro K _ _ n hn
  classical
  have ha : (n : K) ≠ 0 := by exact_mod_cast hn.ne'
  set I := FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (n : K) with hIdef
  have hD := Formalism.LatticeIndexTer.log_product_formula K (n : K) ha
  have hdeg : (finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  set g : HeightOneSpectrum (𝓞 K) → ℝ := fun w =>
    (FractionalIdeal.count K w I : ℝ) * Real.log (Ideal.absNorm w.asIdeal : ℝ) with hg
  have hgfin : (Function.support g).Finite := by
    have hf := FractionalIdeal.finite_factors (K := K) I
    rw [Filter.eventually_cofinite] at hf
    refine hf.subset ?_
    intro w hw
    rw [Function.mem_support] at hw
    intro h0
    apply hw
    simp only [hg, h0, Int.cast_zero, zero_mul]
  have hfun : (fun w : HeightOneSpectrum (𝓞 K) => lw w * (vw w (n : K) : ℝ)) =
      fun w => (finrank ℚ K : ℝ)⁻¹ * g w := by
    funext w
    simp only [lw, vw, hg, hIdef]
    field_simp
  have hfin : (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
      lw w * (vw w (n : K) : ℝ)).Finite := by
    rw [hfun]
    exact hgfin.subset (Function.support_mul_subset_right _ _)
  have hlhs : ∑ σ : K →+* ℂ, Real.log ‖σ (n : K)‖ = (finrank ℚ K : ℝ) * Real.log (n : ℝ) := by
    have : ∀ σ : K →+* ℂ, Real.log ‖σ (n : K)‖ = Real.log (n : ℝ) := by
      intro σ
      rw [map_natCast, Complex.norm_natCast]
    rw [Finset.sum_congr rfl (fun σ _ => this σ), Finset.sum_const, Finset.card_univ,
      NumberField.Embeddings.card, nsmul_eq_mul]
  have hsum : ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (vw w (n : K) : ℝ) = Real.log (n : ℝ) := by
    rw [hfun, ← mul_finsum, hg, ← hD, hlhs]
    field_simp
  refine ⟨hfin, hsum, fun S => ?_⟩
  rw [← hsum, finsum_eq_sum_of_support_subset (s := S ∪ hfin.toFinset) _ (by
    intro w hw
    rw [Finset.coe_union]
    exact Or.inr (by simpa using hw))]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    (fun w _ _ => mul_nonneg (W5.lw_nonneg w) (by exact_mod_cast W5.vw_nat_nonneg w n))

theorem untwisted_choice : UntwistedChoice := by
  intro Pl J _ S Tw D hD hTS l ell I Ic jT F err Jx η hA hF h3 h4
  classical
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  refine ⟨fun w j => if w ∈ Tw then err w j else (I w j + Ic w j) / D,
    fun w j => if w ∈ Tw then Jx w j else jT w j / D,
    fun w j => if w ∈ Tw then η w j else 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw j
    simp only [hw, if_true, and_self]
  · intro w hw
    by_cases hT : w ∈ Tw
    · simpa only [hT, if_true] using h3 w hT
    · simp only [hT, if_false]
      have e : ∑ j, (2 * F w j + (I w j + Ic w j) / D) = (∑ j, (I w j + Ic w j)) / D := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun j _ => by rw [hF w hw hT j]; ring)
      rw [e, add_mul, div_mul_cancel₀ _ hD'.ne']
      have : 0 ≤ 2 / ell w ^ 2 * (D : ℝ) := by positivity
      linarith
  · intro w hw j
    by_cases hT : w ∈ Tw
    · simpa only [hT, if_true] using h4 w hT j
    · simp only [hT, if_false]
      rw [div_mul_cancel₀ _ hD'.ne', add_zero]
  · intro j
    rw [← Finset.sum_subset hTS (fun w hw hT => by
      simp only [hT, if_false]
      rw [← add_div, hA w hw hT j, zero_div, mul_zero])]
    exact Finset.sum_congr rfl (fun w hw => by simp only [hw, if_true])
  · intro j
    rw [← Finset.sum_subset hTS (fun w hw hT => by
      simp only [hT, if_false, mul_zero, zero_div])]
    exact Finset.sum_congr rfl (fun w hw => by simp only [hw, if_true])
  · intro j
    exact (Finset.sum_subset hTS (fun w hw hT => by rw [hF w hw hT j, mul_zero])).symm

namespace W5

end W5

end Formalism.DivisionValues
