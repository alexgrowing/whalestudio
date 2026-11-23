import Mathlib
import Formalism.LocalRingCardinality.DataDIV
import Formalism.SharpRestriction.Divisibility.LatticeTransfer

open Formalism.BasicNotions Formalism.BasicNotions.DV

namespace GlobalTheory.RootChernRules

section Ring
variable {R : Type*} [CommRing R]

theorem geom_succ (k : ℕ) (a b : R) :
    ∑ i ∈ Finset.range (k + 1), a ^ i * b ^ (k + 1 - 1 - i) =
      a ^ k + b * ∑ i ∈ Finset.range k, a ^ i * b ^ (k - 1 - i) := by
  rw [Finset.sum_range_succ, Finset.mul_sum, add_comm]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    have : k + 1 - 1 - i = (k - 1 - i) + 1 := by omega
    rw [this]; ring

theorem exists_divided_difference (k : ℕ) (y w z : R) : ∃ H : R,
    (∑ i ∈ Finset.range k, y ^ i * z ^ (k - 1 - i)) -
        (∑ i ∈ Finset.range k, y ^ i * w ^ (k - 1 - i)) = (z - w) * H ∧
    (∑ i ∈ Finset.range k, y ^ i * z ^ (k - 1 - i)) -
        (∑ i ∈ Finset.range k, w ^ i * z ^ (k - 1 - i)) = (y - w) * H ∧
    (∑ i ∈ Finset.range k, w ^ i * z ^ (k - 1 - i)) -
        (∑ i ∈ Finset.range k, y ^ i * w ^ (k - 1 - i)) = (z - y) * H := by
  induction k with
  | zero => exact ⟨0, by simp, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨H, h1, h2, h3⟩ := ih
    have eyw := geom_sum₂_mul y w k
    rw [geom_succ, geom_succ, geom_succ]
    refine ⟨(∑ i ∈ Finset.range k, y ^ i * w ^ (k - 1 - i)) + z * H, ?_, ?_, ?_⟩
    · linear_combination z * h1
    · linear_combination z * h2 - eyw
    · linear_combination z * h3 + eyw

end Ring

variable {Z : ITh}

theorem ck_add (hc : ∀ (E E' : Z.VDiv) (a : Z.Ch), Z.capDeg E (Z.cD E' * a) = Z.capDeg E' (Z.cD E * a))
    {r : ℕ} (P P' P'' : FPair Z r) (h1 : P'.x = P.x') (h2 : P''.x = P.x) (h3 : P''.x' = P'.x')
    (h4 : ∀ i, P''.Dv i = P.Dv i + P'.Dv i) (k : ℕ) (Q : Z.Ch) :
    ck P'' k Q = ck P k Q + ck P' k Q := by
  unfold ck
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hP := P.hx i
  have hP' := P'.hx i
  rw [h1] at hP'
  rw [h4, h2, h3, h1, map_add, LinearMap.add_apply]
  obtain ⟨H, e1, e2, -⟩ := exists_divided_difference k (Z.c1 (P.x i)) (Z.c1 (P.x' i)) (Z.c1 (P'.x' i))
  have f1 : Gk Z k (Z.c1 (P.x i)) (Z.c1 (P'.x' i)) * Q =
      Gk Z k (Z.c1 (P.x i)) (Z.c1 (P.x' i)) * Q - Z.cD (P'.Dv i) * (H * Q) := by
    unfold Gk
    linear_combination Q * e1 + H * Q * hP'
  have f2 : Gk Z k (Z.c1 (P.x i)) (Z.c1 (P'.x' i)) * Q =
      Gk Z k (Z.c1 (P.x' i)) (Z.c1 (P'.x' i)) * Q + Z.cD (P.Dv i) * (H * Q) := by
    unfold Gk
    linear_combination Q * e2 - H * Q * hP
  have g1 := congrArg (Z.capDeg (P.Dv i)) f1
  have g2 := congrArg (Z.capDeg (P'.Dv i)) f2
  rw [map_sub] at g1
  rw [map_add] at g2
  rw [g1, g2, hc (P.Dv i) (P'.Dv i)]
  ring

theorem ck_scalar {r : ℕ} (P : FPair Z r) (v : ℚ) (h : ∀ i, P.Dv i = v • Z.divP) (k : ℕ) (Q : Z.Ch) :
    ck P k Q = (k : ℚ) * v * Z.capDeg Z.divP ((∑ i, Z.c1 (P.x i) ^ (k - 1)) * Q) := by
  unfold ck
  rw [Finset.sum_mul, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hP := P.hx i
  rw [h, map_smul, Z.cD_divP, smul_zero, sub_zero] at hP
  have hG : Gk Z k (Z.c1 (P.x i)) (Z.c1 (P.x i)) * Q = (k : ℚ) • (Z.c1 (P.x i) ^ (k - 1) * Q) := by
    unfold Gk
    rw [geom_sum₂_self, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_assoc]
  rw [h, hP, hG, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

theorem ck_scale {r : ℕ} (P P' : FPair Z r) (c : ℚ)
    (h1 : ∀ i, Z.c1 (P'.x i) = c • Z.c1 (P.x i)) (h2 : ∀ i, Z.c1 (P'.x' i) = c • Z.c1 (P.x' i))
    (h3 : ∀ i, P'.Dv i = c • P.Dv i) (k : ℕ) (Q : Z.Ch) : ck P' k Q = c ^ k * ck P k Q := by
  unfold ck
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases k with _ | k
  · simp [Gk]
  have hG : Gk Z (k + 1) (c • Z.c1 (P.x i)) (c • Z.c1 (P.x' i)) * Q =
      c ^ k • (Gk Z (k + 1) (Z.c1 (P.x i)) (Z.c1 (P.x' i)) * Q) := by
    unfold Gk
    rw [← smul_mul_assoc, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha' := Finset.mem_range.1 ha
    rw [smul_pow, smul_pow, smul_mul_smul_comm, ← pow_add]
    congr 2
    omega
  rw [h1, h2, h3, hG, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

end GlobalTheory.RootChernRules
