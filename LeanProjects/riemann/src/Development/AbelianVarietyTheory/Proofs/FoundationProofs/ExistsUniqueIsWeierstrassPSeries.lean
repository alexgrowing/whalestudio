import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFixedOfContract
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.WpSeries

open PowerSeries

variable {K : Type} [Field K]

def euler (R : PowerSeries K) : PowerSeries K := X * derivativeFun R

theorem coeff_euler (R : PowerSeries K) (n : ℕ) : coeff n (euler R) = (n : K) * coeff n R := by
  cases n with
  | zero => simp [euler]
  | succ n =>
    rw [euler, coeff_succ_X_mul,
      show coeff n (derivativeFun R) = coeff (n + 1) R * ((n : K) + 1) from coeff_derivative R n]
    push_cast
    ring

theorem euler_one_add (R : PowerSeries K) : euler (1 + X * R) = X * (R + euler R) := by
  ext n
  cases n with
  | zero => simp [coeff_euler]
  | succ n =>
    simp only [coeff_euler, map_add, coeff_succ_X_mul, coeff_one]
    simp
    ring

def inv4 (R : PowerSeries K) : PowerSeries K := PowerSeries.mk fun n => coeff n R / (4 * ((n : K) + 2))

theorem inverseShiftedEulerOperatorFour_eq_iff [CharZero K] (R S : PowerSeries K) :
    inv4 S = R ↔ S = 4 * (2 * R + euler R) := by
  have h4 : (4 : PowerSeries K) = C 4 := (map_ofNat _ 4).symm
  have h2 : (2 : PowerSeries K) = C 2 := (map_ofNat _ 2).symm
  rw [PowerSeries.ext_iff, PowerSeries.ext_iff]
  refine forall_congr' fun n => ?_
  have hn : (4 * ((n : K) + 2)) ≠ 0 := by
    have : ((n : K) + 2) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    exact mul_ne_zero (by norm_num) this
  rw [inv4, coeff_mk, div_eq_iff hn, h4, h2, coeff_C_mul, map_add, coeff_C_mul, coeff_euler]
  constructor <;> intro h <;> rw [h] <;> ring

def rest (a b : K) (R : PowerSeries K) : PowerSeries K :=
  (euler R - R) ^ 2 - 12 * R ^ 2 - 4 * X * R ^ 3 + C a * X ^ 2 * (1 + X * R) + C b * X ^ 4

theorem contract (a b : K) (n : ℕ) (x y : PowerSeries K) (h : X ^ n ∣ x - y) :
    X ^ (n + 1) ∣ inv4 (X * rest a b x) - inv4 (X * rest a b y) := by
  have he : X ^ n ∣ euler x - euler y := by
    rw [X_pow_dvd_iff] at h ⊢
    intro m hm
    have := h m hm
    rw [map_sub, sub_eq_zero] at this
    rw [map_sub, coeff_euler, coeff_euler, this, sub_self]
  obtain ⟨u, hu⟩ := h
  obtain ⟨v, hv⟩ := he
  have hr : X ^ (n + 1) ∣ X * rest a b x - X * rest a b y := by
    refine ⟨(v - u) * (euler x - x + (euler y - y)) - 12 * u * (x + y)
      - 4 * X * u * (x ^ 2 + x * y + y ^ 2) + C a * X ^ 3 * u, ?_⟩
    unfold rest
    linear_combination X * (euler x - x + (euler y - y)) * hv +
      X * (-(euler x - x + (euler y - y)) - 12 * (x + y)
        - 4 * X * (x ^ 2 + x * y + y ^ 2) + C a * X ^ 3) * hu
  rw [X_pow_dvd_iff] at hr ⊢
  intro m hm
  have := hr m hm
  rw [map_sub, sub_eq_zero] at this
  rw [map_sub, inv4, inv4, coeff_mk, coeff_mk, this, sub_self]

theorem isWpSer_iff [CharZero K] (a b : K) (R : PowerSeries K) :
    IsWpSer a b (1 + X * R) ↔ inv4 (X * rest a b R) = R := by
  rw [inverseShiftedEulerOperatorFour_eq_iff]
  have he := euler_one_add R
  have hX : (X : PowerSeries K) ≠ 0 := X_ne_zero
  unfold IsWpSer
  change _ ∧ (euler (1 + X * R) - _) ^ 2 = _ ↔ _
  rw [he]
  unfold rest
  constructor
  · rintro ⟨-, h⟩
    apply mul_left_cancel₀ hX
    linear_combination h
  · intro h
    refine ⟨by simp, ?_⟩
    linear_combination X * h

theorem eq_one_add {P : PowerSeries K} (h : constantCoeff P = 1) : ∃ R, P = 1 + X * R := by
  obtain ⟨R, hR⟩ : X ∣ P - 1 := by rw [X_dvd_iff]; simp [h]
  exact ⟨R, by linear_combination hR⟩

theorem existsUnique_isWpSer :
    ∀ (K : Type) [Field K] [CharZero K] (a b : K), ∃! P : PowerSeries K, IsWpSer a b P := by
  intro K _ _ a b
  obtain ⟨R, hR⟩ := GlobalTheory.GenusOneDatum.exists_fixed_of_contract
    (fun R : PowerSeries K => inv4 (X * rest a b R)) (contract a b)
  refine ⟨1 + X * R, (isWpSer_iff a b R).2 hR, fun P hP => ?_⟩
  obtain ⟨S, rfl⟩ := eq_one_add hP.1
  have hS := (isWpSer_iff a b S).1 hP
  have hd : ∀ n : ℕ, X ^ n ∣ S - R := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := contract a b n S R ih
      rwa [hS, show inv4 (X * rest a b R) = R from hR] at this
  have : S = R := by
    ext n
    have := X_pow_dvd_iff.1 (hd (n + 1)) n (by omega)
    rwa [map_sub, sub_eq_zero] at this
  rw [this]

end GlobalTheory.WpSeries
