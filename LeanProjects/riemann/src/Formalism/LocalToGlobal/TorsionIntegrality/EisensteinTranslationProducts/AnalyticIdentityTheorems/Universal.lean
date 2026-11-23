import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinS2LimitFormula
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.WeierstrassNumeratorDenominator
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.TaylorWp
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CoeffPowEqZeroOfCc

noncomputable section
open scoped BigOperators
open Formalism.L2.Th1.CM (cW)
open PowerSeries

namespace Formalism.L2.Th1.F

namespace Universal

def IsU (a : ∀ (K : Type) [Field K] [CharZero K], K → K → K) : Prop :=
  ∃ p : MvPolynomial (Fin 2) ℚ, ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K),
    a K g2 g3 = MvPolynomial.aeval ![g2, g3] p

theorem IsU.congr {a b : ∀ (K : Type) [Field K] [CharZero K], K → K → K} (h : IsU a)
    (hab : ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K), b K g2 g3 = a K g2 g3) : IsU b := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, fun K _ _ g2 g3 => by rw [hab, hp]⟩

theorem isU_const (q : ℚ) : IsU (fun K [Field K] [CharZero K] _ _ => (q : K)) :=
  ⟨MvPolynomial.C q, fun K _ _ g2 g3 => by rw [MvPolynomial.aeval_C, eq_ratCast]⟩

theorem universal_g2 : IsU (fun K [Field K] [CharZero K] g2 _ => g2) :=
  ⟨MvPolynomial.X 0, fun K _ _ g2 g3 => by simp⟩

theorem universal_g3 : IsU (fun K [Field K] [CharZero K] _ g3 => g3) :=
  ⟨MvPolynomial.X 1, fun K _ _ g2 g3 => by simp⟩

theorem IsU.add {a b : ∀ (K : Type) [Field K] [CharZero K], K → K → K} (ha : IsU a) (hb : IsU b) :
    IsU (fun K [Field K] [CharZero K] g2 g3 => a K g2 g3 + b K g2 g3) := by
  obtain ⟨p, hp⟩ := ha
  obtain ⟨q, hq⟩ := hb
  exact ⟨p + q, fun K _ _ g2 g3 => by
    show a K g2 g3 + b K g2 g3 = _
    rw [map_add, hp, hq]⟩

theorem IsU.mul {a b : ∀ (K : Type) [Field K] [CharZero K], K → K → K} (ha : IsU a) (hb : IsU b) :
    IsU (fun K [Field K] [CharZero K] g2 g3 => a K g2 g3 * b K g2 g3) := by
  obtain ⟨p, hp⟩ := ha
  obtain ⟨q, hq⟩ := hb
  exact ⟨p * q, fun K _ _ g2 g3 => by
    show a K g2 g3 * b K g2 g3 = _
    rw [map_mul, hp, hq]⟩

theorem IsU.sum {ι : Type} (s : Finset ι) (a : ι → ∀ (K : Type) [Field K] [CharZero K], K → K → K)
    (h : ∀ i ∈ s, IsU (a i)) :
    IsU (fun K [Field K] [CharZero K] g2 g3 => ∑ i ∈ s, a i K g2 g3) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (isU_const 0).congr fun K _ _ g2 g3 => by simp
  | insert i s hi ih =>
    refine ((h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))).congr fun K _ _ g2 g3 => ?_
    rw [Finset.sum_insert hi]

theorem isU_cW (k : ℕ) : IsU (fun K [Field K] [CharZero K] g2 g3 => cW g2 g3 k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases h2 : k = 2
    · refine (universal_g2.mul (isU_const (1 / 20))).congr fun K _ _ g2 g3 => ?_
      rw [POf.cW_eq, if_pos h2]
      push_cast
      ring
    by_cases h3 : k = 3
    · refine (universal_g3.mul (isU_const (1 / 28))).congr fun K _ _ g2 g3 => ?_
      rw [POf.cW_eq, if_neg h2, if_pos h3]
      push_cast
      ring
    by_cases h4 : 4 ≤ k
    · refine ((isU_const (3 / ((2 * (k : ℚ) + 1) * ((k : ℚ) - 3)))).mul
        (IsU.sum Finset.univ (fun (m : Fin (k - 3)) K [Field K] [CharZero K] g2 g3 =>
          cW g2 g3 (m.val + 2) * cW g2 g3 (k - (m.val + 2)))
          fun m _ => (ih (m.val + 2) (by omega)).mul (ih (k - (m.val + 2)) (by omega)))).congr
        fun K _ _ g2 g3 => ?_
      rw [POf.cW_eq, if_neg h2, if_neg h3, if_pos h4]
      push_cast
      rfl
    · refine (isU_const 0).congr fun K _ _ g2 g3 => ?_
      rw [POf.cW_eq, if_neg h2, if_neg h3, if_neg h4]
      simp

theorem isU_pOf (n : ℕ) : IsU (fun K [Field K] [CharZero K] g2 g3 => coeff n (pOf g2 g3)) := by
  by_cases hn : Even n
  · exact (isU_cW (n / 2 + 1)).congr fun K _ _ g2 g3 => by rw [POf.coeff_pOf, if_pos hn]
  · exact (isU_const 0).congr fun K _ _ g2 g3 => by rw [POf.coeff_pOf, if_neg hn]; simp

theorem isU_prim (n : ℕ) :
    IsU (fun K [Field K] [CharZero K] g2 g3 => coeff n (-B.prim (pOf g2 g3))) := by
  by_cases hn : n = 0
  · exact (isU_const 0).congr fun K _ _ g2 g3 => by
      rw [map_neg, B.prim, coeff_mk, if_pos hn]; simp
  · refine ((isU_pOf (n - 1)).mul (isU_const (-1 / (n : ℚ)))).congr fun K _ _ g2 g3 => ?_
    rw [map_neg, B.prim, coeff_mk, if_neg hn]
    push_cast
    ring

variable {K : Type} [Field K] [CharZero K]

theorem coeff_exp_succ (P : PowerSeries K) (n : ℕ) :
    coeff (n + 1) (B.fExp (B.sigS P) : PowerSeries K) =
      ((1 / ((n : ℚ) + 1) : ℚ) : K) * ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        coeff ij.1 (-B.prim P) * coeff ij.2 (B.fExp (B.sigS P) : PowerSeries K) := by
  have hS0 : constantCoeff (B.sigS P) = 0 := by
    rw [B.sigS, map_neg, B.constantCoeff_prim, neg_zero]
  have hSd : derivative K (B.sigS P) = -B.prim P := by
    rw [B.sigS, map_neg]
    exact congrArg Neg.neg (B.dz_prim _)
  have h : derivative K (B.fExp (B.sigS P) : PowerSeries K) =
      -B.prim P * (B.fExp (B.sigS P) : PowerSeries K) := by
    rw [← hSd]
    exact C.derivative_mvExp hS0
  have hc := congrArg (coeff n) h
  rw [coeff_derivative, coeff_mul] at hc
  rw [← hc]
  have hn : ((n : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp

theorem coeff_exp_zero (P : PowerSeries K) :
    coeff 0 (B.fExp (B.sigS P) : PowerSeries K) = 1 := by
  have hS0 : constantCoeff (B.sigS P) = 0 := by
    rw [B.sigS, map_neg, B.constantCoeff_prim, neg_zero]
  rw [coeff_zero_eq_constantCoeff_apply]
  exact C.constantCoeff_mvExp hS0

theorem isU_exp (n : ℕ) : IsU (fun K [Field K] [CharZero K] g2 g3 =>
    coeff n (B.fExp (B.sigS (pOf g2 g3)) : PowerSeries K)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · exact (isU_const 1).congr fun K _ _ g2 g3 => by rw [coeff_exp_zero]; simp
    · refine ((isU_const (1 / ((n : ℚ) + 1))).mul
        (IsU.sum (Finset.HasAntidiagonal.antidiagonal n) (fun ij K [Field K] [CharZero K] g2 g3 =>
          coeff ij.1 (-B.prim (pOf g2 g3)) *
            coeff ij.2 (B.fExp (B.sigS (pOf g2 g3)) : PowerSeries K))
          fun ij hij => (isU_prim ij.1).mul (ih ij.2 ?_))).congr
        fun K _ _ g2 g3 => coeff_exp_succ _ n
      have := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      omega

theorem isU_sigma (n : ℕ) : IsU (fun K [Field K] [CharZero K] g2 g3 =>
    coeff n (B.sigma (pOf g2 g3))) := by
  rcases n with _ | n
  · exact (isU_const 0).congr fun K _ _ g2 g3 => by
      rw [B.sigma, coeff_zero_X_mul]; simp
  · exact (isU_exp n).congr fun K _ _ g2 g3 => by
      rw [B.sigma, coeff_succ_X_mul]

end Universal

theorem sigmaUniversal_of (hu : IsWpUnique) (hp : POfIsWp) : SigmaUniversal := by
  choose U hU using Universal.isU_sigma
  refine ⟨U, fun K _ _ g2 g3 P hP n => ?_⟩
  rw [hu K g2 g3 P (pOf g2 g3) hP (hp K g2 g3)]
  exact hU n K g2 g3

theorem sigma_universal : SigmaUniversal := sigmaUniversal_of weierstrass_series_unique weierstrass_p_of_series

end Formalism.L2.Th1.F
