import Mathlib
import Formalism.LocalToGlobal.Columns.BrzoPairAtZeroRight
import Formalism.LocalToGlobal.Columns.BzdConjTTranspose
import Formalism.LocalToGlobal.Columns.SliceIntegralDeltaNeBot

open NumberField IsDedekindDomain Module MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN Formalism.HermitianLattices.TraceIntegrality

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ} (lam : DomWeight n)

def extQ (lam : DomWeight n) : ℚ := Formalism.GradedWeylDivisibility.fockQ (extremal ℚ n lam) (extremal ℚ n lam)

def supS : Finset ((Unit × Fin n × Fin n) →₀ ℕ) :=
  Finset.univ.biUnion fun i : VVIdx (oneW lam) => (bVVfun K (oneW lam) i).support

end Std

section Std2

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ} (lam : DomWeight n)

def wS (m : (Unit × Fin n × Fin n) →₀ ℕ) : ℝ := (mfact m : ℝ) / (extQ lam : ℝ)

end Std2

theorem factorial_sum_le_pow_mul_prod {k : ℕ} (a : Fin k → ℕ) : (∑ i, a i).factorial ≤ k ^ (∑ i, a i) * ∏ i, (a i).factorial := by
  have h1 := Nat.multinomial_spec Finset.univ a
  have h2 := Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset (Fin k)) (fun _ => (1 : ℕ)) (∑ i, a i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, one_pow, Finset.prod_const_one,
    Nat.cast_id] at h2
  have h3 : Nat.multinomial Finset.univ a ≤ k ^ (∑ i, a i) := by
    rw [h2]
    exact Finset.single_le_sum (f := fun b => Nat.multinomial Finset.univ b) (fun _ _ => Nat.zero_le _)
      (Finset.mem_piAntidiag.2 ⟨rfl, fun i _ => Finset.mem_univ i⟩)
  calc (∑ i, a i).factorial = (∏ i, (a i).factorial) * Nat.multinomial Finset.univ a := h1.symm
    _ ≤ (∏ i, (a i).factorial) * k ^ (∑ i, a i) := Nat.mul_le_mul_left _ h3
    _ = _ := mul_comm _ _

section Deg

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ} (lam : DomWeight n)

end Deg

def HwNormBound : Prop :=
  ∀ (κ : ℕ) (ν : Fin (κ + 1) → ℕ), Antitone ν →
    Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl (κ + 1)) ν) (Formalism.GradedWeylDivisibility.hw ℚ (le_refl (κ + 1)) ν) ≤
      ((∏ i, (ν i).factorial : ℕ) : ℚ) * ((ν 0 + κ + 1 : ℕ) : ℚ) ^ ((κ + 1) * κ / 2)

theorem natural_weight_cast_eq {κ : ℕ} (lam : DomWeight (κ + 1)) (i : Fin (κ + 1)) :
    ((lam.natW i : ℕ) : ℤ) = plus (castW rfl lam) i := by
  have hds : lam.detShift = lam.w (Fin.last κ) := by
    unfold DomWeight.detShift
    rw [dif_pos (Nat.succ_pos κ)]
    congr 1
  have hle : lam.w (Fin.last κ) ≤ lam.w i := lam.anti (Fin.le_last i)
  simp only [DomWeight.natW, plus, castW, Fin.cast_eq_self, hds]
  rw [Int.toNat_of_nonneg (by linarith)]

theorem natural_weight_antitone {n : ℕ} (lam : DomWeight n) : Antitone lam.natW := fun a b hab => by
  show (lam.w b - lam.detShift).toNat ≤ (lam.w a - lam.detShift).toNat
  exact Int.toNat_le_toNat (sub_le_sub_right (lam.anti hab) _)

theorem triangular_number_cast (κ : ℕ) : (((κ + 1) * κ / 2 : ℕ) : ℝ) = ((κ : ℝ) + 1) * (κ : ℝ) / 2 := by
  have h2 : 2 ∣ (κ + 1) * κ := by
    rw [mul_comm]
    exact (Nat.even_mul_succ_self κ).two_dvd
  rw [Nat.cast_div h2 (by norm_num)]
  push_cast
  ring

end Formalism.L2.Col
