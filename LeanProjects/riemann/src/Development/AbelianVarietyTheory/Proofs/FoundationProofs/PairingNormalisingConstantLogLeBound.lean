import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FockNormExtremalVectorEqBoundedNatStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogFactorialPowMulFactorialPowLeStatement
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem extNorm_eq_nat_log_le_bound : ∀ (K : Type) [Field K] [StarRing K] [CharZero K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R → ∃ s : ℕ, 0 < s ∧ extNorm K lam = (s : K) ∧ Real.log s ≤ bound (Fintype.card ι) n R := by
  intro K _ _ _ ι _ n lam R hR hS
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hw : ∀ τ i, (lam τ).natW i ≤ ⌊R⌋₊ := by
    intro τ i
    have hn : 0 < n := Fin.pos i
    have h := hS τ i ⟨n - 1, by omega⟩
    have h2 : (lam τ).w i - (lam τ).w ⟨n - 1, by omega⟩ ≤ (⌊R⌋₊ : ℤ) := by
      rw [Int.natCast_floor_eq_floor hR0]
      exact Int.le_floor.mpr h
    unfold DomWeight.natW DomWeight.detShift
    rw [dif_pos hn]
    omega
  choose s hs0 hs1 hs2 using fun τ => GlobalTheory.T.fockNorm_extremal_vector_eq_bounded_nat n (lam τ) ⌊R⌋₊ (hw τ)
  refine ⟨∏ τ, s τ, Finset.prod_pos fun τ _ => hs0 τ, ?_, ?_⟩
  · unfold extNorm
    rw [Nat.cast_prod]
    exact Finset.prod_congr rfl fun τ _ => hs2 τ K
  · rw [Nat.cast_prod, Real.log_prod (fun τ _ => by exact_mod_cast (hs0 τ).ne')]
    have hb := GlobalTheory.T.log_factorial_pow_mul_factorial_pow_le' n ⌊R⌋₊ R hR (Nat.floor_le hR0)
    have h1 : ∀ τ, Real.log (s τ) ≤ 4 * (n : ℝ) * R * Real.log (n * R) := fun τ =>
      le_trans (Real.log_le_log (by exact_mod_cast hs0 τ) (by exact_mod_cast hs1 τ)) hb
    calc ∑ τ, Real.log (s τ) ≤ ∑ _τ : ι, 4 * (n : ℝ) * R * Real.log (n * R) :=
          Finset.sum_le_sum fun τ _ => h1 τ
      _ = bound (Fintype.card ι) n R := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          unfold bound
          ring

end GlobalTheory
