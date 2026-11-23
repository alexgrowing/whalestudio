import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem coeff_prod_one_sub_C_mul_X (c : ℂ) (α : Multiset ℂ) (k : ℕ) :
    ((α.map fun a => (1 : Polynomial ℂ) - Polynomial.C (c * a) * Polynomial.X).prod).coeff k
      = (-1 : ℂ) ^ k * c ^ k * α.esymm k := by
  induction α using Multiset.induction_on generalizing k with
  | empty =>
    cases k with
    | zero => simp [Multiset.esymm]
    | succ k => simp [Multiset.esymm, Polynomial.coeff_one, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, sub_mul, one_mul, mul_assoc, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul]
    cases k with
    | zero => rw [ih]; simp [Multiset.esymm]
    | succ k =>
      have h : (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
        simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]
      rw [Polynomial.coeff_X_mul, ih, ih, h]
      ring

theorem normalised_esymm_eq_coeff :
    ∀ (r : ℕ) (q : ℝ), 0 < q → ∀ (α : Multiset ℂ), Multiset.card α = r → ∀ k, k ≤ r → (-1 : ℂ) ^ k * (q : ℂ) ^ (k * (k - 1) / 2) * ((q : ℂ) ^ (((k : ℂ) * ((r : ℂ) - k)) / 2) * α.esymm k) = ((α.map fun a => (1 : Polynomial ℂ) - Polynomial.C ((q : ℂ) ^ (((r : ℂ) - 1) / 2) * a) * Polynomial.X).prod).coeff k := by
  intro r q hq α _ k _
  rw [coeff_prod_one_sub_C_mul_X]
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hk : ((k * (k - 1) / 2 : ℕ) : ℂ) = (k : ℂ) * ((k : ℂ) - 1) / 2 := by
    rw [← Nat.choose_two_right, Nat.cast_choose_two]
  have h : (q : ℂ) ^ (k * (k - 1) / 2) * (q : ℂ) ^ (((k : ℂ) * ((r : ℂ) - k)) / 2)
      = ((q : ℂ) ^ (((r : ℂ) - 1) / 2)) ^ k := by
    rw [← Complex.cpow_natCast (q : ℂ) (k * (k - 1) / 2), ← Complex.cpow_add _ _ hq0, hk,
      ← Complex.cpow_nat_mul]
    congr 1
    ring
  rw [← h]
  ring

end GlobalTheory
