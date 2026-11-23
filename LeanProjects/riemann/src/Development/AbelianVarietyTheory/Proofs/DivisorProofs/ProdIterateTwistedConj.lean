import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal

open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes
open scoped TensorProduct

namespace GlobalTheory.LKResNrmConj

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem coe_frobQ_iterate (r k : ℕ) (b : Qr p r) :
    (((⇑(frobQ p r))^[k] b : Qr p r) : PadicAlgCl p) = (frobK p (Q0 p) ^ k) (b : PadicAlgCl p) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ', AlgEquiv.mul_apply, ← ih]
    rfl

theorem frobQ_iterate_self (r : ℕ) (hr : 0 < r) (b : Qr p r) : (⇑(frobQ p r))^[r] b = b := by
  refine Subtype.ext ?_
  have hK : FiniteDimensional ℚ_[p] (Q0 p) := inferInstance
  rw [coe_frobQ_iterate]
  exact (IsFrobOn.pow_fixes_iff p (Q0 p) hK hr ((isFrob_frobK hK).isFrobOn r) r).2 dvd_rfl _ b.2

theorem sigKQ_iterate_self (r : ℕ) (hr : 0 < r) (y : KQ p K r) : (⇑(sigKQ p K r))^[r] y = y := by
  have ht : ∀ (k : ℕ) (a : K) (b : Qr p r), (⇑(sigKQ p K r))^[k] (inclK p K r a * inclQ p K r b) =
      inclK p K r a * inclQ p K r ((⇑(frobQ p r))^[k] b) := by
    intro k a b
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, map_mul, sigKQ_apply_inclK, sigKQ_apply_inclQ,
        Function.iterate_succ_apply']
  have key : ∀ z : K ⊗[ℚ_[p]] Qr p r, (⇑(sigKQ p K r))^[r] (z : KQ p K r) = (z : KQ p K r) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact iterate_map_zero (sigKQ p K r) r
    | tmul a b =>
      have e : inclK p K r a * inclQ p K r b = (a ⊗ₜ[ℚ_[p]] b : K ⊗[ℚ_[p]] Qr p r) := by
        change (a ⊗ₜ[ℚ_[p]] (1 : Qr p r)) * ((1 : K) ⊗ₜ[ℚ_[p]] b) = a ⊗ₜ[ℚ_[p]] b
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      have h := ht r a b
      rw [frobQ_iterate_self p r hr, e] at h
      exact h
    | add z w hz hw =>
      exact (iterate_map_add (sigKQ p K r) r (z : KQ p K r) (w : KQ p K r)).trans (congrArg₂ (· + ·) hz hw)
  exact key y

theorem sigRes_iterate_self (n r : ℕ) (hr : 0 < r) (g : GL (Fin n) (KQ p K r)) :
    (⇑(sigRes p K n r))^[r] g = g := by
  have h : ∀ (k : ℕ) (i j : Fin n), ((⇑(sigRes p K n r))^[k] g).val i j = (⇑(sigKQ p K r))^[k] (g.val i j) := by
    intro k i j
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [h, sigKQ_iterate_self p K r hr]

end GlobalTheory.LKResNrmConj
