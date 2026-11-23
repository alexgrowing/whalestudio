import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefficientCongruenceOfTwistedValuesStatement
import Development.AbelianVarietyTheory.Definitions.Foundations.NotZeroChi
open GlobalTheory.KZ GlobalTheory.Ord2 UpperTheory.V.HV Formalism.ConjugateSelfDual PowerSeries

namespace GlobalTheory

theorem KZ.norm_prime_lt_one_qbar (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [map_natCast] at h
  rw [h]
  exact Padic.norm_p_lt_one

theorem KZ.eq_zero_of_cg_all (l : ℕ) [Fact l.Prime] (x : Qbar l) (h : ∀ k : ℕ, Cg k x 0) :
    x = 0 := by
  have hlt := KZ.norm_prime_lt_one_qbar l
  have hn : 0 ≤ ‖((l : ℕ) : Qbar l)‖ := norm_nonneg _
  have ht : Filter.Tendsto (fun k : ℕ => ‖((l : ℕ) : Qbar l)‖ ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hn hlt
  have hle : ∀ k : ℕ, ‖x‖ ≤ ‖((l : ℕ) : Qbar l)‖ ^ k := by
    intro k
    have := h k
    unfold Cg at this
    simpa [norm_pow] using this
  have h0 : ‖x‖ ≤ 0 := ge_of_tendsto' ht hle
  exact norm_le_zero_iff.mp h0

theorem KZ.series_eq_zero_of_vals_tendsto_zero : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (F : PowerSeries (Qbar l)), (∀ n, F.coeff n ∈ c.O) → (∀ k : ℕ, ∃ m₁ : ℕ, ∀ m, m₁ ≤ m → ∀ z : Qbar l, IsPrimitiveRoot z (l ^ m) → Cg k (tval F (l ^ (3 * m)) z) 0) → F = 0 := by
  intro l _ c F hO hv
  ext n
  rw [map_zero]
  apply KZ.eq_zero_of_cg_all l
  intro k
  obtain ⟨m₁, hm⟩ := hv k
  exact GlobalTheory.T.coefficient_congruence_of_twisted_values l c F k m₁ hO hm n

end GlobalTheory
