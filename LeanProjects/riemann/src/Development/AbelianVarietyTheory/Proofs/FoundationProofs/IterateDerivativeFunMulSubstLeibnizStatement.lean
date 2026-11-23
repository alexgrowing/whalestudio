import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IterateDerivativeFunMulSubstLeibniz
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iterate_derivativeFun_mul_subst_leibniz : ∀ (k : Type) [Field k] (a φ ψ : PowerSeries k) (l : ℕ), PowerSeries.constantCoeff a = 0 →
 (((PowerSeries.derivativeFun)^[l] (φ * ψ)).subst a : PowerSeries k) = ∑ p ∈ Finset.range (l + 1), l.choose p • ((((PowerSeries.derivativeFun)^[p] φ).subst a : PowerSeries k) * ((PowerSeries.derivativeFun)^[l - p] ψ).subst a) := by
  first | exact @GlobalTheory.iterate_derivativeFun_mul_subst | exact GlobalTheory.iterate_derivativeFun_mul_subst | (intros; apply GlobalTheory.iterate_derivativeFun_mul_subst <;> assumption)
