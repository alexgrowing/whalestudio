import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DsumEqZeroOfFibreSums
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockParOpp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPartMul
open MeasureTheory Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dsum_eq_zero_of_fibre_sums' : ∀ (H : Type) [Group H] (T P N L U : Subgroup H) (Ψ : H → ℂ), T ≤ P → N ≤ P → L ≤ P →
  (∀ p ∈ P, ∀ n ∈ N, p * n * p⁻¹ ∈ N) → (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) →
  (∀ t ∈ T, ∀ x, Ψ (t * x) = Ψ x) → (∀ l ∈ L, ∀ x, Ψ (x * l) = Ψ x) → (∀ x, x ∉ P → Ψ x = 0) →
  (∀ x ∈ P, (T ⊓ L.map (MulAut.conj x).toMonoidHom).relIndex (T ⊓ (L ⊔ N).map (MulAut.conj x).toMonoidHom) ≠ 0) →
  (∀ m ∈ P, ∑ᶠ q : H ⧸ (N ⊓ L), (if Quotient.out q ∈ N then Ψ (m * Quotient.out q) else 0) = 0) →
  GlobalTheory.OrbDesc.dsum T L U Ψ = 0 := by
  first | (exact @GlobalTheory.OrbDesc.dsum_eq_zero_of_fibre_sums) | (exact GlobalTheory.OrbDesc.dsum_eq_zero_of_fibre_sums) | (intros; apply GlobalTheory.OrbDesc.dsum_eq_zero_of_fibre_sums  <;> assumption)
