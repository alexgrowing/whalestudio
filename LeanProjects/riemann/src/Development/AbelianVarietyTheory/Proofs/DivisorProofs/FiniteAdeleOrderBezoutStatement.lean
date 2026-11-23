import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleOrderBezout
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTensorFiniteAdeleEquiv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousSymmFinite
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_adele_order_bezout : ∀ (E : Type) [Field E] [NumberField E] (R : Set (FiniteAdeleRing (𝓞 E) E)), (∀ y, y ∈ R ↔ ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (y P) ≤ 1) →
    (∀ a b : FiniteAdeleRing (𝓞 E) E, ∃ u ∈ R, ∃ v ∈ R, ∃ r ∈ R, ∃ r' ∈ R, a = r * (u * a + v * b) ∧ b = r' * (u * a + v * b)) ∧
    (∀ p ∈ R, ∀ q ∈ R, ∃ s ∈ R, ∃ t ∈ R, ∃ d ∈ R, ∃ d' ∈ R, (s + t * p) * d = 1 ∧ (s * q + t) * d' = 1) ∧
    (∀ c ∈ R, ∃ e ∈ R, ∃ d ∈ R, e * e = e ∧ e * c * d = e ∧ ∀ m ∈ R, ∀ m' ∈ R, m * m' = 1 → ∀ a ∈ R, ∃ d' ∈ R, (m + (1 - e) * c * a) * d' = 1) := by
  first | exact @GlobalTheory.AdeleRing.bezout_units_idempotent | exact GlobalTheory.AdeleRing.bezout_units_idempotent | (intros; apply GlobalTheory.AdeleRing.bezout_units_idempotent <;> assumption)
