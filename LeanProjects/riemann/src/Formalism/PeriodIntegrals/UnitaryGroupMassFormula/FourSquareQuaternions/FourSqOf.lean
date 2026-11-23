import Mathlib
import Formalism.PeriodIntegrals.KerIso

noncomputable section
open scoped BigOperators

namespace PI.KerIso.FourSqW

def DiagId {K E : Type} [Field K] [Field E] [Algebra K E] (cj : E → E) {n : Type} [Fintype n]
    (b : Module.Basis n K E) (q : n → ℚ) : Prop :=
  ∀ x y, algebraMap K E (Algebra.trace K E (x * cj y)) =
    ∑ i, (q i : E) * (algebraMap K E (b.repr x i) * cj (algebraMap K E (b.repr y i)))

def OrthDiag : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (cj : E ≃ₐ[ℚ] E)
    (n : Type) [Fintype n],
    Module.finrank ℚ K = 2 → Fintype.card n = Module.finrank K E → IsConj K cj →
    (∀ x : E, x ≠ 0 → 0 < Algebra.trace ℚ E (x * cj x)) →
      ∃ (b : Module.Basis n K E) (q : n → ℚ), (∀ i, 0 < q i) ∧ DiagId (K := K) cj b q

def FromDiag : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (cj : E ≃ₐ[ℚ] E)
    (n : Type) [Fintype n] (b : Module.Basis n K E) (q : n → ℚ),
    (∀ i, 0 < q i) → DiagId (K := K) cj b q →
      ∃ g : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K), IsIsom cj g

theorem fourSq_of (hA : OrthDiag) (hB : FromDiag) : FourSq := by
  intro K E _ _ _ _ _ cj n _ h2 hn hc hpos
  obtain ⟨b, q, hq, hb⟩ := hA K E cj n h2 hn hc hpos
  exact hB K E cj n b q hq hb

end PI.KerIso.FourSqW
