import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIdealCoprimeConjMulEqSpanSingleton
import Formalism.LocalRingCardinality.DataSpaces
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ideal_coprime_conj_mul_eq_spanSingleton' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E → ∀ (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), c ≠ 0 → ∀ N : 𝓞 E, N ≠ 0 → ∃ P : Ideal (𝓞 E), P ≠ ⊥ ∧ P ⊔ P.comap (RingOfIntegers.mapRingHom (starRingEnd E)) = ⊤ ∧ (∃ t : 𝓞 E, ∃ p ∈ P, t * N + p = 1) ∧ ∃ α : E, (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) α := by
  first | exact @GlobalTheory.exists_ideal_coprime_conj_mul_eq_spanSingleton | exact GlobalTheory.exists_ideal_coprime_conj_mul_eq_spanSingleton | (intros; apply GlobalTheory.exists_ideal_coprime_conj_mul_eq_spanSingleton <;> assumption)
