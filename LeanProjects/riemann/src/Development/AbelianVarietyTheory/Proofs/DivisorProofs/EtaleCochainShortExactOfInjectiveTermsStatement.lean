import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainShortExactOfInjectiveTerms
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
theorem _root_.GlobalTheory.T.etaleCochain_shortExact_of_injective_terms : ∀ (R : Type) [CommRing R] (I : Cx R), (∀ n, Injective (I.X n)) → ∀ (S : ShortComplex (Cx R)), S.ShortExact → ∀ n : ℤ, (∀ a : Cochain S.X₁ I n, ∃ b : Cochain S.X₂ I n, (Cochain.ofHom S.f).comp b (zero_add n) = a) ∧ (∀ b : Cochain S.X₂ I n, (Cochain.ofHom S.f).comp b (zero_add n) = 0 → ∃ c : Cochain S.X₃ I n, (Cochain.ofHom S.g).comp c (zero_add n) = b) ∧ ∀ c : Cochain S.X₃ I n, (Cochain.ofHom S.g).comp c (zero_add n) = 0 → c = 0 := by
  first | exact @GlobalTheory.EtC.cochain_shortExact_of_injective | exact GlobalTheory.EtC.cochain_shortExact_of_injective | (intros; apply GlobalTheory.EtC.cochain_shortExact_of_injective <;> assumption)
