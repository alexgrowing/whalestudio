import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeneratorPowPrimeOneModModulus
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeNormOfKummer
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_pow_prime_one_mod_modulus : ∀ (L : Type) [Field L] [NumberField L] (𝔮 : Ideal (𝓞 L)) (h : ℕ), 𝔮 ≠ ⊥ → (∀ I : Ideal (𝓞 L), I ≠ ⊥ → IsCoprime I 𝔮 → ∃ α β : 𝓞 L, RayPair 𝔮 α β ∧ I ^ h * Ideal.span {β} = Ideal.span {α}) → ∀ v : HeightOneSpectrum (𝓞 L), ∃ k : Lˣ, FractionalIdeal.spanSingleton (𝓞 L)⁰ (k : L) = (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ h ∧ ∀ w : HeightOneSpectrum (𝓞 L), w ≠ v → w.asIdeal ∣ 𝔮 → w.valuation L ((k : L) - 1) < 1 := by
  first | exact @GlobalTheory.Mem.FieldsEx.exists_gen_pow_prime_one_mod | exact GlobalTheory.Mem.FieldsEx.exists_gen_pow_prime_one_mod | (intros; apply GlobalTheory.Mem.FieldsEx.exists_gen_pow_prime_one_mod <;> assumption)
