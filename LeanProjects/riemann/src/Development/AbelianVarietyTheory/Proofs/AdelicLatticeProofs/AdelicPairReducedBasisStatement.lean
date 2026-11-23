import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AdelicPairReducedBasis
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_pair_reduced_basis : ∀ (F : Type) [Field F] [NumberField F] (β : Type) [Fintype β] (ω : Module.Basis β ℤ (𝓞 F)), ∃ (R : Type) (_ : CommRing R) (_ : Algebra ℚ R) (R₀ : Subring R) (_ : Algebra R (FiniteAdeleRing (𝓞 F) F)) (b : Module.Basis β R (FiniteAdeleRing (𝓞 F) F)), AdelicPair R R₀ ∧ IsReduced R ∧ (∀ i, b i = algebraMap F (FiniteAdeleRing (𝓞 F) F) (ω i : 𝓞 F)) ∧ ∀ a : FiniteAdeleRing (𝓞 F) F, (∀ v, (a : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ↔ ∀ i, b.repr a i ∈ R₀ := by
  first | exact @GlobalTheory.AdeleFree.finiteAdele_free | exact GlobalTheory.AdeleFree.finiteAdele_free | (intros; apply GlobalTheory.AdeleFree.finiteAdele_free <;> assumption)
