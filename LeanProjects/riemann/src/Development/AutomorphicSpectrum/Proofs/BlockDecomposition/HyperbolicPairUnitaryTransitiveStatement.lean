import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicPairUnitaryTransitive
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeGramScalarAlmostAll
open HeckeCharacterZeroLocus.SiegelWeilU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_pair_unitary_transitive : ∀ (A : Type) [CommRing A] (τ : A →+* A), (∀ y, τ (τ y) = y) → IsUnit (2 : A) → (∀ p β : A, IsUnit β → τ β = β → ∃ ε z : A, ε * τ ε = 1 ∧ (β - τ ε * p) * z = 1) → ∀ (N : ℕ) (H Hi : Matrix (Fin N) (Fin N) A), H * Hi = 1 → (∀ i j, τ (H j i) = H i j) → ∀ e f y a : Fin N → A, hform τ H e e = 0 → hform τ H f f = 0 → hform τ H e f = 1 → hform τ H y y = 0 → ∑ k, a k * y k = 1 → ∃ g ∈ UJ τ H, (g : Matrix (Fin N) (Fin N) A) *ᵥ e = y := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry.exists_unitary_carry_primitive | exact GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry.exists_unitary_carry_primitive | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry.exists_unitary_carry_primitive <;> assumption)
