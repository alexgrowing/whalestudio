import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullLatticePrimeToPBasis
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPart
open NumberField ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt GlobalTheory.LieRead
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_lattice_prime_to_p_basis : ∀ (K : Type) [Field K] [NumberField K] (g p : ℕ) [Fact p.Prime] (L : Submodule (𝓞 K) (Fin g → K)), Full L → ∃ (x : Fin g → Fin g → K) (s : ℕ), (∀ i, x i ∈ L) ∧ LinearIndependent K x ∧ ¬ p ∣ s ∧ ∀ v ∈ L, (s : K) • v ∈ Submodule.span (𝓞 K) (Set.range x) := by
  first | exact @GlobalTheory.FullLatLocBasis.exists_basis_primeTo_p | exact GlobalTheory.FullLatLocBasis.exists_basis_primeTo_p | (intros; apply GlobalTheory.FullLatLocBasis.exists_basis_primeTo_p <;> assumption)
