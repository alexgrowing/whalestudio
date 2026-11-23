import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericHasGenericIrreducibleSubquotient
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_has_generic_irreducible_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V), IsSmooth ρ → GlobalTheory.SmGL.HasFiniteLength ρ → IsGenericFor ψ ρ → ∃ A B : Subrepresentation ρ, B ≤ A ∧ (subQuot A B).IsIrreducible ∧ IsSmooth (subQuot A B) ∧ IsGenericFor ψ (subQuot A B) := by
  first | exact @GlobalTheory.CompanionTheory.GenExists.exists_generic_subQuot | exact GlobalTheory.CompanionTheory.GenExists.exists_generic_subQuot | (intros; apply GlobalTheory.CompanionTheory.GenExists.exists_generic_subQuot <;> assumption)
