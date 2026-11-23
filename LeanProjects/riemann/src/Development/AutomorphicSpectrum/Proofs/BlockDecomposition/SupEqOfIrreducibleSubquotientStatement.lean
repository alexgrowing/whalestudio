import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupEqOfIrreducibleSubquotient
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sup_eq_of_irreducible_subquotient : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (A B E : Subrepresentation ρ), B ≤ A → (subQuot A B).IsIrreducible → E ≤ A → ¬ E ≤ B → E ⊔ B = A := by
  first | exact @GlobalTheory.CompanionTheory.GenCore.sup_eq_of_isIrreducible_subQuot | exact GlobalTheory.CompanionTheory.GenCore.sup_eq_of_isIrreducible_subQuot | (intros; apply GlobalTheory.CompanionTheory.GenCore.sup_eq_of_isIrreducible_subQuot <;> assumption)
