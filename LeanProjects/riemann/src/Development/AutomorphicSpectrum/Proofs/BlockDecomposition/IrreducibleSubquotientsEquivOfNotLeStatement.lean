import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientsEquivOfNotLe
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_subquotients_equiv_of_not_le : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (E K L : Subrepresentation ρ), (subQuot E K).IsIrreducible → (subQuot E L).IsIrreducible → ¬ E ≤ E ⊓ K ⊔ E ⊓ L → Nonempty ((subQuot E K).Equiv (subQuot E L)) := by
  first | exact @GlobalTheory.CompanionTheory.GenCore.nonempty_equiv_subQuot | exact GlobalTheory.CompanionTheory.GenCore.nonempty_equiv_subQuot | (intros; apply GlobalTheory.CompanionTheory.GenCore.nonempty_equiv_subQuot <;> assumption)
