import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoGenericSubquotientsImpossible
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfNotInCodimOneSubmoduleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientEquivOfSupEqStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupEqOfIrreducibleSubquotientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientsEquivOfNotLeStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_equiv_subQuot_of_not_le_sup : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (T : Submodule ℂ V), Module.rank ℂ (V ⧸ T) ≤ 1 → (∀ X Y : Subrepresentation ρ, (X ⊔ Y).toSubmodule ⊓ T ≤ X.toSubmodule ⊓ T ⊔ Y.toSubmodule ⊓ T) → ∀ A B C D : Subrepresentation ρ, B ≤ A → D ≤ C → (subQuot A B).IsIrreducible → (subQuot C D).IsIrreducible → ¬ A.toSubmodule ≤ B.toSubmodule ⊔ T → ¬ C.toSubmodule ≤ D.toSubmodule ⊔ T → Nonempty ((subQuot A B).Equiv (subQuot C D)) := by
  first | exact @GlobalTheory.CompanionTheory.GenCoreMain.nonempty_equiv_of_generic | exact GlobalTheory.CompanionTheory.GenCoreMain.nonempty_equiv_of_generic | (intros; apply GlobalTheory.CompanionTheory.GenCoreMain.nonempty_equiv_of_generic <;> assumption)
