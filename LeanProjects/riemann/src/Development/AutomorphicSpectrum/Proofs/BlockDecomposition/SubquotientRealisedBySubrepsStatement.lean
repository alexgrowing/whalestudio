import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientRealisedBySubreps
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subquotient_realised_by_subreps : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (π : Representation ℂ G W), IsSubquotient π ρ → ∃ A B : Subrepresentation ρ, B ≤ A ∧ Nonempty (π.Equiv (subQuot A B)) := by
  first | exact @GlobalTheory.CompanionTheory.SubquotPres.exists_equiv_subQuot | exact GlobalTheory.CompanionTheory.SubquotPres.exists_equiv_subQuot | (intros; apply GlobalTheory.CompanionTheory.SubquotPres.exists_equiv_subQuot <;> assumption)
