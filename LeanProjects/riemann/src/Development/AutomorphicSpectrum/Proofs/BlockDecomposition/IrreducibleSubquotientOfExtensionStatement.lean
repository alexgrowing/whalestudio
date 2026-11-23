import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientOfExtension
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitImgMono
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_subquotient_of_extension : ∀ (G V W : Type) [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (A B : Subrepresentation ρ), A ≤ B → σ.IsIrreducible → IsSubquotient σ B.toRepresentation →
    IsSubquotient σ A.toRepresentation ∨ IsSubquotient σ (subQuot B A) := by
  first | exact @GlobalTheory.CompanionTheory.SubquotExt.isSubquotient_sub_or_quot | exact GlobalTheory.CompanionTheory.SubquotExt.isSubquotient_sub_or_quot | (intros; apply GlobalTheory.CompanionTheory.SubquotExt.isSubquotient_sub_or_quot <;> assumption)
