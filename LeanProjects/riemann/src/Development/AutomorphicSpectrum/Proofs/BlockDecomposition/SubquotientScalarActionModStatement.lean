import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientScalarActionMod
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subquotient_scalar_action_mod : ∀ {M W X : Type} [Group M] [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ M W) (σ : Representation ℂ M X) (S T : Subrepresentation ρ), Nonempty ((subQuot S T).Equiv σ) → ∀ (g : M) (c : ℂ), (∀ x, σ g x = c • x) → ∀ s ∈ S.toSubmodule, ρ g s - c • s ∈ T.toSubmodule := by
  first | exact @GlobalTheory.CompanionTheory.SubQuotScalar.sub_smul_mem_of_equiv_subQuot | exact GlobalTheory.CompanionTheory.SubQuotScalar.sub_smul_mem_of_equiv_subQuot | (intros; apply GlobalTheory.CompanionTheory.SubQuotScalar.sub_smul_mem_of_equiv_subQuot <;> assumption)
