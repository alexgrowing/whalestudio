import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquivOfMultiplicityOneUniqueFactor
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equiv_of_multiplicity_one_unique_factor : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (T : Representation ℂ G W) (J : Representation ℂ G V), T.IsIrreducible → HasFiniteLength J → jhMult T J = 1 → (∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X), ρ.IsIrreducible → IsSubquotient ρ J → Nonempty (ρ.Equiv T)) → Nonempty (J.Equiv T) := by
  first | exact @GlobalTheory.CompanionTheory.FineStep.nonempty_equiv_of_jhMult_eq_one | exact GlobalTheory.CompanionTheory.FineStep.nonempty_equiv_of_jhMult_eq_one | (intros; apply GlobalTheory.CompanionTheory.FineStep.nonempty_equiv_of_jhMult_eq_one <;> assumption)
